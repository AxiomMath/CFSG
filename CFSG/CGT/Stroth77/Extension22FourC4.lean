module

public import CFSG.CGT.Stroth77.Extension22FourProof

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {m : ℕ}

theorem pow_four_mem_fourB {τ : StrothTypeIndex} (D : StrothTypeData B τ) (b : B) :
    b ^ 4 ∈ fourB D := by
  rw [mem_fourB_iff]
  exact ⟨D.ec b, by rw [ec_pow]⟩

@[expose] noncomputable def conjByHom (g : S) (hg : g ∈ Subgroup.normalizer C) : C →* C where
  toFun x := conjBy hg x
  map_one' := by
    ext
    simp [conjBy]
  map_mul' x y := by
    ext
    simp [conjBy]
    group

@[simp]
theorem conjByHom_apply (g : S) (hg : g ∈ Subgroup.normalizer C) (x : C) :
    conjByHom g hg x = conjBy hg x := rfl

theorem conjByHom_mul (g h : S) (hg : g ∈ Subgroup.normalizer C)
    (hh : h ∈ Subgroup.normalizer C) :
    conjByHom (g * h) (Subgroup.mul_mem _ hg hh) =
      (conjByHom h hh).comp (conjByHom g hg) := by
  ext x
  simp only [MonoidHom.comp_apply, conjByHom_apply, conjBy]
  group

theorem conjByHom_mul_eq {g h g' h' : S}
    (hg : g ∈ Subgroup.normalizer C) (hh : h ∈ Subgroup.normalizer C)
    (hg' : g' ∈ Subgroup.normalizer C) (hh' : h' ∈ Subgroup.normalizer C)
    (hgh : g * h = g' * h') :
    conjByHom (g * h) (Subgroup.mul_mem _ hg hh) =
      conjByHom (g' * h') (Subgroup.mul_mem _ hg' hh') := by
  ext x
  simp only [conjByHom_apply, conjBy]
  rw [hgh]

theorem conjByHom_comp_inv (g : S) (hg : g ∈ Subgroup.normalizer C) :
    (conjByHom g hg).comp (conjByHom g⁻¹ (Subgroup.inv_mem _ hg)) = MonoidHom.id C := by
  ext x
  simp only [MonoidHom.comp_apply, conjByHom_apply, conjBy, MonoidHom.id_apply]
  group

theorem conjByHom_inv_comp (g : S) (hg : g ∈ Subgroup.normalizer C) :
    (conjByHom g⁻¹ (Subgroup.inv_mem _ hg)).comp (conjByHom g hg) = MonoidHom.id C := by
  ext x
  simp only [MonoidHom.comp_apply, conjByHom_apply, conjBy, MonoidHom.id_apply]
  group

section QuotientAction

variable [hN : (B.subgroupOf C).Normal]

noncomputable def conjByQuotientMap (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    (C ⧸ B.subgroupOf C) →* (C ⧸ B.subgroupOf C) :=
  QuotientGroup.map (B.subgroupOf C) (B.subgroupOf C) (conjByHom g hgC) (by
    intro x hx
    rw [Subgroup.mem_comap]
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simp only [conjByHom_apply, conjBy]
    exact (Subgroup.mem_normalizer_iff''.mp hgB (x : S)).mp hx)

@[simp]
theorem conjByQuotientMap_mk (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjByQuotientMap g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjByHom g hgC x) :=
  QuotientGroup.map_mk _ _ _ _ x

theorem conjByQuotientMap_left_inv (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.LeftInverse
      (conjByQuotientMap g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjByQuotientMap g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjByQuotientMap_mk, conjByQuotientMap_mk]
    congr 1
    have h := DFunLike.congr_fun (conjByHom_inv_comp g hgC) x
    simpa using h

theorem conjByQuotientMap_right_inv (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) :
    Function.RightInverse
      (conjByQuotientMap g⁻¹ (Subgroup.inv_mem _ hgC) (Subgroup.inv_mem _ hgB))
      (conjByQuotientMap g hgC hgB) := by
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    rw [conjByQuotientMap_mk, conjByQuotientMap_mk]
    congr 1
    have h := DFunLike.congr_fun (conjByHom_comp_inv g hgC) x
    simpa using h

noncomputable def conjByAutQuotient (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) : MulAut (C ⧸ B.subgroupOf C) :=
  MulEquiv.ofBijective (conjByQuotientMap g hgC hgB)
    ⟨(conjByQuotientMap_left_inv g hgC hgB).injective,
     (conjByQuotientMap_right_inv g hgC hgB).surjective⟩

@[simp]
theorem conjByAutQuotient_apply_mk (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (x : C) :
    conjByAutQuotient g hgC hgB (QuotientGroup.mk x) =
      QuotientGroup.mk (conjByHom g hgC x) := by
  show conjByQuotientMap g hgC hgB (QuotientGroup.mk x) = _
  exact conjByQuotientMap_mk g hgC hgB x

theorem conjByAutQuotient_one :
    conjByAutQuotient (B := B) (C := C) (1 : S) (Subgroup.one_mem _) (Subgroup.one_mem _) = 1 := by
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [conjByAutQuotient_apply_mk, MulAut.one_apply, conjByHom_apply, conjBy,
      Subgroup.coe_mk, inv_one, one_mul, mul_one]

theorem conjByAutQuotient_mul (g h : S) (hgC : g ∈ Subgroup.normalizer C)
    (hhC : h ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (hhB : h ∈ Subgroup.normalizer B) :
    conjByAutQuotient (g * h) (Subgroup.mul_mem _ hgC hhC)
        (Subgroup.mul_mem _ hgB hhB) =
      conjByAutQuotient h hhC hhB * conjByAutQuotient g hgC hgB := by
  apply MulEquiv.ext
  intro q
  induction q using QuotientGroup.induction_on with
  | H x =>
    simp only [MulAut.mul_apply, conjByAutQuotient_apply_mk]
    congr 1
    have h := DFunLike.congr_fun (conjByHom_mul g h hgC hhC) x
    simpa using h

theorem conjByAutQuotient_pow (g : S) (hgC : g ∈ Subgroup.normalizer C)
    (hgB : g ∈ Subgroup.normalizer B) (n : ℕ) :
    conjByAutQuotient (g ^ n) (Subgroup.pow_mem _ hgC n) (Subgroup.pow_mem _ hgB n) =
      (conjByAutQuotient g hgC hgB) ^ n := by
  induction n with
  | zero =>
    simpa using (conjByAutQuotient_one (B := B) (C := C) (S := S))
  | succ n ih =>
    calc conjByAutQuotient (g ^ (n + 1)) (Subgroup.pow_mem _ hgC (n + 1))
          (Subgroup.pow_mem _ hgB (n + 1))
        = conjByAutQuotient g hgC hgB * conjByAutQuotient (g ^ n)
            (Subgroup.pow_mem _ hgC n) (Subgroup.pow_mem _ hgB n) := by
          simpa only [pow_succ] using conjByAutQuotient_mul (g ^ n) g
            (Subgroup.pow_mem _ hgC n) hgC (Subgroup.pow_mem _ hgB n) hgB
      _ = conjByAutQuotient g hgC hgB * (conjByAutQuotient g hgC hgB) ^ n := by rw [ih]
      _ = (conjByAutQuotient g hgC hgB) ^ (n + 1) := by rw [pow_succ']

theorem exists_mul_of_conjByAutQuotient_eq_one [IsMulCommutative C]
    {g : S} (hgC : g ∈ Subgroup.normalizer C) (hgB : g ∈ Subgroup.normalizer B)
    (hA : conjByAutQuotient g hgC hgB = 1) (x : C) :
    ∃ b : B, g⁻¹ * (x : S) * g = (x : S) * (b : S) := by
  classical
  let aC : C := conjByHom g hgC x
  have haC : (aC : S) = g⁻¹ * (x : S) * g := by
    simp [aC, conjByHom, conjBy]
  have hmk : QuotientGroup.mk' (B.subgroupOf C) aC = QuotientGroup.mk' (B.subgroupOf C) x := by
    have h := congrArg (fun σ : MulAut (C ⧸ B.subgroupOf C) =>
      σ (QuotientGroup.mk' (B.subgroupOf C) x)) hA
    simpa [aC, conjByAutQuotient_apply_mk] using h
  have hbH : aC⁻¹ * x ∈ B.subgroupOf C := QuotientGroup.eq.mp hmk
  have hb : aC * x⁻¹ ∈ B.subgroupOf C := by
    have h' : aC * x⁻¹ = (aC⁻¹ * x)⁻¹ := by
      calc aC * x⁻¹ = x⁻¹ * aC := mul_comm' _ _
        _ = (aC⁻¹ * x)⁻¹ := by rw [mul_inv_rev, inv_inv]
    rw [h']
    exact (B.subgroupOf C).inv_mem hbH
  refine ⟨⟨aC * x⁻¹, hb⟩, ?_⟩
  change g⁻¹ * (x : S) * g = (x : S) * ((aC * x⁻¹ : C) : S)
  rw [← haC]
  have hCeq : aC = x * (aC * x⁻¹) := by
    calc aC = aC * (x⁻¹ * x) := by group
      _ = (aC * x⁻¹) * x := by group
      _ = x * (aC * x⁻¹) := by rw [mul_comm' (aC * x⁻¹) x]
  simpa using congrArg (fun y : C => (y : S)) hCeq

end QuotientAction

theorem conjBy_pow_four_mem_fourB
    {τ : StrothTypeIndex} {D : StrothTypeData B τ} {g : S}
    (hgB : g ∈ Subgroup.normalizer B) (z : C) (b : B)
    (hz4B : (z : S) ^ 4 ∈ B)
    (hgb : g⁻¹ * (z : S) * g = (z : S) * (b : S))
    (hcomm : Commute (z : S) (b : S)) :
    conjBy hgB (⟨(z : S) ^ 4, hz4B⟩ : B) * (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D := by
  let yB : B := ⟨(z : S) ^ 4, hz4B⟩
  have hconjpow : g⁻¹ * (z : S) ^ 4 * g = (z : S) ^ 4 * (b : S) ^ 4 := by
    have hpow : g⁻¹ * (z : S) ^ 4 * g = (g⁻¹ * (z : S) * g) ^ 4 := by
      simpa using (conj_pow (a := g⁻¹) (b := (z : S)) (i := 4)).symm
    rw [hpow, hgb]
    exact hcomm.mul_pow 4
  have hconj : conjBy hgB yB * yB⁻¹ = b ^ 4 := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow, conjBy, Subgroup.coe_mk]
    change (g⁻¹ * (yB : S) * g) * (yB : S)⁻¹ = (b : S) ^ 4
    have hy : (yB : S) = (z : S) ^ 4 := rfl
    rw [hy, hconjpow, (hcomm.pow_pow 4 4).eq]
    group
  rw [hconj]
  exact pow_four_mem_fourB D b

theorem not_cyclic_quotient_four_zero
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hm : m = 0)
    (hcyc : ∃ z : C, Subgroup.zpowers z = ⊤) : False := by
  subst m
  let D := hB.data
  haveI : IsCyclic C := isCyclic_iff_exists_zpowers_eq_top.mpr hcyc
  haveI : IsCyclic B := Subgroup.isCyclic_of_le hBC
  have hna : orderOf D.a = 2 := by
    rw [D.orderOf_a, n_t100]
    norm_num
  have hnb : orderOf D.b = 2 := by
    rw [D.orderOf_b, n_t100]
    norm_num
  have ha2 : D.a ^ 2 = 1 := by
    rw [← hna]
    exact pow_orderOf_eq_one D.a
  have hb2 : D.b ^ 2 = 1 := by
    rw [← hnb]
    exact pow_orderOf_eq_one D.b
  have ha1 : D.a ≠ 1 := by
    intro h
    have : orderOf D.a = 1 := by rw [h, orderOf_one]
    rw [hna] at this
    norm_num at this
  have hb1 : D.b ≠ 1 := by
    intro h
    have : orderOf D.b = 1 := by rw [h, orderOf_one]
    rw [hnb] at this
    norm_num at this
  have hab : D.a ≠ D.b := by
    intro h
    have h' : (Torus.a : Torus (StrothTypeIndex.t100 0).k) = Torus.b := by
      have := congrArg (fun x : B => D.e (Additive.ofMul x)) h
      simpa [StrothTypeData.a, StrothTypeData.b] using this
    have hne : (Torus.a : Torus (StrothTypeIndex.t100 0).k) 1 ≠
        (Torus.b : Torus (StrothTypeIndex.t100 0).k) 1 := by
      simp [Torus.a, Torus.b, gen, Pi.single_apply]
      decide
    exact hne (congrFun h' 1)
  classical
  haveI : Fintype B := Fintype.ofFinite B
  have hle : (Finset.univ.filter (fun x : B => x ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (α := B) (n := 2) (by norm_num)
  have h1a : (1 : B) ≠ D.a := fun h => ha1 h.symm
  have h1b : (1 : B) ≠ D.b := fun h => hb1 h.symm
  let t : Finset B := {1, D.a, D.b}
  have ht : t.card = 3 :=
    Finset.card_eq_three.mpr ⟨1, D.a, D.b, h1a, h1b, hab, rfl⟩
  have hsub : t ⊆ Finset.univ.filter (fun x : B => x ^ 2 = 1) := by
    intro x hx
    simp only [t, Finset.mem_insert, Finset.mem_singleton] at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hx with rfl | rfl | rfl
    · simp
    · exact ha2
    · exact hb2
  have h3 : 3 ≤ (Finset.univ.filter (fun x : B => x ^ 2 = 1)).card := by
    rw [← ht]
    exact Finset.card_le_card hsub
  omega

theorem not_cyclic_quotient_four_of_pos
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hm : 1 ≤ m)
    (hcyc : ∃ z : C, Subgroup.zpowers z = ⊤) : False := by
  classical
  let D := hB.data
  haveI hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  haveI : IsCyclic C := isCyclic_iff_exists_zpowers_eq_top.mpr hcyc
  letI : CommGroup C := IsCyclic.commGroup
  obtain ⟨z, hz⟩ := hcyc
  let q : C ⧸ B.subgroupOf C := QuotientGroup.mk' (B.subgroupOf C) z
  have hQcard : Nat.card (C ⧸ B.subgroupOf C) = 4 :=
    card_quotient_four hBC hC hrel
  haveI : IsCyclic (C ⧸ B.subgroupOf C) :=
    isCyclic_of_surjective (QuotientGroup.mk' (B.subgroupOf C))
      (QuotientGroup.mk'_surjective _)
  have hq_gen : Subgroup.zpowers q = ⊤ := by
    have h := MonoidHom.map_zpowers (QuotientGroup.mk' (B.subgroupOf C)) z
    rw [hz, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h
    exact h.symm
  have hq_order : orderOf q = 4 := by
    rw [orderOf_eq_card_of_zpowers_eq_top hq_gen, hQcard]
  have hq4 : q ^ 4 = 1 := by
    rw [← hq_order]
    exact pow_orderOf_eq_one q
  have hz4H : z ^ 4 ∈ B.subgroupOf C := by
    have h : QuotientGroup.mk' (B.subgroupOf C) (z ^ 4) = 1 := by
      simpa [q, map_pow] using hq4
    exact (QuotientGroup.eq_one_iff _).mp h
  have hz4B : (z : S) ^ 4 ∈ B := by
    have := Subgroup.mem_subgroupOf.mp hz4H
    simpa using this
  have hq2 : q ^ 2 ≠ 1 := by
    intro h
    have hdvd : orderOf q ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr h
    rw [hq_order] at hdvd
    norm_num at hdvd
  have hAutSq : ∀ σ : MulAut (C ⧸ B.subgroupOf C), σ * σ = 1 := by
    intro σ
    have hcard : Nat.card (MulAut (C ⧸ B.subgroupOf C)) = 2 := by
      rw [IsCyclic.card_mulAut (C ⧸ B.subgroupOf C), hQcard]
      decide
    have h : orderOf σ ∣ 2 := by
      rw [← hcard]
      exact orderOf_dvd_natCard σ
    simpa [pow_two] using (orderOf_dvd_iff_pow_eq_one).mp h
  have huvC : D.uv ∈ Subgroup.normalizer C := hL D.uv_mem_L
  have htC : D.t ∈ Subgroup.normalizer C := hL D.t_mem_L
  have hρC : D.ρ ∈ Subgroup.normalizer C := hL D.ρ_mem_L
  let Auv : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.uv huvC D.uv_mem
  let At : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.t htC D.t_mem
  let Ar : MulAut (C ⧸ B.subgroupOf C) := conjByAutQuotient D.ρ hρC D.ρ_mem
  have hAuv_sq : Auv * Auv = 1 := by
    have h := conjByAutQuotient_pow D.uv huvC D.uv_mem 2
    simpa [pow_two, D.uv_sq, conjByAutQuotient_one] using h.symm
  have hAt_sq : At * At = 1 := by
    have h := conjByAutQuotient_pow D.t htC D.t_mem 2
    simpa [pow_two, D.t_sq, conjByAutQuotient_one] using h.symm
  have hAr_cube : Ar ^ 3 = 1 := by
    have h := conjByAutQuotient_pow D.ρ hρC D.ρ_mem 3
    have hρ3 : D.ρ * (D.ρ * D.ρ) = 1 := by
      rw [← mul_assoc]
      exact D.rho_cube
    simpa [pow_three, mul_assoc, hρ3, conjByAutQuotient_one] using h.symm
  have hcomp1 : (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC) =
      (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := by
    have h1 := conjByHom_mul D.uv D.ρ huvC hρC
    have h2 := conjByHom_mul D.ρ D.t hρC htC
    have h3 : conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) =
        conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) :=
      conjByHom_mul_eq huvC hρC hρC htC D.uv_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.uv huvC)
        = conjByHom (D.uv * D.ρ) (Subgroup.mul_mem _ huvC hρC) := h1.symm
      _ = conjByHom (D.ρ * D.t) (Subgroup.mul_mem _ hρC htC) := h3
      _ = (conjByHom D.t htC).comp (conjByHom D.ρ hρC) := h2
  have hcomp2 : (conjByHom D.ρ hρC).comp (conjByHom D.t htC) =
      (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
    have h1 := conjByHom_mul D.t D.ρ htC hρC
    have h2 := conjByHom_mul (D.ρ * D.uv) D.t (Subgroup.mul_mem _ hρC huvC) htC
    have h3 := conjByHom_mul D.ρ D.uv hρC huvC
    have h4 : conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) =
        conjByHom ((D.ρ * D.uv) * D.t) (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) :=
      conjByHom_mul_eq htC hρC (Subgroup.mul_mem _ hρC huvC) htC D.t_rho
    calc (conjByHom D.ρ hρC).comp (conjByHom D.t htC)
        = conjByHom (D.t * D.ρ) (Subgroup.mul_mem _ htC hρC) := h1.symm
      _ = conjByHom ((D.ρ * D.uv) * D.t)
            (Subgroup.mul_mem _ (Subgroup.mul_mem _ hρC huvC) htC) := h4
      _ = (conjByHom D.t htC).comp (conjByHom (D.ρ * D.uv)
            (Subgroup.mul_mem _ hρC huvC)) := h2
      _ = (conjByHom D.t htC).comp ((conjByHom D.uv huvC).comp (conjByHom D.ρ hρC)) := by
            rw [h3]
  have hAr : Ar = 1 := by
    have hsq := hAutSq Ar
    calc Ar = Ar * 1 := (mul_one Ar).symm
      _ = Ar * (Ar * Ar) := by rw [hsq]
      _ = Ar * Ar * Ar := by rw [← mul_assoc]
      _ = Ar ^ 3 := by rw [pow_three, mul_assoc]
      _ = 1 := hAr_cube
  have hAuv_Ar : Ar * Auv = At * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk (by simpa using DFunLike.congr_fun hcomp1 x)
  have hAt_Ar : Ar * At = At * Auv * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk
        (by simpa [MonoidHom.comp_apply] using DFunLike.congr_fun hcomp2 x)
  have hAuv_eq_At : Auv = At := by
    simpa [hAr] using hAuv_Ar
  have hAuv : Auv = 1 := by
    have h := hAt_Ar
    rw [hAr] at h
    have h' : At = At * Auv := by simpa using h
    have h'' : At * At = At * (At * Auv) := congrArg (fun x => At * x) h'
    rw [← mul_assoc] at h''
    have h''' : (1 : MulAut (C ⧸ B.subgroupOf C)) = Auv := by
      simpa [hAt_sq] using h''
    exact h'''.symm
  have hAt : At = 1 := hAuv_eq_At.symm.trans hAuv
  obtain ⟨bρ, hbρ⟩ := exists_mul_of_conjByAutQuotient_eq_one hρC D.ρ_mem hAr z
  obtain ⟨bt, hbt⟩ := exists_mul_of_conjByAutQuotient_eq_one htC D.t_mem hAt z
  have hcommρ : Commute (z : S) (bρ : S) := by
    have h := mul_comm (⟨(z : S), z.2⟩ : C) ⟨(bρ : S), hBC bρ.2⟩
    exact congrArg Subtype.val h
  have hcommt : Commute (z : S) (bt : S) := by
    have h := mul_comm (⟨(z : S), z.2⟩ : C) ⟨(bt : S), hBC bt.2⟩
    exact congrArg Subtype.val h
  have hρfix : conjBy D.ρ_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.ρ_mem z bρ hz4B hbρ hcommρ
  have htfix : conjBy D.t_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.t_mem z bt hz4B hbt hcommt
  have hcases := t100_fixed_rho_t_mod_four_of_mem (D := D) hm
    (y := (⟨(z : S) ^ 4, hz4B⟩ : B)) hρfix htfix
  rcases hcases with hy4 | hyc2
  · obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hy4
    let sC : C := ⟨s, hBC s.2⟩
    let yC : C := ⟨(z : S) ^ 4, hBC hz4B⟩
    have hz4C : z ^ 4 = yC := by ext; rfl
    have hsC4 : sC ^ 4 = yC := by
      apply Subtype.ext
      simpa [sC, yC] using congrArg (fun x : B => (x : S)) hs
    let wC : C := z * sC⁻¹
    have hw4 : wC ^ 4 = 1 := by
      calc wC ^ 4 = z ^ 4 * (sC ^ 4)⁻¹ := by
            rw [show wC = z * sC⁻¹ from rfl, mul_pow, inv_pow]
        _ = yC * yC⁻¹ := by rw [hz4C, hsC4]
        _ = 1 := mul_inv_cancel yC
    let winv : C := wC ^ 2
    have hwinv2 : winv * winv = 1 := by
      have h : winv * winv = wC ^ 4 := by
        show (wC ^ 2) * (wC ^ 2) = wC ^ 4
        group
      rw [h, hw4]
    have hwinvS2 : (winv : S) * (winv : S) = 1 := by
      simpa using congrArg (fun x : C => (x : S)) hwinv2
    have hwinv_notB : (winv : S) ∉ B := by
      intro hmem
      have hmemH : winv ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hmem
      have h1 : QuotientGroup.mk' (B.subgroupOf C) winv = 1 :=
        (QuotientGroup.eq_one_iff winv).mpr hmemH
      have hmkw : QuotientGroup.mk' (B.subgroupOf C) wC = q := by
        have hs1 : QuotientGroup.mk' (B.subgroupOf C) sC = 1 :=
          (QuotientGroup.eq_one_iff sC).mpr (Subgroup.mem_subgroupOf.mpr s.2)
        rw [show wC = z * sC⁻¹ from rfl, map_mul, map_inv, hs1]
        simp [q]
      have hq2eq : q ^ 2 = 1 := by
        rw [← hmkw, ← map_pow]
        simpa [winv] using h1
      exact hq2 hq2eq
    exact hwinv_notB (hH (winv : S) (hcS winv.2) hwinvS2 (hC winv.2))
  · obtain ⟨s, hs⟩ := exists_pow_four_of_mem_fourB D hyc2
    let sC : C := ⟨s, hBC s.2⟩
    let yC : C := ⟨(z : S) ^ 4, hBC hz4B⟩
    let cC : C := ⟨D.c, hBC D.c.2⟩
    have hz4C : z ^ 4 = yC := by ext; rfl
    have hsC4 : sC ^ 4 = yC * cC ^ (-2 : ℤ) := by
      apply Subtype.ext
      simpa [sC, yC, cC] using congrArg (fun x : B => (x : S)) hs
    let wC : C := z * sC⁻¹
    have hw4 : wC ^ 4 = cC ^ 2 := by
      calc wC ^ 4 = z ^ 4 * (sC ^ 4)⁻¹ := by
            rw [show wC = z * sC⁻¹ from rfl, mul_pow, inv_pow]
        _ = yC * (yC * cC ^ (-2 : ℤ))⁻¹ := by rw [hz4C, hsC4]
        _ = cC ^ 2 := by
            have hcinv : (cC ^ (-2 : ℤ))⁻¹ = cC ^ 2 := by
              simpa using (zpow_neg cC (-2 : ℤ)).symm
            rw [mul_inv_rev, hcinv]
            calc yC * (cC ^ 2 * yC⁻¹) = (yC * cC ^ 2) * yC⁻¹ := by rw [mul_assoc]
              _ = (cC ^ 2 * yC) * yC⁻¹ := by rw [mul_comm yC (cC ^ 2)]
              _ = cC ^ 2 * (yC * yC⁻¹) := by rw [mul_assoc]
              _ = cC ^ 2 := by rw [mul_inv_cancel, mul_one]
    let winv : C := wC ^ 2 * cC⁻¹
    have hwinv2 : winv * winv = 1 := by
      have hcomm : Commute (wC ^ 2) (cC⁻¹) := (Commute.all wC cC).pow_left 2 |>.inv_right
      have h : winv * winv = wC ^ 4 * cC ^ (-2 : ℤ) := by
        rw [show winv * winv = (wC ^ 2 * cC⁻¹) ^ 2 by rw [pow_two]]
        rw [hcomm.mul_pow 2, ← pow_mul, inv_pow]
        norm_num
      rw [h, hw4, zpow_neg]
      group
    have hwinvS2 : (winv : S) * (winv : S) = 1 := by
      simpa using congrArg (fun x : C => (x : S)) hwinv2
    have hwinv_notB : (winv : S) ∉ B := by
      intro hmem
      have hmemH : winv ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr hmem
      have h1 : QuotientGroup.mk' (B.subgroupOf C) winv = 1 :=
        (QuotientGroup.eq_one_iff winv).mpr hmemH
      have hmkw : QuotientGroup.mk' (B.subgroupOf C) wC = q := by
        have hs1 : QuotientGroup.mk' (B.subgroupOf C) sC = 1 :=
          (QuotientGroup.eq_one_iff sC).mpr (Subgroup.mem_subgroupOf.mpr s.2)
        rw [show wC = z * sC⁻¹ from rfl, map_mul, map_inv, hs1]
        simp [q]
      have hc1 : QuotientGroup.mk' (B.subgroupOf C) cC = 1 :=
        (QuotientGroup.eq_one_iff cC).mpr (Subgroup.mem_subgroupOf.mpr D.c.2)
      have hq2eq : q ^ 2 = 1 := by
        have hwinv : QuotientGroup.mk' (B.subgroupOf C) winv = q ^ 2 := by
          rw [show winv = wC ^ 2 * cC⁻¹ from rfl, map_mul, map_pow, map_inv, hmkw, hc1]
          simp
        rw [← hwinv]
        exact h1
      exact hq2 hq2eq
    exact hwinv_notB (hH (winv : S) (hcS winv.2) hwinvS2 (hC winv.2))

theorem not_cyclic_quotient_four
    (hB : HasStrothType B (StrothTypeIndex.t100 m))
    (hBC : B ≤ C) (hC : C ≤ Subgroup.centralizer (B : Set S))
    (hrel : Nat.card C = 4 * Nat.card B)
    (hL : hB.data.L ≤ Subgroup.normalizer C)
    (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S') (hne : C ≠ B)
    (hcyc : ∃ z : C, Subgroup.zpowers z = ⊤) : False := by
  rcases Nat.eq_zero_or_pos m with hm0 | hpos
  · exact not_cyclic_quotient_four_zero hB hBC hm0 hcyc
  · exact not_cyclic_quotient_four_of_pos hB hBC hC hrel hL hH hcS hpos hcyc

end CFSG.CGT.Stroth77
