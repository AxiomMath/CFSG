module

public import CFSG.CGT.Stroth77.Extension212Group
public import CFSG.CGT.Stroth77.Extension25Common

public section

namespace CFSG.CGT.Stroth77

variable {S : Type*} [Group S] [Finite S] {B C S' : Subgroup S} {τ : StrothTypeIndex}

section NotCyclic

variable (D : StrothTypeData B τ)

theorem not_isCyclic_quotient_of_data [hN : (B.subgroupOf C).Normal] (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hfix4 : ∀ y : B, conjBy D.ρ_mem y * y⁻¹ ∈ fourB D → conjBy D.t_mem y * y⁻¹ ∈ fourB D →
      ∃ σ : B, σ * σ = y) :
    ¬ IsCyclic (C ⧸ B.subgroupOf C) := by
  intro hcycQ
  classical
  have hcomm : ∀ x y : C, x * y = y * x :=
    comm_of_le_centralizer_of_cyclic_quotient hBC hC hcycQ
  letI : CommGroup C := { mul_comm := hcomm }
  obtain ⟨q₀, hq₀⟩ := hcycQ.exists_generator
  obtain ⟨z, hzq⟩ := QuotientGroup.mk'_surjective (B.subgroupOf C) q₀
  let q : C ⧸ B.subgroupOf C := QuotientGroup.mk' (B.subgroupOf C) z
  have hQcard : Nat.card (C ⧸ B.subgroupOf C) = 4 :=
    card_quotient_four hBC hC hrel
  have hq_gen : Subgroup.zpowers q = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hqq : q = q₀ := hzq
    rw [hqq]
    exact hq₀ y
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
  have hAr_cube : Ar ^ 3 = 1 := by
    have h := conjByAutQuotient_pow D.ρ hρC D.ρ_mem 3
    have hρ3 : D.ρ * (D.ρ * D.ρ) = 1 := by
      rw [← mul_assoc]
      exact D.rho_cube
    simpa [pow_three, mul_assoc, hρ3, conjByAutQuotient_one] using h.symm
  have hAt_sq : At * At = 1 := by
    have h := conjByAutQuotient_pow D.t htC D.t_mem 2
    simpa [pow_two, D.t_sq, conjByAutQuotient_one] using h.symm
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
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
      exact congrArg QuotientGroup.mk (by simpa using DFunLike.congr_fun hcomp1 x)
  have hAt_Ar : Ar * At = At * Auv * Ar := by
    apply MulEquiv.ext
    intro q
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp only [Ar, Auv, At, MulAut.mul_apply, conjByAutQuotient_apply_mk]
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
  obtain ⟨bρ, hbρ⟩ := exists_mul_of_conjByAutQuotient_eq_one_Idx4 hcomm hρC D.ρ_mem hAr z
  obtain ⟨bt, hbt⟩ := exists_mul_of_conjByAutQuotient_eq_one_Idx4 hcomm htC D.t_mem hAt z
  have hcommρ : Commute (z : S) (bρ : S) := by
    have h := hcomm (⟨(z : S), z.2⟩ : C) ⟨(bρ : S), hBC bρ.2⟩
    exact congrArg Subtype.val h
  have hcommt : Commute (z : S) (bt : S) := by
    have h := hcomm (⟨(z : S), z.2⟩ : C) ⟨(bt : S), hBC bt.2⟩
    exact congrArg Subtype.val h
  have hρfix : conjBy D.ρ_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.ρ_mem z bρ hz4B hbρ hcommρ
  have htfix : conjBy D.t_mem (⟨(z : S) ^ 4, hz4B⟩ : B) *
      (⟨(z : S) ^ 4, hz4B⟩ : B)⁻¹ ∈ fourB D :=
    conjBy_pow_four_mem_fourB D.t_mem z bt hz4B hbt hcommt
  obtain ⟨σ, hσ⟩ := hfix4 _ hρfix htfix
  have hσS : (σ : S) * σ = ((z : S) ^ 2) * ((z : S) ^ 2) := by
    have h := congrArg Subtype.val hσ
    simp only [Subgroup.coe_mul] at h
    rw [h]
    group
  have hz2C : ((z : S) ^ 2) ∈ C := C.pow_mem z.2 2
  have hz2B : ((z : S) ^ 2) ∉ B := by
    intro hmem
    have hmemH : z ^ 2 ∈ B.subgroupOf C := Subgroup.mem_subgroupOf.mpr (by simpa using hmem)
    have h1 : QuotientGroup.mk' (B.subgroupOf C) (z ^ 2) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr hmemH
    exact hq2 (by simpa [q, map_pow] using h1)
  exact false_of_mul_self_eq hBC hC hH hcS hz2C hz2B hσS

end NotCyclic

section Basis

variable (D : StrothTypeData B τ)

theorem fix_of_torus (hfix : ∀ v : Torus τ.k, τ.action.φρ v = v → τ.action.φt v = v → v = 0) :
    ∀ y : B, conjBy D.ρ_mem y = y → conjBy D.t_mem y = y → y = 1 := by
  intro y hρ ht
  rw [← D.ec_eq_zero_iff]
  apply hfix
  · rw [← ec_conj_ρ_data D, hρ]
  · rw [← ec_conj_t_data D, ht]

theorem fix4_of_torus (hfix4 : ∀ v : Torus τ.k, (∃ z, 4 • z = τ.action.φρ v - v) →
      (∃ z, 4 • z = τ.action.φt v - v) → ∃ z, 2 • z = v) :
    ∀ y : B, conjBy D.ρ_mem y * y⁻¹ ∈ fourB D → conjBy D.t_mem y * y⁻¹ ∈ fourB D →
      ∃ σ : B, σ * σ = y := by
  intro y hρ ht
  rw [mem_fourB_iff, ec_conj_mul_inv D D.ρ_mem (ec_conj_ρ_data D)] at hρ
  rw [mem_fourB_iff, ec_conj_mul_inv D D.t_mem (ec_conj_t_data D)] at ht
  obtain ⟨z, hz⟩ := hfix4 _ hρ ht
  exact exists_mul_self_eq_of_two_nsmul D y hz

theorem conjBy_ρ_a_of_data (hρa : τ.action.φρ (gen τ.k 1) = gen τ.k 2) :
    conjBy D.ρ_mem D.a = D.b := by
  apply D.ec_injective
  rw [ec_conj_ρ_data D, D.ec_a, D.ec_b]
  exact hρa

variable [hN : (B.subgroupOf C).Normal]

theorem exists_torusBasis_idx4_of_data (hk : ∀ i, 1 ≤ τ.k i) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hρpar : ∀ v, parityTorus _ hk (τ.action.φρ v) = rhoBar300 (parityTorus _ hk v))
    (hρa : τ.action.φρ (gen τ.k 1) = gen τ.k 2)
    (hfix : ∀ y : B, conjBy D.ρ_mem y = y → conjBy D.t_mem y = y → y = 1)
    (hncyc : ¬ IsCyclic (C ⧸ B.subgroupOf C)) {K : Fin 3 → ℕ} (hK0 : K 0 = τ.k 0)
    (hK1 : K 1 = τ.k 1 + 1) (hK2 : K 2 = τ.k 2 + 1) {g : C} (hg : g * g = ⟨D.a, hBC D.a.2⟩) :
    ∃ E : Torus K ≃+ Additive C, E (gen K 0) = Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C) ∧
      E (gen K 1) = Additive.ofMul g ∧ E (gen K 2) = Additive.ofMul (conjBy (hL D.ρ_mem_L) g) := by
  classical
  have hcommC : IsMulCommutative C :=
    isMulCommutative_of_relIndex_four_Idx4 D hBC hC hrel hL hncyc hfix
  have hcomm : ∀ x y : C, x * y = y * x := fun x y => hcommC.is_comm.comm x y
  have hsq : ∀ x : C, (x : S) * x ∈ B := sq_mem_of_not_cyclic_quotient_four hBC hC hrel hncyc
  have hcardQ : Nat.card (C ⧸ B.subgroupOf C) = 4 := card_quotient_four hBC hC hrel
  have hexp : ∀ q : C ⧸ B.subgroupOf C, q * q = 1 := by
    rcases cyclic_or_sq_eq_one hcardQ with hcyc | h
    · exact absurd hcyc hncyc
    · exact h
  let h' : C := conjBy (hL D.ρ_mem_L) g
  have hh : h' * h' = ⟨D.b, hBC D.b.2⟩ := by
    rw [← conjBy_mul, hg]
    apply Subtype.ext
    have h := congrArg Subtype.val (conjBy_ρ_a_of_data D hρa)
    simpa [conjBy_val] using h
  let P : C → Fin 3 → ZMod 2 := sqParityIdx4 D hk hsq
  have hPg : P g = Pi.single 1 1 :=
    (sqParityIdx4_of_sq_eq hBC hg).trans (by rw [D.ec_a]; exact parityTorus_gen _ _ 1)
  have hPh : P h' = Pi.single 2 1 :=
    (sqParityIdx4_of_sq_eq hBC hh).trans (by rw [D.ec_b]; exact parityTorus_gen _ _ 2)
  have hPB : ∀ x : C, x ∈ B.subgroupOf C → P x = 0 := fun x hx =>
    sqParityIdx4_of_mem x (Subgroup.mem_subgroupOf.mp hx)
  have hg_not : g ∉ B.subgroupOf C := fun h => by
    have := hPB g h
    rw [hPg] at this
    exact absurd (congrFun this 1) (by simp)
  have hh_not : h' ∉ B.subgroupOf C := fun h => by
    have := hPB h' h
    rw [hPh] at this
    exact absurd (congrFun this 2) (by simp)
  have hgh_not : g * h'⁻¹ ∉ B.subgroupOf C := fun h => by
    have h1 := hPB _ h
    have h2 : P (g * h'⁻¹ * h') = P (g * h'⁻¹) + P h' := sqParityIdx4_mul hcomm _ _
    rw [inv_mul_cancel_right, h1, zero_add, hPg, hPh] at h2
    exact absurd (congrFun h2 1) (by simp)
  let x : Fin 3 → C := ![⟨D.c, hBC D.c.2⟩, g, h']
  have hx : ∀ i, x i ^ (2 ^ K i) = 1 := by
    intro i
    fin_cases i
    · change (⟨D.c, hBC D.c.2⟩ : C) ^ (2 ^ K 0) = 1
      rw [hK0]
      exact pow_two_pow_eq_one_of_orderOf hBC (orderOf_c_lift D)
    · change g ^ (2 ^ K 1) = 1
      rw [hK1, pow_succ', pow_mul, sq, hg]
      exact pow_two_pow_eq_one_of_orderOf hBC (orderOf_a_lift D)
    · change h' ^ (2 ^ K 2) = 1
      rw [hK2, pow_succ', pow_mul, sq, hh]
      exact pow_two_pow_eq_one_of_orderOf hBC (orderOf_b_lift D)
  have hgen : Subgroup.closure (Set.range x) = ⊤ := by
    let H := Subgroup.closure (Set.range x)
    have hcH : (⟨D.c, hBC D.c.2⟩ : C) ∈ H := Subgroup.subset_closure ⟨0, rfl⟩
    have hgH : g ∈ H := Subgroup.subset_closure ⟨1, rfl⟩
    have hhH : h' ∈ H := Subgroup.subset_closure ⟨2, rfl⟩
    have hBH : ∀ y : C, y ∈ B.subgroupOf C → y ∈ H := by
      intro y hy
      have hyB : (y : S) ∈ B := Subgroup.mem_subgroupOf.mp hy
      obtain ⟨i, j, l, hijl⟩ := torus_eq_zsmul_gens _ (D.ec ⟨y, hyB⟩)
      have hβ := eq_zpow_c_a_b_Idx4 D hijl
      have hyeq : y = (⟨D.c, hBC D.c.2⟩ : C) ^ i * (g * g) ^ j * (h' * h') ^ l := by
        rw [hg, hh]
        apply Subtype.ext
        have h := congrArg Subtype.val hβ
        simpa using h
      rw [hyeq]
      exact H.mul_mem (H.mul_mem (H.zpow_mem hcH i) (H.zpow_mem (H.mul_mem hgH hgH) j))
        (H.zpow_mem (H.mul_mem hhH hhH) l)
    rw [eq_top_iff]
    intro y _
    rcases mem_cosets_Idx4 hcardQ hexp hg_not hh_not hgh_not y with h | h | h | h
    · exact hBH y h
    · have := H.mul_mem (hBH _ h) hgH
      rw [inv_mul_cancel_right] at this
      exact this
    · have := H.mul_mem (hBH _ h) hhH
      rw [inv_mul_cancel_right] at this
      exact this
    · have := H.mul_mem (hBH _ h) (H.mul_mem hgH hhH)
      rw [inv_mul_cancel_right] at this
      exact this
  have hcard : Nat.card (Torus K) = Nat.card C := by
    rw [card_torus, hrel, D.card, hK0, hK1, hK2]
    rw [show τ.k 0 + (τ.k 1 + 1) + (τ.k 2 + 1) = (τ.k 0 + τ.k 1 + τ.k 2) + 2 by ring, pow_add]
    ring
  obtain ⟨E, hE⟩ := exists_torusEquiv_Idx4 hcomm x hx hgen hcard
  exact ⟨E, hE 0, hE 1, hE 2⟩

theorem E_incl4 (hBC : B ≤ C) {K : Fin 3 → ℕ} (hK0 : K 0 = τ.k 0) (hK1 : K 1 = τ.k 1 + 1)
    (hK2 : K 2 = τ.k 2 + 1) {g h : C} (hg : g * g = ⟨D.a, hBC D.a.2⟩)
    (hh : h * h = ⟨D.b, hBC D.b.2⟩) (E : Torus K ≃+ Additive C)
    (hE0 : E (gen K 0) = Additive.ofMul (⟨D.c, hBC D.c.2⟩ : C))
    (hE1 : E (gen K 1) = Additive.ofMul g) (hE2 : E (gen K 2) = Additive.ofMul h) (β : B) :
    E (incl4 τ.k K hK0 hK1 hK2 (D.ec β)) = Additive.ofMul (⟨β, hBC β.2⟩ : C) := by
  obtain ⟨i, j, l, hijl⟩ := torus_eq_zsmul_gens _ (D.ec β)
  have hβ := eq_zpow_c_a_b_Idx4 D hijl
  have hβC : (⟨β, hBC β.2⟩ : C) = (⟨D.c, hBC D.c.2⟩ : C) ^ i * (g * g) ^ j * (h * h) ^ l := by
    rw [hg, hh]
    apply Subtype.ext
    simpa using congrArg Subtype.val hβ
  rw [hijl, incl4_apply, map_add, map_add, map_zsmul, map_zsmul, map_zsmul, hE0, hE1, hE2, hβC,
    ofMul_mul, ofMul_mul, ofMul_zpow, ofMul_zpow, ofMul_zpow, ofMul_mul, ofMul_mul,
    mul_comm (2 : ℤ) j, mul_comm (2 : ℤ) l, mul_zsmul, mul_zsmul, two_zsmul, two_zsmul]

end Basis

theorem hasStrothTypeOver_or_of_index_four_of_data (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hk : ∀ i, 1 ≤ τ.k i)
    (hρpar : ∀ v, parityTorus _ hk (τ.action.φρ v) = rhoBar300 (parityTorus _ hk v))
    (hρa : τ.action.φρ (gen τ.k 1) = gen τ.k 2)
    (hfix : ∀ v : Torus τ.k, τ.action.φρ v = v → τ.action.φt v = v → v = 0)
    (hfix4 : ∀ v : Torus τ.k, (∃ z, 4 • z = τ.action.φρ v - v) →
      (∃ z, 4 • z = τ.action.φt v - v) → ∃ z, 2 • z = v)
    (τ₁ : StrothTypeIndex) (hK0 : τ₁.k 0 = τ.k 0) (hK1 : τ₁.k 1 = τ.k 1 + 1)
    (hK2 : τ₁.k 2 = τ.k 2 + 1) (A' : SigmaFourAction τ₁.k)
    (hP : Profile4 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ)
    (hT : Twist4 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ A'.φuv A'.φt A'.φu
      A'.φρ)
    (cV : MatEq τ₁.k (τ₁.action.uv * diag4) (diag4 * τ.action.uv))
    (cW : MatEq τ₁.k (τ₁.action.t * diag4) (diag4 * τ.action.t))
    (cU : MatEq τ₁.k (τ₁.action.u * diag4) (diag4 * τ.action.u))
    (cR : MatEq τ₁.k (τ₁.action.ρ * diag4) (diag4 * τ.action.ρ)) :
    HasStrothTypeOver D C τ₁ ∨ ∃ (E : Torus τ₁.k ≃+ Additive C) (φ : Torus τ₁.k ≃+ Torus τ₁.k),
      ∀ j, φ.symm (conjTorusIdx4 E (hL D.uv_mem_L) (φ (gen τ₁.k j))) = A'.φuv (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.t_mem_L) (φ (gen τ₁.k j))) = A'.φt (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.u_mem_L) (φ (gen τ₁.k j))) = A'.φu (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.ρ_mem_L) (φ (gen τ₁.k j))) = A'.φρ (gen τ₁.k j) := by
  have hN : (B.subgroupOf C).Normal :=
    Subgroup.normal_of_le_center (subgroupOf_le_center hBC hC)
  have hfix' := fix_of_torus D hfix
  have hncyc := not_isCyclic_quotient_of_data D hBC hC hrel hL hH hcS (fix4_of_torus D hfix4)
  obtain ⟨g, hg⟩ := exists_sq_eq_a_of_data_Idx4 D hk hρpar hfix' hBC hC hrel hL hH hcS hncyc
  obtain ⟨E, hE0, hE1, hE2⟩ := exists_torusBasis_idx4_of_data D hk hBC hC hrel hL hH hcS hρpar
    hρa hfix' hncyc hK0 hK1 hK2 hg
  have hh : conjBy (hL D.ρ_mem_L) g * conjBy (hL D.ρ_mem_L) g = ⟨D.b, hBC D.b.2⟩ := by
    rw [← conjBy_mul, hg]
    apply Subtype.ext
    have h := congrArg Subtype.val (conjBy_ρ_a_of_data D hρa)
    simpa [conjBy_val] using h
  have hE := E_incl4 D hBC hK0 hK1 hK2 hg hh E hE0 hE1 hE2
  have hV := agreeB4_of_data D hBC hL hK0 hK1 hK2 E hE D.uv_mem_L D.uv_mem (ec_conj_uv_data D)
    (A' := τ₁.action.φuv) (matAct_incl4 hK0 hK1 hK2 _ _ cV)
  have hW := agreeB4_of_data D hBC hL hK0 hK1 hK2 E hE D.t_mem_L D.t_mem (ec_conj_t_data D)
    (A' := τ₁.action.φt) (matAct_incl4 hK0 hK1 hK2 _ _ cW)
  have hU := agreeB4_of_data D hBC hL hK0 hK1 hK2 E hE D.u_mem_L D.u_mem (ec_conj_u_data D)
    (A' := τ₁.action.φu) (matAct_incl4 hK0 hK1 hK2 _ _ cU)
  have hR := agreeB4_of_data D hBC hL hK0 hK1 hK2 E hE D.ρ_mem_L D.ρ_mem (ec_conj_ρ_data D)
    (A' := τ₁.action.φρ) (matAct_incl4 hK0 hK1 hK2 _ _ cR)
  have hk1 : ∀ j, 1 ≤ τ₁.k j := forall_fin_three (by rw [hK0]; exact hk 0) (by rw [hK1]; omega)
    (by rw [hK2]; omega)
  obtain ⟨φ, h1 | h2⟩ := classify_idx4 hk1 (by rw [hK1]; have := hk 1; omega)
    (by rw [hK2]; have := hk 2; omega) τ₁.action.rels hP hT (conjTorusIdx4_rels E D hL)
    hV hW hU hR
  · exact Or.inl (hasStrothTypeOver_of_basisChange D hL τ₁ E φ h1)
  · exact Or.inr ⟨E, φ, h2⟩

theorem hasStrothType_or_of_index_four_of_data (D : StrothTypeData B τ) (hBC : B ≤ C)
    (hC : C ≤ Subgroup.centralizer (B : Set S)) (hrel : Nat.card C = 4 * Nat.card B)
    (hL : D.L ≤ Subgroup.normalizer C) (hH : NoInvolutionsCentralizing S' B) (hcS : C ≤ S')
    (hk : ∀ i, 1 ≤ τ.k i)
    (hρpar : ∀ v, parityTorus _ hk (τ.action.φρ v) = rhoBar300 (parityTorus _ hk v))
    (hρa : τ.action.φρ (gen τ.k 1) = gen τ.k 2)
    (hfix : ∀ v : Torus τ.k, τ.action.φρ v = v → τ.action.φt v = v → v = 0)
    (hfix4 : ∀ v : Torus τ.k, (∃ z, 4 • z = τ.action.φρ v - v) →
      (∃ z, 4 • z = τ.action.φt v - v) → ∃ z, 2 • z = v)
    (τ₁ : StrothTypeIndex) (hK0 : τ₁.k 0 = τ.k 0) (hK1 : τ₁.k 1 = τ.k 1 + 1)
    (hK2 : τ₁.k 2 = τ.k 2 + 1) (A' : SigmaFourAction τ₁.k)
    (hP : Profile4 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ)
    (hT : Twist4 τ₁.k τ₁.action.φuv τ₁.action.φt τ₁.action.φu τ₁.action.φρ A'.φuv A'.φt A'.φu
      A'.φρ)
    (cV : MatEq τ₁.k (τ₁.action.uv * diag4) (diag4 * τ.action.uv))
    (cW : MatEq τ₁.k (τ₁.action.t * diag4) (diag4 * τ.action.t))
    (cU : MatEq τ₁.k (τ₁.action.u * diag4) (diag4 * τ.action.u))
    (cR : MatEq τ₁.k (τ₁.action.ρ * diag4) (diag4 * τ.action.ρ)) :
    HasStrothType C τ₁ ∨ ∃ (E : Torus τ₁.k ≃+ Additive C) (φ : Torus τ₁.k ≃+ Torus τ₁.k),
      ∀ j, φ.symm (conjTorusIdx4 E (hL D.uv_mem_L) (φ (gen τ₁.k j))) = A'.φuv (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.t_mem_L) (φ (gen τ₁.k j))) = A'.φt (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.u_mem_L) (φ (gen τ₁.k j))) = A'.φu (gen τ₁.k j) ∧
        φ.symm (conjTorusIdx4 E (hL D.ρ_mem_L) (φ (gen τ₁.k j))) = A'.φρ (gen τ₁.k j) :=
  (hasStrothTypeOver_or_of_index_four_of_data D hBC hC hrel hL hH hcS hk hρpar hρa hfix hfix4 τ₁ hK0
    hK1 hK2 A' hP hT cV cW cU cR).imp_left (·.hasStrothType)

end CFSG.CGT.Stroth77
