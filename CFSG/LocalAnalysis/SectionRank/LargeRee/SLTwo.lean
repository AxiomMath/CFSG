module

public import CFSG.LieType.Simplicity.ReeCells
public import CFSG.LieType.Ree.ReeTorus
public import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
public import CFSG.LieType.Steinberg.Adjoint.Presentation
public import CFSG.LieType.Chevalley.OrbitGroups

public section

namespace CFSG.SectionRank.LargeRee

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Simplicity
  CFSG.LieType.Steinberg Matrix

section Ordinary

variable {τ : Tag} {K : Type} [Field K]

theorem eltElement_neg_simpleRoot
    (i : Fin τ.rank) (c : K) :
    (rootOperatorFamily τ).eltElement (-simpleRoot τ i) c = yElement i c :=
  Subtype.ext ((rootOperatorFamily τ).eltUnit_neg_simple i c)

theorem yElement_mem_X
    (i : Fin τ.rank) (c : K) :
    yElement i c ∈ (nativeRootSubgroups τ K).X (-simpleRoot τ i) :=
  ((nativeRootSubgroups τ K).mem_neg_simple i _).2 ⟨c, rfl⟩

theorem exists_sl2_hom_F4
    (i : Fin ReeTag.F4.tag.rank) :
    ∃ φ : SpecialLinearGroup (Fin 2) K →* adjointGroup ReeTag.F4.tag K, Function.Injective φ ∧
      (∀ c, φ (sl2Upper c) = xElement i c) ∧ ∀ c, φ (sl2Lower c) = yElement i c := by
  obtain ⟨k, hk, -⟩ := Adjoint.neighbour_F4 i
  have hk' : ReeTag.F4.tag.cartan i k = -1 := hk
  obtain ⟨φ, hφ, hx, hy⟩ := Adjoint.exists_sl2_hom (K := K) (rootOperatorFamily ReeTag.F4.tag)
    hk'
  exact ⟨φ, hφ, fun c => (hx c).trans (eltElement_simpleRoot i c),
    fun c => (hy c).trans (eltElement_neg_simpleRoot i c)⟩

theorem reflect_single_of_cartan_eq_zero {i j : Fin τ.rank} (h : τ.cartan j i = 0) :
    reflect τ j (Pi.single i 1) = Pi.single i 1 := by
  rw [reflect, Finset.sum_eq_single i (fun k _ hk => by simp [hk]) (by simp)]
  simp [h]

theorem simple_smul_simpleRoot_of_cartan_eq_zero {i j : Fin τ.rank} (h : τ.cartan j i = 0) :
    simple τ j • simpleRoot τ i = simpleRoot τ i :=
  Subtype.ext (by rw [coe_smul_root, simple_smul]; exact reflect_single_of_cartan_eq_zero h)

theorem simple_smul_neg_simpleRoot_of_cartan_eq_zero {i j : Fin τ.rank}
    (h : τ.cartan j i = 0) : simple τ j • (-simpleRoot τ i) = -simpleRoot τ i := by
  rw [smul_neg_root, simple_smul_simpleRoot_of_cartan_eq_zero h]

theorem simple_smul_neg_simpleRoot_self (j : Fin τ.rank) :
    simple τ j • (-simpleRoot τ j) = simpleRoot τ j := by
  apply Subtype.ext
  rw [coe_smul_root, coe_neg_root, smul_neg, simple_smul]
  change -reflect τ j (Pi.single j 1) = Pi.single j 1
  rw [reflect_single_self, neg_neg]

theorem weylElement_conj_mem_X
    (j : Fin τ.rank) {α : Root τ} {y : adjointGroup τ K}
    (hy : y ∈ (nativeRootSubgroups τ K).X α) :
    weylElement τ K j * y * (weylElement τ K j)⁻¹ ∈
      (nativeRootSubgroups τ K).X (simple τ j • α) := by
  rw [← (nativeRootSubgroups τ K).conj_weyl j α]
  exact ⟨y, hy, rfl⟩

theorem commute_of_commute_conj {G : Type*} [Group G] (g : G) {x y : G}
    (h : Commute (g * x * g⁻¹) (g * y * g⁻¹)) : Commute x y := by
  have := h.map (MulAut.conj g⁻¹).toMonoidHom
  simpa [MulAut.conj_apply, mul_assoc] using this

theorem commute_of_orthogonal
    {i j : Fin τ.rank} (hij : i ≠ j) (hc : τ.cartan i j = 0)
    (hc' : τ.cartan j i = 0) (c d : K) :
    Commute (xElement i c) (xElement j d) ∧ Commute (xElement i c) (yElement j d) ∧
      Commute (yElement i c) (xElement j d) ∧ Commute (yElement i c) (yElement j d) := by
  have hxx : ∀ c d : K, Commute (xElement i c) (xElement j d) := fun c d =>
    commute_of_mem_simple hij hc (xElement_mem_X i c) (xElement_mem_X j d)
  have hxy : ∀ c d : K, Commute (xElement i c) (yElement j d) := by
    intro c d
    refine commute_of_commute_conj (weylElement τ K j) ?_
    have h1 := weylElement_conj_mem_X (K := K) j (xElement_mem_X i c)
    have h2 := weylElement_conj_mem_X (K := K) j (yElement_mem_X j d)
    rw [simple_smul_simpleRoot_of_cartan_eq_zero hc'] at h1
    rw [simple_smul_neg_simpleRoot_self] at h2
    exact commute_of_mem_simple hij hc h1 h2
  have hyx : ∀ c d : K, Commute (yElement i c) (xElement j d) := by
    intro c d
    refine commute_of_commute_conj (weylElement τ K i) ?_
    have h1 := weylElement_conj_mem_X (K := K) i (yElement_mem_X i c)
    have h2 := weylElement_conj_mem_X (K := K) i (xElement_mem_X j d)
    rw [simple_smul_neg_simpleRoot_self] at h1
    rw [simple_smul_simpleRoot_of_cartan_eq_zero hc] at h2
    exact commute_of_mem_simple hij hc h1 h2
  refine ⟨hxx c d, hxy c d, hyx c d, ?_⟩
  refine commute_of_commute_conj (weylElement τ K j) ?_
  have h1 := weylElement_conj_mem_X (K := K) j (yElement_mem_X i c)
  have h2 := weylElement_conj_mem_X (K := K) j (yElement_mem_X j d)
  rw [simple_smul_neg_simpleRoot_of_cartan_eq_zero hc'] at h1
  rw [simple_smul_neg_simpleRoot_self] at h2
  obtain ⟨c', hc'⟩ := ((nativeRootSubgroups τ K).mem_neg_simple i _).1 h1
  obtain ⟨d', hd'⟩ := ((nativeRootSubgroups τ K).mem_simple j _).1 h2
  have e1 : weylElement τ K j * yElement i c * (weylElement τ K j)⁻¹ = yElement i c' :=
    Subtype.ext hc'
  have e2 : weylElement τ K j * yElement j d * (weylElement τ K j)⁻¹ = xElement j d' :=
    Subtype.ext hd'
  rw [e1, e2]
  exact hyx c' d'

end Ordinary

section Matrices

variable {K : Type} [Field K]

@[expose] def sl2Diag (t : Kˣ) : SpecialLinearGroup (Fin 2) K :=
  ⟨!![(t : K), 0; 0, ((t⁻¹ : Kˣ) : K)], by simp [det_fin_two]⟩

@[expose] def sl2Weyl : SpecialLinearGroup (Fin 2) K :=
  ⟨!![0, 1; -1, 0], by simp [det_fin_two]⟩

theorem sl2Diag_eq (t : Kˣ) :
    sl2Diag t = sl2Upper (t : K) * sl2Lower (-((t⁻¹ : Kˣ) : K)) * sl2Upper (t : K) *
      (sl2Upper (-1) * sl2Lower 1 * sl2Upper (-1)) := by
  have ht : (t : K) * ((t⁻¹ : Kˣ) : K) = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [sl2Diag, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2Weyl_eq : sl2Weyl = sl2Upper (1 : K) * sl2Lower (-1) * sl2Upper 1 := by
  refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
  simp only [sl2Weyl, Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower]
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

theorem sl2_commute_of_gens
    {G : Type*} [Group G] (φ : SpecialLinearGroup (Fin 2) K →* G)
    {y : G} (hx : ∀ c, Commute (φ (sl2Upper c)) y) (hy : ∀ c, Commute (φ (sl2Lower c)) y)
    (g : SpecialLinearGroup (Fin 2) K) : Commute (φ g) y := by
  have hg : g ∈ (EvenCover.sl2Rels K).sub := by rw [EvenCover.sl2Rels_sub]; trivial
  rw [RankOneRels.sub] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx' =>
    rcases hx' with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · exact hx c
    · exact hy c
  | one => rw [map_one]; exact Commute.one_left y
  | mul x z _ _ h1 h2 => rw [map_mul]; exact h1.mul_left h2
  | inv x _ h => rw [map_inv]; exact h.inv_left

end Matrices

section RankOne

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}

abbrev ix (i : Fin 4) : Fin ReeTag.F4.tag.rank :=
  Fin.cast rfl i

theorem perm_ix_zero : ReeTag.F4.perm (ix 0) = ix 3 := by decide

theorem perm_ix_three : ReeTag.F4.perm (ix 3) = ix 0 := by decide

theorem relationExponent_ix_zero : ReeTag.F4.relationExponent a (ix 0) = 2 ^ a := by
  simp only [ReeTag.relationExponent, ReeTag.prime]
  exact ite_eq_left_iff.2 fun h => absurd (by decide) h

theorem relationExponent_ix_three : ReeTag.F4.relationExponent a (ix 3) = 2 ^ (a + 1) := by
  simp only [ReeTag.relationExponent, ReeTag.prime]
  exact ite_eq_right_iff.2 fun h => absurd h (by decide)

theorem reeOrbitWord_ix_zero : ReeTag.F4.reeOrbitWord (ix 0) = [ix 0, ix 3] := rfl

theorem cartan_ix_zero_three : ReeTag.F4.tag.cartan (ix 0) (ix 3) = 0 := by decide

theorem cartan_ix_three_zero : ReeTag.F4.tag.cartan (ix 3) (ix 0) = 0 := by decide

theorem supportCheck_blockElt_zero :
    supportCheck ReeTag.F4.tag [ix 0, ix 3] [ix 0, ix 3] = true := by
  decide +kernel

theorem height_blockElt_zero_smul_zero :
    height (ReeTag.F4.blockElt (ix 0) • simpleRoot ReeTag.F4.tag (ix 0)).1 < 0 := by
  rw [coe_smul_root, CFSG.LieType.Ree.wordProd_smul]
  decide +kernel

theorem height_blockElt_zero_smul_three :
    height (ReeTag.F4.blockElt (ix 0) • simpleRoot ReeTag.F4.tag (ix 3)).1 < 0 := by
  rw [coe_smul_root, CFSG.LieType.Ree.wordProd_smul]
  decide +kernel

omit [CharP K ReeTag.F4.prime] in
theorem pow_pow_eq_self (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (c : K) :
    (c ^ 2 ^ a) ^ 2 ^ (a + 1) = c := by
  have := Fintype.ofFinite K
  rw [← pow_mul, ← pow_add, show a + (a + 1) = 2 * a + 1 by ring]
  have h := FiniteField.pow_card c
  rwa [← Nat.card_eq_fintype_card, hK] at h

omit [CharP K ReeTag.F4.prime] in
theorem pow_pow_eq_self' (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) (c : K) :
    (c ^ 2 ^ (a + 1)) ^ 2 ^ a = c := by
  rw [← pow_mul, mul_comm, pow_mul]
  exact pow_pow_eq_self hK c

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem map_sl2Diag_eq_torusElement
    {τ : Tag} {i : Fin τ.rank}
    {φ : SpecialLinearGroup (Fin 2) K →* adjointGroup τ K}
    (hx : ∀ c, φ (sl2Upper c) = xElement i c) (hy : ∀ c, φ (sl2Lower c) = yElement i c)
    (t : Kˣ) : φ (sl2Diag t) = torusElement τ K i t := by
  simp only [sl2Diag_eq, map_mul, hx, hy]
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, torusElement, torusElt, coe_weylElt]
  simp [xElement, yElement, coe_xUnit, coe_yUnit, mul_assoc]

omit [Finite K] [CharP K ReeTag.F4.prime] in
theorem map_sl2Weyl_eq_weylElement
    {τ : Tag} {i : Fin τ.rank}
    {φ : SpecialLinearGroup (Fin 2) K →* adjointGroup τ K}
    (hx : ∀ c, φ (sl2Upper c) = xElement i c) (hy : ∀ c, φ (sl2Lower c) = yElement i c) :
    φ sl2Weyl = weylElement τ K i := by
  simp only [sl2Weyl_eq, map_mul, hx, hy]
  apply Subtype.ext
  apply Units.ext
  change _ = ((weylElt τ K i 1 : (Module.End K (RootModule τ K))ˣ) : Module.End K (RootModule τ K))
  rw [coe_weylElt]
  simp [xElement, yElement, coe_xUnit, coe_yUnit]

theorem exists_sl2_rankOne
    (hK : Nat.card K = ReeTag.F4.prime ^ (2 * a + 1)) :
    ∃ ψ : SpecialLinearGroup (Fin 2) K →* reeFixed ReeTag.F4 K a, Function.Injective ψ ∧
      (∀ c, (ψ (sl2Upper c) : adjointGroup ReeTag.F4.tag K) =
        xElement (ix 0) c * xElement (ix 3) (c ^ 2 ^ a)) ∧
      (∀ c, (ψ (sl2Lower c) : adjointGroup ReeTag.F4.tag K) =
        yElement (ix 0) c * yElement (ix 3) (c ^ 2 ^ a)) ∧
      (∀ c, (ψ (sl2Upper c) : adjointGroup ReeTag.F4.tag K) ∈
        Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (ix 0))) ∧
      (∀ x ∈ reeFixed ReeTag.F4 K a, x ∈ Uminus ReeTag.F4.tag K (ReeTag.F4.blockElt (ix 0)) →
        ∃ c, (ψ (sl2Upper c) : adjointGroup ReeTag.F4.tag K) = x) ∧
      (∀ t : Kˣ, (ψ (sl2Diag t) : adjointGroup ReeTag.F4.tag K) = ReeTag.F4.reeTorus a (ix 0) t) ∧
      (ψ sl2Weyl : adjointGroup ReeTag.F4.tag K) =
        nrep ReeTag.F4.tag K (ReeTag.F4.blockElt (ix 0)) := by
  have hexp : ExpChar K 2 := by
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    exact ExpChar.prime Nat.prime_two
  obtain ⟨φ₀, hφ₀, hx₀, hy₀⟩ := exists_sl2_hom_F4 (K := K) (ix 0)
  obtain ⟨φ₃, -, hx₃, hy₃⟩ := exists_sl2_hom_F4 (K := K) (ix 3)
  set fr : SpecialLinearGroup (Fin 2) K →* SpecialLinearGroup (Fin 2) K :=
    SpecialLinearGroup.map (iterateFrobenius K 2 a) with hfr
  have hfrU : ∀ c, fr (sl2Upper c) = sl2Upper (c ^ 2 ^ a) := fun c => by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    change (sl2Upper c : Matrix (Fin 2) (Fin 2) K).map (iterateFrobenius K 2 a) i j = _
    rw [Matrix.map_apply, coe_sl2Upper, coe_sl2Upper, iterateFrobenius_def]
    fin_cases i <;> fin_cases j <;> simp
  have hfrL : ∀ c, fr (sl2Lower c) = sl2Lower (c ^ 2 ^ a) := fun c => by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    change (sl2Lower c : Matrix (Fin 2) (Fin 2) K).map (iterateFrobenius K 2 a) i j = _
    rw [Matrix.map_apply, coe_sl2Lower, coe_sl2Lower, iterateFrobenius_def]
    fin_cases i <;> fin_cases j <;> simp
  have horth := fun c d => commute_of_orthogonal (K := K) (τ := ReeTag.F4.tag)
    (i := ix 0) (j := ix 3) (by decide) cartan_ix_zero_three cartan_ix_three_zero c d
  have hxx := fun c d => (horth c d).1
  have hxy := fun c d => (horth c d).2.1
  have hyx := fun c d => (horth c d).2.2.1
  have hyy := fun c d => (horth c d).2.2.2
  have hcomm : ∀ g h, Commute (φ₀ g) (φ₃ h) := by
    have h1 : ∀ c h, Commute (xElement (ix 0) c) (φ₃ h) ∧ Commute (yElement (ix 0) c) (φ₃ h) :=
      fun c h => ⟨(sl2_commute_of_gens φ₃ (fun d => by rw [hx₃]; exact (hxx c d).symm)
        (fun d => by rw [hy₃]; exact (hxy c d).symm) h).symm,
        (sl2_commute_of_gens φ₃ (fun d => by rw [hx₃]; exact (hyx c d).symm)
        (fun d => by rw [hy₃]; exact (hyy c d).symm) h).symm⟩
    intro g h
    exact sl2_commute_of_gens φ₀ (fun c => by rw [hx₀]; exact (h1 c h).1)
      (fun c => by rw [hy₀]; exact (h1 c h).2) g
  let ψ' : SpecialLinearGroup (Fin 2) K →* adjointGroup ReeTag.F4.tag K :=
    { toFun := fun g => φ₀ g * φ₃ (fr g)
      map_one' := by simp only [map_one, mul_one]
      map_mul' := fun g h => by
        simp only [map_mul]
        rw [mul_assoc (φ₀ g), ← mul_assoc (φ₀ h), (hcomm h (fr g)).eq]
        group }
  have hψ' : ∀ g, ψ' g = φ₀ g * φ₃ (fr g) := fun _ => rfl
  have hψU : ∀ c, ψ' (sl2Upper c) = xElement (ix 0) c * xElement (ix 3) (c ^ 2 ^ a) := fun c => by
    rw [hψ', hfrU, hx₀, hx₃]
  have hψL : ∀ c, ψ' (sl2Lower c) = yElement (ix 0) c * yElement (ix 3) (c ^ 2 ^ a) := fun c => by
    rw [hψ', hfrL, hy₀, hy₃]
  have hF : ∀ g, ReeTag.F4.reeAut K a (ψ' g) = ψ' g := by
    have h : (ReeTag.F4.reeAut K a).toMonoidHom.comp ψ' = ψ' := by
      refine EvenCover.sl2_hom_ext (fun c => ?_) (fun c => ?_)
      · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψU, map_mul, ReeTag.reeAut_xElement,
          ReeTag.reeAut_xElement, perm_ix_zero, perm_ix_three, relationExponent_ix_zero,
          relationExponent_ix_three, pow_pow_eq_self hK]
        exact (hxx c (c ^ 2 ^ a)).symm.eq
      · rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hψL, map_mul, ReeTag.reeAut_yElement,
          ReeTag.reeAut_yElement, perm_ix_zero, perm_ix_three, relationExponent_ix_zero,
          relationExponent_ix_three, pow_pow_eq_self hK]
        exact (hyy c (c ^ 2 ^ a)).symm.eq
    exact fun g => congrArg (· g) h
  let ψ : SpecialLinearGroup (Fin 2) K →* reeFixed ReeTag.F4 K a :=
    ψ'.codRestrict _ fun g => (mem_reeFixed ReeTag.F4 K a).2 (hF g)
  have hψ : ∀ g, (ψ g : adjointGroup ReeTag.F4.tag K) = ψ' g := fun _ => rfl
  refine ⟨ψ, ?_, fun c => by rw [hψ, hψU], fun c => by rw [hψ, hψL], fun c => ?_,
    fun x hxF hx => ?_, fun t => ?_, ?_⟩
  ·
    rw [injective_iff_map_eq_one]
    intro g hg
    have hg' : φ₀ g = (φ₃ (fr g))⁻¹ := eq_inv_of_mul_eq_one_left (congrArg Subtype.val hg)
    have hcen : g ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply hφ₀
      rw [map_mul, map_mul, hg']
      exact ((hcomm h (fr g)).inv_right).eq
    obtain ⟨r, hr, hrg⟩ := (Matrix.SpecialLinearGroup.mem_center_iff).1 hcen
    rw [Fintype.card_fin] at hr
    have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
    have hr1 : r = 1 := CharTwo.sq_inj.1 (by rw [hr, one_pow])
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    rw [← hrg, hr1]
    simp
  ·
    rw [hψ, hψU]
    exact mul_mem (mem_Uminus_of_mem_X (height_simpleRoot_pos _)
      height_blockElt_zero_smul_zero (xElement_mem_X _ c))
      (mem_Uminus_of_mem_X (height_simpleRoot_pos _) height_blockElt_zero_smul_three
        (xElement_mem_X _ _))
  ·
    have hle := Uminus_le_of_supportCheck K supportCheck_blockElt_zero
    have hx' : x ∈ (nativeRootSubgroups ReeTag.F4.tag K).X (simpleRoot ReeTag.F4.tag (ix 0)) ⊔
        (nativeRootSubgroups ReeTag.F4.tag K).X (simpleRoot ReeTag.F4.tag (ix 3)) := by
      have hle2 : (⨆ (j : Fin ReeTag.F4.tag.rank) (_ : j ∈ [ix 0, ix 3]),
          (nativeRootSubgroups ReeTag.F4.tag K).X (simpleRoot ReeTag.F4.tag j)) ≤
          (nativeRootSubgroups ReeTag.F4.tag K).X (simpleRoot ReeTag.F4.tag (ix 0)) ⊔
            (nativeRootSubgroups ReeTag.F4.tag K).X (simpleRoot ReeTag.F4.tag (ix 3)) := by
        refine iSup₂_le fun j hj => ?_
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl
        · exact le_sup_left
        · exact le_sup_right
      exact hle2 (hle hx)
    obtain ⟨c, d, rfl⟩ := exists_eq_xElement_mul_of_mem_sup (by decide) cartan_ix_zero_three hx'
    have hFx := (mem_reeFixed ReeTag.F4 K a).1 hxF
    rw [map_mul, ReeTag.reeAut_xElement, ReeTag.reeAut_xElement, perm_ix_zero, perm_ix_three,
      relationExponent_ix_zero, relationExponent_ix_three,
      ← (hxx (d ^ 2 ^ (a + 1)) (c ^ 2 ^ a)).eq] at hFx
    obtain ⟨h1, h2⟩ := eq_of_xElement_mul_xElement_eq (by decide) hFx
    refine ⟨c, ?_⟩
    rw [hψ, hψU, h2]
  ·
    rw [hψ, hψ', map_sl2Diag_eq_torusElement hx₀ hy₀]
    have hd : fr (sl2Diag t) = sl2Diag (t ^ 2 ^ a) := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      change ((sl2Diag t : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map
        (iterateFrobenius K 2 a) i j = _
      rw [Matrix.map_apply, iterateFrobenius_def]
      fin_cases i <;> fin_cases j <;> simp [sl2Diag]
    rw [hd, map_sl2Diag_eq_torusElement hx₃ hy₃]
    rfl
  ·
    rw [hψ, hψ', map_sl2Weyl_eq_weylElement hx₀ hy₀]
    have hw : fr sl2Weyl = sl2Weyl := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      change ((sl2Weyl : SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).map
        (iterateFrobenius K 2 a) i j = _
      rw [Matrix.map_apply, iterateFrobenius_def]
      have : CharP K 2 := ‹CharP K ReeTag.F4.prime›
      fin_cases i <;> fin_cases j <;> simp [sl2Weyl, CharTwo.neg_eq]
    rw [hw, map_sl2Weyl_eq_weylElement hx₃ hy₃, ReeTag.blockElt,
      nrep_eq_prod ReeTag.F4.tag K (isReduced_reeOrbitWord ReeTag.F4 (ix 0)), reeOrbitWord_ix_zero]
    simp

end RankOne

end CFSG.SectionRank.LargeRee
