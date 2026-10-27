module

public import CFSG.LocalAnalysis.LyonsUnitaryFour.OrderFifteen.ElementarySixteen
public import CFSG.CharacterTheory.Blocks.InnerProduct

public section

namespace CFSG.LyonsUnitaryFour

open CFSG.TwoRankLowerBound.Helpers
open scoped BigOperators

abbrev SixteenVector : Type := Fin 4 → ZMod 2

noncomputable instance sixteenVector_addChar_fintype : Fintype (AddChar SixteenVector ℂ) :=
  AddChar.instFintype _ _

theorem card_sixteenVector : Fintype.card SixteenVector = 16 := rfl

theorem card_addChar_sixteenVector : Fintype.card (AddChar SixteenVector ℂ) = 16 := by
  convert AddChar.card_eq (α := SixteenVector) <;> rfl

section Coordinates

variable {H : Type*} [Group H] {P : Subgroup H} (e : P ≃* Multiplicative SixteenVector)

@[expose] def sixteenCoord (x : P) : SixteenVector := Multiplicative.toAdd (e x)

theorem sixteenCoord_mul (x y : P) :
    sixteenCoord e (x * y) = sixteenCoord e x + sixteenCoord e y := by
  simp [sixteenCoord]

theorem sixteenCoord_one : sixteenCoord e 1 = 0 := by simp [sixteenCoord]

theorem sixteenCoord_injective : Function.Injective (sixteenCoord e) := fun _ _ h =>
  e.injective (Multiplicative.toAdd.injective h)

theorem sixteenCoord_eq_zero_iff (x : P) : sixteenCoord e x = 0 ↔ x = 1 := by
  rw [← sixteenCoord_one e]
  exact (sixteenCoord_injective e).eq_iff

@[expose] def sixteenPoint (w : SixteenVector) : P := e.symm (Multiplicative.ofAdd w)

@[simp] theorem sixteenCoord_point (w : SixteenVector) : sixteenCoord e (sixteenPoint e w) = w := by
  simp [sixteenCoord, sixteenPoint]

@[simp] theorem sixteenPoint_coord (x : P) : sixteenPoint e (sixteenCoord e x) = x := by
  simp [sixteenCoord, sixteenPoint]

@[expose] def sixteenEquiv : SixteenVector ≃ P where
  toFun := sixteenPoint e
  invFun := sixteenCoord e
  left_inv := sixteenCoord_point e
  right_inv := sixteenPoint_coord e

@[expose] noncomputable def sixteenCharHom (ψ : AddChar SixteenVector ℂ) : P →* ℂ :=
  (AddChar.toMonoidHom ψ).comp e.toMonoidHom

@[expose] noncomputable def sixteenChar (ψ : AddChar SixteenVector ℂ) : P → ℂ :=
  sixteenCharHom e ψ

theorem sixteenChar_apply (ψ : AddChar SixteenVector ℂ) (x : P) :
    sixteenChar e ψ x = ψ (sixteenCoord e x) :=
  rfl

theorem sixteenChar_mul (ψ : AddChar SixteenVector ℂ) (x y : P) :
    sixteenChar e ψ (x * y) = sixteenChar e ψ x * sixteenChar e ψ y :=
  map_mul (sixteenCharHom e ψ) x y

theorem sixteenChar_one (ψ : AddChar SixteenVector ℂ) : sixteenChar e ψ 1 = 1 :=
  map_one (sixteenCharHom e ψ)

theorem sixteenChar_zero : sixteenChar e (0 : AddChar SixteenVector ℂ) = fun _ => 1 := by
  funext x
  rw [sixteenChar_apply]
  exact AddChar.zero_apply _

theorem sixteenChar_injective : Function.Injective (sixteenChar e) := by
  intro ψ φ h
  ext w
  have := congrFun h (sixteenPoint e w)
  rwa [sixteenChar_apply, sixteenChar_apply, sixteenCoord_point] at this

theorem sixteenChar_eq_one_iff (ψ : AddChar SixteenVector ℂ) :
    sixteenChar e ψ = (fun _ => 1) ↔ ψ = 0 := by
  rw [← sixteenChar_zero e]
  exact (sixteenChar_injective e).eq_iff

theorem sixteenChar_mul_self (ψ : AddChar SixteenVector ℂ) (x : P) :
    sixteenChar e ψ x * sixteenChar e ψ x = 1 := by
  rw [← sixteenChar_mul, ← sixteenChar_one e ψ]
  congr 1
  apply e.injective
  rw [map_mul, map_one]
  apply Multiplicative.toAdd.injective
  funext i
  simp only [toAdd_mul, toAdd_one, Pi.add_apply, Pi.zero_apply]
  exact CharTwo.add_self_eq_zero _

theorem sixteenChar_conj (ψ : AddChar SixteenVector ℂ) (x : P) :
    starRingEnd ℂ (sixteenChar e ψ x) = sixteenChar e ψ x := by
  rcases mul_self_eq_one_iff.mp (sixteenChar_mul_self e ψ x) with h | h <;> rw [h] <;> simp

end Coordinates

theorem scalarHomRepresentation_isIrreducible {G : Type*} [Group G] (χ : G →* ℂ) :
    (scalarHomRepresentation χ).IsIrreducible := by
  change IsSimpleOrder (Subrepresentation (scalarHomRepresentation χ))
  have hnontrivial : (⊥ : Subrepresentation (scalarHomRepresentation χ)) ≠ ⊤ := by
    intro hequal
    have hmem : (1 : ℂ) ∈ (⊥ : Subrepresentation (scalarHomRepresentation χ)) := by
      rw [hequal]
      trivial
    exact one_ne_zero hmem
  let : Nontrivial (Subrepresentation (scalarHomRepresentation χ)) := ⟨⟨⊥, ⊤, hnontrivial⟩⟩
  constructor
  intro subrepresentation
  obtain hbot | htop := eq_bot_or_eq_top subrepresentation.toSubmodule
  · exact Or.inl (Subrepresentation.ext hbot)
  · exact Or.inr (Subrepresentation.ext htop)

section Irreducible

variable {H : Type*} [Group H] {P : Subgroup H} (e : P ≃* Multiplicative SixteenVector)

theorem sixteenChar_mem_blocksIrr (ψ : AddChar SixteenVector ℂ) :
    sixteenChar e ψ ∈ CFSG.BlocksIrr P :=
  ⟨ℂ, inferInstance, inferInstance, inferInstance, scalarHomRepresentation (sixteenCharHom e ψ),
    scalarHomRepresentation_isIrreducible _, scalarHomRepresentation_character _⟩

theorem exists_sixteenChar_of_mem_blocksIrr {χ : P → ℂ} (hχ : χ ∈ CFSG.BlocksIrr P) :
    ∃ ψ : AddChar SixteenVector ℂ, χ = sixteenChar e ψ := by
  obtain ⟨V, _, _, _, ρ, hirr, rfl⟩ := hχ
  have hcommP : ∀ a b : P, a * b = b * a := fun a b =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  have : IsMulCommutative P := ⟨⟨hcommP⟩⟩
  have : ρ.IsIrreducible := hirr
  have hdim := Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative ρ
  have hscalar : ∀ x : P, ρ x = (ρ.character x) • LinearMap.id := by
    intro x
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (ρ x)
    have htr : ρ.character x = c := by
      change LinearMap.trace ℂ V (ρ x) = c
      rw [hc, map_smul, LinearMap.trace_id, hdim]
      simp
    rw [htr]
    exact hc
  have hmul : ∀ x y : P, ρ.character (x * y) = ρ.character x * ρ.character y := by
    intro x y
    change LinearMap.trace ℂ V (ρ (x * y)) = _
    rw [map_mul, hscalar x, hscalar y, smul_mul_smul_comm, Module.End.mul_eq_comp,
      LinearMap.id_comp, map_smul, LinearMap.trace_id, hdim]
    simp
  have hone : ρ.character 1 = 1 := by
    rw [Representation.char_one, hdim]
    simp
  let hom : P →* ℂ := { toFun := ρ.character, map_one' := hone, map_mul' := hmul }
  refine ⟨AddChar.toMonoidHomEquiv.symm (hom.comp e.symm.toMonoidHom), ?_⟩
  funext x
  rw [sixteenChar_apply]
  change ρ.character x = hom (e.symm (Multiplicative.ofAdd (sixteenCoord e x)))
  simp [sixteenCoord, hom]

end Irreducible

theorem sum_addChar_sixteenVector (v : SixteenVector) :
    ∑ ψ : AddChar SixteenVector ℂ, ψ v = if v = 0 then 16 else 0 := by
  classical
  have h := AddChar.sum_apply_eq_ite (α := SixteenVector) v
  exact h

section Characters

open scoped Classical

variable {H : Type} [Group H] {P : Subgroup H} (e : P ≃* Multiplicative SixteenVector)

include e in
theorem natCard_sixteen : Nat.card P = 16 := by
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem sum_sixteenChar (x : P) :
    ∑ ψ : AddChar SixteenVector ℂ, sixteenChar e ψ x = if x = 1 then 16 else 0 := by
  have h := sum_addChar_sixteenVector (sixteenCoord e x)
  simp only [sixteenCoord_eq_zero_iff] at h
  exact h

variable [Fintype H]

theorem sum_P_eq_sum_vector (f : P → ℂ) :
    ∑ x : P, f x = ∑ w : SixteenVector, f (sixteenPoint e w) :=
  (Equiv.sum_comp (sixteenEquiv e) f).symm

theorem sum_monoidHom_eq (ν : P →* ℂ) :
    ∑ x : P, ν x = if ν = 1 then (Nat.card P : ℂ) else 0 := by
  split_ifs with hν
  · rw [hν]
    simp [Nat.card_eq_fintype_card]
  · obtain ⟨y, hy⟩ : ∃ y, ν y ≠ 1 := by
      by_contra hall
      push Not at hall
      exact hν (MonoidHom.ext hall)
    have h : ∑ x : P, ν x = ν y * ∑ x : P, ν x := by
      rw [Finset.mul_sum]
      exact (Fintype.sum_equiv (Equiv.mulLeft y) _ _ (fun x => by simp)).symm
    have h' : (1 - ν y) * ∑ x : P, ν x = 0 := by rw [sub_mul, one_mul, ← h, sub_self]
    rcases mul_eq_zero.mp h' with h0 | h0
    · exact absurd (sub_eq_zero.mp h0).symm hy
    · exact h0

theorem blocksInnerProduct_sixteenChar (ψ φ : AddChar SixteenVector ℂ) :
    BlocksInnerProduct (sixteenChar e ψ) (sixteenChar e φ) = if ψ = φ then 1 else 0 := by
  unfold BlocksInnerProduct
  simp_rw [sixteenChar_conj]
  have hsum := sum_monoidHom_eq (sixteenCharHom e ψ * sixteenCharHom e φ)
  have hsum' : ∑ x : P, sixteenChar e ψ x * sixteenChar e φ x =
      ∑ x : P, (sixteenCharHom e ψ * sixteenCharHom e φ) x := rfl
  rw [hsum', hsum, natCard_sixteen (e := e)]
  have hiff : sixteenCharHom e ψ * sixteenCharHom e φ = 1 ↔ ψ = φ := by
    constructor
    · intro h
      apply sixteenChar_injective e
      funext x
      have h1 := DFunLike.congr_fun h x
      change sixteenChar e ψ x * sixteenChar e φ x = 1 at h1
      have h2 := sixteenChar_mul_self e φ x
      have hne : sixteenChar e φ x ≠ 0 := fun h0 => by rw [h0, mul_zero] at h2; norm_num at h2
      exact mul_right_cancel₀ hne (h1.trans h2.symm)
    · rintro rfl
      ext x
      exact sixteenChar_mul_self e ψ x
  by_cases h : ψ = φ
  · rw [ite_eq_left (hiff.mpr h), ite_eq_left h]
    norm_num
  · rw [ite_eq_right (fun h' => h (hiff.mp h')), ite_eq_right h, mul_zero]

omit [Fintype H] in
theorem sixteenChar_mul_eq_inv_mul (ψ : AddChar SixteenVector ℂ) (x y : P) :
    sixteenChar e ψ y * sixteenChar e ψ x = sixteenChar e ψ (y⁻¹ * x) := by
  rw [sixteenChar_mul]
  congr 1
  have h1 := sixteenChar_mul_self e ψ y
  have h2 : sixteenChar e ψ y * sixteenChar e ψ y⁻¹ = 1 := by
    rw [← sixteenChar_mul, mul_inv_cancel, sixteenChar_one]
  have hne : sixteenChar e ψ y ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; norm_num at h1
  exact mul_left_cancel₀ hne (h1.trans h2.symm)

theorem sixteenChar_fourier (f : P → ℂ) (x : P) :
    f x = ∑ ψ : AddChar SixteenVector ℂ,
      BlocksInnerProduct f (sixteenChar e ψ) * sixteenChar e ψ x := by
  unfold BlocksInnerProduct
  simp_rw [sixteenChar_conj]
  have h1 : ∀ ψ : AddChar SixteenVector ℂ,
      (Nat.card P : ℂ)⁻¹ * (∑ y : P, f y * sixteenChar e ψ y) * sixteenChar e ψ x =
        ∑ y : P, (Nat.card P : ℂ)⁻¹ * f y * sixteenChar e ψ (y⁻¹ * x) := by
    intro ψ
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro y _
    rw [← sixteenChar_mul_eq_inv_mul]
    ring
  simp_rw [h1]
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, sum_sixteenChar]
  rw [Finset.sum_eq_single x]
  · rw [inv_mul_cancel, ite_eq_left rfl, natCard_sixteen (e := e)]
    push_cast
    field_simp
  · intro y _ hy
    rw [ite_eq_right (fun h => hy (inv_mul_eq_one.mp h)), mul_zero]
  · intro h
    exact absurd (Finset.mem_univ x) h

end Characters

section Conjugation

variable {H : Type*} [Group H] {P : Subgroup H}

@[expose] def sylowConj (n : Subgroup.normalizer (P : Set H)) (j : ℕ) (θ : P → ℂ) : P → ℂ :=
  fun x => θ (Subgroup.normalizerMonoidHom P (n ^ j)⁻¹ x)

theorem coe_normalizerMonoidHom_inv_pow (n : Subgroup.normalizer (P : Set H)) (j : ℕ) (x : P) :
    ((Subgroup.normalizerMonoidHom P (n ^ j)⁻¹ x : P) : H) = ((n : H) ^ j)⁻¹ * x * (n : H) ^ j := by
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  simp

variable (e : P ≃* Multiplicative SixteenVector)

@[expose] noncomputable def conjAddChar (m : Subgroup.normalizer (P : Set H))
    (ψ : AddChar SixteenVector ℂ) : AddChar SixteenVector ℂ :=
  AddChar.toMonoidHomEquiv.symm (((sixteenCharHom e ψ).comp
    (Subgroup.normalizerMonoidHom P m).toMonoidHom).comp e.symm.toMonoidHom)

theorem sixteenChar_conjAddChar (m : Subgroup.normalizer (P : Set H))
    (ψ : AddChar SixteenVector ℂ) (x : P) :
    sixteenChar e (conjAddChar e m ψ) x = sixteenChar e ψ (Subgroup.normalizerMonoidHom P m x) := by
  rw [sixteenChar_apply, conjAddChar, AddChar.toMonoidHomEquiv_symm_apply]
  simp [sixteenCoord, sixteenChar_apply]
  rfl

theorem sylowConj_sixteenChar (n : Subgroup.normalizer (P : Set H)) (j : ℕ)
    (ψ : AddChar SixteenVector ℂ) :
    sylowConj n j (sixteenChar e ψ) = sixteenChar e (conjAddChar e (n ^ j)⁻¹ ψ) := by
  funext x
  rw [sixteenChar_conjAddChar]
  rfl

theorem conjAddChar_conjAddChar (a b : Subgroup.normalizer (P : Set H))
    (ψ : AddChar SixteenVector ℂ) :
    conjAddChar e a (conjAddChar e b ψ) = conjAddChar e (b * a) ψ := by
  apply sixteenChar_injective e
  funext x
  rw [sixteenChar_conjAddChar, sixteenChar_conjAddChar, sixteenChar_conjAddChar, map_mul]
  rfl

theorem conjAddChar_eq_zero_iff (m : Subgroup.normalizer (P : Set H))
    (ψ : AddChar SixteenVector ℂ) : conjAddChar e m ψ = 0 ↔ ψ = 0 := by
  rw [← sixteenChar_eq_one_iff e, ← sixteenChar_eq_one_iff e]
  constructor
  · intro h
    funext x
    have := congrFun h (Subgroup.normalizerMonoidHom P m⁻¹ x)
    rw [sixteenChar_conjAddChar, ← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one,
      MulAut.one_apply] at this
    exact this
  · intro h
    funext x
    rw [sixteenChar_conjAddChar, h]

theorem iterate_conjAddChar (n : Subgroup.normalizer (P : Set H)) (j : ℕ)
    (ψ : AddChar SixteenVector ℂ) :
    (conjAddChar e n⁻¹)^[j] ψ = conjAddChar e (n ^ j)⁻¹ ψ := by
  induction j with
  | zero =>
    apply sixteenChar_injective e
    funext x
    rw [Function.iterate_zero_apply, sixteenChar_conjAddChar, pow_zero, inv_one, map_one,
      MulAut.one_apply]
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih, conjAddChar_conjAddChar, pow_succ', mul_inv_rev]

variable [Finite H]

theorem conjAddChar_ne_self
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer (P : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = P)
    (n : Subgroup.normalizer (P : Set H)) (hnC : (n : H) ∉ Subgroup.centralizer (P : Set H))
    {ψ : AddChar SixteenVector ℂ} (hψ : ψ ≠ 0) : conjAddChar e n⁻¹ ψ ≠ ψ := by
  intro hfix
  apply hψ
  rw [← sixteenChar_eq_one_iff e]
  have hcommP : ∀ a b : P, a * b = b * a := fun a b =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  set σ := Subgroup.normalizerMonoidHom P n⁻¹ with hσ
  have hσx : ∀ x : P, ((σ x : P) : H) = (n : H)⁻¹ * x * n := by
    intro x
    rw [hσ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    simp
  have hχ : ∀ x : P, sixteenChar e ψ (σ x) = sixteenChar e ψ x := by
    intro x
    rw [← sixteenChar_conjAddChar, hfix]
  set ν : P → P := fun x => x⁻¹ * σ x with hν
  have hνinj : Function.Injective ν := by
    intro x y hxy
    simp only [hν] at hxy
    have hz : σ (y * x⁻¹) = y * x⁻¹ := by
      rw [map_mul, map_inv]
      have h1 : σ x = x * (y⁻¹ * σ y) := by rw [← hxy]; group
      rw [h1]
      calc σ y * (x * (y⁻¹ * σ y))⁻¹ = σ y * ((σ y)⁻¹ * y * x⁻¹) := by group
        _ = y * x⁻¹ := by group
    have hz' : ((n : H)⁻¹ * ((y * x⁻¹ : P) : H) * n) = ((y * x⁻¹ : P) : H) := by
      rw [← hσx, hz]
    have h1 : (y * x⁻¹ : P) = 1 := by
      apply Subtype.ext
      apply eq_one_of_conj_eq_of_generator hidx hirr n.2 hnC (y * x⁻¹).2
      calc (n : H) * ((y * x⁻¹ : P) : H) * (n : H)⁻¹ =
          (n : H) * ((n : H)⁻¹ * ((y * x⁻¹ : P) : H) * n) * (n : H)⁻¹ := by rw [hz']
        _ = ((y * x⁻¹ : P) : H) := by group
    have := mul_inv_eq_one.mp h1
    exact this.symm
  have hνsurj := Finite.surjective_of_injective hνinj
  funext y
  obtain ⟨x, rfl⟩ := hνsurj y
  simp only [hν]
  rw [sixteenChar_mul, hχ x]
  have h1 := sixteenChar_mul_self e ψ x
  have h2 : sixteenChar e ψ x⁻¹ * sixteenChar e ψ x = 1 := by
    rw [← sixteenChar_mul, inv_mul_cancel, sixteenChar_one]
  exact h2

theorem exists_three_sixteenChar_orbits
    (hidx : ((Subgroup.centralizer (P : Set H)).subgroupOf
      (Subgroup.normalizer (P : Set H))).index = 5)
    (hirr : ∀ A : Subgroup H, A ≤ P →
      (∀ n ∈ Subgroup.normalizer (P : Set H), ∀ a ∈ A, n * a * n⁻¹ ∈ A) → A = ⊥ ∨ A = P)
    (n : Subgroup.normalizer (P : Set H)) (hnC : (n : H) ∉ Subgroup.centralizer (P : Set H)) :
    ∃ r : Fin 3 → AddChar SixteenVector ℂ, (∀ i, r i ≠ 0) ∧
      ∀ ψ : AddChar SixteenVector ℂ, ψ ≠ 0 →
        ∃! ik : Fin 3 × Fin 5, ψ = conjAddChar e (n ^ (ik.2 : ℕ))⁻¹ (r ik.1) := by
  classical
  have hXcard : Fintype.card {ψ : AddChar SixteenVector ℂ // ψ ≠ 0} = 15 := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_eq, card_addChar_sixteenVector]
  let f : {ψ : AddChar SixteenVector ℂ // ψ ≠ 0} → {ψ : AddChar SixteenVector ℂ // ψ ≠ 0} :=
    fun ψ => ⟨conjAddChar e n⁻¹ ψ.1, fun h => ψ.2 ((conjAddChar_eq_zero_iff e _ _).mp h)⟩
  have hfiter : ∀ (j : ℕ) (ψ : {ψ : AddChar SixteenVector ℂ // ψ ≠ 0}),
      (f^[j] ψ).1 = conjAddChar e (n ^ j)⁻¹ ψ.1 := by
    intro j
    induction j with
    | zero => intro ψ; rw [Function.iterate_zero_apply, ← iterate_conjAddChar]; rfl
    | succ j ih =>
      intro ψ
      rw [Function.iterate_succ_apply', ← iterate_conjAddChar]
      change conjAddChar e n⁻¹ (f^[j] ψ).1 = _
      rw [ih, iterate_conjAddChar, ← iterate_conjAddChar e n (j + 1), Function.iterate_succ_apply',
        iterate_conjAddChar]
  have h5 : ∀ ψ : {ψ : AddChar SixteenVector ℂ // ψ ≠ 0}, f^[5] ψ = ψ := by
    intro ψ
    apply Subtype.ext
    rw [hfiter]
    apply sixteenChar_injective e
    funext x
    rw [sixteenChar_conjAddChar]
    congr 1
    apply Subtype.ext
    rw [coe_normalizerMonoidHom_inv_pow]
    have hc := (Subgroup.mem_centralizer_iff.mp (pow_five_mem_centralizer hidx n.2)) x x.2
    rw [mul_assoc, hc, ← mul_assoc, inv_mul_cancel, one_mul]
  have hfix : ∀ ψ : {ψ : AddChar SixteenVector ℂ // ψ ≠ 0}, f ψ ≠ ψ := by
    intro ψ h
    exact conjAddChar_ne_self e hidx hirr n hnC ψ.2 (congrArg Subtype.val h)
  obtain ⟨r, hr⟩ := exists_three_free_orbits hXcard f h5 hfix
  refine ⟨fun i => (r i).1, fun i => (r i).2, fun ψ hψ => ?_⟩
  obtain ⟨ik, hik, huniq⟩ := hr ⟨ψ, hψ⟩
  refine ⟨ik, ?_, fun jk hjk => huniq jk ?_⟩
  · have := congrArg Subtype.val hik
    rw [hfiter] at this
    exact this
  · apply Subtype.ext
    rw [hfiter]
    exact hjk

end Conjugation

end CFSG.LyonsUnitaryFour
