module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSp48Aut

public section

namespace CFSG.AGLEmbedding.KFactProofs.Sp48

open CFSG.Quasithin CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.QuasithinUnique.Lin2.Five (tauAut projEquiv)

theorem frobE_ne_one : frobE ≠ 1 := by
  intro h
  have := congrArg (fun τ : GF8 ≃+* GF8 => τ (GF8.ofNat' 2)) h
  simp only [frobE_apply] at this
  revert this
  decide

theorem frob_not_inner (h : Sp8) : fr ≠ MulAut.conj h := by
  intro hfr
  have h1 := congrArg (MulAut.congr piP) hfr
  rw [show fr = fieldSp 2 GF8 frobE from rfl, congr_piP_fieldSp,
    CFSG.ComponentClassification.OuterAutomorphisms.congr_conj] at h1
  exact frobE_ne_one (CFSG.QuasithinUnique.Lin2.Five.fieldAut_eq_one_of_mem_inner (σ := frobE)
    ⟨piP h, h1.symm⟩)

theorem card_outer_le : Nat.card (Outer (StatedProj (StatedSp 2 GF8))) ≤ 6 := by
  have hR : Nat.card (GF8 ≃+* GF8) = 3 :=
    (card_ringAut_and_isCyclic Nat.prime_two GF8 (by rw [card_gf8]; norm_num)).1
  have : Finite (GF8 ≃+* GF8) := Nat.finite_of_card_ne_zero (by rw [hR]; norm_num)
  set q := QuotientGroup.mk' (inner (StatedProj (StatedSp 2 GF8))) with hq
  have hsurj : Function.Surjective
      (fun p : (GF8 ≃+* GF8) × Fin 2 =>
        q (fieldAut 2 GF8 p.1 * tauAut ^ (p.2 : ℕ))) := by
    intro x
    obtain ⟨α, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨A, σ, ε, hε, rfl⟩ :=
      CFSG.RankThree.PartTwo.KFacts.exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow α
    refine ⟨(σ, ⟨ε, by omega⟩), ?_⟩
    have hc : q (conjAut 2 _ A) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr
        (CFSG.RankThree.PartTwo.KFacts.conjAut_mem_inner_of_charTwo A)
    change q (fieldAut 2 _ σ * tauAut ^ ε) = q (conjAut 2 _ A * fieldAut 2 _ σ * tauAut ^ ε)
    rw [mul_assoc, map_mul q (conjAut 2 _ A), hc, one_mul]
  have h1 := Nat.card_le_card_of_surjective _ hsurj
  rwa [Nat.card_prod, hR, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin] at h1

section Emb

variable {Y : Type} [Group Y] {K : Subgroup Y} [K.Normal] {eK : K ≃* Sp8}
  (hC : Subgroup.centralizer (K : Set Y) = ⊥)

include hC in
theorem exists_frob {y : Y} (hy : y ∉ K) {m : ℕ} (hy3 : y ^ (3 ^ m) = 1) :
    ∃ φ : Y, adHom K eK φ = fr ∧ φ ^ 3 = 1 ∧ φ ∉ K := by
  have hα : (adHom K eK y) ^ (3 ^ m) = 1 := by rw [← map_pow, hy3, map_one]
  obtain ⟨g, σ, hgσ⟩ := exists_conj_fieldSp hα
  have hg : adHom K eK ((eK.symm g : K) : Y) = MulAut.conj g := by
    rw [adHom_coe, MulEquiv.apply_symm_apply]
  have hfr3 : fr ^ 3 = 1 := fr_pow_three
  have key : ∀ φ : Y, adHom K eK φ = fr → φ ^ 3 = 1 ∧ φ ∉ K := fun φ hφ => by
    refine ⟨adHom_injective hC (by rw [map_pow, hφ, hfr3, map_one]), fun hmem => ?_⟩
    have := adHom_coe (eK := eK) ⟨φ, hmem⟩
    rw [hφ] at this
    exact frob_not_inner _ this
  rcases ringAut_gf8 σ with rfl | rfl | rfl
  · exfalso
    apply hy
    have : adHom K eK y = adHom K eK ((eK.symm g : K) : Y) := by
      rw [hgσ, hg, map_one, mul_one]
    rw [adHom_injective hC this]
    exact (eK.symm g).2
  · refine ⟨((eK.symm g : K) : Y)⁻¹ * y, ?_⟩
    have : adHom K eK (((eK.symm g : K) : Y)⁻¹ * y) = fr := by
      rw [map_mul, map_inv, hg, hgσ]
      show (MulAut.conj g)⁻¹ * (MulAut.conj g * fr) = fr
      group
    exact ⟨this, key _ this⟩
  · refine ⟨(((eK.symm g : K) : Y)⁻¹ * y) ^ 2, ?_⟩
    have h1 : adHom K eK (((eK.symm g : K) : Y)⁻¹ * y) = fr ^ 2 := by
      rw [map_mul, map_inv, hg, hgσ, map_pow]
      show (MulAut.conj g)⁻¹ * (MulAut.conj g * fr ^ 2) = fr ^ 2
      group
    have : adHom K eK ((((eK.symm g : K) : Y)⁻¹ * y) ^ 2) = fr := by
      rw [map_pow, h1, ← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hfr3, one_mul, pow_one]
    exact ⟨this, key _ this⟩

include hC in
theorem exists_embedding {y : Y} (hy : y ∉ K) {m : ℕ} (hy3 : y ^ (3 ^ m) = 1) :
    ∃ Θ : Hh →* Y, Function.Injective Θ ∧
      (∀ k : Sp8, Θ (SemidirectProduct.inl k) = ((eK.symm k : K) : Y)) ∧
      (∀ x : Hh, Θ x ∈ K ↔ x.right = 1) := by
  obtain ⟨φ, hφ, hφ3, hφK⟩ := exists_frob hC (eK := eK) hy hy3
  let f₂ : Multiplicative (ZMod 3) →* Y :=
    { toFun := fun j => φ ^ (Multiplicative.toAdd j).val
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [toAdd_mul, ZMod.val_add]
        rw [← pow_add, ← pow_eq_pow_mod _ hφ3] }
  let f₁ : Sp8 →* Y := K.subtype.comp eK.symm.toMonoidHom
  have hfr1 : ∀ x, f₁ (fr x) = φ * f₁ x * φ⁻¹ := fun x => by
    have := coe_symm_adHom K eK φ x
    rw [hφ] at this
    exact this
  have hfrn : ∀ (n : ℕ) (x : Sp8), f₁ ((fr ^ n) x) = φ ^ n * f₁ x * (φ ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x; simp
    | succ n ih =>
      intro x
      rw [pow_succ', MulAut.mul_apply, hfr1, ih, pow_succ']
      group
  have hcompat : ∀ j, f₁.comp (phi j).toMonoidHom =
      (MulAut.conj (f₂ j)).toMonoidHom.comp f₁ := fun j => by
    refine MonoidHom.ext fun x => ?_
    show f₁ ((fr ^ (Multiplicative.toAdd j).val) x) = _
    rw [hfrn]
    rfl
  let Θ : Hh →* Y := SemidirectProduct.lift f₁ f₂ hcompat
  have hΘ : ∀ x : Hh, Θ x = f₁ x.left * f₂ x.right := fun x => by
    conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right x]
    rw [map_mul]
    show Θ (SemidirectProduct.inl x.left) * Θ (SemidirectProduct.inr x.right) = _
    rw [SemidirectProduct.lift_inl, SemidirectProduct.lift_inr]
  have hf₁K : ∀ x, f₁ x ∈ K := fun x => (eK.symm x).2
  have hφj : ∀ j : Multiplicative (ZMod 3), f₂ j ∈ K ↔ j = 1 := by
    intro j
    constructor
    · intro hj
      have h3 : (Multiplicative.toAdd j).val < 3 := ZMod.val_lt _
      by_contra hne
      have hv : (Multiplicative.toAdd j).val ≠ 0 := fun h0 => hne (by
        apply Multiplicative.toAdd.injective
        exact (ZMod.val_eq_zero _).1 h0)
      have hj' : φ ^ (Multiplicative.toAdd j).val ∈ K := hj
      generalize (Multiplicative.toAdd j).val = v at hj' h3 hv
      interval_cases v
      · exact hv rfl
      · exact hφK (by simpa using hj')
      · apply hφK
        have : φ = (φ ^ 2) ^ 2 := by
          rw [← pow_mul, pow_eq_pow_mod (2 * 2) hφ3]; norm_num
        rw [this]
        exact K.pow_mem hj' 2
    · rintro rfl
      simp [f₂]
  refine ⟨Θ, ?_, fun k => ?_, fun x => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    rw [hΘ] at hx
    have h1 : f₂ x.right ∈ K := by
      have : f₂ x.right = (f₁ x.left)⁻¹ := eq_inv_of_mul_eq_one_right hx
      rw [this]
      exact K.inv_mem (hf₁K _)
    have h2 : x.right = 1 := (hφj _).1 h1
    rw [h2, map_one, mul_one] at hx
    have h3 : x.left = 1 :=
      (fun a b (h : f₁ a = f₁ b) => eK.symm.injective (Subtype.val_injective h))
        x.left 1 (hx.trans (map_one f₁).symm)
    exact SemidirectProduct.ext h3 h2
  · rw [SemidirectProduct.lift_inl]
    rfl
  · rw [hΘ]
    constructor
    · intro h
      have : f₂ x.right ∈ K := by
        have := K.mul_mem (K.inv_mem (hf₁K x.left)) h
        simpa using this
      exact (hφj _).1 this
    · intro h
      rw [h, map_one, mul_one]
      exact hf₁K _

include eK hC in
theorem index_le_six : K.index ≤ 6 := by
  let ψ : Y →* Outer Sp8 := (QuotientGroup.mk' (inner Sp8)).comp (adHom K eK)
  have hker : ψ.ker = K := by
    ext y
    rw [MonoidHom.mem_ker]
    change QuotientGroup.mk' (inner Sp8) (adHom K eK y) = 1 ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    constructor
    · rintro ⟨g, hg⟩
      have : adHom K eK y = adHom K eK ((eK.symm g : K) : Y) := by
        rw [adHom_coe, MulEquiv.apply_symm_apply, hg]
      rw [adHom_injective hC this]
      exact (eK.symm g).2
    · intro hy
      exact ⟨eK ⟨y, hy⟩, by rw [← adHom_coe (eK := eK) ⟨y, hy⟩]⟩
  have hfin : Finite (Outer Sp8) := inferInstance
  rw [← hker, Subgroup.index_ker]
  calc Nat.card ψ.range ≤ Nat.card (Outer Sp8) :=
        Nat.card_le_card_of_injective _ Subtype.val_injective
    _ = Nat.card (Outer (StatedProj (StatedSp 2 GF8))) :=
        Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence piP).toEquiv
    _ ≤ 6 := card_outer_le

end Emb

end CFSG.AGLEmbedding.KFactProofs.Sp48
