module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.HardMathSupport.Timmesfeld.Balance.Basic
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1ThreeKit
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Balance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Co1T
open scoped Matrix

@[expose] def NormF (f : Fin 4 → ZMod 5) : Prop :=
  f = 0 ∨ ∃ p : Fin 4, f p = 1 ∧ ∀ j : Fin 4, j < p → f j = 0

theorem perp_iff (f g : Fin 4 → ZMod 5) (hf : f = 0 ∨ ∃ p : Fin 4, f p = 1) :
    (∀ c : Fin 4 → ZMod 5, f ⬝ᵥ c = 0 → g ⬝ᵥ c = 0) ↔ ∃ t : ZMod 5, g = t • f := by
  constructor
  · intro h
    rcases hf with rfl | ⟨p, hp⟩
    · refine ⟨0, funext fun j => ?_⟩
      have := h (Pi.single j 1) (by simp)
      simpa using this
    · refine ⟨g p, funext fun j => ?_⟩
      have hc : f ⬝ᵥ (Pi.single j (f p) - Pi.single p (f j) : Fin 4 → ZMod 5) = 0 := by
        simp [dotProduct_sub, dotProduct_single]
        ring
      have := h _ hc
      simp [dotProduct_sub, dotProduct_single, hp] at this
      simp only [Pi.smul_apply, smul_eq_mul]
      linear_combination this
  · rintro ⟨t, rfl⟩ c hc
    simp [smul_dotProduct, hc]

theorem exists_functional_of_index_five (S : AddSubgroup (Fin 4 → ZMod 5)) (hS : S.index = 5) :
    ∃ f : Fin 4 → ZMod 5, f ≠ 0 ∧ ∀ c, c ∈ S ↔ f ⬝ᵥ c = 0 := by
  have hsmul : ∀ (k : ZMod 5) (c : Fin 4 → ZMod 5), c ∈ S → k • c ∈ S := by
    intro k c hc
    have hk : k • c = k.val • c := by
      funext i
      simp [nsmul_eq_mul]
    rw [hk]
    exact S.nsmul_mem hc _
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ ∉ S := by
    by_contra h
    push Not at h
    have : S = ⊤ := by
      ext c
      simp [h c]
    rw [this, AddSubgroup.index_top] at hS
    omega
  let Φ : ZMod 5 →+ (Fin 4 → ZMod 5) ⧸ S :=
    (QuotientAddGroup.mk' S).comp
      { toFun := fun k => k • c₀
        map_zero' := zero_smul _ _
        map_add' := fun a b => add_smul a b c₀ }
  have hΦinj : Function.Injective Φ := by
    rw [injective_iff_map_eq_zero]
    intro k hk
    by_contra hk0
    apply hc₀
    have h1 : k • c₀ ∈ S := (QuotientAddGroup.eq_zero_iff _).1 hk
    have h2 := hsmul k⁻¹ _ h1
    rwa [inv_smul_smul₀ hk0] at h2
  have hcard : Nat.card ((Fin 4 → ZMod 5) ⧸ S) = Nat.card (ZMod 5) := by
    rw [Nat.card_zmod]
    exact hS
  have hfin : Finite ((Fin 4 → ZMod 5) ⧸ S) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; simp)
  have hΦbij : Function.Bijective Φ := hΦinj.bijective_of_nat_card_le hcard.le
  let ψ : ((Fin 4 → ZMod 5) ⧸ S) →+ ZMod 5 := (AddEquiv.ofBijective Φ hΦbij).symm.toAddMonoidHom
  let F : (Fin 4 → ZMod 5) →+ ZMod 5 := ψ.comp (QuotientAddGroup.mk' S)
  have hFker : ∀ c, F c = 0 ↔ c ∈ S := by
    intro c
    change (AddEquiv.ofBijective Φ hΦbij).symm (QuotientAddGroup.mk c) = 0 ↔ _
    rw [AddEquiv.map_eq_zero_iff]
    exact QuotientAddGroup.eq_zero_iff c
  have hFc : ∀ c : Fin 4 → ZMod 5, F c = (fun i => F (Pi.single i 1)) ⬝ᵥ c := by
    intro c
    have hc : c = ∑ i, (c i).val • (Pi.single i (1 : ZMod 5) : Fin 4 → ZMod 5) := by
      funext j
      rw [Finset.sum_apply]
      simp only [Pi.smul_apply, Pi.single_apply, smul_ite, smul_zero]
      rw [Finset.sum_ite_eq Finset.univ j (fun i => (c i).val • (1 : ZMod 5))]
      simp [nsmul_eq_mul]
    conv_lhs => rw [hc]
    rw [map_sum]
    simp only [map_nsmul]
    simp only [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val, mul_comm]
  refine ⟨fun i => F (Pi.single i 1), ?_, fun c => ?_⟩
  · intro h
    apply hc₀
    rw [← hFker, hFc, h]
    simp
  · rw [← hFker, hFc]

theorem exists_normF_of_index_five (S : AddSubgroup (Fin 4 → ZMod 5)) (hS : S.index = 5) :
    ∃ f : Fin 4 → ZMod 5, NormF f ∧ f ≠ 0 ∧ ∀ c, c ∈ S ↔ f ⬝ᵥ c = 0 := by
  obtain ⟨f₀, hf₀, hker⟩ := exists_functional_of_index_five S hS
  have hex : ∃ i, f₀ i ≠ 0 := by
    by_contra h
    push Not at h
    exact hf₀ (funext h)
  classical
  set T : Finset (Fin 4) := Finset.univ.filter fun i => f₀ i ≠ 0 with hT
  have hTne : T.Nonempty := by
    obtain ⟨i, hi⟩ := hex
    exact ⟨i, by simp [hT, hi]⟩
  set p : Fin 4 := T.min' hTne with hp
  have hp0 : f₀ p ≠ 0 := by
    have := T.min'_mem hTne
    simpa [hT] using this
  have hpmin : ∀ j : Fin 4, j < p → f₀ j = 0 := by
    intro j hj
    by_contra hne
    have : j ∈ T := by simp [hT, hne]
    exact absurd (T.min'_le j this) (not_le.2 hj)
  have hinv : (f₀ p)⁻¹ * f₀ p = 1 := inv_mul_cancel₀ hp0
  refine ⟨(f₀ p)⁻¹ • f₀, Or.inr ⟨p, ?_, fun j hj => ?_⟩, ?_, fun c => ?_⟩
  · simp only [Pi.smul_apply, smul_eq_mul]
    exact hinv
  · simp [hpmin j hj]
  · intro h
    have := congrFun h p
    simp only [Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
    rw [hinv] at this
    exact one_ne_zero this
  · rw [hker, smul_dotProduct, smul_eq_mul]
    constructor
    · intro h
      rw [h, mul_zero]
    · intro h
      exact (mul_eq_zero.1 h).resolve_left (inv_ne_zero hp0)

section Rec

variable {S : Type*} [Group S] [Finite S] (φ : Multiplicative (Fin 4 → ZMod 5) →* S)

@[expose] def phiAdd (c : Fin 4 → ZMod 5) : S := φ (Multiplicative.ofAdd c)

theorem phiAdd_add (c d : Fin 4 → ZMod 5) : phiAdd φ (c + d) = phiAdd φ c * phiAdd φ d := by
  simp only [phiAdd, ofAdd_add, map_mul]

theorem phiAdd_nsmul (m : ℕ) (c : Fin 4 → ZMod 5) : phiAdd φ (m • c) = phiAdd φ c ^ m := by
  simp only [phiAdd, ofAdd_nsmul, map_pow]

theorem gLAPPrimeCoreOf_centralizer_of_hyperplanes (hinj : Function.Injective φ)
    (hleaf : ∀ f : Fin 4 → ZMod 5, NormF f →
      GLAPPrimeCoreOf 5 (Subgroup.centralizer (phiAdd φ '' {c | f ⬝ᵥ c = 0})) = ⊥)
    {y : Fin 4 → ZMod 5} (hy : y ≠ 0) :
    GLAPPrimeCoreOf 5 (Subgroup.centralizer {phiAdd φ y}) = ⊥ := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set A := φ.range with hAdef
  have hmemA : ∀ c, phiAdd φ c ∈ A := fun c => ⟨Multiplicative.ofAdd c, rfl⟩
  have hAcomm : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hA : IsElemAbelian 5 A := by
    refine ⟨⟨⟨fun x z => Subtype.ext (hAcomm x x.2 z z.2)⟩⟩, ?_⟩
    rintro _ ⟨a, rfl⟩
    rw [← map_pow]
    have : a ^ 5 = 1 := by
      rw [← ofAdd_toAdd a, ← ofAdd_nsmul]
      have h5 : (5 • Multiplicative.toAdd a : Fin 4 → ZMod 5) = 0 := by
        funext j
        simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
        have : (5 : ZMod 5) = 0 := rfl
        rw [Nat.cast_ofNat, this, zero_mul]
      rw [h5, ofAdd_zero]
    rw [this, map_one]
  have hAC : A ≤ Subgroup.centralizer {phiAdd φ y} := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hAcomm x hx _ (hmemA y)
  have hA1 : A ≠ ⊥ := by
    intro h
    have h1 : phiAdd φ y ∈ (⊥ : Subgroup S) := h ▸ hmemA y
    rw [Subgroup.mem_bot] at h1
    have h2 : φ (Multiplicative.ofAdd y) = φ 1 := by rw [map_one]; exact h1
    exact hy (hinj h2)
  refine gLAPPrimeCoreOf_eq_bot_of_hyperplanes Nat.prime_five hA hAC hA1 fun B hBA hidx => ?_
  set S₀ : AddSubgroup (Fin 4 → ZMod 5) := Subgroup.toAddSubgroup' (B.comap φ) with hS₀
  have hmemS₀ : ∀ c, c ∈ S₀ ↔ phiAdd φ c ∈ B := fun c => Iff.rfl
  have hS₀idx : S₀.index = 5 := by
    have h1 : S₀.index = (B.comap φ).index := rfl
    rw [h1, Subgroup.index_comap]
    exact hidx
  obtain ⟨f, hfN, hf0, hfker⟩ := exists_normF_of_index_five S₀ hS₀idx
  have hBeq : (B : Set S) = phiAdd φ '' {c | f ⬝ᵥ c = 0} := by
    ext b
    constructor
    · intro hb
      obtain ⟨a, rfl⟩ := hBA hb
      refine ⟨Multiplicative.toAdd a, ?_, by simp [phiAdd]⟩
      change Multiplicative.toAdd a ∈ {c | f ⬝ᵥ c = 0}
      rw [Set.mem_setOf_eq, ← hfker, hmemS₀]
      simpa [phiAdd] using hb
    · rintro ⟨c, hc, rfl⟩
      exact (hmemS₀ c).1 ((hfker c).2 hc)
  by_cases hyk : f ⬝ᵥ y = 0
  · have hyB : phiAdd φ y ∈ B := (hmemS₀ y).1 ((hfker y).2 hyk)
    have hle : Subgroup.centralizer (B : Set S) ≤ Subgroup.centralizer {phiAdd φ y} :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.2 hyB)
    rw [inf_eq_right.2 hle, hBeq]
    exact hleaf f hfN
  · have heq : Subgroup.centralizer {phiAdd φ y} ⊓ Subgroup.centralizer (B : Set S) =
        Subgroup.centralizer (phiAdd φ '' {c | (0 : Fin 4 → ZMod 5) ⬝ᵥ c = 0}) := by
      ext g
      simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_iff, hBeq, Set.mem_singleton_iff,
        forall_eq, Set.forall_mem_image, Set.mem_setOf_eq, zero_dotProduct, forall_const]
      constructor
      · rintro ⟨h1, h2⟩ c'
        set k : ZMod 5 := (f ⬝ᵥ c') * (f ⬝ᵥ y)⁻¹ with hk
        set c : Fin 4 → ZMod 5 := c' - k • y with hc
        have hfc : f ⬝ᵥ c = 0 := by
          rw [hc, dotProduct_sub, dotProduct_smul, smul_eq_mul, hk]
          field_simp
          ring
        have hky : k • y = k.val • y := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod 5), ZMod.natCast_zmod_val]
        have hcy : c' = c + k.val • y := by
          rw [← hky, hc, sub_add_cancel]
        have hcomm : Commute (phiAdd φ c' ) g := by
          rw [hcy, phiAdd_add, phiAdd_nsmul]
          exact (show Commute (phiAdd φ c) g from h2 hfc).mul_left
            ((show Commute (phiAdd φ y) g from h1).pow_left _)
        exact hcomm.eq
      · intro h
        exact ⟨@h y, fun c _ => @h c⟩
    rw [heq]
    exact hleaf 0 (Or.inl rfl)

end Rec

end CFSG.HardMathSupport.Timmesfeld.CrossChar.SmallQ5

end
