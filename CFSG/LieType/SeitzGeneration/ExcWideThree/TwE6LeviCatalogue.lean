module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6RegularLevi
public import CFSG.LieType.SeitzGeneration.ExcWideThree.TwE6LeviCatalogueCentralizer
public import CFSG.LieType.Chevalley.E6A5CubeLevi
public import CFSG.LieType.Chevalley.E6A5CubeUnitaryCover

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.Chevalley.E6A5Cube
open CFSG.LieType.Universal.Unitary (SU)

section Pure

variable {K : Type} [Field K] [Finite K]

theorem exists_trace_zero (σ : K ≃+* K) {q : ℕ} (hq2 : 2 ≤ q) (hK : Nat.card K = q ^ 2)
    (hσ : ∀ c, σ c = c ^ q) : ∃ ζ : K, ζ ≠ 0 ∧ σ ζ = -ζ := by
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ c : K, c ^ (q ^ 2) = c := fun c => by
    have := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hK] at this
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, ← pow_mul, ← pow_two, hpow]
  obtain ⟨c, hc⟩ : ∃ c : K, σ c ≠ c := by
    by_contra hcon
    push Not at hcon
    have hne : (Polynomial.X ^ q - Polynomial.X : Polynomial K) ≠ 0 :=
      FiniteField.X_pow_card_sub_X_ne_zero K (by omega)
    have hdeg := FiniteField.X_pow_card_sub_X_natDegree_eq K (show 1 < q by omega)
    have hsub : (Finset.univ : Finset K).val ⊆ (Polynomial.X ^ q - Polynomial.X : Polynomial K).roots := by
      intro c _
      rw [Polynomial.mem_roots hne]
      have h1 : c ^ q = c := (hσ c).symm.trans (hcon c)
      simp [Polynomial.IsRoot, h1]
    have hle := Polynomial.card_le_degree_of_subset_roots hsub
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hK, hdeg] at hle
    nlinarith
  refine ⟨c - σ c, sub_ne_zero.2 hc.symm, ?_⟩
  rw [map_sub, hσσ]
  ring

end Pure


section Cover


theorem isPSU6Cover_of_embedding {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q) (Q : TauCeti.PrimePower)
    (hQ : Q.card = q) {G' : Type*} [Group G'] (ι : ↥(fixA K σ.toRingHom) →* G')
    (hι : Function.Injective ι) : IsPSU6Cover ι.range Q := by
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hq2 : 2 ≤ q := by
    by_contra h
    push Not at h
    interval_cases q <;> norm_num at hK <;> omega
  obtain ⟨ζ, hζ, hσζ⟩ := exists_trace_zero σ hq2 hK hσ
  have : Fintype K := Fintype.ofFinite K
  have hpow : ∀ c : K, c ^ (q ^ 2) = c := fun c => by
    have := FiniteField.pow_card c
    rwa [← Nat.card_eq_fintype_card, hK] at this
  have hσσ : ∀ c, σ (σ c) = c := fun c => by
    rw [hσ, hσ, ← pow_mul, ← pow_two, hpow]
  have hq : ∃ p f : ℕ, p.Prime ∧ q = p ^ f :=
    ⟨Q.p, Q.exponent, Q.prime_p, by rw [← hQ, TauCeti.PrimePower.card_def]⟩
  set J := ι.range with hJ
  let e : ↥(fixA K σ.toRingHom) ≃* ↥J := MonoidHom.ofInjective hι
  let φ : SU σ 6 →* ↥J := e.toMonoidHom.comp (leviHom σ hζ hσζ)
  have hsurj : Function.Surjective φ := e.surjective.comp (leviHom_surjective σ hζ hσσ hσζ)
  have hker : ∀ x, φ x = 1 → x ∈ Subgroup.center (SU σ 6) := by
    intro x hx
    have h1 : leviHom σ hζ hσζ x = 1 := e.injective (by rw [map_one]; exact hx)
    exact (mem_center_SU_iff σ hK hσ hq x).2 (leviHom_eq_one σ hζ hσζ h1)
  have hsq : ∀ z ∈ Subgroup.center (SU σ 6), φ (z * z) = 1 := by
    intro z hz
    obtain ⟨l, hl⟩ := (mem_center_SU_iff σ hK hσ hq z).1 hz
    change e (leviHom σ hζ hσζ (z * z)) = 1
    rw [leviHom_scalar_sq σ hζ hσζ hl, map_one]
  have hv : (TauCeti.LieTypeIndex.twistedA 5 Q).Valid := by simp
  obtain ⟨h1, h2, h3⟩ := su6_cover σ hK hσ Q hQ hv φ hsurj hker hsq
  refine ⟨?_, h2, h3⟩
  have h5 := congrArg (Subgroup.map J.subtype) h1
  rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h5
  exact h5

end Cover


section Fixed

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem groupA_le_adjointGroup : groupA K ≤ adjointGroup Tag.E6 K :=
  Subgroup.closure_mono fun g ⟨i, _, c, h⟩ =>
    ⟨i, c, by rcases h with rfl | rfl; exacts [Or.inl rfl, Or.inr rfl]⟩

variable (K) in
@[expose] def twE6LeviSA (σ : K ≃+* K) : Subgroup (ModGL Tag.E6 K) :=
  groupA K ⊓ (twistedFixedGroup TwistTag.E6 K σ.toRingHom : Subgroup (ModGL Tag.E6 K))

variable (K) in
@[expose] def fixAToMod (σ : K ≃+* K) : ↥(fixA K σ.toRingHom) →* ModGL Tag.E6 K :=
  (groupA K).subtype.comp (fixA K σ.toRingHom).subtype

theorem fixAToMod_injective : Function.Injective (fixAToMod K σ) :=
  fun _ _ h => Subtype.ext (Subtype.ext h)

theorem range_fixAToMod : (fixAToMod K σ).range = twE6LeviSA K σ := by
  ext g
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨x.1.2, groupA_le_adjointGroup x.1.2, ?_⟩
    exact congrArg Subtype.val (mem_fixA_iff.1 x.2)
  · rintro ⟨hg1, hg2⟩
    refine ⟨⟨⟨g, hg1⟩, ?_⟩, rfl⟩
    exact Subtype.ext ((mem_twistedFixedGroup_iff_twistHom _ _ _).1 hg2).2


theorem twE6LeviSA_perfect {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (Q : TauCeti.PrimePower) (hQ : Q.card = q) :
    ⁅twE6LeviSA K σ, twE6LeviSA K σ⁆ = twE6LeviSA K σ := by
  have := (isPSU6Cover_of_embedding σ hK hσ Q hQ (fixAToMod K σ) (fixAToMod_injective σ)).1
  rwa [range_fixAToMod] at this

theorem isPSU6Cover_comap {q : ℕ} (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    (Q : TauCeti.PrimePower) (hQ : Q.card = q) (G : Subgroup (ModGL Tag.E6 K))
    (hSG : twE6LeviSA K σ ≤ G) : IsPSU6Cover ((twE6LeviSA K σ).comap G.subtype) Q := by
  let ι : ↥(fixA K σ.toRingHom) →* ↥G :=
    (fixAToMod K σ).codRestrict G fun x => hSG (by rw [← range_fixAToMod σ]; exact ⟨x, rfl⟩)
  have hι : Function.Injective ι := fun x y h =>
    fixAToMod_injective σ (show fixAToMod K σ x = fixAToMod K σ y from
      congrArg (fun z : ↥G => (z : ModGL Tag.E6 K)) h)
  have hrange : ι.range = (twE6LeviSA K σ).comap G.subtype := by
    ext g
    constructor
    · rintro ⟨x, rfl⟩
      show (fixAToMod K σ x) ∈ twE6LeviSA K σ
      rw [← range_fixAToMod σ]
      exact ⟨x, rfl⟩
    · intro hg
      have : (g : ModGL Tag.E6 K) ∈ (fixAToMod K σ).range := by
        rw [range_fixAToMod σ]
        exact hg
      obtain ⟨x, hx⟩ := this
      exact ⟨x, Subtype.ext hx⟩
  rw [← hrange]
  exact isPSU6Cover_of_embedding σ hK hσ Q hQ ι hι


end Fixed

section Final

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem twE6LeviCatalogue_holds : TwE6LeviCatalogue := by
  intro K _ _ σ q _ hσ hK Q hQ
  have hp : Q.p.Prime := Q.prime_p
  have hf : 1 ≤ Q.exponent := Q.exponent_pos
  have hqQ : q = Q.p ^ Q.exponent := by rw [← hQ, TauCeti.PrimePower.card_def]
  have hK' : Nat.card K = (Q.p ^ Q.exponent) ^ 2 := by rw [← hqQ]; exact hK
  have hσ' : ∀ c, σ c = c ^ (Q.p ^ Q.exponent) := by rw [← hqQ]; exact hσ
  have hperf := twE6LeviSA_perfect σ hK hσ Q hQ
  obtain ⟨hSG, hJ⟩ := twE6LongRootLevi_eq_subsystem σ hp hf hK' hσ' hperf
  rw [hJ]
  exact isPSU6Cover_comap σ hK hσ Q hQ (graphFixedRootGroup TwistTag.E6 K σ.toRingHom) hSG

end Final

end CFSG.LieType.SeitzGeneration.ExcWideThree
