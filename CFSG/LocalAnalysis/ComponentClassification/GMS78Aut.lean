module

public import CFSG.RankThree.SteinbergR3ESuzukiFieldSplitting
public import CFSG.Walter.W67.W2Cor32A
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoBenderHypII
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoStandardDefs

public section

namespace CFSG.ComponentClassification.GMS78

open Subgroup CFSG.Open CFSG.ComponentClassification.RankTwoStandard
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms

variable {G : Type} [Group G]

@[expose] noncomputable def quotAutHom (L : Subgroup G) :
    normalizer (L : Set G) →* MulAut (rankTwoQuot L) :=
  (centerQuotientHom L).comp L.normalizerMonoidHom

theorem quotAutHom_apply_mk (L : Subgroup G) (t : normalizer (L : Set G)) (x : L) :
    quotAutHom L t (QuotientGroup.mk' (center L) x) =
      QuotientGroup.mk' (center L) (L.normalizerMonoidHom t x) :=
  onCenterQuotient_apply_mk _ x

theorem onCenterQuotient_conj {X : Type*} [Group X] (y : X) :
    onCenterQuotient (MulAut.conj y) = MulAut.conj (QuotientGroup.mk' (center X) y) := by
  ext q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (center X) q
  rw [onCenterQuotient_apply_mk, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]

theorem mem_sup_centralizer_of_quotAut_mem_inner {L : Subgroup G} (hLp : commutator L = ⊤)
    {t : G} (htN : t ∈ normalizer (L : Set G))
    (h : quotAutHom L ⟨t, htN⟩ ∈ inner (rankTwoQuot L)) :
    t ∈ L ⊔ centralizer (L : Set G) := by
  have : Group.IsPerfect L := ⟨hLp⟩
  obtain ⟨yb, hyb⟩ := h
  obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (center L) yb
  have hα : L.normalizerMonoidHom ⟨t, htN⟩ = MulAut.conj y := by
    apply centerQuotientHom_injective L
    change quotAutHom L ⟨t, htN⟩ = onCenterQuotient (MulAut.conj y)
    rw [onCenterQuotient_conj, ← hyb]
  have hc : (y : G)⁻¹ * t ∈ centralizer (L : Set G) := by
    rw [mem_centralizer_iff]
    intro z hz
    have h1 := congrArg (fun φ : MulAut L => ((φ ⟨z, hz⟩ : L) : G)) hα
    simp only [normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply, coe_mul, coe_inv] at h1
    calc z * ((y : G)⁻¹ * t) = (y : G)⁻¹ * (y * z * (y : G)⁻¹) * t := by group
      _ = (y : G)⁻¹ * (t * z * t⁻¹) * t := by rw [h1]
      _ = (y : G)⁻¹ * t * z := by group
  have := mul_mem_sup y.2 hc
  rwa [mul_inv_cancel_left] at this

theorem eq_one_of_pow_two_pow_eq_one_of_odd {H : Type*} [Group H] (hodd : Odd (Nat.card H))
    {q : H} {k : ℕ} (hq : q ^ 2 ^ k = 1) : q = 1 := by
  have : Finite H := Nat.finite_of_card_ne_zero hodd.pos.ne'
  have h1 := orderOf_dvd_of_pow_eq_one hq
  have h2 := orderOf_dvd_natCard q
  have hcop : Nat.Coprime (2 ^ k) (Nat.card H) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hodd)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem odd_card_outer_of_sz {Y : Type} [Group Y] {a : ℕ}
    (ha : 1 ≤ a) (eY : Y ≃* Sz a) : Odd (Nat.card (Outer Y)) := by
  obtain ⟨eS⟩ := CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.nonempty_mulEquiv_sz_suzukiGroup a
  have hK : Nat.card (GaloisField 2 (2 * a + 1)) = 2 ^ (2 * a + 1) :=
    GaloisField.card 2 (2 * a + 1) (by omega)
  have hodd := (CFSG.RankThree.Automorphisms.Suzuki_full_field_automorphism_splitting a ha
    (GaloisField 2 (2 * a + 1)) hK).2.2.2.2.2.2
  rwa [← Nat.card_congr (equivalence (eY.trans eS)).toEquiv] at hodd

theorem mem_sup_centralizer_of_sz {L : Subgroup G}
    (hLp : commutator L = ⊤) {a : ℕ} (ha : 1 ≤ a) (e : rankTwoQuot L ≃* Sz a) {t : G}
    (htN : t ∈ normalizer (L : Set G)) {k : ℕ} (htk : t ^ 2 ^ k = 1) :
    t ∈ L ⊔ centralizer (L : Set G) := by
  apply mem_sup_centralizer_of_quotAut_mem_inner hLp htN
  have hk : quotAutHom L ⟨t, htN⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨t, htN⟩ : normalizer (L : Set G)) ^ 2 ^ k = 1 := Subtype.ext (by simpa using htk)
    rw [this, map_one]
  have hq : (QuotientGroup.mk (quotAutHom L ⟨t, htN⟩) : Outer (rankTwoQuot L)) = 1 :=
    eq_one_of_pow_two_pow_eq_one_of_odd (odd_card_outer_of_sz ha e)
      (by rw [← QuotientGroup.mk_pow, hk]; rfl)
  exact (QuotientGroup.eq_one_iff _).mp hq

theorem exists_mem_sup_centralizer_of_commute
    [Finite G] {L : Subgroup G} (hLp : commutator L = ⊤)
    (hB : fusionIsBenderGroup (rankTwoQuot L)) {e₁ e₂ : G}
    (h₁ : e₁ ∈ normalizer (L : Set G)) (h₂ : e₂ ∈ normalizer (L : Set G))
    (h₁₁ : e₁ * e₁ = 1) (h₂₂ : e₂ * e₂ = 1) (h₁₂ : e₁ * e₂ = e₂ * e₁) :
    e₁ ∈ L ⊔ centralizer (L : Set G) ∨ e₂ ∈ L ⊔ centralizer (L : Set G) ∨
      e₁ * e₂ ∈ L ⊔ centralizer (L : Set G) := by
  have hE := RankTwoBender.e4Inner_of_bender hB
  set α := quotAutHom L
  set n₁ : normalizer (L : Set G) := ⟨e₁, h₁⟩
  set n₂ : normalizer (L : Set G) := ⟨e₂, h₂⟩
  have hn₁ : n₁ * n₁ = 1 := Subtype.ext h₁₁
  have hn₂ : n₂ * n₂ = 1 := Subtype.ext h₂₂
  have hn₁₂ : n₁ * n₂ = n₂ * n₁ := Subtype.ext h₁₂
  rcases hE (α n₁) (α n₂) (by rw [← map_mul, hn₁, map_one]) (by rw [← map_mul, hn₂, map_one])
      (by rw [← map_mul, ← map_mul, hn₁₂]) with ⟨y, hy⟩ | ⟨y, hy⟩ | ⟨y, hy⟩
  · exact Or.inl (mem_sup_centralizer_of_quotAut_mem_inner hLp h₁ ⟨y, hy.symm⟩)
  · exact Or.inr (Or.inl (mem_sup_centralizer_of_quotAut_mem_inner hLp h₂ ⟨y, hy.symm⟩))
  · refine Or.inr (Or.inr (mem_sup_centralizer_of_quotAut_mem_inner hLp (mul_mem h₁ h₂) ⟨y, ?_⟩))
    have : (⟨e₁ * e₂, mul_mem h₁ h₂⟩ : normalizer (L : Set G)) = n₁ * n₂ := rfl
    rw [this, map_mul]
    exact hy.symm

theorem card_le_two_mul_inf [Finite G]
    {L : Subgroup G} (hLp : commutator L = ⊤) (hB : fusionIsBenderGroup (rankTwoQuot L))
    {E : Subgroup G} (hEN : E ≤ normalizer (L : Set G)) (hE : IsElemAbelian 2 E) :
    Nat.card E ≤ 2 * Nat.card (E ⊓ (L ⊔ centralizer (L : Set G)) : Subgroup G) := by
  set F := E ⊓ (L ⊔ centralizer (L : Set G)) with hF
  have hsq : ∀ x ∈ E, x * x = 1 := fun x hx => by rw [← sq]; exact hE.2 x hx
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  by_contra hlt
  push Not at hlt
  have hFE : F ≤ E := inf_le_left
  obtain ⟨e₁, he₁E, he₁F⟩ : ∃ e₁ ∈ E, e₁ ∉ F := by
    by_contra hall
    push Not at hall
    have : E ≤ F := hall
    have := card_le_of_le this
    omega
  set Z := zpowers e₁ with hZ
  have hZE : Z ≤ E := (zpowers_le).mpr he₁E
  have hZN : Z ≤ normalizer (F : Set G) := by
    rw [zpowers_le, mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      rw [hcomm e₁ he₁E y (hFE hy), mul_inv_cancel_right]
      exact hy
    · intro hy
      have hyE : y ∈ E := by
        have := E.mul_mem (E.mul_mem (E.inv_mem he₁E) (hFE hy)) he₁E
        simpa [mul_assoc] using this
      rwa [hcomm e₁ he₁E y hyE, mul_inv_cancel_right] at hy
  have hFZ : F ⊓ Z = ⊥ := by
    rw [eq_bot_iff]
    intro x ⟨hxF, hxZ⟩
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hxZ
    rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · rw [mem_bot, ← two_mul, zpow_mul, show e₁ ^ (2 : ℤ) = 1 by
        rw [zpow_two, hsq e₁ he₁E], one_zpow]
    · exfalso
      apply he₁F
      have h1 : e₁ ^ (2 * k + 1) = e₁ := by
        rw [zpow_add, zpow_mul, show e₁ ^ (2 : ℤ) = 1 by rw [zpow_two, hsq e₁ he₁E], one_zpow,
          one_mul, zpow_one]
      rw [h1] at hxF
      exact hxF
  have hZcard : Nat.card Z = 2 := by
    rw [hZ, Nat.card_zpowers]
    refine orderOf_eq_prime (by rw [sq]; exact hsq e₁ he₁E) ?_
    intro h1
    apply he₁F
    rw [h1]
    exact F.one_mem
  have hFZcard : Nat.card (F ⊔ Z : Subgroup G) = 2 * Nat.card F := by
    have h := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer hZN
    rw [hFZ, card_bot, mul_one, hZcard, mul_comm] at h
    exact h
  obtain ⟨e₂, he₂E, he₂FZ⟩ : ∃ e₂ ∈ E, e₂ ∉ F ⊔ Z := by
    by_contra hall
    push Not at hall
    have : E ≤ F ⊔ Z := hall
    have := card_le_of_le this
    omega
  have he₂F : e₂ ∉ F := fun h => he₂FZ (mem_sup_left h)
  have he₁₂F : e₁ * e₂ ∉ F := by
    intro h
    apply he₂FZ
    have : e₂ = e₁ * (e₁ * e₂) := by rw [← mul_assoc, hsq e₁ he₁E, one_mul]
    rw [this, sup_comm]
    exact mul_mem_sup (mem_zpowers e₁) h
  rcases exists_mem_sup_centralizer_of_commute hLp hB (hEN he₁E) (hEN he₂E) (hsq e₁ he₁E)
      (hsq e₂ he₂E) (hcomm e₁ he₁E e₂ he₂E) with h | h | h
  · exact he₁F ⟨he₁E, h⟩
  · exact he₂F ⟨he₂E, h⟩
  · exact he₁₂F ⟨E.mul_mem he₁E he₂E, h⟩

end CFSG.ComponentClassification.GMS78
