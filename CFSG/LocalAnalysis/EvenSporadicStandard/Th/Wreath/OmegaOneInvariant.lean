module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.SL7V8Facts

public section

namespace CFSG.EvenSporadicStandard.ThStd

open Subgroup SylowEnd

variable {G : Type} [Group G] [Finite G] {L R : Subgroup G} {t : G} {S A B Aa D : Subgroup G}
  {z b : G}

theorem ThLocalIn.eq_bot_or_eq_A_of_le (W : ThLocalIn L S A B z) {Y : Subgroup G} (hYA : Y ≤ A)
    (hY : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) :
    Y = ⊥ ∨ Y = A := by
  by_cases hbot : Y = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hbot
    have hya : (a : G) ∈ Y := a.2
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    obtain ⟨n, hnL, hnA, hnz⟩ := W.trans (a : G) (hYA hya) ha1'
    have hnN : n ∈ normalizer (A : Set G) := by
      have hinv : n⁻¹ ∈ normalizer (A : Set G) :=
        mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := n⁻¹) (by simpa using hnA))
      simpa using (normalizer (A : Set G)).inv_mem hinv
    have hzY : z ∈ Y := by
      have h1 : n⁻¹ * (a : G) * n ∈ Y := by
        simpa using hY n⁻¹ ⟨L.inv_mem hnL, (normalizer (A : Set G)).inv_mem hnN⟩ (a : G) hya
      have h2 : n⁻¹ * (a : G) * n = z := by rw [← hnz]; group
      rwa [h2] at h1
    refine le_antisymm hYA ?_
    intro a' ha'
    by_cases h1 : a' = 1
    · simpa [h1] using Y.one_mem
    · obtain ⟨m, hmL, hmA, hmz⟩ := W.trans a' ha' h1
      have hmN : m ∈ normalizer (A : Set G) := by
        have hinv : m⁻¹ ∈ normalizer (A : Set G) :=
          mem_normalizer_iff.2 (mem_iff_conj_of_conj_le A (g := m⁻¹) (by simpa using hmA))
        simpa using (normalizer (A : Set G)).inv_mem hinv
      have h2 : m * z * m⁻¹ ∈ Y := hY m ⟨hmL, hmN⟩ z hzY
      rwa [hmz] at h2

theorem ThCyc.A_le_of_conj_mem (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) {X : Subgroup G}
    (hXV : X ≤ omega1 D hD.comm)
    (hXH : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hXt : ∀ x ∈ X, t * x * t⁻¹ ∈ X) (hX : X ≠ ⊥) : A ≤ X := by
  have hnorm : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ y ∈ X ⊓ A, n * y * n⁻¹ ∈ X ⊓ A := by
    rintro n hn y ⟨hyX, hyA⟩
    exact ⟨hXH n hn y hyX, (mem_normalizer_iff.1 hn.2 y).1 hyA⟩
  rcases W.eq_bot_or_eq_A_of_le inf_le_right hnorm with hbot | htop
  · exfalso
    apply hX
    refine eq_bot_iff.2 fun x hx => ?_
    have hxV : x ∈ omega1 D hD.comm := hXV hx
    have hconv : t * x * t⁻¹ ∈ X := hXt x hx
    have hmem : thV t x ∈ X := by
      have hEq : thV t x = x * (t * x * t⁻¹) := rfl
      rw [hEq]
      exact X.mul_mem hx hconv
    have hθ : thV t x ∈ X ⊓ A := ⟨hmem, H.thV_mem_A W W2 hD hxV⟩
    have hθ1 : thV t x = 1 := by
      have h' : thV t x ∈ (⊥ : Subgroup G) := hbot ▸ hθ
      simpa using h'
    have hxA : x ∈ A := (H.thV_eq_one_iff W W2 hD hxV).1 hθ1
    have h' : x ∈ (⊥ : Subgroup G) := hbot ▸ ⟨hx, hxA⟩
    simpa using h'
  · intro a ha
    exact (htop ▸ ha).1

theorem ThCyc.eq_A_or_eq_omega1 (H : ThCyc G L R t) (W : ThLocalIn L S A B z)
    (W2 : ThLocalIn2 B A Aa b) (hD : DHyp A Aa t D) (h4 : ∀ d ∈ D, d ^ 4 = 1)
    {X : Subgroup G} (hAX : A ≤ X) (hXV : X ≤ omega1 D hD.comm)
    (hXH : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ x ∈ X, n * x * n⁻¹ ∈ X) :
    X = A ∨ X = omega1 D hD.comm := by
  have hsq : ∀ d ∈ D, d ^ 2 ∈ A := fun d hd => H.D_sq_mem_A_of_fourth W W2 hD h4 hd
  let θX : ↥X →* ↥A :=
    { toFun := fun x => ⟨thV t (x : G), H.thV_mem_A W W2 hD (hXV x.2)⟩
      map_one' := Subtype.ext (by simp [thV])
      map_mul' := fun x y => Subtype.ext (by
        show thV t ((x : G) * (y : G)) = thV t (x : G) * thV t (y : G)
        exact H.thV_mul W W2 hD (hXV x.2) (hXV y.2)) }
  let Z : Subgroup G := θX.range.map A.subtype
  have hZle : Z ≤ A := Subgroup.map_subtype_le θX.range
  have hmemZ : ∀ z : G, z ∈ Z ↔ ∃ x : ↥X, thV t (x : G) = z := by
    intro z
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨x, hx⟩ := ha
      exact ⟨x, congrArg Subtype.val hx⟩
    · rintro ⟨x, rfl⟩
      exact ⟨θX x, ⟨x, rfl⟩, rfl⟩
  have hZn : ∀ n ∈ L ⊓ normalizer (A : Set G), ∀ z ∈ Z, n * z * n⁻¹ ∈ Z := by
    rintro n hn z hz
    obtain ⟨x, rfl⟩ := (hmemZ z).1 hz
    rw [← H.thV_conj W W2 hD hn.1]
    exact (hmemZ _).2 ⟨⟨n * (x : G) * n⁻¹, hXH n hn x.1 x.2⟩, rfl⟩
  rcases W.eq_bot_or_eq_A_of_le hZle hZn with hbot | htop
  · left
    refine le_antisymm ?_ hAX
    intro x hx
    have h1 : ((θX ⟨x, hx⟩ : ↥A) : G) ∈ (⊥ : Subgroup G) := by
      have hmem : ((θX ⟨x, hx⟩ : ↥A) : G) ∈ Z := ⟨θX ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩, rfl⟩
      rwa [hbot] at hmem
    have h2 : ((θX ⟨x, hx⟩ : ↥A) : G) = 1 := by simpa using h1
    exact (H.thV_eq_one_iff W W2 hD (hXV hx)).1 h2
  · right
    have hXcard : Nat.card ↥X = 2 ^ 8 := by
      have h1 := Subgroup.card_ker_mul_card_range θX
      have hker : Nat.card ↥θX.ker = Nat.card ↥A := by
        have heq : θX.ker = A.subgroupOf X := by
          ext x
          rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
          exact ⟨fun h => (H.thV_eq_one_iff W W2 hD (hXV x.2)).1 (congrArg Subtype.val h),
            fun h => Subtype.ext ((H.thV_eq_one_iff W W2 hD (hXV x.2)).2 h)⟩
        rw [heq]
        exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAX).toEquiv
      have hrange : Nat.card ↥θX.range = Nat.card ↥A := by
        have h2 : Nat.card ↥Z = Nat.card ↥θX.range :=
          Subgroup.card_map_of_injective A.subtype_injective
        rw [← h2, htop, W.A_card]
      rw [hker, hrange, W.A_card] at h1
      rw [← h1]
      norm_num
    exact Subgroup.eq_of_le_of_card_ge hXV (by rw [H.card_omega1 W W2 hD hsq, hXcard])

end CFSG.EvenSporadicStandard.ThStd
