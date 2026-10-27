module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D6
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D5

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem eq_of_mem_of_mem (hΩ : Assumption41 Ω) {K L : Subgroup G} (hK : K ∈ Ω) (hL : L ∈ Ω)
    {z : G} (hzK : z ∈ K) (hzL : z ∈ L) (hz1 : z ≠ 1) (hzz : z * z = 1) : K = L := by
  by_contra hne
  have hP : IsPGroup 2 (zpowers z) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hzz)
  have h1 := Assumption41.inf_eq_bot hΩ hK hL hne hP ((zpowers_le).mpr hzK)
    ((zpowers_le).mpr hzL)
  rw [inf_idem] at h1
  exact hz1 (mem_bot.mp (h1 ▸ mem_zpowers z))

theorem isSylowOf_of_isSylowOf_le {K M R P : Subgroup G} (hR : IsSylowOf 2 R K) (hRM : R ≤ M)
    (hMK : M ≤ K) (hP : IsSylowOf 2 P M) : IsSylowOf 2 P K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hRM' : IsSylowOf 2 R M := hR.of_le hRM hMK
  apply isSylowOf_of_card (hP.le.trans hMK)
  rw [hP.card_eq, ← hRM'.card_eq, hR.card_eq]

theorem rot_eq_of_le_sec4W (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {K R R' V V' : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K) (hV : IsDihedralRot V R)
    (hR' : IsSylowOf 2 R' K) (hV' : IsDihedralRot V' R') (hVW : V ≤ sec4W Ω S)
    (hV'W : V' ≤ sec4W Ω S) : V = V' :=
  eq_of_isRot_of_le hΩ (hS.isPGroup.to_le (sec4W_le S)) hK hR hV hR' hV' hVW hV'W

theorem exists_isSylowOf_le_normalizer_normalized {K R A W : Subgroup G} (hR : IsSylowOf 2 R K)
    (hRW : R ≤ normalizer (W : Set G)) (hA : IsPGroup 2 A) (hAK : A ≤ normalizer (K : Set G))
    (hAW : A ≤ normalizer (W : Set G)) :
    ∃ P, IsSylowOf 2 P K ∧ P ≤ normalizer (W : Set G) ∧ A ≤ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAM : A ≤ normalizer ((K ⊓ normalizer (W : Set G) : Subgroup G) : Set G) :=
    fun a ha => inf_le_normalizer_inf (mem_inf.mpr ⟨hAK ha, le_normalizer (hAW ha)⟩)
  obtain ⟨P, hP, hAP⟩ := exists_isSylowOf_normalized hA hAM
  exact ⟨P, isSylowOf_of_isSylowOf_le hR (le_inf hR.le hRW) inf_le_left hP,
    hP.le.trans inf_le_right, hAP⟩

theorem isDihedralTwoGroup_of_not_dStarAdj (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {J L R U : Subgroup G} (hJ : J ∈ Ω) (hL : L ∈ Ω) (hJL : ¬ DStarAdj Ω L J) {t : G}
    (htJ : t ∈ J) (ht1 : t ≠ 1) (htt : t * t = 1) (htL : t ∈ normalizer (L : Set G))
    (hR : IsSylowOf 2 R L) (hU : IsDihedralRot U R) (htR : t ∈ normalizer (R : Set G)) :
    IsDihedralTwoGroup (zpowers t ⊔ R) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := zpowers t with hVdef
  have hV2 : IsPGroup 2 V :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  have hVle : V ≤ J ⊓ normalizer (L : Set G) := (zpowers_le).mpr (mem_inf.mpr ⟨htJ, htL⟩)
  have hVcard : Nat.card V = 2 := by
    rw [hVdef, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact htt) ht1
  obtain ⟨V₁, hV₁, hVV₁⟩ := exists_isSylowOf_le hV2 hVle
  have hV₁1 : V₁ ≠ ⊥ := by
    intro h
    rw [h] at hVV₁
    exact ht1 (mem_bot.mp (hVV₁ (mem_zpowers t)))
  have hV₁card := card_eq_two_of_not_dStarAdj h22 hΩ hJ hL hJL hV₁ hV₁1
  have hVV : V = V₁ := eq_of_le_of_card_ge hVV₁ (by rw [hV₁card, hVcard])
  have hVsyl : IsSylowOf 2 V (J ⊓ normalizer (L : Set G)) := hVV ▸ hV₁
  have hVR : V ≤ normalizer (R : Set G) := (zpowers_le).mpr htR
  have hV1 : V ≠ ⊥ := hVV ▸ hV₁1
  rcases lemma415 h22 hΩ hL hJ hR hU hVsyl hV1 hVR with ⟨-, hJL', hLJ'⟩ | ⟨⟨e⟩, -, -⟩ |
    ⟨-, hD, -⟩
  · exact absurd (dStarAdj_of_le_normalizer hΩ hL hJ hJL' hLJ') hJL
  · exfalso
    have : Nat.card V = Nat.card U := Nat.card_congr e.toEquiv
    have h4 := hU.four_le
    omega
  · exact hD

theorem IsDihedralRot.pow_half_eq {U R : Subgroup G} (hU : IsDihedralRot U R) {z : G}
    (hz : ∀ y ∈ U, y * y = 1 → y = 1 ∨ y = z) {w : G} (hw : w ∈ U) :
    w ^ (Nat.card U / 2) = 1 ∨ w ^ (Nat.card U / 2) = z := by
  apply hz _ (pow_mem hw _)
  obtain ⟨m, hm⟩ := hU.two_dvd_card
  have hm0 : Nat.card U / 2 = m := by omega
  rw [hm0, ← pow_add, ← two_mul, ← hm]
  have h1 : (⟨w, hw⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
  have h2 := congrArg Subtype.val h1
  rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2

end CFSG.ComponentClassification.Asc76.Sec4
