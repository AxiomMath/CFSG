module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVCoreDual
import CFSG.LocalAnalysis.AGLEmbedding.OneSmallSmallPFrame

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G]

theorem false_of_frame_dual {P R T : Subgroup G} {z : G} (hP : IsPGroup 3 P) (hRP : R ≤ P)
    (hRcomm : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRcard : Nat.card R = 27) (hTR : T ≤ R)
    (hTcard : Nat.card T = 9) (hzR : z ∈ R) (hzp : orderOf z = 3)
    (hstab : ∀ y ∈ Subgroup.normalizer (R : Set G), y * z = z * y →
      (∃ k : ℕ, y ^ 3 ^ k = 1) → y ∈ R)
    (hTZ : ∀ t ∈ T, t ≠ 1 → t ∈ fusionSet R z) (h4 : 4 ≤ Open.pRank 3 P) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup G := P ⊓ Subgroup.normalizer (R : Set G) with hNdef
  have hRN : R ≤ N := le_inf hRP Subgroup.le_normalizer
  have hNp : IsPGroup 3 N := hP.to_le inf_le_left
  have h3 : ∀ s ∈ P, ∃ k : ℕ, s ^ 3 ^ k = 1 := fun s hs => by
    obtain ⟨k, hk⟩ := hP ⟨s, hs⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hNcard : Nat.card N ≤ 81 :=
    card_normalizer_le_of_dual hP hRP hRcomm hRcard hTR hTcard hzp hstab hTZ
  have hPN : P = N := by
    refine eq_of_isPGroup_of_le_of_normalizer hP inf_le_left fun g hgP hgN => ?_
    by_contra hgN'
    have hgR : g ∉ Subgroup.normalizer (R : Set G) := fun h => hgN' ⟨hgP, h⟩
    set R' := R.map (MulAut.conj g).toMonoidHom with hR'
    have hR'N : R' ≤ N := by
      rintro _ ⟨r, hr, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hgN r).mp (hRN hr)
    have hR'card : Nat.card R' = 27 := by
      rw [hR', Subgroup.card_map_of_injective (MulAut.conj g).injective, hRcard]
    obtain ⟨y, hyR', hyR⟩ : ∃ y ∈ R', y ∉ R := by
      by_contra h
      push Not at h
      have heq : R' = R := Subgroup.eq_of_le_of_card_ge h (by rw [hRcard, hR'card])
      apply hgR
      rw [Subgroup.mem_normalizer_iff]
      intro r
      constructor
      · intro hr
        rw [← heq]
        exact ⟨r, hr, rfl⟩
      · intro hr
        rw [← heq] at hr
        obtain ⟨r', hr', hrr⟩ := hr
        have : r' = r := by
          simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply] at hrr
          exact mul_left_cancel (mul_right_cancel hrr)
        rw [← this]
        exact hr'
    have hR'R : R' ≤ Subgroup.normalizer (R : Set G) := hR'N.trans inf_le_right
    have hc := card_sup_mul_card_inf_eq_of_le_normalizer hR'R
    have hsup : Nat.card (R ⊔ R' : Subgroup G) ≤ 81 :=
      (Subgroup.card_le_of_le (sup_le hRN hR'N)).trans hNcard
    have hE : 9 ≤ Nat.card (R ⊓ R' : Subgroup G) := by
      rw [hRcard, hR'card] at hc
      by_contra h
      push Not at h
      have : Nat.card (R ⊔ R' : Subgroup G) * Nat.card (R ⊓ R' : Subgroup G) ≤ 81 * 8 :=
        Nat.mul_le_mul hsup (by omega)
      omega
    obtain ⟨t, ⟨htRR', htT⟩, ht1⟩ : ∃ t ∈ (R ⊓ R') ⊓ T, t ≠ 1 := by
      by_contra h
      push Not at h
      have hbot : (R ⊓ R') ⊓ T = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
      have h1 := mul_card_le_of_inf_eq_bot inf_le_left hTR hbot
      rw [hTcard, hRcard] at h1
      omega
    have hyN := hR'N hyR'
    apply hyR
    refine mem_of_comm_mem_fusionSet hzp hstab hyN.2 (h3 y hyN.1) (hTZ t htT ht1) ?_
    obtain ⟨r, hr, rfl⟩ := hyR'
    obtain ⟨s, hs, hse⟩ := htRR'.2
    rw [← hse]
    simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply]
    calc g * r * g⁻¹ * (g * s * g⁻¹) = g * (r * s) * g⁻¹ := by group
      _ = g * (s * r) * g⁻¹ := by rw [hRcomm r hr s hs]
      _ = g * s * g⁻¹ * (g * r * g⁻¹) := by group
  have hPcard : Nat.card P ≤ 81 := hPN ▸ hNcard
  have hle := pRank_le_three_of_card_le hPcard (fun h => by
    have hPR : P ≤ R := fun g hg => hstab g (hPN ▸ hg : g ∈ N).2 (h g hg z (hRP hzR))
      (h3 g hg)
    have h1 := Subgroup.card_le_of_le hPR
    have h2 := le_card_of_four_le_pRank h4
    omega)
  omega

end CFSG.AGLEmbedding
