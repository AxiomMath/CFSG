module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanBlockCycGroup
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanG28Generic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank

open CFSG.Open

theorem exists_E27_quotient_center {W : Type} [Group W] [Finite W] (L : Subgroup W)
    (h3 : 3 ≤ Open.pRank 3 L) (hZ : ¬ 3 ∣ Nat.card (Subgroup.center ↥L)) :
    ∃ E : Subgroup (↥L ⧸ Subgroup.center ↥L), IsElemAbelian 3 E ∧ Nat.card E = 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h3' : 3 ≤ Open.pRank 3 (⊤ : Subgroup ↥L) := by
    rw [CFSG.RankThreeEvenClassification.Helpers.pRank_top_subgroup 3 Nat.prime_three L]
    exact h3
  obtain ⟨E, -, hel, hcard⟩ := CFSG.AGLEmbedding.KFactProofs.G28.exists_elemAbelian_27 h3'
  set q : ↥L →* ↥L ⧸ Subgroup.center ↥L := QuotientGroup.mk' (Subgroup.center ↥L) with hq
  have hinj : Function.Injective (q.comp E.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hx1 : q (x : ↥L) = 1 := hx
    have hxZ : (x : ↥L) ∈ Subgroup.center ↥L := (QuotientGroup.eq_one_iff _).1 hx1
    have hx3 : (x : ↥L) ^ 3 = 1 := hel.2 x x.2
    have h1 : orderOf (x : ↥L) ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have h2 : orderOf (x : ↥L) ∣ Nat.card (Subgroup.center ↥L) :=
      Subgroup.orderOf_dvd_natCard _ hxZ
    have hcop : Nat.Coprime 3 (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hZ
    have : orderOf (x : ↥L) = 1 :=
      Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
    exact Subgroup.mem_bot.2 (Subtype.ext (orderOf_eq_one_iff.1 this))
  refine ⟨E.map q, CFSG.AGLEmbedding.BlockCyc.isElemAbelian_map q hel, ?_⟩
  have e := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at e
  rw [← e, hcard]

theorem not_dvd_27_card_psl_two {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) {r : ℕ}
    (hr : r = 3 ∨ r = 4) :
    ¬ 27 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) := by
  have : Fintype F := Fintype.ofFinite F
  have hF' : Fintype.card F = 2 := by rw [← Nat.card_eq_fintype_card]; exact hF
  intro h
  have h1 : Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin (r + 1)) F) ∣
      Nat.card (Matrix.SpecialLinearGroup (Fin (r + 1)) F) := Subgroup.card_quotient_dvd_card _
  have h2 := Matrix.card_SL_field (n := r + 1) (𝔽 := F)
  rw [hF'] at h2
  rcases hr with rfl | rfl
  · simp [Fin.prod_univ_succ] at h2
    rw [h2] at h1
    have := h.trans h1
    omega
  · simp [Fin.prod_univ_succ] at h2
    rw [h2] at h1
    have := h.trans h1
    omega

end CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank
