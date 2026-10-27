module

public import CFSG.LocalAnalysis.AGLEmbedding.ToralCensusHubCenter

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus

open CFSG.Open CFSG.AGLEmbedding TauCeti

theorem odd_card_center_of_twistedA (hGA : CFSG.Open.GriessAllModelsStatement) {A : Type}
    [Group A] [Finite A] [Group.IsPerfect A] {r : ℕ} {q : PrimePower}
    (hv : (LieTypeIndex.twistedA r q).Valid) (hq2 : q.p = 2) (hq : q.card ≠ 2)
    (e : A ⧸ Subgroup.center A ≃* (CFSGIndex.lie ⟨.twistedA r q, hv⟩).Group) :
    Odd (Nat.card (Subgroup.center A)) := by
  have hc := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA r q hv (MulEquiv.refl _)
  have hm : CFSG.Models.LieModel _ _ _ _ _ := ⟨hc.1, Or.inl hc⟩
  have hf2 : 2 ≤ q.exponent := by
    have h1 := q.exponent_pos
    by_contra h
    apply hq
    rw [PrimePower.card_def, hq2]
    have : q.exponent = 1 := by omega
    rw [this]; norm_num
  rw [hq2] at hm
  have h := ToralCensus.card_center_dvd_multiplierOrders hGA e hm
  obtain ⟨g, hg⟩ : ∃ g, q.exponent = g + 2 := ⟨q.exponent - 2, by omega⟩
  rw [hg] at h
  simp only [CFSG.Blueprint.Multiplier.genericOrders,
    CFSG.Blueprint.Multiplier.exceptionalOrders] at h
  rw [mul_one, one_mul, mul_one] at h
  have hodd : Odd (2 ^ (g + 2) + 1) :=
    (Nat.even_pow' (by omega)).2 even_two |>.add_one
  exact hodd.of_dvd_nat (h.trans (Nat.gcd_dvd_right _ _))

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus
