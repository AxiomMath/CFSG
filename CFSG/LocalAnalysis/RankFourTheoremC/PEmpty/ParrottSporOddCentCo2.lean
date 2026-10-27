module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.ParrottSporOddCent
public import CFSG.Sporadic.Co2HeavyRank
public import CFSG.Sporadic.Co2Schreier.InvolClasses
public import CFSG.Sporadic.Presentation.Co2Exact

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Sporadic.Co2Schreier CFSG.Sporadic.Co2Cert CFSG.QuasithinUnique.Lin2.RankCert

theorem co2P_inv_not_commute
    {p : ℕ} (h0 : ¬ p ∣ 743178240) (h1 : ¬ p ∣ 41287680) (h2 : ¬ p ∣ 1474560) :
    ∀ t z : ↥co2P, orderOf t = 2 → orderOf z = p → t * z ≠ z * t := by
  intro t z ht hz htz
  have key : ∀ x : ↥co2P, IsConj t x →
      Nat.card ↥(co2P ⊓ Subgroup.centralizer {(x : Equiv.Perm (Fin 2300))}) =
        Nat.card ↥(co2P ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 2300))}) := by
    intro x hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hx
    have hxc : (x : Equiv.Perm (Fin 2300)) = (c : Equiv.Perm (Fin 2300)) *
        (t : Equiv.Perm (Fin 2300)) * (c : Equiv.Perm (Fin 2300))⁻¹ := by
      rw [← hc]
      rfl
    rw [hxc, card_inf_centralizer_conj c.2]
  have hzmem : (z : Equiv.Perm (Fin 2300)) ∈
      co2P ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 2300))} :=
    ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val htz).symm⟩
  have hdvd : p ∣ Nat.card ↥(co2P ⊓ Subgroup.centralizer {(t : Equiv.Perm (Fin 2300))}) := by
    rw [← hz, ← Subgroup.orderOf_coe, ← Subgroup.orderOf_mk _ hzmem]
    exact orderOf_dvd_natCard _
  rcases isConj_cases_myRep t ht with h | h | h
  · rw [← key zP h, show ((zP : ↥co2P) : Equiv.Perm (Fin 2300)) = locZ from rfl,
      ← locC_eq_centralizer, card_locC] at hdvd
    exact h0 hdvd
  · rw [← key tP h, show ((tP : ↥co2P) : Equiv.Perm (Fin 2300)) = locT from rfl,
      ← locD_eq_centralizer, card_locD] at hdvd
    exact h1 hdvd
  · rw [← key uP h, show ((uP : ↥co2P) : Equiv.Perm (Fin 2300)) = locU from rfl,
      show co2P ⊓ Subgroup.centralizer {locU} = locH3 from rfl, card_locH3] at hdvd
    exact h2 hdvd

theorem row_Co2_23 :
    KFactSporLocalRow .Co2 23 := by
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.Co2.nonempty_mulEquiv
  have e0 : (TauCeti.CFSGIndex.sporadic .Co2).Group ≃* CFSG.Blueprint.NativeSporadic.Co2 := b.symm
  have h11 : orderOf (2 : ZMod 23) = 11 :=
    orderOf_two_zmod_eq 23 11 (by norm_num) (by decide) (by decide)
  refine row_of_oddCent_rank ↥co2P ⟨(e0.trans co2PermEquiv).symm⟩
    (co2P_inv_not_commute (by norm_num) (by norm_num) (by norm_num)) ?_
  rw [h11]
  exact CFSG.Sporadic.Co2Heavy.elemAbelianLt_co2P

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
