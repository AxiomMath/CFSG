module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.ConnPath
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.ConnModel
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.GammaProof.ConnOut

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] [Finite G] {a z : G}

theorem gamma_W_Q (H : GammaHyps a z) {t : G} (htQ : t ∈ Qz z) (ht : IsConj z t) (htz : t ≠ z) :
    ∃ w : G, IsConj a w ∧ w ∈ Gx z ∧ w ∈ Gx t := by
  obtain ⟨v, w, hvQ, hvz, hvne, hwA, hwz, hwv⟩ := gamma_exists_QB_comm H
  obtain ⟨k, hkGz, hkvt⟩ :=
    (H.hOrb.self).orbit_QB.1.transitive v ⟨hvQ, hvz, hvne⟩ t ⟨htQ, ht, htz⟩
  have hwv' : v * w = w * v := mem_Gx.mp hwv
  refine ⟨k * w * k⁻¹, hwA.trans (isConj_iff.mpr ⟨k, rfl⟩), ?_, ?_⟩
  · exact (Gx z).mul_mem ((Gx z).mul_mem hkGz hwz) ((Gx z).inv_mem hkGz)
  · rw [mem_Gx, ← hkvt]
    calc (k * v * k⁻¹) * (k * w * k⁻¹) = k * (v * w) * k⁻¹ := by group
      _ = k * (w * v) * k⁻¹ := by rw [hwv']
      _ = (k * w * k⁻¹) * (k * v * k⁻¹) := by group

theorem gamma_connected (H : GammaHyps a z) : (Gamma a).Connected := by
  have key : ∀ c : G, ∀ hc : IsConj a c,
      (Gamma a).Reachable ⟨a, IsConj.refl a⟩ ⟨c, hc⟩ := by
    intro c hc
    obtain ⟨b₀, hb₀⟩ : (orb2B a z a).Nonempty := by
      simpa [tab5Set] using ((H.hT5.self).partition.orbit 1).nonempty
    let z' : G := a * b₀
    have hz' : IsConj z z' := hb₀.2
    have haa : a * a = 1 := H.mul_self_a (IsConj.refl a)
    have hcomm_a : a * b₀ = b₀ * a := H.comm_of_orb2B (IsConj.refl a) hb₀
    have hz'a : a * z' = z' * a := by
      show a * (a * b₀) = (a * b₀) * a
      rw [show a * (a * b₀) = b₀ by rw [← mul_assoc, haa, one_mul],
        show (a * b₀) * a = b₀ by rw [hcomm_a, mul_assoc, haa, mul_one]]
    have hz'a' : z' * a = a * z' := hz'a.symm
    have hz'2 : z' ^ 2 = 1 := H.sq_z hz'
    have heven : Even (orderOf (z' * c)) := by
      by_contra hodd
      exact H.not_isConj_both hc
        (hz'.trans (isConj_of_odd_orderOf_mul hz'2 (H.sq_a hc) (Nat.not_even_iff_odd.mp hodd)))
    obtain ⟨t, -, ht2, ht1, htz', htc, -⟩ :=
      exists_central_involution_of_even_orderOf_mul hz'2 (H.sq_a hc) heven
    have htord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
    rcases (H.hCls.self).inv_two t htord with htA | htB
    · refine (gamma_reach_of_inv H (IsConj.refl a) htA ?_).trans
        (gamma_reach_of_inv H htA hc ?_)
      · exact ⟨z', H.orderOf_z hz', mem_Gxy.mpr ⟨mem_Gx.mpr hz'a, mem_Gx.mpr htz'⟩⟩
      · exact ⟨t, htord, mem_Gxy.mpr ⟨self_mem_Gx t, mem_Gx.mpr htc.symm⟩⟩
    · have hz't : IsConj z' t := hz'.symm.trans htB
      have hwt : ∃ w : G, IsConj a w ∧ w ∈ Gx z' ∧ w ∈ Gx t := by
        by_cases ht_eq : t = z'
        · rw [ht_eq]
          exact ⟨a, IsConj.refl a, mem_Gx.mpr hz'a', mem_Gx.mpr hz'a'⟩
        · by_cases htQ : t ∈ Qz z'
          · exact gamma_W_Q (H.of_isConj (IsConj.refl a) hz') htQ hz't ht_eq
          · exact gamma_W_out (H.of_isConj (IsConj.refl a) hz') (mem_Gx.mpr htz'.symm) htQ hz't
      obtain ⟨w, hwA, hwz', hwt'⟩ := hwt
      have hwz'c : w * z' = z' * w := (mem_Gx.mp hwz').symm
      have hwtc : w * t = t * w := (mem_Gx.mp hwt').symm
      refine (gamma_reach_of_inv H (IsConj.refl a) hwA ?_).trans
        (gamma_reach_of_inv H hwA hc ?_)
      · exact ⟨z', H.orderOf_z hz', mem_Gxy.mpr ⟨mem_Gx.mpr hz'a, mem_Gx.mpr hwz'c⟩⟩
      · exact ⟨t, htord, mem_Gxy.mpr ⟨mem_Gx.mpr hwtc, mem_Gx.mpr htc.symm⟩⟩
  refine (SimpleGraph.connected_iff_exists_forall_reachable (Gamma a)).2
    ⟨⟨a, IsConj.refl a⟩, fun v => ?_⟩
  exact key v.1 v.2

end CFSG.EvenSporadicStandard.HNRecog.Section3
