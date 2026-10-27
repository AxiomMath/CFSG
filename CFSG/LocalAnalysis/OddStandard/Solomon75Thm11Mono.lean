module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11Lift

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

theorem IsAhatIntr.subgroupOf {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}
    (h : IsAhatIntr X t L) {H : Subgroup X} (htH : t ∈ H) (hLH : L ≤ H) :
    IsAhatIntr ↥H ⟨t, htH⟩ (L.subgroupOf H) := by
  obtain ⟨hLC, htL, hpc, n, hn, hcov⟩ := h
  refine ⟨?_, htL, ?_, n, hn, ?_⟩
  · rw [centralizer_singleton_subgroup htH]
    exact Subgroup.subgroupOf_mono H hLC
  · rw [centralizer_singleton_subgroup htH]
    exact (isPComponent_subgroupOf_subgroupOf_iff hLC hLH).2
      (isPComponent_subgroupOf_mono (le_inf hLC hLH) inf_le_left hpc)
  · obtain ⟨q⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hLH)
    exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr q.symm hcov

theorem IsMLIntr.subgroupOf {X : Type} [Group X] [Finite X] {t : X} {M : Subgroup X}
    (h : IsMLIntr X t M) {H : Subgroup X} (htH : t ∈ H) (hMH : M ≤ H) :
    IsMLIntr ↥H ⟨t, htH⟩ (M.subgroupOf H) := by
  obtain ⟨hMC, hpc, htype, hcov⟩ := h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [centralizer_singleton_subgroup htH]
    exact Subgroup.subgroupOf_mono H hMC
  · rw [centralizer_singleton_subgroup htH]
    exact (isPComponent_subgroupOf_subgroupOf_iff hMC hMH).2
      (isPComponent_subgroupOf_mono (le_inf hMC hMH) inf_le_left hpc)
  · obtain ⟨q⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hMH)
    rcases htype with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨q.trans e⟩
    · exact Or.inr ⟨q.trans e⟩
  · intro s' hs' hs'2
    have hsM : (s' : X) ∈ M := hs'
    have hsH : (s' : X) ∈ H := s'.2
    have hs2 : orderOf (s' : X) = 2 := by rw [Subgroup.orderOf_coe]; exact hs'2
    obtain ⟨J, ⟨hJC, hsJ, hJpc, n, hn, hdc⟩, hJcov⟩ := hcov (s' : X) hsM hs2
    have hcen : centralizer ({s'} : Set ↥H) = (centralizer ({(s' : X)} : Set X)).subgroupOf H :=
      centralizer_singleton_subgroup s'.2
    obtain ⟨J', hJ'CH, hJ'pc, hJ'cov, hJ'two, ⟨q⟩⟩ := exists_isPComponent_inf_of_covered
      (C := cen (s' : X)) (H := H) (O := oddCoreOf (cen (s' : X))) (E := M ⊓ cen (s' : X))
      (J := J) (oddCoreOf_le _) (le_normalizer_oddCoreOf _) (odd_card_oddCoreOf _) inf_le_right
      (inf_le_left.trans hMH) hJC hJpc hJcov
    have hJ'C : J' ≤ cen (s' : X) := (hJ'CH.trans inf_le_left)
    have hJ'H : J' ≤ H := (hJ'CH.trans inf_le_right)
    have hs2' : (s' : X) ^ 2 ^ 1 = 1 := by
      rw [pow_one, ← hs2]
      exact pow_orderOf_eq_one _
    have hsJ' : (s' : X) ∈ J' :=
      hJ'two (s' : X) (Subgroup.mem_inf.2 ⟨hsJ, hsH⟩) ⟨1, hs2'⟩
    refine ⟨J'.subgroupOf H, ⟨?_, hsJ', ?_, n, hn, ?_⟩, ?_⟩
    · rw [hcen]
      exact Subgroup.subgroupOf_mono H hJ'C
    · rw [hcen]
      exact (isPComponent_subgroupOf_subgroupOf_iff hJ'C hJ'H).2 hJ'pc
    · obtain ⟨q₀⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hJ'H)
      exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr (q₀.trans q).symm hdc
    · have h1 : J'.subgroupOf H ≤
          (M ⊓ cen (s' : X) ⊔ oddCoreOf (cen (s' : X)) ⊓ H).subgroupOf H :=
        Subgroup.subgroupOf_mono H hJ'cov
      rw [Subgroup.subgroupOf_sup (inf_le_left.trans hMH) inf_le_right,
        show (M ⊓ cen (s' : X)).subgroupOf H =
          M.subgroupOf H ⊓ (cen (s' : X)).subgroupOf H from Subgroup.comap_inf _ _ _,
        ← hcen, Subgroup.inf_subgroupOf_right] at h1
      refine h1.trans (sup_le_sup_left ?_ _)
      refine le_oddCoreOf_of_normalized ?_ ?_ ?_
      · rw [hcen]
        exact Subgroup.subgroupOf_mono H (oddCoreOf_le _)
      · intro c hc x
        rw [hcen] at hc
        have hc' : (c : X) ∈ cen (s' : X) := hc
        have hn := Subgroup.mem_normalizer_iff.mp (le_normalizer_oddCoreOf (cen (s' : X)) hc')
          (x : X)
        exact hn
      · have e1 : Nat.card ↥((oddCoreOf (cen (s' : X))).subgroupOf H) =
            Nat.card ↥(oddCoreOf (cen (s' : X)) ⊓ H) := by
          rw [← Subgroup.inf_subgroupOf_right (oddCoreOf (cen (s' : X))) H]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
        rw [e1]
        exact (odd_card_oddCoreOf (cen (s' : X))).of_dvd_nat
          (Subgroup.card_dvd_of_le inf_le_left)

theorem SolomonThm11At.le_KProdIn {X : Type} [Group X] [Finite X] {H : Subgroup X}
    (hH : SolomonThm11At ↥H) {t : X} (ht : orderOf t = 2) (htH : t ∈ H) {L : Subgroup X}
    (hLH : L ≤ H) (hL : IsAhatIntr X t L ∨ IsMLIntr X t L) : L ≤ KProdIn H := by
  have ht' : orderOf (⟨t, htH⟩ : ↥H) = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have h1 : L.subgroupOf H ≤ KProd ↥H := hH ⟨t, htH⟩ ht' (L.subgroupOf H)
    (hL.imp (fun h => h.subgroupOf htH hLH) (fun h => h.subgroupOf htH hLH))
  have h2 := Subgroup.map_mono (f := H.subtype) h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hLH] at h2

end CFSG.OddStandard.Solomon75
