module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Thm11KProd
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aOddQuotTools

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.ComponentClassification.GSThmB
  CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X] {N : Subgroup X} [N.Normal]

omit [Finite X] in
theorem not_two_dvd_card_ker_mk' (hN : Odd (Nat.card N)) :
    ¬ 2 ∣ Nat.card (QuotientGroup.mk' N).ker := by
  rw [QuotientGroup.ker_mk']
  intro h
  exact (Nat.not_even_iff_odd.mpr hN) (even_iff_two_dvd.mpr h)

omit [Finite X] in
theorem exists_involution_lift_of_odd {M : Subgroup X} (hN : Odd (Nat.card N)) {sb : X ⧸ N}
    (hsb : sb ∈ M.map (QuotientGroup.mk' N)) (hsb2 : orderOf sb = 2) :
    ∃ s ∈ M, QuotientGroup.mk' N s = sb ∧ orderOf s = 2 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨y, hyM, hy⟩ := Subgroup.mem_map.1 hsb
  have hsq : sb ^ 2 = 1 := hsb2 ▸ pow_orderOf_eq_one sb
  have hy2 : y ^ 2 ∈ N := by
    refine (QuotientGroup.eq_one_iff (y ^ 2)).1 ?_
    change QuotientGroup.mk' N (y ^ 2) = 1
    rw [map_pow, hy, hsq]
  obtain ⟨c, hc⟩ := hN
  have hmker : (y ^ 2) ^ Nat.card N = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (Subgroup.orderOf_dvd_natCard N hy2)
  have hπs : QuotientGroup.mk' N (y ^ Nat.card N) = sb := by
    rw [map_pow, hy, hc, pow_succ, pow_mul, hsq, one_pow, one_mul]
  have hs2 : (y ^ Nat.card N) ^ 2 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hmker]
  refine ⟨y ^ Nat.card N, Subgroup.pow_mem M hyM _, hπs, orderOf_eq_prime hs2 fun h1 => ?_⟩
  rw [h1, map_one] at hπs
  rw [← hπs] at hsb2
  simp at hsb2

theorem isTwoGenQuasi_of_isAhatIntr {t : X} {L : Subgroup X} (h : IsAhatIntr X t L) :
    IsTwoGenQuasi ↥L :=
  (isTwoGenQuasi_subgroupOf_iff h.1).1 (isPComponent_two_iff.1 h.2.2.1).2

theorem isTwoGenQuasi_of_isMLIntr {t : X} {M : Subgroup X} (h : IsMLIntr X t M) :
    IsTwoGenQuasi ↥M :=
  (isTwoGenQuasi_subgroupOf_iff h.1).1 (isPComponent_two_iff.1 h.2.1).2

theorem IsAhatIntr.map_odd (hN : Odd (Nat.card N)) {t : X} (ht : orderOf t = 2)
    {L : Subgroup X} (h : IsAhatIntr X t L) :
    IsAhatIntr (X ⧸ N) (QuotientGroup.mk' N t) (L.map (QuotientGroup.mk' N)) := by
  obtain ⟨hLC, htL, hpc, n, hn, hcov⟩ := h
  have hker := not_two_dvd_card_ker_mk' hN
  have ht2 : t * t = 1 := by rw [← sq]; exact ht ▸ pow_orderOf_eq_one t
  have hcen := UnbalancedLayer.map_centralizer_eq hN ht2
  refine ⟨?_, Subgroup.mem_map_of_mem _ htL, ?_, n, hn, ?_⟩
  · rw [← hcen]
    exact Subgroup.map_mono hLC
  · have := OddQuot.isPComponent_map (QuotientGroup.mk' N) hker hLC hpc
    rwa [hcen] at this
  · obtain ⟨q⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv (QuotientGroup.mk' N) hker L
    exact GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr q hcov

theorem IsMLIntr.map_odd (hN : Odd (Nat.card N)) {t : X} (ht : orderOf t = 2)
    {M : Subgroup X} (h : IsMLIntr X t M) :
    IsMLIntr (X ⧸ N) (QuotientGroup.mk' N t) (M.map (QuotientGroup.mk' N)) := by
  obtain ⟨hMC, hpc, htype, hcov⟩ := h
  have hker := not_two_dvd_card_ker_mk' hN
  have ht2 : t * t = 1 := by rw [← sq]; exact ht ▸ pow_orderOf_eq_one t
  have hcen := UnbalancedLayer.map_centralizer_eq hN ht2
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hcen]
    exact Subgroup.map_mono hMC
  · have := OddQuot.isPComponent_map (QuotientGroup.mk' N) hker hMC hpc
    rwa [hcen] at this
  · obtain ⟨q⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv (QuotientGroup.mk' N) hker M
    rcases htype with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    · exact Or.inl ⟨q.symm.trans e⟩
    · exact Or.inr ⟨q.symm.trans e⟩
  · intro sb hsb hsb2
    obtain ⟨s, hsM, hπs, hs2⟩ := exists_involution_lift_of_odd hN hsb hsb2
    obtain ⟨J, hJ, hJcov⟩ := hcov s hsM hs2
    refine ⟨J.map (QuotientGroup.mk' N), ?_, ?_⟩
    · rw [← hπs]
      exact hJ.map_odd hN hs2
    · rw [← hπs]
      have hs2' : s * s = 1 := by rw [← sq]; exact hs2 ▸ pow_orderOf_eq_one s
      have hcens := UnbalancedLayer.map_centralizer_eq hN hs2'
      have h1 : J.map (QuotientGroup.mk' N) ≤
          ((M ⊓ cen s) ⊔ oddCoreOf (cen s)).map (QuotientGroup.mk' N) := Subgroup.map_mono hJcov
      rw [Subgroup.map_sup] at h1
      have hcens' : cen (QuotientGroup.mk' N s) = (cen s).map (QuotientGroup.mk' N) := hcens.symm
      have h2 : (oddCoreOf (cen s)).map (QuotientGroup.mk' N) =
          oddCoreOf (cen (QuotientGroup.mk' N s)) := by
        rw [hcens']
        exact OddQuot.map_oddCoreIn (QuotientGroup.mk' N) hker (cen s)
      rw [h2] at h1
      refine h1.trans (sup_le_sup_right ?_ _)
      exact le_inf (Subgroup.map_mono inf_le_left) (hcens ▸ Subgroup.map_mono inf_le_right)

theorem solomonThm11At_of_odd_quotient (hN : Odd (Nat.card N)) (h : SolomonThm11At (X ⧸ N)) :
    SolomonThm11At X := by
  intro t ht L hL
  have hπ := UnbalancedLayer.orderOf_mk_eq_two hN ht
  have hL' : IsAhatIntr (X ⧸ N) (QuotientGroup.mk' N t) (L.map (QuotientGroup.mk' N)) ∨
      IsMLIntr (X ⧸ N) (QuotientGroup.mk' N t) (L.map (QuotientGroup.mk' N)) :=
    hL.imp (fun h => h.map_odd hN ht) (fun h => h.map_odd hN ht)
  have hq : IsTwoGenQuasi ↥L := hL.elim isTwoGenQuasi_of_isAhatIntr isTwoGenQuasi_of_isMLIntr
  exact le_KProd_of_map_le_of_odd hN hq.1 (h _ hπ _ hL')

end CFSG.OddStandard.Solomon75
