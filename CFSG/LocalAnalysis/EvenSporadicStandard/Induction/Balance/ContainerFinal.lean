module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerCore
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerAlt
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Exclusion2
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Balance.ContainerDefs

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup CFSG CFSG.GH74.GLS CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.McLStd

theorem exists_doubleCover_of_containerCase (hC : CatalogNoFixedDoubleCover) {k : ℕ}
    (hk : k = 8 ∨ k = 11) {G : Type} [Group G] [Finite G] {L : Subgroup G} (h : StdHyp G L)
    {t u : G} (ht : t ∈ centralizer (L : Set G)) (ht2 : orderOf t = 2) (hu : u ∈ L)
    (hu2 : orderOf u = 2) (hB : IsDoubleCoverOfAlt ↥(centralizer ({u} : Set G) ⊓ L) k)
    (hA : ContainerCase L t u) :
    ∃ m : ℕ, 8 ≤ m ∧
      IsDoubleCoverOfAlt (↥(layerClosure L u) ⧸ pPrimeCore 2 ↥(layerClosure L u)) m := by
  have := h.simple
  set H : Subgroup G := centralizer ({u} : Set G) with hHdef
  set B : Subgroup G := H ⊓ L with hBdef
  set K : Subgroup G := layerClosure L u with hKdef
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp hA.1.1
  have hBK : B ≤ K := le_layerClosure L u
  have huB : u ∈ B := ⟨mem_centralizer_singleton_iff.2 rfl, hu⟩
  have hu1 : u ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hu2
    exact absurd hu2 (by decide)
  have hcen : center G = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h' | h'
    · exact h'
    · obtain ⟨a, b, hab⟩ := h.nonabelian
      exact absurd (mem_center_iff.1 (h' ▸ mem_top b) a) hab
  have hHtop : H ≠ ⊤ := by
    intro htop
    have hucen : u ∈ center G := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ H := htop ▸ mem_top g
      exact mem_centralizer_singleton_iff.1 hg
    rw [hcen, mem_bot] at hucen
    exact hu1 hucen
  have hKtop : K ≠ ⊤ := by
    intro hKt
    rw [hKt] at hKH
    exact hHtop (top_le_iff.1 hKH)
  have hOH : pPrimeCore 2 ↥H = ⊥ :=
    pPrimeCore_eq_bot_of_standardComponentOddCore_eq_bot (h.oddCore u hu2)
  have hsub : (K.subgroupOf H).IsSubnormal :=
    CFSG.QuasithinUnique.Id2519.subgroupOf_isSubnormal_of_open
      (CFSG.Quasithin.subnormal_of_mem_cComp hA.1.1)
  have hOK : pPrimeCore 2 ↥K = ⊥ := pPrimeCore_eq_bot_of_isSubnormal hKH hsub hOH
  have hKq : CFSG.IsQuasisimple ↥K := isQuasisimple_of_pPrimeCore_eq_bot hA.1.2 hOK
  have hZK : IsPGroup 2 ↥(center ↥K) := isPGroup_center_of_pPrimeCore_eq_bot hOK
  have hcat : CFSG.Blueprint.Catalog (↥K ⧸ center ↥K) :=
    catalog_center_quotient_of_kProper h.kProper hKtop hKq
  have hBt : B ≤ centralizer ({t} : Set G) := fun b hb =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht b hb.2)
  have hnorm := normal_subgroupOf_inf_centralizer h ht ht2 hKH
  have hucomm : ∀ x ∈ K, u * x = x * u := fun x hx =>
    (mem_centralizer_singleton_iff.1 (hKH hx)).symm
  have hZ : ∀ z ∈ B, (∀ b ∈ B, z * b = b * z) → ∀ x ∈ K, z * x = x * z := by
    intro z hzB hzc x hxK
    rcases eq_one_or_eq_of_center_card_two hB.2.1 huB hu1
      (fun b hb => hucomm b (hBK hb)) hzB hzc with hz1 | hzu
    · rw [hz1, one_mul, mul_one]
    · rw [hzu]
      exact hucomm x hxK
  by_cases halt : IsAltType (↥K ⧸ center ↥K)
  · obtain ⟨m, hm5, ⟨e⟩⟩ := halt
    have hk8 : 8 ≤ k := by rcases hk with rfl | rfl <;> norm_num
    obtain ⟨hkm, hcov⟩ := doubleCover_of_alt hk8 hm5 hKq hZK hBK hB hZ huB hu2 hucomm e
    refine ⟨m, le_trans hk8 hkm, ?_⟩
    exact CFSG.GH74.GLS.Stage12.McLRec.isDoubleCoverOfAlt_congr
      ((QuotientGroup.quotientMulEquivOfEq hOK).trans QuotientGroup.quotientBot).symm hcov
  · exact (hC k hk G K B t hKq hZK hcat halt ht2 hA.2 hBK hBt hB hZ hnorm).elim

theorem containerIsDoubleCover_of_catalog (hC : CatalogNoFixedDoubleCover)
    {s : TauCeti.SporadicName} {k : ℕ} (hk : k = 8 ∨ k = 11)
    (hcov : ∀ (T : Type) [Group T], IsSporadic T s → ∀ t : T, orderOf t = 2 →
      IsDoubleCoverOfAlt ↥(centralizer ({t} : Set T)) k) : ContainerIsDoubleCover s := by
  intro G _ _ L hStd hL t u ht ht2 hu hu2 hA
  have hu2' : orderOf (⟨u, hu⟩ : ↥L) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact hu2
  have hB : IsDoubleCoverOfAlt ↥(centralizer ({u} : Set G) ⊓ L) k :=
    isDoubleCoverOfAlt_inf hu (hcov ↥L hL ⟨u, hu⟩ hu2')
  exact exists_doubleCover_of_containerCase hC hk hStd ht ht2 hu hu2 hB hA

theorem containerIsDoubleCover_mcl
    (hC : CatalogNoFixedDoubleCover) : ContainerIsDoubleCover .McL :=
  containerIsDoubleCover_of_catalog hC (Or.inl rfl) fun _ _ hT _ ht =>
    isDoubleCoverOfAlt_mcl hT ht

theorem containerIsDoubleCover_ly
    (hC : CatalogNoFixedDoubleCover) :
    ContainerIsDoubleCover .Ly :=
  containerIsDoubleCover_of_catalog hC (Or.inr rfl) fun _ _ hT _ ht =>
    LyStd.isDoubleCoverOfAlt_ly hT ht

theorem mcLLyContainerInputs_of_catalog
    (hS : ComponentClassification.GSThmB.Solomon2AnInput) (hC : CatalogNoFixedDoubleCover) :
    McLLyContainerInputs :=
  ⟨hS, containerIsDoubleCover_mcl hC, containerIsDoubleCover_ly hC⟩

end CFSG.EvenSporadicStandard.Induction.Balance
