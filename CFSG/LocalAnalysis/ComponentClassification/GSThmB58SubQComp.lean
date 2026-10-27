module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubQ
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB58SubW
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecData

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

variable {X : Type} [Group X] [Finite X] {h : Hyp52 X} {y : X}

namespace Hyp52

namespace SubQAux

theorem le_secL0_of_isPComponent {M : Subgroup X} (hMC : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X)))) : M ≤ h.secL0 y := by
  have h1 := map_mono (f := (centralizer (h.secB0 y : Set X)).subtype)
    (show M.subgroupOf (centralizer (h.secB0 y : Set X)) ≤ pLayer _ 2 from le_sSup hM)
  rwa [map_subgroupOf_eq_of_le hMC] at h1

theorem le_secSub_of_isPComponent {M : Subgroup X} (hMC : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X)))) : M ≤ h.secSub y :=
  (le_secL0_of_isPComponent hMC hM).trans (h.secL0_le_secSub y)

end SubQAux

theorem isPComponent_map_subQ {M : Subgroup X} (hMC : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X)))) :
    IsPComponent 2 ((M.subgroupOf (h.secSub y)).map (h.subQ y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMG : M ≤ h.secG0 y := hMC.trans (h.centralizer_le_G0 y)
  have hMH' : M ≤ h.secSub y := SubQAux.le_secSub_of_isPComponent hMC hM
  have hMH : h.secImage y M ≤ h.secSubImg y := secImage_mono hMH'
  have h1 : IsPComponent 2 (M.subgroupOf (h.secG0 y)) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_isSubnormal hMC (h.centralizer_le_G0 y)
      (Subgroup.Normal.isSubnormal (Subgroup.normal_subgroupOf_centralizer_normalizer _)) hM
  have h2 := secImage_isPComponent hMG le_rfl hMC h1
  have htop : h.secImage y (h.secG0 y) = ⊤ := by
    show ((h.secG0 y).subgroupOf (h.secG0 y)).map (h.secMk y) = ⊤
    rw [subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  rw [htop] at h2
  have h3 : IsPComponent 2 ((h.secImage y M).subgroupOf (h.secSubImg y)) :=
    CatalogueBPrimeJoin.pComponent_subgroupOf_of_le hMH le_top h2
  have h4 := OddQuot.isPComponent_map (QuotientGroup.mk' (pPrimeCore 2 ↥(h.secSubImg y)))
    OddQuot.not_two_dvd_card_ker le_top
    (show IsPComponent 2 (((h.secImage y M).subgroupOf (h.secSubImg y)).subgroupOf ⊤) from
      B5a.isPComponent_subgroupOf_top_iff.mpr h3)
  rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _),
    B5a.isPComponent_subgroupOf_top_iff] at h4
  rw [map_subQ hMH']
  exact h4

theorem subQ_map_eq (h' : Hyp59 (h.subQuot y)) {M : Subgroup X}
    (hMC : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X)))) :
    (M.subgroupOf (h.secSub y)).map (h.subQ y) = conjClosure h'.J (pLayer (h.subQuot y) 2) := by
  have hpc := isPComponent_map_subQ hMC hM
  exact h'.generalizedFitting_simple.2.2.2.2 _
    (B5a.isComponent_of_isPComponent h'.oddCore_eq_bot hpc)

theorem eq_of_isPComponent_centralizer_sub (h' : Hyp59 (h.subQuot y)) {N M : Subgroup X}
    (hNC : N ≤ centralizer (h.secB0 y : Set X))
    (hN : IsPComponent 2 (N.subgroupOf (centralizer (h.secB0 y : Set X))))
    (hMC : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X)))) : N = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hNM
  set C := centralizer (h.secB0 y : Set X) with hC
  have hne : N.subgroupOf C ≠ M.subgroupOf C := fun h1 => hNM (by
    have := congrArg (Subgroup.map C.subtype) h1
    rwa [map_subgroupOf_eq_of_le hNC, map_subgroupOf_eq_of_le hMC] at this)
  obtain ⟨-, -, hcomm, -⟩ :=
    (CatalogueBPrimeJoin.distinct_p_components_core_commutation 2 Nat.prime_two _ _ hN hM).2 hne
  have hcommX : ⁅N, M⁆ ≤ oddCoreIn M := by
    have h1 := map_mono (f := C.subtype) (hcomm.trans inf_le_right)
    rwa [map_commutator, map_subgroupOf_eq_of_le hNC, map_subgroupOf_eq_of_le hMC,
      pPrimeCore_map_subgroupOf 2 M C hMC] at h1
  set Λ := conjClosure h'.J (pLayer (h.subQuot y) 2) with hΛ
  obtain ⟨-, -, -, hcomp, -⟩ := h'.generalizedFitting_simple
  rw [← hΛ] at hcomp
  have hNH : N ≤ h.secSub y := SubQAux.le_secSub_of_isPComponent hNC hN
  have hMH : M ≤ h.secSub y := SubQAux.le_secSub_of_isPComponent hMC hM
  have hNΛ : (N.subgroupOf (h.secSub y)).map (h.subQ y) = Λ := subQ_map_eq h' hNC hN
  have hMΛ : (M.subgroupOf (h.secSub y)).map (h.subQ y) = Λ := subQ_map_eq h' hMC hM
  have hperf : ⁅Λ, Λ⁆ = Λ := by
    have : Group.IsPerfect ↥Λ := hcomp.1.1
    exact Subgroup.commutator_eq_self
  have himg : (⁅N, M⁆.subgroupOf (h.secSub y)).map (h.subQ y) = Λ := by
    rw [← SubWAux.commutator_subgroupOf hNH hMH, map_commutator, hNΛ, hMΛ, hperf]
  set Ô := ((oddCoreIn M).subgroupOf (h.secSub y)).map (h.subQ y) with hÔ
  have hOM : oddCoreIn M ≤ M := map_subtype_le _
  have hÔΛ : Ô ≤ Λ := by
    rw [← hMΛ]
    exact map_mono (fun w hw => mem_subgroupOf.mpr (hOM (mem_subgroupOf.mp hw)))
  have hΛÔ : Λ ≤ Ô := by
    rw [← himg]
    exact map_mono (fun w hw => mem_subgroupOf.mpr (hcommX (mem_subgroupOf.mp hw)))
  have hodd : ¬ 2 ∣ Nat.card Ô := by
    intro h2
    have h3 : Nat.card Ô ∣ Nat.card ((oddCoreIn M).subgroupOf (h.secSub y)) :=
      Subgroup.card_map_dvd _ _
    have h4 : Nat.card ((oddCoreIn M).subgroupOf (h.secSub y)) = Nat.card (pPrimeCore 2 ↥M) := by
      rw [Nat.card_congr (subgroupOfEquivOfLe (hOM.trans hMH)).toEquiv, oddCoreIn,
        card_map_of_injective M.subtype_injective]
    rw [h4] at h3
    exact Nat.not_coprime_of_dvd_of_dvd one_lt_two dvd_rfl (h2.trans h3)
      (pPrimeCore_coprime_card (p := 2) (G := ↥M))
  have heven : Even (Nat.card Λ) := even_card_of_isQuasisimple' hcomp.1
  apply hodd
  rw [le_antisymm hÔΛ hΛÔ]
  exact even_iff_two_dvd.mp heven

theorem layerIn_centralizer_eq_sub (h' : Hyp59 (h.subQuot y)) {M : Subgroup X}
    (hMC : M ≤ centralizer (h.secB0 y : Set X))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer (h.secB0 y : Set X)))) : h.secL0 y = M := by
  set C := centralizer (h.secB0 y : Set X) with hC
  apply le_antisymm
  · show (pLayer ↥C 2).map C.subtype ≤ M
    rw [map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    have hN' : IsPComponent 2 ((N.map C.subtype).subgroupOf C) := by
      rwa [show (N.map C.subtype).subgroupOf C = N from
        comap_map_eq_self_of_injective C.subtype_injective N]
    have heq := eq_of_isPComponent_centralizer_sub h' (map_subtype_le N) hN' hMC hM
    intro w hw
    rw [mem_comap, ← heq]
    exact mem_map_of_mem _ hw
  · intro m hm
    have hle : M.subgroupOf C ≤ pLayer ↥C 2 :=
      le_sSup (show M.subgroupOf C ∈ {L : Subgroup ↥C | IsPComponent 2 L} from hM)
    exact ⟨⟨m, hMC hm⟩, hle (mem_subgroupOf.mpr hm), rfl⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
