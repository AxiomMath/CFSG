module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Cover82A
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5aSecData
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB7TransL
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.ComponentClassification.CatFactsL4U4

namespace Cover82

open CFSG Subgroup CFSG.ComponentClassification.GSThmB

theorem center_eq_bot_of_isPGroup_center {Y : Type} [Group Y] [Finite Y] {p f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hf : 1 ≤ f) (hYq : IsQuasisimple Y)
    (hZ2 : IsPGroup 2 (center Y))
    (htype : Blueprint.LieModel (Y ⧸ center Y) .PSL 4 p f ∨
      Blueprint.LieModel (Y ⧸ center Y) .PSU 4 p f)
    {ℓ : Y} (hℓ : ℓ * ℓ = 1) {M : Subgroup Y} (hMC : M ≤ centralizer ({ℓ} : Set Y))
    (hM : IsPComponent 2 (M.subgroupOf (centralizer ({ℓ} : Set Y))))
    (hMtype : IsSec8JType (↥M ⧸ pPrimeCore 2 ↥M) p f) : center Y = ⊥ := by
  classical
  have : Group.IsPerfect Y := hYq.1
  have hℓ2 : ℓ ^ 2 ∈ center Y := by
    rw [sq, hℓ]
    exact one_mem _
  obtain ⟨hJc, ⟨s, hs, hs2, hsq, -, hsJ⟩, hnc⟩ := jdata hp hp2 hf hMtype
  have hJp : ⁅M, M⁆ = M := commutator_eq_self_of_isPComponent hMC hM
  by_cases hℓZ : ℓ ∈ center Y
  · exfalso
    have hCY : centralizer ({ℓ} : Set Y) = ⊤ := by
      refine eq_top_iff.mpr fun w _ => ?_
      rw [mem_centralizer_singleton_iff]
      exact mem_center_iff.mp hℓZ w
    rw [hCY, B5a.isPComponent_subgroupOf_top_iff] at hM
    obtain ⟨-, -, hMsn, -, -⟩ := hM
    have hq := le_sq_mul (three_le_pow hp hp2 hf)
    rcases hMsn.lt_normal with htop | ⟨K, hKn, hMK, hKlt⟩
    · let eM : ↥M ≃* Y := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
      have hYJ : IsSec8JType (Y ⧸ pPrimeCore 2 Y) p f :=
        isSec8JType_of_mulEquiv (UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 eM)
          hMtype
      exact false_of_central hp hp2 hf hYq (htype.elim Or.inl fun h => Or.inr (Or.inl h)) hYJ
    · have : K.Normal := hKn
      rcases LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hYq K with hK | hK
      · have hMb : M = ⊥ := by
          rw [← hJp, commutator_eq_bot_iff_le_centralizer]
          exact (hMK.trans hK).trans (center_le_centralizer _)
        have h1 : Nat.card M = 1 := by rw [hMb, card_bot]
        omega
      · exact absurd hK hKlt.ne
  rcases htype with hL | hU
  · obtain ⟨-, F, _, _, hF, ⟨eL⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hL
    let : Fintype F := Fintype.ofFinite F
    have hFq : Fintype.card F = p ^ f := by rw [Fintype.card_eq_nat_card, hF]
    have hqF : Odd (Fintype.card F) := hFq ▸ (hp.odd_of_ne_two hp2).pow
    exact center_eq_bot_of_inner_L4 hZ2 hqF eL hℓZ hℓ2 hMC hJp (by rw [hFq]; exact hJc) hs hs2
      (by rw [hFq]; exact hsq) hsJ hnc
  · obtain ⟨-, K', _, _, hK', ⟨eU⟩⟩ := statedClassicalModel_of_lieModel_ne_zero (by norm_num) hU
    have hUF : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K' :=
      ⟨hp, hf, by rw [hK', ← pow_mul, mul_comm]⟩
    exact center_eq_bot_of_inner_U4 hUF hZ2 hp2 eU hℓZ hℓ2 hMC hJp hJc hs hs2 hsq hsJ hnc

end Cover82

end CFSG.ComponentClassification.CatFactsL4U4

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped MatrixGroups

namespace Seven

variable {X : Type} [Group X] [Finite X]

theorem isPComponent_map_of_le_inf {L J₀ Y : Subgroup X} {t : X} (htL : t ∈ L)
    (ht : t * t = 1) (hJ0L : J₀ ≤ L) (hJ0t : J₀ ≤ centralizer ({t} : Set X))
    (hYt : L ⊓ centralizer ({t} : Set X) ≤ Y) (hJ0pc : IsPComponent 2 (J₀.subgroupOf Y)) :
    (J₀.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)) ≤
        centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨t, htL⟩} :
          Set (↥L ⧸ pPrimeCore 2 ↥L)) ∧
      IsPComponent 2 (((J₀.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L))).subgroupOf
        (centralizer ({QuotientGroup.mk' (pPrimeCore 2 ↥L) ⟨t, htL⟩} :
          Set (↥L ⧸ pPrimeCore 2 ↥L)))) ∧
      Nonempty (↥J₀ ⧸ pPrimeCore 2 ↥J₀ ≃*
        ↥((J₀.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L))) ⧸
          pPrimeCore 2 ↥((J₀.subgroupOf L).map (QuotientGroup.mk' (pPrimeCore 2 ↥L)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht'2 : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 := Subtype.ext ht
  have hJ0Lt : J₀ ≤ L ⊓ centralizer ({t} : Set X) := le_inf hJ0L hJ0t
  have hpc1 : IsPComponent 2 (J₀.subgroupOf (L ⊓ centralizer ({t} : Set X))) :=
    UnbalancedCorr.isPComponent_subgroupOf_of_le hJ0Lt hYt hJ0pc
  have hpc2 : IsPComponent 2 ((J₀.subgroupOf L).subgroupOf
      (centralizer ({⟨t, htL⟩} : Set ↥L))) := by
    rw [← inf_centralizer_subgroupOf htL]
    exact (UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff' inf_le_left 2
      Nat.prime_two).mpr hpc1
  have hMt : J₀.subgroupOf L ≤ centralizer ({⟨t, htL⟩} : Set ↥L) := by
    rw [← inf_centralizer_subgroupOf htL]
    intro v hv
    exact mem_subgroupOf.mpr (hJ0Lt (mem_subgroupOf.mp hv))
  obtain ⟨hMbt, hMbpc⟩ := isPComponent_centralizer_map ht'2 hMt hpc2
  obtain ⟨e₁⟩ := OddQuot.nonempty_quotient_pPrimeCore_equiv
    (QuotientGroup.mk' (pPrimeCore 2 ↥L)) OddQuot.not_two_dvd_card_ker (J₀.subgroupOf L)
  let e₂ := UnbalancingLocal.Correspondence.quotientPPrimeCoreCongr 2 (subgroupOfEquivOfLe hJ0L)
  exact ⟨hMbt, hMbpc, ⟨e₂.symm.trans e₁⟩⟩

end Seven

end CFSG.ComponentClassification.GSThmB
