module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import CFSG.GroupTheory.PCore.NormalPCoreOf
import CFSG.LieType.BorelTits.Basic
import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymSub

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Small

open CFSG.Open

theorem card_map_mk'_eq_relIndex {G : Type*} [Group G] (N T : Subgroup G) [N.Normal] :
    Nat.card (T.map (QuotientGroup.mk' N)) = N.relIndex T := by
  rw [← Subgroup.relIndex_ker, QuotientGroup.ker_mk']

theorem inf_normalCore_le_pCore {G : Type*} [Group G] {T : Subgroup G} (hT : IsPGroup 2 T) :
    (Subgroup.normalizer (T : Set G)).normalCore ⊓ T ≤ CFSG.pCore 2 G := by
  set D : Subgroup G := (Subgroup.normalizer (T : Set G)).normalCore with hD
  have hDN : D ≤ Subgroup.normalizer (T : Set G) := Subgroup.normalCore_le _
  have hDnormal : D.Normal := Subgroup.normalCore_normal _
  have hnorm : D ≤ Subgroup.normalizer ((D ⊓ T : Subgroup G) : Set G) := by
    intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hdT := Subgroup.mem_normalizer_iff.1 (hDN hd) x
    constructor
    · rintro ⟨hxD, hxT⟩
      exact ⟨hDnormal.conj_mem x hxD d, hdT.1 hxT⟩
    · rintro ⟨hxD, hxT⟩
      refine ⟨?_, hdT.2 hxT⟩
      have := hDnormal.conj_mem _ hxD d⁻¹
      simpa [mul_assoc] using this
  have h1 : D ⊓ T ≤ pCoreOf 2 D :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
      (hT.to_le inf_le_right)
  have h2 : pCoreOf 2 D ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.GroupTheory.pCoreOf_le_pCoreOf_of_le_normalizer 2 le_top
      (Subgroup.normalizer_eq_top_iff.2 hDnormal).ge
  rw [Sym.pCoreOf_top_eq] at h2
  exact h1.trans h2

theorem relIndex_pCore_le_two {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) (hidx : (Subgroup.normalizer (T : Set G)).index ∣ 3) :
    (CFSG.pCore 2 G).relIndex T ≤ 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := Subgroup.normalizer (T : Set G) with hN
  have hD6 : N.normalCore.index ∣ 6 := by
    have h1 : N.normalCore.index ∣ Nat.factorial N.index :=
      Subgroup.index_normalCore_dvd_factorial_index N
    have h2 : Nat.factorial N.index ∣ Nat.factorial 3 :=
      Nat.factorial_dvd_factorial (Nat.le_of_dvd (by norm_num) hidx)
    have h3 : Nat.factorial 3 = 6 := rfl
    rw [h3] at h2
    exact h1.trans h2
  have hle : (CFSG.pCore 2 G).relIndex T ∣ N.normalCore.relIndex T := by
    have := Subgroup.relIndex_dvd_of_le_left T (inf_normalCore_le_pCore hT)
    rwa [Subgroup.inf_relIndex_right] at this
  have h6 : (CFSG.pCore 2 G).relIndex T ∣ 6 :=
    hle.trans ((Subgroup.relIndex_dvd_index_of_normal ..).trans hD6)
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hT
  have h2n : (CFSG.pCore 2 G).relIndex T ∣ 2 ^ n := by
    have := Subgroup.relIndex_dvd_card (H := CFSG.pCore 2 G) (K := T)
    rwa [hn] at this
  have hcop : Nat.Coprime ((CFSG.pCore 2 G).relIndex T) 3 :=
    Nat.Coprime.coprime_dvd_left h2n (Nat.Coprime.pow_left n (by norm_num))
  have h2 : (CFSG.pCore 2 G).relIndex T ∣ 2 :=
    hcop.dvd_of_dvd_mul_right (by simpa using h6)
  exact Nat.le_of_dvd (by norm_num) h2

theorem card_map_pCore_le_two {G : Type*} [Group G] [Finite G] {T : Subgroup G}
    (hT : IsPGroup 2 T) (hidx : (Subgroup.normalizer (T : Set G)).index ∣ 3) :
    Nat.card (T.map (QuotientGroup.mk' (CFSG.pCore 2 G))) ≤ 2 := by
  rw [card_map_mk'_eq_relIndex]
  exact relIndex_pCore_le_two hT hidx

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Small
