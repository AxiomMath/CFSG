module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAltSmall
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81LnTwoCentralizerLift
import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerCriterion

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe

open CFSG.Open CFSG.AGLEmbedding Subgroup CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree
open scoped commutatorElement

theorem three_dvd_card_map_of_isPGroup_ker {G H : Type*} [Group G] [Finite G] [Group H]
    (f : G →* H) (hker : IsPGroup 2 f.ker) {D : Subgroup G} (h3 : 3 ∣ Nat.card D) :
    3 ∣ Nat.card (D.map f) := by
  have hker' : IsPGroup 2 (f.domRestrict D).ker := by
    have h : (f.domRestrict D).ker = f.ker.comap D.subtype := by
      ext x
      simp [MonoidHom.mem_ker]
    rw [h]
    exact hker.comap_of_injective D.subtype D.subtype_injective
  obtain ⟨m, hm⟩ := hker'.exists_card_eq
  have h := Subgroup.card_ker_mul_card_range (f.domRestrict D)
  rw [hm, MonoidHom.domRestrict_range] at h
  rw [← h] at h3
  exact (Nat.Coprime.pow_right m (by norm_num : Nat.Coprime 3 2)).dvd_of_dvd_mul_left h3

theorem mk_mem_wSup_of_perfect {A : Type} [Group A] [Finite A] {P J : Subgroup A}
    (hodd : ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index) (hJP : J ≤ P) (hJ : ⁅J, J⁆ = J) {j : A}
    (hj : j ∈ J) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥P) ⟨j, hJP hj⟩ ∈ wSup (↥P ⧸ CFSG.pCore 2 ↥P) := by
  haveI hWn : (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).Normal := ⟨fun n hn c => by
    rw [← map_wSup_eq (MulAut.conj c)]
    exact ⟨n, hn, rfl⟩⟩
  have hcard : Odd (Nat.card ((↥P ⧸ CFSG.pCore 2 ↥P) ⧸ wSup (↥P ⧸ CFSG.pCore 2 ↥P))) := by
    rw [← Subgroup.index_eq_card, ← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact hodd
  haveI : Group.IsSolvable ((↥P ⧸ CFSG.pCore 2 ↥P) ⧸ wSup (↥P ⧸ CFSG.pCore 2 ↥P)) :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ hcard
  have h := CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.map_eq_one_of_perfect hJP hJ
    ((QuotientGroup.mk' (wSup (↥P ⧸ CFSG.pCore 2 ↥P))).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥P))) j hj
  exact (QuotientGroup.eq_one_iff _).1 h

theorem exists_perfect_le_centralizer_of_perfect {A : Type} [Group A] [Finite A] {P J : Subgroup A}
    {β : A} (hβ3 : orderOf β = 3) (hβP : β ∈ normalizer (P : Set A))
    (hW : ParabComm.WCent P β) (hodd : ¬ 2 ∣ (wSup (↥P ⧸ CFSG.pCore 2 ↥P)).index)
    (hJP : J ≤ P) (hJ : ⁅J, J⁆ = J) (hJ3 : 3 ∣ Nat.card J) :
    ∃ D : Subgroup A, D ≤ P ∧ D ≤ centralizer ({β} : Set A) ∧ ⁅D, D⁆ = D ∧ 3 ∣ Nat.card D := by
  classical
  set q : ↥P →* ↥P ⧸ CFSG.pCore 2 ↥P := QuotientGroup.mk' (CFSG.pCore 2 ↥P) with hq
  have hβodd : Odd (orderOf β) := by
    rw [hβ3]
    decide
  set J' : Subgroup ↥P := J.subgroupOf P with hJ'
  have hJ'perf : ⁅J', J'⁆ = J' := by
    apply Subgroup.map_injective P.subtype_injective
    rw [map_commutator, hJ', subgroupOf_map_subtype, inf_eq_left.2 hJP, hJ]
  set Jh : Subgroup (↥P ⧸ CFSG.pCore 2 ↥P) := J'.map q with hJh
  set C₀ : Subgroup ↥P := (centralizer ({β} : Set A)).subgroupOf P ⊓ Jh.comap q with hC₀
  have hmap : C₀.map q = Jh := by
    refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
    · obtain ⟨c, hc, rfl⟩ := hy
      exact hc.2
    · obtain ⟨x, hx, rfl⟩ := hy
      have hxJ : (x : A) ∈ J := hx
      have hc := hW (x : A) x.2 (mk_mem_wSup_of_perfect hodd hJP hJ hxJ)
      obtain ⟨h, hh, hβh⟩ := exists_centralizing_lift hβP hβodd x.2 hc
      refine ⟨h, ⟨?_, ?_⟩, ?_⟩
      · refine mem_subgroupOf.2 (mem_centralizer_iff.2 fun g hg => ?_)
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hβh
      · change q h ∈ Jh
        rw [hh]
        exact ⟨x, hx, rfl⟩
      · exact hh
  have hC₀perf : ⁅C₀.map q, C₀.map q⁆ = C₀.map q := by
    rw [hmap, hJh, ← map_commutator, hJ'perf]
  obtain ⟨I, hIC, -, hIperf, hImap⟩ := LnTwoLift.exists_perfect_isSubnormal_map_eq q C₀ hC₀perf
  refine ⟨I.map P.subtype, map_subtype_le I, fun x hx => ?_, ?_, ?_⟩
  · obtain ⟨y, hy, rfl⟩ := hx
    exact mem_subgroupOf.1 (hIC hy).1
  · rw [← map_commutator, hIperf]
  · have hker : IsPGroup 2 q.ker := by
      rw [hq, QuotientGroup.ker_mk']
      exact CFSG.pCore_isPGroup
    have h1 : 3 ∣ Nat.card J' := by
      rwa [hJ', Nat.card_congr (subgroupOfEquivOfLe hJP).toEquiv]
    have h2 : 3 ∣ Nat.card Jh := three_dvd_card_map_of_isPGroup_ker q hker h1
    have h3 : Nat.card Jh ∣ Nat.card I := by
      rw [← hmap, ← hImap]
      exact Subgroup.card_map_dvd I q
    rw [Subgroup.card_map_of_injective P.subtype_injective]
    exact h2.trans h3

end CFSG.LocalAnalysis.RankThreeTheoremC.TwelveLe
