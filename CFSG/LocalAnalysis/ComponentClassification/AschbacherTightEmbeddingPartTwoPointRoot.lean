module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Final
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.ElementaryHull

public noncomputable section

namespace CFSG.ComponentClassification.AschbacherTightEmbedding

open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1

variable {G : Type*} [Group G]

theorem involution_core_eq_top_of_involution_normal_generation
    (z : G) (hz : orderOf z = 2)
    (hgen : Subgroup.normalClosure ({z} : Set G) = ⊤) :
    involutionCore G = ⊤ := by
  have hzI : IsInvolution z :=
    ⟨(orderOf_eq_prime_iff.mp hz).2, (orderOf_eq_prime_iff.mp hz).1⟩
  have hle : Subgroup.normalClosure ({z} : Set G) ≤ involutionCore G :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr
      (Subgroup.subset_closure hzI))
  exact top_unique (hgen ▸ hle)

variable [Finite G]

theorem corefree_involution_generated_strong_embedding_borel
    (H : Subgroup G) (hH : CFSG.BenderSuzuki.IsStronglyEmbedded H)
    (hrank : TwoRankAtLeastTwo G) (hgen : involutionCore G = ⊤)
    (hcore : CFSG.oddCore G = ⊥) :
    IsSimpleBenderGroup G ∧ IsBorelSubgroup H := by
  let L := involutionCore G
  let K := twoPrimeCore L
  let eL : L ≃* G := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hLrank : TwoRankAtLeastTwo L :=
    hrank.map_of_injective eL.symm.toMonoidHom eL.symm.injective
  have hSE : TheoremSEBenderConclusion H := by
    rcases theorem_SE H hH with hlow | hmodel
    · exact (hlow hLrank).elim
    · exact hmodel
  have hKbot : K = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective K L.subtype_injective).mp
    have hmap := CFSG.ComponentClassification.OddCore.normal_intersection G L
    change (CFSG.oddCore L).map L.subtype = L ⊓ CFSG.oddCore G at hmap
    rw [hcore, inf_bot_eq] at hmap
    simpa only [K, CFSG.ShultStronglyClosedTI.oddCore_eq_twoPrimeCore] using hmap
  let eK : (L ⧸ K) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hKbot).trans
      (QuotientGroup.quotientBot (G := L))
  let e : (L ⧸ K) ≃* G := eK.trans eL
  have he_mk : ∀ l : L, e (QuotientGroup.mk l) = (l : G) := by
    intro l
    change eL (eK (QuotientGroup.mk l)) = (l : G)
    have heq : (QuotientGroup.quotientMulEquivOfEq hKbot)
        (QuotientGroup.mk l) = QuotientGroup.mk l :=
      QuotientGroup.quotientMulEquivOfEq_mk hKbot l
    rw [show eK (QuotientGroup.mk l) = QuotientGroup.quotientBot
      ((QuotientGroup.quotientMulEquivOfEq hKbot) (QuotientGroup.mk l)) from rfl, heq]
    change eL ((QuotientGroup.kerLift (MonoidHom.id L)) (QuotientGroup.mk l)) = (l : G)
    rw [QuotientGroup.kerLift_mk]
    rfl
  have hBmap :
      ((((H ⊓ L).subgroupOf L).map (QuotientGroup.mk' K)).map e.toMonoidHom) = H := by
    ext x
    constructor
    · rintro ⟨y, ⟨l, hl, hly⟩, hxy⟩
      have hx : x = (l : G) := hxy.symm.trans ((congrArg e hly.symm).trans (he_mk l))
      exact hx ▸ hl.1
    · intro hx
      let l : L := ⟨x, by change x ∈ involutionCore G; rw [hgen]; trivial⟩
      exact ⟨QuotientGroup.mk l, ⟨l, ⟨hx, l.property⟩, rfl⟩, he_mk l⟩
  change IsSimpleBenderGroup (L ⧸ K) ∧ _ at hSE
  refine ⟨hSE.1.map_mulEquiv e, ?_⟩
  have hB := hSE.2.2.map_mulEquiv e
  rwa [hBmap] at hB

theorem borel_exists_normal_sylow_two_root (H : Subgroup G)
    (hB : IsBorelSubgroup H) :
    Group.IsSolvable H ∧ ∃ P : Sylow 2 H,
      (P : Subgroup H).Normal ∧
        Subgroup.normalizer ((P : Subgroup H).map H.subtype : Set G) = H := by
  obtain ⟨hsolv, S, hH⟩ := hB
  have hSH : (S : Subgroup G) ≤ H := by rw [hH]; exact Subgroup.le_normalizer
  let P := S.subtype hSH
  have hmap : (P : Subgroup H).map H.subtype = (S : Subgroup G) := by
    rw [Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSH]
  refine ⟨hsolv, P, ?_, ?_⟩
  · rw [Sylow.coe_subtype]
    exact Subgroup.normal_subgroupOf_of_le_normalizer hH.le
  · rw [hmap]
    exact hH.symm

theorem normal_sylow_two_exists_odd_hall_complement
    (P : Sylow 2 G) (hP : (P : Subgroup G).Normal) :
    ∃ D : Subgroup G, (P : Subgroup G).IsComplement' D ∧
      Odd (Nat.card D) ∧ CFSG.IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} D := by
  let : (P : Subgroup G).Normal := hP
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D, hcompl⟩ := Subgroup.exists_right_complement'_of_coprime P.card_coprime_index
  have hodd : Odd (Nat.card D) := by
    rw [← hcompl.symm.index_eq_card]
    exact Nat.not_even_iff_odd.mp (fun hEven => P.not_dvd_index hEven.two_dvd)
  have hHall : CFSG.IsHallSubgroup {p : Nat.Primes | p.val ≠ 2} D := by
    refine ⟨?_, ?_⟩
    · intro p hp
      change p.val ≠ 2
      intro heq
      exact hodd.not_two_dvd_nat (heq ▸ hp)
    · intro p hp
      change ¬ p.val ≠ 2
      rw [hcompl.index_eq_card] at hp
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2) (G := (P : Subgroup G))).mp P.isPGroup'
      rw [hn] at hp
      exact not_not.mpr ((Nat.dvd_prime_two_le Nat.prime_two p.property.two_le).mp
        (p.property.dvd_of_dvd_pow hp))
  exact ⟨D, hcompl, hodd, hHall⟩

end CFSG.ComponentClassification.AschbacherTightEmbedding
