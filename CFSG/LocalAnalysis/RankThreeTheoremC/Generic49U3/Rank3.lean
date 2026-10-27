module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Config
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.Struct
import CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3.CenterCard
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_10Absorb
import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x : G}
  {J : Subgroup G}

theorem u3_rank3_plane_cube {p : ℕ} [Fact p.Prime] {J E₂ : Subgroup G} {x c : G}
    (hxp : x ^ p = 1) (hcp : c ^ p = 1) (hc1 : c ≠ 1) (hcJ : c ∈ J) (hE₂J : E₂ ≤ J)
    (hxJ : x ∉ J) (hJC : J ≤ Subgroup.centralizer ({x} : Set G))
    (hE₂e : IsElemAbelian p E₂) (hE₂c : Nat.card E₂ = p ^ 2) (hcE : ∀ e ∈ E₂, e * c = c * e) :
    IsElemAbelian p (Subgroup.zpowers c ⊔ Subgroup.zpowers x) ∧
      Nat.card (Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 2 ∧
      IsElemAbelian p (E₂ ⊔ Subgroup.zpowers x) ∧
      Nat.card (E₂ ⊔ Subgroup.zpowers x : Subgroup G) = p ^ 3 ∧
      E₂ ⊔ Subgroup.zpowers x ≤
        Subgroup.centralizer ((Subgroup.zpowers c ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
  have hp : p.Prime := Fact.out
  have hxJc : ∀ y ∈ J, y * x = x * y := fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hJC hy)
  have hcz : Subgroup.zpowers c ≤ J := Subgroup.zpowers_le.mpr hcJ
  have hxE₂ : x ∉ E₂ := fun h => hxJ (hE₂J h)
  have hxc : x ∉ Subgroup.zpowers c := fun h => hxJ (hcz h)
  have hEc' : E₂ ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({c} : Set G) :=
    sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (hcE e he))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (hxJc c hcJ).symm))
  have hEx' : E₂ ⊔ Subgroup.zpowers x ≤ Subgroup.centralizer ({x} : Set G) :=
    sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (hxJc e (hE₂J he)))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hcp)
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hxp) ?_
    rintro a ⟨m, rfl⟩ b ⟨n, rfl⟩
    exact (Commute.zpow_zpow (hxJc c hcJ : Commute c x) m n).eq
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp (Subgroup.zpowers c) hxp hxc
      (fun e he => hxJc e (hcz he)), Nat.card_zpowers, orderOf_eq_prime hcp hc1, sq]
  · refine CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hE₂e
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers hxp) ?_
    rintro a ha b ⟨n, rfl⟩
    exact (Commute.zpow_right (hxJc a (hE₂J ha) : Commute a x) n).eq
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hp E₂ hxp hxE₂
      (fun e he => hxJc e (hE₂J he)), hE₂c]
    ring
  · rw [Subgroup.le_centralizer_iff]
    refine sup_le (Subgroup.zpowers_le.mpr ?_) (Subgroup.zpowers_le.mpr ?_)
    · exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
        Subgroup.mem_centralizer_singleton_iff.mp (hEc' hh)
    · exact Subgroup.mem_centralizer_iff.mpr fun h hh =>
        Subgroup.mem_centralizer_singleton_iff.mp (hEx' hh)

theorem u3_rank3_absorb (hS : Setting G) (hD1 : TheoremD1 G) (hU0 : FullCoreLocal G)
    (hc : U3Config G p P M x J) :
    ∀ H : Subgroup G, IsTwoLocal H → u3U0 P x J ≤ H → 3 ≤ CFSG.Open.pRank p H → H ≤ M := by
  intro H hH hUH hH3
  have hpp : p.Prime := hc.prime
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨hTcard, hTexp, hTnc, hxJ⟩ := u3_T_structure hc
  obtain ⟨hxP, hLO, -, -⟩ := hc.generic
  obtain ⟨-, -, hxp, -, -⟩ := hLO
  have hPM : (P : Subgroup G) ≤ M := (sylow_le_of_isCoreMaxLocal hS hc.sigma hc.core).1
  have hxM : x ∈ M := hPM hxP
  have hSsplit : ∀ a ∈ u3S P x, a ∈ (P : Subgroup G) ∧
      a ∈ Subgroup.centralizer ({x} : Set G) :=
    fun a ha => Subgroup.mem_inf.mp ha
  have hTsplit : ∀ a ∈ u3T P x J, a ∈ u3S P x ∧ a ∈ J := fun a ha => Subgroup.mem_inf.mp ha
  have hZsplit : ∀ a ∈ u3ZT P x J, a ∈ u3T P x J ∧
      a ∈ Subgroup.centralizer ((u3T P x J : Subgroup G) : Set G) :=
    fun a ha => Subgroup.mem_inf.mp ha
  have hTJ : u3T P x J ≤ J := fun a ha => (hTsplit a ha).2
  have hTS : u3T P x J ≤ u3S P x := fun a ha => (hTsplit a ha).1
  have hSP : u3S P x ≤ (P : Subgroup G) := fun a ha => (hSsplit a ha).1
  have hZT : u3ZT P x J ≤ u3T P x J := fun a ha => (hZsplit a ha).1
  have hZcard : Nat.card (u3ZT P x J : Subgroup G) = p :=
    card_inf_centralizer_of_nonabelian_card_p_cube hTcard hTnc
  haveI : Nontrivial (u3ZT P x J : Subgroup G) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hZcard]; exact hpp.one_lt)
  obtain ⟨c, hcZ, hc1⟩ : ∃ c : G, c ∈ u3ZT P x J ∧ c ≠ 1 := by
    obtain ⟨c', hc'1⟩ := exists_ne (1 : ↥(u3ZT P x J))
    exact ⟨c'.1, c'.2, fun h => hc'1 (Subtype.ext h)⟩
  have hcT : c ∈ u3T P x J := (hZsplit c hcZ).1
  have hcJ : c ∈ J := (hTsplit c hcT).2
  have hcp : c ^ p = 1 := hTexp c hcT
  have hZc : ∀ a ∈ u3ZT P x J, ∀ b ∈ u3T P x J, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hZsplit a ha).2 b hb).symm
  obtain ⟨t, htT, htZ⟩ : ∃ t ∈ u3T P x J, t ∉ u3ZT P x J := by
    by_contra hcon
    push_neg at hcon
    apply hTnc
    refine ⟨⟨fun a b => ?_⟩⟩
    exact Subtype.ext (hZc a.1 (hcon a.1 a.2) b.1 b.2)
  have hZe : IsElemAbelian p (u3ZT P x J : Subgroup G) :=
    CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff.mpr
      ⟨fun a ha b hb => hZc a ha b (hZT hb), fun y hy => hTexp y (hZT hy)⟩
  have hE₂e : IsElemAbelian p (u3ZT P x J ⊔ Subgroup.zpowers t : Subgroup G) := by
    refine CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.sup hZe
      (CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_zpowers (hTexp t htT)) ?_
    rintro a ha b ⟨n, rfl⟩
    exact (Commute.zpow_right (hZc a ha t htT : Commute a t) n).eq
  have hE₂c : Nat.card (u3ZT P x J ⊔ Subgroup.zpowers t : Subgroup G) = p ^ 2 := by
    rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers hpp (u3ZT P x J) (hTexp t htT) htZ
      (fun e he => hZc e he t htT), hZcard]
    ring
  have hE₂T : u3ZT P x J ⊔ Subgroup.zpowers t ≤ u3T P x J :=
    sup_le hZT (Subgroup.zpowers_le.mpr htT)
  have hE₂J : u3ZT P x J ⊔ Subgroup.zpowers t ≤ J := hE₂T.trans hTJ
  have hE₂P : u3ZT P x J ⊔ Subgroup.zpowers t ≤ (P : Subgroup G) :=
    (hE₂T.trans hTS).trans hSP
  have hcE : ∀ e ∈ u3ZT P x J ⊔ Subgroup.zpowers t, e * c = c * e := by
    have hEc' : u3ZT P x J ⊔ Subgroup.zpowers t ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le (fun e he => Subgroup.mem_centralizer_singleton_iff.mpr (hZc e he c hcT))
        (Subgroup.zpowers_le.mpr
          (Subgroup.mem_centralizer_singleton_iff.mpr (hZc c hcZ t htT).symm))
    exact fun e he => Subgroup.mem_centralizer_singleton_iff.mp (hEc' he)
  obtain ⟨hRe, hRc, hEe, hEc, hER⟩ :=
    u3_rank3_plane_cube hxp hcp hc1 hcJ hE₂J hxJ hc.le_cent hE₂e hE₂c hcE
  have hRU : Subgroup.zpowers c ⊔ Subgroup.zpowers x ≤ u3U0 P x J :=
    sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_left hcZ))
      (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right (Subgroup.mem_zpowers x)))
  have hRH : Subgroup.zpowers c ⊔ Subgroup.zpowers x ≤ H := hRU.trans hUH
  have hEM : u3ZT P x J ⊔ Subgroup.zpowers t ⊔ Subgroup.zpowers x ≤ M :=
    sup_le (hE₂P.trans hPM) (Subgroup.zpowers_le.mpr hxM)
  exact le_of_isTwoLocal_of_three_le_pRank hS hD1 hU0 hc.sigma hc.core hRe hRc hEe hEc hEM hER
    hH hRH hH3

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic49U3
