module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Coordinator CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.ComponentClassification.CatalogueBPrimeJoin CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem not_isQuasisimple_bot {Q : Type*} [Group Q] :
    ¬ CFSG.Open.IsQuasisimple ↥(⊥ : Subgroup Q) := by
  intro hq
  have hnt := hq.2.toNontrivial
  have hss : Subsingleton (↥(⊥ : Subgroup Q) ⧸ Subgroup.center ↥(⊥ : Subgroup Q)) :=
    (QuotientGroup.mk'_surjective _).subsingleton
  exact (not_nontrivial_iff_subsingleton.2 hss) hnt

theorem not_dvd_card_of_perfect_central_sylow {J : Type*} [Group J] [Finite J] {p : ℕ}
    [Fact p.Prime] (hperf : Group.IsPerfect J) (P : Sylow p J)
    (hP : (P : Subgroup J) ≤ Subgroup.center J) : ¬ p ∣ Nat.card J := by
  intro hdvd
  have hN : Subgroup.normalizer (P : Subgroup J) ≤ Subgroup.centralizer (P : Set J) := by
    intro n _ c hc
    exact (Subgroup.mem_center_iff.1 (hP hc) n).symm
  let φ := MonoidHom.transferSylow P hN
  have hcomm : ∀ x y : ↥P, ⁅x, y⁆ = 1 := by
    intro x y
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hP x.2) y).symm
  have hker : (⊤ : Subgroup J) ≤ φ.ker := by
    rw [← hperf.commutator_eq_top, commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact hcomm _ _
  have hPbot : (P : Subgroup J) = ⊥ := by
    rw [eq_bot_iff]
    intro g hg
    have h1 : φ g = 1 := MonoidHom.mem_ker.1 (hker (Subgroup.mem_top g))
    rw [MonoidHom.transferSylow_eq_pow P hN g hg] at h1
    have h2 : g ^ (P : Subgroup J).index = 1 := congrArg Subtype.val h1
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨g, hg⟩
    have hgk : g ^ p ^ k = 1 := congrArg Subtype.val hk
    have h3 : orderOf g ∣ p ^ k := orderOf_dvd_of_pow_eq_one hgk
    have h4 : orderOf g ∣ (P : Subgroup J).index := orderOf_dvd_of_pow_eq_one h2
    have h5 := Nat.eq_one_of_dvd_coprimes
      ((Nat.Coprime.pow_left k ((Fact.out : p.Prime).coprime_iff_not_dvd.2 P.not_dvd_index))) h3 h4
    rw [orderOf_eq_one_iff.1 h5]
    exact Subgroup.one_mem _
  have := P.dvd_card_of_dvd_card hdvd
  rw [hPbot, Subgroup.card_bot] at this
  exact (Fact.out : p.Prime).one_lt.ne' (Nat.dvd_one.1 this)

theorem no_glaPComponent_of_exact {S : Type} [Group S] [Finite S] {p : ℕ} (hp : p.Prime) {s : S}
    (hs : orderOf s = p) (hcard : ¬ p ^ 2 ∣ Nat.card S) {J : Subgroup S}
    (hJ : GLAPComponent p (Subgroup.centralizer ({s} : Set S)) J) : False := by
  have : Fact p.Prime := ⟨hp⟩
  set C := Subgroup.centralizer ({s} : Set S) with hC
  obtain ⟨hJC, hPc⟩ := (i183_glaPComponent_iff_isPComponent hp).1 hJ
  set L : Subgroup ↥C := J.subgroupOf C with hL
  have hperf : Group.IsPerfect ↥L := isPerfect_of_isPComponent p hPc
  have hres := primeResidual_eq_top_of_pComponent p L hPc
  have hbar : barX p C J ≠ ⊥ := by
    intro h
    have hq : CFSG.Open.IsQuasisimple ↥(barX p C J) := hJ.2.2.1.2.2
    rw [h] at hq
    exact not_isQuasisimple_bot hq
  have hLne : L ≠ ⊥ := fun h => hbar (by rw [barX, ← hL, h, Subgroup.map_bot])
  have hpL : p ∣ Nat.card ↥L := by
    by_contra h
    have hP : ∀ P : Subgroup ↥L, IsPGroup p P → P = ⊥ := by
      intro P hP'
      rcases hP'.card_eq_or_dvd with h1 | h1
      · exact Subgroup.card_eq_one.1 h1
      · exact absurd (h1.trans (Subgroup.card_subgroup_dvd_card P)) h
    have hle : (⊤ : Subgroup ↥L) ≤ ⊥ := by
      rw [← hres]
      exact sSup_le fun P hP' => (hP P hP').le
    have h1 : Nat.card ↥L = 1 := by
      have := Subgroup.card_top (G := ↥L)
      rw [le_bot_iff.1 hle, Subgroup.card_bot] at this
      exact this.symm
    exact hLne (Subgroup.card_eq_one.1 h1)
  obtain ⟨P⟩ : Nonempty (Sylow p ↥L) := inferInstance
  let z : ↥C := ⟨s, Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have hzc : ∀ c : ↥C, c * z = z * c := fun c =>
    Subtype.ext (Subgroup.mem_centralizer_singleton_iff.1 c.2)
  have hzo : orderOf z = p := by
    rw [← orderOf_injective C.subtype C.subtype_injective z]
    exact hs
  have hzcenter : z ∈ Subgroup.center ↥C := Subgroup.mem_center_iff.2 hzc
  have hCdvd : Nat.card ↥C ∣ Nat.card S := Subgroup.card_subgroup_dvd_card C
  have hpC : p ∣ Nat.card ↥C := hzo ▸ orderOf_dvd_natCard z
  have hfac : (Nat.card ↥C).factorization p = 1 := by
    have hne : Nat.card ↥C ≠ 0 := Nat.card_pos.ne'
    have h1 : 1 ≤ (Nat.card ↥C).factorization p :=
      (hp.dvd_iff_one_le_factorization hne).1 hpC
    have h2 : ¬ 2 ≤ (Nat.card ↥C).factorization p := fun h2 =>
      hcard ((hp.pow_dvd_iff_le_factorization hne).2 h2 |>.trans hCdvd)
    omega
  let R : Sylow p ↥C := Sylow.ofCard (Subgroup.zpowers z)
    (by rw [Nat.card_zpowers, hzo, hfac, pow_one])
  have hRc : (R : Subgroup ↥C) ≤ Subgroup.center ↥C := Subgroup.zpowers_le.2 hzcenter
  have hRn : (R : Subgroup ↥C).Normal :=
    ⟨fun n hn g => by
      have := Subgroup.mem_center_iff.1 (hRc hn) g
      rw [this, mul_inv_cancel_right]
      exact hn⟩
  have huniq : Unique (Sylow p ↥C) := Sylow.unique_of_normal R hRn
  set K : Subgroup ↥C := (P : Subgroup ↥L).map L.subtype with hK
  have hKp : IsPGroup p K := P.isPGroup'.map _
  obtain ⟨R', hKR'⟩ := hKp.exists_le_sylow
  have hR' : R' = R := Subsingleton.elim _ _
  have hKc : K ≤ Subgroup.center ↥C := hR' ▸ hKR' |>.trans hRc
  have hPc : (P : Subgroup ↥L) ≤ Subgroup.center ↥L := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro l
    have h1 := Subgroup.mem_center_iff.1 (hKc ⟨x, hx, rfl⟩) (l : ↥C)
    exact Subtype.ext h1
  exact not_dvd_card_of_perfect_central_sylow hperf P hPc hpL

theorem b3SporPair_of_card_exact {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo)
    (hcard : ∀ (S : Type) [Group S] [Finite S],
      Nonempty (S ≃* (TauCeti.CFSGIndex.sporadic name).Group) → ¬ p ^ 2 ∣ Nat.card S) :
    B3SporPair name p := by
  intro S _ _ hs hnc he β hβ
  have := hs
  have : Fact p.Prime := ⟨hp⟩
  have hcen : Subgroup.center S = ⊥ := center_eq_bot_of_isSimpleGroup hnc
  have hout : Nat.card (Outer S) ≤ 2 := hOut S hs hnc name he
  obtain ⟨s, rfl, hsp⟩ := exists_conj_of_pow hp hp2 hcen hout β hβ
  by_cases hs1 : s = 1
  · subst hs1
    rw [map_one]
    exact layer_comm_one p
  · have hord : orderOf s = p := orderOf_eq_prime hsp hs1
    rw [fixSubgroup_conj]
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 (sSup_le fun J hJ => ?_)
    exact (no_glaPComponent_of_exact hp hord (hcard S he) hJ).elim

end CFSG.HardMathSupport.Solomon.Coordinator
