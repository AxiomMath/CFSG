module

public import CFSG.CGT.PushingUpLit.T2KR.Count1
public import CFSG.CGT.PushingUpLit.T2KR.Wc
public import CFSG.CGT.PushingUpLit.T2KR.CfgFacts

public section

namespace CFSG.CGT.PushingUpLit.T2KR

open CFSG CFSG.RankThree.PartOne CFSG.Open CFSG.CGT.PushingUpLit.BHS
  CFSG.CGT.PushingUpLit.T2K CFSG.CGT.Timmesfeld75
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L M T : Subgroup G} {n : ℕ} {D : Subgroup G} {g : G}

noncomputable def MData.ofSec6 (hE1 : FooteNonsolvableSimple) (hs : Sec6 G L M T n) :
    MData G L M n where
  D := hs.sec4.hyp.natBlock.natData
  nat := hs.sec4.hyp.natBlock
  le := hs.sec4.hyp.le
  normal := hs.sec4.hyp.normal hE1
  C_G := hs.C_G
  Q_comm := fun _ ha _ hb => elemAbelian_mul_comm hs.Q_abelian ha hb
  Q_sq := fun _ ha => elemAbelian_mul_self hs.Q_abelian ha

abbrev Aof (L M : Subgroup G) (g : G) : Subgroup G := conjSubgroup g (QOf L M)

omit [Finite G] in
theorem normIn_star {X Y : Subgroup G} (hDX : D ≤ X) (hDY : D ≤ Y) (hYH : Y ≤ Hc D) :
    normIn (star D X) (star D Y) = star D (normIn X Y) := by
  have hDN : D ≤ normIn X Y := le_inf hDX (hDY.trans Subgroup.le_normalizer)
  ext a
  obtain ⟨x, rfl⟩ := pi_surjective D a
  rw [mem_normIn, mem_star_iff hDX, mem_normalizer_star_iff hDY hYH, mem_star_iff hDN, mem_normIn]

section Setting

variable (hs : Sit64 G L M T n D g)

include hs in
theorem D_le_Q' : D ≤ QOf L M := hs.D_lt_Q.le

include hs in
theorem Q_le_Hc : QOf L M ≤ Hc D := fun _ hq => Subgroup.mem_centralizer_iff.2 fun _ hd =>
  elemAbelian_mul_comm hs.sec6.Q_abelian (hs.D_lt_Q.le hd) hq

include hs in
theorem D_le_A : D ≤ Aof L M g := D_le_conjSubgroup hs.D_lt_Q.le ⟨g, hs.g_mem⟩

include hs in
theorem A_isElemAbelian : IsElemAbelian 2 (Aof L M g) := isElemAbelian_map_conj hs.sec6.Q_abelian g

include hs in
theorem A_le_Hc : Aof L M g ≤ Hc D := fun _ ha => Subgroup.mem_centralizer_iff.2 fun _ hd =>
  elemAbelian_mul_comm (A_isElemAbelian hs) (D_le_A hs hd) ha

include hs in
theorem star_A_eq : star D (Aof L M g) =
    conjSubgroup (pi D ⟨g, hs.g_mem⟩) (star D (QOf L M)) :=
  (star_conj hs.D_lt_Q.le ⟨g, hs.g_mem⟩).symm

include hs in
theorem Q_ne_A : QOf L M ≠ Aof L M g := by
  intro h
  have h1 := hs.ti g hs.g_mem hs.g_not_M
  have h2 : QOf L M ⊓ (QOf L M).map (MulAut.conj g).toMonoidHom = QOf L M := by
    have : (QOf L M).map (MulAut.conj g).toMonoidHom = QOf L M := h.symm
    rw [this, inf_idem]
  rw [h1] at h2
  exact hs.D_lt_Q.ne h2

include hs in
theorem normIn_A_Q : normIn (Aof L M g) (QOf L M) = Aof L M g ⊓ M := by
  rw [normIn, hs.sec6.N_Q]

include hs in
theorem B_not_le_D : ¬ normIn (Aof L M g) (QOf L M) ≤ D := by
  intro h
  rw [normIn_A_Q hs] at h
  exact lt_irrefl _ (hs.D_lt.trans_le h)

include hs in
theorem star_cfg : Cfg (star D (QOf L M)) (star D (Aof L M g)) := by
  have hDQ := D_le_Q' hs
  have hDA := D_le_A hs
  have hWC : IsWC (star D (QOf L M)) := isWC_star hs
  have hWA : IsWC (star D (Aof L M g)) := by
    rw [star_A_eq hs]
    exact hWC.conj _
  set ĝ : Ghat D := pi D ⟨g, hs.g_mem⟩ with hĝ
  have hconj : conjSubgroup ĝ⁻¹ (star D (Aof L M g)) = star D (QOf L M) := by
    rw [star_A_eq hs, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
  have hne : conjSubgroup ĝ⁻¹ (star D (Aof L M g)) ≠ star D (Aof L M g) := by
    rw [hconj]
    intro h
    apply Q_ne_A hs
    apply le_antisymm
    · exact (star_le_iff hDQ hDA (Q_le_Hc hs)).1 h.le
    · exact (star_le_iff hDA hDQ (A_le_Hc hs)).1 h.ge
  have hL : normIn (star D (Aof L M g)) (conjSubgroup ĝ⁻¹ (star D (Aof L M g))) ≠ ⊥ := by
    rw [hconj, normIn_star hDA hDQ (Q_le_Hc hs)]
    intro hbot
    have hDB : D ≤ normIn (Aof L M g) (QOf L M) := le_inf hDA (hDQ.trans Subgroup.le_normalizer)
    have hBH : normIn (Aof L M g) (QOf L M) ≤ Hc D := inf_le_left.trans (A_le_Hc hs)
    exact B_not_le_D hs (le_of_star_eq_bot hDB hBH hbot)
  have c := Cfg.of_conj hWA hne hL
  rw [hconj] at c
  exact c.symm

theorem pairFacts_of_sit64 (hE1 : FooteNonsolvableSimple) (hs : Sit64 G L M T n D g)
    (hTorus : 2 < (normIn (QOf L M) (Aof L M g)).relIndex (QOf L M) →
      ∃ h ∈ M, ∀ x ∈ normIn (Aof L M g) (QOf L M),
        ∃ x' ∈ normIn (Aof L M g) (QOf L M), ∃ d ∈ D, x = ⁅x', h⁆ * d) :
    PairFacts (MData.ofSec6 hE1 hs.sec6) (normIn (QOf L M) (Aof L M g))
      (normIn (Aof L M g) (QOf L M)) D := by
  classical
  have hDQ := D_le_Q' hs
  have hDA := D_le_A hs
  have hQH := Q_le_Hc hs
  have hAH := A_le_Hc hs
  have c := star_cfg hs
  have hDP : D ≤ normIn (QOf L M) (Aof L M g) :=
    le_inf hDQ (hDA.trans Subgroup.le_normalizer)
  have hDB : D ≤ normIn (Aof L M g) (QOf L M) :=
    le_inf hDA (hDQ.trans Subgroup.le_normalizer)
  have hPH : normIn (QOf L M) (Aof L M g) ≤ Hc D := inf_le_left.trans hQH
  have hBH : normIn (Aof L M g) (QOf L M) ≤ Hc D := inf_le_left.trans hAH
  have hNiP : normIn (star D (QOf L M)) (star D (Aof L M g)) =
      star D (normIn (QOf L M) (Aof L M g)) := normIn_star hDQ hDA hAH
  have hNiB : normIn (star D (Aof L M g)) (star D (QOf L M)) =
      star D (normIn (Aof L M g) (QOf L M)) := normIn_star hDA hDQ hQH
  have hconj : ∃ x : Ghat D, star D (Aof L M g) = conjSubgroup x (star D (QOf L M)) :=
    ⟨_, star_A_eq hs⟩
  have hPneQ : normIn (QOf L M) (Aof L M g) ≠ QOf L M := by
    intro hPQ
    have hQN : QOf L M ≤ Subgroup.normalizer ((Aof L M g : Subgroup G) : Set G) := by
      intro q hq
      have : q ∈ normIn (QOf L M) (Aof L M g) := by rw [hPQ]; exact hq
      exact this.2
    have hA2 : IsPGroup 2 (Aof L M g) := isPGroup_two_of_isElemAbelian (A_isElemAbelian hs)
    have hQ2 : IsPGroup 2 (QOf L M) := isPGroup_two_of_isElemAbelian hs.sec6.Q_abelian
    have hS : IsPGroup 2 ↥(Aof L M g ⊔ QOf L M) := hA2.to_sup_of_normal_left' hQ2 hQN
    have hAM : Aof L M g ≤ M := le_sup_left.trans (hs.two_le_M _ hS le_sup_right)
    exact hs.g_not_M (mem_of_conjSubgroup_le hs.sec6 hAM)
  refine
    { D_le_P := hDP
      P_le_Q := inf_le_left
      D_le_B := hDB
      B_le_M := ?_
      B_sq := fun x hx => elemAbelian_mul_self (A_isElemAbelian hs) hx.1
      B_comm := fun x hx y hy => elemAbelian_mul_comm (A_isElemAbelian hs) hx.1 hy.1
      B_inf_Q := ?_
      D_ne_B := fun h => B_not_le_D hs h.symm.le
      P_ne_Q := hPneQ
      card_PB := ?_
      P_le_comm := ?_
      comm_mem := ?_
      P_comm := ?_
      inj := ?_
      torus := hTorus }
  · rw [normIn_A_Q hs]
    exact inf_le_right
  · refine le_antisymm ?_ (le_inf hDB hDQ)
    rintro x ⟨hxB, hxQ⟩
    have : x ∈ QOf L M ⊓ (QOf L M).map (MulAut.conj g).toMonoidHom := ⟨hxQ, hxB.1⟩
    rw [hs.ti g hs.g_mem hs.g_not_M] at this
    exact this
  ·
    have h1 := c.card_normIn_eq hconj
    rw [hNiP, hNiB, card_star hPH, card_star hBH] at h1
    have h2 := PairFacts.relIndex_mul_card_of_le hDP
    have h3 := PairFacts.relIndex_mul_card_of_le hDB
    rw [h1] at h2
    rw [← h2, ← h3]
  ·
    intro p hp
    obtain ⟨t, htQ, htP⟩ := IsConcreteLE.not_le_iff_exists.1
      (fun h : QOf L M ≤ normIn (QOf L M) (Aof L M g) => hPneQ (le_antisymm inf_le_left h))
    have ht' : pi D ⟨t, hQH htQ⟩ ∈ star D (QOf L M) := (mem_star_iff hDQ _).2 htQ
    have htL : pi D ⟨t, hQH htQ⟩ ∉ normIn (star D (QOf L M)) (star D (Aof L M g)) := by
      rw [hNiP]
      intro h
      exact htP ((mem_star_iff hDP _).1 h)
    have hpL : pi D ⟨p, hPH hp⟩ ∈ normIn (star D (QOf L M)) (star D (Aof L M g)) := by
      rw [hNiP]
      exact (mem_star_iff hDP _).2 hp
    obtain ⟨y, hy, hyc⟩ := cfg_exists_comm_eq c hconj ht' htL hpL
    obtain ⟨b, rfl⟩ := pi_surjective D y
    rw [hNiB] at hy
    have hbB : (b : G) ∈ normIn (Aof L M g) (QOf L M) := (mem_star_iff hDB b).1 hy
    have h1 : pi D ⟨p, hPH hp⟩ = pi D ⁅(⟨t, hQH htQ⟩ : ↥(Hc D)), b⁆ := by
      rw [map_commutatorElement]
      exact hyc.symm
    have hd := (pi_eq_pi_iff D).1 h1
    have hcomm : ⁅t, (b : G)⁆ ∈ ⁅QOf L M, normIn (Aof L M g) (QOf L M)⁆ :=
      Subgroup.commutator_mem_commutator htQ hbB
    have hpe : p = ⁅t, (b : G)⁆ * (p⁻¹ * ⁅t, (b : G)⁆)⁻¹ := by group
    rw [hpe]
    exact Subgroup.mul_mem_sup hcomm (D.inv_mem hd)
  ·
    intro u hu x hx
    have hu' : pi D ⟨u, hQH hu⟩ ∈ star D (QOf L M) := (mem_star_iff hDQ _).2 hu
    have hx' : pi D ⟨x, hBH hx⟩ ∈ normIn (star D (Aof L M g)) (star D (QOf L M)) := by
      rw [hNiB]
      exact (mem_star_iff hDB _).2 hx
    have h1 := c.comm_mem_normIn hu' hx'
    rw [hNiP, ← map_commutatorElement] at h1
    exact (mem_star_iff hDP _).1 h1
  ·
    intro t ht x hx
    have ht' : pi D ⟨t, hPH ht⟩ ∈ normIn (star D (QOf L M)) (star D (Aof L M g)) := by
      rw [hNiP]
      exact (mem_star_iff hDP _).2 ht
    have hx' : pi D ⟨x, hBH hx⟩ ∈ normIn (star D (Aof L M g)) (star D (QOf L M)) := by
      rw [hNiB]
      exact (mem_star_iff hDB _).2 hx
    have h1 := c.comm_L_L₁ ht' hx'
    have h2 : pi D ⁅(⟨x, hBH hx⟩ : ↥(Hc D)), ⟨t, hPH ht⟩⁆ = 1 := by
      rw [map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.2 h1.symm
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)
  ·
    intro t htQ htP x hx hxt
    have ht' : pi D ⟨t, hQH htQ⟩ ∈ star D (QOf L M) := (mem_star_iff hDQ _).2 htQ
    have htL : pi D ⟨t, hQH htQ⟩ ∉ normIn (star D (QOf L M)) (star D (Aof L M g)) := by
      rw [hNiP]
      intro h
      exact htP ((mem_star_iff hDP _).1 h)
    have hx' : pi D ⟨x, hBH hx⟩ ∈ normIn (star D (Aof L M g)) (star D (QOf L M)) := by
      rw [hNiB]
      exact (mem_star_iff hDB _).2 hx
    have h1 : ⁅pi D ⟨x, hBH hx⟩, pi D ⟨t, hQH htQ⟩⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hxt)
    have h2 := cfg_eq_one_of_comm c ht' htL hx' h1
    exact Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 h2)

end Setting

end CFSG.CGT.PushingUpLit.T2KR
