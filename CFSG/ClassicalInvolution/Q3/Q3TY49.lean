module

public import CFSG.ClassicalInvolution.Q3.Q3TY48
public import CFSG.ClassicalInvolution.Q3.Q3TY47
public import CFSG.ClassicalInvolution.Q3.Q3TY46
public import CFSG.ClassicalInvolution.Q3.Q3TY45
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSixMain

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.LieType.RootSystem CFSG.Timmesfeld
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.ModelFacts.E8D8
open scoped MatrixGroups commutatorElement

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem minus_fixed_of_nodes_six3 (c : Q3TC.TCtx3 .POmegaMinus 6 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes3 (6 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β) :
    ∃ x : SpinM3 6,
      locImg Ω z (nd.J ⟨2, by omega⟩) =
        ((rankOne (minusDatum 6 (minusCoeffs_irr 3 1)).rootGroup
          (⟨0, by omega⟩ : Fin (6 - 1))).map (MulAut.conj x).toMonoidHom).map c.d.ψ ∧
      ∀ k : Fin (6 - 1), 1 ≤ k.val →
        ∀ r ∈ (rankOne (minusDatum 6 (minusCoeffs_irr 3 1)).rootGroup k).map
          (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r := by
  classical
  have hMFZ : Gaps.FundNoncentral 3 := Gaps.fundNoncentral 3
  have hirr := minusCoeffs_irr 3 1
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  have hKβ' := hKβ
  obtain ⟨W, hW⟩ := hKβ'
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaMinus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have : Finite (modelUniv .POmegaMinus 6 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have cq := ctx_centralQuot3 (by norm_num : 4 ≤ 6)
  have hKJ : ∀ a (h : a < 6 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 6 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 6 - 1), 2 ≤ a →
      ∃ b, ∃ hb : b < 6 - 1, 2 ≤ b ∧ DNodes3.Adj (⟨a, h⟩ : Fin (6 - 1)) ⟨b, hb⟩ := by
    intro a h ha
    have : a < 5 := h
    interval_cases a
    · exact ⟨3, by omega, by omega, by fr_idx⟩
    · exact ⟨2, by omega, by omega, by fr_idx⟩
    · exact ⟨2, by omega, by omega, by fr_idx⟩
  have hlayer : ∀ a (h : a < 6 - 1), 2 ≤ a → IsLayerMember3 c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember3.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (SpinM3 6),
      ∀ (h : a < 6 - 1), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr 3 1)) ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 6 - 1 ∧ 2 ≤ a
    · obtain ⟨R, hR, hLR⟩ := (hlayer a hv.1 hv.2).exists_fund
      exact ⟨R, fun _ _ => ⟨hR, hLR⟩⟩
    · exact ⟨⊥, fun h ha => absurd ⟨h, ha⟩ hv⟩
  choose Rz hRz using hexRz
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  obtain ⟨N, hNz, hNM, hNc⟩ := hMN
  have hMlayer : IsLayerMember3 c M :=
    IsLayerMember3.of_not_commutes c hMz hNz (fun h => hNM h.symm) hNc
  obtain ⟨RzM, hRzM, hMR⟩ := hMlayer.exists_fund
  have hcommz : ∀ a (ha : a < 6 - 1) b (hb : b < 6 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 6 - 1) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 6 - 1) b (hb : b < 6 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin (6 - 1)) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (SpinM3 6)) (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    c.modelAdj_of_adj3 (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w _ _) (nd.conjSub_w hab)
  have hlinz : ∀ a (ha : a < 6 - 1) b (hb : b < 6 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin (6 - 1)) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact c.lift_lin (hRz a ha ha2).1 (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 6 - 1), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 6 - 1), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hMβ : Commutes M β := by
    rw [← h1]
    exact nd.commK _
  have hMβ' : Commutes β M := commutes_symm hMβ
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map
      (locAut hΩ.conjInvariant htz).toMonoidHom = locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by fr_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadMinus 6 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    c.locAut_mem_range htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (p := 3) (f := 1) (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (SpinM3 6) := fun a => Rz (a + 2)
  let Rtw : Subgroup (SpinM3 6) := Rz 4
  let RM : Subgroup (SpinM3 6) := RzM
  have hR2 := (hRz 2 (by omega) (by omega)).1
  have hR3 := (hRz 3 (by omega) (by omega)).1
  have hR4 := (hRz 4 (by omega) (by omega)).1
  have hRf : ∀ a ≤ 1, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum 6 (minusCoeffs_irr 3 1)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr 3 1)) :=
    hR4
  have hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr 3 1)) :=
    hRzM
  have hadj : ∀ a < 1, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hlin : ∀ a < 1, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ 1 → Commutes (R a) (R b) := fun a b hab hb => by omega
  have hM : ∀ a ≤ 1, Commutes RM (R a) := fun a ha =>
    hMcomm (a + 2) (by omega) (by omega)
  have hne : Rtw ≠ R 1 := by
    intro h
    have h' : Rz 4 = Rz (1 + 2) := h
    have h2' : nd.J ⟨4, by omega⟩ = nd.J ⟨1 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 4 (by omega) (by omega)).2, (hRz (1 + 2) (by omega) (by omega)).2, h'])
    exact nd.ne_J (Gaps.fin_ne_of_val_ne (by simp)) h2'
  obtain ⟨i₂, hi₂⟩ := cq.map_mem (Rz 2) hR2
  obtain ⟨i₃, hi₃⟩ := cq.map_mem (Rz 3) hR3
  obtain ⟨i₄, hi₄⟩ := cq.map_mem (Rz 4) hR4
  obtain ⟨iM, hiM⟩ := cq.map_mem RzM hRzM
  have hadj23 := hadjz 2 (by omega) 3 (by omega) (by omega) (by omega) (by fr_idx)
  have hadj24 := hadjz 2 (by omega) 4 (by omega) (by omega) (by omega) (by fr_idx)
  have hne23 : (Rz 2).map (spinAction (QM3 6)) ≠ (Rz 3).map (spinAction (QM3 6)) :=
    fun e => hadj23.1 (cq.map_inj hR2 hR3 e)
  have hne24 : (Rz 2).map (spinAction (QM3 6)) ≠ (Rz 4).map (spinAction (QM3 6)) :=
    fun e => hadj24.1 (cq.map_inj hR2 hR4 e)
  have hnc23 : ¬ Commutes ((Rz 2).map (spinAction (QM3 6)))
      ((Rz 3).map (spinAction (QM3 6))) := fun h => hadj23.2.1 ((cq.commutes_iff hR2).mp h)
  have hnc24 : ¬ Commutes ((Rz 2).map (spinAction (QM3 6)))
      ((Rz 4).map (spinAction (QM3 6))) := fun h => hadj24.2.1 ((cq.commutes_iff hR2).mp h)
  have hc34 : Commutes ((Rz 3).map (spinAction (QM3 6)))
      ((Rz 4).map (spinAction (QM3 6))) :=
    commutes_map_of_commutes _ (hcommz 3 (by omega) 4 (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp)) (by fr_idx)))
  have hM2 : Commutes (RzM.map (spinAction (QM3 6))) ((Rz 2).map (spinAction (QM3 6))) :=
    commutes_map_of_commutes _ (hMcomm 2 (by omega) (by omega))
  have hM3 : Commutes (RzM.map (spinAction (QM3 6))) ((Rz 3).map (spinAction (QM3 6))) :=
    commutes_map_of_commutes _ (hMcomm 3 (by omega) (by omega))
  have hM4 : Commutes (RzM.map (spinAction (QM3 6))) ((Rz 4).map (spinAction (QM3 6))) :=
    commutes_map_of_commutes _ (hMcomm 4 (by omega) (by omega))
  have hMne3 : RzM.map (spinAction (QM3 6)) ≠ (Rz 3).map (spinAction (QM3 6)) := by
    intro e
    rw [e] at hM3
    exact not_commutes_self_of_isFundamental hi₃ hM3
  have hMne4 : RzM.map (spinAction (QM3 6)) ≠ (Rz 4).map (spinAction (QM3 6)) := by
    intro e
    rw [e] at hM4
    exact not_commutes_self_of_isFundamental hi₄ hM4
  have htw : i₄ = i₃ := TwinSmall.twin_of_leaves_six hirr hodd hi₂ hi₃ hi₄ hiM hne23 hne24 hnc23
    hnc24 hc34 hM2 hM3 hM4 hMne3 hMne4
  have hdist : ∀ a b, a + 1 < b → b ≤ 1 → ∀ i j,
      IsFundamental (QM3 6) ((R a).map (spinAction (QM3 6))) i →
      IsFundamental (QM3 6) ((R b).map (spinAction (QM3 6))) j → i ≠ j :=
    fun a b hab hb => by omega
  have htwin : ∀ i j, IsFundamental (QM3 6) ((R 1).map (spinAction (QM3 6))) i →
      IsFundamental (QM3 6) (Rtw.map (spinAction (QM3 6))) j → i = j := by
    intro i j hi hj
    have e1 : i = i₃ := IsFundamental.involution_unique hodd hi hi₃
    have e2 : j = i₄ := IsFundamental.involution_unique hodd hj hi₄
    rw [e1, e2, htw]
  have hfix : ∀ a, 1 ≤ a → a ≤ 1 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 y hy =>
    hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)) _
      (by rw [(hRz (a + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode 4 (by omega) (by omega) (hβJ 4 (by omega) (by omega)) _
      (by rw [(hRz 4 (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y := fun y hy =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hMz).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hMβ' t ht.mem n hn).symm) _
      (by rw [hMR]; exact ⟨y, hy, rfl⟩)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := by
    intro y hy
    have hL : locImg Ω z (nd.J ⟨2, by omega⟩) = (R 0).map θ :=
      (hRz (0 + 2) (by omega) (by omega)).2
    rw [← hL, ← hstab2]
    refine ⟨θ y, ?_, rfl⟩
    rw [hL]
    exact ⟨y, hy, rfl⟩
  obtain ⟨x, tM, hxR, hxtw, hxM, α, g₀, hαθ, hg₀O, hg₀2, hconj⟩ := minusLift_of_chain_frame3
    (s := 1) (by omega) θ c.d.ker_le σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hdist
    hne htwin hfix hfixtw hfixM hnorm0
  have hnode : ∀ a (ha : a ≤ 1), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp 6 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
          c.d.ψ := by
    intro a ha
    rw [(hRz (a + 2) (by omega) (by omega)).2]
    have h := hxR a ha
    change Rz (a + 2) = _ at h
    rw [h]
  have hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp 6 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 3 4
        (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [hMR]
    have h : RM = _ := hxM
    change RzM = _ at h
    rw [h]
  have hconj' : ∀ y, spinAction (QM3 6) (α y) * g₀ = g₀ * spinAction (QM3 6) y :=
    fun y => LinearEquiv.ext fun v => hconj y v
  have hmov0 : ∃ y ∈ (rootSL2 (minusHyp 6 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 0 1
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom,
      σ (θ y) ≠ θ y := by
    by_contra hcon
    push Not at hcon
    have hJ2 := hmemz 2 (by omega) (by omega)
    have hNt : nd.J ⟨2, by omega⟩ ≤ Subgroup.centralizer ({t} : Set G) := by
      rw [locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hJ2]
      intro a ha
      rw [hnode 0 (by omega)] at ha
      obtain ⟨y, hy, rfl⟩ := ha
      exact hcon y hy
    have hβJ2 : Commutes β (nd.J ⟨2, by omega⟩) :=
      c.commutes_partner_of_centralizes3 hMFZ hsingle D (h1 ▸ nd.mem _) ht ⟨W, hW⟩ hJ2
        hNt (hKJ 2 (by omega) le_rfl)
    exact nd.not_commutes_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by fr_idx)
      (h1 ▸ hβJ2)
  obtain ⟨xM, hxM'⟩ := hΩ.classical M hMΩ
  have hN0 : (∀ y ∈ (rootSL2 (minusHyp 6 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 0 3
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom,
      σ (θ y) = θ y) → False := fun hfix03 =>
    false_of_fixed_zero_three3 c hsingle D (h1 ▸ nd.mem _) ht htz ⟨W, hW⟩
      (nd.mem ⟨3, by omega⟩) (nd.cl ⟨3, by omega⟩) (hKJ 3 (by omega) (by omega))
      (hβJ 3 (by omega) (by omega)) hMΩ hxM' hMK hMβ (nd.commK _) x tM (hnode 1 (by omega))
      hMimg hfix03
  have hdim9 : 9 ≤ Module.finrank (GaloisField 3 1) (Vm 6 (GaloisField 3 1)) := by
    rw [finrank_minus 3 1 6 (by omega)]
    omega
  have hR₁ : (rootSL2 (minusHyp 6 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 1 2 (by omega)
      (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom ∈
      fundamentalSubgroups .POmegaMinus (minusDatum 6 (minusCoeffs_irr 3 1)) :=
    cq.rootSL2_conj_mem _ (by omega) (by omega) (by omega) _ _ x
  obtain ⟨R₀, R₀', hR₀, hR₀', hadjP, hcP, hcP', hfP, hfP'⟩ := exists_fixed_adjacent_pair3 c hsingle
    (h1 ▸ nd.mem _) ht htz ⟨W, hW⟩ (nd.mem ⟨3, by omega⟩) (nd.cl ⟨3, by omega⟩)
    (hKJ 3 (by omega) (by omega)) (hβJ 3 (by omega) (by omega)) (hnode 1 (by omega))
  have hgR : ∀ y ∈ R₀, g₀ * spinAction (QM3 6) y = spinAction (QM3 6) y * g₀ :=
    commute_of_fixed3 θ c.d.ker_le c.hY.cop α σ hαθ (spinAction (QM3 6)) hconj' (cq.pow3 R₀ hR₀) hfP
  have hgR' : ∀ y ∈ R₀', g₀ * spinAction (QM3 6) y = spinAction (QM3 6) y * g₀ :=
    commute_of_fixed3 θ c.d.ker_le c.hY.cop α σ hαθ (spinAction (QM3 6)) hconj' (cq.pow3 R₀' hR₀')
      hfP'
  have hpair : ∃ (T₀ : Submodule (GaloisField 3 1) (Vm 6 (GaloisField 3 1))) (s : GaloisField 3 1),
      6 ≤ Module.finrank (GaloisField 3 1) T₀ ∧ (∀ v ∈ T₀, g₀ v = s • v) ∧
      (∀ v ∈ T₀, ∀ k : Fin (6 - 1), (k.val = 1 ∨ k.val = 2) → ∀ u,
        polar (QM3 6) v (spinAction (QM3 6) x (minusVec 6 k u)) = 0) := by
    obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
    obtain ⟨T, s, hT6, hTg, hTp⟩ := hpair_data3 hodd hdim9 cq hR₀ hR₀' hR₁ hadjP hcP hcP' hi₁ hg₀O
      hg₀2 hgR hgR'
    refine ⟨T, s, hT6, hTg, fun v hv k hk u => hTp v hv _ ?_⟩
    exact TwinSmall.spinAction_vec_mem_negSpace hodd
      (minusHyp 6 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) (a := 1) (b := 2) (by omega) (by omega)
      (by omega) true false x hi₁ (k := k.val) k.isLt hk u
  have hcopZ : ∀ w ∈ Subgroup.center (spinGroup (quadMinus 6 (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf w :=
    fun w hw => c.hY.cop w hw
  have hpowR : ∀ (a b' : ℕ) (ha : a < 6 - 1) (hb' : b' < 6 - 1) (hab : a ≠ b')
      (sg tg : Bool) (x' : spinGroup (quadMinus 6 (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)),
      Pow3 ((rootSL2 (minusHyp (6) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a b' ha hb'
        hab sg tg).map (MulAut.conj x').toMonoidHom) :=
    fun a b' ha hb' hab sg tg x' => cq.pow3 _ (cq.rootSL2_conj_mem _ ha hb' hab sg tg x')
  have hpowk : ∀ (k : Fin (6 - 1)) (x' : spinGroup (quadMinus (6)
      (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)),
      Pow3 ((rankOne (minusDatum (6) hirr).rootGroup k).map
        (MulAut.conj x').toMonoidHom) := by
    intro k x'
    by_cases hk : k.val + 1 < 6 - 1
    · rw [rankOne_minusDatum_of_lt hirr hk]
      exact hpowR k.val (k.val + 1) k.isLt hk (by omega) true false x'
    · have := fact_shortField hirr
      have := finite_shortField (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
      have hperf : rankOne (minusDatum (6) hirr).rootGroup k ≤
          ⁅rankOne (minusDatum (6) hirr).rootGroup k,
            rankOne (minusDatum (6) hirr).rootGroup k⁆ := by
        rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_short hirr hk]
        exact range_perfect_of_sl2
          (CFSG.ClassicalInvolution.Models.TwistedPairs.four_le_card_shortField'
            (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)) _
      have hperf' : ⁅rankOne (minusDatum (6) hirr).rootGroup k,
          rankOne (minusDatum (6) hirr).rootGroup k⁆ =
          rankOne (minusDatum (6) hirr).rootGroup k :=
        le_antisymm (commutator_self_le _) hperf
      intro l hl
      have h2' : ⁅(rankOne (minusDatum (6) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom, (rankOne (minusDatum (6) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom⁆ = (rankOne (minusDatum (6) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom := by
        rw [← Subgroup.map_commutator, hperf']
      rw [h2']
      exact pow_mem hl 3
  refine ⟨x, ?_, ?_⟩
  · rw [rankOne_minusDatum_of_lt hirr (by show 0 + 1 < 6 - 1; omega)]
    exact hnode 0 (by omega)
  · refine minus_nodes_fixed_six3 hirr hodd h2 hcopZ hpowR hpowk cq.ker_le θ c.d.ker_le σ α hαθ hg₀O
      hg₀2 hconj' x tM ?_ ?_ ?_ hmov0 hN0 hpair
    · intro y hy
      exact hfix 1 le_rfl le_rfl y (by rw [hxR 1 le_rfl]; exact hy)
    · intro y hy
      exact hfixM y (by rw [hxM]; exact hy)
    · intro y hy
      have h := hnorm0 y (by rw [hxR 0 (by omega)]; exact hy)
      rwa [hxR 0 (by omega)] at h

end Main

section Stmt

theorem partnerPatternStmt3_six (h3 : OddThreeFreeInput) : PartnerPatternStmt3 6 := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  have hadm : StatedLieAdmissible .POmegaMinus 6 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  obtain ⟨c⟩ := Q3TC.nonempty_tctx3 (yData3_minus (by norm_num) hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨ι, -, D, -, -⟩ := id hshape
  have htz : t * z * t⁻¹ = z := by
    obtain ⟨W, hW⟩ := hKβ
    have hzt : Commute z t := standardPair_involutions_commute two_ne_zero_gf3 hW c.hz.mem ht.mem
      c.hz.orderOf_eq_two ht.orderOf_eq_two
    rw [mul_inv_eq_iff_eq_mul]
    exact hzt.symm.eq
  exact PartnerPatternMinus3.of_fixed_nodes (by norm_num) c hsingle hβ ht hKβ htz
    (fun hMΩ hMN nd h0 h1 => minus_fixed_of_nodes_six3 c hsingle D ht htz hKβ hMΩ hMN nd h0 h1)
    hfix

end Stmt

end CFSG.ClassicalInvolution.Q3.Q3TY
