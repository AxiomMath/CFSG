module

public import CFSG.ClassicalInvolution.Q3.Q3TY37
public import CFSG.ClassicalInvolution.Q3.Q3TY35
public import CFSG.ClassicalInvolution.Q3.Q3TY34
public import CFSG.ClassicalInvolution.Q3.Q3TY19
public import CFSG.ClassicalInvolution.Q3.Q3TY8
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusSmallZ

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
  CFSG.ClassicalInvolution.Models.OrthogonalPairs
open scoped MatrixGroups commutatorElement

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem minus_fixed_of_nodes_ge3_3 (hMFZ : Gaps.FundNoncentral 3) {u : ℕ}
    (c : Q3TC.TCtx3 .POmegaMinus (u + 3 + 5) Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes3 (u + 3 + 5 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K)
    (h1 : nd.J ⟨1, by omega⟩ = β) :
    ∃ x : spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2),
      locImg Ω z (nd.J ⟨2, by omega⟩) =
        ((rankOne (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)).rootGroup
          (⟨0, by omega⟩ : Fin (u + 3 + 5 - 1))).map (MulAut.conj x).toMonoidHom).map c.d.ψ ∧
      ∀ k : Fin (u + 3 + 5 - 1), 1 ≤ k.val →
        ∀ r ∈ (rankOne (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)).rootGroup k).map
          (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r := by
  classical
  have hirr := minusCoeffs_irr 3 1
  have hm3 : 3 ≤ u + 3 + 5 - 1 := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaMinus (u + 3 + 5) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ u + 3 + 5; omega⟩
  have : Finite (modelUniv .POmegaMinus (u + 3 + 5) 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by omega) Nat.prime_three trivial hadm
  have hKJ : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a →
      ∃ b, ∃ hb : b < u + 3 + 5 - 1, 2 ≤ b ∧
        DNodes3.Adj (⟨a, h⟩ : Fin (u + 3 + 5 - 1)) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a ≤ u + 4
    · exact ⟨a + 1, by omega, by omega, by fr_idx⟩
    · exact ⟨u + 4, by omega, by omega, by fr_idx⟩
  have hlayer : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → IsLayerMember3 c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember3.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaMinus (u + 3 + 5) 3 1 Nat.prime_three).K,
      ∀ (h : a < u + 3 + 5 - 1), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaMinus
            (modelUniv .POmegaMinus (u + 3 + 5) 3 1 Nat.prime_three).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < u + 3 + 5 - 1 ∧ 2 ≤ a
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
  have hcommz : ∀ a (ha : a < u + 3 + 5 - 1) b (hb : b < u + 3 + 5 - 1) (ha2 : 2 ≤ a)
      (hb2 : 2 ≤ b), Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < u + 3 + 5 - 1) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < u + 3 + 5 - 1) b (hb : b < u + 3 + 5 - 1) (ha2 : 2 ≤ a)
      (hb2 : 2 ≤ b), DNodes3.Adj (⟨a, ha⟩ : Fin (u + 3 + 5 - 1)) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaMinus (u + 3 + 5) 3 1 Nat.prime_three).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    c.modelAdj_of_adj3 (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w _ _) (nd.conjSub_w hab)
  have hlinz : ∀ a (ha : a < u + 3 + 5 - 1) b (hb : b < u + 3 + 5 - 1) (ha2 : 2 ≤ a)
      (hb2 : 2 ≤ b), DNodes3.Adj (⟨a, ha⟩ : Fin (u + 3 + 5 - 1)) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact c.lift_lin (hRz a ha ha2).1 (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < u + 3 + 5 - 1), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < u + 3 + 5 - 1), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map
      (locAut hΩ.conjInvariant htz).toMonoidHom = locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by fr_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    c.locAut_mem_range htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (p := 3) (f := 1) (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := fun a => Rz (a + 2)
  let Rtw : Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := Rz (u + 6)
  let RM : Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) := RzM
  have hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)) :=
    (hRz (u + 6) (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)) := hRzM
  have hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hM : ∀ a ≤ u + 3, Commutes RM (R a) := fun a ha =>
    hMcomm (a + 2) (by omega) (by omega)
  have hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw :=
    hadjz (u + 2 + 2) (by omega) (u + 6) (by omega) (by omega) (by omega) (by fr_idx)
  have hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw := fun a ha =>
    hcommz (a + 2) (by omega) (u + 6) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hcommtw' : Commutes (R (u + 3)) Rtw :=
    hcommz (u + 3 + 2) (by omega) (u + 6) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hne : Rtw ≠ R (u + 3) := by
    intro h
    have h' : Rz (u + 6) = Rz (u + 3 + 2) := h
    have h2' : nd.J ⟨u + 6, by omega⟩ = nd.J ⟨u + 3 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz (u + 6) (by omega) (by omega)).2, (hRz (u + 3 + 2) (by omega) (by omega)).2,
          h'])
    exact nd.ne_J (Gaps.fin_ne_of_val_ne (by simp)) h2'
  have hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 y hy =>
    hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)) _
      (by rw [(hRz (a + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode (u + 6) (by omega) (by omega) (hβJ (u + 6) (by omega) (by omega)) _
      (by rw [(hRz (u + 6) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y := fun y hy =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hMz).mp (fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm) _
      (by rw [hMR]; exact ⟨y, hy, rfl⟩)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := by
    intro y hy
    have hL : locImg Ω z (nd.J ⟨2, by omega⟩) = (R 0).map θ :=
      (hRz (0 + 2) (by omega) (by omega)).2
    rw [← hL, ← hstab2]
    refine ⟨θ y, ?_, rfl⟩
    rw [hL]
    exact ⟨y, hy, rfl⟩
  obtain ⟨x, tM, hxR, hxtw, hxM, α, g₀, hαθ, hg₀O, hg₀2, hconj⟩ := minusLift_of_chain_long3
    θ c.d.ker_le σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hadjtw hcommtw hcommtw' hne hfix
    hfixtw hfixM hnorm0
  have cq := centralQuot3_minus hadm
  have hnode : ∀ a (ha : a ≤ u + 3), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp (u + 3 + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
          c.d.ψ := by
    intro a ha
    rw [(hRz (a + 2) (by omega) (by omega)).2]
    have h := hxR a ha
    change Rz (a + 2) = _ at h
    rw [h]
  have hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp (u + 3 + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) (u + 3 + 2)
        (u + 3 + 3) (by omega) (by omega) (by omega) true tM).map
          (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [hMR]
    have h : RM = _ := hxM
    change RzM = _ at h
    rw [h]
  have hconj' : ∀ y, spinAction (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) (α y) * g₀ = g₀ * spinAction _ y :=
    fun y => LinearEquiv.ext fun v => hconj y v
  have hMβ' : Commutes β M := hMβ
  have hcopZ : ∀ w ∈ Subgroup.center (spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf w :=
    fun w hw => c.hY.cop w hw
  have hpowR : ∀ (a b' : ℕ) (ha : a < u + 3 + 5 - 1) (hb' : b' < u + 3 + 5 - 1) (hab : a ≠ b')
      (sg tg : Bool) (x' : spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)),
      Pow3 ((rootSL2 (minusHyp (u + 3 + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a b' ha hb'
        hab sg tg).map (MulAut.conj x').toMonoidHom) :=
    fun a b' ha hb' hab sg tg x' => cq.pow3 _ (cq.rootSL2_conj_mem _ ha hb' hab sg tg x')
  have hpowk : ∀ (k : Fin (u + 3 + 5 - 1)) (x' : spinGroup (quadMinus (u + 3 + 5)
      (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)),
      Pow3 ((rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k).map
        (MulAut.conj x').toMonoidHom) := by
    intro k x'
    by_cases hk : k.val + 1 < u + 3 + 5 - 1
    · rw [rankOne_minusDatum_of_lt hirr hk]
      exact hpowR k.val (k.val + 1) k.isLt hk (by omega) true false x'
    · have := fact_shortField hirr
      have := finite_shortField (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
      have hperf : rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k ≤
          ⁅rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k,
            rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k⁆ := by
        rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_short hirr hk]
        exact range_perfect_of_sl2
          (CFSG.ClassicalInvolution.Models.TwistedPairs.four_le_card_shortField'
            (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)) _
      have hperf' : ⁅rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k,
          rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k⁆ =
          rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k :=
        le_antisymm (commutator_self_le _) hperf
      intro l hl
      have h2' : ⁅(rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom, (rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom⁆ = (rankOne (minusDatum (u + 3 + 5) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom := by
        rw [← Subgroup.map_commutator, hperf']
      rw [h2']
      exact pow_mem hl 3
  refine ⟨x, ?_, ?_⟩
  · rw [rankOne_minusDatum_of_lt hirr (by show 0 + 1 < u + 3 + 5 - 1; omega)]
    exact hnode 0 (by omega)
  · refine minus_nodes_fixed_bridge3 hirr h2 (s := u + 3) (by omega) hcopZ hpowR hpowk cq.ker_le
      θ c.d.ker_le σ α hαθ hg₀O hg₀2 hconj' x tM ?_ ?_ ?_ ?_ ?_ ?_
    · intro a h1' ha j1 j2 j3 y hy
      exact hfix a h1' ha y (by rw [hxR a ha]; exact hy)
    · intro j1 j2 j3
      exact leafBridge_fixed3 (s := u + 3) (by omega) c hsingle ht htz hMΩ hMz nd h0 h1 x tM hnode
        hMimg
    · intro j1 j2 j3 y hy
      exact hfixM y (by rw [hxM]; exact hy)
    · intro j1 j2 j3 w y hy
      exact leafW_fixed_ge3_3 (s := u + 3) (by omega) c hsingle ht htz hMΩ hMz nd h0 h1 x tM hnode
        hMimg (Pi.single w 1) y hy
    · intro j1 j2 j3 y hy
      have h := hnorm0 y (by rw [hxR 0 (by omega)]; exact hy)
      rwa [hxR 0 (by omega)] at h
    · intro j1 j2 j3
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
        c.commutes_partner_of_centralizes3 hMFZ hsingle D (h1 ▸ nd.mem _) ht ⟨W, hW⟩ hJ2 hNt
          (hKJ 2 (by omega) le_rfl)
      exact nd.not_commutes_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by fr_idx)
        (h1 ▸ hβJ2)

end Main

end CFSG.ClassicalInvolution.Q3.Q3TY
