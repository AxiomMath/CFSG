module

public import CFSG.ClassicalInvolution.Q3.Q3TY44
public import CFSG.ClassicalInvolution.Q3.Q3TY43
public import CFSG.ClassicalInvolution.Q3.Q3TY42
public import CFSG.ClassicalInvolution.Q3.Q3TY39
public import CFSG.ClassicalInvolution.RouteD.TwinSmallLift
public import CFSG.ClassicalInvolution.RouteD.TwinSmallSeven

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

local notation "OPFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local macro "fr_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)


section Lift

variable {X : Type} [Group X]

theorem minusLift_of_chain_frame3 {s : ℕ} (hs : 1 ≤ s)
    {X : Type} [Group X]
    (θ : spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (s + 5) (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    {Rtw RM : Subgroup (spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    (hRf : ∀ a ≤ s, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (s + 5) (minusCoeffs_irr 3 1)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus (minusDatum (s + 5) (minusCoeffs_irr 3 1)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum (s + 5) (minusCoeffs_irr 3 1)))
    (hadj : ∀ a < s, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < s, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ s → Commutes (R a) (R b))
    (hM : ∀ a ≤ s, Commutes RM (R a))
    (hdist : ∀ a b, a + 1 < b → b ≤ s → ∀ i j,
      IsFundamental (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        ((R a).map (spinAction (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) i →
      IsFundamental (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        ((R b).map (spinAction (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) j → i ≠ j)
    (hne : Rtw ≠ R s)
    (htwin : ∀ i j,
      IsFundamental (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        ((R s).map (spinAction (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) i →
      IsFundamental (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)
        (Rtw.map (spinAction (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
          (minusCoeffs 3 1).2))) j → i = j)
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (x : spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) (t : Bool),
      (∀ a (ha : a ≤ s), R a = ((rootSL2 (minusFrame (s + 5) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2).toHypFrame a (a + 1) (by omega) (by omega) (by omega) true false).map
          (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (minusFrame (s + 5) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2).toHypFrame s (s + 1) (by omega) (by omega) (by omega) true
          true).map (MulAut.conj x).toMonoidHom) ∧
      RM = ((rootSL2 (minusFrame (s + 5) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2).toHypFrame (s + 2) (s + 3) (by omega) (by omega) (by omega)
          true t).map (MulAut.conj x).toMonoidHom) ∧ MinusLift θ σ := by
  have hadm : StatedLieAdmissible .POmegaMinus (s + 5) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ s + 5; omega⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have cq := centralQuot3_minus hadm
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (s + 5 - 1) ⊕ Fin (s + 5 - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_minus 3 1 _ (by omega)]
    omega
  have hQ : (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField 3 1) (minusCoeffs_irr 3 1))
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen3 hQ (s := s) hs
    (minusFrame (s + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame hdim cq hRf hRtwf
    hRMf hadj hlin hcomm hM hdist hne htwin
  exact ⟨x, t, hxR, hxtw, hxM, (toralNormal_minus_of_frame_chain3 hs θ hker σ hσ2 hσr x t
    hxR hxtw hxM hfix hfixtw hfixM hnorm0).2⟩

end Lift

section Main

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem minus_fixed_of_nodes_seven3 (c : Q3TC.TCtx3 .POmegaMinus 7 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes3 (7 - 1) Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β) :
    ∃ x : spinGroup (quadMinus 7 (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
      locImg Ω z (nd.J ⟨2, by omega⟩) =
        ((rankOne (minusDatum 7 (minusCoeffs_irr 3 1)).rootGroup
          (⟨0, by omega⟩ : Fin (7 - 1))).map (MulAut.conj x).toMonoidHom).map c.d.ψ ∧
      ∀ k : Fin (7 - 1), 1 ≤ k.val →
        ∀ r ∈ (rankOne (minusDatum 7 (minusCoeffs_irr 3 1)).rootGroup k).map
          (MulAut.conj x).toMonoidHom,
        locAut c.hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r := by
  classical
  have hMFZ : Gaps.FundNoncentral 3 := Gaps.fundNoncentral 3
  have hirr := minusCoeffs_irr 3 1
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaMinus 7 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
  have : Finite (modelUniv .POmegaMinus 7 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have cq := ctx_centralQuot3 (by norm_num : 4 ≤ 7)
  have hKJ : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp; omega)) (by fr_idx)
  have hmemz : ∀ a (h : a < 7 - 1), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 7 - 1), 2 ≤ a →
      ∃ b, ∃ hb : b < 7 - 1, 2 ≤ b ∧ DNodes3.Adj (⟨a, h⟩ : Fin (7 - 1)) ⟨b, hb⟩ := by
    intro a h ha
    have : a < 6 := h
    interval_cases a
    · exact ⟨3, by omega, by omega, by fr_idx⟩
    · exact ⟨2, by omega, by omega, by fr_idx⟩
    · exact ⟨3, by omega, by omega, by fr_idx⟩
    · exact ⟨3, by omega, by omega, by fr_idx⟩
  have hlayer : ∀ a (h : a < 7 - 1), 2 ≤ a → IsLayerMember3 c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember3.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (SpinM3 7),
      ∀ (h : a < 7 - 1), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 7 - 1 ∧ 2 ≤ a
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
  have hcommz : ∀ a (ha : a < 7 - 1) b (hb : b < 7 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 7 - 1) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 7 - 1) b (hb : b < 7 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin (7 - 1)) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (SpinM3 7)) (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    c.modelAdj_of_adj3 (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w _ _) (nd.conjSub_w hab)
  have hlinz : ∀ a (ha : a < 7 - 1) b (hb : b < 7 - 1) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin (7 - 1)) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact c.lift_lin (hRz a ha ha2).1 (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 7 - 1), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 7 - 1), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
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
  let θ : spinGroup (quadMinus 7 (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    c.locAut_mem_range htz h2t hKt
      (Exotic.range_le_iSup_fund_minus (p := 3) (f := 1) (by omega) hadm c.hY.std c.d.ψ) k'
  let R : ℕ → Subgroup (SpinM3 7) := fun a => Rz (a + 2)
  let Rtw : Subgroup (SpinM3 7) := Rz 5
  let RM : Subgroup (SpinM3 7) := RzM
  have hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum 7 (minusCoeffs_irr 3 1)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) :=
    (hRz 5 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum 7 (minusCoeffs_irr 3 1)) :=
    hRzM
  have hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by fr_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx)) (by fr_idx))
  have hM : ∀ a ≤ 2, Commutes RM (R a) := fun a ha =>
    hMcomm (a + 2) (by omega) (by omega)
  have hne : Rtw ≠ R 2 := by
    intro h
    have h' : Rz 5 = Rz (2 + 2) := h
    have h2' : nd.J ⟨5, by omega⟩ = nd.J ⟨2 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 5 (by omega) (by omega)).2, (hRz (2 + 2) (by omega) (by omega)).2, h'])
    exact nd.ne_J (Gaps.fin_ne_of_val_ne (by simp)) h2'
  obtain ⟨hdist2, htwin2⟩ := chain_twin_data_seven3 c hsingle hMΩ nd h0
    (hRz 2 (by omega) (by omega)).1 (hRz 3 (by omega) (by omega)).1 (hRz 4 (by omega) (by omega)).1
    (hRz 5 (by omega) (by omega)).1 (hRz 2 (by omega) (by omega)).2 (hRz 3 (by omega) (by omega)).2
    (hRz 4 (by omega) (by omega)).2 (hRz 5 (by omega) (by omega)).2
  have hdist : ∀ a b, a + 1 < b → b ≤ 2 → ∀ i j,
      IsFundamental (QM3 7) ((R a).map (spinAction (QM3 7))) i →
      IsFundamental (QM3 7) ((R b).map (spinAction (QM3 7))) j → i ≠ j := by
    intro a b hab hb
    obtain rfl : a = 0 := by omega
    obtain rfl : b = 2 := by omega
    exact hdist2
  have htwin : ∀ i j, IsFundamental (QM3 7) ((R 2).map (spinAction (QM3 7))) i →
      IsFundamental (QM3 7) (Rtw.map (spinAction (QM3 7))) j → i = j := htwin2
  have hfix : ∀ a, 1 ≤ a → a ≤ 2 → ∀ y ∈ R a, σ (θ y) = θ y := fun a ha1 ha2 y hy =>
    hfixnode (a + 2) (by omega) (by omega) (hβJ (a + 2) (by omega) (by omega)) _
      (by rw [(hRz (a + 2) (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y := fun y hy =>
    hfixnode 5 (by omega) (by omega) (hβJ 5 (by omega) (by omega)) _
      (by rw [(hRz 5 (by omega) (by omega)).2]; exact ⟨y, hy, rfl⟩)
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
  obtain ⟨x, tM, hxR, hxtw, hxM, α, g₀, hαθ, hg₀O, hg₀2, hconj⟩ := minusLift_of_chain_frame3
    (s := 2) (by omega) θ c.d.ker_le σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hdist
    hne htwin hfix hfixtw hfixM hnorm0
  have hnode : ∀ a (ha : a ≤ 2), locImg Ω z (nd.J ⟨a + 2, by omega⟩) =
      ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a (a + 1)
        (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
          c.d.ψ := by
    intro a ha
    rw [(hRz (a + 2) (by omega) (by omega)).2]
    have h := hxR a ha
    change Rz (a + 2) = _ at h
    rw [h]
  have hMimg : locImg Ω z M =
      ((rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 4 5
        (by omega) (by omega) (by omega) true tM).map (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    rw [hMR]
    have h : RM = _ := hxM
    change RzM = _ at h
    rw [h]
  have hconj' : ∀ y, spinAction (QM3 7) (α y) * g₀ = g₀ * spinAction (QM3 7) y :=
    fun y => LinearEquiv.ext fun v => hconj y v
  obtain ⟨R₁, hR₁, ⟨F₁, hR₁m, hv₁, hα₁⟩, hR₁f⟩ := leaf_fixed_cluster3 c hsingle ht htz hMΩ nd
    h0 h1 x tM hnode hMimg
  obtain ⟨R₂, hR₂, ⟨F₂, hR₂m, hv₂, hα₂⟩, hR₂f⟩ := leaf_fixed_M3 c hsingle ht htz hMΩ nd
    h0 h1 x tM hnode hMimg
  have hmov0 : ∃ y ∈ (rootSL2 (minusHyp 7 (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) 0 1
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
  have hcopZ : ∀ w ∈ Subgroup.center (spinGroup (quadMinus (7) (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)), ¬ 3 ∣ orderOf w :=
    fun w hw => c.hY.cop w hw
  have hpowR : ∀ (a b' : ℕ) (ha : a < 7 - 1) (hb' : b' < 7 - 1) (hab : a ≠ b')
      (sg tg : Bool) (x' : spinGroup (quadMinus (7) (GaloisField 3 1) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2)),
      Pow3 ((rootSL2 (minusHyp (7) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) a b' ha hb'
        hab sg tg).map (MulAut.conj x').toMonoidHom) :=
    fun a b' ha hb' hab sg tg x' => cq.pow3 _ (cq.rootSL2_conj_mem _ ha hb' hab sg tg x')
  have hpowk : ∀ (k : Fin (7 - 1)) (x' : spinGroup (quadMinus (7)
      (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)),
      Pow3 ((rankOne (minusDatum (7) hirr).rootGroup k).map
        (MulAut.conj x').toMonoidHom) := by
    intro k x'
    by_cases hk : k.val + 1 < 7 - 1
    · rw [rankOne_minusDatum_of_lt hirr hk]
      exact hpowR k.val (k.val + 1) k.isLt hk (by omega) true false x'
    · have := fact_shortField hirr
      have := finite_shortField (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)
      have hperf : rankOne (minusDatum (7) hirr).rootGroup k ≤
          ⁅rankOne (minusDatum (7) hirr).rootGroup k,
            rankOne (minusDatum (7) hirr).rootGroup k⁆ := by
        rw [CFSG.ClassicalInvolution.WeakCT.rankOne_minusDatum_short hirr hk]
        exact range_perfect_of_sl2
          (CFSG.ClassicalInvolution.Models.TwistedPairs.four_le_card_shortField'
            (b := (minusCoeffs 3 1).1) (c := (minusCoeffs 3 1).2)) _
      have hperf' : ⁅rankOne (minusDatum (7) hirr).rootGroup k,
          rankOne (minusDatum (7) hirr).rootGroup k⁆ =
          rankOne (minusDatum (7) hirr).rootGroup k :=
        le_antisymm (commutator_self_le _) hperf
      intro l hl
      have h2' : ⁅(rankOne (minusDatum (7) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom, (rankOne (minusDatum (7) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom⁆ = (rankOne (minusDatum (7) hirr).rootGroup k).map
          (MulAut.conj x').toMonoidHom := by
        rw [← Subgroup.map_commutator, hperf']
      rw [h2']
      exact pow_mem hl 3
  refine ⟨x, ?_, ?_⟩
  · rw [rankOne_minusDatum_of_lt hirr (by show 0 + 1 < 7 - 1; omega)]
    exact hnode 0 (by omega)
  · refine minus_nodes_fixed_seven3 hirr h2 hcopZ hpowR hpowk cq.ker_le θ c.d.ker_le σ α hαθ hg₀O
      hg₀2 hconj' x tM ?_ ?_ ⟨R₁, F₁, cq.pow3 R₁ hR₁, hR₁m, hv₁, hα₁, hR₁f⟩
      ⟨R₂, F₂, cq.pow3 R₂ hR₂, hR₂m, hv₂, hα₂, hR₂f⟩ ?_ hmov0
    · intro a h1' ha y hy
      exact hfix a h1' ha y (by rw [hxR a ha]; exact hy)
    · intro y hy
      exact hfixM y (by rw [hxM]; exact hy)
    · intro y hy
      have h := hnorm0 y (by rw [hxR 0 (by omega)]; exact hy)
      rwa [hxR 0 (by omega)] at h

theorem PartnerPatternMinus3.of_fixed_nodes {m : ℕ} (hm : 5 ≤ m)
    (c : Q3TC.TCtx3 .POmegaMinus m Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) (htz : t * z * t⁻¹ = z)
    (hfixed : ∀ {M : Subgroup G}, M ∈ Ω →
      (∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N) →
      ∀ nd : DNodes3 (m - 1) Ω M, nd.J ⟨0, by omega⟩ = K → nd.J ⟨1, by omega⟩ = β →
        ∃ x : spinGroup (quadMinus m (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2),
          locImg Ω z (nd.J ⟨2, by omega⟩) =
            ((rankOne (minusDatum m (minusCoeffs_irr 3 1)).rootGroup
              (⟨0, by omega⟩ : Fin (m - 1))).map (MulAut.conj x).toMonoidHom).map c.d.ψ ∧
          ∀ k : Fin (m - 1), 1 ≤ k.val →
            ∀ r ∈ (rankOne (minusDatum m (minusCoeffs_irr 3 1)).rootGroup k).map
              (MulAut.conj x).toMonoidHom,
            locAut c.hΩ.conjInvariant htz (c.d.ψ r) = c.d.ψ r)
    (hfix : HasFixedMember Ω K β z) : PartnerPatternMinus3 m Ω K β t := by
  classical
  have hΩ := c.hΩ
  obtain ⟨M, hMΩ, hKM, hβM, hMnot⟩ := hfix
  have hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra hcon
    push Not at hcon
    exact hMnot hcon
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_minus3 hm c hsingle hβ ht hKβ hMΩ hKM hβM
  obtain ⟨x, hx2, hxfix⟩ := hfixed hMΩ hMN nd h0 h1
  obtain ⟨j, hjK, hjY, hjΩ, hjperf, hjc, hjp, hjtw, hjimg⟩ :=
    c.exists_nodes_typeTwistedD3_img (m := m) (by omega)
      (spinMinus6Generated_galois (p := 3) (f := 1) (by norm_num))
  obtain ⟨y₀, hy₀⟩ := QuotientGroup.mk_surjective (c.d.ψ x)
  have hy : (y₀ : G) ∈ locLayer Ω z := y₀.2
  have hyz : (y₀ : G) * z * (y₀ : G)⁻¹ = z := by
    have := Subgroup.mem_centralizer_singleton_iff.mp
      (centralizingLayer_le_centralizer Ω {z} hy)
    rw [mul_inv_eq_iff_eq_mul]
    exact this
  have himg : ∀ a : Fin (m - 1), locImg Ω z (conjSub (y₀ : G) (j a)) =
      ((rankOne (minusDatum m (minusCoeffs_irr 3 1)).rootGroup a).map
        (MulAut.conj x).toMonoidHom).map c.d.ψ := by
    intro a
    rw [locImg_conjSub_layer, hjimg a, show locMk Ω z y₀ = c.d.ψ x from hy₀]
    exact map_conj_map_hom c.d.ψ x _
  refine PartnerPatternMinus3.of_locAut c hjK hjY (fun a ha => (hjΩ a ha).1) hjperf hjc hjp hjtw
    hy htz (fun a ha w hw => ?_) (fun a ha => ?_)
  · rw [himg a] at hw
    obtain ⟨r, hr, rfl⟩ := hw
    exact hxfix a ha r hr
  ·
    obtain ⟨a', ha'⟩ := a
    have ha0 : a' = 0 := ha
    subst ha0
    have hmemy : conjSub (y₀ : G) (j ⟨0, by omega⟩) ∈ centralizingMembers Ω {z} := by
      have := centralizingMembers_conj hΩ.conjInvariant (y₀ : G) z
      rw [hyz] at this
      rw [this]
      exact ⟨j ⟨0, by omega⟩, mem_centralizingMembers_of_commutes
        (hjΩ _ (by show 0 + 2 < m; omega)).1.1 c.hz.mem (commutes_symm (hjK _)), rfl⟩
    have hK2 : Commutes K (nd.J ⟨2, by omega⟩) := by
      rw [← h0]
      exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by simp)) (by fr_idx)
    have hJ2 : nd.J ⟨2, by omega⟩ ∈ centralizingMembers Ω {z} :=
      mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem (commutes_symm hK2)
    have heq : conjSub (y₀ : G) (j ⟨0, by omega⟩) = nd.J ⟨2, by omega⟩ :=
      c.eq_of_locImg_eq hmemy hJ2 (by rw [himg, hx2])
    rw [heq]
    obtain ⟨W, hW⟩ := nd.pair_of_adj (a := ⟨1, by omega⟩) (b := ⟨2, by omega⟩) (by fr_idx)
    rw [h1] at hW
    exact ⟨W, hW⟩

end Main

section Stmt

theorem partnerPatternStmt3_seven (h3 : OddThreeFreeInput) : PartnerPatternStmt3 7 := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  have hadm : StatedLieAdmissible .POmegaMinus 7 3 1 := ⟨Nat.prime_three, le_rfl, by norm_num⟩
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
    (fun hMΩ hMN nd h0 h1 => minus_fixed_of_nodes_seven3 c hsingle D ht htz hKβ hMΩ hMN nd h0 h1)
    hfix

end Stmt

end CFSG.ClassicalInvolution.Q3.Q3TY
