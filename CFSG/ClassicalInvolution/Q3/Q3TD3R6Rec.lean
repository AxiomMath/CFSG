module

public import CFSG.ClassicalInvolution.Q3.Q3TD3R6Lift
public import CFSG.ClassicalInvolution.RouteD.TWED6Rec

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.Timmesfeld CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.TWE.D6 (star_twin_of_distinguish')
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


section Group

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem fin_ne_of_val_ne3 {n : ℕ} {a b : Fin n} (h : a.val ≠ b.val) : a ≠ b :=
  fun e => h (congrArg Fin.val e)

local macro "d6_idx" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

theorem recognition_plus_six3 (c : TCtx3 .POmegaPlus 6 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t) (htz : t * z * t⁻¹ = z)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMlayer : IsLayerMember3 c M)
    (nd : DNodes3 6 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β)
    {N : Subgroup G} (hNΩ : N ∈ Ω) (hNc : ∀ a : Fin 6, a.val < 3 → Commutes N (nd.J a))
    (hN4 : ¬ Commutes N (nd.J ⟨4, by omega⟩)) (hN5 : ¬ Commutes N (nd.J ⟨5, by omega⟩)) :
    ∃ (Rz : ℕ → Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
      (RzM : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
      (RN : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
      (x : spinGroup (quadPlus 6 (GaloisField 3 1))) (tM : Bool)
      (α : spinGroup (quadPlus 6 (GaloisField 3 1)) ≃* spinGroup (quadPlus 6 (GaloisField 3 1)))
      (g₀ : (Fin 6 ⊕ Fin 6 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
        (Fin 6 ⊕ Fin 6 → GaloisField 3 1)),
      (∀ a (h : a < 6), 2 ≤ a →
        Rz a ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = (Rz a).map c.d.ψ) ∧
      (RzM ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D ∧
        locImg Ω z M = RzM.map c.d.ψ) ∧
      (RN ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D ∧
        locImg Ω z N = RN.map c.d.ψ) ∧
      (∀ a (ha : a ≤ 2), Rz (a + 2) = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) a
        (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      RzM = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 4 5 (by omega) (by omega)
        (by omega) true tM).map (MulAut.conj x).toMonoidHom) ∧
      (∀ y, c.d.ψ (α y) = locAut c.hΩ.conjInvariant htz (c.d.ψ y)) ∧
      g₀ ∈ TauCeti.QuadraticMap.orthogonalGroup (quadPlus 6 (GaloisField 3 1)) ∧ g₀ * g₀ = 1 ∧
      (∀ y v, spinAction (quadPlus 6 (GaloisField 3 1)) (α y) (g₀ v) =
        g₀ (spinAction (quadPlus 6 (GaloisField 3 1)) y v)) ∧
      (∀ a : Fin 6, 1 ≤ a.val → a.val ≤ 3 → ∀ s,
        g₀ (spinAction (quadPlus 6 (GaloisField 3 1)) x
          ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec a s)) =
        spinAction (quadPlus 6 (GaloisField 3 1)) x
          ((plusFrame 6 (GaloisField 3 1) (by norm_num)).vec a s)) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hadm : StatedLieAdmissible .POmegaPlus 6 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ 6; omega⟩
  have : Finite (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K :=
    CFSG.ClassicalInvolution.ModelFacts.finite_modelUniv (by norm_num) Nat.prime_three trivial hadm
  have hKJ : ∀ a (h : a < 6), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne3 (by d6_idx)) (by d6_idx)
  have hmemz : ∀ a (h : a < 6), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 6), 2 ≤ a →
      ∃ b, ∃ hb : b < 6, 2 ≤ b ∧ DNodes3.Adj (⟨a, h⟩ : Fin 6) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h3 : a = 3
    · exact ⟨4, by omega, by omega, by subst h3; d6_idx⟩
    · exact ⟨3, by omega, by omega, by d6_idx⟩
  have hlayer : ∀ a (h : a < 6), 2 ≤ a → IsLayerMember3 c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember3.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K,
      ∀ (h : a < 6), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 6 ∧ 2 ≤ a
    · obtain ⟨R, hR, hLR⟩ := (hlayer a hv.1 hv.2).exists_fund
      exact ⟨R, fun _ _ => ⟨hR, hLR⟩⟩
    · exact ⟨⊥, fun h ha => absurd ⟨h, ha⟩ hv⟩
  choose Rz hRz using hexRz
  have hMK : Commutes M K := by
    rw [← h0]
    exact nd.commK _
  have hMz : M ∈ centralizingMembers Ω {z} :=
    mem_centralizingMembers_of_commutes hMΩ c.hz.mem hMK
  obtain ⟨RzM, hRzM, hMR⟩ := hMlayer.exists_fund
  have hNz : N ∈ centralizingMembers Ω {z} := by
    have := hNc ⟨0, by omega⟩ (by norm_num)
    rw [h0] at this
    exact mem_centralizingMembers_of_commutes hNΩ c.hz.mem this
  have hn45 : Commutes (nd.J ⟨4, by omega⟩) (nd.J ⟨5, by omega⟩) :=
    nd.commutes_of_not_adj (fin_ne_of_val_ne3 (by d6_idx)) (by d6_idx)
  have hN4ne : N ≠ nd.J ⟨4, by omega⟩ := fun h => hN5 (h ▸ hn45)
  have hNlayer : IsLayerMember3 c N :=
    IsLayerMember3.of_not_commutes c hNz (hmemz 4 (by omega) (by omega)) hN4ne hN4
  obtain ⟨RN, hRN, hNR⟩ := hNlayer.exists_fund
  have hcommz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    c.modelAdj_of_adj3 (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w _ _) (nd.conjSub_w hab)
  have hlinz : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact c.lift_lin (hRz a ha ha2).1 (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 6), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 6), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (fin_ne_of_val_ne3 (by d6_idx)) (by d6_idx)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map
      (locAut hΩ.conjInvariant htz).toMonoidHom = locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by d6_idx)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadPlus 6 (GaloisField 3 1)) →* locQuot Ω z := c.d.ψ
  let σ := locAut hΩ.conjInvariant htz
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := fun k' =>
    c.locAut_mem_range htz h2t hKt
      (range_le_iSup_fund_plus (p := 3) (f := 1) (by omega) hadm c.d.ψ) k'
  let R : ℕ → Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1))) := fun a => Rz (a + 2)
  let Rtw : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1))) := Rz 5
  let RM : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1))) := RzM
  have hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)) := fun a ha =>
    (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)) := (hRz 5 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)) := hRzM
  have hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)) := fun a ha =>
    hadjz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by d6_idx)
  have hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)) :=
    fun a ha => hlinz (a + 2) (by omega) (a + 3) (by omega) (by omega) (by omega) (by d6_idx)
  have hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b) := fun a b hab hb =>
    hcommz (a + 2) (by omega) (b + 2) (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (fin_ne_of_val_ne3 (by d6_idx)) (by d6_idx))
  have hM : ∀ a ≤ 2, Commutes RM (R a) := fun a ha => hMcomm (a + 2) (by omega) (by omega)
  have hne : Rtw ≠ R 2 := by
    intro h
    have h' : Rz 5 = Rz (2 + 2) := h
    have h2' : nd.J ⟨5, by omega⟩ = nd.J ⟨2 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 5 (by omega) (by omega)).2, (hRz (2 + 2) (by omega) (by omega)).2, h'])
    exact nd.ne_J (fin_ne_of_val_ne3 (by simp)) h2'
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
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have cq := centralQuot3_plus (m := 6) (by norm_num : 4 ≤ 6)
  have hdimV : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus3]
    omega
  have hstar : ∃ i₁ i₂ i₃, IsFundamental (quadPlus 6 (GaloisField 3 1))
      ((Rz 2).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i₁ ∧
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        ((Rz 4).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i₂ ∧
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        ((Rz 5).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i₃ ∧
      i₂ ≠ i₁ ∧ i₃ ≠ i₁ ∧ i₃ = i₂ := by
    obtain ⟨ic, hic⟩ := cq.map_mem _ (hRz 3 (by omega) (by omega)).1
    obtain ⟨i₁, hi₁⟩ := cq.map_mem _ (hRz 2 (by omega) (by omega)).1
    obtain ⟨i₂, hi₂⟩ := cq.map_mem _ (hRz 4 (by omega) (by omega)).1
    obtain ⟨i₃, hi₃⟩ := cq.map_mem _ (hRz 5 (by omega) (by omega)).1
    obtain ⟨iS, hiS⟩ := cq.map_mem _ hRN
    have hRf' : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), Rz a ∈ fundamentalSubgroups .POmegaPlus
        (plusDatum 6 (GaloisField 3 1) (by norm_num)) := fun a ha ha2 => (hRz a ha ha2).1
    have cm : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
        a ≠ b → ¬ DNodes3.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        Commutes ((Rz a).map (spinAction (quadPlus 6 (GaloisField 3 1))))
          ((Rz b).map (spinAction (quadPlus 6 (GaloisField 3 1)))) :=
      fun a ha b hb ha2 hb2 hab hn =>
      (cq.commutes_iff (hRf' a ha ha2)).mpr (hcommz a ha b hb ha2 hb2
        (nd.commutes_of_not_adj (fin_ne_of_val_ne3 hab) hn))
    have ad : ∀ a (ha : a < 6) b (hb : b < 6) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
        DNodes3.Adj (⟨a, ha⟩ : Fin 6) ⟨b, hb⟩ →
        ModelAdj (scalars (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1))
          ((Rz a).map (spinAction (quadPlus 6 (GaloisField 3 1))))
          ((Rz b).map (spinAction (quadPlus 6 (GaloisField 3 1)))) := fun a ha b hb ha2 hb2 hab =>
      cq.modelAdj (hRf' a ha ha2) (hRf' b hb hb2) (hadjz a ha b hb ha2 hb2 hab)
    have hNne : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), N ≠ nd.J ⟨a, ha⟩ →
        (RN.map (spinAction (quadPlus 6 (GaloisField 3 1)))) ≠
          ((Rz a).map (spinAction (quadPlus 6 (GaloisField 3 1)))) := fun a ha ha2 hne e =>
      hne (c.eq_of_locImg_eq hNz (hmemz a ha ha2) (by
        rw [hNR, (hRz a ha ha2).2, cq.map_inj hRN (hRf' a ha ha2) e]))
    have hnc : ∀ a (ha : a < 6) (ha2 : 2 ≤ a), (hcn : ¬ Commutes N (nd.J ⟨a, ha⟩)) →
        ¬ Commutes (RN.map (spinAction (quadPlus 6 (GaloisField 3 1))))
          ((Rz a).map (spinAction (quadPlus 6 (GaloisField 3 1)))) := fun a ha ha2 hcn h =>
      hcn ((c.commutes_iff_fund hNz (hmemz a ha ha2) hRN hNR (hRz a ha ha2).2).mpr
        ((cq.commutes_iff hRN).mp h))
    have hcN2 : Commutes (RN.map (spinAction (quadPlus 6 (GaloisField 3 1))))
        ((Rz 2).map (spinAction (quadPlus 6 (GaloisField 3 1)))) :=
      (cq.commutes_iff hRN).mpr ((c.commutes_iff_fund hNz (hmemz 2 (by omega) (by omega)) hRN hNR
        (hRz 2 (by omega) (by omega)).2).mp (hNc ⟨2, by omega⟩ (by norm_num)))
    have hN2ne : N ≠ nd.J ⟨2, by omega⟩ := fun h => by
      obtain ⟨wN, hwN⟩ := hΩ.classical N hNΩ
      exact not_commutes_self3 hwN (h ▸ hNc ⟨2, by omega⟩ (by norm_num))
    have hN5ne : N ≠ nd.J ⟨5, by omega⟩ := fun h => hN4 (h ▸ commutes_symm hn45)
    refine ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, ?_⟩
    exact star_twin_of_distinguish' hodd hdimV hic hi₁ hi₂ hi₃ hiS
      (ad 3 (by omega) 2 (by omega) (by omega) (by omega) (by d6_idx))
      (ad 3 (by omega) 4 (by omega) (by omega) (by omega) (by d6_idx))
      (ad 3 (by omega) 5 (by omega) (by omega) (by omega) (by d6_idx))
      (cm 2 (by omega) 4 (by omega) (by omega) (by omega) (by omega) (by d6_idx))
      (cm 2 (by omega) 5 (by omega) (by omega) (by omega) (by omega) (by d6_idx))
      (cm 4 (by omega) 5 (by omega) (by omega) (by omega) (by omega) (by d6_idx))
      (hNne 2 (by omega) (by omega) hN2ne) (hNne 4 (by omega) (by omega) hN4ne)
      (hNne 5 (by omega) (by omega) hN5ne) hcN2
      (hnc 4 (by omega) (by omega) hN4) (hnc 5 (by omega) (by omega) hN5)
  obtain ⟨i₁, i₂, i₃, hi₁, hi₂, hi₃, hn21, hn31, h32⟩ := hstar
  have hdist : ∀ i j, IsFundamental (quadPlus 6 (GaloisField 3 1))
      ((R 0).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i →
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        ((R 2).map (spinAction (quadPlus 6 (GaloisField 3 1)))) j → i ≠ j := fun i j hi hj => by
    have e1 := IsFundamental.involution_unique hodd hi hi₁
    have e2 := IsFundamental.involution_unique hodd hj hi₂
    rw [e1, e2]
    exact hn21.symm
  have htwin : ∀ i j, IsFundamental (quadPlus 6 (GaloisField 3 1))
      ((R 2).map (spinAction (quadPlus 6 (GaloisField 3 1)))) i →
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        (Rtw.map (spinAction (quadPlus 6 (GaloisField 3 1)))) j → i = j := fun i j hi hj => by
    have e1 := IsFundamental.involution_unique hodd hi hi₂
    have e2 := IsFundamental.involution_unique hodd hj hi₃
    rw [e1, e2, h32]
  obtain ⟨x, tM, α, g₀, hxR, hxtw, hxM, hαθ, hg₀O, hg₀2, hconj, hfixv⟩ := toral_lift_plus_six3
    θ c.d.ker_le σ hσ2 hσr hRf hRtwf hRMf hadj hlin hcomm hM hdist hne htwin hfix hfixtw
    hfixM hnorm0
  exact ⟨Rz, RzM, RN, x, tM, α, g₀, fun a h ha => hRz a h ha, ⟨hRzM, hMR⟩, ⟨hRN, hNR⟩, hxR, hxM,
    hαθ, hg₀O, hg₀2, hconj, hfixv⟩

end Group

end CFSG.ClassicalInvolution.Q3.Q3TD
