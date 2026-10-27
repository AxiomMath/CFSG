module

public import CFSG.ClassicalInvolution.Q3.Q3TD3Pat
public import CFSG.ClassicalInvolution.Q3.Q3TD3Pairs
public import CFSG.ClassicalInvolution.RouteD.GapsFrFive

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TD

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TY CFSG.LieType.Universal
  CFSG.LieType CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin CFSG.LieType.CurtisTits
  CFSG.Timmesfeld CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups


local macro "fr_idx5" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (simp; done)
    | (simp; omega)
    | omega)

local macro "idx_tac5" : tactic =>
  `(tactic| first
    | (simp [DNodes3.adj_def]; done)
    | (simp [DNodes3.adj_def]; omega)
    | (apply Gaps.fin_ne_of_val_ne; simp only; omega)
    | (left; apply Fin.ext; simp only; omega)
    | (right; apply Fin.ext; simp only; omega))

section Five

theorem chain_twin_five3
    {R0 R1 Rtw RM : Subgroup (spinGroup (quadPlus 5 (GaloisField 3 1)))}
    (hR0 : R0 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hR1 : R1 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hRtw : Rtw ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hRM : RM ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hadj1 : ModelAdj (Subgroup.center _) R0 R1) (hadj2 : ModelAdj (Subgroup.center _) R0 Rtw)
    (hc12 : Commutes R1 Rtw) (hM0 : Commutes RM R0) (hM1 : Commutes RM R1)
    (hM2 : Commutes RM Rtw) :
    ∀ i j, IsFundamental (quadPlus 5 (GaloisField 3 1))
        (R1.map (spinAction (quadPlus 5 (GaloisField 3 1)))) i →
      IsFundamental (quadPlus 5 (GaloisField 3 1))
        (Rtw.map (spinAction (quadPlus 5 (GaloisField 3 1)))) j → i = j := by
  classical
  have hm3 : 3 ≤ 5 := by omega
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hfr : Module.finrank (GaloisField 3 1) (Fin 5 ⊕ Fin 5 → GaloisField 3 1) = 10 := by
    rw [finrank_plus]
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 5 ⊕ Fin 5 → GaloisField 3 1) := by
    omega
  have cq := centralQuot3_plus (by omega : 4 ≤ 5)
  obtain ⟨i0, hi0⟩ := cq.map_mem _ hR0
  obtain ⟨i1, hi1⟩ := cq.map_mem _ hR1
  obtain ⟨i2, hi2⟩ := cq.map_mem _ hRtw
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRM
  intro i j hi hj
  have e1 : i1 = i := IsFundamental.involution_unique hodd hi1 hi
  have e2 : i2 = j := IsFundamental.involution_unique hodd hi2 hj
  rw [← e1, ← e2]
  by_contra hne
  have hadj1V := cq.modelAdj hR0 hR1 hadj1
  have hadj2V := cq.modelAdj hR0 hRtw hadj2
  have c12 : Commutes (R1.map (spinAction (quadPlus 5 (GaloisField 3 1))))
      (Rtw.map (spinAction (quadPlus 5 (GaloisField 3 1)))) := (cq.commutes_iff hR1).mpr hc12
  have cM0 : Commutes (RM.map (spinAction (quadPlus 5 (GaloisField 3 1))))
      (R0.map (spinAction (quadPlus 5 (GaloisField 3 1)))) := (cq.commutes_iff hRM).mpr hM0
  have cM1 : Commutes (R1.map (spinAction (quadPlus 5 (GaloisField 3 1))))
      (RM.map (spinAction (quadPlus 5 (GaloisField 3 1)))) :=
    (cq.commutes_iff hR1).mpr (commutes_symm hM1)
  have cM2 : Commutes (Rtw.map (spinAction (quadPlus 5 (GaloisField 3 1))))
      (RM.map (spinAction (quadPlus 5 (GaloisField 3 1)))) :=
    (cq.commutes_iff hRtw).mpr (commutes_symm hM2)
  have o12 : ∀ x ∈ negSpace i1, ∀ y ∈ negSpace i2,
      polar (quadPlus 5 (GaloisField 3 1)) x y = 0 := by
    rcases orth_or_twin hodd hi1 hi2 c12 with h | h
    · exact h
    · exact absurd h.symm hne
  have oM : ∀ {L : Subgroup ((Fin 5 ⊕ Fin 5 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
        (Fin 5 ⊕ Fin 5 → GaloisField 3 1))}
      {il : (Fin 5 ⊕ Fin 5 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
        (Fin 5 ⊕ Fin 5 → GaloisField 3 1)},
      IsFundamental (quadPlus 5 (GaloisField 3 1)) L il →
      ModelAdj (scalars (GaloisField 3 1) (Fin 5 ⊕ Fin 5 → GaloisField 3 1))
        (R0.map (spinAction (quadPlus 5 (GaloisField 3 1)))) L →
      Commutes L (RM.map (spinAction (quadPlus 5 (GaloisField 3 1)))) →
      ∀ x ∈ negSpace il, ∀ y ∈ negSpace iM, polar (quadPlus 5 (GaloisField 3 1)) x y = 0 := by
    intro L il hl hadj hcomm
    rcases orth_or_twin hodd hl hiM hcomm with h | h
    · exact h
    · exfalso
      obtain ⟨-, -, C⟩ := adj_data hodd hdim hi0 hl hadj
      apply C
      rw [← h]
      exact Subgroup.mem_centralizer_iff.mpr fun g hg => (cM0 iM hiM.mem g hg).symm
  exact not_three_orth_fours (Q := quadPlus 5 (GaloisField 3 1)) (U₁ := negSpace i1)
    (U₂ := negSpace i2) (U₃ := negSpace iM) (by omega) (finrank_negSpace hodd hi1)
    (finrank_negSpace hodd hi2) (finrank_negSpace hodd hiM) (polarNondegOn_negSpace hodd hi1)
    (polarNondegOn_negSpace hodd hiM) o12 (oM hi1 hadj1V cM1) (oM hi2 hadj2V cM2)


theorem toralNormal_of_chain3 {s : ℕ} (hs : 1 ≤ s) {X : Type}
    [Group X] (θ : spinGroup (quadPlus (s + 4) (GaloisField 3 1)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus (s + 4) (GaloisField 3 1))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus (s + 4) (GaloisField 3 1)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus (s + 4) (GaloisField 3 1)))}
    (hRf : ∀ a ≤ s, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField 3 1) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField 3 1) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField 3 1) (by omega)))
    (hadj : ∀ a < s, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < s, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ s → Commutes (R a) (R b))
    (hM : ∀ a ≤ s, Commutes RM (R a))
    (hdist : ∀ a b, a + 1 < b → b ≤ s → ∀ i j,
      IsFundamental (quadPlus (s + 4) (GaloisField 3 1))
        ((R a).map (spinAction (quadPlus (s + 4) (GaloisField 3 1)))) i →
      IsFundamental (quadPlus (s + 4) (GaloisField 3 1))
        ((R b).map (spinAction (quadPlus (s + 4) (GaloisField 3 1)))) j → i ≠ j)
    (hne : Rtw ≠ R s)
    (htwin : ∀ i j, IsFundamental (quadPlus (s + 4) (GaloisField 3 1))
        ((R s).map (spinAction (quadPlus (s + 4) (GaloisField 3 1)))) i →
      IsFundamental (quadPlus (s + 4) (GaloisField 3 1))
        (Rtw.map (spinAction (quadPlus (s + 4) (GaloisField 3 1)))) j → i = j)
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadPlus (s + 4) (GaloisField 3 1))) (v : Fin (s + 4) → ZMod 2),
      ∀ γ : Fin (s + 4) → ℤ, γ ∈ (plusDatum (s + 4) (GaloisField 3 1) (by omega)).roots →
        ((((plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) := by
  have hm3 : 3 ≤ s + 4 := by omega
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero two_ne_zero_gf3
  have hQ : (quadPlus (s + 4) (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadPlus (s + 4) (GaloisField 3 1))
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (s + 4) ⊕ Fin (s + 4) → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have cq := centralQuot3_plus (m := s + 4) (by omega)
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen3 hQ (s := s) hs
    (plusFrame (s + 4) (GaloisField 3 1) hm3) hdim cq hRf hRtwf hRMf hadj hlin hcomm hM hdist hne
    htwin
  exact toralNormal_of_frame_chain3 hs θ hker σ hσ2 hσr x t hxR hxtw hxM hfix hfixtw hfixM hnorm0

theorem toralNormal_of_chain_five3 {X : Type} [Group X]
    (θ : spinGroup (quadPlus 5 (GaloisField 3 1)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus 5 (GaloisField 3 1))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus 5 (GaloisField 3 1)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus 5 (GaloisField 3 1)))}
    (hRf : ∀ a ≤ 1, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus (plusDatum 5 (GaloisField 3 1) (by omega)))
    (hadj : ModelAdj (Subgroup.center _) (R 0) (R 1))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R 0) (R 1))
    (hM : ∀ a ≤ 1, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R 0) Rtw) (hcommtw : Commutes (R 1) Rtw)
    (hMtw : Commutes RM Rtw) (hne : Rtw ≠ R 1)
    (hfix : ∀ y ∈ R 1, σ (θ y) = θ y) (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y)
    (hfixM : ∀ y ∈ RM, σ (θ y) = θ y) (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadPlus 5 (GaloisField 3 1))) (v : Fin 5 → ZMod 2),
      ∀ γ : Fin 5 → ℤ, γ ∈ (plusDatum 5 (GaloisField 3 1) (by omega)).roots →
        ((((plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup γ ⊔
              (plusDatum 5 (GaloisField 3 1) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) :=
  toralNormal_of_chain3 (s := 1) (by omega) θ hker σ hσ2 hσr hRf hRtwf hRMf
    (fun a ha => by
      obtain rfl : a = 0 := by omega
      exact hadj)
    (fun a ha => by
      obtain rfl : a = 0 := by omega
      exact hlin)
    (fun a b hab hb => absurd hb (by omega)) hM
    (fun a b hab hb => absurd hb (by omega)) hne
    (chain_twin_five3 (hRf 0 (by omega)) (hRf 1 le_rfl) hRtwf hRMf hadj hadjtw hcommtw
      (hM 0 (by omega)) (hM 1 le_rfl) hMtw)
    (fun a ha1 ha2 => by
      obtain rfl : a = 1 := by omega
      exact hfix)
    hfixtw hfixM hnorm0

theorem toralNormalD3_of_nodes_five {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}
    {K : Subgroup G} {z : G} (c : TCtx3 .POmegaPlus 5 Ω K z) {β : Subgroup G} {t : G}
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β) {M : Subgroup G} (hMΩ : M ∈ Ω)
    (hMN : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N)
    (nd : DNodes3 5 Ω M) (h0 : nd.J ⟨0, by omega⟩ = K) (h1 : nd.J ⟨1, by omega⟩ = β) :
    ToralNormalD3 c (partner_involution_commutes_z3 c.hz ht hKβ) := by
  classical
  have hm3 : 3 ≤ 5 := by omega
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have htz := partner_involution_commutes_z3 c.hz ht hKβ
  have h2t : t * t = 1 := by
    have := pow_orderOf_eq_one t
    rwa [ht.orderOf_eq_two, pow_two] at this
  obtain ⟨W, hW⟩ := hKβ
  have hKt : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hF := orthFacts3_plus (le_refl 5)
  obtain ⟨e, ι, hcι⟩ := exists_isoCompatPlus (p := 3) (f := 1) hm3
  have hadm : StatedLieAdmissible .POmegaPlus 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ 5; omega⟩
  have hKJ : ∀ a (h : a < 5), 2 ≤ a → Commutes K (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h0]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx5)) (by fr_idx5)
  have hmemz : ∀ a (h : a < 5), 2 ≤ a → nd.J ⟨a, h⟩ ∈ centralizingMembers Ω {z} :=
    fun a h ha => mem_centralizingMembers_of_commutes (nd.mem _) c.hz.mem
      (commutes_symm (hKJ a h ha))
  have hnb : ∀ a (h : a < 5), 2 ≤ a →
      ∃ b, ∃ hb : b < 5, 2 ≤ b ∧ DNodes3.Adj (⟨a, h⟩ : Fin 5) ⟨b, hb⟩ := by
    intro a h ha
    by_cases h1 : a = 2
    · exact ⟨3, by omega, by omega, by fr_idx5⟩
    · exact ⟨2, by omega, by omega, by fr_idx5⟩
  have hlayer : ∀ a (h : a < 5), 2 ≤ a → IsLayerMember3 c (nd.J ⟨a, h⟩) := by
    intro a h ha
    obtain ⟨b, hb, hb2, hab⟩ := hnb a h ha
    exact IsLayerMember3.of_not_commutes c (hmemz a h ha) (hmemz b hb hb2)
      (nd.ne_J hab.ne) (nd.not_commutes_of_adj hab)
  have hexRz : ∀ a : ℕ, ∃ R : Subgroup (modelUniv .POmegaPlus 5 3 1 Nat.prime_three).K,
      ∀ (h : a < 5), 2 ≤ a →
        R ∈ fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 5 3 1 Nat.prime_three).D ∧
          locImg Ω z (nd.J ⟨a, h⟩) = R.map c.d.ψ := by
    intro a
    by_cases hv : a < 5 ∧ 2 ≤ a
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
  have hcommz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      Commutes (nd.J ⟨a, ha⟩) (nd.J ⟨b, hb⟩) → Commutes (Rz a) (Rz b) :=
    fun a ha b hb ha2 hb2 h => (c.commutes_iff_fund (hmemz a ha ha2) (hmemz b hb hb2)
      (hRz a ha ha2).1 (hRz a ha ha2).2 (hRz b hb hb2).2).mp h
  have hMcomm : ∀ a (ha : a < 5) (ha2 : 2 ≤ a), Commutes RzM (Rz a) :=
    fun a ha ha2 => (c.commutes_iff_fund hMz (hmemz a ha ha2) hRzM hMR (hRz a ha ha2).2).mp
      (nd.commK _)
  have hadjz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin 5) ⟨b, hb⟩ →
        ModelAdj (Subgroup.center (modelUniv .POmegaPlus 5 3 1 Nat.prime_three).K)
          (Rz a) (Rz b) := fun a ha b hb ha2 hb2 hab =>
    c.modelAdj_of_adj3 (hmemz a ha ha2) (hmemz b hb hb2) (hRz a ha ha2).1 (hRz b hb hb2).1
      (hRz a ha ha2).2 (hRz b hb hb2).2 (nd.cl _) (nd.cl _) (nd.ne_J hab.ne)
      (nd.not_commutes_of_adj hab) (nd.commute_w _ _) (nd.conjSub_w hab)
  have hlinz : ∀ a (ha : a < 5) b (hb : b < 5) (ha2 : 2 ≤ a) (hb2 : 2 ≤ b),
      DNodes3.Adj (⟨a, ha⟩ : Fin 5) ⟨b, hb⟩ →
        ∃ W₁, LinearBlockStandardPair (GaloisField 3 1) W₁ (Rz a) (Rz b) := by
    intro a ha b hb ha2 hb2 hab
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj hab
    obtain ⟨W₂, hW₂⟩ := linearBlockStandardPair_locImg_of_members c.hP1 (hmemz a ha ha2)
      (hmemz b hb hb2) hW₁
    rw [(hRz a ha ha2).2, (hRz b hb hb2).2] at hW₂
    exact hF.lift c.d.ψ c.d.ker_le _ (hRz a ha ha2).1 _ (hRz b hb hb2).1 ⟨W₂, hW₂⟩
  have hfixnode : ∀ a (h : a < 5), 2 ≤ a → Commutes β (nd.J ⟨a, h⟩) →
      ∀ x ∈ locImg Ω z (nd.J ⟨a, h⟩), locAut hΩ.conjInvariant htz x = x := fun a h ha hc =>
    (locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz (hmemz a h ha)).mp fun n hn =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hc t ht.mem n hn).symm
  have hβJ : ∀ a (h : a < 5), 3 ≤ a → Commutes β (nd.J ⟨a, h⟩) := by
    intro a h ha
    rw [← h1]
    exact nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx5)) (by fr_idx5)
  have hMβ : Commutes β M := by
    rw [← h1]
    exact commutes_symm (nd.commK _)
  have hstab2 : (locImg Ω z (nd.J ⟨2, by omega⟩)).map (locAut hΩ.conjInvariant htz).toMonoidHom =
      locImg Ω z (nd.J ⟨2, by omega⟩) := by
    rw [locAut_locImg hΩ.conjInvariant htz]
    congr 1
    obtain ⟨W₁, hW₁⟩ := nd.pair_of_adj (a := ⟨2, by omega⟩) (b := ⟨1, by omega⟩) (by fr_idx5)
    rw [h1] at hW₁
    exact conjSub_eq_of_standardPair h2 hW₁ ht.mem ht.orderOf_eq_two
  let θ : spinGroup (quadPlus 5 (GaloisField 3 1)) →* locQuot Ω z := c.d.ψ.comp ι.toMonoidHom
  let σ := locAut hΩ.conjInvariant htz
  have hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus 5 (GaloisField 3 1))) := by
    intro y hy
    have h1 : ι y ∈ c.d.ψ.ker := hy
    exact (MulEquivClass.apply_mem_center_iff ι).mp (c.d.ker_le h1)
  have hσ2 : ∀ y, σ (σ y) = y := locAut_locAut hΩ.conjInvariant htz h2t
  have hσr : ∀ k', σ (θ k') ∈ θ.range := by
    intro k'
    obtain ⟨x, hx⟩ := c.locAut_mem_range htz h2t hKt
      (range_le_iSup_fund_plus (p := 3) (f := 1) (by omega) hadm c.d.ψ) (ι k')
    exact ⟨ι.symm x, by simpa [θ] using hx⟩
  let R : ℕ → Subgroup (spinGroup (quadPlus 5 (GaloisField 3 1))) := fun a =>
    (Rz (a + 2)).map ι.symm.toMonoidHom
  let Rtw : Subgroup (spinGroup (quadPlus 5 (GaloisField 3 1))) :=
    (Rz 4).map ι.symm.toMonoidHom
  let RM : Subgroup (spinGroup (quadPlus 5 (GaloisField 3 1))) :=
    RzM.map ι.symm.toMonoidHom
  have hRf : ∀ a ≤ 1, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField 3 1) (by omega)) := fun a ha =>
    map_symm_mem_fund_iso hm3 hcι (hRz (a + 2) (by omega) (by omega)).1
  have hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField 3 1) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι (hRz 4 (by omega) (by omega)).1
  have hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 5 (GaloisField 3 1) (by omega)) :=
    map_symm_mem_fund_iso hm3 hcι hRzM
  have hadj : ModelAdj (Subgroup.center _) (R 0) (R 1) :=
    ModelAdj.map_equiv ι.symm (hadjz 2 (by omega) 3 (by omega) (by omega) (by omega) (by fr_idx5))
  have hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R 0) (R 1) := by
    obtain ⟨W₁, hW₁⟩ := hlinz 2 (by omega) 3 (by omega) (by omega) (by omega) (by fr_idx5)
    exact ⟨_, linearBlockStandardPair_map_equiv ι.symm hW₁⟩
  have hM : ∀ a ≤ 1, Commutes RM (R a) := fun a ha =>
    (commutes_map_equiv ι.symm).mpr (hMcomm (a + 2) (by omega) (by omega))
  have hadjtw : ModelAdj (Subgroup.center _) (R 0) Rtw :=
    ModelAdj.map_equiv ι.symm (hadjz 2 (by omega) 4 (by omega) (by omega) (by omega) (by fr_idx5))
  have hcommtw : Commutes (R 1) Rtw :=
    (commutes_map_equiv ι.symm).mpr (hcommz 3 (by omega) 4 (by omega) (by omega) (by omega)
      (nd.commutes_of_not_adj (Gaps.fin_ne_of_val_ne (by fr_idx5)) (by fr_idx5)))
  have hMtw : Commutes RM Rtw :=
    (commutes_map_equiv ι.symm).mpr (hMcomm 4 (by omega) (by omega))
  have hne : Rtw ≠ R 1 := by
    intro h
    have h1' : Rz 4 = Rz (1 + 2) := Subgroup.map_injective ι.symm.injective h
    have h2' : nd.J ⟨4, by omega⟩ = nd.J ⟨1 + 2, by omega⟩ :=
      c.eq_of_locImg_eq (hmemz _ _ (by omega)) (hmemz _ _ (by omega))
        (by rw [(hRz 4 (by omega) (by omega)).2, (hRz (1 + 2) (by omega) (by omega)).2, h1'])
    exact nd.ne_J (Gaps.fin_ne_of_val_ne (by fr_idx5)) h2'
  have hfix : ∀ y ∈ R 1, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ (hRz (1 + 2) (by omega) (by omega)).2
      (hfixnode (1 + 2) (by omega) (by omega) (hβJ (1 + 2) (by omega) (by omega)))
  have hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ (hRz 4 (by omega) (by omega)).2
      (hfixnode 4 (by omega) (by omega) (hβJ 4 (by omega) (by omega)))
  have hfixM : ∀ y ∈ RM, σ (θ y) = θ y :=
    fixed_of_map_symm ι c.d.ψ σ hMR
      ((locAut_fixed_iff3 hΩ c.hex c.hP1 c.hO3 htz hMz).mp fun n hn =>
        Subgroup.mem_centralizer_singleton_iff.mpr (hMβ t ht.mem n hn).symm)
  have hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ := fun y hy =>
    norm_of_map_symm ι c.d.ψ σ (hRz (0 + 2) (by omega) (by omega)).2 hstab2 y hy
  obtain ⟨k₀, v, hk₀⟩ := toralNormal_of_chain_five3 θ hker σ hσ2 hσr hRf hRtwf hRMf hadj
    hlin hM hadjtw hcommtw hMtw hne hfix hfixtw hfixM hnorm0
  exact toralNormalD3_of_toral hm3 c htz hcι ⟨k₀, v, hk₀⟩


end Five

section Adapted

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem adapted_pattern_D53
    (hF : OrthFacts
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 5 3 1 Nat.prime_three).D)
      (GaloisField 3 1))
    (c : TCtx3 .POmegaPlus 5 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K)
    (nd : DNodes3 5 Ω K)
    {β : Subgroup G} {t : G} (hβ : β ∈ Ω) (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    {pp : Fin 5} (hfix : ∀ a, a ≠ pp → Commutes β (nd.J a))
    (hmov : ¬ Commutes β (nd.J pp)) (hnorm : conjSub t (nd.J pp) = nd.J pp) :
    pp.val = 0 ∧ ∃ W : Subgroup G, LinearBlockStandardPair (GaloisField 3 1) W β (nd.J pp) := by
  classical
  have hΩ := c.hΩ
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  obtain ⟨W, hW⟩ := hKβ
  have hnKβ : ¬ Commutes K β := not_commutes_of_linearBlockStandardPair hW
  have hKne : K ≠ β := ne_of_linearBlockStandardPair hW
  have hzt : Commute z t :=
    standardPair_involutions_commute h2 hW c.hz.mem ht.mem c.hz.orderOf_eq_two ht.orderOf_eq_two
  have hnormK : conjSub t K = K := conjSub_eq_of_standardPair h2 hW ht.mem ht.orderOf_eq_two
  have hβJ : ∀ a, β ≠ nd.J a := fun a h => by
    have := nd.commK a
    rw [← h] at this
    exact hnKβ this
  have hsymm : Commute (nd.w pp) t :=
    (commute_of_conjSub_eq3 (nd.cl pp) hnorm).symm
  have hp0 : pp.val = 0 := by
    by_contra hne
    have hpv := pp.isLt
    obtain ⟨pv, hpv'⟩ := pp
    simp only at hne hpv
    interval_cases pv
    · exact hne rfl
    ·
      obtain ⟨cx⟩ := c.exists_ctx_member hsingle (nd.mem ⟨0, by omega⟩)
        (nd.cl ⟨0, by omega⟩)
      refine absurd (pair_config3 cx (pairBound_plus3 (by norm_num))
        (nd.mem_loc ⟨0, by omega⟩ c.hK (nd.commK _))
        (nd.mem_loc ⟨0, by omega⟩ hβ (hfix _ (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨2, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨3, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        c.hz ht (nd.cl _) (nd.cl _) hKne hnKβ hzt hnormK
        (nd.ne_J (by idx_tac5)) (nd.not_commutes_of_adj (by idx_tac5)) (nd.commute_w _ _)
        (nd.conjSub_w (by idx_tac5)) (nd.commK _) (nd.commK _) (hfix _ (by idx_tac5))
        (hfix _ (by idx_tac5))) (by norm_num)
    ·
      obtain ⟨cx⟩ := c.exists_ctx_member hsingle (nd.mem ⟨3, by omega⟩)
        (nd.cl ⟨3, by omega⟩)
      refine absurd (pair_config3 cx (pairBound_plus3 (by norm_num))
        (nd.mem_loc ⟨3, by omega⟩ c.hK (nd.commK _))
        (nd.mem_loc ⟨3, by omega⟩ hβ (hfix _ (by idx_tac5)))
        (nd.mem_loc ⟨3, by omega⟩ (nd.mem ⟨0, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨3, by omega⟩ (nd.mem ⟨1, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        c.hz ht (nd.cl _) (nd.cl _) hKne hnKβ hzt hnormK
        (nd.ne_J (by idx_tac5)) (nd.not_commutes_of_adj (by idx_tac5)) (nd.commute_w _ _)
        (nd.conjSub_w (by idx_tac5)) (nd.commK _) (nd.commK _) (hfix _ (by idx_tac5))
        (hfix _ (by idx_tac5))) (by norm_num)
    ·
      obtain ⟨cx⟩ := c.exists_ctx_member hsingle (nd.mem ⟨0, by omega⟩)
        (nd.cl ⟨0, by omega⟩)
      exact chain5_false3 cx (chainBound0_plus3 (by norm_num)) (by norm_num)
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨4, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨2, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨3, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ hβ (hfix _ (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ c.hK (nd.commK _))
        (nd.cl _) (nd.cl _) (nd.cl _) ht c.hz
        ⟨nd.ne_J (by idx_tac5), nd.not_commutes_of_adj (by idx_tac5), nd.commute_w _ _,
          nd.conjSub_w (by idx_tac5)⟩
        ⟨nd.ne_J (by idx_tac5), nd.not_commutes_of_adj (by idx_tac5), nd.commute_w _ _,
          nd.conjSub_w (by idx_tac5)⟩
        ⟨(hβJ _).symm, fun h => hmov (commutes_symm h), hsymm, hnorm⟩
        ⟨hKne.symm, fun h => hnKβ (commutes_symm h), hzt.symm,
          conjSub_eq_of_standardPair h2 (linearBlockStandardPair_symm hW) c.hz.mem
            c.hz.orderOf_eq_two⟩
        (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)) (commutes_symm (hfix _ (by idx_tac5)))
        (commutes_symm (nd.commK _)) (commutes_symm (hfix _ (by idx_tac5)))
        (commutes_symm (nd.commK _)) (commutes_symm (nd.commK _))
    ·
      obtain ⟨cx⟩ := c.exists_ctx_member hsingle (nd.mem ⟨0, by omega⟩)
        (nd.cl ⟨0, by omega⟩)
      exact chain5_false3 cx (chainBound0_plus3 (by norm_num)) (by norm_num)
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨3, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨2, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ (nd.mem ⟨4, by omega⟩)
          (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ hβ (hfix _ (by idx_tac5)))
        (nd.mem_loc ⟨0, by omega⟩ c.hK (nd.commK _))
        (nd.cl _) (nd.cl _) (nd.cl _) ht c.hz
        ⟨nd.ne_J (by idx_tac5), nd.not_commutes_of_adj (by idx_tac5), nd.commute_w _ _,
          nd.conjSub_w (by idx_tac5)⟩
        ⟨nd.ne_J (by idx_tac5), nd.not_commutes_of_adj (by idx_tac5), nd.commute_w _ _,
          nd.conjSub_w (by idx_tac5)⟩
        ⟨(hβJ _).symm, fun h => hmov (commutes_symm h), hsymm, hnorm⟩
        ⟨hKne.symm, fun h => hnKβ (commutes_symm h), hzt.symm,
          conjSub_eq_of_standardPair h2 (linearBlockStandardPair_symm hW) c.hz.mem
            c.hz.orderOf_eq_two⟩
        (nd.commutes_of_not_adj (by idx_tac5) (by idx_tac5)) (commutes_symm (hfix _ (by idx_tac5)))
        (commutes_symm (nd.commK _)) (commutes_symm (hfix _ (by idx_tac5)))
        (commutes_symm (nd.commK _)) (commutes_symm (nd.commK _))
  refine ⟨hp0, ?_⟩
  refine scenario_C3 hF c hsingle nd hβ ht ⟨W, hW⟩ (pp := pp) (b := ⟨2, by omega⟩) hfix hmov
    hnorm ?_ ?_ <;>
  idx_tac5

end Adapted

section Five2

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K : Subgroup G} {z : G}

theorem toralNormalD3_of_fixed_member_five (c : TCtx3 .POmegaPlus 5 Ω K z)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    ToralNormalD3 c (partner_involution_commutes_z3 c.hz ht hKβ) := by
  obtain ⟨M, hMΩ, hKM, hβM, hMN⟩ := hfixM
  have hMN' : ∃ N ∈ centralizingMembers Ω {z}, N ≠ M ∧ ¬ Commutes M N := by
    by_contra h
    exact hMN fun N hN hNM => by_contra fun hc => h ⟨N, hN, hNM, hc⟩
  obtain ⟨nd, h0, h1⟩ := exists_dnodes_of_pair_plus3 (le_refl 5) c hsingle hβ ht hKβ hMΩ hKM hβM
  exact toralNormalD3_of_nodes_five c ht hKβ hMΩ hMN' nd h0 h1

theorem PartnerPatternPlus3.of_fixed_member_five (hMFZ : Gaps.FundNoncentral 3)
    (c : TCtx3 .POmegaPlus 5 Ω K z) (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {ι : Type}
    (D : LieSystemData3 ι (locQuot Ω z) (locFamily Ω z)) {β : Subgroup G} {t : G} (hβ : β ∈ Ω)
    (ht : IsClassicalMember3 β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W K β)
    (hfixM : HasFixedMember Ω K β z) :
    PartnerPatternPlus3 5 Ω K β t :=
  PartnerPatternPlus3.of_toral_normal_of_adapted (le_refl 5) hMFZ (orthFacts3_plus (le_refl 5)) c
    hsingle D hβ ht hKβ hfixM (toralNormalD3_of_fixed_member_five c hsingle hβ ht hKβ hfixM)
    fun nd {_ _} hβ' ht' hKβ' {_} hfix hmov hnorm =>
      adapted_pattern_D53 (orthFacts3_plus (le_refl 5)) c hsingle nd hβ' ht' hKβ' hfix hmov hnorm

end Five2

theorem partnerPatternStmtD3_five (h3 : OddThreeFreeInput) : PartnerPatternStmtD3 5 := by
  intro G _ _ _ hnab K z hR hshape β hβ t ht hKβ hfix
  have hadm : StatedLieAdmissible .POmegaPlus 5 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ 5; omega⟩
  obtain ⟨c⟩ := nonempty_tctx3 (yData3_plus (by omega) hadm) h3 hR hshape
  have hsingle : ∀ L ∈ conjClass3 K, ∃ g : G, L = conjSub g K := by
    rintro L ⟨g, rfl⟩
    exact ⟨g, rfl⟩
  obtain ⟨ι, hι, D, hcard, -⟩ := id hshape
  exact PartnerPatternPlus3.of_fixed_member_five (Gaps.fundNoncentral 3) c hsingle D hβ ht hKβ hfix

end CFSG.ClassicalInvolution.Q3.Q3TD
