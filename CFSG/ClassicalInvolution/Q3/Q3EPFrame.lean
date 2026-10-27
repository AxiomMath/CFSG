module

public import CFSG.ClassicalInvolution.Q3.Q3EPQuot
public import CFSG.ClassicalInvolution.RouteD.GapsFrPair
public import CFSG.ClassicalInvolution.RouteD.TypeEPatternTorGeom

public section

namespace CFSG.ClassicalInvolution.Q3.Q3W

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair B12 B23)
open CFSG.ClassicalInvolution.Models.OrthogonalPairs
open CFSG.LieType.Universal.Spin
open scoped commutatorElement MatrixGroups

set_option linter.unusedSectionVars false


section AdjPerp

variable {KY X : Type} [Group KY] [Group X] {π : KY →* X} {𝓕 : Set (Subgroup KY)}
  {𝓕' : Set (Subgroup X)} {Z' : Subgroup X}

theorem CentralQuot3.adjPerp [Finite KY] (hC : ¬ 3 ∣ Nat.card (Subgroup.center KY))
    (h : CentralQuot3 π 𝓕 𝓕' Z') (hG : AdjPerp (GaloisField 3 1) Z' 𝓕') :
    AdjPerp (GaloisField 3 1) (Subgroup.center KY) 𝓕 := by
  intro A hA B hB hAB S hS hSA hSB
  obtain ⟨N', hN', ⟨W, hW⟩, hc⟩ := hG (A.map π) (h.map_mem A hA) (B.map π) (h.map_mem B hB)
    (h.modelAdj hA hB hAB) (S.map π) (h.map_mem S hS) ((h.commutes_iff hS).mpr hSA)
    ((h.commutes_iff hS).mpr hSB)
  obtain ⟨N, hN, rfl⟩ := h.surj N' hN'
  exact ⟨N, hN, exists_lin_of_map3 hC π h.ker_le (h.pow3 S hS) (h.pow3 N hN) ⟨W, hW⟩,
    (h.commutes_iff hN).mp hc⟩

theorem adjPerp3_plus6 :
    AdjPerp (GaloisField 3 1) (Subgroup.center (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).K)
      (fundamentalSubgroups .POmegaPlus (modelUniv .POmegaPlus 6 3 1 Nat.prime_three).D) := by
  have hm3 : 3 ≤ 6 := by norm_num
  have hdim : 11 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have hG := adjPerp_model (Q := quadPlus 6 (GaloisField 3 1)) odd_gf3
    (nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1)) hdim
  have : Finite (spinGroup (quadPlus 6 (GaloisField 3 1))) :=
    ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  have hcop : ∀ w ∈ Subgroup.center (spinGroup (quadPlus 6 (GaloisField 3 1))),
      ¬ 3 ∣ orderOf w := by
    intro w hw h3
    have h4 := pow_four_of_mem_center_spinPlus (K := GaloisField 3 1) hm3 hw
    have := h3.trans (orderOf_dvd_of_pow_eq_one h4)
    omega
  have e := RouteD.modelUniv_POmegaPlus_eq (p := 3) (f := 1) hm3
  rw [e]
  exact centralQuot3_plus6.adjPerp (not_three_dvd_card_center hcop) hG

end AdjPerp

section RootSL2

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  {Q : QuadraticForm (GaloisField 3 1) V} {m : ℕ}

theorem rootSL2_map_conj_pow3 (F₀ : HypFrame Q m) (a b : ℕ) (ha : a < m) (hb : b < m)
    (hab : a ≠ b) (s t : Bool) (x : spinGroup Q) :
    Pow3 ((rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom) :=
  (pow3_range_sl2 card_gf3 _).map _

end RootSL2

section Linear

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}

theorem hasSingularVector_of_linearPair3
    {L₁ L₂ : Subgroup (V ≃ₗ[GaloisField 3 1] V)} {i₁ i₂ : V ≃ₗ[GaloisField 3 1] V}
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[GaloisField 3 1] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[GaloisField 3 1] V)))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W L₁ L₂) :
    HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) := by
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by
    rw [card_gf3]
    norm_num
  have hK' : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by omega)]
    norm_num
  obtain ⟨W, hW⟩ := hlin
  obtain ⟨-, hd⟩ := lemma_6_10_dichotomy hK hK' odd_gf3 h₁ h₂ hc hN hC
  rcases hd with ⟨hs, -⟩ | ⟨-, hu⟩
  · exact hs
  · exfalso
    have hW' : LinearBlockStandardPair (GaloisField 3 1) (L₁ ⊔ L₂) L₁ L₂ :=
      linear_eq_sup hW ▸ hW
    exact not_linear_and_unitary hK hK' odd_gf3 hW' hu

end Linear

section Pair

theorem exists_spin_pair3
    {R₀ R₁ : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1)))}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hR₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R₀ R₁) :
    ∃ x : spinGroup (quadPlus 6 (GaloisField 3 1)),
      R₀ = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 0 1 (by norm_num)
        (by norm_num) (by norm_num) true false).map (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 1 2 (by norm_num)
        (by norm_num) (by norm_num) true false).map (MulAut.conj x).toMonoidHom) := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have hQ : (quadPlus 6 (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus 6 (GaloisField 3 1))
  have cq := centralQuot3_plus6
  let L : ℕ → Subgroup ((Fin 6 ⊕ Fin 6 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 6 ⊕ Fin 6 → GaloisField 3 1)) :=
    fun a => (if a = 0 then R₀ else R₁).map (spinAction (quadPlus 6 (GaloisField 3 1)))
  have hL0 : L 0 = R₀.map (spinAction (quadPlus 6 (GaloisField 3 1))) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction (quadPlus 6 (GaloisField 3 1))) := by simp [L]
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let i : ℕ → ((Fin 6 ⊕ Fin 6 → GaloisField 3 1) ≃ₗ[GaloisField 3 1]
      (Fin 6 ⊕ Fin 6 → GaloisField 3 1)) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental (quadPlus 6 (GaloisField 3 1)) (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  have hadjV : ModelAdj (scalars (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1))
      (R₀.map (spinAction (quadPlus 6 (GaloisField 3 1))))
      (R₁.map (spinAction (quadPlus 6 (GaloisField 3 1)))) := cq.modelAdj hR₀ hR₁ hadj
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hi₀ hi₁ hadjV
  have hVchain : VChain (quadPlus 6 (GaloisField 3 1)) 2 L i := by
    refine ⟨hi, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_, fun a ha => ?_,
      fun a b hab hb => by omega⟩
    · have : a = 0 := by omega
      subst this
      simpa [i] using cm
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using N
    · have : a = 0 := by omega
      subst this
      simpa [L, i] using C
    · have : a = 0 := by omega
      subst this
      obtain ⟨W, hW⟩ := hlin
      have := hasSingularVector_of_linearPair3 hi₀ hi₁ cm N C
        ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
      simpa [i] using this
  obtain ⟨pp, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hVchain (le_refl 2)
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ (plusFrame 6 (GaloisField 3 1) hm3) (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 (plusFrame 6 (GaloisField 3 1) hm3) a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction (quadPlus 6 (GaloisField 3 1))) := by
    intro a ha
    have := La_range_eq_of_pairs (plusFrame 6 (GaloisField 3 1) hm3) (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  refine ⟨x, ?_, ?_⟩
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₀)
      (rootSL2_map_conj_pow3 _ 0 1 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hR₁)
      (rootSL2_map_conj_pow3 _ 1 2 (by omega) (by omega) (by omega) true false x)
      (by rw [← hL1]; exact hnode 1 (by omega))

end Pair

section Chain

theorem spin_chain_recognition3
    {R : ℕ → Subgroup (spinGroup (quadPlus (2 + 4) (GaloisField 3 1)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus (2 + 4) (GaloisField 3 1)))}
    (hRf : ∀ a ≤ 2, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (2 + 4) (GaloisField 3 1) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (2 + 4) (GaloisField 3 1) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (2 + 4) (GaloisField 3 1) (by omega)))
    (hadj : ∀ a < 2, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < 2, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ 2 → Commutes (R a) (R b))
    (hM : ∀ a ≤ 2, Commutes RM (R a))
    (hdist : ∀ a b, a + 1 < b → b ≤ 2 → ∀ i j,
      IsFundamental (quadPlus (2 + 4) (GaloisField 3 1))
        ((R a).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) i →
      IsFundamental (quadPlus (2 + 4) (GaloisField 3 1))
        ((R b).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) j → i ≠ j)
    (hne : Rtw ≠ R 2)
    (htwin : ∀ i j, IsFundamental (quadPlus (2 + 4) (GaloisField 3 1))
        ((R 2).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) i →
      IsFundamental (quadPlus (2 + 4) (GaloisField 3 1))
        (Rtw.map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) j → i = j) :
    ∃ x : spinGroup (quadPlus (2 + 4) (GaloisField 3 1)),
      (∀ a (ha : a ≤ 2), R a = ((rootSL2 (plusFrame (2 + 4) (GaloisField 3 1) (by omega)) a
        (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (plusFrame (2 + 4) (GaloisField 3 1) (by omega)) 2 (2 + 1) (by omega)
        (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      ∃ t : Bool, RM = ((rootSL2 (plusFrame (2 + 4) (GaloisField 3 1) (by omega)) (2 + 2)
        (2 + 3) (by omega) (by omega) (by omega) true t).map (MulAut.conj x).toMonoidHom) := by
  classical
  have hm3 : 3 ≤ 2 + 4 := by omega
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (2 + 4) ⊕ Fin (2 + 4) → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have hQ : (quadPlus (2 + 4) (GaloisField 3 1)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadPlus (2 + 4) (GaloisField 3 1))
  have cq := centralQuot3_plus6
  have hex : ∀ a, ∃ i, a ≤ 2 → IsFundamental (quadPlus (2 + 4) (GaloisField 3 1))
      ((R a).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) i := fun a => by
    by_cases ha : a ≤ 2
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRMf
  have hadjV : ∀ a < 2, ModelAdj (scalars (GaloisField 3 1)
      (Fin (2 + 4) ⊕ Fin (2 + 4) → GaloisField 3 1))
      ((R a).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1))))
      ((R (a + 1)).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hdata : ∀ a < 2, i a * i (a + 1) = i (a + 1) * i a ∧
      i (a + 1) ∈ Subgroup.normalizer
        (((R a).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1))) : Subgroup _) : Set _) ∧
      i (a + 1) ∉ Subgroup.centralizer
        (((R a).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1))) : Subgroup _) : Set _) :=
    fun a ha => adj_data hodd hdim (hi a (by omega)) (hi (a + 1) (by omega)) (hadjV a ha)
  have hVchain : VChain (quadPlus (2 + 4) (GaloisField 3 1)) (2 + 1)
      (fun a => (R a).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) i := by
    refine ⟨fun a ha => hi a (by omega), fun a ha => (hdata a (by omega)).1,
      fun a ha => (hdata a (by omega)).2.1, fun a ha => (hdata a (by omega)).2.2, fun a ha => ?_,
      fun a b hab hb x hx y hy => ?_⟩
    · obtain ⟨W, hW⟩ := hlin a (by omega)
      exact hasSingularVector_of_linearPair3 (hi a (by omega))
        (hi (a + 1) (by omega)) (hdata a (by omega)).1 (hdata a (by omega)).2.1
        (hdata a (by omega)).2.2 ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
    · have hcV := (cq.commutes_iff (hRf a (by omega))).mpr (hcomm a b hab (by omega))
      rcases orth_or_twin hodd (hi a (by omega)) (hi b (by omega)) hcV with h | h
      · exact h x hx y hy
      · exact absurd h.symm (hdist a b hab (by omega) _ _ (hi a (by omega)) (hi b (by omega)))
  have hcM : ∀ a ≤ 2, Commutes ((R a).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1))))
      (RM.map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) := fun a ha =>
    (cq.commutes_iff (hRf a ha)).mpr (commutes_symm (hM a ha))
  have hMne : ∀ a ≤ 2, iM ≠ i a := by
    intro a ha
    by_cases has : a < 2
    · have hD := hi (a + 1) (by omega)
      refine ne_of_distinguish hodd hdim (hi a ha) hiM hD ?_ ?_ ?_ ?_ ?_
      · exact fun e => (hadjV a has).1 e.symm
      · intro e
        apply (hadjV a has).2.1
        have := hcM a ha
        rwa [← e] at this
      · exact (ModelInvComm.of_adj (hadjV a has)).symm'
      · exact modelInvComm_of_commutes hodd hD hiM (hcM (a + 1) (by omega))
      · intro hiff
        exact (hadjV a has).2.1 (commutes_symm (hiff.mpr (hcM (a + 1) (by omega))))
    · have has' : a = 2 := by omega
      subst has'
      have hD := hi 1 (by omega)
      have hadj' : ModelAdj (scalars (GaloisField 3 1)
          (Fin (2 + 4) ⊕ Fin (2 + 4) → GaloisField 3 1))
          ((R 1).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1))))
          ((R 2).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) := hadjV 1 (by omega)
      refine ne_of_distinguish hodd hdim (hi 2 ha) hiM hD ?_ ?_ ?_ ?_ ?_
      · exact hadj'.1
      · intro e
        apply hadj'.2.1
        have := hcM 2 ha
        rw [← e] at this
        exact commutes_symm this
      · exact ModelInvComm.of_adj hadj'
      · exact modelInvComm_of_commutes hodd hD hiM (hcM 1 (by omega))
      · intro hiff
        exact hadj'.2.1 (hiff.mpr (hcM 1 (by omega)))
  have hMorth : ∀ a < 2 + 1, ∀ x ∈ negSpace iM, ∀ y ∈ negSpace (i a), polar
      (quadPlus (2 + 4) (GaloisField 3 1)) x y = 0 := by
    intro a ha x hx y hy
    rcases orth_or_twin hodd (hi a (by omega)) hiM (hcM a (by omega)) with h | h
    · rw [polar_comm]
      exact h y hy x hx
    · exact absurd h (hMne a (by omega))
  have hLtw : IsFundamental (quadPlus (2 + 4) (GaloisField 3 1))
      (Rtw.map (spinAction (quadPlus (2 + 4) (GaloisField 3 1)))) (i 2) :=
    htwin (i 2) itw (hi 2 le_rfl) hitw ▸ hitw
  have hneL : Rtw.map (spinAction (quadPlus (2 + 4) (GaloisField 3 1))) ≠
      (R 2).map (spinAction (quadPlus (2 + 4) (GaloisField 3 1))) :=
    fun h => hne (cq.map_inj hRtwf (hRf 2 le_rfl) h)
  obtain ⟨x, hxL, hxtw, t, hxM⟩ := exists_spin_chain (r := 2 + 1) hodd hQ
    (F₀ := plusFrame (2 + 4) (GaloisField 3 1) hm3) (s := 2) rfl rfl (by omega) hVchain hiM
    hMorth hLtw hneL
  refine ⟨x, fun a ha => ?_, ?_, t, ?_⟩
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ (hRf a ha))
      (rootSL2_map_conj_pow3 _ a (a + 1) (by omega) (by omega) (by omega) true false x)
      (hxL a (by omega))
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hRtwf)
      (rootSL2_map_conj_pow3 _ 2 (2 + 1) (by omega) (by omega) (by omega) true true x) hxtw
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hRMf)
      (rootSL2_map_conj_pow3 _ (2 + 2) (2 + 3) (by omega) (by omega) (by omega) true t x) hxM

theorem spin6_chain_frame3
    {R0 R1 R2 RN RM : Subgroup (spinGroup (quadPlus 6 (GaloisField 3 1)))}
    (h0 : R0 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (h1 : R1 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (h2 : R2 ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hN : RN ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hM : RM ∈ fundamentalSubgroups .POmegaPlus (plusDatum 6 (GaloisField 3 1) (by norm_num)))
    (hadj01 : ModelAdj (Subgroup.center _) R0 R1) (hadj12 : ModelAdj (Subgroup.center _) R1 R2)
    (hlin01 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R0 R1)
    (hlin12 : ∃ W, LinearBlockStandardPair (GaloisField 3 1) W R1 R2)
    (hc02 : Commutes R0 R2) (hM0 : Commutes RM R0) (hM1 : Commutes RM R1)
    (hM2 : Commutes RM R2) (hadjN : ModelAdj (Subgroup.center _) R0 RN)
    (hcN : Commutes R2 RN) :
    ∃ x : spinGroup (quadPlus 6 (GaloisField 3 1)),
      R0 = (rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 0 1 (by norm_num) (by norm_num)
        (by norm_num) true false).map (MulAut.conj x).toMonoidHom ∧
      R1 = (rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 1 2 (by norm_num) (by norm_num)
        (by norm_num) true false).map (MulAut.conj x).toMonoidHom ∧
      R2 = (rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 2 3 (by norm_num) (by norm_num)
        (by norm_num) true false).map (MulAut.conj x).toMonoidHom ∧
      ∃ t : Bool, RM = (rootSL2 (plusFrame 6 (GaloisField 3 1) (by norm_num)) 4 5 (by norm_num)
        (by norm_num) (by norm_num) true t).map (MulAut.conj x).toMonoidHom := by
  classical
  have hm3 : 3 ≤ 6 := by norm_num
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1) := by
    rw [finrank_plus]
    omega
  have cq := centralQuot3_plus6
  obtain ⟨i2, hi2⟩ := cq.map_mem _ h2
  obtain ⟨L', hL', hLne, -, -⟩ := IsFundamental.exists_twin hodd hi2
  obtain ⟨Rtw, hRtwf, hRtw⟩ := cq.surj L' ⟨i2, hL'⟩
  have hne : Rtw ≠ R2 := by
    intro h
    exact hLne (by rw [← hRtw, h])
  have htwin : ∀ i j, IsFundamental (quadPlus 6 (GaloisField 3 1))
      (R2.map (spinAction (quadPlus 6 (GaloisField 3 1)))) i →
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        (Rtw.map (spinAction (quadPlus 6 (GaloisField 3 1)))) j → i = j := by
    intro i j hi hj
    rw [hRtw] at hj
    exact (IsFundamental.involution_unique hodd hi hi2).trans
      (IsFundamental.involution_unique hodd hj hL').symm
  obtain ⟨iN, hiN⟩ := cq.map_mem _ hN
  have hdist : ∀ i j, IsFundamental (quadPlus 6 (GaloisField 3 1))
      (R0.map (spinAction (quadPlus 6 (GaloisField 3 1)))) i →
      IsFundamental (quadPlus 6 (GaloisField 3 1))
        (R2.map (spinAction (quadPlus 6 (GaloisField 3 1)))) j → i ≠ j := by
    intro i j hi hj
    have hadjV : ModelAdj (scalars (GaloisField 3 1) (Fin 6 ⊕ Fin 6 → GaloisField 3 1))
        (R0.map (spinAction (quadPlus 6 (GaloisField 3 1))))
        (RN.map (spinAction (quadPlus 6 (GaloisField 3 1)))) := cq.modelAdj h0 hN hadjN
    have hcV : Commutes (R2.map (spinAction (quadPlus 6 (GaloisField 3 1))))
        (RN.map (spinAction (quadPlus 6 (GaloisField 3 1)))) :=
      (cq.commutes_iff h2).mpr hcN
    have hc02V : Commutes (R0.map (spinAction (quadPlus 6 (GaloisField 3 1))))
        (R2.map (spinAction (quadPlus 6 (GaloisField 3 1)))) :=
      (cq.commutes_iff h0).mpr hc02
    refine (ne_of_distinguish hodd hdim hj hi hiN ?_ ?_ ?_ ?_ ?_)
    · intro e
      rw [← e] at hc02V
      exact hadjV.2.1 hc02V
    · exact fun e => hadjV.1 e.symm
    · exact modelInvComm_of_commutes hodd hiN hj (commutes_symm hcV)
    · exact (ModelInvComm.of_adj hadjV).symm'
    · intro hiff
      exact hadjV.2.1 (commutes_symm (hiff.mp (commutes_symm hcV)))
  let R : ℕ → Subgroup (spinGroup (quadPlus (2 + 4) (GaloisField 3 1))) := fun a =>
    if a = 0 then R0 else if a = 1 then R1 else R2
  have hR0 : R 0 = R0 := by simp [R]
  have hR1 : R 1 = R1 := by simp [R]
  have hR2 : R 2 = R2 := by simp [R]
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition3 (R := R) (Rtw := Rtw) (RM := RM)
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ h0, hR1 ▸ h1, hR2 ▸ h2])
    hRtwf hM
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ hR1 ▸ hadj01, hR1 ▸ hR2 ▸ hadj12])
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ hR1 ▸ hlin01, hR1 ▸ hR2 ▸ hlin12])
    (fun a b hab hb => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
      exact hR0 ▸ hR2 ▸ hc02)
    (fun a ha => by
      interval_cases a
      exacts [hR0 ▸ hM0, hR1 ▸ hM1, hR2 ▸ hM2])
    (fun a b hab hb => by
      obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 2 := by omega
      exact hR0 ▸ hR2 ▸ hdist)
    (hR2 ▸ hne) htwin
  exact ⟨x, hR0 ▸ hxR 0 (by norm_num), hR1 ▸ hxR 1 (by norm_num), hR2 ▸ hxR 2 (by norm_num), t,
    hxM⟩

end Chain

end CFSG.ClassicalInvolution.Q3.Q3W
