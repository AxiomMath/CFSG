module

public import CFSG.ClassicalInvolution.Q3.Q3TY33
public import CFSG.ClassicalInvolution.Q3.Q3TY23
public import CFSG.ClassicalInvolution.RouteD.GapsFrMinusZ

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.RouteD.Gaps CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.LieType.Universal CFSG.LieType CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalInvolution.WeakCT
  CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (toralNormal_minus_of_normalized_subgroups)
open CFSG.LieType.Universal.Spin
open scoped MatrixGroups commutatorElement


section Recognition

variable {V : Type} [AddCommGroup V] [Module (GaloisField 3 1) V]
  [FiniteDimensional (GaloisField 3 1) V] {Q : QuadraticForm (GaloisField 3 1) V}

theorem spin_chain_recognition_gen3 (hQ : Q.Nondegenerate)
    {s : ℕ} (hs : 1 ≤ s) (F₀ : HypFrame Q (s + 4))
    (hdim : 9 ≤ Module.finrank (GaloisField 3 1) V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField 3 1) V))
    {R : ℕ → Subgroup (spinGroup Q)} {Rtw RM : Subgroup (spinGroup Q)}
    (hRf : ∀ a ≤ s, R a ∈ 𝓕) (hRtwf : Rtw ∈ 𝓕) (hRMf : RM ∈ 𝓕)
    (hadj : ∀ a < s, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < s, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ s → Commutes (R a) (R b))
    (hM : ∀ a ≤ s, Commutes RM (R a))
    (hdist : ∀ a b, a + 1 < b → b ≤ s → ∀ i j,
      IsFundamental Q ((R a).map (spinAction Q)) i →
      IsFundamental Q ((R b).map (spinAction Q)) j → i ≠ j)
    (hne : Rtw ≠ R s)
    (htwin : ∀ i j, IsFundamental Q ((R s).map (spinAction Q)) i →
      IsFundamental Q (Rtw.map (spinAction Q)) j → i = j) :
    ∃ x : spinGroup Q,
      (∀ a (ha : a ≤ s), R a = ((rootSL2 F₀ a (a + 1) (by omega) (by omega) (by omega) true
        false).map (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 F₀ s (s + 1) (by omega) (by omega) (by omega) true true).map
        (MulAut.conj x).toMonoidHom) ∧
      ∃ t : Bool, RM = ((rootSL2 F₀ (s + 2) (s + 3) (by omega) (by omega) (by omega) true t).map
        (MulAut.conj x).toMonoidHom) := by
  classical
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have hex : ∀ a, ∃ i, a ≤ s → IsFundamental Q
      ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ s
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRMf
  have hadjV : ∀ a < s, ModelAdj (scalars (GaloisField 3 1)
      V)
      ((R a).map (spinAction Q))
      ((R (a + 1)).map (spinAction Q)) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hdata : ∀ a < s, i a * i (a + 1) = i (a + 1) * i a ∧
      i (a + 1) ∈ Subgroup.normalizer
        (((R a).map (spinAction Q) : Subgroup _) : Set _) ∧
      i (a + 1) ∉ Subgroup.centralizer
        (((R a).map (spinAction Q) : Subgroup _) : Set _) :=
    fun a ha => adj_data hodd hdim (hi a (by omega)) (hi (a + 1) (by omega)) (hadjV a ha)
  have hVchain : VChain Q (s + 1)
      (fun a => (R a).map (spinAction Q)) i := by
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
  have hcM : ∀ a ≤ s, Commutes ((R a).map (spinAction Q))
      (RM.map (spinAction Q)) := fun a ha =>
    (cq.commutes_iff (hRf a ha)).mpr (commutes_symm (hM a ha))
  have hMne : ∀ a ≤ s, iM ≠ i a := by
    intro a ha
    by_cases has : a < s
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
    · have has' : a = s := by omega
      subst has'
      have hD := hi (a - 1) (by omega)
      have hadj' : ModelAdj (scalars (GaloisField 3 1)
          V)
          ((R (a - 1)).map (spinAction Q))
          ((R a).map (spinAction Q)) := by
        have := hadjV (a - 1) (by omega)
        rwa [show a - 1 + 1 = a by omega] at this
      refine ne_of_distinguish hodd hdim (hi a ha) hiM hD ?_ ?_ ?_ ?_ ?_
      · exact hadj'.1
      · intro e
        apply hadj'.2.1
        have := hcM a ha
        rw [← e] at this
        exact commutes_symm this
      · exact ModelInvComm.of_adj hadj'
      · exact modelInvComm_of_commutes hodd hD hiM (hcM (a - 1) (by omega))
      · intro hiff
        exact hadj'.2.1 (hiff.mpr (hcM (a - 1) (by omega)))
  have hMorth : ∀ a < s + 1, ∀ x ∈ negSpace iM, ∀ y ∈ negSpace (i a), polar
      Q x y = 0 := by
    intro a ha x hx y hy
    rcases orth_or_twin hodd (hi a (by omega)) hiM (hcM a (by omega)) with h | h
    · rw [polar_comm]
      exact h y hy x hx
    · exact absurd h (hMne a (by omega))
  have hLtw : IsFundamental Q
      (Rtw.map (spinAction Q)) (i s) :=
    htwin (i s) itw (hi s le_rfl) hitw ▸ hitw
  have hneL : Rtw.map (spinAction Q) ≠
      (R s).map (spinAction Q) :=
    fun h => hne (cq.map_inj hRtwf (hRf s le_rfl) h)
  obtain ⟨x, hxL, hxtw, t, hxM⟩ := exists_spin_chain (r := s + 1) hodd hQ
    (F₀ := F₀) (s := s) rfl rfl (by omega) hVchain hiM hMorth
    hLtw hneL
  refine ⟨x, fun a ha => ?_, ?_, t, ?_⟩
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ (hRf a ha))
      (rootSL2_map_conj_pow3 F₀ a (a + 1) (by omega) (by omega) (by omega) true false x)
      (hxL a (by omega))
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hRtwf)
      (rootSL2_map_conj_pow3 F₀ s (s + 1) (by omega) (by omega) (by omega) true true x) hxtw
  · exact eq_of_map_eq_of_pow3 _ cq.ker_le cq.cop (cq.pow3 _ hRMf)
      (rootSL2_map_conj_pow3 F₀ (s + 2) (s + 3) (by omega) (by omega) (by omega) true t x) hxM


theorem chain_distinct_twin_gen3
    (hdim : 9 ≤ Module.finrank (GaloisField 3 1) V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot3 (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField 3 1) V)) {u : ℕ}
    {R : ℕ → Subgroup (spinGroup Q)} {Rtw : Subgroup (spinGroup Q)}
    (hRf : ∀ a ≤ u + 3, R a ∈ 𝓕) (hRtwf : Rtw ∈ 𝓕)
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw) :
    (∀ a b, a + 1 < b → b ≤ u + 3 → ∀ i j,
      IsFundamental Q ((R a).map (spinAction Q)) i →
      IsFundamental Q ((R b).map (spinAction Q)) j → i ≠ j) ∧
    (∀ i j, IsFundamental Q ((R (u + 3)).map (spinAction Q)) i →
      IsFundamental Q (Rtw.map (spinAction Q)) j → i = j) := by
  classical
  have hodd : Odd (Nat.card (GaloisField 3 1)) := odd_gf3
  have hex : ∀ a, ∃ i, a ≤ u + 3 → IsFundamental Q
      ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ u + 3
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  have hadjV : ∀ a < u + 3, ModelAdj (scalars (GaloisField 3 1)
      V)
      ((R a).map (spinAction Q))
      ((R (a + 1)).map (spinAction Q)) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hchain : IsChain (scalars (GaloisField 3 1)
      V)
      (fundSet Q) (u + 3 + 1)
      (fun a => (R a).map (spinAction Q)) :=
    ⟨fun a ha => cq.map_mem _ (hRf a (by omega)), fun a ha => hadjV a (by omega),
      fun a b hab hb => (cq.commutes_iff (hRf a (by omega))).mpr (hcomm a b hab (by omega))⟩
  have hNC : ∀ a b, a + 1 < b → b ≤ u + 3 → ∀ x ∈ negSpace (i a), ∀ y ∈ negSpace (i b),
      polar Q x y = 0 := fun a b hab hb =>
    chain_orth hodd hdim (by omega) hchain (fun a ha => hi a (by omega)) hab (by omega)
  have hdist : ∀ a b, a + 1 < b → b ≤ u + 3 → ∀ i' j',
      IsFundamental Q
        ((R a).map (spinAction Q)) i' →
      IsFundamental Q
        ((R b).map (spinAction Q)) j' → i' ≠ j' := by
    intro a b hab hb i' j' hi' hj' hij
    have e1 : i a = i' := IsFundamental.involution_unique hodd (hi a (by omega)) hi'
    have e2 : i b = j' := IsFundamental.involution_unique hodd (hi b hb) hj'
    have e : i a = i b := by rw [e1, e2, hij]
    exact not_orth_self hodd (hi a (by omega)) fun x hx y hy =>
      hNC a b hab hb x hx y (by rw [← e]; exact hy)
  refine ⟨hdist, fun i' j' hi' hj' => ?_⟩
  have e1 : i (u + 3) = i' := IsFundamental.involution_unique hodd (hi (u + 3) le_rfl) hi'
  have e2 : itw = j' := IsFundamental.involution_unique hodd hitw hj'
  rw [← e1, ← e2]
  by_contra hne
  have hne' : i (u + 3) ≠ itw := hne
  have hcA : Commutes ((R (u + 1)).map (spinAction Q))
      (Rtw.map (spinAction Q)) :=
    (cq.commutes_iff (hRf (u + 1) (by omega))).mpr (hcommtw (u + 1) le_rfl)
  have hcB : Commutes ((R (u + 3)).map (spinAction Q))
      (Rtw.map (spinAction Q)) :=
    (cq.commutes_iff (hRf (u + 3) le_rfl)).mpr hcommtw'
  have hcD : Commutes ((R u).map (spinAction Q))
      (Rtw.map (spinAction Q)) :=
    (cq.commutes_iff (hRf u (by omega))).mpr (hcommtw u (by omega))
  have oAT : ∀ x ∈ negSpace (i (u + 1)), ∀ y ∈ negSpace itw,
      polar Q x y = 0 := by
    rcases orth_or_twin hodd (hi (u + 1) (by omega)) hitw hcA with h | h
    · exact h
    · exfalso
      refine ne_of_distinguish hodd hdim (hi (u + 1) (by omega)) hitw (hi u (by omega)) ?_ ?_ ?_
        ?_ ?_ h
      · exact (hadjV u (by omega)).1
      · intro e
        apply (hadjV u (by omega)).2.1
        have := hcA
        rw [← e] at this
        exact commutes_symm this
      · exact ModelInvComm.of_adj (hadjV u (by omega))
      · exact modelInvComm_of_commutes hodd (hi u (by omega)) hitw hcD
      · intro hiff
        exact (hadjV u (by omega)).2.1 (hiff.mpr hcD)
  have oBT : ∀ x ∈ negSpace (i (u + 3)), ∀ y ∈ negSpace itw,
      polar Q x y = 0 := by
    rcases orth_or_twin hodd (hi (u + 3) le_rfl) hitw hcB with h | h
    · exact h
    · exact absurd h.symm hne'
  have hadjtwV := cq.modelAdj (hRf (u + 2) (by omega)) hRtwf hadjtw
  obtain ⟨cm1, N1, C1⟩ := adj_data hodd hdim (hi (u + 1) (by omega)) (hi (u + 2) (by omega))
    (hadjV (u + 1) (by omega))
  obtain ⟨cm2, N2, C2⟩ := adj_data hodd hdim (hi (u + 2) (by omega)) (hi (u + 3) le_rfl)
    (hadjV (u + 2) (by omega))
  obtain ⟨cm3, N3, C3⟩ := adj_data hodd hdim (hi (u + 2) (by omega)) hitw hadjtwV
  have pd1 := (lemma_6_10 hodd (hi (u + 1) (by omega)) (hi (u + 2) (by omega)) cm1 N1 C1).1
  have pd2 := (lemma_6_10 hodd (hi (u + 2) (by omega)) (hi (u + 3) le_rfl) cm2 N2 C2).1
  have pd3 := (lemma_6_10 hodd (hi (u + 2) (by omega)) hitw cm3 N3 C3).1
  refine not_three_orth_planes (Q := Q)
    (W := negSpace (i (u + 2)))
    (P₁ := negSpace (i (u + 1)) ⊓ negSpace (i (u + 2)))
    (P₂ := negSpace (i (u + 2)) ⊓ negSpace (i (u + 3)))
    (P₃ := negSpace (i (u + 2)) ⊓ negSpace itw) (finrank_negSpace hodd (hi (u + 2) (by omega)))
    inf_le_right inf_le_left inf_le_left pd1.finrank_U₂ pd2.finrank_U₂ pd3.finrank_U₂
    pd1.nondeg₂ pd3.nondeg₂ ?_ ?_ ?_
  · exact fun x hx y hy => hNC (u + 1) (u + 3) (by omega) le_rfl x (Submodule.mem_inf.mp hx).1 y
      (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => oAT x (Submodule.mem_inf.mp hx).1 y (Submodule.mem_inf.mp hy).2
  · exact fun x hx y hy => oBT x (Submodule.mem_inf.mp hx).2 y (Submodule.mem_inf.mp hy).2

end Recognition

section Lift

theorem toralNormal_minus_of_frame_chain3 {s : ℕ} (hs : 1 ≤ s)
    {X : Type} [Group X]
    (θ : spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (s + 5) (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    (x : spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2))
    (t : Bool)
    {R : ℕ → Subgroup (spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    {Rtw RM : Subgroup (spinGroup (quadMinus (s + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    (hR : ∀ a (ha : a ≤ s), R a = ((rootSL2 (minusFrame (s + 5) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).toHypFrame a (a + 1) (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom))
    (hRtw : Rtw = ((rootSL2 (minusFrame (s + 5) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).toHypFrame s (s + 1) (by omega) (by omega) (by omega) true true).map
        (MulAut.conj x).toMonoidHom))
    (hRM : RM = ((rootSL2 (minusFrame (s + 5) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).toHypFrame (s + 2) (s + 3) (by omega) (by omega) (by omega) true t).map
        (MulAut.conj x).toMonoidHom))
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ((∃ k₀ v, MinusToral (minusCoeffs_irr 3 1) θ σ k₀ v) ∨
      (∃ k₀ v, MinusOuter (minusCoeffs_irr 3 1) θ σ k₀ v)) ∧ MinusLift θ σ := by
  classical
  have hirr := minusCoeffs_irr 3 1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hf : 1 ≤ 1 := le_rfl
  have hK : Nat.card (GaloisField 3 1) = 3 ^ 1 := by rw [card_gf3, pow_one]
  have hscal : ∀ z ∈ Subgroup.center (spinGroup (quadMinus (s + 5) (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)),
      ∃ η : GaloisField 3 1, ∀ v, spinAction (quadMinus (s + 5) (GaloisField 3 1)
        (minusCoeffs 3 1).1 (minusCoeffs 3 1).2) z v = η • v := by
    intro z hz
    obtain ⟨c, hc⟩ := mem_scalars.mp (Exotic.spinAction_center_mem_scalars_minus (by omega) hirr hz)
    exact ⟨c, hc⟩
  obtain ⟨H1g, H2g, H3g⟩ := frame_chain_fixed_data hs
    (minusFrame (s + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame θ hker σ hscal x t hR
    hRtw hRM hfix hfixtw hfixM hnorm0
  let i₀ : Fin (s + 5 - 1) := ⟨s + 2, by omega⟩
  let i₁ : Fin (s + 5 - 1) := ⟨s + 3, by omega⟩
  let c₀ : Fin (s + 5 - 1) := ⟨0, by omega⟩
  let jj : Fin (s + 5 - 1) := ⟨1, by omega⟩
  have h01 : i₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₀, i₁] at this
  have hc0 : c₀ ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, c₀] at this
  have hc1 : c₀ ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, c₀] at this
  have hj0 : jj ≠ i₀ := fun h => by have := congrArg Fin.val h; simp [i₀, jj] at this
  have hj1 : jj ≠ i₁ := fun h => by have := congrArg Fin.val h; simp [i₁, jj] at this
  have hjc : c₀ ≠ jj := fun h => by have := congrArg Fin.val h; simp [c₀, jj] at this
  have hγ₀ : toStdB (s + 5 - 1) (ofStdB (s + 5 - 1) (Pi.single i₀ (boolSign true) +
      Pi.single i₁ (boolSign t))) = Pi.single i₀ (boolSign true) + Pi.single i₁ (boolSign t) :=
    toStdB_ofStdB _ _
  have hγ₁ : toStdB (s + 5 - 1) (ofStdB (s + 5 - 1) (Pi.single c₀ (boolSign false) +
      Pi.single jj (boolSign true))) = Pi.single c₀ (boolSign false) +
        Pi.single jj (boolSign true) := toStdB_ofStdB _ _
  set γ₀ := ofStdB (s + 5 - 1) (Pi.single i₀ (boolSign true) + Pi.single i₁ (boolSign t))
    with hγ₀d
  set γ₁ := ofStdB (s + 5 - 1) (Pi.single c₀ (boolSign false) + Pi.single jj (boolSign true))
    with hγ₁d
  have hH1 : ∀ y ∈ (((minusDatum (s + 5) hirr).rootGroup γ₀ ⊔
      (minusDatum (s + 5) hirr).rootGroup (-γ₀)).map (MulAut.conj x).toMonoidHom),
      σ (θ y) = θ y := by
    rw [rootGroup_sup_eq_longSL2_range_minus hirr h01 true t hγ₀]
    exact H1g
  have hH2 : ∀ (a a' : Fin (s + 5 - 1)), a ≠ a' → a ≠ i₀ → a ≠ i₁ → a ≠ c₀ → a' ≠ i₀ →
      a' ≠ i₁ → a' ≠ c₀ → ∀ (s' t' : Bool) {γ : Fin (s + 5 - 1) → ℤ},
        toStdB (s + 5 - 1) γ = Pi.single a (boolSign s') + Pi.single a' (boolSign t') →
          ∀ y ∈ ((minusDatum (s + 5) hirr).rootGroup γ).map (MulAut.conj x).toMonoidHom,
            σ (θ y) = θ y := by
    intro a b hab ha0 ha1 hac hb0 hb1 hbc s' t' γ hγ y hy
    have hXγ : (minusDatum (s + 5) hirr).rootGroup γ =
        ((minusFrame (s + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).longRoot hab s' t').range :=
      minusRootGroup_eq_long (s + 5) hirr hab s' t' hγ
    rw [hXγ] at hy
    obtain ⟨g, ⟨c, rfl⟩, rfl⟩ := hy
    exact H2g a b hab (fun h => ha0 (Fin.ext h)) (fun h => ha1 (Fin.ext h))
      (fun h => hac (Fin.ext h)) (fun h => hb0 (Fin.ext h)) (fun h => hb1 (Fin.ext h))
      (fun h => hbc (Fin.ext h)) s' t' (Multiplicative.toAdd c)
  have hH3 : ∀ y ∈ ((minusDatum (s + 5) hirr).rootGroup γ₁).map (MulAut.conj x).toMonoidHom,
      σ (θ y) ∈ (((minusDatum (s + 5) hirr).rootGroup γ₁).map (MulAut.conj x).toMonoidHom).map
        θ := by
    have hXγ₁ : (minusDatum (s + 5) hirr).rootGroup γ₁ =
        ((minusFrame (s + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).longRoot hjc false
          true).range :=
      minusRootGroup_eq_long (s + 5) hirr hjc false true hγ₁
    rw [hXγ₁]
    exact H3g
  exact ⟨toralNormal_minus_of_normalized_subgroups hp2 hf hK hirr (n := s + 5) (by omega) θ hker σ
      hσ2 hσr h01 hc0 hc1 hj0 hj1 hjc hγ₀ hγ₁ x hH1 hH2 hH3,
    minusLift_of_normalized_subgroups hp2 hf hK hirr (n := s + 5) (by omega) θ hker σ hσ2 hσr h01
      hc0 hc1 hj0 hj1 hjc hγ₀ hγ₁ x hH1 hH2 hH3⟩

theorem minusLift_of_chain_long3 {u : ℕ} {X : Type} [Group X]
    (θ : spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1)
      (minusCoeffs 3 1).1 (minusCoeffs 3 1).2)))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    {Rtw RM : Subgroup (spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaMinus
      (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaMinus (minusDatum (u + 3 + 5) (minusCoeffs_irr 3 1)))
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField 3 1) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hM : ∀ a ≤ u + 3, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw)
    (hne : Rtw ≠ R (u + 3))
    (hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (x : spinGroup (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2)) (t : Bool),
      (∀ a (ha : a ≤ u + 3), R a = ((rootSL2 (minusFrame (u + 3 + 5) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2).toHypFrame a (a + 1) (by omega) (by omega) (by omega) true false).map
          (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (minusFrame (u + 3 + 5) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2).toHypFrame (u + 3) (u + 3 + 1) (by omega) (by omega) (by omega) true
          true).map (MulAut.conj x).toMonoidHom) ∧
      RM = ((rootSL2 (minusFrame (u + 3 + 5) (minusCoeffs 3 1).1
        (minusCoeffs 3 1).2).toHypFrame (u + 3 + 2) (u + 3 + 3) (by omega) (by omega) (by omega)
          true t).map (MulAut.conj x).toMonoidHom) ∧ MinusLift θ σ := by
  have hadm : StatedLieAdmissible .POmegaMinus (u + 3 + 5) 3 1 :=
    ⟨Nat.prime_three, le_rfl, by show 4 ≤ u + 3 + 5; omega⟩
  have h2 : (2 : GaloisField 3 1) ≠ 0 := two_ne_zero_gf3
  have : Invertible (2 : GaloisField 3 1) := invertibleOfNonzero h2
  have cq := centralQuot3_minus hadm
  have hdim : 9 ≤ Module.finrank (GaloisField 3 1)
      (Fin (u + 3 + 5 - 1) ⊕ Fin (u + 3 + 5 - 1) ⊕ Fin 2 → GaloisField 3 1) := by
    rw [finrank_minus 3 1 _ (by omega)]
    omega
  have hQ : (quadMinus (u + 3 + 5) (GaloisField 3 1) (minusCoeffs 3 1).1
      (minusCoeffs 3 1).2).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadMinus_of_finite _ (GaloisField 3 1) (minusCoeffs_irr 3 1))
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin_gen3 hdim cq hRf hRtwf hadj hcomm hadjtw
    hcommtw hcommtw'
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition_gen3 hQ (s := u + 3) (by omega)
    (minusFrame (u + 3 + 5) (minusCoeffs 3 1).1 (minusCoeffs 3 1).2).toHypFrame hdim cq hRf hRtwf
    hRMf hadj hlin hcomm hM hdist hne htwin
  exact ⟨x, t, hxR, hxtw, hxM, (toralNormal_minus_of_frame_chain3 (s := u + 3) (by omega) θ
    hker σ hσ2 hσr x t hxR hxtw hxM hfix hfixtw hfixM hnorm0).2⟩

end Lift

end CFSG.ClassicalInvolution.Q3.Q3TY
