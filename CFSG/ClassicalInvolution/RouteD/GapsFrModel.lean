module

public import CFSG.ClassicalInvolution.RouteD.GapsFrMain
public import CFSG.ClassicalInvolution.RouteD.GapsOrthChain

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

section Linear

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

theorem hasSingularVector_of_linearPair (hp2 : p ≠ 2) (hq : 4 ≤ p ^ f)
    {L₁ L₂ : Subgroup (V ≃ₗ[GaloisField p f] V)} {i₁ i₂ : V ≃ₗ[GaloisField p f] V}
    (h₁ : IsFundamental Q L₁ i₁) (h₂ : IsFundamental Q L₂ i₂) (hc : i₁ * i₂ = i₂ * i₁)
    (hN : i₂ ∈ Subgroup.normalizer (L₁ : Set (V ≃ₗ[GaloisField p f] V)))
    (hC : i₂ ∉ Subgroup.centralizer (L₁ : Set (V ≃ₗ[GaloisField p f] V)))
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W L₁ L₂) :
    HasSingularVector Q (negSpace i₁ ⊓ negSpace i₂) := by
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) hq
  have hK' : Nat.card (GaloisField p (2 * f)) = (p ^ f) ^ 2 := by
    rw [GaloisField.card p (2 * f) (by omega), ← pow_mul, mul_comm]
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨W, hW⟩ := hlin
  obtain ⟨-, hd⟩ := lemma_6_10_dichotomy hK hK' hodd h₁ h₂ hc hN hC
  rcases hd with ⟨hs, -⟩ | ⟨-, hu⟩
  · exact hs
  · exfalso
    have hW' : LinearBlockStandardPair (GaloisField p f) (L₁ ⊔ L₂) L₁ L₂ :=
      linear_eq_sup hW ▸ hW
    exact not_linear_and_unitary hK hK' hodd hW' hu

end Linear

section Recognition

variable {p f : ℕ} [Fact p.Prime]

theorem rootSL2_map_conj_perfect {m : ℕ} (hq : 4 ≤ p ^ f)
    (F₀ : HypFrame (quadPlus m (GaloisField p f)) m) (a b : ℕ) (ha : a < m) (hb : b < m)
    (hab : a ≠ b) (s t : Bool) (x : spinGroup (quadPlus m (GaloisField p f))) :
    ⁅(rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom,
      (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom⁆ =
      (rootSL2 F₀ a b ha hb hab s t).map (MulAut.conj x).toMonoidHom := by
  obtain ⟨-, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) hq
  have hperf : Group.IsPerfect SL(2, GaloisField p f) :=
    CFSG.ClassicalInvolution.sl2_isPerfect (by omega)
  have h1 : ⁅rootSL2 F₀ a b ha hb hab s t, rootSL2 F₀ a b ha hb hab s t⁆ =
      rootSL2 F₀ a b ha hb hab s t :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.range _)
  rw [← Subgroup.map_commutator, h1]

end Recognition

section Main

variable {p f : ℕ} [Fact p.Prime]

theorem spin_chain_recognition (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s : ℕ} (hs : 1 ≤ s)
    {R : ℕ → Subgroup (spinGroup (quadPlus (s + 4) (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus (s + 4) (GaloisField p f)))}
    (hRf : ∀ a ≤ s, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField p f) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField p f) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField p f) (by omega)))
    (hadj : ∀ a < s, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < s, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ s → Commutes (R a) (R b))
    (hM : ∀ a ≤ s, Commutes RM (R a))
    (hdist : ∀ a b, a + 1 < b → b ≤ s → ∀ i j,
      IsFundamental (quadPlus (s + 4) (GaloisField p f))
        ((R a).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) i →
      IsFundamental (quadPlus (s + 4) (GaloisField p f))
        ((R b).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) j → i ≠ j)
    (hne : Rtw ≠ R s)
    (htwin : ∀ i j, IsFundamental (quadPlus (s + 4) (GaloisField p f))
        ((R s).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) i →
      IsFundamental (quadPlus (s + 4) (GaloisField p f))
        (Rtw.map (spinAction (quadPlus (s + 4) (GaloisField p f)))) j → i = j) :
    ∃ x : spinGroup (quadPlus (s + 4) (GaloisField p f)),
      (∀ a (ha : a ≤ s), R a = ((rootSL2 (plusFrame (s + 4) (GaloisField p f) (by omega)) a
        (a + 1) (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom)) ∧
      Rtw = ((rootSL2 (plusFrame (s + 4) (GaloisField p f) (by omega)) s (s + 1) (by omega)
        (by omega) (by omega) true true).map (MulAut.conj x).toMonoidHom) ∧
      ∃ t : Bool, RM = ((rootSL2 (plusFrame (s + 4) (GaloisField p f) (by omega)) (s + 2)
        (s + 3) (by omega) (by omega) (by omega) true t).map (MulAut.conj x).toMonoidHom) := by
  classical
  have hm3 : 3 ≤ s + 4 := by omega
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (s + 4) ⊕ Fin (s + 4) → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hQ : (quadPlus (s + 4) (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp
      (nondegenerate_polarBilin_quadPlus (s + 4) (GaloisField p f))
  have cq := centralQuot_plus hp2 (by omega : 4 ≤ s + 4) hm3 hq
  have hex : ∀ a, ∃ i, a ≤ s → IsFundamental (quadPlus (s + 4) (GaloisField p f))
      ((R a).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) i := fun a => by
    by_cases ha : a ≤ s
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRMf
  have hadjV : ∀ a < s, ModelAdj (scalars (GaloisField p f)
      (Fin (s + 4) ⊕ Fin (s + 4) → GaloisField p f))
      ((R a).map (spinAction (quadPlus (s + 4) (GaloisField p f))))
      ((R (a + 1)).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hdata : ∀ a < s, i a * i (a + 1) = i (a + 1) * i a ∧
      i (a + 1) ∈ Subgroup.normalizer
        (((R a).map (spinAction (quadPlus (s + 4) (GaloisField p f))) : Subgroup _) : Set _) ∧
      i (a + 1) ∉ Subgroup.centralizer
        (((R a).map (spinAction (quadPlus (s + 4) (GaloisField p f))) : Subgroup _) : Set _) :=
    fun a ha => adj_data hodd hdim (hi a (by omega)) (hi (a + 1) (by omega)) (hadjV a ha)
  have hVchain : VChain (quadPlus (s + 4) (GaloisField p f)) (s + 1)
      (fun a => (R a).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) i := by
    refine ⟨fun a ha => hi a (by omega), fun a ha => (hdata a (by omega)).1,
      fun a ha => (hdata a (by omega)).2.1, fun a ha => (hdata a (by omega)).2.2, fun a ha => ?_,
      fun a b hab hb x hx y hy => ?_⟩
    · obtain ⟨W, hW⟩ := hlin a (by omega)
      exact hasSingularVector_of_linearPair hp2 (by omega) (hi a (by omega))
        (hi (a + 1) (by omega)) (hdata a (by omega)).1 (hdata a (by omega)).2.1
        (hdata a (by omega)).2.2 ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
    · have hcV := (cq.commutes_iff (hRf a (by omega))).mpr (hcomm a b hab (by omega))
      rcases orth_or_twin hodd (hi a (by omega)) (hi b (by omega)) hcV with h | h
      · exact h x hx y hy
      · exact absurd h.symm (hdist a b hab (by omega) _ _ (hi a (by omega)) (hi b (by omega)))
  have hcM : ∀ a ≤ s, Commutes ((R a).map (spinAction (quadPlus (s + 4) (GaloisField p f))))
      (RM.map (spinAction (quadPlus (s + 4) (GaloisField p f)))) := fun a ha =>
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
      have hadj' : ModelAdj (scalars (GaloisField p f)
          (Fin (a + 4) ⊕ Fin (a + 4) → GaloisField p f))
          ((R (a - 1)).map (spinAction (quadPlus (a + 4) (GaloisField p f))))
          ((R a).map (spinAction (quadPlus (a + 4) (GaloisField p f)))) := by
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
      (quadPlus (s + 4) (GaloisField p f)) x y = 0 := by
    intro a ha x hx y hy
    rcases orth_or_twin hodd (hi a (by omega)) hiM (hcM a (by omega)) with h | h
    · rw [polar_comm]
      exact h y hy x hx
    · exact absurd h (hMne a (by omega))
  have hLtw : IsFundamental (quadPlus (s + 4) (GaloisField p f))
      (Rtw.map (spinAction (quadPlus (s + 4) (GaloisField p f)))) (i s) :=
    htwin (i s) itw (hi s le_rfl) hitw ▸ hitw
  have hneL : Rtw.map (spinAction (quadPlus (s + 4) (GaloisField p f))) ≠
      (R s).map (spinAction (quadPlus (s + 4) (GaloisField p f))) :=
    fun h => hne (cq.map_inj hRtwf (hRf s le_rfl) h)
  obtain ⟨x, hxL, hxtw, t, hxM⟩ := exists_spin_chain (r := s + 1) hodd hQ
    (F₀ := plusFrame (s + 4) (GaloisField p f) hm3) (s := s) rfl rfl (by omega) hVchain hiM hMorth
    hLtw hneL
  have hperf := rootSL2_map_conj_perfect (p := p) (f := f) (m := s + 4) (by omega)
    (plusFrame (s + 4) (GaloisField p f) hm3) (x := x)
  refine ⟨x, fun a ha => ?_, ?_, t, ?_⟩
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ (hRf a ha)) (hperf a (a + 1) (by omega) (by omega) (by omega) true false)
      (hxL a (by omega))
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hRtwf) (hperf s (s + 1) (by omega) (by omega) (by omega) true true) hxtw
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hRMf) (hperf (s + 2) (s + 3) (by omega) (by omega) (by omega) true t) hxM

end Main

section Star

variable {p f : ℕ} [Fact p.Prime]

omit [Fact p.Prime] in
theorem not_orth_self {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] {Q : QuadraticForm K V} (hodd : Odd (Nat.card K))
    {L : Subgroup (V ≃ₗ[K] V)} {i : V ≃ₗ[K] V} (h : IsFundamental Q L i)
    (horth : ∀ x ∈ negSpace i, ∀ y ∈ negSpace i, polar Q x y = 0) : False := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨F, rfl, rfl⟩ := h
  rw [negSpace_La_neg_one h2] at horth
  have h4 : Module.finrank K F.span = 4 := F.finrank_span
  have hne : F.span ≠ ⊥ := fun h0 => by rw [h0, finrank_bot] at h4; omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact hx0 (F.polarNondegOn_span x hx fun y hy => horth x hx y hy)

end Star

section Star2

variable {p f : ℕ} [Fact p.Prime]

theorem chain_distinct_twin (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : ℕ}
    {R : ℕ → Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f)))}
    {Rtw : Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f)))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)))
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw) :
    (∀ a b, a + 1 < b → b ≤ u + 3 → ∀ i j,
      IsFundamental (quadPlus (u + 3 + 4) (GaloisField p f))
        ((R a).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) i →
      IsFundamental (quadPlus (u + 3 + 4) (GaloisField p f))
        ((R b).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) j → i ≠ j) ∧
    (∀ i j, IsFundamental (quadPlus (u + 3 + 4) (GaloisField p f))
        ((R (u + 3)).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) i →
      IsFundamental (quadPlus (u + 3 + 4) (GaloisField p f))
        (Rtw.map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) j → i = j) := by
  classical
  have hm3 : 3 ≤ u + 3 + 4 := by omega
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hdim : 9 ≤ Module.finrank (GaloisField p f)
      (Fin (u + 3 + 4) ⊕ Fin (u + 3 + 4) → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have cq := centralQuot_plus hp2 (by omega : 4 ≤ u + 3 + 4) hm3 hq
  have hex : ∀ a, ∃ i, a ≤ u + 3 → IsFundamental (quadPlus (u + 3 + 4) (GaloisField p f))
      ((R a).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) i := fun a => by
    by_cases ha : a ≤ u + 3
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  have hadjV : ∀ a < u + 3, ModelAdj (scalars (GaloisField p f)
      (Fin (u + 3 + 4) ⊕ Fin (u + 3 + 4) → GaloisField p f))
      ((R a).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f))))
      ((R (a + 1)).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hchain : IsChain (scalars (GaloisField p f)
      (Fin (u + 3 + 4) ⊕ Fin (u + 3 + 4) → GaloisField p f))
      (fundSet (quadPlus (u + 3 + 4) (GaloisField p f))) (u + 3 + 1)
      (fun a => (R a).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) :=
    ⟨fun a ha => cq.map_mem _ (hRf a (by omega)), fun a ha => hadjV a (by omega),
      fun a b hab hb => (cq.commutes_iff (hRf a (by omega))).mpr (hcomm a b hab (by omega))⟩
  have hNC : ∀ a b, a + 1 < b → b ≤ u + 3 → ∀ x ∈ negSpace (i a), ∀ y ∈ negSpace (i b),
      polar (quadPlus (u + 3 + 4) (GaloisField p f)) x y = 0 := fun a b hab hb =>
    chain_orth hodd hdim (by omega) hchain (fun a ha => hi a (by omega)) hab (by omega)
  have hdist : ∀ a b, a + 1 < b → b ≤ u + 3 → ∀ i' j',
      IsFundamental (quadPlus (u + 3 + 4) (GaloisField p f))
        ((R a).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) i' →
      IsFundamental (quadPlus (u + 3 + 4) (GaloisField p f))
        ((R b).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) j' → i' ≠ j' := by
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
  have hcA : Commutes ((R (u + 1)).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f))))
      (Rtw.map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) :=
    (cq.commutes_iff (hRf (u + 1) (by omega))).mpr (hcommtw (u + 1) le_rfl)
  have hcB : Commutes ((R (u + 3)).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f))))
      (Rtw.map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) :=
    (cq.commutes_iff (hRf (u + 3) le_rfl)).mpr hcommtw'
  have hcD : Commutes ((R u).map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f))))
      (Rtw.map (spinAction (quadPlus (u + 3 + 4) (GaloisField p f)))) :=
    (cq.commutes_iff (hRf u (by omega))).mpr (hcommtw u (by omega))
  have oAT : ∀ x ∈ negSpace (i (u + 1)), ∀ y ∈ negSpace itw,
      polar (quadPlus (u + 3 + 4) (GaloisField p f)) x y = 0 := by
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
      polar (quadPlus (u + 3 + 4) (GaloisField p f)) x y = 0 := by
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
  refine not_three_orth_planes (Q := quadPlus (u + 3 + 4) (GaloisField p f))
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

end Star2

section Long

variable {p f : ℕ} [Fact p.Prime]

theorem toralNormal_of_chain_long (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {u : ℕ} {X : Type} [Group X]
    (θ : spinGroup (quadPlus (u + 3 + 4) (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus (u + 3 + 4) (GaloisField p f)))}
    (hRf : ∀ a ≤ u + 3, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)))
    (hadj : ∀ a < u + 3, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < u + 3, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ u + 3 → Commutes (R a) (R b))
    (hM : ∀ a ≤ u + 3, Commutes RM (R a))
    (hadjtw : ModelAdj (Subgroup.center _) (R (u + 2)) Rtw)
    (hcommtw : ∀ a, a ≤ u + 1 → Commutes (R a) Rtw) (hcommtw' : Commutes (R (u + 3)) Rtw)
    (hne : Rtw ≠ R (u + 3))
    (hfix : ∀ a, 1 ≤ a → a ≤ u + 3 → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadPlus (u + 3 + 4) (GaloisField p f))) (v : Fin (u + 3 + 4) → ZMod 2),
      ∀ γ : Fin (u + 3 + 4) → ℤ,
        γ ∈ (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)).roots →
        ((((plusDatum (u + 3 + 4) (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum (u + 3 + 4) (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum (u + 3 + 4) (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum (u + 3 + 4) (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) := by
  obtain ⟨hdist, htwin⟩ := chain_distinct_twin hp2 hq hRf hRtwf hadj hcomm hadjtw hcommtw hcommtw'
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition hp2 hq (s := u + 3) (by omega) hRf hRtwf
    hRMf hadj hlin hcomm hM hdist hne htwin
  exact toralNormal_of_frame_chain hp2 hq (s := u + 3) (by omega) θ hker σ hσ2 hσr x t hxR hxtw hxM
    hfix hfixtw hfixM hnorm0

end Long

section General

variable {p f : ℕ} [Fact p.Prime]

theorem toralNormal_of_chain (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {s : ℕ} (hs : 1 ≤ s) {X : Type}
    [Group X] (θ : spinGroup (quadPlus (s + 4) (GaloisField p f)) →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup (quadPlus (s + 4) (GaloisField p f))))
    (σ : X ≃* X) (hσ2 : ∀ y, σ (σ y) = y) (hσr : ∀ k, σ (θ k) ∈ θ.range)
    {R : ℕ → Subgroup (spinGroup (quadPlus (s + 4) (GaloisField p f)))}
    {Rtw RM : Subgroup (spinGroup (quadPlus (s + 4) (GaloisField p f)))}
    (hRf : ∀ a ≤ s, R a ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField p f) (by omega)))
    (hRtwf : Rtw ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField p f) (by omega)))
    (hRMf : RM ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum (s + 4) (GaloisField p f) (by omega)))
    (hadj : ∀ a < s, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < s, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
    (hcomm : ∀ a b, a + 1 < b → b ≤ s → Commutes (R a) (R b))
    (hM : ∀ a ≤ s, Commutes RM (R a))
    (hdist : ∀ a b, a + 1 < b → b ≤ s → ∀ i j,
      IsFundamental (quadPlus (s + 4) (GaloisField p f))
        ((R a).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) i →
      IsFundamental (quadPlus (s + 4) (GaloisField p f))
        ((R b).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) j → i ≠ j)
    (hne : Rtw ≠ R s)
    (htwin : ∀ i j, IsFundamental (quadPlus (s + 4) (GaloisField p f))
        ((R s).map (spinAction (quadPlus (s + 4) (GaloisField p f)))) i →
      IsFundamental (quadPlus (s + 4) (GaloisField p f))
        (Rtw.map (spinAction (quadPlus (s + 4) (GaloisField p f)))) j → i = j)
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    ∃ (k₀ : spinGroup (quadPlus (s + 4) (GaloisField p f))) (v : Fin (s + 4) → ZMod 2),
      ∀ γ : Fin (s + 4) → ℤ, γ ∈ (plusDatum (s + 4) (GaloisField p f) (by omega)).roots →
        ((((plusDatum (s + 4) (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ).map σ.toMonoidHom =
          (((plusDatum (s + 4) (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ ∧
        ((∀ y ∈ (((plusDatum (s + 4) (GaloisField p f) (by omega)).rootGroup γ ⊔
              (plusDatum (s + 4) (GaloisField p f) (by omega)).rootGroup (-γ)).map
            (MulAut.conj k₀).toMonoidHom).map θ, σ y = y) ↔
          ∑ i, (γ i : ZMod 2) * v i = 0) := by
  obtain ⟨x, hxR, hxtw, t, hxM⟩ := spin_chain_recognition hp2 hq hs hRf hRtwf hRMf hadj hlin hcomm
    hM hdist hne htwin
  exact toralNormal_of_frame_chain hp2 hq hs θ hker σ hσ2 hσr x t hxR hxtw hxM hfix hfixtw hfixM
    hnorm0

end General

end CFSG.ClassicalInvolution.RouteD.Gaps
