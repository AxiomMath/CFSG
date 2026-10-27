module

public import CFSG.ClassicalInvolution.RouteD.GapsFrPair

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups commutatorElement

section Recognition

variable {p f : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (GaloisField p f) V]
  [FiniteDimensional (GaloisField p f) V] {Q : QuadraticForm (GaloisField p f) V}

omit [FiniteDimensional (GaloisField p f) V] in
theorem rootSL2_map_conj_perfect_gen {m : ℕ} (hq : 4 ≤ p ^ f) (F₀ : HypFrame Q m) (a b : ℕ)
    (ha : a < m) (hb : b < m) (hab : a ≠ b) (s t : Bool) (x : spinGroup Q) :
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

theorem spin_chain_recognition_gen (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hQ : Q.Nondegenerate)
    {s : ℕ} (hs : 1 ≤ s) (F₀ : HypFrame Q (s + 4))
    (hdim : 9 ≤ Module.finrank (GaloisField p f) V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    {R : ℕ → Subgroup (spinGroup Q)} {Rtw RM : Subgroup (spinGroup Q)}
    (hRf : ∀ a ≤ s, R a ∈ 𝓕) (hRtwf : Rtw ∈ 𝓕) (hRMf : RM ∈ 𝓕)
    (hadj : ∀ a < s, ModelAdj (Subgroup.center _) (R a) (R (a + 1)))
    (hlin : ∀ a < s, ∃ W, LinearBlockStandardPair (GaloisField p f) W (R a) (R (a + 1)))
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
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hex : ∀ a, ∃ i, a ≤ s → IsFundamental Q
      ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ s
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  obtain ⟨iM, hiM⟩ := cq.map_mem _ hRMf
  have hadjV : ∀ a < s, ModelAdj (scalars (GaloisField p f)
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
      exact hasSingularVector_of_linearPair hp2 (by omega) (hi a (by omega))
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
      have hadj' : ModelAdj (scalars (GaloisField p f)
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
  have hperf := rootSL2_map_conj_perfect_gen (p := p) (f := f) (m := s + 4) (by omega)
    F₀ (x := x)
  refine ⟨x, fun a ha => ?_, ?_, t, ?_⟩
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ (hRf a ha)) (hperf a (a + 1) (by omega) (by omega) (by omega) true false)
      (hxL a (by omega))
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hRtwf) (hperf s (s + 1) (by omega) (by omega) (by omega) true true) hxtw
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hRMf) (hperf (s + 2) (s + 3) (by omega) (by omega) (by omega) true t) hxM


theorem chain_distinct_twin_gen (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hdim : 9 ≤ Module.finrank (GaloisField p f) V) {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V)) {u : ℕ}
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
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hex : ∀ a, ∃ i, a ≤ u + 3 → IsFundamental Q
      ((R a).map (spinAction Q)) i := fun a => by
    by_cases ha : a ≤ u + 3
    · obtain ⟨i, hi⟩ := cq.map_mem _ (hRf a ha)
      exact ⟨i, fun _ => hi⟩
    · exact ⟨1, fun h => absurd h ha⟩
  choose i hi using hex
  obtain ⟨itw, hitw⟩ := cq.map_mem _ hRtwf
  have hadjV : ∀ a < u + 3, ModelAdj (scalars (GaloisField p f)
      V)
      ((R a).map (spinAction Q))
      ((R (a + 1)).map (spinAction Q)) := fun a ha =>
    cq.modelAdj (hRf a (by omega)) (hRf (a + 1) (by omega)) (hadj a ha)
  have hchain : IsChain (scalars (GaloisField p f)
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

theorem exists_spin_pair_gen (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) (hQ : Q.Nondegenerate) {m : ℕ}
    (hm : 4 ≤ m) (F₀ : HypFrame Q m) (hdim : 9 ≤ Module.finrank (GaloisField p f) V)
    {𝓕 : Set (Subgroup (spinGroup Q))}
    (cq : CentralQuot (spinAction Q) 𝓕 (fundSet Q) (scalars (GaloisField p f) V))
    {R₀ R₁ : Subgroup (spinGroup Q)} (hR₀ : R₀ ∈ 𝓕) (hR₁ : R₁ ∈ 𝓕)
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ x : spinGroup Q,
      R₀ = ((rootSL2 F₀ 0 1 (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 F₀ 1 2 (by omega) (by omega) (by omega) true false).map
        (MulAut.conj x).toMonoidHom) := by
  classical
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  let L : ℕ → Subgroup (V ≃ₗ[GaloisField p f]
      V) :=
    fun a => (if a = 0 then R₀ else R₁).map (spinAction Q)
  have hL0 : L 0 = R₀.map (spinAction Q) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction Q) := by simp [L]
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let i : ℕ → (V ≃ₗ[GaloisField p f]
      V) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental Q (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  have hadjV : ModelAdj (scalars (GaloisField p f) V)
      (R₀.map (spinAction Q))
      (R₁.map (spinAction Q)) := cq.modelAdj hR₀ hR₁ hadj
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hi₀ hi₁ hadjV
  have hVchain : VChain Q 2 L i := by
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
      have := hasSingularVector_of_linearPair hp2 (by omega) hi₀ hi₁ cm N C
        ⟨_, linearBlockStandardPair_map _ cq.ker_le hW⟩
      simpa [i] using this
  obtain ⟨pp, horth, hpl, hLp⟩ := exists_chain_pairs true hodd hVchain (le_refl 2)
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ F₀ (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 F₀ a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction Q) := by
    intro a ha
    have := La_range_eq_of_pairs F₀ (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  have hperf := rootSL2_map_conj_perfect_gen (p := p) (f := f) (m := m) (by omega)
    F₀ (x := x)
  refine ⟨x, ?_, ?_⟩
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hR₀) (hperf 0 1 (by omega) (by omega) (by omega) true false)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hR₁) (hperf 1 2 (by omega) (by omega) (by omega) true false)
      (by rw [← hL1]; exact hnode 1 (by omega))

end Recognition

section FixedData

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem frame_chain_fixed_data {s : ℕ} (hs : 1 ≤ s) {X : Type} [Group X]
    (F₀ : HypFrame Q (s + 4)) (θ : spinGroup Q →* X)
    (hker : θ.ker ≤ Subgroup.center (spinGroup Q)) (σ : X ≃* X)
    (hscal : ∀ z ∈ Subgroup.center (spinGroup Q), ∃ η : K, ∀ v, spinAction Q z v = η • v)
    (x : spinGroup Q) (t : Bool) {R : ℕ → Subgroup (spinGroup Q)} {Rtw RM : Subgroup (spinGroup Q)}
    (hR : ∀ a (ha : a ≤ s), R a = ((rootSL2 F₀ a (a + 1) (by omega) (by omega) (by omega) true
      false).map (MulAut.conj x).toMonoidHom))
    (hRtw : Rtw = ((rootSL2 F₀ s (s + 1) (by omega) (by omega) (by omega) true true).map
      (MulAut.conj x).toMonoidHom))
    (hRM : RM = ((rootSL2 F₀ (s + 2) (s + 3) (by omega) (by omega) (by omega) true t).map
      (MulAut.conj x).toMonoidHom))
    (hfix : ∀ a, 1 ≤ a → a ≤ s → ∀ y ∈ R a, σ (θ y) = θ y)
    (hfixtw : ∀ y ∈ Rtw, σ (θ y) = θ y) (hfixM : ∀ y ∈ RM, σ (θ y) = θ y)
    (hnorm0 : ∀ y ∈ R 0, σ (θ y) ∈ (R 0).map θ) :
    (∀ y ∈ (rootSL2 F₀ (s + 2) (s + 3) (by omega) (by omega) (by omega) true t).map
        (MulAut.conj x).toMonoidHom, σ (θ y) = θ y) ∧
    (∀ (a b : Fin (s + 4)) (hab : a ≠ b), a.val ≠ s + 2 → a.val ≠ s + 3 → a.val ≠ 0 →
      b.val ≠ s + 2 → b.val ≠ s + 3 → b.val ≠ 0 → ∀ (s' t' : Bool) (c : K),
        σ (θ (x * F₀.longRoot hab s' t' (.ofAdd c) * x⁻¹)) =
          θ (x * F₀.longRoot hab s' t' (.ofAdd c) * x⁻¹)) ∧
    (∀ y ∈ ((F₀.longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (fun h => by have := congrArg Fin.val h; simp at this) false true).range).map
          (MulAut.conj x).toMonoidHom,
      σ (θ y) ∈ (((F₀.longRoot (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)
        (fun h => by have := congrArg Fin.val h; simp at this) false true).range).map
          (MulAut.conj x).toMonoidHom).map θ) := by
  classical
  have hm3 : 3 ≤ s + 4 := by omega
  let i₀ : Fin (s + 4) := ⟨s + 2, by omega⟩
  let i₁ : Fin (s + 4) := ⟨s + 3, by omega⟩
  let c₀ : Fin (s + 4) := ⟨0, by omega⟩
  let jj : Fin (s + 4) := ⟨1, by omega⟩
  have hjc : c₀ ≠ jj := fun h => by have := congrArg Fin.val h; simp [c₀, jj] at this
  let Fix : Subgroup (spinGroup Q) :=
    MonoidHom.eqLocus (σ.toMonoidHom.comp (θ.comp (MulAut.conj x).toMonoidHom))
      (θ.comp (MulAut.conj x).toMonoidHom)
  have hFix : ∀ g, g ∈ Fix ↔ σ (θ (x * g * x⁻¹)) = θ (x * g * x⁻¹) := fun g => Iff.rfl
  have H1 : ∀ y ∈ (rootSL2 F₀ (s + 2) (s + 3) (by omega) (by omega) (by omega) true t).map
      (MulAut.conj x).toMonoidHom, σ (θ y) = θ y := fun y hy => hfixM y (by rw [hRM]; exact hy)
  have hFixR : ∀ a (ha1 : 1 ≤ a) (ha2 : a ≤ s) (g : spinGroup Q),
      g ∈ rootSL2 F₀ a (a + 1) (by omega) (by omega) (by omega) true false → g ∈ Fix := by
    intro a ha1 ha2 g hg
    rw [hFix]
    exact hfix a ha1 ha2 _ (by rw [hR a ha2]; exact ⟨g, hg, rfl⟩)
  have hFixT : ∀ g : spinGroup Q,
      g ∈ rootSL2 F₀ s (s + 1) (by omega) (by omega) (by omega) true true → g ∈ Fix := by
    intro g hg
    rw [hFix]
    exact hfixtw _ (by rw [hRtw]; exact ⟨g, hg, rfl⟩)
  have hA : ∀ a, 1 ≤ a → a < s + 1 →
      RootInN F₀ Fix a (a + 1) true false ∧ RootInN F₀ Fix (a + 1) a true false := by
    intro a ha1 ha2
    constructor
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixR a ha1 (by omega)
      exact ⟨upperSL2 c, HypFrame.longSL2_upperSL2 F₀ _ true false c⟩
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixR a ha1 (by omega)
      exact ⟨lowerSL2 c, HypFrame.longSL2_lowerSL2 F₀ _ true false c⟩
  have hT : RootInN F₀ Fix (s + 1 - 1) (s + 1) true true ∧
      RootInN F₀ Fix (s + 1) (s + 1 - 1) false false := by
    have e : s + 1 - 1 = s := by omega
    rw [e]
    constructor
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixT
      exact ⟨upperSL2 c, HypFrame.longSL2_upperSL2 F₀ _ true true c⟩
    · refine ⟨by omega, by omega, by omega, fun c => ?_⟩
      apply hFixT
      exact ⟨lowerSL2 c, HypFrame.longSL2_lowerSL2 F₀ _ true true c⟩
  have hall := rootInN_of_chain (F := F₀) (Fix := Fix) (n := s + 1) (by omega) hA hT
  refine ⟨H1, ?_, ?_⟩
  ·
    intro a b hab ha0 ha1 hac hb0 hb1 hbc s' t' c
    have hav : 1 ≤ a.val ∧ a.val ≤ s + 1 := by
      have := a.isLt
      omega
    have hbv : 1 ≤ b.val ∧ b.val ≤ s + 1 := by
      have := b.isLt
      omega
    have hab' : a.val ≠ b.val := fun h => hab (Fin.ext h)
    obtain ⟨_, _, _, hroot⟩ := hall a.val b.val s' t' hav.1 hav.2 hbv.1 hbv.2 hab'
    exact (hFix _).mp (hroot c)
  ·
    let k2 : Fin (s + 4) := ⟨2, by omega⟩
    have hjk : jj ≠ k2 := fun h => by have := congrArg Fin.val h; simp [jj, k2] at this
    have hik : c₀ ≠ k2 := fun h => by have := congrArg Fin.val h; simp [c₀, k2] at this
    rintro y ⟨u, ⟨c, rfl⟩, rfl⟩
    set c0 : K := Multiplicative.toAdd c with hc0
    have hcc : c = Multiplicative.ofAdd c0 := rfl
    rw [hcc]
    have hswap := HypFrame.longRoot_swap F₀ hjc false true c0
    have hu : F₀.longRoot hjc false true (.ofAdd c0) ∈ rootSL2 F₀ 0 1 (by omega) (by omega)
        (by omega) true false := by
      refine ⟨lowerSL2 (-c0), ?_⟩
      rw [HypFrame.longSL2_lowerSL2]
      exact hswap.symm
    have hy0 : (MulAut.conj x).toMonoidHom (F₀.longRoot hjc false true (.ofAdd c0)) ∈ R 0 := by
      rw [hR 0 (by omega)]
      exact ⟨_, hu, rfl⟩
    obtain ⟨y', hy'R, hy'θ⟩ := hnorm0 _ hy0
    rw [hR 0 (by omega)] at hy'R
    obtain ⟨g, hg, rfl⟩ := hy'R
    have hc : ∀ c' : K, ⁅g, F₀.longRoot hjk true false (.ofAdd c')⁆ ∈
        Subgroup.center (spinGroup Q) := by
      intro c'
      set w := F₀.longRoot hjk true false (.ofAdd c') with hw
      have hwR : (MulAut.conj x).toMonoidHom w ∈ R 1 := by
        rw [hR 1 hs]
        refine ⟨w, ⟨upperSL2 c', ?_⟩, rfl⟩
        exact HypFrame.longSL2_upperSL2 F₀ _ true false c'
      have hfw := hfix 1 le_rfl hs _ hwR
      have hcomm : Commute (F₀.longRoot hjc false true (.ofAdd c0)) w := by
        rw [hswap]
        exact HypFrame.commute_longRoot_longRoot_left F₀ (i := jj) (j := c₀) (l := k2) hjc.symm
          hjk true false false (-c0) c'
      have hcomm' := hcomm.map (MulAut.conj x).toMonoidHom
      exact commutator_central_of_conj x g w
        (commutator_central_of_stable θ hker σ hy'θ hfw hcomm'.eq)
    obtain ⟨c', hgc⟩ := mem_lowerRoot_of_comm_central F₀ hscal hjc hjk hik hg hc
    have hgU : g ∈ (F₀.longRoot hjc false true).range :=
      ⟨Multiplicative.ofAdd (-c'), (HypFrame.longRoot_swap F₀ hjc false true (-c')).trans
        (by rw [neg_neg]; exact hgc.symm)⟩
    rw [← hy'θ]
    exact ⟨_, ⟨g, hgU, rfl⟩, rfl⟩

end FixedData

end CFSG.ClassicalInvolution.RouteD.Gaps
