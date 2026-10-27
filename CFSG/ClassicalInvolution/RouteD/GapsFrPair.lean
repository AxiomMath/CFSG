module

public import CFSG.ClassicalInvolution.RouteD.GapsFrModel

public section

namespace CFSG.ClassicalInvolution.RouteD.Gaps

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic (Commutes conjSub fundamentalSubgroups)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open CFSG.ClassicalInvolution.ModelFacts.OrthAut (IsHypFam exists_isometry_of_isHypFam)
open scoped MatrixGroups commutatorElement

section Prefix

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {m : ℕ}

theorem exists_spin_prefix (hodd : Odd (Nat.card K)) (hQ : Q.Nondegenerate) (F₀ : HypFrame Q m)
    {k : ℕ} (hk : k < m) {P : ℕ → HypPair Q}
    (horth : ∀ a b, a < k → b < k → a ≠ b → (P a).Orth (P b)) :
    ∃ x : spinGroup Q, ∀ a (ha : a < k), (P a).e = spinAction Q x (F₀.vec ⟨a, by omega⟩ true) ∧
      (P a).f = spinAction Q x (F₀.vec ⟨a, by omega⟩ false) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : K) := invertibleOfNonzero h2
  let v : Fin k → Bool → V := fun i s => F₀.vec ⟨i.val, by omega⟩ s
  have hv : IsHypFam Q v :=
    ⟨fun i s => F₀.map_vec _ s,
      fun i j hij s t => F₀.polar_vec_of_ne (fun h => hij (Fin.ext (Fin.mk.inj h))) s t,
      fun i s => F₀.polar_vec_not _ s⟩
  have hv' : IsHypFam Q (famVec (fun i : Fin k => P i.val)) :=
    isHypFam_famVec _ fun i j hij => horth i j i.isLt j.isLt (fun e => hij (Fin.ext e))
  obtain ⟨ω, hω, hωv⟩ := exists_isometry_of_isHypFam hv hv'
  have hωe : ∀ (a : ℕ) (ha : a < k), ω (F₀.vec ⟨a, by omega⟩ true) = (P a).e := fun a ha =>
    hωv ⟨a, ha⟩ true
  have hωf : ∀ (a : ℕ) (ha : a < k), ω (F₀.vec ⟨a, by omega⟩ false) = (P a).f := fun a ha =>
    hωv ⟨a, ha⟩ false
  let Pf : Fin m → HypPair Q := fun a => if h : a.val < k then P a.val else imgPair F₀ a hω
  have hPf : ∀ i j, i ≠ j → (Pf i).Orth (Pf j) := by
    have himg : ∀ i j : Fin m, i ≠ j → (imgPair F₀ i hω).Orth (imgPair F₀ j hω) := fun i j hij =>
      ⟨by show polar Q (ω (F₀.vec i true)) (ω (F₀.vec j true)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hij true true,
       by show polar Q (ω (F₀.vec i true)) (ω (F₀.vec j false)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hij true false,
       by show polar Q (ω (F₀.vec i false)) (ω (F₀.vec j true)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hij false true,
       by show polar Q (ω (F₀.vec i false)) (ω (F₀.vec j false)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hij false false⟩
    have hmix : ∀ (a : ℕ) (ha : a < k) (j : Fin m), (⟨a, by omega⟩ : Fin m) ≠ j →
        (P a).Orth (imgPair F₀ j hω) := fun a ha j hj =>
      ⟨by rw [← hωe a ha]; show polar Q (ω (F₀.vec _ true)) (ω (F₀.vec j true)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hj true true,
       by rw [← hωe a ha]; show polar Q (ω (F₀.vec _ true)) (ω (F₀.vec j false)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hj true false,
       by rw [← hωf a ha]; show polar Q (ω (F₀.vec _ false)) (ω (F₀.vec j true)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hj false true,
       by rw [← hωf a ha]; show polar Q (ω (F₀.vec _ false)) (ω (F₀.vec j false)) = 0
          rw [polar_map_of_mem hω]; exact F₀.polar_vec_of_ne hj false false⟩
    intro i j hij
    by_cases hi : i.val < k
    · have ePi : Pf i = P i.val := by simp [Pf, hi]
      by_cases hj : j.val < k
      · have ePj : Pf j = P j.val := by simp [Pf, hj]
        rw [ePi, ePj]
        exact horth i.val j.val hi hj (fun e => hij (Fin.ext e))
      · have ePj : Pf j = imgPair F₀ j hω := by simp [Pf, hj]
        rw [ePi, ePj]
        exact hmix i.val hi j hij
    · have ePi : Pf i = imgPair F₀ i hω := by simp [Pf, hi]
      by_cases hj : j.val < k
      · have ePj : Pf j = P j.val := by simp [Pf, hj]
        rw [ePi, ePj]
        exact (hmix j.val hj i (fun e => hij e.symm)).symm
      · have ePj : Pf j = imgPair F₀ j hω := by simp [Pf, hj]
        rw [ePi, ePj]
        exact himg i j hij
  obtain ⟨x, hx1, -⟩ := exists_spin_family hodd hQ F₀ hPf (⟨k, hk⟩ : Fin m)
  refine ⟨x, fun a ha => ?_⟩
  have hne : (⟨a, by omega⟩ : Fin m) ≠ ⟨k, hk⟩ := fun h => by
    have := congrArg Fin.val h
    simp at this
    omega
  have h1 := hx1 _ hne
  have e : Pf ⟨a, by omega⟩ = P a := by simp [Pf, ha]
  rw [e] at h1
  exact h1

end Prefix

section Pair

variable {p f : ℕ} [Fact p.Prime]

theorem exists_spin_pair (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {m : ℕ} (hm : 5 ≤ m)
    {R₀ R₁ : Subgroup (spinGroup (quadPlus m (GaloisField p f)))}
    (hR₀ : R₀ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField p f) (by omega)))
    (hR₁ : R₁ ∈ fundamentalSubgroups .POmegaPlus
      (plusDatum m (GaloisField p f) (by omega)))
    (hadj : ModelAdj (Subgroup.center _) R₀ R₁)
    (hlin : ∃ W, LinearBlockStandardPair (GaloisField p f) W R₀ R₁) :
    ∃ x : spinGroup (quadPlus m (GaloisField p f)),
      R₀ = ((rootSL2 (plusFrame m (GaloisField p f) (by omega)) 0 1 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) ∧
      R₁ = ((rootSL2 (plusFrame m (GaloisField p f) (by omega)) 1 2 (by omega) (by omega)
        (by omega) true false).map (MulAut.conj x).toMonoidHom) := by
  classical
  have hm3 : 3 ≤ m := by omega
  obtain ⟨hf0, hK⟩ := RouteD.card_galoisField_of_four_le (p := p) (f := f) (by omega)
  have hodd : Odd (Nat.card (GaloisField p f)) := by
    rw [hK]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h2 : (2 : GaloisField p f) ≠ 0 :=
    CFSG.ClassicalInvolution.ModelFacts.two_ne_zero_galoisField f hp2
  have : Invertible (2 : GaloisField p f) := invertibleOfNonzero h2
  have hdim : 9 ≤ Module.finrank (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f) := by
    rw [finrank_plus]
    omega
  have hQ : (quadPlus m (GaloisField p f)).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_quadPlus m (GaloisField p f))
  have cq := centralQuot_plus hp2 (by omega : 4 ≤ m) hm3 hq
  let L : ℕ → Subgroup ((Fin m ⊕ Fin m → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin m ⊕ Fin m → GaloisField p f)) :=
    fun a => (if a = 0 then R₀ else R₁).map (spinAction (quadPlus m (GaloisField p f)))
  have hL0 : L 0 = R₀.map (spinAction (quadPlus m (GaloisField p f))) := by simp [L]
  have hL1 : L 1 = R₁.map (spinAction (quadPlus m (GaloisField p f))) := by simp [L]
  obtain ⟨i₀, hi₀⟩ := cq.map_mem _ hR₀
  obtain ⟨i₁, hi₁⟩ := cq.map_mem _ hR₁
  let i : ℕ → ((Fin m ⊕ Fin m → GaloisField p f) ≃ₗ[GaloisField p f]
      (Fin m ⊕ Fin m → GaloisField p f)) := fun a => if a = 0 then i₀ else i₁
  have hi : ∀ a < 2, IsFundamental (quadPlus m (GaloisField p f)) (L a) (i a) := by
    intro a ha
    by_cases h0 : a = 0
    · subst h0
      simpa [L, i] using hi₀
    · simpa [L, i, h0] using hi₁
  have hadjV : ModelAdj (scalars (GaloisField p f) (Fin m ⊕ Fin m → GaloisField p f))
      (R₀.map (spinAction (quadPlus m (GaloisField p f))))
      (R₁.map (spinAction (quadPlus m (GaloisField p f)))) := cq.modelAdj hR₀ hR₁ hadj
  obtain ⟨cm, N, C⟩ := adj_data hodd hdim hi₀ hi₁ hadjV
  have hVchain : VChain (quadPlus m (GaloisField p f)) 2 L i := by
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
  obtain ⟨x, hx⟩ := exists_spin_prefix hodd hQ (plusFrame m (GaloisField p f) hm3) (k := 3)
    (by omega) (P := pp) (fun a b ha hb hab => horth a b (by omega) (by omega) hab)
  have hnode : ∀ a (ha : a < 2), L a = ((rootSL2 (plusFrame m (GaloisField p f) hm3) a (a + 1)
      (by omega) (by omega) (by omega) true false).map (MulAut.conj x).toMonoidHom).map
        (spinAction (quadPlus m (GaloisField p f))) := by
    intro a ha
    have := La_range_eq_of_pairs (plusFrame m (GaloisField p f) hm3) (a := a) (b := a + 1)
      (by omega) (by omega) (by omega) true false x
      (orth_swapPair (horth a (a + 1) ha.le (by omega) (by omega))) (hx a (by omega))
      ⟨(hx (a + 1) (by omega)).2, (hx (a + 1) (by omega)).1⟩
    rw [hLp a ha]
    exact this
  have hperf := rootSL2_map_conj_perfect (p := p) (f := f) (m := m) (by omega)
    (plusFrame m (GaloisField p f) hm3) (x := x)
  refine ⟨x, ?_, ?_⟩
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hR₀) (hperf 0 1 (by omega) (by omega) (by omega) true false)
      (by rw [← hL0]; exact hnode 0 (by omega))
  · exact CFSG.ClassicalInvolution.ModelFacts.eq_of_map_eq_of_isPerfect _ cq.ker_le
      (cq.perf _ hR₁) (hperf 1 2 (by omega) (by omega) (by omega) true false)
      (by rw [← hL1]; exact hnode 1 (by omega))

end Pair

end CFSG.ClassicalInvolution.RouteD.Gaps
