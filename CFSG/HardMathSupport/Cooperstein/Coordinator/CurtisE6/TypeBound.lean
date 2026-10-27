module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.TabNode
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.TabDead
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.NodeBound

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule CoxeterSystem
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.QuasithinUnique.Setup.SL2Modules
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

section NoJUniv


variable {K : Type} [Field K] [Finite K] [CharP K 2]
  {k : Type} [Field k] [Algebra K k] [CharP k 2] {V : Type} [AddCommGroup V] [Module k V]

theorem exists_torus_mul_center {h : ↥(e6Data_valid.minGroup K)}
    (hh : h ∈ (e6CoverData K).datum.H) :
    ∃ t ∈ ⨆ i, e6Data_valid.torus K i, ∃ z ∈ Subgroup.center ↥(e6Data_valid.minGroup K),
      h = t * z := by
  obtain ⟨t, ht, e⟩ := exists_lift_torusGroup (k := K) hh
  refine ⟨t, ht, t⁻¹ * h, ?_, by group⟩
  refine Isogeny.ker_e6IsogenyT_le_center K ?_
  rw [MonoidHom.mem_ker, map_mul, map_inv]
  exact inv_mul_eq_one.2 (Subtype.ext e)

theorem center_le_iSup_torus :
    Subgroup.center ↥(e6Data_valid.minGroup K) ≤ ⨆ i, e6Data_valid.torus K i := by
  intro z hz
  have h1 := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.center_le_range_minTorus
    e6Data_valid K isFiniteType_cartan_E6 (e6Datum_isCTGroupDatum K) (e6Datum_steinbergExtras K)
    (e6Datum_bruhatExtras K) hz
  have h2 : (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K).range =
      ⨆ i, e6Data_valid.torus K i := by
    unfold CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus
    rw [MonoidHom.noncommPiCoprod_range]
    rfl
  rw [← h2]; exact h1

theorem chi_eq_one_of_hm {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (h1 : ∀ (i : N6) (u : Kˣ),
      χ (e6Data_valid.hm K i u) = 1) : ∀ h ∈ (e6CoverData K).datum.H, χ h = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (e6Cover_split k)
  have hT : ∀ t ∈ ⨆ i, e6Data_valid.torus K i, t ∈ (e6CoverData K).datum.H ∧ χ t = 1 := by
    intro t ht'
    refine Subgroup.iSup_induction _ (C := fun t => t ∈ (e6CoverData K).datum.H ∧ χ t = 1)
      ht' (fun i t hti => ?_) ⟨one_mem _, hμ.chi_one⟩ (fun a b ha hb => ?_)
    · obtain ⟨u, rfl⟩ := (e6Data_valid.mem_torus K).1 hti
      exact ⟨e6_hm_mem_H i u, h1 i u⟩
    · exact ⟨mul_mem ha.1 hb.1, by rw [hμ.chi_mul ha.1 hb.1, ha.2, hb.2, one_mul]⟩
  intro h hh
  obtain ⟨t, ht', z, hz, rfl⟩ := exists_torus_mul_center hh
  obtain ⟨htH, htχ⟩ := hT t ht'
  obtain ⟨hzH, hzχ⟩ := hT z (center_le_iSup_torus hz)
  rw [hμ.chi_mul htH hzH, htχ, hzχ, one_mul]

theorem no_J_univ {ρ : Representation k ↥(e6Data_valid.minGroup K) V} (hρ : IsSimpleRep ρ)
    {y : V} {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) (hJ : J = Finset.univ) :
    ∀ g v, ρ g v = v := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hχi : ∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) = 1 := fun i u =>
    ((ht.2.2.2 i).1 (hJ ▸ Finset.mem_univ i)).1 u
  have hχ1 := chi_eq_one_of_hm hρ ht hχi
  set ρ0 : Representation k ↥(e6Data_valid.minGroup K) (Unit →₀ k) :=
    Representation.trivial k _ (Unit →₀ k) with hρ0def
  have hρ0 : IsSimpleRep ρ0 := by
    refine ⟨⟨⟨0, Finsupp.single () 1, fun h => by simpa using congrArg (fun f => f ()) h⟩⟩,
      fun W _ => ?_⟩
    by_cases hW : W = ⊥
    · exact Or.inl hW
    right
    obtain ⟨f, hfW, hf0⟩ := (Submodule.ne_bot_iff W).1 hW
    have hf : f = f () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    have hc : f () ≠ 0 := fun h => hf0 (by rw [hf, h, zero_smul])
    generalize f () = c at hf hc
    have hs : Finsupp.single () (1 : k) ∈ W := by
      have := W.smul_mem c⁻¹ hfW
      rwa [hf, smul_smul, inv_mul_cancel₀ hc, one_smul] at this
    refine eq_top_iff.2 fun g _ => ?_
    have : g = g () • Finsupp.single () 1 := Finsupp.ext fun u => by cases u; simp
    rw [this]
    exact Submodule.smul_mem _ _ hs
  have ht0 : IsCoverType (e6CoverRankOne K) ρ0 (Finsupp.single () (1 : k)) χ J := by
    refine ⟨fun u _ => by simp [hρ0def], fun h => by simpa using congrArg (fun f => f ()) h,
      fun h hh => ?_, fun i => ?_⟩
    · simp [hρ0def, hχ1 h hh]
    · refine ⟨fun _ => ⟨hχi i, ?_⟩, fun _ => hJ ▸ Finset.mem_univ i⟩
      letI : Fintype K := Fintype.ofFinite K
      refine ((e6CoverRankOne K).heckeT_datum ρ0 i _).trans ?_
      simp only [hρ0def, Representation.trivial_apply, Finset.sum_const, Finset.card_univ]
      have hev : Even (Fintype.card K) :=
        Nat.even_iff.2 ((FiniteField.even_card_iff_char_two (F := K)).1 (ringChar.eq K 2))
      obtain ⟨r, hr⟩ := hev
      have : (Fintype.card K • Finsupp.single () (1 : k)) = 0 := by
        have h0 : ((Fintype.card K : ℕ) : k) = 0 := by
          rw [hr]; push_cast; rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
        rw [← Nat.cast_smul_eq_nsmul k, h0, zero_smul]
      exact this
  obtain ⟨β, hβ⟩ := e6_iso_of_isCoverType hρ hρ0 ht ht0
  intro g v
  apply β.injective
  rw [hβ]
  simp [hρ0def]

end NoJUniv

section TypeBound


variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] def E6TypeBound (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) : Prop :=
  ∀ (k : Type) [Field k] [Finite k] [CharP k 2] [Algebra K k] (m : ℕ)
    (ρ : Representation k ↥(e6Data_valid.minGroup K) (Fin m → k)) (y : Fin m → k)
    (χ : ↥(e6Data_valid.minGroup K) → k) (J : Finset N6) (g : ℕ),
    IsSimpleRep ρ → (∃ (x : ↥(e6Data_valid.minGroup K)) (v : Fin m → k), ρ x v ≠ v) →
    IsCoverType (e6CoverRankOne K) ρ y χ J → 1 ≤ g → g ∣ n →
    (∀ (i : N6) (t : Kˣ), χ (e6Data_valid.hm K i t) ^ (2 ^ g) = χ (e6Data_valid.hm K i t)) →
    (n / g = 1 → (∃ (s : N6) (b : ℕ),
        (s = ⟨0, by decide⟩ ∨ s = ⟨5, by decide⟩ ∨ s = ⟨1, by decide⟩) ∧ b < n ∧
        J = Finset.univ.erase s ∧ ∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) =
          if i = s then (algebraMap K k (u : K)) ^ (2 ^ b) else 1) ∨ 79 ≤ m) ∧
    (2 ≤ n / g → 78 * (n / g) + 2 ≤ m)

theorem node_cases (s' : N6) : s' = ⟨0, by decide⟩ ∨ s' = ⟨1, by decide⟩ ∨ s' = ⟨2, by decide⟩ ∨
    s' = ⟨3, by decide⟩ ∨ s' = ⟨4, by decide⟩ ∨ s' = ⟨5, by decide⟩ := by
  rcases s' with ⟨i, hi⟩
  have : i < 6 := hi
  interval_cases i <;> simp

theorem surv_of_node {k : Type} [Field k] [Algebra K k] {V : Type} [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(e6Data_valid.minGroup K) V} {y : V}
    {χ : ↥(e6Data_valid.minGroup K) → k} {J : Finset N6}
    (ht : IsCoverType (e6CoverRankOne K) ρ y χ J) {s : N6} (hJ : ∀ s', s' ≠ s → s' ∈ J)
    (hs : s ∉ J) {b : ℕ}
    (hχ : ∀ z : Kˣ, χ (e6Data_valid.hm K s z) = (algebraMap K k (z : K)) ^ (2 ^ b)) :
    J = Finset.univ.erase s ∧ ∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) =
      if i = s then (algebraMap K k (u : K)) ^ (2 ^ b) else 1 := by
  classical
  refine ⟨?_, fun i u => ?_⟩
  · ext i
    simp only [Finset.mem_erase, Finset.mem_univ, and_true]
    constructor
    · intro hi hh; exact hs (hh ▸ hi)
    · exact fun hi => hJ i hi
  · by_cases hi : i = s
    · subst hi; simp [hχ u]
    · simp only [hi, ↓reduceIte]
      exact ((ht.2.2.2 i).1 (hJ i hi)).1 u

theorem e6_typeBound {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) : E6TypeBound K n := by
  classical
  intro k _ _ _ _ m ρ y χ J g hρ hnt ht hg hgn hper
  have hfin : Module.finrank k (Fin m → k) = m := Module.finrank_fin_fun k
  have hJne : J ≠ Finset.univ := by
    intro hJ
    obtain ⟨x, v, hxv⟩ := hnt
    exact hxv (no_J_univ hρ ht hJ x v)
  have fin_conv : ((n / g = 1 → 79 ≤ Module.finrank k (Fin m → k)) ∧
      (2 ≤ n / g → 78 * (n / g) + 2 ≤ Module.finrank k (Fin m → k))) →
      ((n / g = 1 → (∃ (s : N6) (b : ℕ),
        (s = ⟨0, by decide⟩ ∨ s = ⟨5, by decide⟩ ∨ s = ⟨1, by decide⟩) ∧ b < n ∧
        J = Finset.univ.erase s ∧ ∀ (i : N6) (u : Kˣ), χ (e6Data_valid.hm K i u) =
          if i = s then (algebraMap K k (u : K)) ^ (2 ^ b) else 1) ∨ 79 ≤ m) ∧
      (2 ≤ n / g → 78 * (n / g) + 2 ≤ m)) := by
    rintro ⟨h1, h2⟩
    rw [hfin] at h1 h2
    exact ⟨fun h => Or.inr (h1 h), h2⟩
  have hp : ∀ s : N6, χ (e6Data_valid.hm K s 1) = 1 → True := fun _ _ => trivial
  by_cases h2 : (⟨2, by decide⟩ : N6) ∈ J
  swap
  · refine fin_conv (dead_bound d1n3T d1n3C (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hn hK hρ ht h2 ?_ ?_ hg hgn (hper _))
    · intro j hj; simp [d1n3T] at hj; subst hj; exact h2
    · intro j hj; simp [d1n3C] at hj; subst hj; exact h2
  by_cases h3 : (⟨3, by decide⟩ : N6) ∈ J
  swap
  · refine fin_conv (dead_bound d1n4T d1n4C (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hn hK hρ ht h3 ?_ ?_ hg hgn (hper _))
    · intro j hj; simp [d1n4T] at hj; subst hj; exact h3
    · intro j hj; simp [d1n4C] at hj; subst hj; exact h3
  by_cases h4 : (⟨4, by decide⟩ : N6) ∈ J
  swap
  · refine fin_conv (dead_bound d1n5T d1n5C (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hn hK hρ ht h4 ?_ ?_ hg hgn (hper _))
    · intro j hj; simp [d1n5T] at hj; subst hj; exact h4
    · intro j hj; simp [d1n5C] at hj; subst hj; exact h4
  by_cases h0 : (⟨0, by decide⟩ : N6) ∈ J <;> by_cases h1 : (⟨1, by decide⟩ : N6) ∈ J <;>
    by_cases h5 : (⟨5, by decide⟩ : N6) ∈ J
  · exfalso
    apply hJne
    refine Finset.eq_univ_of_forall fun j => ?_
    rcases node_cases j with rfl | rfl | rfl | rfl | rfl | rfl <;> assumption
  ·
    have hJ5 : ∀ s' : N6, s' ≠ ⟨5, by decide⟩ → s' ∈ J := by
      intro s' hs'
      rcases node_cases s' with rfl | rfl | rfl | rfl | rfl | rfl <;> first | assumption | exact absurd rfl hs'
    obtain ⟨hb1, hb2⟩ := node_bound e6n5Tab e6n5STab (smallCheck_sound _ _ _ e6n5_small)
      (prim_of_contentL e6n5Tab e6n5_prim) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hn hK hρ ht hJ5 h5 hg hgn (hper _)
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hb1 hh with ⟨b, hb, hχ⟩ | h79
      · left
        exact ⟨⟨5, by decide⟩, b, Or.inr (Or.inl rfl), hb, surv_of_node ht hJ5 h5 hχ⟩
      · right; rwa [hfin] at h79
    · have := hb2 hh; rwa [hfin] at this
  ·
    have hJ1 : ∀ s' : N6, s' ≠ ⟨1, by decide⟩ → s' ∈ J := by
      intro s' hs'
      rcases node_cases s' with rfl | rfl | rfl | rfl | rfl | rfl <;> first | assumption | exact absurd rfl hs'
    obtain ⟨hb1, hb2⟩ := node_bound e6n1Tab e6n1STab (smallCheck_sound _ _ _ e6n1_small)
      (prim_of_contentL e6n1Tab e6n1_prim) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hn hK hρ ht hJ1 h1 hg hgn (hper _)
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hb1 hh with ⟨b, hb, hχ⟩ | h79
      · left
        exact ⟨⟨1, by decide⟩, b, Or.inr (Or.inr rfl), hb, surv_of_node ht hJ1 h1 hχ⟩
      · right; rwa [hfin] at h79
    · have := hb2 hh; rwa [hfin] at this
  ·
    refine fin_conv (dead_bound d3n26T d2n2C (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hn hK hρ ht h1 ?_ ?_ hg hgn (hper _))
    · intro j hj; simp [d3n26T] at hj; rcases hj with rfl | rfl <;> assumption
    · intro j hj; simp [d2n2C] at hj; subst hj; exact h1
  ·
    have hJ0 : ∀ s' : N6, s' ≠ ⟨0, by decide⟩ → s' ∈ J := by
      intro s' hs'
      rcases node_cases s' with rfl | rfl | rfl | rfl | rfl | rfl <;> first | assumption | exact absurd rfl hs'
    obtain ⟨hb1, hb2⟩ := node_bound e6n0Tab e6n0STab (smallCheck_sound _ _ _ e6n0_small)
      (prim_of_contentL e6n0Tab e6n0_prim) (by decide +kernel) (by decide +kernel)
      (by decide +kernel) (by decide +kernel) hn hK hρ ht hJ0 h0 hg hgn (hper _)
    refine ⟨fun hh => ?_, fun hh => ?_⟩
    · rcases hb1 hh with ⟨b, hb, hχ⟩ | h79
      · left
        exact ⟨⟨0, by decide⟩, b, Or.inl rfl, hb, surv_of_node ht hJ0 h0 hχ⟩
      · right; rwa [hfin] at h79
    · have := hb2 hh; rwa [hfin] at this
  ·
    refine fin_conv (dead_bound d5n16T d5n16C (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hn hK hρ ht h0 ?_ ?_ hg hgn (hper _))
    · intro j hj; simp [d5n16T] at hj; rcases hj with rfl | rfl <;> assumption
    · intro j hj; simp [d5n16C] at hj; rcases hj with rfl | rfl <;> assumption
  ·
    refine fin_conv (dead_bound d2n12T d2n2C (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hn hK hρ ht h1 ?_ ?_ hg hgn (hper _))
    · intro j hj; simp [d2n12T] at hj; rcases hj with rfl | rfl <;> assumption
    · intro j hj; simp [d2n2C] at hj; subst hj; exact h1
  ·
    refine fin_conv (dead_bound d4n126T d2n2C (by decide +kernel) (by decide +kernel)
      (by decide +kernel) hn hK hρ ht h1 ?_ ?_ hg hgn (hper _))
    · intro j hj; simp [d4n126T] at hj; rcases hj with rfl | rfl | rfl <;> assumption
    · intro j hj; simp [d2n2C] at hj; subst hj; exact h1

end TypeBound

end CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6
