module

public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThreeOrbits
public import CFSG.HardMathSupport.Lang.Triality.TraceKernel
public import CFSG.HardMathSupport.Lang.E27Lie.TrialityThreeLayers

public noncomputable section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Lang.E27Lie

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Lang.Triality


variable {K : Type} [Field K] [Finite K]

theorem twistHom_pinnedX_sign (t : TwistTag) (σ : K →+* K) {γ : Fin t.tag.rank → ℤ}
    (hγ : IsRoot t.tag γ) :
    ∃ ε : K, ε * ε = 1 ∧ ∀ c : K, twistHom t K σ (pinnedX t.tag K γ c) =
      pinnedX t.tag K (permLattice t.perm γ) (ε * σ c) := by
  obtain ⟨ε, he, hε⟩ := diagramMap_conj_pinnedX (K := K) t hγ
  refine ⟨ε, he, fun c => ?_⟩
  have h1 : twistHom t K σ (pinnedX t.tag K γ c) =
      diagramMap t K * Units.map (entrywiseHom σ) (pinnedX t.tag K γ c) * (diagramMap t K)⁻¹ :=
    rfl
  rw [h1, show Units.map (entrywiseHom σ) (pinnedX t.tag K γ c) = pinnedX t.tag K γ (σ c) from
    Units.ext (entrywise_pinnedX σ γ c), hε]

theorem rootCoord_fixedRoot (t : TwistTag) (σ : K →+* K) {α : Fin t.tag.rank → ℤ}
    (hα : IsRoot t.tag α ∧ 0 < height α) (hρα : permLattice t.perm α = α)
    {x : ModGL t.tag K} (hx : x ∈ heightSeries t.tag K (height α))
    (hxF : twistHom t K σ x = x) :
    ∃ ε : K, ε * ε = 1 ∧ rootCoord hα x = ε * σ (rootCoord hα x) := by
  have hα' : IsRoot t.tag (permLattice t.perm α) ∧ 0 < height (permLattice t.perm α) :=
    ⟨hα.1.permLattice t.cartan_perm, by rw [height_permLattice]; exact hα.2⟩
  obtain ⟨ε', hε'⟩ := rootCoord_twistHom t σ hα hα'
  obtain ⟨ε₀, he₀, hF₀⟩ := twistHom_pinnedX_sign t σ hα.1
  have hmem1 : pinnedX t.tag K α 1 ∈ heightSeries t.tag K (height α) :=
    pinnedX_mem_heightSeries_height hα 1
  have hε'1 : ε' = ε₀ := by
    have h1 := hε' _ hmem1
    rw [hF₀ 1, rootCoord_self hα', rootCoord_self hα, map_one, mul_one, mul_one] at h1
    exact h1.symm
  refine ⟨ε', hε'1 ▸ he₀, ?_⟩
  have h2 := hε' x hx
  rw [hxF] at h2
  have e : rootCoord hα x = rootCoord hα' x := rootCoord_congr t hρα.symm hα hα'
  rw [e] at h2 ⊢
  exact h2

theorem card_traceKer (σ : K ≃+* K) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hK : Nat.card K = Nat.card {c : K // σ c = c} ^ 3) :
    Nat.card {c : K // c + σ c + σ (σ c) = 0} = Nat.card {c : K // σ c = c} ^ 2 := by
  classical
  set q := Nat.card {c : K // σ c = c} with hq
  have hσ3c : ∀ c, σ (σ (σ c)) = c := fun c => by
    have := congrArg (fun e : K ≃+* K => e c) hσ3
    simpa [pow_succ] using this
  let f := CFSG.HardMathSupport.Lang.Triality.subHom σ
  have hker : Nat.card f.ker = q := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    show c ∈ f.ker ↔ σ c = c
    rw [AddMonoidHom.mem_ker, CFSG.HardMathSupport.Lang.Triality.subHom_apply]
    exact sub_eq_zero
  have hrange : Nat.card {c : K // c + σ c + σ (σ c) = 0} = Nat.card f.range := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun c => ?_)
    show _ ↔ c ∈ f.range
    rw [AddMonoidHom.mem_range]
    constructor
    · intro h
      obtain ⟨d, hd⟩ := CFSG.HardMathSupport.Lang.Triality.exists_sub_of_trace_eq_zero σ hσ3 hσ1
        hK c h
      exact ⟨d, by rw [CFSG.HardMathSupport.Lang.Triality.subHom_apply]; exact hd.symm⟩
    · rintro ⟨d, rfl⟩
      rw [CFSG.HardMathSupport.Lang.Triality.subHom_apply]
      simp only [map_sub, hσ3c]
      ring
  have hmul := AddSubgroup.card_ker_mul_card_range f
  haveI : Nonempty {c : K // σ c = c} := ⟨⟨0, map_zero σ⟩⟩
  have hqpos : 0 < q := Nat.card_pos
  rw [hker, hK] at hmul
  rw [hrange]
  have : q * Nat.card f.range = q * q ^ 2 := by rw [hmul]; ring
  exact Nat.eq_of_mul_eq_mul_left hqpos this

theorem card_box {I : Type} [Fintype I] (P : I → K → Prop) :
    Nat.card {a : Multiplicative (I → K) // ∀ O, P O (Multiplicative.toAdd a O)} =
      ∏ O, Nat.card {c : K // P O c} := by
  rw [← Nat.card_pi]
  refine Nat.card_congr
    { toFun := fun a O => ⟨Multiplicative.toAdd a.1 O, a.2 O⟩
      invFun := fun f => ⟨Multiplicative.ofAdd (fun O => (f O).1), fun O => (f O).2⟩
      left_inv := fun a => by ext; rfl
      right_inv := fun f => by funext O; rfl }

theorem permLattice_mem_diagramOrbit (t : TwistTag) (α : Fin t.tag.rank → ℤ) :
    permLattice t.perm α ∈ t.diagramOrbit α :=
  (t.mem_diagramOrbit).2 ⟨t.perm, Subgroup.mem_zpowers _, rfl⟩

open Classical in
noncomputable def coordPred (σ : K ≃+* K) (O : Finset D4Vec) (c : K) : Prop :=
  if O.card = 1 then σ c = c else c + σ c + σ (σ c) = 0

variable (σ : K ≃+* K)

theorem coord_ok {k : ℕ} (a : LayerCoord (K := K) k) (ha : a ∈ (layerPhi σ k).range)
    (hT : a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1)
    (O : ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ))) :
    coordPred σ O.1 (Multiplicative.toAdd a O) := by
  classical
  obtain ⟨x, rfl⟩ := ha
  have hrep := repOf_spec TwistTag.D4 ((k + 1 : ℕ) : ℤ) O
  have hα : IsRoot TwistTag.D4.tag (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) ∧
      0 < height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) :=
    ⟨hrep.1, by rw [hrep.2.1]; positivity⟩
  have hc : Multiplicative.toAdd (layerPhi σ k x) O =
      rootCoord hα ((x : ↥(graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) :
        ModGL TwistTag.D4.tag K) := rfl
  have hTc : Multiplicative.toAdd (layerPhi σ k x) O +
      σ (Multiplicative.toAdd (layerPhi σ k x) O) +
      σ (σ (Multiplicative.toAdd (layerPhi σ k x) O)) = 0 := by
    have := congrArg (fun b : LayerCoord (K := K) k => Multiplicative.toAdd b O) hT
    simpa [layerTau, toAdd_mul] using this
  unfold coordPred
  split_ifs with hcard
  ·
    have hρ : permLattice TwistTag.D4.perm (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O) =
        repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O := by
      have h1 := permLattice_mem_diagramOrbit TwistTag.D4
        (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)
      have h2 := TwistTag.D4.self_mem_diagramOrbit (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)
      rw [hrep.2.2] at h1 h2
      exact Finset.card_le_one.1 hcard.le _ h1 _ h2
    have hxΓ : twistHom TwistTag.D4 K σ.toRingHom (x : ModGL TwistTag.D4.tag K) = x :=
      ((mem_twistedFixedGroup_iff_twistHom _ _ _).1
        (graphFixedRootGroup_le TwistTag.D4 K σ.toRingHom x.1.2)).2
    have hxh : (x : ModGL TwistTag.D4.tag K) ∈ heightSeries TwistTag.D4.tag K
        (height (repOf TwistTag.D4 ((k + 1 : ℕ) : ℤ) O)) :=
      mem_heightSeries_of_height_eq TwistTag.D4 hrep.2.1 x.2
    obtain ⟨ε, hε, hcε⟩ := rootCoord_fixedRoot TwistTag.D4 σ.toRingHom hα hρ hxh hxΓ
    rw [hc] at hTc ⊢
    set c := rootCoord hα (x : ModGL TwistTag.D4.tag K) with hcdef
    have hcε' : c = ε * σ c := hcε
    rcases mul_self_eq_one_iff.1 hε with h1 | h1
    · rw [h1, one_mul] at hcε'
      exact hcε'.symm
    · rw [h1, neg_one_mul] at hcε'
      have hσc : σ c = -c := by linear_combination hcε'
      have hσσ : σ (σ c) = c := by rw [hσc, map_neg, hσc, neg_neg]
      rw [hσσ, hσc] at hTc
      have : c = 0 := by linear_combination hTc
      rw [hσc, this]; simp
  · rw [hc] at hTc ⊢
    exact hTc

theorem layer_bound (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1)
    (hK : Nat.card K = Nat.card {c : K // σ c = c} ^ 3) (k : ℕ) :
    Nat.card {a : LayerCoord (K := K) k // a ∈ (layerPhi σ k).range ∧
        a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1} ≤
      Nat.card {c : K // σ c = c} ^
        ∑ O ∈ orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ), orbitWeight O := by
  classical
  set q := Nat.card {c : K // σ c = c} with hq
  set I := ↥(orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)) with hI
  have hle : Nat.card {a : LayerCoord (K := K) k // a ∈ (layerPhi σ k).range ∧
        a * layerTau σ k a * layerTau σ k (layerTau σ k a) = 1} ≤
      Nat.card {a : Multiplicative (I → K) // ∀ O : I, coordPred σ O.1 (Multiplicative.toAdd a O)} :=
    Nat.card_le_card_of_injective (fun a => ⟨a.1, coord_ok σ a.1 a.2.1 a.2.2⟩) (fun x y h => by
      have h' := congrArg (fun z : {a : Multiplicative (I → K) //
        ∀ O : I, coordPred σ O.1 (Multiplicative.toAdd a O)} => (z : Multiplicative (I → K))) h
      exact Subtype.ext h')
  have hbox := card_box (K := K) (fun (O : I) c => coordPred σ O.1 c)
  have hfac : ∀ O : I, Nat.card {c : K // coordPred σ O.1 c} = q ^ orbitWeight O.1 := by
    intro O
    unfold coordPred orbitWeight
    by_cases hc : O.1.card = 1
    · simp only [hc, if_true, pow_one]
      exact hq.symm
    · simp only [hc, if_false]
      exact card_traceKer σ hσ3 hσ1 hK
  rw [hbox] at hle
  refine hle.trans (le_of_eq ?_)
  rw [Finset.prod_congr rfl fun O _ => hfac O, Finset.prod_pow_eq_pow_sum, Finset.sum_coe_sort
    (orbitsAt TwistTag.D4 ((k + 1 : ℕ) : ℤ)) (fun O => orbitWeight O)]

end CFSG.HardMathSupport.Lang.E27Lie
