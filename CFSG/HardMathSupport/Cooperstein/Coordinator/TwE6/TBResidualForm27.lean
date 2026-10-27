module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.TwE6Rep27
public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.Interfaces

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))


private theorem form27_minRep_xm_neg (i : Fin TwistTag.E6.tag.rank) (c : K) :
    minRep e6Data_valid K (e6Data_valid.xm K (-Pi.single i 1) c) =
      1 + c • e6Data.rootOp K (-Pi.single i 1) :=
  minRep_xm e6Data_valid _ c

private theorem form27_rootOp_neg_single_apply (i : Fin TwistTag.E6.tag.rank) (a : Fin e6Data.d) :
    e6Data.rootOp K (-Pi.single i 1) (Finsupp.single a 1) =
      if e6Data.wt a i = 1 then Finsupp.single (e6Data_valid.sRefl i a) 1 else 0 :=
  e6Data_valid.rootOp_neg_single_apply _ _

private theorem form27_wt_sRefl (i : Fin TwistTag.E6.tag.rank) (a : Fin e6Data.d) :
    e6Data.wt (e6Data_valid.sRefl i a : ℕ) i = -e6Data.wt a i :=
  e6Data_valid.wt_sRefl_self _ _

private theorem form27_sRefl_sRefl (i : Fin TwistTag.E6.tag.rank) (a : Fin e6Data.d) :
    e6Data_valid.sRefl i (e6Data_valid.sRefl i a) = a :=
  e6Data_valid.sRefl_sRefl _ _

private theorem form27_minRep_vSL_card_one (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 1) (c : orbitField TwistTag.E6 K σ a) :
    minRep e6Data_valid K (minOrbitHom σ a (vSL c)) =
      minRep e6Data_valid K (e6Data_valid.xm K (-Pi.single (TwistTag.E6.orbitMin a) 1) (c : K)) := by
  rw [minOrbitHom_vSL, ha]
  simp

private theorem form27_minRep_vSL_card_two (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 2) (c : orbitField TwistTag.E6 K σ a) :
    minRep e6Data_valid K (minOrbitHom σ a (vSL c)) =
      minRep e6Data_valid K (e6Data_valid.xm K (-Pi.single (TwistTag.E6.orbitMin a) 1) (c : K)) *
        minRep e6Data_valid K
          (e6Data_valid.xm K (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) (σ (c : K))) := by
  rw [minOrbitHom_vSL, ha]
  simp [List.range_succ, map_mul]

private theorem form27_vSL_two_apply (a : Fin TwistTag.E6.foldedTag.rank)
    (ha : (TwistTag.E6.orbit a).card = 2) (c : orbitField TwistTag.E6 K σ a)
    (w : Fin e6Data.d →₀ K) :
    minRep e6Data_valid K (minOrbitHom σ a (vSL c)) w - w =
      (c : K) • e6Data.rootOp K (-Pi.single (TwistTag.E6.orbitMin a) 1) w +
        σ (c : K) • e6Data.rootOp K (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) w +
        ((c : K) * σ (c : K)) • e6Data.rootOp K (-Pi.single (TwistTag.E6.orbitMin a) 1)
          (e6Data.rootOp K (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) w) := by
  rw [form27_minRep_vSL_card_two σ a ha, Module.End.mul_apply, form27_minRep_xm_neg,
    form27_minRep_xm_neg]
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, map_add, map_smul,
    smul_add, smul_smul, mul_comm (σ (c : K)) (c : K)]
  abel

include hf hK hσ in
private theorem form27_rootOp_neg_mem (a : Fin TwistTag.E6.foldedTag.rank)
    (S : Submodule K (Fin e6Data.d →₀ K)) (w : Fin e6Data.d →₀ K)
    (hw : ∀ c : orbitField TwistTag.E6 K σ a,
      minRep e6Data_valid K (minOrbitHom σ a (vSL c)) w - w ∈ S)
    {i : Fin TwistTag.E6.tag.rank} (hi : i ∈ TwistTag.E6.orbit a) :
    e6Data.rootOp K (-Pi.single i 1) w ∈ S := by
  rcases orbit_card_one_or_two a with ha | ha
  · have hi' : i = TwistTag.E6.orbitMin a := by
      have := orbit_one_data a ha
      rw [this, Finset.mem_singleton] at hi
      exact hi
    have h1 := hw 1
    rw [form27_minRep_vSL_card_one σ a ha, form27_minRep_xm_neg] at h1
    simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply] at h1
    rw [hi']
    simpa using h1
  · obtain ⟨-, hset⟩ := orbit_two_data a ha
    obtain ⟨hfin, hcard⟩ := natCard_eq_q_sq_fintype hK
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have hmem : ∀ c : K, c ∈ orbitField TwistTag.E6 K σ a := fun c => by
      rw [mem_orbitField, ha]
      simp only [pow_two, RingHom.mul_def, RingHom.id_apply]
      exact sigma_sigma_eq hK σ hσ c
    have key := mem_of_forall_poly hq hcard S σ hσ
      (e6Data.rootOp K (-Pi.single (TwistTag.E6.orbitMin a) 1) w)
      (e6Data.rootOp K (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) w)
      (e6Data.rootOp K (-Pi.single (TwistTag.E6.orbitMin a) 1)
        (e6Data.rootOp K (-Pi.single (TwistTag.E6.perm (TwistTag.E6.orbitMin a)) 1) w))
      (fun c => by
        have h1 := hw ⟨c, hmem c⟩
        rw [form27_vSL_two_apply σ a ha] at h1
        exact h1)
    rw [hset] at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact key.1
    · exact key.2.1

include hf hK hσ in
private theorem form27_rootOp_neg_apply {f₂₇ : Module.Dual K (Fin e6Data.d →₀ K)}
    (hf₂₇ : ∀ z ∈ augSub (twRep27 σ) (twistedE6CoverData hf hK σ hσ).datum.L, f₂₇ z = 0)
    (i : Fin TwistTag.E6.tag.rank) (w : Fin e6Data.d →₀ K) :
    f₂₇ (e6Data.rootOp K (-Pi.single i 1) w) = 0 := by
  refine LinearMap.mem_ker.1 (form27_rootOp_neg_mem hf hK σ hσ (TwistTag.E6.orbitIndex i)
    (LinearMap.ker f₂₇) w (fun c => ?_) (mem_orbit_orbitIndex' i))
  rw [LinearMap.mem_ker]
  apply hf₂₇
  have hY : hatY hf hK σ hσ (TwistTag.E6.orbitIndex i) c ∈
      (twistedE6CoverData hf hK σ hσ).datum.L :=
    (twistedE6CoverRankOne hf hK σ hσ).y_mem (TwistTag.E6.orbitIndex i) c
  have h := sub_mem_augSub (twRep27 σ) hY w
  rw [twRep27_apply] at h
  exact h

include hf hK hσ in
private theorem form27_apply_single_eq_zero {f₂₇ : Module.Dual K (Fin e6Data.d →₀ K)}
    (hf₂₇ : ∀ z ∈ augSub (twRep27 σ) (twistedE6CoverData hf hK σ hσ).datum.L, f₂₇ z = 0)
    (b : Fin e6Data.d) (hb : b ≠ ⟨0, by decide⟩) :
    f₂₇ (Finsupp.single b 1) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i : Fin TwistTag.E6.tag.rank, e6Data.wt b i = -1 := by
    by_contra h
    push Not at h
    exact hb (e6_dominant b h)
  have h := form27_rootOp_neg_apply hf hK σ hσ hf₂₇ i (Finsupp.single (e6Data_valid.sRefl i b) 1)
  rw [form27_rootOp_neg_single_apply] at h
  have hw : e6Data.wt (e6Data_valid.sRefl i b : ℕ) i = 1 := by
    rw [form27_wt_sRefl, hi]
    norm_num
  rw [if_pos hw, form27_sRefl_sRefl] at h
  exact h

theorem form27_eq_coord {f₂₇ : Module.Dual K (Fin e6Data.d →₀ K)}
    (hf₂₇ : ∀ z ∈ augSub (twRep27 σ) (twistedE6CoverData hf hK σ hσ).datum.L, f₂₇ z = 0)
    (h1 : f₂₇ (e6Y27 : Fin e6Data.d →₀ K) = 1) (v : Fin e6Data.d →₀ K) :
    f₂₇ v = v ⟨0, by decide⟩ := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add g k hg hk => rw [map_add, hg, hk, Finsupp.add_apply]
  | single b c =>
    have hsingle : f₂₇ (Finsupp.single b c) = c * f₂₇ (Finsupp.single b 1) := by
      rw [← Finsupp.smul_single_one b c, map_smul, smul_eq_mul]
    rw [hsingle, Finsupp.single_apply]
    by_cases hb : b = ⟨0, by decide⟩
    · subst hb
      have h0 : f₂₇ (Finsupp.single (⟨0, by decide⟩ : Fin e6Data.d) (1 : K)) = 1 := h1
      rw [h0, mul_one, if_pos rfl]
    · rw [form27_apply_single_eq_zero hf hK σ hσ hf₂₇ b hb, mul_zero, if_neg hb]

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
