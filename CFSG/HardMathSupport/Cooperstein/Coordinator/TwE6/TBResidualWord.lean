module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.AdjDispTorus
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors.TwE6Rep27

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Minuscule CFSG.HardMathSupport.Cooperstein.Coordinator.Survivors
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))


@[expose] def nWord (l : List (Fin TwistTag.E6.foldedTag.rank)) : ↥(TwistedE6.fixedGroup K σ) :=
  (l.map fun a => (twistedE6CoverData hf hK σ hσ).nhat a).prod
@[expose] def wordIdx (l : List (Fin TwistTag.E6.foldedTag.rank)) (b : Fin e6Data.d) : Fin e6Data.d :=
  l.foldr (fun a b => (TwistTag.E6.orbitWord a).foldr (fun i b => e6Data_valid.sRefl i b) b) b
@[expose] def idx1 : Fin e6Data.d := e6Data_valid.sRefl ⟨0, by decide⟩ ⟨0, by decide⟩
@[expose] def lwIdx : Fin e6Data.d := ⟨26, by decide⟩
@[expose] def lw1Idx : Fin e6Data.d := e6Data_valid.sRefl ⟨5, by decide⟩ lwIdx

private def tw27n0 : Fin Tag.E6.rank := ⟨0, by decide⟩

private def tw27n5 : Fin Tag.E6.rank := ⟨5, by decide⟩

private def tw27v0 : Fin e6Data.d := ⟨0, by decide⟩

private theorem tw27_isSign_eq_one {ε : K} (h : IsSign ε) : ε = 1 := by
  rcases h with h | h
  · exact h
  · rw [h]
    exact CharTwo.neg_eq 1

private theorem tw27_nhat_single (a : Fin TwistTag.E6.foldedTag.rank) (b : Fin e6Data.d) :
    twRep27 σ ((twistedE6CoverData hf hK σ hσ).nhat a) (Finsupp.single b 1) =
      Finsupp.single ((TwistTag.E6.orbitWord a).foldr (fun i b => e6Data_valid.sRefl i b) b) 1 := by
  obtain ⟨ε, hε, hε'⟩ := minRep_prod_nm_single e6Data_valid (K := K) (TwistTag.E6.orbitWord a) b
  have hnc : twRep27 σ ((twistedE6CoverData hf hK σ hσ).nhat a) (Finsupp.single b 1) =
      ε • Finsupp.single ((TwistTag.E6.orbitWord a).foldr (fun i b => e6Data_valid.sRefl i b) b) 1 := by
    rw [twRep27_apply, nhat_coe hf hK σ hσ a, minOrbitHom_WSL]
    exact hε'
  rw [hnc, tw27_isSign_eq_one hε, one_smul]

theorem twRep27_nWord_single (l : List (Fin TwistTag.E6.foldedTag.rank)) (b : Fin e6Data.d) :
    twRep27 σ (nWord hf hK σ hσ l) (Finsupp.single b 1) = Finsupp.single (wordIdx l b) 1 := by
  induction l with
  | nil => simp [nWord, wordIdx]
  | cons a l ih =>
    have hn : nWord hf hK σ hσ (a :: l) =
        (twistedE6CoverData hf hK σ hσ).nhat a * nWord hf hK σ hσ l := by
      simp [nWord]
    rw [hn, map_mul, Module.End.mul_apply, ih, tw27_nhat_single]
    rfl

private theorem tw27_nWord_single_coeff (l : List (Fin TwistTag.E6.foldedTag.rank))
    (b : Fin e6Data.d) (c : K) :
    twRep27 σ (nWord hf hK σ hσ l) (Finsupp.single b c) = Finsupp.single (wordIdx l b) c := by
  rw [← Finsupp.smul_single_one b c, map_smul, twRep27_nWord_single, Finsupp.smul_single_one]

private theorem tw27_nWord_e6Y27 (l : List (Fin TwistTag.E6.foldedTag.rank)) :
    twRep27 σ (nWord hf hK σ hσ l) (e6Y27 : Fin e6Data.d →₀ K) =
      Finsupp.single (wordIdx l ⟨0, by decide⟩) 1 :=
  twRep27_nWord_single hf hK σ hσ l ⟨0, by decide⟩

private theorem tw27_minOrbitHom_vSL (c : orbitField TwistTag.E6 K σ twN0) :
    minOrbitHom σ twN0 (vSL c) =
      e6Data_valid.xm K (-Pi.single tw27n0 1) (c : K) *
        e6Data_valid.xm K (-Pi.single tw27n5 1) (σ (c : K)) := by
  have hp0 : (TwistTag.E6.perm ^ 0) (TwistTag.E6.orbitMin twN0) = tw27n0 := Fin.ext (by decide)
  have hp1 : (TwistTag.E6.perm ^ 1) (TwistTag.E6.orbitMin twN0) = tw27n5 := Fin.ext (by decide)
  rw [minOrbitHom_vSL, orbit_card_twN0, show List.range 2 = [0, 1] from rfl]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, hp0, hp1]
  simp only [pow_zero, pow_one, RingHom.coe_one, id_eq]
  rfl

private theorem tw27_hatY_eq (c : orbitField TwistTag.E6 K σ twN0) (x : Fin e6Data.d →₀ K) :
    twRep27 σ (hatY hf hK σ hσ twN0 c) x =
      (1 + (c : K) • e6Data.rootOp K (-Pi.single tw27n0 1))
        ((1 + σ (c : K) • e6Data.rootOp K (-Pi.single tw27n5 1)) x) := by
  rw [twRep27_apply]
  change minRep e6Data_valid K (minOrbitHom σ twN0 (vSL c)) x = _
  rw [tw27_minOrbitHom_vSL, map_mul, Module.End.mul_apply, minRep_xm, minRep_xm]

private theorem tw27_hatY_e6Y27 (c : orbitField TwistTag.E6 K σ twN0) :
    twRep27 σ (hatY hf hK σ hσ twN0 c) (e6Y27 : Fin e6Data.d →₀ K) =
      (e6Y27 : Fin e6Data.d →₀ K) + Finsupp.single idx1 (c : K) := by
  have h5 : e6Data.rootOp K (-Pi.single tw27n5 1) (e6Y27 : Fin e6Data.d →₀ K) = 0 := by
    have hw : e6Data.wt tw27v0 tw27n5 ≠ 1 := by decide +kernel
    show e6Data.rootOp K (-Pi.single tw27n5 1) (Finsupp.single tw27v0 1) = 0
    rw [e6Data_valid.rootOp_neg_single_apply (R := K), if_neg hw]
  have h0 : e6Data.rootOp K (-Pi.single tw27n0 1) (e6Y27 : Fin e6Data.d →₀ K) =
      Finsupp.single idx1 1 := by
    have hw : e6Data.wt tw27v0 tw27n0 = 1 := by decide +kernel
    show e6Data.rootOp K (-Pi.single tw27n0 1) (Finsupp.single tw27v0 1) =
      Finsupp.single idx1 1
    rw [e6Data_valid.rootOp_neg_single_apply (R := K), if_pos hw]
    rfl
  rw [tw27_hatY_eq hf hK σ hσ c]
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, h5, h0, smul_zero,
    add_zero, Finsupp.smul_single_one]

theorem twRep27_point (l : List (Fin TwistTag.E6.foldedTag.rank))
    (c : orbitField TwistTag.E6 K σ twN0) :
    twRep27 σ (nWord hf hK σ hσ l * hatY hf hK σ hσ twN0 c) (e6Y27 : Fin e6Data.d →₀ K) =
      Finsupp.single (wordIdx l ⟨0, by decide⟩) 1 + Finsupp.single (wordIdx l idx1) (c : K) := by
  rw [map_mul, Module.End.mul_apply, tw27_hatY_e6Y27 hf hK σ hσ c, map_add,
    tw27_nWord_e6Y27 hf hK σ hσ l, tw27_nWord_single_coeff hf hK σ hσ l idx1 (c : K)]

private theorem tw27_e0_no_lw (b : Fin e6Data.d) (h : e6Data.wt b tw27n0 = 1) :
    e6Data_valid.sRefl tw27n0 b ≠ lwIdx := by
  intro h'
  have h1 := e6Data_valid.wt_sRefl_self tw27n0 b
  rw [h', h] at h1
  have h0 : e6Data.wt lwIdx tw27n0 = 0 := by decide +kernel
  rw [h0] at h1
  norm_num at h1

private theorem tw27_rootOp_neg_e0_lw (w : Fin e6Data.d →₀ K) :
    e6Data.rootOp K (-Pi.single tw27n0 1) w lwIdx = 0 := by
  induction w using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [map_add, hu, hv]
  | single b c =>
    rw [← Finsupp.smul_single_one b c, map_smul, e6Data_valid.rootOp_neg_single_apply (R := K)]
    by_cases hb : e6Data.wt b tw27n0 = 1
    · rw [if_pos hb, Finsupp.smul_apply, Finsupp.single_apply, if_neg (tw27_e0_no_lw b hb),
        smul_zero]
    · rw [if_neg hb]
      simp

private theorem tw27_lw1_eq : lw1Idx = e6Data_valid.sRefl tw27n5 lwIdx := rfl

private theorem tw27_sRefl5_iff (b : Fin e6Data.d) :
    e6Data_valid.sRefl tw27n5 b = lwIdx ↔ b = lw1Idx := by
  constructor
  · intro h
    rw [tw27_lw1_eq, ← h, e6Data_valid.sRefl_sRefl]
  · intro h
    rw [h, tw27_lw1_eq, e6Data_valid.sRefl_sRefl]

private theorem tw27_rootOp_neg_e5_lw (x : Fin e6Data.d →₀ K) :
    e6Data.rootOp K (-Pi.single tw27n5 1) x lwIdx = x lw1Idx := by
  have hwl : e6Data.wt lwIdx tw27n5 = -1 := by decide +kernel
  have hw1 : e6Data.wt lw1Idx tw27n5 = 1 := by
    simp only [tw27_lw1_eq, e6Data_valid.wt_sRefl_self, hwl, neg_neg]
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [map_add, hu, hv]
  | single b c =>
    rw [← Finsupp.smul_single_one b c, map_smul, e6Data_valid.rootOp_neg_single_apply (R := K)]
    by_cases hb : e6Data.wt b tw27n5 = 1
    · rw [if_pos hb]
      simp only [Finsupp.smul_apply, Finsupp.single_apply, tw27_sRefl5_iff]
    · have hne : b ≠ lw1Idx := fun e => hb (by rw [e]; exact hw1)
      rw [if_neg hb]
      simp [Finsupp.single_apply, hne]

private theorem tw27_hatY_lw (c : orbitField TwistTag.E6 K σ twN0) (x : Fin e6Data.d →₀ K) :
    twRep27 σ (hatY hf hK σ hσ twN0 c) x lwIdx = x lwIdx + σ (c : K) * x lw1Idx := by
  rw [tw27_hatY_eq hf hK σ hσ c]
  simp only [LinearMap.add_apply, Module.End.one_apply, LinearMap.smul_apply, Finsupp.add_apply,
    Finsupp.smul_apply, smul_eq_mul, tw27_rootOp_neg_e0_lw, tw27_rootOp_neg_e5_lw, smul_zero,
    mul_zero, add_zero]

private theorem tw27_injective_foldr (L : List (Fin TwistTag.E6.tag.rank)) :
    Function.Injective
      (fun x : Fin e6Data.d => L.foldr (fun i b => e6Data_valid.sRefl i b) x) := by
  induction L with
  | nil => exact fun a b h => h
  | cons i L ih => exact (e6Data_valid.sRefl_injective i).comp ih

private theorem tw27_wordIdx_injective (l : List (Fin TwistTag.E6.foldedTag.rank)) :
    Function.Injective (wordIdx l) := by
  induction l with
  | nil => exact fun a b h => h
  | cons a l ih => exact (tw27_injective_foldr (TwistTag.E6.orbitWord a)).comp ih

private theorem tw27_iff_wordIdx {l l' : List (Fin TwistTag.E6.foldedTag.rank)}
    {a p u : Fin e6Data.d} (ha : wordIdx l a = wordIdx l' p) :
    a = u ↔ wordIdx l u = wordIdx l' p :=
  ⟨fun h => by rw [← ha, h], fun h => (tw27_wordIdx_injective l (h.trans ha.symm)).symm⟩

private theorem tw27_perm_coord {π : Fin e6Data.d → Fin e6Data.d} (hπ : Function.Injective π)
    (g : ↥(TwistedE6.fixedGroup K σ))
    (hg : ∀ b, twRep27 σ g (Finsupp.single b 1) = Finsupp.single (π b) 1)
    (z : Fin e6Data.d →₀ K) (a : Fin e6Data.d) : twRep27 σ g z (π a) = z a := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add u v hu hv => simp [map_add, hu, hv]
  | single b c =>
    rw [← Finsupp.smul_single_one b c, map_smul, hg]
    by_cases hba : b = a
    · subst hba
      simp
    · have hne : π b ≠ π a := fun e => hba (hπ e)
      simp [Finsupp.single_apply, hba, hne]

open Classical in
theorem twChi27_entry (w0 : List (Fin TwistTag.E6.foldedTag.rank))
    (hw0 : wordIdx w0 lwIdx = ⟨0, by decide⟩)
    (l l' : List (Fin TwistTag.E6.foldedTag.rank)) (c c' : orbitField TwistTag.E6 K σ twN0) :
    twChi27 σ (nWord hf hK σ hσ w0 * (nWord hf hK σ hσ l * hatY hf hK σ hσ twN0 c)⁻¹ *
        (nWord hf hK σ hσ l' * hatY hf hK σ hσ twN0 c')) =
      (if wordIdx l lwIdx = wordIdx l' ⟨0, by decide⟩ then 1 else 0) +
      (c' : K) * (if wordIdx l lwIdx = wordIdx l' idx1 then 1 else 0) +
      σ (c : K) * ((if wordIdx l lw1Idx = wordIdx l' ⟨0, by decide⟩ then 1 else 0) +
        (c' : K) * (if wordIdx l lw1Idx = wordIdx l' idx1 then 1 else 0)) := by
  obtain ⟨a, ha⟩ : ∃ a : Fin e6Data.d, wordIdx l a = wordIdx l' ⟨0, by decide⟩ :=
    Finite.surjective_of_injective (tw27_wordIdx_injective l) _
  obtain ⟨b, hb⟩ : ∃ b : Fin e6Data.d, wordIdx l b = wordIdx l' idx1 :=
    Finite.surjective_of_injective (tw27_wordIdx_injective l) _
  obtain ⟨x, hx_def⟩ : ∃ x : Fin e6Data.d →₀ K,
      x = Finsupp.single a 1 + Finsupp.single b (c' : K) := ⟨_, rfl⟩
  have hx : twRep27 σ (nWord hf hK σ hσ l) x =
      Finsupp.single (wordIdx l' ⟨0, by decide⟩) 1 + Finsupp.single (wordIdx l' idx1) (c' : K) := by
    rw [hx_def, map_add, twRep27_nWord_single, tw27_nWord_single_coeff, ha, hb]
  have hinv : ∀ v, twRep27 σ (hatY hf hK σ hσ twN0 c)
      (twRep27 σ (hatY hf hK σ hσ twN0 c) v) = v := by
    intro v
    rw [← Module.End.mul_apply, ← map_mul, ← pow_two, hatY_sq hf hK σ hσ twN0 c, map_one,
      Module.End.one_apply]
  have hyB : twRep27 σ (nWord hf hK σ hσ l * hatY hf hK σ hσ twN0 c)
      (twRep27 σ (hatY hf hK σ hσ twN0 c) x) =
      twRep27 σ (nWord hf hK σ hσ l' * hatY hf hK σ hσ twN0 c') (e6Y27 : Fin e6Data.d →₀ K) := by
    rw [twRep27_point hf hK σ hσ l' c', map_mul, Module.End.mul_apply, hinv, hx]
  have hBinv : twRep27 σ (nWord hf hK σ hσ l * hatY hf hK σ hσ twN0 c)⁻¹
      (twRep27 σ (nWord hf hK σ hσ l' * hatY hf hK σ hσ twN0 c') (e6Y27 : Fin e6Data.d →₀ K)) =
      twRep27 σ (hatY hf hK σ hσ twN0 c) x := by
    rw [← hyB, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hw := tw27_perm_coord σ (tw27_wordIdx_injective w0) (nWord hf hK σ hσ w0)
    (twRep27_nWord_single hf hK σ hσ w0) (twRep27 σ (hatY hf hK σ hσ twN0 c) x) lwIdx
  rw [hw0] at hw
  have ea0 := tw27_iff_wordIdx (u := lwIdx) ha
  have eb0 := tw27_iff_wordIdx (u := lwIdx) hb
  have ea1 := tw27_iff_wordIdx (u := lw1Idx) ha
  have eb1 := tw27_iff_wordIdx (u := lw1Idx) hb
  unfold twChi27
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hBinv, hw,
    tw27_hatY_lw hf hK σ hσ c x, hx_def]
  simp only [Finsupp.add_apply, Finsupp.single_apply, ea0, eb0, ea1, eb1, mul_ite, mul_one,
    mul_zero]

end CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6
