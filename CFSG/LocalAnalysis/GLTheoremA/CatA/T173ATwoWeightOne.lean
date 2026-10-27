module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoWeightOneLayer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoStdForm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoFrameSupp
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoFrameNorm
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173ATwoTransv

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173A

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.S172A.GL (fixSp comSp Nsub)
open CFSG.LocalAnalysis.GLTheoremA.T173X
  (stdLayer innerClosure stdFamily IsStdElt StdVanishes StdTyped StdExtends)
open scoped BigOperators

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]

private theorem pow_apply_of_fixed (e : V ≃ₗ[ZMod 2] V) {w : V} (hw : e w = w) (n : ℕ) :
    (e ^ n) w = w := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hw, ih]

private theorem sum_pow_apply (e : V ≃ₗ[ZMod 2] V) (n : ℕ) (v : V) :
    e (∑ i ∈ Finset.range n, (e ^ i) v) - (∑ i ∈ Finset.range n, (e ^ i) v) =
      (e ^ n) v - v := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, map_add]
      have h1 : e ((e ^ n) v) = (e ^ (n + 1)) v := by
        rw [pow_succ']
        rfl
      rw [h1]
      have h2 : e (∑ i ∈ Finset.range n, (e ^ i) v) + (e ^ (n + 1)) v -
          ((∑ i ∈ Finset.range n, (e ^ i) v) + (e ^ n) v) =
          (e (∑ i ∈ Finset.range n, (e ^ i) v) -
            (∑ i ∈ Finset.range n, (e ^ i) v)) +
            ((e ^ (n + 1)) v - (e ^ n) v) := by abel
      rw [h2, ih]
      abel

private theorem comSp_pow_le (e : V ≃ₗ[ZMod 2] V) (n : ℕ) : comSp (e ^ n) ≤ comSp e := by
  intro a ha
  rw [S172A.GL.mem_comSp] at ha ⊢
  obtain ⟨v, hv⟩ := ha
  exact ⟨∑ i ∈ Finset.range n, (e ^ i) v, by rw [sum_pow_apply e n v, hv]⟩

private theorem map_fixSp_conj (σ e : V ≃ₗ[ZMod 2] V) :
    Submodule.map σ.toLinearMap (fixSp e) = fixSp (σ * e * σ.symm) := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_map] at hv
    obtain ⟨w, hw, hfw⟩ := hv
    rw [S172A.GL.mem_fixSp] at hw ⊢
    rw [← hfw]
    change σ (e (σ.symm (σ w))) = σ w
    rw [LinearEquiv.symm_apply_apply, hw]
  · intro v hv
    rw [Submodule.mem_map]
    rw [S172A.GL.mem_fixSp] at hv
    refine ⟨σ.symm v, ?_, by simp⟩
    rw [S172A.GL.mem_fixSp]
    apply σ.injective
    change σ (e (σ.symm v)) = σ (σ.symm v)
    rw [LinearEquiv.apply_symm_apply]
    have hv' : σ (e (σ.symm v)) = v := by
      simpa only [LinearEquiv.mul_apply] using hv
    exact hv'

private theorem map_comSp_conj (σ e : V ≃ₗ[ZMod 2] V) :
    Submodule.map σ.toLinearMap (comSp e) = comSp (σ * e * σ.symm) := by
  apply le_antisymm
  · intro v hv
    rw [Submodule.mem_map] at hv
    obtain ⟨w, hw, hfw⟩ := hv
    rw [S172A.GL.mem_comSp] at hw ⊢
    obtain ⟨u, hu⟩ := hw
    refine ⟨σ u, ?_⟩
    rw [← hfw]
    change σ (e (σ.symm (σ u))) - σ u = σ w
    rw [LinearEquiv.symm_apply_apply, ← map_sub, hu]
  · intro v hv
    rw [S172A.GL.mem_comSp] at hv
    obtain ⟨u, hu⟩ := hv
    rw [Submodule.mem_map]
    refine ⟨e (σ.symm u) - σ.symm u, ?_, ?_⟩
    · rw [S172A.GL.mem_comSp]
      exact ⟨σ.symm u, rfl⟩
    · change σ (e (σ.symm u) - σ.symm u) = v
      rw [map_sub, LinearEquiv.apply_symm_apply]
      have hv' : σ (e (σ.symm u)) - u = v := by
        simpa only [LinearEquiv.mul_apply] using hu
      exact hv'

private theorem map_Nsub_conj {e e' : V ≃ₗ[ZMod 2] V} (σ : V ≃ₗ[ZMod 2] V)
    (h3 : e ^ 3 = 1) (h3' : e' ^ 3 = 1) (hconj : σ * e * σ.symm = e') :
    Subgroup.map (MulAut.conj σ).toMonoidHom (Nsub h3) = Nsub h3' := by
  have hcom : Submodule.map σ.toLinearMap (comSp e) = comSp e' := by
    rw [map_comSp_conj, hconj]
  have hfix : Submodule.map σ.toLinearMap (fixSp e) = fixSp e' := by
    rw [map_fixSp_conj, hconj]
  apply le_antisymm
  · intro h hh
    obtain ⟨h₀, hh₀, hfh⟩ := Subgroup.mem_map.1 hh
    rw [← hfh]
    change σ * h₀ * σ.symm ∈ Nsub h3'
    rw [S172A.GL.mem_Nsub] at hh₀ ⊢
    refine ⟨?_, ?_⟩
    · intro a ha
      rw [← hcom, Submodule.mem_map] at ha
      obtain ⟨b, hb, hfb⟩ := ha
      rw [← hfb]
      change σ (h₀ (σ.symm (σ b))) = σ b
      rw [LinearEquiv.symm_apply_apply, hh₀.1 b hb]
    · intro w hw
      rw [← hfix, Submodule.mem_map] at hw
      obtain ⟨b, hb, hfb⟩ := hw
      rw [← hfb]
      rw [← hfix, Submodule.mem_map]
      refine ⟨h₀ b, hh₀.2 b hb, ?_⟩
      change σ (h₀ b) = σ (h₀ (σ.symm (σ b)))
      rw [LinearEquiv.symm_apply_apply]
  · intro h hh
    rw [Subgroup.mem_map]
    refine ⟨σ.symm * h * σ, ?_, ?_⟩
    · rw [S172A.GL.mem_Nsub] at hh ⊢
      refine ⟨?_, ?_⟩
      · intro a ha
        have hσa : σ a ∈ comSp e' := by
          rw [← hcom, Submodule.mem_map]
          exact ⟨a, ha, rfl⟩
        change σ.symm (h (σ a)) = a
        rw [hh.1 (σ a) hσa, LinearEquiv.symm_apply_apply]
      · intro w hw
        have hσw : σ w ∈ fixSp e' := by
          rw [← hfix, Submodule.mem_map]
          exact ⟨w, hw, rfl⟩
        have hhσw : h (σ w) ∈ fixSp e' := hh.2 (σ w) hσw
        rw [← hfix, Submodule.mem_map] at hhσw
        obtain ⟨z, hz, hzσ⟩ := hhσw
        have hzw : σ.symm (h (σ w)) = z := by
          rw [← hzσ]
          exact σ.symm_apply_apply z
        rw [show (σ.symm * h * σ) w = σ.symm (h (σ w)) by
          simp only [LinearEquiv.mul_apply]]
        rw [hzw]
        exact hz
    · change MulAut.conj σ (σ⁻¹ * h * σ) = h
      rw [MulAut.conj_apply]
      group

theorem lin_two_weightOne_innerClosure (hV : 6 ≤ Module.finrank (ZMod 2) V)
    {A : Subgroup (V ≃ₗ[ZMod 2] V)} {g : V ≃ₗ[ZMod 2] V} (hA : GLAIsBmax 3 A)
    (hg : IsStdElt 3 A g) (h2 : Module.finrank (ZMod 2) (comSp g) = 2) :
    innerClosure A g = ⊤ := by
  obtain ⟨hgA, -, hg3, -, -⟩ := hg
  obtain ⟨x, P, V0, hF⟩ :=
    lin_two_std_form_of_bmax (by omega : 3 ≤ Module.finrank (ZMod 2) V) hA
  have hr : 3 ≤ Module.finrank (ZMod 2) V / 2 := by omega
  obtain ⟨i₀, k, hgk⟩ := lin_two_frame_weightOne hF hgA h2
  have hfrE : Module.finrank (ZMod 2) (comSp (x i₀)) = 2 := by
    rw [hF.2.2.2.2.1 i₀, hF.2.2.1 i₀]
  have hcomle : comSp g ≤ comSp (x i₀) := by
    rw [hgk]
    exact comSp_pow_le (x i₀) k
  have hcom : comSp g = comSp (x i₀) :=
    Submodule.eq_of_le_of_finrank_eq hcomle (by rw [h2, hfrE])
  have hfixle : fixSp (x i₀) ≤ fixSp g := by
    intro w hw
    rw [S172A.GL.mem_fixSp] at hw
    rw [S172A.GL.mem_fixSp, hgk]
    exact pow_apply_of_fixed (x i₀) hw k
  have hfrfix : Module.finrank (ZMod 2) (fixSp (x i₀)) =
      Module.finrank (ZMod 2) (fixSp g) := by
    have h1 := S172A.GL.finrank_fixSp (hF.2.2.2.1 i₀)
    have h2' := S172A.GL.finrank_fixSp hg3
    rw [hcom] at h2'
    omega
  have hfix : fixSp (x i₀) = fixSp g := Submodule.eq_of_le_of_finrank_eq hfixle hfrfix
  have hNsub : Nsub hg3 = Nsub (hF.2.2.2.1 i₀) := by
    apply le_antisymm
    · intro h hh
      rw [S172A.GL.mem_Nsub] at hh ⊢
      rw [← hcom, hfix]
      exact hh
    · intro h hh
      rw [S172A.GL.mem_Nsub] at hh ⊢
      rw [hcom, ← hfix]
      exact hh
  unfold innerClosure
  rw [lin_two_weightOne_layer (by omega : 5 ≤ Module.finrank (ZMod 2) V) hg3 h2]
  rw [eq_top_iff, ← lin_two_nsub_generate hF hr]
  apply iSup_le
  intro j
  by_cases hij : j = i₀
  · subst hij
    rw [← hNsub]
    exact le_closureIn_self _ _
  · have hji : i₀ ≠ j := fun h => hij h.symm
    obtain ⟨σ, hσN, hσconj, -, -⟩ := lin_two_frame_swap hF i₀ j hji
    have hmapN : GLBConj σ⁻¹ (Nsub hg3) = Nsub (hF.2.2.2.1 j) := by
      rw [GLBConj, inv_inv, hNsub,
        map_Nsub_conj σ (hF.2.2.2.1 i₀) (hF.2.2.2.1 j) hσconj]
    rw [← hmapN, closureIn_eq_iSup_gLBConj]
    exact le_biSup (fun n => GLBConj n (Nsub hg3)) (Subgroup.inv_mem _ hσN)

end CFSG.LocalAnalysis.GLTheoremA.T173A

end
