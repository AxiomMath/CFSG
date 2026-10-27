module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfCent
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinTargets
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinPfShared
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThinTail

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC CFSG.ClassicalInvolution.Q3.TC.Graph
  CFSG.ClassicalInvolution.Q3.TC.Thin
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3.AE

set_option linter.unusedSectionVars false

namespace TwinThin

@[expose] def ThinKerOdd (IH : Prop) (m : ℕ) (𝒜 : Set (Finset (Fin m))) (H : Subgroup (AEQ m)) :
    Prop :=
  IH → ∀ (G : Type) [Group G] [Finite G] (K₀ K K' : Subgroup G) (z : G) (π : Set (Subgroup G))
    (g : G), Setting K₀ K K' z π g → IsSimpleGroup ↥(genFittingFStar G) →
    (∃ a b : ↥(genFittingFStar G), a * b ≠ b * a) →
    ∀ (I : AEIdentOn (fam K (conjSub g (piGen π))) m 𝒜 H)
      (zS : ↥(pSpan (fam K (conjSub g (piGen π))))), (zS : G) = z →
      ∀ k ∈ I.φ.ker, k ∈ Subgroup.closure
        {w : ↥(pSpan (fam K (conjSub g (piGen π)))) | w * zS = zS * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1}

variable {G : Type} [Group G] [Finite G] {K₀ K K' : Subgroup G} {z : G} {π : Set (Subgroup G)}
  {g : G}

namespace Setting

variable (S : Setting K₀ K K' z π g)
include S

theorem false_of_model {m : ℕ} {𝒜 : Set (Finset (Fin m))} {H : Subgroup (AEQ m)} (hm : 5 ≤ m)
    (I : AEIdentOn (fam K (conjSub g (piGen π))) m 𝒜 H)
    (h37 : ∀ Q : Set (Subgroup G), AEIdentOn Q m 𝒜 H → ∀ {y : G},
      y ∈ Subgroup.normalizer (pSpan Q : Set G) → (∃ a : ℕ, y ^ 3 ^ a = 1) → ∀ {L : Subgroup G},
        L ∈ Q → (∀ l ∈ L, y * l = l * y) → (∀ L' ∈ Q, ∃ x ∈ pSpan Q, conjSub x L = L') →
          ∀ x ∈ pSpan Q, y * x = x * y)
    (hCl : TwinThinPf.OddClosure H 𝒜)
    (hKer : ∀ (zS : ↥(pSpan (fam K (conjSub g (piGen π))))), (zS : G) = z →
      ∀ k ∈ I.φ.ker, k ∈ Subgroup.closure
        {w : ↥(pSpan (fam K (conjSub g (piGen π)))) | w * zS = zS * w ∧
          ∃ a : ℕ, w ^ 3 ^ a = 1}) : False := by
  have hP : pSpan (fam K (conjSub g (piGen π))) = conjSub g (piGen π) := S.fam_gen
  have hO : classicalInvolutionOddCore ↥(pSpan (fam K (conjSub g (piGen π)))) = ⊥ := by
    rw [hP]; exact S.hO
  set J := I.toLabel with hJ
  have hk : IsPGroup 2 J.φ.ker := J.isPGroup_ker hO
  have hc8 : ∀ L ∈ fam K (conjSub g (piGen π)), Nat.card L = 8 := fun L hL =>
    S.card8 L (fam_subset S.hos.graph S.hK hL)
  obtain ⟨α, hα, h4, b, hlabK⟩ := I.label K S.mem_fam_self
  have hzS : z ∈ pSpan (fam K (conjSub g (piGen π))) := le_pSpan S.mem_fam_self S.hz.mem
  set zS : ↥(pSpan (fam K (conjSub g (piGen π)))) := ⟨z, hzS⟩ with hzSdef
  have hzmap : J.φ zS = zBar α h4 :=
    phi_map_eq_zBar J.φ hm S.mem_fam_self (hc8 K S.mem_fam_self) hlabK S.hz
  let T : Subgroup ↥(pSpan (fam K (conjSub g (piGen π)))) := Subgroup.closure
    {w | w * zS = zS * w ∧ ∃ a : ℕ, w ^ 3 ^ a = 1}
  have hTc : ∀ w ∈ T, ∀ x ∈ piGen π, x * (w : G) = (w : G) * x := by
    intro w hw
    have hle : T ≤ (Subgroup.centralizer (piGen π : Set G)).comap
        (pSpan (fam K (conjSub g (piGen π)))).subtype := by
      refine Subgroup.closure_le _ |>.mpr ?_
      rintro w ⟨hwz, a, hwa⟩
      have hwX : (w : G) ∈ conjSub g (piGen π) := by
        exact (SetLike.ext_iff.mp hP (w : G)).mp w.2
      have hwz' : (w : G) * z = z * (w : G) := congrArg Subtype.val hwz
      have := S.centralizes_of_three I h37 hwX hwz' ⟨a, by
        have := congrArg Subtype.val hwa
        simpa using this⟩
      intro x hx
      exact (this x hx).symm
    intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hw) x hx
  have hmodel : ∀ β ∈ 𝒜, ∀ h4' : β.card = 4, zBar β h4' ∈ T.map J.φ := by
    intro β hβ h4'
    have h1 := hCl α hα h4 β hβ h4'
    refine (Subgroup.closure_le (T.map J.φ)).mpr ?_ h1
    rintro x ⟨hxH, hxc, hx3⟩
    have hxr : x ∈ J.φ.range := by
      rw [show J.φ = I.φ from rfl, I.range_eq]; exact hxH
    obtain ⟨y, hyx, a, hya⟩ := J.exists_lift_pow_three hxr hx3
    refine ⟨y, Subgroup.subset_closure ⟨?_, a, hya⟩, hyx⟩
    refine J.comm_of_pow_three hk hya ?_
    rw [hyx, hzmap]
    exact hxc
  refine S.false_of_cent fun L hL u hu x hx => ?_
  obtain ⟨β, hβ, h4', b', hlab'⟩ := I.label L hL
  have hu' : J.φ ⟨u, le_pSpan hL hu.mem⟩ = zBar β h4' :=
    phi_map_eq_zBar J.φ hm hL (hc8 L hL) hlab' hu
  obtain ⟨t, htT, hte⟩ := hmodel β hβ h4'
  have hker : t⁻¹ * ⟨u, le_pSpan hL hu.mem⟩ ∈ J.φ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hte, hu', inv_mul_cancel]
  have hkT : t⁻¹ * ⟨u, le_pSpan hL hu.mem⟩ ∈ T := hKer zS rfl _ hker
  have huT : (⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan (fam K (conjSub g (piGen π))))) ∈ T := by
    have := T.mul_mem htT hkT
    simpa using this
  exact hTc _ huT x hx

end Setting

theorem thinE64_of_targets {IH : Prop} (hFix : TwinThinPf.FixTrivial AE.e64Sub AE.e64Sets)
    (hCl : TwinThinPf.OddClosure AE.e64Sub AE.e64Sets)
    (hKer : ThinKerOdd IH 7 AE.e64Sets AE.e64Sub) : ThinE64 IH :=
  fun hIH G _ _ K₀ K K' z π g S hS hnab ⟨I⟩ =>
    S.false_of_model (by norm_num) I
      (fun Q I' _ hy hy3 _ hL hyL htr => TwinThinPf.centralizes_of_e64 I' hFix hy hy3 hL hyL htr)
      hCl (hKer hIH G K₀ K K' z π g S hS hnab I)

end TwinThin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
