module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFB0Dat
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFD6
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3S22ESup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3Pf11Main
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3WFB0Lift

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section B0Main




variable {n : ℕ}


variable {n : ℕ}

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K K' K₃ : Subgroup Y} {u₁ u₂ u₃ : Y} {K₄ W : Subgroup Y}

theorem twist_mul {x x' y y' : Y} (ht2 : t * t = 1) (hty : t * y = y * t)
    (hx : x' = x ∨ x' = x * t) (hy : y' = y ∨ y' = y * t) :
    x' * y' = x * y ∨ x' * y' = x * y * t := by
  rcases hx with hx | hx <;> rcases hy with hy | hy <;> rw [hx, hy]
  · exact Or.inl rfl
  · exact Or.inr (mul_assoc _ _ _).symm
  · right
    calc x * t * y = x * (t * y) := mul_assoc _ _ _
      _ = x * (y * t) := by rw [hty]
      _ = x * y * t := (mul_assoc _ _ _).symm
  · left
    calc x * t * (y * t) = x * (t * y) * t := by group
      _ = x * (y * t) * t := by rw [hty]
      _ = x * y * (t * t) := by group
      _ = x * y := by rw [ht2, mul_one]

theorem prod4_twist {b b' : Fin 4 → Y} (ht2 : t * t = 1) (htc : ∀ i, t * b i = b i * t)
    (hb : ∀ i, b' i = b i ∨ b' i = b i * t) :
    b' 0 * b' 1 * b' 2 * b' 3 = b 0 * b 1 * b 2 * b 3 ∨
      b' 0 * b' 1 * b' 2 * b' 3 = b 0 * b 1 * b 2 * b 3 * t := by
  have h1 := twist_mul ht2 (htc 1) (hb 0) (hb 1)
  have h2 := twist_mul ht2 (htc 2) h1 (hb 2)
  exact twist_mul ht2 (htc 3) h2 (hb 3)

theorem WFIn.frameInv_twist (h : WFIn n R S t K K' K₃ u₁ u₂ u₃ K₄ W) {W' : Subgroup Y}
    (hW' : W' ∈ WSet (CoreAssembly.conjClass (tightCore R))) {s s' : Y}
    (hs : s ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W')
    (hs' : s' ∈ FrameInv (CoreAssembly.conjClass (tightCore R)) K W') : s' = s ∨ s' = s * t := by
  obtain ⟨M, a, y, hfr⟩ := h.exists_frame
  obtain ⟨b, hb, rfl⟩ := hfr.frameInv_canonical h hW' hs
  obtain ⟨b', hb', rfl⟩ := hfr.frameInv_canonical h hW' hs'
  have hab := Q3.Q3T6.abelian_of_mem_WSet3 h.hyp hW'
  exact prod4_twist (h.q8 (hfr.mem 0)).z_sq
    (fun i => (h.q8 (hfr.mem i)).z_central _ (hb i).1)
    (fun i => eq_or_mul_t_of_comm (h.q8 (hfr.mem i)) (hb i).1 (hb' i).1 (hb i).2.2 (hb' i).2.2
      (hab _ (hb i).2.1 _ (hb' i).2.1))

theorem wfB0_of_facts (hcit : CIT3Below n) (hP : CFSG.ClassicalInvolution.Q3.TL4.TightBelowRPlus 3 n)
    (h4 : Thm4RTwinBelow 3 n) (h5 : V3Fourth n) (h7 : V3Alpha13 n) : WFB0 n := by
  intro Y _ _ R S t K K' K₃ u₁ u₂ u₃ K₄ W h W' hW' htW' L hL L' hL' hne a ha a' ha' oa oa' s hs
  have hStd := h.hStd
  have hd := hStd.datum
  have h2g := h.exit.2.2.2.1
  have hTri := v3Tri_of_thm4 hcit hP h4
  have hzL := h.uniqInv hL
  have hzL' := h.uniqInv hL'
  have hLsyl : IsSylow2In L L := ⟨le_rfl, h2g L hL.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have hL'syl : IsSylow2In L' L' :=
    ⟨le_rfl, h2g L' hL'.1, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨L₃, w, hd''⟩ := hd.exists_datum_of_pair hL hL' (Ne.symm hne) hLsyl hL'syl
    (h.comm hL hL' hne) ha.1 ha'.1 oa oa'
  have hStd'' : V3Std n Y R S t L L' L₃ a a' w :=
    ⟨hStd.perp, hStd.two, hStd.exit, hd'', hStd.wyl⟩
  obtain ⟨K₄', hF⟩ := h5 Y R S t L L' L₃ a a' w hStd''
  have hα := h7 Y R S t L L' L₃ a a' w hStd'' K₄' hF (hTri Y R S t L L' L₃ a a' w hStd'' K₄' hF)
  obtain ⟨V, hV⟩ := h.uniq W' hW' L hL L' hL' hne a ha a' ha' oa oa'
  have hΩ := h.hyp
  have hc2 : IsPGroup 2 (Subgroup.zpowers (a * a')) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd''.sq_12
  have hmem3 : L₃ ∈ Q3NL.tqMembers3 (CoreAssembly.conjClass (tightCore R)) (a * a') :=
    tq_of_hyp22G hd''
  have hno : ¬ SecNoExitAt (CoreAssembly.conjClass (tightCore R)) (a * a') := by
    intro hNo
    have hNo' : NoExit _ (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) := hNo
    obtain ⟨htC, htY, hinv⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2 hmem3 hd''.hzK₃
    have hVW : V ∈ WSet (TwinDisc.secFam (CoreAssembly.conjClass (tightCore R)) (a * a')) := by
      rw [hV]; exact Set.mem_singleton V
    have hV2 : IsPGroup 2 V := Thompson.isPGroup_of_mem_WSet hVW
    have hVn : V.Normal := TwinPerp23.W.wset_normal (TwinDisc.hypOmegaGen_secFam hΩ hc2) hV
    obtain ⟨W₀, hW₀, hzW⟩ := TwinPerp.wz_of_hypOmegaGen (TwinDisc.hypOmegaGen_secFam hΩ hc2)
      (TwinDisc.secImg_mem_secFam hmem3) hinv
    rw [hV] at hW₀
    have hW₀V : W₀ = V := hW₀
    rw [hW₀V] at hzW
    exact (hNo' _ (TwinDisc.secImg_mem_secFam hmem3) _ hinv).2.1 ⟨V, hVn, hV2, hzW⟩
  have hin : V3ExitIn n R S t L L' L₃ a a' w K₄' := ⟨hStd'', hF, hα, h2g, hno⟩
  have hLD := twin_mem_DSet h.partI h2g hW' htW' hL.1 hzL
  have hL'D := twin_mem_DSet h.partI h2g hW' htW' hL'.1 hzL'
  have hL₃D := twin_mem_DSet h.partI h2g hW' htW' hd''.hK₃.1 hd''.hzK₃
  obtain ⟨z₀, j, hz₀, hKlein⟩ := v3_secKlein hin hW' hLD hL'D hL₃D ha.2 ha'.2 hV
  have hcent : ∀ m ∈ oddCoreOf (Subgroup.centralizer ({a * a'} : Set Y)), m * t = t * m := by
    intro m hm
    have hle : ⁅oddCoreOf (Subgroup.centralizer ({a * a'} : Set Y)),
        Subgroup.closure ({a * a', t} : Set Y)⁆ ≤
        alphaOf (Subgroup.closure ({a * a', t} : Set Y)) :=
      le_sup_of_le_left (le_iSup₂_of_le (a * a') (Subgroup.subset_closure (by simp))
        (le_iSup_of_le hd''.mul_ne_one le_rfl))
    have h1 : ⁅m, t⁆ ∈ alphaOf (Subgroup.closure ({a * a', t} : Set Y)) :=
      hle (Subgroup.commutator_mem_commutator hm (Subgroup.subset_closure (by simp)))
    rw [hα, Subgroup.mem_bot, commutatorElement_def] at h1
    calc m * t = (m * t * m⁻¹ * t⁻¹) * (t * m) := by group
      _ = t * m := by rw [h1, one_mul]
  obtain ⟨y, hyC, hyF⟩ := h.exists_fuse_pair hW' htW' hL hL' hne ha ha' oa oa'
  obtain ⟨M, a_, y_, hfr⟩ := h.exists_frame
  obtain ⟨bf, hbf, hfeq⟩ := hfr.frameInv_canonical h hW' hyF
  obtain ⟨-, hft, -, hfne, -⟩ := hfr.frame_basic h hbf
  rw [← hfeq] at hft hfne
  have hlift := lift_conj_involution hΩ hc2 hmem3 hd''.hzK₃ hcent hyC hft hfne z₀ j hz₀ hKlein
  have htw := h.frameInv_twist hW' hs hyF
  have ht2 : t * t = 1 := (h.q8 (hfr.mem 0)).z_sq
  have htS : t ∈ Subgroup.closure ({t, s} : Set Y) := Subgroup.subset_closure (by simp)
  have hsS : s ∈ Subgroup.closure ({t, s} : Set Y) := Subgroup.subset_closure (by simp)
  have hs1S : y * t * y⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) := by
    rcases htw with e | e
    · rw [e]; exact hsS
    · rw [e]; exact Subgroup.mul_mem _ hsS htS
  have hconjT : ∀ c ∈ Subgroup.centralizer ({a * a'} : Set Y),
      c * t * c⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) := by
    intro c hc
    rcases hlift c hc with e | e | e
    · rw [e]; exact htS
    · rw [e]; exact hs1S
    · rw [e]; exact Subgroup.mul_mem _ htS hs1S
  have hconjS : ∀ c ∈ Subgroup.centralizer ({a * a'} : Set Y),
      c * s * c⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) := by
    intro c hc
    have hy' : c * (y * t * y⁻¹) * c⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) := by
      have := hconjT (c * y) (Subgroup.mul_mem _ hc hyC)
      have e : c * y * t * (c * y)⁻¹ = c * (y * t * y⁻¹) * c⁻¹ := by group
      rwa [e] at this
    rcases htw with e | e
    · rw [e] at hy'
      exact hy'
    · have hs_eq : s = (y * t * y⁻¹) * t := by rw [e, mul_assoc, ht2, mul_one]
      have e2 : c * s * c⁻¹ = (c * (y * t * y⁻¹) * c⁻¹) * (c * t * c⁻¹) := by
        rw [hs_eq]
        group
      rw [e2]
      exact Subgroup.mul_mem _ hy' (hconjT c hc)
  have hconj : ∀ c ∈ Subgroup.centralizer ({a * a'} : Set Y),
      ∀ x ∈ Subgroup.closure ({t, s} : Set Y), c * x * c⁻¹ ∈ Subgroup.closure ({t, s} : Set Y) := by
    intro c hc x hx
    refine Subgroup.closure_induction (p := fun x _ => c * x * c⁻¹ ∈ Subgroup.closure ({t, s} : Set Y))
      ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hx with rfl | rfl
      · exact hconjT c hc
      · exact hconjS c hc
    · simpa using Subgroup.one_mem _
    · intro x x' _ _ hx hx'
      have e : c * (x * x') * c⁻¹ = (c * x * c⁻¹) * (c * x' * c⁻¹) := by group
      rw [e]
      exact Subgroup.mul_mem _ hx hx'
    · intro x _ hx
      have e : c * x⁻¹ * c⁻¹ = (c * x * c⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hx
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hconj c hc x hx
  · intro hx
    have := hconj c⁻¹ (Subgroup.inv_mem _ hc) _ hx
    simpa [mul_assoc] using this

end B0Main

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
