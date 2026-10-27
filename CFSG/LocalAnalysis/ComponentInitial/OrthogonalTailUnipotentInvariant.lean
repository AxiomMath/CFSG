module

public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailParameterKernels
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailSubspaceCount

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin Module
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit

variable {K : Type*} [Field K] {A : Type*} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A}

section Action

theorem eichler_inl_tail_mem_tailUnipotent (i : Fin r) (b : A) :
    eichler (quadTail r qA) (hypVec K A (.inl i)) ((0 : Fin r ⊕ Fin r → K), b) ∈
      tailUnipotent r qA :=
  tailRootGroup_le_tailUnipotent (Or.inl ⟨i, rfl⟩) (mem_tailRootGroup_eps.2 ⟨b, rfl⟩)

theorem tailLongElt_mem_tailUnipotent {β : Fin r → ℤ} (hβ : β ∈ posRoots r) (t : K) :
    tailLongElt r qA β t ∈ tailUnipotent r qA :=
  tailRootGroup_le_tailUnipotent (Or.inr hβ)
    ((mem_tailRootGroup_long (posRoots_subset_roots hβ)).2 ⟨t, rfl⟩)

theorem eichler_inl_tail_apply (i : Fin r) (b : A) (w : (Fin r ⊕ Fin r → K) × A) :
    eichler (quadTail r qA) (hypVec K A (.inl i)) ((0 : Fin r ⊕ Fin r → K), b) w =
      w + w.1 (.inr i) • ((0 : Fin r ⊕ Fin r → K), b) -
        (polar (quadTail r qA) w ((0 : Fin r ⊕ Fin r → K), b) + qA b * w.1 (.inr i)) •
          hypVec K A (.inl i) := by
  rw [eichler_apply (quadTail_hypVec _) (polar_hypVec_tail _ _), polar_hypVec, quadTail_tail]
  rfl

theorem tailLongElt_sub_apply {i j : Fin r} (hij : i < j) (w : (Fin r ⊕ Fin r → K) × A) :
    tailLongElt r qA (eps r i - eps r j) 1 w =
      w + w.1 (.inr i) • ((-1 : K) • hypVec K A (.inr j)) -
        (-w.1 (.inl j)) • hypVec K A (.inl i) := by
  have hw : polar (quadTail r qA) (hypVec K A (.inl i)) ((-1 : K) • hypVec K A (.inr j)) = 0 := by
    rw [polar_smul_right_eq, polar_hypVec_hypVec]
    simp [hij.ne']
  rw [tailLongElt_eps_sub_eps hij, eichler_apply (quadTail_hypVec _) hw, polar_hypVec,
    polar_smul_right_eq, polar_hypVec, QuadraticMap.map_smul, quadTail_hypVec]
  simp

theorem quadTail_eq_of_inr_eq_zero {w : (Fin r ⊕ Fin r → K) × A} (hw : ∀ j, w.1 (.inr j) = 0) :
    quadTail r qA w = qA w.2 := by
  rw [quadTail_apply, quadPlus_apply, Finset.sum_eq_zero fun j _ => by rw [hw j, mul_zero],
    zero_add]

end Action

section Fixed

theorem tailUnipotent_le_stabilizer (hr : 1 ≤ r) :
    tailUnipotent r qA ≤ MulAction.stabilizer
      (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A))
      (hypVec K A (.inl ⟨0, hr⟩)) := by
  refine iSup₂_le fun β hβ => ?_
  rcases hβ with ⟨i, rfl⟩ | hlong
  · rintro _ hx
    obtain ⟨b, rfl⟩ := mem_tailRootGroup_eps.1 hx
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def,
      eichler_inl_apply_hypVec_inl (polar_hypVec_tail _ _)]
    simp
  · rintro _ hx
    obtain ⟨t, rfl⟩ := (mem_tailRootGroup_long (posRoots_subset_roots hlong)).1 hx
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def]
    obtain ⟨a, b, hab, rfl | rfl⟩ := hlong
    · have hb0 : b ≠ ⟨0, hr⟩ := fun h => by
        rw [h, Fin.lt_def] at hab
        exact Nat.not_lt_zero _ hab
      have hw : polar (quadTail r qA) (hypVec K A (.inl a)) ((-t) • hypVec K A (.inr b)) = 0 := by
        rw [polar_smul_right_eq, polar_hypVec_hypVec]
        simp [hab.ne']
      rw [tailLongElt_eps_sub_eps hab, eichler_inl_apply_hypVec_inl hw]
      simp [hypVec, Ne.symm hb0]
    · have hw : polar (quadTail r qA) (hypVec K A (.inl a)) ((-t) • hypVec K A (.inl b)) = 0 := by
        rw [polar_smul_right_eq, polar_hypVec_hypVec]
        simp
      rw [tailLongElt_eps_add_eps hab, eichler_inl_apply_hypVec_inl hw]
      simp [hypVec]

theorem fixed_tailUnipotent_eq (hr : 1 ≤ r) (hreg : (polarBilin qA).Nondegenerate)
    (hA : ∃ a : A, a ≠ 0) :
    {v : (Fin r ⊕ Fin r → K) × A | ∀ u ∈ tailUnipotent r qA, u v = v} =
      ((K ∙ hypVec K A (.inl ⟨0, hr⟩) : Submodule K _) : Set ((Fin r ⊕ Fin r → K) × A)) := by
  obtain ⟨b, hb⟩ := hA
  ext v
  change (∀ u ∈ tailUnipotent r qA, u v = v) ↔ v ∈ K ∙ hypVec K A (.inl ⟨0, hr⟩)
  constructor
  · intro hv
    have hy : ∀ i, v.1 (.inr i) = 0 := fun i => by
      have h := congrArg Prod.snd (hv _ (eichler_inl_tail_mem_tailUnipotent (qA := qA) i b))
      rw [eichler_inl_tail_apply] at h
      simp only [Prod.snd_sub, Prod.snd_add, Prod.smul_snd, hypVec, smul_zero, sub_zero,
        add_eq_left] at h
      exact (smul_eq_zero.1 h).resolve_right hb
    have ha : v.2 = 0 := by
      refine eq_zero_of_polar_eq_zero hreg fun c => ?_
      have h := congrArg (fun w : (Fin r ⊕ Fin r → K) × A => w.1 (.inl ⟨0, hr⟩))
        (hv _ (eichler_inl_tail_mem_tailUnipotent (qA := qA) ⟨0, hr⟩ c))
      simp only [eichler_inl_tail_apply, hy, polar_quadTail, polar_zero_right] at h
      simpa [hypVec] using h
    have hx : ∀ j : Fin r, j ≠ ⟨0, hr⟩ → v.1 (.inl j) = 0 := fun j hj => by
      have h0j : (⟨0, hr⟩ : Fin r) < j := by
        rw [Fin.lt_def]
        rw [Ne, Fin.ext_iff] at hj
        simp only at hj ⊢
        omega
      have h := congrArg (fun w : (Fin r ⊕ Fin r → K) × A => w.1 (.inl ⟨0, hr⟩))
        (hv _ (tailLongElt_mem_tailUnipotent (qA := qA) ⟨⟨0, hr⟩, j, h0j, Or.inl rfl⟩ 1))
      simp only [tailLongElt_sub_apply h0j, hy] at h
      simpa [hypVec] using h
    refine Submodule.mem_span_singleton.2 ⟨v.1 (.inl ⟨0, hr⟩), Prod.ext (funext fun c => ?_) ?_⟩
    · rcases c with j | j
      · by_cases hj : j = ⟨0, hr⟩
        · subst hj
          simp [hypVec]
        · simp [hypVec, hj, hx j hj]
      · simp [hypVec, hy j]
    · simp [hypVec, ha]
  · intro hv
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hv
    intro u hu
    have h := tailUnipotent_le_stabilizer hr hu
    rw [MulAction.mem_stabilizer_iff, LinearEquiv.smul_def] at h
    rw [map_smul, h]

end Fixed

section Invariant

variable {W : Submodule K ((Fin r ⊕ Fin r → K) × A)}

theorem inr_eq_zero_of_invariant (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0)
    (hWs : ∀ w ∈ W, quadTail r qA w = 0)
    (hWinv : ∀ u ∈ tailUnipotent r qA,
      W.map (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ≤ W)
    {w : (Fin r ⊕ Fin r → K) × A} (hw : w ∈ W) (i : Fin r) : w.1 (.inr i) = 0 := by
  obtain ⟨b, hb⟩ := hA
  have hu := eichler_inl_tail_mem_tailUnipotent (qA := qA) i b
  have huw := hWinv _ hu ⟨w, hw, rfl⟩
  have hz := hWs _ (W.sub_mem huw hw)
  rw [LinearEquiv.coe_coe] at hz
  have hz1 : ∀ j, (eichler (quadTail r qA) (hypVec K A (.inl i)) ((0 : Fin r ⊕ Fin r → K), b) w -
      w).1 (.inr j) = 0 := fun j => by
    rw [eichler_inl_tail_apply]
    simp [hypVec]
  have hz2 : (eichler (quadTail r qA) (hypVec K A (.inl i)) ((0 : Fin r ⊕ Fin r → K), b) w -
      w).2 = w.1 (.inr i) • b := by
    rw [eichler_inl_tail_apply]
    simp [hypVec]
  rw [quadTail_eq_of_inr_eq_zero hz1, hz2] at hz
  exact (smul_eq_zero.1 (hani _ hz)).resolve_right hb

theorem snd_eq_zero_of_invariant (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0)
    (hWs : ∀ w ∈ W, quadTail r qA w = 0)
    (hWinv : ∀ u ∈ tailUnipotent r qA,
      W.map (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ≤ W)
    {w : (Fin r ⊕ Fin r → K) × A} (hw : w ∈ W) : w.2 = 0 := by
  have h := hWs w hw
  rw [quadTail_eq_of_inr_eq_zero (inr_eq_zero_of_invariant hani hA hWs hWinv hw)] at h
  exact hani _ h

variable [FiniteDimensional K A]

theorem eq_tailFlag_of_invariant (hani : qA.Anisotropic) (hA : ∃ a : A, a ≠ 0) (hW0 : W ≠ ⊥)
    (hWs : ∀ w ∈ W, quadTail r qA w = 0)
    (hWinv : ∀ u ∈ tailUnipotent r qA,
      W.map (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ≤ W) :
    ∃ k, 1 ≤ k ∧ k ≤ r ∧ W = tailFlag K A r k := by
  classical
  have hy := fun (w : (Fin r ⊕ Fin r → K) × A) (hw : w ∈ W) (i : Fin r) =>
    inr_eq_zero_of_invariant hani hA hWs hWinv hw i
  have ha := fun (w : (Fin r ⊕ Fin r → K) × A) (hw : w ∈ W) =>
    snd_eq_zero_of_invariant hani hA hWs hWinv hw
  have hP : ∃ n, ∀ w ∈ W, ∀ j : Fin r, n ≤ j.val → w.1 (.inl j) = 0 :=
    ⟨r, fun w _ j hj => absurd j.isLt (by omega)⟩
  have hPm := Nat.find_spec hP
  have hle : W ≤ tailFlag K A r (Nat.find hP) := fun w hw =>
    mem_tailFlag_iff.2 ⟨mem_flag.2 ⟨hy w hw, hPm w hw⟩, ha w hw⟩
  have hm1 : 1 ≤ Nat.find hP := by
    by_contra h0
    have hm0 : Nat.find hP = 0 := by omega
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    rw [Submodule.mem_bot]
    refine Prod.ext (funext fun c => ?_) (ha w hw)
    rcases c with j | j
    · exact hPm w hw j (by omega)
    · exact hy w hw j
  have hmr : Nat.find hP ≤ r := Nat.find_min' hP fun w _ j hj => absurd j.isLt (by omega)
  have hnot := Nat.find_min hP (show Nat.find hP - 1 < Nat.find hP by omega)
  simp only [not_forall, exists_prop] at hnot
  obtain ⟨w, hw, j, hj, hwj⟩ := hnot
  have hjm : j.val = Nat.find hP - 1 := by
    by_contra h
    exact hwj (hPm w hw j (by omega))
  have hF : tailFlag K A r (Nat.find hP - 1) ≤ W := by
    rw [tailFlag, Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    have hij : i < j := by
      rw [Fin.lt_def]
      have : i.val < Nat.find hP - 1 := hi
      omega
    have hR := hWinv _ (tailLongElt_mem_tailUnipotent (qA := qA) ⟨i, j, hij, Or.inl rfl⟩ 1)
      ⟨w, hw, rfl⟩
    rw [LinearEquiv.coe_coe] at hR
    have hdiff : tailLongElt r qA (eps r i - eps r j) 1 w - w =
        w.1 (.inl j) • hypVec K A (.inl i) := by
      rw [tailLongElt_sub_apply hij, hy w hw i]
      simp
    have h := W.smul_mem (w.1 (.inl j))⁻¹ (W.sub_mem hR hw)
    rw [hdiff, smul_smul, inv_mul_cancel₀ hwj, one_smul] at h
    exact h
  have hwF : w ∉ tailFlag K A r (Nat.find hP - 1) := fun h =>
    hwj ((mem_flag.1 (mem_tailFlag_iff.1 h).1).2 j (by omega))
  have hlt : tailFlag K A r (Nat.find hP - 1) < W :=
    lt_of_le_of_ne hF fun h => hwF (by rw [h]; exact hw)
  have h1 := Submodule.finrank_lt_finrank_of_lt hlt
  have h2 := Submodule.finrank_mono hle
  rw [finrank_tailFlag (by omega)] at h1 h2
  refine ⟨Nat.find hP, hm1, hmr, Submodule.eq_of_le_of_finrank_eq hle ?_⟩
  rw [finrank_tailFlag hmr]
  omega

theorem map_tailFlag_of_mem_tailUnipotent (hani : qA.Anisotropic) {k : ℕ} (hk : k ≤ r)
    {u : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)}
    (hu : u ∈ tailUnipotent r qA) :
    (tailFlag K A r k).map (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] _) = tailFlag K A r k := by
  rcases Nat.eq_zero_or_pos k with h0 | hpos
  · subst h0
    rw [tailFlag_zero, Submodule.map_bot]
  · exact (mem_tailBorel.1 (tailUnipotent_le_tailBorel hani hu)).2 k hpos hk

omit [FiniteDimensional K A] in
theorem tailFlag_mem_singularFlags :
    (fun i : Fin r => tailFlag K A r (i + 1)) ∈ singularFlags (quadTail r qA) r :=
  ⟨fun i => finrank_tailFlag (by omega), fun i j hij => Submodule.span_mono
    (Set.image_mono fun l (hl : l.val < i.val + 1) =>
      show l.val < j.val + 1 by have := Fin.le_def.1 hij; omega),
    fun _ _ hx => quadTail_eq_zero_of_mem_tailFlag hx⟩

end Invariant


theorem orthogonal_geometry_tail_unipotent_invariant_singular_subspaces {K : Type*} [Field K]
    {A : Type*} [AddCommGroup A] [Module K A] [FiniteDimensional K A] {r : ℕ} (hr : 1 ≤ r)
    {qA : QuadraticForm K A} (hani : qA.Anisotropic) (hreg : (polarBilin qA).Nondegenerate)
    (hA : ∃ a : A, a ≠ 0) :
    {v : (Fin r ⊕ Fin r → K) × A | ∀ u ∈ tailUnipotent r qA, u v = v} =
        ((K ∙ hypVec K A (.inl ⟨0, hr⟩) : Submodule K _) : Set ((Fin r ⊕ Fin r → K) × A)) ∧
    (∀ W : Submodule K ((Fin r ⊕ Fin r → K) × A), W ≠ ⊥ → (∀ w ∈ W, quadTail r qA w = 0) →
      (∀ u ∈ tailUnipotent r qA,
        W.map (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) ≤ W) →
      ∃ k, 1 ≤ k ∧ k ≤ r ∧ W = tailFlag K A r k) ∧
    (∀ k, 1 ≤ k → k ≤ r → tailFlag K A r k ≠ ⊥ ∧
      (∀ w ∈ tailFlag K A r k, quadTail r qA w = 0) ∧
      ∀ u ∈ tailUnipotent r qA,
        (tailFlag K A r k).map (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) =
          tailFlag K A r k) ∧
    (fun i : Fin r => tailFlag K A r (i + 1)) ∈ singularFlags (quadTail r qA) r ∧
    ∀ W ∈ singularFlags (quadTail r qA) r,
      (∀ i, ∀ u ∈ tailUnipotent r qA,
        (W i).map (u : ((Fin r ⊕ Fin r → K) × A) →ₗ[K] ((Fin r ⊕ Fin r → K) × A)) = W i) ↔
      ∀ i, W i = tailFlag K A r (i + 1) := by
  refine ⟨fixed_tailUnipotent_eq hr hreg hA, fun W hW0 hWs hWinv =>
    eq_tailFlag_of_invariant hani hA hW0 hWs hWinv, fun k hk hkr => ⟨fun h => ?_,
      fun _ hx => quadTail_eq_zero_of_mem_tailFlag hx,
      fun u hu => map_tailFlag_of_mem_tailUnipotent hani hkr hu⟩, tailFlag_mem_singularFlags,
    fun W hW => ⟨fun hinv i => ?_, fun heq i u hu => ?_⟩⟩
  · have := finrank_tailFlag (K := K) (A := A) hkr
    rw [h, finrank_bot] at this
    omega
  · have hd := hW.1 i
    obtain ⟨k, -, hkr, hk⟩ := eq_tailFlag_of_invariant hani hA
      (fun h => by rw [h, finrank_bot] at hd; omega) (hW.2.2 i) fun u hu => (hinv i u hu).le
    rw [hk, finrank_tailFlag hkr] at hd
    rw [hk, hd]
  · rw [heq i]
    exact map_tailFlag_of_mem_tailUnipotent hani (by omega) hu

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
