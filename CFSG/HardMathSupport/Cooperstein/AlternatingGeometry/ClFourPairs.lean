module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.IsoBlocksFixed
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.KleinEightPoints

public section

set_option linter.unusedSectionVars false

namespace CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

open Equiv Equiv.Perm

namespace PairFrame

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {ι : Type*} [Fintype ι] [DecidableEq ι]
  {W : Subgroup (Perm Ω)} {a a' : ι → Ω}

@[expose] def pt (a a' : ι → Ω) (z : ι × Bool) : Ω := if z.2 then a' z.1 else a z.1

theorem pt_true (a a' : ι → Ω) (i : ι) : pt a a' (i, true) = a' i := rfl
theorem pt_false (a a' : ι → Ω) (i : ι) : pt a a' (i, false) = a i := rfl

theorem pt_injective (h : IsoBlocks W a a') : Function.Injective (pt a a') := by
  rintro ⟨i, b⟩ ⟨j, c⟩ hij
  by_cases hi : i = j
  · subst hi
    cases b <;> cases c
    · rfl
    · exact absurd hij (h.ne i)
    · exact absurd hij.symm (h.ne i)
    · rfl
  · obtain ⟨d1, d2, d3, d4⟩ := h.disj i j hi
    cases b <;> cases c
    · exact absurd hij d1
    · exact absurd hij d2
    · exact absurd hij d3
    · exact absurd hij d4

@[expose] def Δ (a a' : ι → Ω) : Finset Ω := Finset.univ.image (pt a a')

theorem mem_Δ {x : Ω} : x ∈ Δ a a' ↔ ∃ z, pt a a' z = x := by simp [Δ]

@[expose] noncomputable def pe (h : IsoBlocks W a a') : ι × Bool ≃ {x : Ω // x ∈ Δ a a'} :=
  Equiv.ofBijective (fun z => ⟨pt a a' z, mem_Δ.2 ⟨z, rfl⟩⟩)
    ⟨fun z z' hzz' => pt_injective h (congrArg Subtype.val hzz'),
     fun x => by
      obtain ⟨z, hz⟩ := mem_Δ.1 x.2
      exact ⟨z, Subtype.ext hz⟩⟩

@[expose] noncomputable def ext (h : IsoBlocks W a a') : Perm (ι × Bool) →* Perm Ω :=
  Equiv.Perm.extendDomainHom (pe h)

theorem ext_pt (h : IsoBlocks W a a') (g : Perm (ι × Bool)) (z : ι × Bool) :
    ext h g (pt a a' z) = pt a a' (g z) :=
  Equiv.Perm.extendDomain_apply_image g (pe h) z

theorem ext_not_mem (h : IsoBlocks W a a') (g : Perm (ι × Bool)) {x : Ω} (hx : x ∉ Δ a a') :
    ext h g x = x :=
  Equiv.Perm.extendDomain_apply_not_subtype g (pe h) (p := fun x : Ω => x ∈ Δ a a') hx

theorem sign_ext (h : IsoBlocks W a a') (g : Perm (ι × Bool)) : sign (ext h g) = sign g :=
  Equiv.Perm.sign_extendDomain g (pe h)

theorem mem_normalizer_of_pairPerm (h : IsoBlocks W a a') {τ : Perm Ω}
    (hoff : ∀ x, x ∉ Δ a a' → τ x = x)
    (hpair : ∀ i, ∃ j, (τ (a i) = a j ∧ τ (a' i) = a' j) ∨ (τ (a i) = a' j ∧ τ (a' i) = a j)) :
    τ ∈ Subgroup.normalizer (W : Set (Perm Ω)) := by
  classical
  have hτΔ : ∀ x, x ∈ Δ a a' → τ x ∈ Δ a a' := by
    intro x hx
    obtain ⟨⟨i, b⟩, rfl⟩ := mem_Δ.1 hx
    obtain ⟨j, hj⟩ := hpair i
    cases b
    · rcases hj with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact mem_Δ.2 ⟨(j, false), by rw [pt_false, pt_false, h1]⟩
      · exact mem_Δ.2 ⟨(j, true), by rw [pt_false, pt_true, h1]⟩
    · rcases hj with ⟨-, h1⟩ | ⟨-, h1⟩
      · exact mem_Δ.2 ⟨(j, true), by rw [pt_true, pt_true, h1]⟩
      · exact mem_Δ.2 ⟨(j, false), by rw [pt_true, pt_false, h1]⟩
  have hτinvΔ : ∀ x, x ∈ Δ a a' → τ⁻¹ x ∈ Δ a a' := by
    intro x hx
    by_contra hn
    have := hoff _ hn
    have h2 : τ (τ⁻¹ x) = x := by simp
    rw [this] at h2
    exact hn (by rw [h2]; exact hx)
  have hτinvoff : ∀ x, x ∉ Δ a a' → τ⁻¹ x = x := by
    intro x hx
    exact Perm.inv_eq_iff_eq.2 (hoff x hx).symm
  have key : ∀ n, ∀ w ∈ W, (Finset.univ.filter fun i => w (a i) ≠ a i).card = n →
      τ * w * τ⁻¹ ∈ W := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
    intro w hw hn
    by_cases h0 : ∀ i, w (a i) = a i
    ·
      have hwΔ : ∀ x, x ∈ Δ a a' → w x = x := by
        intro x hx
        obtain ⟨⟨i, b⟩, rfl⟩ := mem_Δ.1 hx
        cases b
        · exact h0 i
        · exact (h.fix_iff hw i).1 (h0 i)
      have hwoff : ∀ x, x ∉ Δ a a' → w x ∉ Δ a a' := by
        intro x hx hwx
        apply hx
        have : w x = x := by
          have h1 : w (w x) = w x := hwΔ _ hwx
          exact w.injective h1
        rw [← this]; exact hwx
      have : τ * w * τ⁻¹ = w := by
        apply Equiv.ext
        intro x
        by_cases hx : x ∈ Δ a a'
        · rw [Perm.mul_apply, Perm.mul_apply, hwΔ _ (hτinvΔ x hx), hwΔ x hx]
          simp
        · rw [Perm.mul_apply, Perm.mul_apply, hτinvoff x hx, hoff _ (hwoff x hx)]
      rw [this]; exact hw
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      have hflip : w (a i) = a' i := (h.stab w hw i).resolve_left hi
      have hw' : w * swap (a i) (a' i) ∈ W := W.mul_mem hw (h.swap_mem i)
      have hcard : (Finset.univ.filter fun j => (w * swap (a i) (a' i)) (a j) ≠ a j).card < n := by
        rw [← hn]
        apply Finset.card_lt_card
        rw [Finset.ssubset_iff_of_subset]
        · refine ⟨i, ?_, ?_⟩
          · simp [hi]
          · simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not]
            rw [Perm.mul_apply, swap_apply_left, (h.flip_iff hw i).1 hflip]
        · intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
          by_cases hji : j = i
          · subst hji; exact hi
          · obtain ⟨d1, d2, -, -⟩ := h.disj j i hji
            rw [Perm.mul_apply, swap_apply_of_ne_of_ne d1 d2] at hj
            exact hj
      have h1 := ih _ hcard (w * swap (a i) (a' i)) hw' rfl
      have h2 : τ * swap (a i) (a' i) * τ⁻¹ ∈ W := by
        rw [← swap_apply_apply]
        obtain ⟨j, hj⟩ := hpair i
        rcases hj with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rw [e1, e2]; exact h.swap_mem j
        · rw [e1, e2, swap_comm]; exact h.swap_mem j
      have e : τ * w * τ⁻¹ = (τ * (w * swap (a i) (a' i)) * τ⁻¹) * (τ * swap (a i) (a' i) * τ⁻¹) := by
        have : (τ * (w * swap (a i) (a' i)) * τ⁻¹) * (τ * swap (a i) (a' i) * τ⁻¹) =
            τ * (w * (swap (a i) (a' i) * swap (a i) (a' i))) * τ⁻¹ := by group
        rw [this, swap_mul_self, mul_one]
      rw [e]
      exact W.mul_mem h1 h2
  exact CFSG.HardMathSupport.Cooperstein.Proving.mem_normalizer_of_conj_le fun w hw =>
    key _ w hw rfl

theorem mem_Δ_of_normalizer (h : IsoBlocks W a a') {g : Perm Ω}
    (hg : g ∈ Subgroup.normalizer (W : Set (Perm Ω))) {x : Ω} (hx : x ∈ Δ a a') :
    g x ∈ Δ a a' := by
  obtain ⟨⟨i, b⟩, rfl⟩ := mem_Δ.1 hx
  obtain ⟨j, hj⟩ := h.blk_map hg i
  cases b
  · rcases hj with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact mem_Δ.2 ⟨(j, false), by rw [pt_false, pt_false, h1]⟩
    · exact mem_Δ.2 ⟨(j, true), by rw [pt_false, pt_true, h1]⟩
  · rcases hj with ⟨-, h1⟩ | ⟨-, h1⟩
    · exact mem_Δ.2 ⟨(j, true), by rw [pt_true, pt_true, h1]⟩
    · exact mem_Δ.2 ⟨(j, false), by rw [pt_true, pt_false, h1]⟩

theorem exists_frame_perm (h : IsoBlocks W a a') {g : Perm Ω}
    (hg : g ∈ Subgroup.normalizer (W : Set (Perm Ω))) :
    ∃ g0 : Perm (ι × Bool), (∀ z, pt a a' (g0 z) = g (pt a a' z)) ∧
      ∀ z : ι × Bool, g0 (z.1, !z.2) = ((g0 z).1, !(g0 z).2) := by
  classical
  have hgΔ : ∀ x, g x ∈ Δ a a' ↔ x ∈ Δ a a' := by
    intro x
    constructor
    · intro hx
      have := mem_Δ_of_normalizer h ((Subgroup.normalizer _).inv_mem hg) hx
      simpa using this
    · exact mem_Δ_of_normalizer h hg
  let gsub : Perm {x // x ∈ Δ a a'} := g.subtypePerm hgΔ
  have hpt : ∀ z, pt a a' ((pe h).permCongr.symm gsub z) = g (pt a a' z) := by
    intro z
    have h1 : (pe h).permCongr ((pe h).permCongr.symm gsub) = gsub := Equiv.apply_symm_apply _ _
    have h2 := congrArg (fun f : Perm {x // x ∈ Δ a a'} => f (pe h z)) h1
    simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply] at h2
    exact congrArg Subtype.val h2
  generalize (pe h).permCongr.symm gsub = g0 at hpt
  refine ⟨g0, hpt, ?_⟩
  have hF : ∀ (i : ι) (z : ι × Bool), g (pt a a' (i, false)) = pt a a' z → g0 (i, false) = z :=
    fun i z hz => pt_injective h ((hpt _).trans hz)
  have hT : ∀ (i : ι) (z : ι × Bool), g (pt a a' (i, true)) = pt a a' z → g0 (i, true) = z :=
    fun i z hz => pt_injective h ((hpt _).trans hz)
  rintro ⟨i, b⟩
  obtain ⟨j, hj⟩ := h.blk_map hg i
  rcases hj with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : g0 (i, false) = (j, false) := hF i (j, false) h1
    have e2 : g0 (i, true) = (j, true) := hT i (j, true) h2
    cases b
    · simp only [Bool.not_false, e2, e1]
    · simp only [Bool.not_true, e2, e1, Bool.not_true]
  · have e1 : g0 (i, false) = (j, true) := hF i (j, true) h1
    have e2 : g0 (i, true) = (j, false) := hT i (j, false) h2
    cases b
    · simp only [Bool.not_false, e2, e1, Bool.not_true]
    · simp only [Bool.not_true, e2, e1, Bool.not_false]

open PairFlip KleinEight in
theorem exists_normal_two_group_of_fourPairs [Finite Ω] (h : IsoBlocks W a a')
    (hι : Fintype.card ι = 4) (hΩ : 8 < Fintype.card Ω) :
    ∃ (U : Subgroup (Perm Ω)) (D : Finset Ω), IsPGroup 2 U ∧
      U ≤ Subgroup.normalizer (W : Set (Perm Ω)) ∧
      (∀ g ∈ Subgroup.normalizer (W : Set (Perm Ω)), ∀ u ∈ U, g * u * g⁻¹ ∈ U) ∧
      (∀ u ∈ U, sign u = 1) ∧ 5 ≤ D.card ∧ (∃ k, k ∉ D) ∧
      (∀ u ∈ U, ∀ i, i ∉ D → u i = i) ∧ (∀ i ∈ D, ∀ j ∈ D, ∃ u ∈ U, u i = j) := by
  classical
  have hB : (Finset.univ : Finset ι).card = 4 := by rw [Finset.card_univ, hι]
  have hWJ : ∀ i j : ι, i ≠ j → tp i ∉ J0 ι → tp j ∉ J0 ι → tp i * tp j ∈ J0 ι :=
    fun i _ _ hi _ => absurd (tp_mem_J0 i) hi
  have hout : outSet (J0 ι) = ∅ := by
    ext i; simp [mem_outSet, tp_mem_J0]
  have hT1 : (outSet (J0 ι)).card ≠ 1 := by rw [hout]; simp
  have hBT : (Finset.univ : Finset ι) = outSet (J0 ι) ∨ (Finset.univ : Finset ι) = (outSet (J0 ι))ᶜ :=
    Or.inr (by rw [hout]; simp)
  have hcardΔ : (Δ a a').card = 8 := by
    rw [Δ, Finset.card_image_of_injective _ (pt_injective h)]
    simp [hι]
  refine ⟨(U Finset.univ hB).map (ext h), Δ a a', (isPGroup_U _ hB).map _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rintro _ ⟨u0, hu0, rfl⟩
    refine mem_normalizer_of_pairPerm h (fun x hx => ext_not_mem h u0 hx) fun i => ?_
    have hf := U_flip _ hB hu0 (i, false)
    simp only [Bool.not_false] at hf
    obtain ⟨⟨j, c⟩, hjc⟩ : ∃ y, u0 (i, false) = y := ⟨_, rfl⟩
    rw [hjc] at hf
    refine ⟨j, ?_⟩
    have e1 : ext h u0 (a i) = pt a a' (j, c) :=
      (ext_pt h u0 (i, false)).trans (by rw [hjc])
    have e2 : ext h u0 (a' i) = pt a a' (j, !c) :=
      (ext_pt h u0 (i, true)).trans (by rw [hf])
    cases c
    · left; exact ⟨e1, e2⟩
    · right; exact ⟨e1, e2⟩
  ·
    rintro g hg _ ⟨u0, hu0, rfl⟩
    obtain ⟨g0, hg0, hflip⟩ := exists_frame_perm h hg
    have hg0inv : ∀ z : ι × Bool, g0⁻¹ (z.1, !z.2) = ((g0⁻¹ z).1, !(g0⁻¹ z).2) := by
      intro z
      have h1 := hflip (g0⁻¹ z)
      rw [show g0 (g0⁻¹ z) = z by simp] at h1
      have h2 : g0 (((g0⁻¹ z).1, !(g0⁻¹ z).2)) = (z.1, !z.2) := by
        rw [hflip (g0⁻¹ z)]; simp
      exact Perm.inv_eq_iff_eq.2 h2.symm
    have hg0N : g0 ∈ Subgroup.normalizer ((J0 ι : Subgroup (Perm (ι × Bool))) : Set (Perm (ι × Bool))) := by
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · exact fun hw => conj_mem_J0 hflip hw
      · intro hw
        have := conj_mem_J0 hg0inv hw
        have e : g0⁻¹ * (g0 * w * g0⁻¹) * g0⁻¹⁻¹ = w := by group
        rwa [e] at this
    have hconj := conj_mem_U (le_refl (J0 ι)) hWJ hT1 hB hBT hg0N hu0
    refine ⟨g0 * u0 * g0⁻¹, hconj, ?_⟩
    apply Equiv.ext
    intro x
    show ext h (g0 * u0 * g0⁻¹) x = (g * ext h u0 * g⁻¹) x
    by_cases hx : x ∈ Δ a a'
    · have hx' : g⁻¹ x ∈ Δ a a' := mem_Δ_of_normalizer h ((Subgroup.normalizer _).inv_mem hg) hx
      obtain ⟨z', hz'⟩ := mem_Δ.1 hx'
      have hxz : x = pt a a' (g0 z') := by rw [hg0, hz']; simp
      have e1 : (g * ext h u0 * g⁻¹) x = g (ext h u0 (pt a a' z')) := by
        rw [Perm.mul_apply, Perm.mul_apply, hz']
      have e2 : g (ext h u0 (pt a a' z')) = pt a a' (g0 (u0 z')) := by
        rw [ext_pt, ← hg0]
      have e4 : ext h (g0 * u0 * g0⁻¹) x = pt a a' ((g0 * u0 * g0⁻¹) (g0 z')) := by
        rw [hxz, ext_pt]
      rw [e1, e2, e4]
      simp
    · have hx' : g⁻¹ x ∉ Δ a a' := fun hmem => hx (by
        have := mem_Δ_of_normalizer h hg hmem
        simpa using this)
      rw [ext_not_mem h _ hx, Perm.mul_apply, Perm.mul_apply, ext_not_mem h _ hx']
      simp
  · rintro _ ⟨u0, hu0, rfl⟩
    rw [sign_ext, U_sign _ hB hu0]
  · rw [hcardΔ]; norm_num
  · by_contra hcon
    push Not at hcon
    have : Δ a a' = Finset.univ := Finset.eq_univ_of_forall hcon
    rw [this, Finset.card_univ] at hcardΔ
    omega
  · rintro _ ⟨u0, hu0, rfl⟩ i hi
    exact ext_not_mem h u0 hi
  · intro i hi j hj
    obtain ⟨z, rfl⟩ := mem_Δ.1 hi
    obtain ⟨z', rfl⟩ := mem_Δ.1 hj
    obtain ⟨u0, hu0, hu⟩ := U_transitive (Finset.univ : Finset ι) hB (x := z) (y := z')
      (Finset.mem_univ _) (Finset.mem_univ _)
    exact ⟨ext h u0, ⟨u0, hu0, rfl⟩, by rw [ext_pt, hu]⟩

end PairFrame

end CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
