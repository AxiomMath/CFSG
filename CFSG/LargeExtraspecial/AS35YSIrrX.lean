module

public import CFSG.LargeExtraspecial.AS35YRFrameX

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions CFSG.ClassicalGroups.Orthogonal
  AS35YR

namespace AS35YS

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem sub_hyp_mem_Xp (F : Frame q) (v : V) :
    v - (polar q v F.c' • F.a + polar q v F.a • F.c' + polar q v F.c • F.b +
      polar q v F.b • F.c) ∈ F.Xp := by
  have hca : polar q F.c' F.a = 1 := by rw [polar_comm]; exact F.ac'
  have hcb : polar q F.c F.b = 1 := by rw [polar_comm]; exact F.bc
  have hba : polar q F.b F.a = 0 := by rw [polar_comm]; exact F.ab
  have hca' : polar q F.c F.a = 0 := by rw [polar_comm]; exact F.ac
  have hcb' : polar q F.c' F.b = 0 := by rw [polar_comm]; exact F.bc'
  have hcc : polar q F.c' F.c = 0 := by rw [polar_comm]; exact F.cc'
  refine Frame.mem_Xp.mpr ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [polar_sub_left, polar_add_left, polar_smul_left, polar_self_YR, hca, hcb, hba,
      hca', hcb', hcc, F.ab, F.ac, F.bc, F.ac', F.bc', F.cc', smul_eq_mul, mul_zero, mul_one,
      add_zero, zero_add, sub_self]

theorem eq_zero_of_perp_Xp (hq : q.polarBilin.Nondegenerate) (F : Frame q) {x : V}
    (hx : x ∈ F.Xp) (h : ∀ z ∈ F.Xp, polar q x z = 0) : x = 0 := by
  obtain ⟨ha, hb, hc, hc'⟩ := Frame.mem_Xp.mp hx
  refine hq.1 x fun v => ?_
  rw [polarBilin_apply_apply]
  have e : v = (v - (polar q v F.c' • F.a + polar q v F.a • F.c' + polar q v F.c • F.b +
      polar q v F.b • F.c)) + (polar q v F.c' • F.a + polar q v F.a • F.c' +
      polar q v F.c • F.b + polar q v F.b • F.c) := by abel
  rw [e, polar_add_right, h _ (sub_hyp_mem_Xp F v)]
  simp only [polar_add_right, polar_smul_right, ha, hb, hc, hc', smul_zero, add_zero]

theorem exists_ns_of_nondeg {Z : Submodule (ZMod 2) V}
    (hZ : ∀ z ∈ Z, (∀ z' ∈ Z, polar q z z' = 0) → z = 0) (hZ0 : Z ≠ ⊥) : ∃ z ∈ Z, q z = 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ z ∈ Z, q z = 0 := fun z hz => (Frame.zmod2_cases_YR _).resolve_right (hcon z hz)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hZ0
  refine hz0 (hZ z hz fun z' hz' => ?_)
  have := h0 _ (Z.add_mem hz hz')
  rwa [QuadraticMap.map_add q, h0 z hz, h0 z' hz', zero_add, zero_add] at this

theorem exists_ns_perp_pair [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    (F : Frame q) (hX : 3 ≤ finrank (ZMod 2) F.Xp) {u₁ u₂ : V} (h₁ : u₁ ∈ F.Xp)
    (h₂ : u₂ ∈ F.Xp) (h12 : polar q u₁ u₂ = 1) :
    ∃ x ∈ F.Xp, q x = 1 ∧ polar q x u₁ = 0 ∧ polar q x u₂ = 0 := by
  set K := LinearMap.BilinForm.orthogonal q.polarBilin (Submodule.span (ZMod 2) {u₁, u₂}) with hK
  have hmemK : ∀ {x : V}, x ∈ K ↔ polar q x u₁ = 0 ∧ polar q x u₂ = 0 := by
    intro x
    rw [hK, OrthoF2.mem_orthogonal_iff_polar]
    constructor
    · intro h
      exact ⟨h _ (Submodule.subset_span (by simp)), h _ (Submodule.subset_span (by simp))⟩
    · rintro ⟨ha, hb⟩ u hu
      obtain ⟨α, β, rfl⟩ := Submodule.mem_span_pair.mp hu
      rw [polar_add_right, polar_smul_right, polar_smul_right, ha, hb]
      simp
  set Z := F.Xp ⊓ K with hZ
  have hZ0 : Z ≠ ⊥ := by
    intro hbot
    have hdK := LinearMap.BilinForm.finrank_orthogonal hq (Submodule.span (ZMod 2) {u₁, u₂})
    have hspan : finrank (ZMod 2) (Submodule.span (ZMod 2) ({u₁, u₂} : Set V)) ≤ 2 := by
      classical
      have := finrank_span_le_card (R := ZMod 2) ({u₁, u₂} : Set V)
      have h2 : ({u₁, u₂} : Set V).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        exact Finset.card_insert_le _ _
      omega
    have hsup := Submodule.finrank_sup_add_finrank_inf_eq F.Xp K
    rw [← hZ, hbot, finrank_bot] at hsup
    have hle := Submodule.finrank_le (F.Xp ⊔ K)
    have hV := Submodule.finrank_le (Submodule.span (ZMod 2) ({u₁, u₂} : Set V))
    rw [← hK] at hdK
    omega
  have hZnd : ∀ z ∈ Z, (∀ z' ∈ Z, polar q z z' = 0) → z = 0 := by
    intro z hz hzZ
    obtain ⟨hzX, hzK⟩ := Submodule.mem_inf.mp hz
    obtain ⟨hz1, hz2⟩ := hmemK.mp hzK
    refine eq_zero_of_perp_Xp hq F hzX fun x hx => ?_
    set x' := x - (polar q x u₂ • u₁ + polar q x u₁ • u₂) with hx'
    have h21 : polar q u₂ u₁ = 1 := by rw [polar_comm]; exact h12
    have hx'Z : x' ∈ Z := by
      refine Submodule.mem_inf.mpr ⟨F.Xp.sub_mem hx (F.Xp.add_mem (F.Xp.smul_mem _ h₁)
        (F.Xp.smul_mem _ h₂)), hmemK.mpr ⟨?_, ?_⟩⟩
      · rw [hx', polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left,
          polar_self_YR, h21]
        simp
      · rw [hx', polar_sub_left, polar_add_left, polar_smul_left, polar_smul_left,
          polar_self_YR, h12]
        simp
    have e : x = x' + (polar q x u₂ • u₁ + polar q x u₁ • u₂) := by rw [hx']; abel
    rw [e, polar_add_right, hzZ _ hx'Z, polar_add_right, polar_smul_right, polar_smul_right,
      hz1, hz2]
    simp
  obtain ⟨x, hx, hqx⟩ := exists_ns_of_nondeg hZnd hZ0
  obtain ⟨hxX, hxK⟩ := Submodule.mem_inf.mp hx
  exact ⟨x, hxX, hqx, hmemK.mp hxK⟩

theorem exists_ns_polar_one [FiniteDimensional (ZMod 2) V] (hq : q.polarBilin.Nondegenerate)
    (F : Frame q) (hX : 3 ≤ finrank (ZMod 2) F.Xp) {r : V} (hr : r ∈ F.Xp) (hr0 : r ≠ 0) :
    ∃ w ∈ F.Xp, q w = 1 ∧ polar q w r = 1 := by
  obtain ⟨x, hx, hxr⟩ : ∃ x ∈ F.Xp, polar q x r = 1 := by
    by_contra hcon
    push Not at hcon
    refine hr0 (eq_zero_of_perp_Xp hq F hr fun z hz => ?_)
    rw [polar_comm]
    exact (Frame.zmod2_cases_YR _).resolve_right (hcon z hz)
  rcases Frame.zmod2_cases_YR (q x) with h0 | h1
  · obtain ⟨z, hz, hqz, hzx, hzr⟩ := exists_ns_perp_pair hq F hX hx hr hxr
    refine ⟨x + z, F.Xp.add_mem hx hz, ?_, ?_⟩
    · rw [QuadraticMap.map_add q, h0, hqz, polar_comm, hzx, zero_add, add_zero]
    · rw [polar_add_left, hxr, hzr, add_zero]
  · exact ⟨x, hx, h1, hxr⟩

@[expose] def LeviInv (F : Frame q) (Y : Submodule (ZMod 2) V) : Prop :=
  (∀ v ∈ F.Xp, ∀ w ∈ F.Xp, ∀ (hv : q v = 1) (hw : q w = 1), ∀ y ∈ Y,
      refl1 q v hv (refl1 q w hw y) ∈ Y) ∧
    ∀ u ∈ F.Xp, ∀ w ∈ F.Xp, q u = 0 → q w = 0 → polar q u w = 0 → ∀ y ∈ Y, eichler q u w y ∈ Y

theorem polar_refl1_left {v : V} (hv : q v = 1) (x y : V) :
    polar q (refl1 q v hv x) y = polar q x (refl1 q v hv y) := by
  rw [refl1_apply, refl1_apply, polar_add_left, polar_add_right, polar_smul_left,
    polar_smul_right, polar_comm q v y, smul_eq_mul, smul_eq_mul, mul_comm]

theorem polar_siegel_left {u w : V} (hu : q u = 0) (hw : q w = 0) (huw : polar q u w = 0)
    (x y : V) : polar q (eichler q u w x) y = polar q x (eichler q u w y) := by
  rw [siegel_apply hu hw huw, siegel_apply hu hw huw]
  simp only [polar_add_left, polar_add_right, polar_smul_left, polar_smul_right, smul_eq_mul]
  rw [polar_comm q w y, polar_comm q u y]
  ring

theorem refl1_mem_Xp (F : Frame q) {v : V} (hvX : v ∈ F.Xp) (hv : q v = 1) {x : V}
    (hx : x ∈ F.Xp) : refl1 q v hv x ∈ F.Xp := by
  rw [refl1_apply]
  exact F.Xp.add_mem hx (F.Xp.smul_mem _ hvX)

theorem siegel_mem_Xp (F : Frame q) {u w : V} (huX : u ∈ F.Xp) (hwX : w ∈ F.Xp) (hu : q u = 0)
    (hw : q w = 0) (huw : polar q u w = 0) {x : V} (hx : x ∈ F.Xp) : eichler q u w x ∈ F.Xp := by
  rw [siegel_apply hu hw huw]
  exact F.Xp.add_mem (F.Xp.add_mem hx (F.Xp.smul_mem _ hwX)) (F.Xp.smul_mem _ huX)

namespace LeviInv

variable {F : Frame q} {Y : Submodule (ZMod 2) V}

theorem perp (h : LeviInv F Y) :
    LeviInv F (F.Xp ⊓ LinearMap.BilinForm.orthogonal q.polarBilin Y) := by
  refine ⟨fun v hv w hw hv1 hw1 x hx => ?_, fun u hu w hw hu0 hw0 huw x hx => ?_⟩
  · obtain ⟨hxX, hxY⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨refl1_mem_Xp F hv hv1 (refl1_mem_Xp F hw hw1 hxX), ?_⟩
    rw [OrthoF2.mem_orthogonal_iff_polar] at hxY ⊢
    intro y hy
    rw [polar_refl1_left, polar_refl1_left]
    exact hxY _ (h.1 w hw v hv hw1 hv1 y hy)
  · obtain ⟨hxX, hxY⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨siegel_mem_Xp F hu hw hu0 hw0 huw hxX, ?_⟩
    rw [OrthoF2.mem_orthogonal_iff_polar] at hxY ⊢
    intro y hy
    rw [polar_siegel_left hu0 hw0 huw]
    exact hxY _ (h.2 u hu w hw hu0 hw0 huw y hy)

theorem rad (h : LeviInv F Y) :
    LeviInv F (Y ⊓ LinearMap.BilinForm.orthogonal q.polarBilin Y) := by
  refine ⟨fun v hv w hw hv1 hw1 x hx => ?_, fun u hu w hw hu0 hw0 huw x hx => ?_⟩
  · obtain ⟨hxY', hxY⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨h.1 v hv w hw hv1 hw1 x hxY', ?_⟩
    rw [OrthoF2.mem_orthogonal_iff_polar] at hxY ⊢
    intro y hy
    rw [polar_refl1_left, polar_refl1_left]
    exact hxY _ (h.1 w hw v hv hw1 hv1 y hy)
  · obtain ⟨hxY', hxY⟩ := Submodule.mem_inf.mp hx
    refine Submodule.mem_inf.mpr ⟨h.2 u hu w hw hu0 hw0 huw x hxY', ?_⟩
    rw [OrthoF2.mem_orthogonal_iff_polar] at hxY ⊢
    intro y hy
    rw [polar_siegel_left hu0 hw0 huw]
    exact hxY _ (h.2 u hu w hw hu0 hw0 huw y hy)

theorem exists_ns_mem [FiniteDimensional (ZMod 2) V] (h : LeviInv F Y)
    (hq : q.polarBilin.Nondegenerate) (hX : 3 ≤ finrank (ZMod 2) F.Xp) (hYX : Y ≤ F.Xp)
    (hY0 : Y ≠ ⊥) : ∃ y₀ ∈ Y, q y₀ = 1 := by
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  rcases Frame.zmod2_cases_YR (q y) with hq0 | hq1
  · obtain ⟨z, hz, hyz⟩ : ∃ z ∈ F.Xp, polar q y z = 1 := by
      by_contra hcon
      push Not at hcon
      exact hy0 (eq_zero_of_perp_Xp hq F (hYX hy) fun z hz =>
        (Frame.zmod2_cases_YR _).resolve_right (hcon z hz))
    obtain ⟨x, hx, hqx, hxy, hxz⟩ := exists_ns_perp_pair hq F hX (hYX hy) hz hyz
    obtain ⟨v, hvX, hqv, hyv⟩ : ∃ v ∈ F.Xp, q v = 1 ∧ polar q y v = 1 := by
      rcases Frame.zmod2_cases_YR (q z) with hz0 | hz1
      · refine ⟨z + x, F.Xp.add_mem hz hx, ?_, ?_⟩
        · rw [QuadraticMap.map_add q, hz0, hqx, polar_comm, hxz, zero_add, add_zero]
        · rw [polar_add_right, hyz, polar_comm, hxy, add_zero]
      · exact ⟨z, hz, hz1, hyz⟩
    have hyx : polar q y x = 0 := by rw [polar_comm]; exact hxy
    have hmem := h.1 v hvX x hx hqv hqx y hy
    rw [refl1_apply hqx, hyx, zero_smul, add_zero, refl1_apply hqv, hyv, one_smul] at hmem
    refine ⟨v, ?_, hqv⟩
    have := Y.sub_mem hmem hy
    rwa [add_sub_cancel_left] at this
  · exact ⟨y, hy, hq1⟩

theorem refl_mem (h : LeviInv F Y) {y₀ : V} (hy₀ : y₀ ∈ Y) (hy₀X : y₀ ∈ F.Xp) (hq₀ : q y₀ = 1)
    {w : V} (hwX : w ∈ F.Xp) (hw : q w = 1) {y : V} (hy : y ∈ Y) : refl1 q w hw y ∈ Y := by
  have h1 := h.1 y₀ hy₀X w hwX hq₀ hw y hy
  have e : refl1 q w hw y = refl1 q y₀ hq₀ (refl1 q y₀ hq₀ (refl1 q w hw y)) := by
    rw [← LinearEquiv.mul_apply, refl1_mul_self, LinearEquiv.coe_one, id]
  rw [e, refl1_apply]
  exact Y.add_mem h1 (Y.smul_mem _ hy₀)

end LeviInv

theorem mem_or_perp_of_refl {Y : Submodule (ZMod 2) V} {w : V} (hw : q w = 1)
    (hrefl : ∀ y ∈ Y, refl1 q w hw y ∈ Y) : w ∈ Y ∨ ∀ z ∈ Y, polar q z w = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨hwY, z, hz, hzw⟩ := hcon
  have hz1 : polar q z w = 1 := (Frame.zmod2_cases_YR _).resolve_left hzw
  have := Y.sub_mem (hrefl z hz) hz
  rw [refl1_apply, hz1, one_smul, add_sub_cancel_left] at this
  exact hwY this

namespace LeviInv

variable {F : Frame q} {Y : Submodule (ZMod 2) V}

theorem nondeg [FiniteDimensional (ZMod 2) V] (h : LeviInv F Y)
    (hq : q.polarBilin.Nondegenerate) (hX : 3 ≤ finrank (ZMod 2) F.Xp) (hYX : Y ≤ F.Xp) :
    ∀ y ∈ Y, (∀ y' ∈ Y, polar q y y' = 0) → y = 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hyperp, hy0⟩ := hcon
  set R := Y ⊓ LinearMap.BilinForm.orthogonal q.polarBilin Y with hR
  have hRY : R ≤ Y := inf_le_left
  have hR0 : R ≠ ⊥ := by
    intro hbot
    have hyR : y ∈ R := Submodule.mem_inf.mpr ⟨hy, OrthoF2.mem_orthogonal_iff_polar.mpr
      fun u hu => hyperp u hu⟩
    rw [hbot, Submodule.mem_bot] at hyR
    exact hy0 hyR
  obtain ⟨r₀, hr₀, hqr₀⟩ := h.rad.exists_ns_mem hq hX (hRY.trans hYX) hR0
  obtain ⟨hr₀Y, hr₀perp⟩ := Submodule.mem_inf.mp hr₀
  have hr₀0 : r₀ ≠ 0 := fun e => by rw [e, QuadraticMap.map_zero] at hqr₀; exact zero_ne_one hqr₀
  obtain ⟨w, hwX, hqw, hwr⟩ := exists_ns_polar_one hq F hX (hYX hr₀Y) hr₀0
  rcases mem_or_perp_of_refl hqw (fun y' hy' => h.refl_mem hr₀Y (hYX hr₀Y) hqr₀ hwX hqw hy')
    with hwY | hwperp
  · have := (OrthoF2.mem_orthogonal_iff_polar.mp hr₀perp) w hwY
    rw [polar_comm] at this
    rw [this] at hwr
    exact zero_ne_one hwr
  · have := hwperp r₀ hr₀Y
    rw [polar_comm] at this
    rw [this] at hwr
    exact zero_ne_one hwr

end LeviInv

end AS35YS

end CFSG.LargeExtraspecial
