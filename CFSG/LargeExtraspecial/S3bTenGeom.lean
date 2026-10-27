module

public import CFSG.LargeExtraspecial.OrthoF2Eichler

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions OrthoF2
open TauCeti.QuadraticMap (orthogonalGroup)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem orthogonal_sup_eq (B : LinearMap.BilinForm (ZMod 2) V) (X W : Submodule (ZMod 2) V) :
    B.orthogonal (X ⊔ W) = B.orthogonal X ⊓ B.orthogonal W := by
  ext v
  simp only [Submodule.mem_inf, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Submodule.mem_sup_left hx),
      fun w hw => h w (Submodule.mem_sup_right hw)⟩
  · rintro ⟨hX, hW⟩ y hy
    obtain ⟨x, hx, w, hw, rfl⟩ := Submodule.mem_sup.mp hy
    have h1 := hX x hx
    have h2 := hW w hw
    rw [map_add, LinearMap.add_apply, h1, h2, add_zero]

theorem polar_eq_zero_of_forall_eq_zero {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, q w = 0)
    {w w' : V} (hw : w ∈ W) (hw' : w' ∈ W) : polar q w w' = 0 := by
  have h := map_add_eq q w w'
  rw [hW _ (W.add_mem hw hw'), hW w hw, hW w' hw', zero_add, zero_add] at h
  exact h.symm

theorem le_orthogonal_of_forall_eq_zero {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, q w = 0) :
    W ≤ LinearMap.BilinForm.orthogonal q.polarBilin W := fun w hw => by
  rw [LinearMap.BilinForm.mem_orthogonal_iff]
  intro w' hw'
  rw [polarBilin_apply_apply]
  exact polar_eq_zero_of_forall_eq_zero hW hw' hw

theorem polar_eq_zero_of_mem_orthogonal {W : Submodule (ZMod 2) V} {w u : V} (hw : w ∈ W)
    (hu : u ∈ LinearMap.BilinForm.orthogonal q.polarBilin W) : polar q w u = 0 := by
  rw [LinearMap.BilinForm.mem_orthogonal_iff] at hu
  have := hu w hw
  rwa [polarBilin_apply_apply] at this

theorem map_add_of_mem_orthogonal {W : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, q w = 0)
    {w p : V} (hw : w ∈ W) (hp : p ∈ LinearMap.BilinForm.orthogonal q.polarBilin W) :
    q (w + p) = q p := by
  rw [map_add_eq, hW w hw, zero_add, polar_eq_zero_of_mem_orthogonal hw hp, add_zero]

theorem zmod2_eq_one_of_eq (c : ZMod 2) (h : (1 : ZMod 2) = 1 + 1 + c) : c = 1 := by
  revert c
  decide

theorem false_of_three_anisotropic {u₁ u₂ u₃ : V} (h1 : q u₁ = 1) (h2 : q u₂ = 1) (h3 : q u₃ = 1)
    (h12 : q (u₁ + u₂) = 1) (h13 : q (u₁ + u₃) = 1) (h23 : q (u₂ + u₃) = 1)
    (h123 : q (u₁ + u₂ + u₃) = 1) : False := by
  have p12 : polar q u₁ u₂ = 1 := by
    have := map_add_eq q u₁ u₂
    rw [h12, h1, h2] at this
    exact zmod2_eq_one_of_eq _ this
  have p13 : polar q u₁ u₃ = 1 := by
    have := map_add_eq q u₁ u₃
    rw [h13, h1, h3] at this
    exact zmod2_eq_one_of_eq _ this
  have p23 : polar q u₂ u₃ = 1 := by
    have := map_add_eq q u₂ u₃
    rw [h23, h2, h3] at this
    exact zmod2_eq_one_of_eq _ this
  have := map_add_eq q (u₁ + u₂) u₃
  rw [h123, h12, h3, polar_add_left, p13, p23] at this
  revert this
  decide

variable [FiniteDimensional (ZMod 2) V]

theorem false_of_anisotropic_of_witt (hq : q.polarBilin.Nondegenerate) {n : ℕ}
    (hV : finrank (ZMod 2) V = 2 * n) {W X : Submodule (ZMod 2) V} (hW : ∀ w ∈ W, q w = 0)
    (hWn : finrank (ZMod 2) W + 1 = n) (hX : ∀ x ∈ X, q x = 0) (hXn : finrank (ZMod 2) X = n)
    {u₁ u₂ : V} (hu₁ : u₁ ∈ LinearMap.BilinForm.orthogonal q.polarBilin W)
    (hu₂ : u₂ ∈ LinearMap.BilinForm.orthogonal q.polarBilin W)
    (hq₁ : q u₁ = 1) (hq₂ : q u₂ = 1) (hq₁₂ : q (u₁ + u₂) = 1) : False := by
  have hXX : LinearMap.BilinForm.orthogonal q.polarBilin X = X := by
    refine (Submodule.eq_of_le_of_finrank_eq (le_orthogonal_of_forall_eq_zero hX) ?_).symm
    rw [LinearMap.BilinForm.finrank_orthogonal hq, hV, hXn]
    omega
  have hY : finrank (ZMod 2)
      (X ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W : Submodule (ZMod 2) V) =
      finrank (ZMod 2) (X ⊓ W : Submodule (ZMod 2) V) + 1 := by
    have e : X ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W =
        LinearMap.BilinForm.orthogonal q.polarBilin (X ⊔ W) := by
      rw [orthogonal_sup_eq, hXX]
    rw [e, LinearMap.BilinForm.finrank_orthogonal hq, hV]
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq X W
    rw [hXn] at h1
    omega
  obtain ⟨v, hv, hvW⟩ : ∃ v ∈ X ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W, v ∉ W := by
    by_contra h
    push Not at h
    have hle : X ⊓ LinearMap.BilinForm.orthogonal q.polarBilin W ≤ X ⊓ W :=
      fun v hv => ⟨hv.1, h v hv⟩
    have := Submodule.finrank_mono hle
    omega
  set P := Submodule.span (ZMod 2) {u₁, u₂} with hP
  have hu₁0 : u₁ ≠ 0 := fun h => by rw [h, map_zero] at hq₁; exact zero_ne_one hq₁
  have hu₂0 : u₂ ≠ 0 := fun h => by rw [h, map_zero] at hq₂; exact zero_ne_one hq₂
  have hu₁₂ : u₁ ≠ u₂ := fun h => by
    rw [h, vec_add_self, map_zero] at hq₁₂
    exact zero_ne_one hq₁₂
  have hli : LinearIndependent (ZMod 2) ![u₁, u₂] :=
    linearIndependent_pair_iff.mpr ⟨hu₁0, hu₂0, hu₁₂⟩
  have hPq : ∀ p ∈ P, p ≠ 0 → q p = 1 := by
    intro p hp hp0
    obtain ⟨c₁, c₂, rfl⟩ := Submodule.mem_span_pair.mp hp
    rcases zmod2_eq_zero_or_eq_one c₁ with rfl | rfl <;>
      rcases zmod2_eq_zero_or_eq_one c₂ with rfl | rfl
    · simp at hp0
    · simpa using hq₂
    · simpa using hq₁
    · simpa using hq₁₂
  have hWP : W ⊓ P = ⊥ := by
    rw [eq_bot_iff]
    intro p hp
    by_contra hp0
    have h1 := hPq p hp.2 hp0
    rw [hW p hp.1] at h1
    exact zero_ne_one h1
  have hPperp : P ≤ LinearMap.BilinForm.orthogonal q.polarBilin W := by
    rw [hP, Submodule.span_le]
    rintro _ (rfl | rfl)
    · exact hu₁
    · exact hu₂
  have hWPeq : W ⊔ P = LinearMap.BilinForm.orthogonal q.polarBilin W := by
    refine Submodule.eq_of_le_of_finrank_eq
      (sup_le (le_orthogonal_of_forall_eq_zero hW) hPperp) ?_
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq W P
    rw [hWP, finrank_bot, finrank_span_pair hli] at h1
    rw [LinearMap.BilinForm.finrank_orthogonal hq, hV]
    omega
  have hv' := hv.2
  rw [← hWPeq] at hv'
  obtain ⟨w, hw, p, hp, rfl⟩ := Submodule.mem_sup.mp hv'
  have hp0 : p ≠ 0 := fun h => hvW (by rw [h, add_zero]; exact hw)
  have h1 := hX _ hv.1
  rw [map_add_of_mem_orthogonal hW hw (hPperp hp), hPq p hp hp0] at h1
  exact one_ne_zero h1

theorem le_fixSpace_of_isTypeC (hq : q.polarBilin.Nondegenerate) {s : V ≃ₗ[ZMod 2] V}
    (hs : IsTypeC q s 2) {a : V} (ha0 : a ≠ 0) (haq : q a = 0) (has : a ∈ commSpace s)
    {W' : Submodule (ZMod 2) V} (hW' : ∀ w ∈ W', q w = 0) (hinv : ∀ w ∈ W', s w ∈ W')
    (haW : a ∉ W') :
    W' ≤ fixSpace s ∧ fixSpace s ≤ LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a) := by
  obtain ⟨v, ⟨hv, hv0, hvq⟩, huniq⟩ := existsUnique_singular_of_isTypeC hs
  have hva : a = v := huniq a ⟨has, ha0, haq⟩
  have hsO : s ∈ orthogonalGroup q := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hs.1
  refine ⟨fun w hw => ?_, ?_⟩
  · rw [mem_fixSpace]
    have h1 : s w - w ∈ W' := W'.sub_mem (hinv w hw) hw
    by_contra hne
    have h2 : s w - w ≠ 0 := sub_ne_zero.mpr hne
    have h3 : s w - w = v := huniq _ ⟨sub_mem_commSpace s w, h2, hW' _ h1⟩
    exact haW (by rw [hva, ← h3]; exact h1)
  · rw [fixSpace_eq_orthogonal_commSpace_of_mem hq hsO]
    exact LinearMap.BilinForm.orthogonal_le
      ((Submodule.span_singleton_le_iff_mem _ _).mpr has)

theorem span_sup_isTotallySingular {a : V} (ha0 : a ≠ 0) (haq : q a = 0)
    {W' : Submodule (ZMod 2) V} (hW' : ∀ w ∈ W', q w = 0)
    (hperp : W' ≤ LinearMap.BilinForm.orthogonal q.polarBilin ((ZMod 2) ∙ a)) (haW : a ∉ W') :
    (∀ x ∈ ((ZMod 2) ∙ a) ⊔ W', q x = 0) ∧
      finrank (ZMod 2) (((ZMod 2) ∙ a) ⊔ W' : Submodule (ZMod 2) V) =
        finrank (ZMod 2) W' + 1 := by
  refine ⟨fun x hx => ?_, ?_⟩
  · obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hpw : polar q a w = 0 := (mem_orthogonal_span_singleton_iff).mp (hperp hw)
    rw [map_add_eq, map_smul_zmod2, haq, hW' w hw, polar_smul_left, hpw]
    simp
  · have hinf : ((ZMod 2) ∙ a) ⊓ W' = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      rcases mem_span_singleton_iff.mp hx.1 with h | h
      · rw [h]
        exact Submodule.zero_mem _
      · exact absurd (h ▸ hx.2) haW
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq ((ZMod 2) ∙ a) W'
    rw [hinf, finrank_bot, finrank_span_singleton ha0] at h1
    omega

end CFSG.LargeExtraspecial
