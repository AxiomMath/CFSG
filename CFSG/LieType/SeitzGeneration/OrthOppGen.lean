module

public import CFSG.LieType.SeitzGeneration.OrthHyperRad
import CFSG.ClassicalGroups.Orthogonal.RootCenters
import CFSG.SignalizerFunctorTheorem.NonLocal.OrthRat

public section

namespace CFSG.LieType.SeitzGeneration

open QuadraticMap CFSG.ClassicalGroups.Orthogonal
open scoped commutatorElement

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V]

variable (Q : QuadraticForm K V) in
@[expose] def eichlerRad (X : Submodule K V) : Subgroup (V ≃ₗ[K] V) :=
  Subgroup.closure {g | ∃ x ∈ X, ∃ w ∈ qPerp Q X, eichler Q x w = g}

theorem eichler_mem_eichlerRad {Q : QuadraticForm K V} {X : Submodule K V} {x w : V} (hx : x ∈ X)
    (hw : w ∈ qPerp Q X) : eichler Q x w ∈ eichlerRad Q X :=
  Subgroup.subset_closure ⟨x, hx, w, hw, rfl⟩

theorem eichlerRad_le_qRad {Q : QuadraticForm K V} {X : Submodule K V}
    (hX : ∀ x ∈ X, Q x = 0) : eichlerRad Q X ≤ qRad Q X hX := by
  rw [eichlerRad, Subgroup.closure_le]
  rintro _ ⟨x, hx, w, hw, rfl⟩
  exact eichler_mem_qRad hx hw

theorem eichlerRad_le_elementaryGroup (Q : QuadraticForm K V) (X : Submodule K V) :
    eichlerRad Q X ≤ elementaryGroup Q := by
  rw [eichlerRad, Subgroup.closure_le]
  rintro _ ⟨x, -, w, -, rfl⟩
  exact eichler_mem_elementaryGroup Q x w

private theorem qPerp_eq_orthogonal {Q : QuadraticForm K V} (X : Submodule K V) :
    qPerp Q X = LinearMap.BilinForm.orthogonal (polarBilin Q) X := by
  ext v
  rw [mem_qPerp, LinearMap.BilinForm.mem_orthogonal_iff]
  simp only [polarBilin_apply_apply]

private theorem qPerp_sup {Q : QuadraticForm K V} (X Y : Submodule K V) :
    qPerp Q (X ⊔ Y) = qPerp Q X ⊓ qPerp Q Y := by
  ext v
  rw [mem_qPerp, Submodule.mem_inf, mem_qPerp, mem_qPerp]
  constructor
  · intro h
    exact ⟨fun x hx => h x (Submodule.mem_sup_left hx),
      fun y hy => h y (Submodule.mem_sup_right hy)⟩
  · rintro ⟨h1, h2⟩ w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    rw [polar_add_left, h1 x hx, h2 y hy, add_zero]

private theorem eq_zero_of_forall_polar_eq_zero {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) {X Y : Submodule K V}
    (hXY : IsCompl Y (qPerp Q X)) {x : V} (hx : x ∈ X)
    (h : ∀ y ∈ Y, polar Q x y = 0) : x = 0 := by
  refine eq_zero_of_polar_eq_zero hQ fun v => ?_
  have hv : v ∈ Y ⊔ qPerp Q X := by rw [hXY.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
  rw [polar_add_right, h y hy, mem_qPerp.mp hd x hx, add_zero]

private theorem exists_eichler_params [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0) {X Y : Submodule K V}
    (hX : ∀ x ∈ X, Q x = 0) (hY : ∀ y ∈ Y, Q y = 0) (hXY : IsCompl Y (qPerp Q X))
    (hdim : 2 * Module.finrank K X < Module.finrank K V ∨ 3 ≤ Module.finrank K X)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hx0 : x ≠ 0) :
    ∃ w ∈ qPerp Q X, ∃ w' ∈ qPerp Q Y,
      polar Q y w = 0 ∧ polar Q x w' = 0 ∧ polar Q w w' ≠ 0 := by
  classical
  have hXperp : X ≤ qPerp Q X := le_qPerp_of_singular hX
  have hk_le : Module.finrank K X ≤ Module.finrank K V := Submodule.finrank_le X
  have hperp_fin : Module.finrank K (qPerp Q X) = Module.finrank K V - Module.finrank K X := by
    rw [qPerp_eq_orthogonal]
    exact LinearMap.BilinForm.finrank_orthogonal hQ X
  have hYfin : Module.finrank K Y = Module.finrank K X := by
    have h := Submodule.finrank_add_eq_of_isCompl hXY
    rw [hperp_fin] at h
    omega
  have hXYbot : X ⊓ Y = ⊥ := by
    refine le_antisymm ?_ bot_le
    rintro z ⟨hzX, hzY⟩
    have hmem : z ∈ Y ⊓ qPerp Q X := ⟨hzY, hXperp hzX⟩
    rw [hXY.inf_eq_bot] at hmem
    simpa using hmem
  have hpairX : ∀ x ∈ X, (∀ y ∈ Y, polar Q x y = 0) → x = 0 :=
    fun x hx h => eq_zero_of_forall_polar_eq_zero hQ hXY hx h
  rcases hdim with hA | hB
  ·
    have hsupfin : Module.finrank K ↥(X ⊔ Y) = Module.finrank K X + Module.finrank K X := by
      have h := Submodule.finrank_sup_add_finrank_inf_eq X Y
      rw [hXYbot, hYfin, finrank_bot, add_zero] at h
      omega
    have hMfin : Module.finrank K ↥(qPerp Q X ⊓ qPerp Q Y) =
        Module.finrank K V - (Module.finrank K X + Module.finrank K X) := by
      rw [← qPerp_sup, qPerp_eq_orthogonal, LinearMap.BilinForm.finrank_orthogonal hQ, hsupfin]
    set M : Submodule K V := qPerp Q X ⊓ qPerp Q Y with hMdef
    have hM0 : M ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at hMfin
      omega
    have hXinfM : X ⊓ M = ⊥ := by
      refine le_antisymm ?_ bot_le
      rintro z ⟨hzX, hzXp, hzYp⟩
      exact hpairX z hzX fun y hy => by rw [polar_comm]; exact mem_qPerp.mp hzYp y hy
    have hXM : qPerp Q X = X ⊔ M := by
      have hle : X ⊔ M ≤ qPerp Q X := by
        intro z hz
        obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
        exact (qPerp Q X).add_mem (hXperp ha) hb.1
      have hfin : Module.finrank K ↥(X ⊔ M) = Module.finrank K ↥(qPerp Q X) := by
        have h := Submodule.finrank_sup_add_finrank_inf_eq X M
        rw [hXinfM, finrank_bot, add_zero, hMfin] at h
        rw [hperp_fin]
        omega
      exact (Submodule.eq_of_le_of_finrank_eq hle hfin).symm
    have hMnd : PolarNondegOn Q M := by
      intro m hmM hmOrth
      refine eq_zero_of_polar_eq_zero hQ fun v => ?_
      have hv : v ∈ Y ⊔ qPerp Q X := by rw [hXY.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.mp hv
      have hd' : d ∈ X ⊔ M := by rw [← hXM]; exact hd
      obtain ⟨a, ha, t, ht, rfl⟩ := Submodule.mem_sup.mp hd'
      rw [polar_add_right, polar_add_right, polar_comm Q m y, mem_qPerp.mp hmM.2 y hy,
        polar_comm Q m a, mem_qPerp.mp hmM.1 a ha, hmOrth t ht]
      simp
    have hex : ∃ w ∈ M, polar Q w w ≠ 0 := by
      by_contra h
      push Not at h
      obtain ⟨m, hmM, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hM0
      refine hm0 (hMnd m hmM fun w hw => ?_)
      have h0 : polar Q (m + w) (m + w) = 0 := h (m + w) (M.add_mem hmM hw)
      simp only [polar_add_left, polar_add_right, h m hmM, h w hw, polar_comm Q w m,
        zero_add, add_zero] at h0
      have h2m : (2 : K) * polar Q m w = 0 := by rw [two_mul]; exact h0
      exact (mul_eq_zero.mp h2m).resolve_left h2
    obtain ⟨w, hwM, hww⟩ := hex
    exact ⟨w, hwM.1, w, hwM.2, mem_qPerp.mp hwM.2 y hy, mem_qPerp.mp hwM.1 x hx, hww⟩
  ·
    have hk3 : 3 ≤ Module.finrank K X := hB
    have hUfin : Module.finrank K (LinearMap.range ((polarBilin Q y).comp X.subtype)) +
        Module.finrank K (LinearMap.ker ((polarBilin Q y).comp X.subtype)) =
        Module.finrank K X :=
      LinearMap.finrank_range_add_finrank_ker ((polarBilin Q y).comp X.subtype)
    have hrange_le : Module.finrank K (LinearMap.range ((polarBilin Q y).comp X.subtype)) ≤ 1 := by
      calc Module.finrank K (LinearMap.range ((polarBilin Q y).comp X.subtype)) ≤
          Module.finrank K K := Submodule.finrank_le _
        _ = 1 := Module.finrank_self K
    have hU2 : 2 ≤ Module.finrank K (LinearMap.ker ((polarBilin Q y).comp X.subtype)) := by
      omega
    have hpairUV : ∃ u : LinearMap.ker ((polarBilin Q y).comp X.subtype),
        ∃ v : LinearMap.ker ((polarBilin Q x).comp Y.subtype),
          polar Q (u : V) (v : V) ≠ 0 := by
      by_contra h
      push Not at h
      have hUle : ∀ u : LinearMap.ker ((polarBilin Q y).comp X.subtype),
          (u : V) ∈ Submodule.span K {x} := by
        intro u
        set fu : Y →ₗ[K] K := (polarBilin Q (u : V)).comp Y.subtype with hfudef
        have hker : LinearMap.ker ((polarBilin Q x).comp Y.subtype) ≤ LinearMap.ker fu := by
          intro v hv
          rw [LinearMap.mem_ker] at hv ⊢
          have h1 := h u ⟨v, hv⟩
          rw [hfudef, LinearMap.comp_apply, polarBilin_apply_apply]
          exact h1
        have hspan : fu ∈ Submodule.span K {((polarBilin Q x).comp Y.subtype)} := by
          simpa using FiniteDimensional.mem_span_of_iInf_ker_le_ker
            (L := fun _ : Unit => (polarBilin Q x).comp Y.subtype) (K := fu) (by simpa using hker)
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hspan
        have hux : (u : V) = c • x := by
          have hzero : (u : V) - c • x = 0 := by
            refine hpairX ((u : V) - c • x) (X.sub_mem (u : X).2 (X.smul_mem c hx))
              fun y' hy' => ?_
            have hcy : polar Q (u : V) y' = c * polar Q x y' := by
              have h1 := LinearMap.congr_fun hc ⟨y', hy'⟩
              simp only [hfudef, LinearMap.comp_apply, polarBilin_apply_apply,
                LinearMap.smul_apply, smul_eq_mul] at h1
              exact h1.symm
            rw [polar_sub_left, polar_smul_left_eq, hcy, sub_self]
          rwa [sub_eq_zero] at hzero
        rw [hux]
        exact Submodule.smul_mem _ c (Submodule.mem_span_singleton_self x)
      let φ : LinearMap.ker ((polarBilin Q y).comp X.subtype) →ₗ[K] Submodule.span K {x} :=
        { toFun := fun u => ⟨(u : V), hUle u⟩
          map_add' := fun u v => Subtype.ext rfl
          map_smul' := fun c u => Subtype.ext rfl }
      have hinj : Function.Injective φ := by
        intro u v huv
        have h1 : (u : V) = (v : V) := congrArg (fun z : Submodule.span K {x} => (z : V)) huv
        exact Subtype.ext (Subtype.ext h1)
      have hle := LinearMap.finrank_le_finrank_of_injective hinj
      rw [finrank_span_singleton hx0] at hle
      omega
    obtain ⟨u, v, huv⟩ := hpairUV
    have hyu : polar Q y (u : V) = 0 := by
      have h1 := LinearMap.mem_ker.mp u.2
      rw [LinearMap.comp_apply, polarBilin_apply_apply] at h1
      exact h1
    have hxv : polar Q x (v : V) = 0 := by
      have h1 := LinearMap.mem_ker.mp v.2
      rw [LinearMap.comp_apply, polarBilin_apply_apply] at h1
      exact h1
    exact ⟨(u : V), hXperp (u : X).2, (v : V), le_qPerp_of_singular hY (v : Y).2, hyu, hxv,
      huv⟩

private theorem eichler_mem_sup_of_polar_eq_zero [FiniteDimensional K V]
    {Q : QuadraticForm K V} (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0)
    {X Y : Submodule K V} (hX : ∀ x ∈ X, Q x = 0) (hY : ∀ y ∈ Y, Q y = 0)
    (hXY : IsCompl Y (qPerp Q X))
    (hdim : 2 * Module.finrank K X < Module.finrank K V ∨ 3 ≤ Module.finrank K X)
    {x y : V} (hx : x ∈ X) (hy : y ∈ Y) (hx0 : x ≠ 0) (hxy : polar Q x y = 0) :
    eichler Q x y ∈ eichlerRad Q X ⊔ eichlerRad Q Y := by
  obtain ⟨w, hw, w', hw', hyw, hxw', hww'⟩ :=
    exists_eichler_params hQ h2 hX hY hXY hdim hx hy hx0
  set c : K := polar Q w w' with hcdef
  have hc : c ≠ 0 := hww'
  set w'' : V := c⁻¹ • w' with hw''def
  have hw'' : w'' ∈ qPerp Q Y := (qPerp Q Y).smul_mem _ hw'
  have hxw'' : polar Q x w'' = 0 := by
    rw [hw''def, polar_smul_right_eq, hxw', mul_zero]
  have hyw'' : polar Q y w'' = 0 := by
    rw [hw''def, polar_smul_right_eq, mem_qPerp.mp hw' y hy, mul_zero]
  have hc1 : polar Q w w'' = 1 := by
    rw [hw''def, polar_smul_right_eq, hcdef, inv_mul_cancel₀ hc]
  have hcomm := CFSG.SignalizerFunctorTheorem.NonLocal.Orth.commutator_eichler_heis
    (he₂ := hY y hy) (h12 := hxy) (hw₁ := mem_qPerp.mp hw x hx) (hw₂ := hyw)
    (hw'₁ := hxw'') (hw'₂ := hyw'')
  rw [hc1, one_smul] at hcomm
  rw [← hcomm, commutatorElement_def]
  have hA : eichler Q y w'' ∈ eichlerRad Q X ⊔ eichlerRad Q Y :=
    Subgroup.mem_sup_right (eichler_mem_eichlerRad hy hw'')
  have hB : eichler Q x w ∈ eichlerRad Q X ⊔ eichlerRad Q Y :=
    Subgroup.mem_sup_left (eichler_mem_eichlerRad hx hw)
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hA) hB)
    (Subgroup.inv_mem _ (Subgroup.inv_mem _ hA))) (Subgroup.inv_mem _ hB)

theorem elementaryGroup_le_eichlerRad_sup [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : (polarBilin Q).Nondegenerate) (h2 : (2 : K) ≠ 0)
    {X Y : Submodule K V} (hX : ∀ x ∈ X, Q x = 0) (hY : ∀ y ∈ Y, Q y = 0)
    (hXY : IsCompl Y (qPerp Q X)) (hX0 : X ≠ ⊥)
    (hdim : 2 * Module.finrank K X < Module.finrank K V ∨ 3 ≤ Module.finrank K X) :
    elementaryGroup Q ≤ eichlerRad Q X ⊔ eichlerRad Q Y := by
  classical
  have hXperp : X ≤ qPerp Q X := le_qPerp_of_singular hX
  have hk_le : Module.finrank K X ≤ Module.finrank K V := Submodule.finrank_le X
  have hperp_fin : Module.finrank K (qPerp Q X) = Module.finrank K V - Module.finrank K X := by
    rw [qPerp_eq_orthogonal]
    exact LinearMap.BilinForm.finrank_orthogonal hQ X
  have hYfin : Module.finrank K Y = Module.finrank K X := by
    have h := Submodule.finrank_add_eq_of_isCompl hXY
    rw [hperp_fin] at h
    omega
  have hpairX : ∀ x ∈ X, (∀ y ∈ Y, polar Q x y = 0) → x = 0 :=
    fun x hx h => eq_zero_of_forall_polar_eq_zero hQ hXY hx h
  have hYperp_fin : Module.finrank K (qPerp Q Y) =
      Module.finrank K V - Module.finrank K X := by
    rw [qPerp_eq_orthogonal, LinearMap.BilinForm.finrank_orthogonal hQ, hYfin]
  have hXYsym : IsCompl X (qPerp Q Y) := by
    rw [Submodule.isCompl_iff_disjoint _ _ (by rw [hYperp_fin]; omega), disjoint_iff]
    refine le_antisymm ?_ bot_le
    rintro z ⟨hzX, hzYp⟩
    exact hpairX z hzX fun y hy => by rw [polar_comm]; exact mem_qPerp.mp hzYp y hy
  have hYdim : 2 * Module.finrank K Y < Module.finrank K V ∨
      3 ≤ Module.finrank K Y := by
    rwa [hYfin]
  set H : Subgroup (V ≃ₗ[K] V) := eichlerRad Q X ⊔ eichlerRad Q Y with hH
  have hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hH]
    exact (sup_le (eichlerRad_le_elementaryGroup Q X) (eichlerRad_le_elementaryGroup Q Y)).trans
      (elementaryGroup_le_orthogonalGroup Q)
  have hrootX : ∀ x ∈ X, x ≠ 0 → IsRootCenter Q H x := by
    intro x hx hx0
    refine ⟨hx0, hX x hx, fun z hz => ?_⟩
    have hz' : z ∈ Y ⊔ qPerp Q X := by rw [hXY.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨y, hy, d, hd, rfl⟩ := Submodule.mem_sup.mp hz'
    have hxy : polar Q x y = 0 := by
      rw [polar_add_right, mem_qPerp.mp hd x hx, add_zero] at hz
      exact hz
    have hExd : eichler Q x d ∈ H := Subgroup.mem_sup_left (eichler_mem_eichlerRad hx hd)
    have hExy : eichler Q x y ∈ H := by
      by_cases hy0 : y = 0
      · rw [hy0, eichler_zero_right]
        exact H.one_mem
      · exact eichler_mem_sup_of_polar_eq_zero hQ h2 hX hY hXY hdim hx hy hx0 hxy
    rw [← eichler_mul hxy (mem_qPerp.mp hd x hx)]
    exact H.mul_mem hExy hExd
  have hrootY : ∀ y ∈ Y, y ≠ 0 → IsRootCenter Q H y := by
    intro y hy hy0
    refine ⟨hy0, hY y hy, fun z hz => ?_⟩
    have hz' : z ∈ X ⊔ qPerp Q Y := by rw [hXYsym.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨x, hx, d, hd, rfl⟩ := Submodule.mem_sup.mp hz'
    have hyx : polar Q y x = 0 := by
      rw [polar_add_right, mem_qPerp.mp hd y hy, add_zero] at hz
      exact hz
    have hEyd : eichler Q y d ∈ H := Subgroup.mem_sup_right (eichler_mem_eichlerRad hy hd)
    have hEyx : eichler Q y x ∈ H := by
      by_cases hx0 : x = 0
      · rw [hx0, eichler_zero_right]
        exact H.one_mem
      · simpa only [sup_comm] using
          eichler_mem_sup_of_polar_eq_zero hQ h2 hY hX hXYsym hYdim hy hx hy0 hyx
    rw [← eichler_mul hyx (mem_qPerp.mp hd y hy)]
    exact H.mul_mem hEyx hEyd
  have hk0 : Module.finrank K X ≠ 0 := by
    intro h
    exact hX0 (Submodule.finrank_eq_zero.mp h)
  obtain ⟨x0, hx0X, hx00⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX0
  have hex0 : ∃ y0 ∈ Y, polar Q x0 y0 ≠ 0 := by
    by_contra h
    push Not at h
    exact hx00 (hpairX x0 hx0X h)
  obtain ⟨y0, hy0Y, hy0ne⟩ := hex0
  have hex : ∃ y0 ∈ Y, polar Q x0 y0 = 1 :=
    ⟨(polar Q x0 y0)⁻¹ • y0, Y.smul_mem _ hy0Y, by
      rw [polar_smul_right_eq, inv_mul_cancel₀ hy0ne]⟩
  obtain ⟨y0, hy0Y, hx0y0⟩ := hex
  have hy00 : y0 ≠ 0 := by
    intro h
    rw [h, polar_zero_right Q x0] at hx0y0
    exact zero_ne_one hx0y0
  refine elementaryGroup_le_of_hypPair hQ hHO (HypPair.ofPolarEqOne (hX x0 hx0X) hx0y0) ?_ ?_
  · exact hrootX x0 hx0X hx00
  · simpa [hY y0 hy0Y] using hrootY y0 hy0Y hy00

end CFSG.LieType.SeitzGeneration
