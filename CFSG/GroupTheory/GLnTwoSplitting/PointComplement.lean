module

public import CFSG.GroupTheory.GLnTwoSplitting.PointStabilizer
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover
public import CFSG.LinearAlgebra.LinearGroups.Perfect
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverHigher

public section

namespace CFSG.GroupTheory.GLnTwoSplitting

open Module Submodule
open CFSG.LocalAnalysis.ComponentInitial
open scoped IsMulCommutative

namespace NatExt

variable {G : Type*} [Group G] {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
  {X : NatExt G E} [FiniteDimensional (ZMod 2) E] {hE : 6 ≤ finrank (ZMod 2) E} {e₀ : E}
  {he₀ : e₀ ≠ 0}

instance canonicalGroup_isMulCommutative : IsMulCommutative (X.canonicalGroup hE he₀) :=
  ⟨⟨fun a b => Subtype.ext (canonicalGroup_commute a.2 b.2)⟩⟩

theorem ι_e₀_mem_canonicalGroup : X.ι e₀ ∈ X.canonicalGroup hE he₀ :=
  ι_mem_canonicalGroup_iff.2 (mem_span_singleton_self e₀)

theorem canonicalGroup_le_stab : X.canonicalGroup hE he₀ ≤ X.stab e₀ :=
  canonicalGroup_le_centre.trans (centre_le_stab e₀)

theorem exists_mem_canonicalGroup_of_mem_centre {g : G} (hg : g ∈ X.centre e₀) :
    ∃ w ∈ X.canonicalGroup hE he₀, ∃ v, g = w * X.ι v := by
  obtain ⟨π₀, -, hπ₀⟩ := exists_dual_eq_one_of_notMem (S := ⊥) (w := e₀)
    (by rw [mem_bot]; exact he₀)
  have hgt := π_eq_transvection_coeff hπ₀ hg
  by_cases hc : X.coeff π₀ g = 0
  · obtain ⟨v, rfl⟩ := (X.ker_iff g).1 (by
      rw [hgt]
      ext w
      rw [transvection_apply, hc, LinearMap.zero_apply, zero_smul, add_zero]
      rfl)
    exact ⟨1, one_mem _, v, (one_mul _).symm⟩
  · obtain ⟨a, ha⟩ := X.exists_isCanonical hE he₀ (coeff_apply_e₀ π₀ hg) hc
    obtain ⟨v, hv⟩ := X.exists_eq_mul_ι (g := a) (g' := g) (by rw [ha.1, hgt])
    exact ⟨a, Or.inr ⟨_, _, hc, ha⟩, v, hv⟩

theorem exists_complement_data :
    ∃ W₀ : Subgroup G, W₀ ≤ X.canonicalGroup hE he₀ ∧ X.ι e₀ ∉ W₀ ∧
      (∀ g ∈ X.canonicalGroup hE he₀, g ∈ W₀ ∨ g * X.ι e₀ ∈ W₀) ∧
      ∀ h ∈ X.stab e₀, ∃ v, X.ι v * h ∈ Subgroup.normalizer (W₀ : Set G) := by
  classical
  set W := X.canonicalGroup hE he₀ with hWdef
  let _ : Module (ZMod 2) (Additive W) := AddCommGroup.zmodModule (n := 2) fun x => by
    rw [two_nsmul]
    exact congrArg Additive.ofMul (Subtype.ext (canonicalGroup_mul_self x.toMul.2))
  have hz : X.ι e₀ ∈ W := ι_e₀_mem_canonicalGroup
  have hz0 : (Additive.ofMul (⟨X.ι e₀, hz⟩ : W)) ∉ (⊥ : Submodule (ZMod 2) (Additive W)) := by
    rw [mem_bot]
    intro h
    exact he₀ (X.ι_eq_one_iff.1 (congrArg Subtype.val (Additive.ofMul.injective
      (h.trans ofMul_one.symm))))
  obtain ⟨lamL, -, hlamL⟩ := exists_dual_eq_one_of_notMem hz0
  obtain ⟨lam, lam_of_mem⟩ : ∃ lam : G → ZMod 2,
      ∀ {g} (hg : g ∈ W), lam g = lamL (Additive.ofMul ⟨g, hg⟩) :=
    ⟨fun g => if hg : g ∈ W then lamL (Additive.ofMul ⟨g, hg⟩) else 0, fun hg => by simp [hg]⟩
  have lam_mul : ∀ {g g'}, g ∈ W → g' ∈ W → lam (g * g') = lam g + lam g' := by
    intro g g' hg hg'
    rw [lam_of_mem (mul_mem hg hg'), lam_of_mem hg, lam_of_mem hg', ← map_add]
    rfl
  have lam_z : lam (X.ι e₀) = 1 := by rw [lam_of_mem hz]; exact hlamL
  have lam_one : lam 1 = 0 := by
    have h1 := lam_mul (one_mem W) (one_mem W)
    rw [one_mul, zmod_two_add_self] at h1
    exact h1
  have lam_ι : ∀ c : ZMod 2, lam (X.ι (c • e₀)) = c := by
    intro c
    rcases zmod_two_eq_zero_or_one c with rfl | rfl
    · rw [zero_smul, X.ι_zero, lam_one]
    · rw [one_smul, lam_z]
  let W₀ : Subgroup G :=
    { carrier := {g | g ∈ W ∧ lam g = 0}
      mul_mem' := fun {g g'} hg hg' => ⟨mul_mem hg.1 hg'.1, by
        rw [lam_mul hg.1 hg'.1, hg.2, hg'.2, add_zero]⟩
      one_mem' := ⟨one_mem W, lam_one⟩
      inv_mem' := fun {g} hg => by
        rw [inv_eq_of_mul_eq_one_left (canonicalGroup_mul_self hg.1)]
        exact hg }
  have hW₀ : ∀ {g}, g ∈ W₀ ↔ g ∈ W ∧ lam g = 0 := Iff.rfl
  refine ⟨W₀, fun g hg => hg.1, fun h => by rw [(hW₀.1 h).2] at lam_z; exact zero_ne_one lam_z,
    fun g hg => ?_, fun h hh => ?_⟩
  · rcases zmod_two_eq_zero_or_one (lam g) with h0 | h1
    · exact Or.inl ⟨hg, h0⟩
    · exact Or.inr ⟨mul_mem hg hz, by rw [lam_mul hg hz, h1, lam_z]; rfl⟩
  obtain ⟨π₀, -, hπ₀⟩ := exists_dual_eq_one_of_notMem (S := ⊥) (w := e₀)
    (by rw [mem_bot]; exact he₀)
  have hhinv : h⁻¹ ∈ X.stab e₀ := inv_mem hh
  have hconjW : ∀ {g}, g ∈ W → h⁻¹ * g * h ∈ W := fun hg => by
    have := conj_mem_canonicalGroup hhinv hg
    rwa [inv_inv] at this
  let κ : Additive W →ₗ[ZMod 2] Dual (ZMod 2) E :=
    { toFun := fun x => X.coeff π₀ (x.toMul : G)
      map_add' := fun x y => coeff_mul hπ₀ (canonicalGroup_le_centre x.toMul.2)
        (canonicalGroup_le_centre y.toMul.2)
      map_smul' := fun c x => by
        rw [RingHom.id_apply]
        rcases zmod_two_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul, zero_smul]
          ext w
          change π₀ (X.π 1 w + w) = 0
          rw [map_one]
          change π₀ (w + w) = 0
          rw [two_add_self, map_zero]
        · rw [one_smul, one_smul] }
  let μ : Additive W →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => lam (x.toMul : G) + lam (h⁻¹ * (x.toMul : G) * h)
      map_add' := fun x y => by
        change lam ((x.toMul : G) * y.toMul) + lam (h⁻¹ * ((x.toMul : G) * y.toMul) * h) = _
        rw [show h⁻¹ * ((x.toMul : G) * y.toMul) * h =
          (h⁻¹ * x.toMul * h) * (h⁻¹ * y.toMul * h) by group,
          lam_mul x.toMul.2 y.toMul.2, lam_mul (hconjW x.toMul.2) (hconjW y.toMul.2)]
        change _ = (lam (x.toMul : G) + lam (h⁻¹ * (x.toMul : G) * h)) +
          (lam (y.toMul : G) + lam (h⁻¹ * (y.toMul : G) * h))
        abel
      map_smul' := fun c x => by
        rw [RingHom.id_apply]
        rcases zmod_two_eq_zero_or_one c with rfl | rfl
        · rw [zero_smul, zero_smul]
          change lam 1 + lam (h⁻¹ * 1 * h) = 0
          rw [mul_one, inv_mul_cancel, lam_one, add_zero]
        · rw [one_smul, one_smul] }
  obtain ⟨v, hv'⟩ := exists_eval_of_ker_le κ μ fun x hx => by
    have hx1 : X.π (x.toMul : G) = 1 := by
      rw [π_eq_transvection_coeff hπ₀ (canonicalGroup_le_centre x.toMul.2)]
      ext w
      rw [transvection_apply, show X.coeff π₀ (x.toMul : G) = 0 from hx, LinearMap.zero_apply,
        zero_smul, add_zero]
      rfl
    obtain ⟨v, hv⟩ := (X.ker_iff _).1 hx1
    have hvW : X.ι v ∈ W := hv ▸ x.toMul.2
    obtain ⟨c, rfl⟩ := mem_span_singleton.1 (ι_mem_canonicalGroup_iff.1 hvW)
    change lam (x.toMul : G) + lam (h⁻¹ * (x.toMul : G) * h) = 0
    rw [← hv, X.conj_ι', apply_eq_of_mem_span ((LinearEquiv.symm_apply_eq _).2 hh.symm)
      (smul_mem _ _ (mem_span_singleton_self e₀)), zmod_two_add_self]
  have hv : ∀ g (hg : g ∈ W), lam g + lam (h⁻¹ * g * h) = X.coeff π₀ g v :=
    fun g hg => hv' (Additive.ofMul ⟨g, hg⟩)
  refine ⟨v, (Subgroup.mem_normalizer_iff).2 fun g => ?_⟩
  have hxe₀ : X.ι v * h ∈ X.stab e₀ := mul_mem (centre_le_stab e₀ (V_le_centre e₀ (X.ι_mem_V v))) hh
  by_cases hg : g ∈ W
  · have hg' : h * g * h⁻¹ ∈ W := conj_mem_canonicalGroup hh hg
    have hconj : X.ι v * h * g * (X.ι v * h)⁻¹ =
        (h * g * h⁻¹) * X.ι (X.coeff π₀ (h * g * h⁻¹) v • e₀) := by
      rw [← X.ι_conj_of_lift (coeff_apply_e₀ π₀ (canonicalGroup_le_centre hg'))
        (π_eq_transvection_coeff hπ₀ (canonicalGroup_le_centre hg'))]
      group
    have hmem : X.ι v * h * g * (X.ι v * h)⁻¹ ∈ W := conj_mem_canonicalGroup hxe₀ hg
    have hlam : lam (X.ι v * h * g * (X.ι v * h)⁻¹) = lam g := by
      rw [hconj, lam_mul hg' (ι_mem_canonicalGroup_iff.2
        (smul_mem _ _ (mem_span_singleton_self e₀))), lam_ι, ← hv _ hg']
      rw [show h⁻¹ * (h * g * h⁻¹) * h = g by group, ← add_assoc, zmod_two_add_self, zero_add]
    rw [hW₀, hW₀, hlam]
    exact ⟨fun h1 => ⟨hmem, h1.2⟩, fun h1 => ⟨hg, h1.2⟩⟩
  · refine ⟨fun h1 => absurd h1.1 hg, fun h1 => absurd ?_ hg⟩
    have := conj_mem_canonicalGroup (inv_mem hxe₀) h1.1
    rwa [show (X.ι v * h)⁻¹ * (X.ι v * h * g * (X.ι v * h)⁻¹) * (X.ι v * h)⁻¹⁻¹ = g by group]
      at this

theorem mem_span_of_ι_mem_normalizer {W₀ : Subgroup G} (hz : X.ι e₀ ∉ W₀)
    (hcov : ∀ g ∈ X.canonicalGroup hE he₀, g ∈ W₀ ∨ g * X.ι e₀ ∈ W₀) {v : E}
    (hv : X.ι v ∈ Subgroup.normalizer (W₀ : Set G)) : v ∈ (ZMod 2) ∙ e₀ := by
  by_contra hv'
  obtain ⟨ψ, hψ, hψv⟩ := exists_dual_eq_one_of_notMem hv'
  have hψe₀ : ψ e₀ = 0 := hψ e₀ (mem_span_singleton_self e₀)
  have hψ0 : ψ ≠ 0 := fun h => by rw [h, LinearMap.zero_apply] at hψv; exact zero_ne_one hψv
  obtain ⟨a, ha⟩ := X.exists_isCanonical hE he₀ hψe₀ hψ0
  obtain ⟨b, hbW₀, hb⟩ : ∃ b ∈ W₀, X.π b = LinearEquiv.transvection hψe₀ := by
    rcases hcov a (Or.inr ⟨ψ, hψe₀, hψ0, ha⟩) with h | h
    · exact ⟨a, h, ha.1⟩
    · exact ⟨a * X.ι e₀, h, by rw [map_mul, X.π_ι, mul_one, ha.1]⟩
  have h1 : X.ι v * b * (X.ι v)⁻¹ ∈ W₀ := (Subgroup.mem_normalizer_iff.1 hv b).1 hbW₀
  rw [X.ι_conj_of_lift hψe₀ hb, hψv, one_smul] at h1
  exact hz (by simpa using mul_mem (inv_mem hbW₀) h1)

theorem finrank_quotient_span (he₀ : e₀ ≠ 0) :
    finrank (ZMod 2) (E ⧸ (ZMod 2) ∙ e₀) + 1 = finrank (ZMod 2) E := by
  rw [← finrank_span_singleton (K := ZMod 2) he₀]
  exact Submodule.finrank_quotient_add_finrank _

theorem exists_complement_of_data [Finite G] {W₀ : Subgroup G}
    (hW₀W : W₀ ≤ X.canonicalGroup hE he₀) (hz : X.ι e₀ ∉ W₀)
    (hcov : ∀ g ∈ X.canonicalGroup hE he₀, g ∈ W₀ ∨ g * X.ι e₀ ∈ W₀)
    (hnorm : ∀ h ∈ X.stab e₀, ∃ v, X.ι v * h ∈ Subgroup.normalizer (W₀ : Set G)) :
    ∃ K : Subgroup G, X.V ⊓ K = ⊥ ∧ X.V ⊔ K = X.stab e₀ := by
  classical
  set W := X.canonicalGroup hE he₀ with hWdef
  set m := finrank (ZMod 2) (E ⧸ (ZMod 2) ∙ e₀) with hmdef
  have hm : 5 ≤ m := by have := finrank_quotient_span he₀; omega
  set θ := X.stabHom e₀ hmdef.symm
  set Hh := Subgroup.normalizer (W₀ : Set G) ⊓ X.stab e₀ with hHh
  have hHhstab : Hh ≤ X.stab e₀ := inf_le_right
  have hWHh : W ≤ Hh := by
    intro w hw
    refine ⟨Subgroup.mem_normalizer_iff.2 fun g => ⟨fun hg => ?_, fun hg => ?_⟩,
      canonicalGroup_le_stab hw⟩
    · rw [canonicalGroup_commute hw (hW₀W hg), mul_inv_cancel_right]
      exact hg
    · have hgW : g ∈ W := by
        have := mul_mem (mul_mem (inv_mem hw) (hW₀W hg)) hw
        rwa [show w⁻¹ * (w * g * w⁻¹) * w = g by group] at this
      rwa [canonicalGroup_commute hw hgW, mul_inv_cancel_right] at hg
  have hW₀Hh : W₀ ≤ Hh := hW₀W.trans hWHh
  let θH : Hh →* LinearFlag.projectiveSL m (ZMod 2) := θ.comp (Subgroup.inclusion hHhstab)
  have hθH : ∀ x : Hh, θH x = 1 ↔ (x : G) ∈ X.centre e₀ := fun x =>
    stabHom_eq_one_iff hmdef.symm (Subgroup.inclusion hHhstab x)
  let W₀' := W₀.subgroupOf Hh
  have hW₀'n : W₀'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hW₀Hh).2 inf_le_left
  have hW₀'ker : W₀' ≤ θH.ker := fun x hx =>
    (hθH x).2 (canonicalGroup_le_centre (hW₀W hx))
  let Y := Hh ⧸ W₀'
  let θY : Y →* LinearFlag.projectiveSL m (ZMod 2) := QuotientGroup.lift W₀' θH hW₀'ker
  have hθY : ∀ x : Hh, θY (QuotientGroup.mk x) = θH x := fun x => rfl
  have hθYs : Function.Surjective θY := by
    intro y
    obtain ⟨⟨h, hh⟩, rfl⟩ := X.stabHom_surjective hmdef.symm y
    obtain ⟨v, hv⟩ := hnorm h hh
    have hvh : X.ι v * h ∈ X.stab e₀ :=
      mul_mem (centre_le_stab e₀ (V_le_centre e₀ (X.ι_mem_V v))) hh
    refine ⟨QuotientGroup.mk ⟨X.ι v * h, hv, hvh⟩, ?_⟩
    rw [hθY]
    change θ ⟨X.ι v * h, hvh⟩ = θ ⟨h, hh⟩
    rw [show (⟨X.ι v * h, hvh⟩ : X.stab e₀) =
      ⟨X.ι v, centre_le_stab e₀ (V_le_centre e₀ (X.ι_mem_V v))⟩ * ⟨h, hh⟩ from rfl, map_mul,
      (stabHom_eq_one_iff hmdef.symm _).2 (V_le_centre e₀ (X.ι_mem_V v)), one_mul]
  have hzHh : X.ι e₀ ∈ Hh := hWHh ι_e₀_mem_canonicalGroup
  let z : Y := QuotientGroup.mk ⟨X.ι e₀, hzHh⟩
  have hker : ∀ y : Y, θY y = 1 → y = 1 ∨ y = z := by
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [hθY, hθH] at hy
    obtain ⟨w, hw, v, hxv⟩ := exists_mem_canonicalGroup_of_mem_centre (hE := hE) (he₀ := he₀) hy
    have hvHh : X.ι v ∈ Subgroup.normalizer (W₀ : Set G) := by
      have : X.ι v = w⁻¹ * x := by rw [hxv]; group
      rw [this]
      exact mul_mem (inv_mem (hWHh hw).1) x.2.1
    have hvspan := mem_span_of_ι_mem_normalizer hz hcov hvHh
    have hxW : (x : G) ∈ W := by
      rw [hxv]
      exact mul_mem hw (ι_mem_canonicalGroup_iff.2 hvspan)
    rcases hcov x hxW with h | h
    · exact Or.inl ((QuotientGroup.eq_one_iff x).2 h)
    · refine Or.inr (QuotientGroup.eq.2 ?_)
      change ((x : G))⁻¹ * X.ι e₀ ∈ W₀
      have hc : X.ι e₀ * x = x * X.ι e₀ :=
        ι_mul_comm_of_apply (mem_span_singleton_self e₀) (hHhstab x.2)
      have : ((x : G))⁻¹ * X.ι e₀ = ((x : G) * X.ι e₀)⁻¹ := by
        calc ((x : G))⁻¹ * X.ι e₀ = (x : G)⁻¹ * (X.ι e₀ * x) * (x : G)⁻¹ := by group
          _ = (x : G)⁻¹ * (x * X.ι e₀) * (x : G)⁻¹ := by rw [hc]
          _ = ((x : G) * X.ι e₀)⁻¹ := by rw [mul_inv_rev, X.ι_inv]; group
      rw [this]
      exact inv_mem h
  have hzc : z ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    change (QuotientGroup.mk (x * ⟨X.ι e₀, hzHh⟩) : Y) = QuotientGroup.mk (⟨X.ι e₀, hzHh⟩ * x)
    congr 1
    exact Subtype.ext (ι_mul_comm_of_apply (mem_span_singleton_self e₀) (hHhstab x.2)).symm
  have hz1 : z ≠ 1 := fun h => hz ((QuotientGroup.eq_one_iff (N := W₀')
    (⟨X.ι e₀, hzHh⟩ : Hh)).1 h)
  have hzz : z * z = 1 := by
    change (QuotientGroup.mk (⟨X.ι e₀, hzHh⟩ * ⟨X.ι e₀, hzHh⟩ : Hh) : Y) = 1
    rw [show (⟨X.ι e₀, hzHh⟩ * ⟨X.ι e₀, hzHh⟩ : Hh) = 1 from Subtype.ext (X.ι_mul_self e₀)]
    rfl
  have hθz : θY z = 1 := by
    rw [hθY, hθH]
    exact V_le_centre e₀ (X.ι_mem_V e₀)
  have hcen : ∀ y : Y, θY y = 1 → y ∈ Subgroup.center Y := fun y hy => by
    rcases hker y hy with rfl | rfl
    · exact one_mem _
    · exact hzc
  let D : Subgroup Y := commutator Y
  let η : D →* LinearFlag.projectiveSL m (ZMod 2) := θY.comp D.subtype
  have hP : Group.IsPerfect (LinearFlag.projectiveSL m (ZMod 2)) := by
    have := CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := ZMod 2)
      (n := m) (by omega)
    infer_instance
  have hηs : Function.Surjective η := by
    intro y
    have hmap : D.map θY = ⊤ := by
      change (commutator Y).map θY = ⊤
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top_of_surjective _ hθYs, ← commutator_def]
      exact hP.commutator_eq_top
    obtain ⟨d, hd, rfl⟩ : y ∈ D.map θY := hmap ▸ Subgroup.mem_top y
    exact ⟨⟨d, hd⟩, rfl⟩
  have hηC : η.ker ≤ Subgroup.center D := by
    intro d hd
    rw [Subgroup.mem_center_iff]
    intro d'
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hcen d hd) d')
  have hη2 : IsPGroup 2 η.ker := by
    intro d
    refine ⟨1, Subtype.ext (Subtype.ext ?_)⟩
    rcases hker ((d : D) : Y) d.2 with h | h
    · change ((d : D) : Y) ^ 2 ^ 1 = 1
      rw [h, one_pow]
    · change ((d : D) : Y) ^ 2 ^ 1 = 1
      rw [h, pow_one, pow_two, hzz]
  have hDperf : Group.IsPerfect D := by
    rw [Subgroup.isPerfect_iff]
    refine le_antisymm (Subgroup.commutator_le_left _ _) ?_
    change commutator Y ≤ ⁅D, D⁆
    rw [commutator_def, Subgroup.commutator_le]
    intro y₁ _ y₂ _
    obtain ⟨d₁, hd₁⟩ := hηs (θY y₁)
    obtain ⟨d₂, hd₂⟩ := hηs (θY y₂)
    have hk₁ : (d₁ : Y)⁻¹ * y₁ ∈ Subgroup.center Y := hcen _ (by
      rw [map_mul, map_inv, ← hd₁]
      exact inv_mul_cancel _)
    have hk₂ : (d₂ : Y)⁻¹ * y₂ ∈ Subgroup.center Y := hcen _ (by
      rw [map_mul, map_inv, ← hd₂]
      exact inv_mul_cancel _)
    have e1 : y₁ = ((d₁ : Y)⁻¹ * y₁) * d₁ := by
      rw [← Subgroup.mem_center_iff.1 hk₁ d₁]
      group
    have e2 : y₂ = ((d₂ : Y)⁻¹ * y₂) * d₂ := by
      rw [← Subgroup.mem_center_iff.1 hk₂ d₂]
      group
    rw [e1, e2, CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center hk₁ hk₂]
    exact Subgroup.commutator_mem_commutator d₁.2 d₂.2
  have hηker := LinearCover.ker_eq_bot_of_projectiveSL (K := ZMod 2) (by rw [Nat.card_zmod])
    hm η hηs hηC hη2
  have hzD : z ∉ D := fun hzD => hz1 (congrArg Subtype.val
    ((MonoidHom.ker_eq_bot_iff η).1 hηker (show η ⟨z, hzD⟩ = η 1 by
      rw [map_one]
      exact hθz)))
  have hW₀K : ∀ {w}, w ∈ W₀ → w ∈ (D.comap (QuotientGroup.mk' W₀')).map Hh.subtype :=
    fun {w} hw => ⟨⟨w, hW₀Hh hw⟩, by
      change (QuotientGroup.mk ⟨w, hW₀Hh hw⟩ : Y) ∈ D
      rw [(QuotientGroup.eq_one_iff (N := W₀') (⟨w, hW₀Hh hw⟩ : Hh)).2 hw]
      exact one_mem _, rfl⟩
  refine ⟨(D.comap (QuotientGroup.mk' W₀')).map Hh.subtype, ?_, ?_⟩
  · rw [eq_bot_iff]
    rintro g ⟨⟨v, rfl⟩, ⟨x, hx, hxg⟩⟩
    have hvspan : v ∈ (ZMod 2) ∙ e₀ :=
      mem_span_of_ι_mem_normalizer hz hcov (by rw [← hxg]; exact x.2.1)
    obtain hv0 | hve := mem_span_singleton_iff_two.1 hvspan
    · rw [hv0, X.ι_zero]
      exact one_mem _
    · exfalso
      refine hzD ?_
      have hxg' : (x : G) = X.ι v := hxg
      have : x = ⟨X.ι e₀, hzHh⟩ := Subtype.ext (by rw [hxg', hve])
      rw [this] at hx
      exact hx
  · apply le_antisymm
    · refine sup_le ((V_le_centre e₀).trans (centre_le_stab e₀)) ?_
      rintro _ ⟨x, -, rfl⟩
      exact hHhstab x.2
    · intro h hh
      obtain ⟨d, hd⟩ := hηs (θ ⟨h, hh⟩)
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (d : Y)
      have hxK : (x : G) ∈ (D.comap (QuotientGroup.mk' W₀')).map Hh.subtype :=
        ⟨x, by
          change (QuotientGroup.mk x : Y) ∈ D
          rw [hx]
          exact d.2, rfl⟩
      have h1 : (x : G)⁻¹ * h ∈ X.centre e₀ := by
        refine (stabHom_eq_one_iff hmdef.symm
          ⟨(x : G)⁻¹ * h, mul_mem (inv_mem (hHhstab x.2)) hh⟩).1 ?_
        rw [show (⟨(x : G)⁻¹ * h, mul_mem (inv_mem (hHhstab x.2)) hh⟩ : X.stab e₀) =
          (Subgroup.inclusion hHhstab x)⁻¹ * ⟨h, hh⟩ from rfl, map_mul, map_inv, ← hd]
        change (θH x)⁻¹ * θY (d : Y) = 1
        rw [← hx, hθY, inv_mul_cancel]
      obtain ⟨w, hw, v, hwv⟩ := exists_mem_canonicalGroup_of_mem_centre (hE := hE) (he₀ := he₀) h1
      have hh' : h = (x : G) * w * X.ι v := by rw [mul_assoc, ← hwv, mul_inv_cancel_left]
      rw [sup_comm]
      rcases hcov w hw with hw0 | hw0
      · rw [hh']
        exact Subgroup.mul_mem_sup (mul_mem hxK (hW₀K hw0)) (X.ι_mem_V v)
      · have : h = ((x : G) * (w * X.ι e₀)) * X.ι (e₀ + v) := by
          rw [hh', X.ι_add]
          calc (x : G) * w * X.ι v = (x : G) * w * (X.ι e₀ * X.ι e₀) * X.ι v := by
                rw [X.ι_mul_self, mul_one]
            _ = _ := by group
        rw [this]
        exact Subgroup.mul_mem_sup (mul_mem hxK (hW₀K hw0)) (X.ι_mem_V _)

theorem exists_complement_stab [Finite G] (hE : 6 ≤ finrank (ZMod 2) E) {e₀ : E}
    (he₀ : e₀ ≠ 0) : ∃ K : Subgroup G, X.V ⊓ K = ⊥ ∧ X.V ⊔ K = X.stab e₀ := by
  obtain ⟨W₀, hW₀W, hz, hcov, hnorm⟩ := exists_complement_data (X := X) (hE := hE) (he₀ := he₀)
  exact exists_complement_of_data hW₀W hz hcov hnorm

end NatExt


end CFSG.GroupTheory.GLnTwoSplitting
