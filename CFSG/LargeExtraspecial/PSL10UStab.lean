module

public import CFSG.LargeExtraspecial.PSL10UExt
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBLFourUnitaryAxisFlag

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.PSLPSU10

open Subgroup Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
  CFSG.LocalAnalysis.GorensteinLyons CFSG.LocalAnalysis.GorensteinLyons.FourUnitary

variable {F : Type*} [Field F] {hF : UnitaryFieldData 2 1 F} {W : Type*} [AddCommGroup W]
  [Module F W] {B : W →ₛₗ[hF.bar] W →ₗ[F] F}

theorem apply_eq_zero_of_mem_span_pair {e f u p : W} (hu : u ∈ Submodule.span F {e, f})
    (hp : p ∈ partnerPerp B e f) : B u p = 0 :=
  Submodule.mem_orthogonalBilin.mp hp u hu

theorem apply_eq_zero_of_mem_partnerPerp (hB : B.IsSymm) {e f u p : W}
    (hu : u ∈ Submodule.span F {e, f}) (hp : p ∈ partnerPerp B e f) : B p u = 0 := by
  rw [← hB.eq u p, apply_eq_zero_of_mem_span_pair hu hp, map_zero]

theorem apply_eq_of_mem_span_pair {g : W →ₗ[F] W} {e f : W} (hge : g e = e) (hgf : g f = f)
    {u : W} (hu : u ∈ Submodule.span F {e, f}) : g u = u := by
  obtain ⟨c, d, rfl⟩ := Submodule.mem_span_pair.mp hu
  rw [map_add, map_smul, map_smul, hge, hgf]

theorem apply_mem_partnerPerp {g : LinearMap.GeneralLinearGroup F W} (hg : g ∈ sesqUnitaryGroup B)
    {e f : W} (hge : (g : W →ₗ[F] W) e = e) (hgf : (g : W →ₗ[F] W) f = f) {p : W}
    (hp : p ∈ partnerPerp B e f) : (g : W →ₗ[F] W) p ∈ partnerPerp B e f := by
  rw [mem_partnerPerp] at hp ⊢
  refine ⟨?_, ?_⟩
  · rw [← hp.1, ← mem_sesqUnitaryGroup.mp hg e p, hge]
  · rw [← hp.2, ← mem_sesqUnitaryGroup.mp hg f p, hgf]

@[expose] noncomputable def stabEF {e f : W}
    (hc : IsCompl (Submodule.span F {e, f}) (partnerPerp B e f)) :
    Subgroup (LinearMap.GeneralLinearGroup F W) :=
  (sesqSpecialUnitaryGroup (B.domRestrict₁₂ (partnerPerp B e f) (partnerPerp B e f))).map
    (extGL hc)

theorem mem_stabEF [FiniteDimensional F W] (hB : B.IsSymm) {e f : W}
    (hc : IsCompl (Submodule.span F {e, f}) (partnerPerp B e f))
    {g : LinearMap.GeneralLinearGroup F W} :
    g ∈ stabEF hc ↔ g ∈ sesqSpecialUnitaryGroup B ∧ (g : W →ₗ[F] W) e = e ∧
      (g : W →ₗ[F] W) f = f := by
  have he : e ∈ Submodule.span F {e, f} := Submodule.subset_span (by simp)
  have hf : f ∈ Submodule.span F {e, f} := Submodule.subset_span (by simp)
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    obtain ⟨hσU, hσd⟩ := mem_sesqSpecialUnitaryGroup.mp hσ
    refine ⟨mem_sesqSpecialUnitaryGroup.mpr ⟨fun x y => ?_, ?_⟩, ?_, ?_⟩
    · exact extEnd_isometry hc (fun u hu p hp => apply_eq_zero_of_mem_span_pair hu hp)
        (fun p hp u hu => apply_eq_zero_of_mem_partnerPerp hB hu hp)
        (fun x y => mem_sesqUnitaryGroup.mp hσU x y) x y
    · rw [coe_extGL, det_extEnd]
      exact hσd
    · exact extEnd_apply_left hc _ he
    · exact extEnd_apply_left hc _ hf
  · rintro ⟨hg, hge, hgf⟩
    have hgU := sesqSpecialUnitaryGroup_le B hg
    have hgi : g⁻¹ ∈ sesqSpecialUnitaryGroup B := inv_mem hg
    have hgie : ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) e = e := by
      conv_lhs => rw [← hge]
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    have hgif : ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f = f := by
      conv_lhs => rw [← hgf]
      rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Module.End.one_apply]
    obtain ⟨g', hg', hg'p⟩ := exists_extGL_eq hc g
      (fun u hu => apply_eq_of_mem_span_pair hge hgf hu)
      (fun p hp => apply_mem_partnerPerp hgU hge hgf hp)
      (fun p hp => apply_mem_partnerPerp (sesqSpecialUnitaryGroup_le B hgi) hgie hgif hp)
    refine ⟨g', mem_sesqSpecialUnitaryGroup.mpr ⟨mem_sesqUnitaryGroup.mpr fun x y => ?_, ?_⟩, hg'⟩
    · change B ((g' : partnerPerp B e f →ₗ[F] partnerPerp B e f) x : W)
        ((g' : partnerPerp B e f →ₗ[F] partnerPerp B e f) y : W) = B x y
      rw [hg'p, hg'p]
      exact mem_sesqUnitaryGroup.mp hgU x y
    · rw [← det_extEnd hc, ← coe_extGL, hg']
      exact (mem_sesqSpecialUnitaryGroup.mp hg).2

theorem commute_hermTransvection_of_apply_eq {g : LinearMap.GeneralLinearGroup F W}
    (hg : g ∈ sesqUnitaryGroup B) {e : W} (hge : (g : W →ₗ[F] W) e = e) :
    (g : W →ₗ[F] W) * hermTransvection B e 1 = hermTransvection B e 1 * (g : W →ₗ[F] W) := by
  ext x
  rw [Module.End.mul_apply, Module.End.mul_apply, hermTransvection_apply, hermTransvection_apply,
    map_add, map_smul, hge, ← mem_sesqUnitaryGroup.mp hg e x, hge]

theorem inv_apply_apply_of_GL (g : LinearMap.GeneralLinearGroup F W) (x : W) :
    ((g⁻¹ : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) ((g : W →ₗ[F] W) x) = x := by
  rw [← Module.End.mul_apply, ← Units.val_mul, inv_mul_cancel, Units.val_one, Module.End.one_apply]

theorem card_eq_mul_card_inf_stabEF [FiniteDimensional F W] (hB : B.IsSymm) {e f : W}
    (hff : B f f = 0) (hef : B e f = 1)
    (hc : IsCompl (Submodule.span F {e, f}) (partnerPerp B e f))
    (huniq : ∀ y : W, B y y = 0 → B e y = 1 →
      ∃! g : axisKernel B e, ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f = y)
    (hRle : axisKernel B e ≤ sesqSpecialUnitaryGroup B)
    {K' : Subgroup (LinearMap.GeneralLinearGroup F W)} (hRK : axisKernel B e ≤ K')
    (hKSU : K' ≤ sesqSpecialUnitaryGroup B) (hKe : ∀ k ∈ K', (k : W →ₗ[F] W) e = e) :
    Nat.card K' = Nat.card (axisKernel B e) * Nat.card ↥(K' ⊓ stabEF hc) := by
  have hiso : ∀ k : K', ∀ x y, B (((k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) x)
      (((k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) y) = B x y := fun k =>
    mem_sesqUnitaryGroup.mp (sesqSpecialUnitaryGroup_le B (hKSU k.2))
  have hy : ∀ k : K', B (((k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f)
      (((k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) = 0 ∧
      B e (((k : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f) = 1 := fun k => by
    refine ⟨by rw [hiso k f f, hff], ?_⟩
    conv_lhs => rw [← hKe k k.2]
    rw [hiso k e f, hef]
  choose r hr using fun k : K' => (huniq _ (hy k).1 (hy k).2).exists
  have hre : ∀ g : axisKernel B e,
      ((g : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) e = e :=
    fun g => (mem_axisKernel.mp g.2).2.1
  have hmemL : ∀ k : K', ((r k : LinearMap.GeneralLinearGroup F W))⁻¹ *
      (k : LinearMap.GeneralLinearGroup F W) ∈ K' ⊓ stabEF hc := fun k => by
    refine ⟨K'.mul_mem (K'.inv_mem (hRK (r k).2)) k.2,
      (mem_stabEF hB hc).mpr ⟨mul_mem (inv_mem (hRle (r k).2)) (hKSU k.2), ?_, ?_⟩⟩
    · rw [Units.val_mul, Module.End.mul_apply, hKe k k.2]
      have h := inv_apply_apply_of_GL ((r k : axisKernel B e) : LinearMap.GeneralLinearGroup F W) e
      rwa [hre (r k)] at h
    · rw [Units.val_mul, Module.End.mul_apply, ← hr k]
      exact inv_apply_apply_of_GL _ f
  have hlf : ∀ l : ↥(K' ⊓ stabEF hc),
      ((l : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f = f :=
    fun l => ((mem_stabEF hB hc).mp l.2.2).2.2
  let E : ↥(axisKernel B e) × ↥(K' ⊓ stabEF hc) ≃ K' :=
    { toFun := fun p => ⟨(p.1 : LinearMap.GeneralLinearGroup F W) * p.2,
        K'.mul_mem (hRK p.1.2) p.2.2.1⟩
      invFun := fun k => (r k, ⟨_, hmemL k⟩)
      left_inv := fun p => by
        obtain ⟨a, l⟩ := p
        have hra : r ⟨(a : LinearMap.GeneralLinearGroup F W) * l, K'.mul_mem (hRK a.2) l.2.1⟩ =
            a := by
          refine (huniq _ (hy _).1 (hy _).2).unique (hr _) ?_
          change _ = ((a : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W)
            (((l : LinearMap.GeneralLinearGroup F W) : W →ₗ[F] W) f)
          rw [hlf l]
        refine Prod.ext hra (Subtype.ext ?_)
        change ((r ⟨_, _⟩ : axisKernel B e) : LinearMap.GeneralLinearGroup F W)⁻¹ *
          ((a : LinearMap.GeneralLinearGroup F W) * l) = l
        rw [hra, inv_mul_cancel_left]
      right_inv := fun k => Subtype.ext (mul_inv_cancel_left _ _) }
  rw [← Nat.card_prod]
  exact (Nat.card_congr E).symm

end CFSG.LargeExtraspecial.S14.PSLPSU10
