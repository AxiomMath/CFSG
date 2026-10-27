module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesNSSection
public import CFSG.LargeExtraspecial.S45QLin

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024

open Module Subgroup

section Card

theorem six_dvd_card_GL (m : ℕ) (h3 : 3 ≤ m) : 6 ∣ Nat.card (GL (Fin m) (ZMod 2)) := by
  rw [Matrix.card_GL_field, ZMod.card]
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 3 := ⟨m - 3, by omega⟩
  have h6 : 6 ∣ 2 ^ (k + 3) - 2 ^ (k + 1) := by
    refine ⟨2 ^ k, ?_⟩
    have : 2 ^ (k + 3) = 8 * 2 ^ k := by ring
    have h2 : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    omega
  exact h6.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ (⟨k + 1, by omega⟩ : Fin (k + 3))))

variable (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem six_dvd_card (h3 : 3 ≤ finrank (ZMod 2) V) : 6 ∣ Nat.card (V ≃ₗ[ZMod 2] V) := by
  classical
  haveI : FiniteDimensional (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  let b := Module.finBasis (ZMod 2) V
  let e : Matrix.GeneralLinearGroup (Fin (finrank (ZMod 2) V)) (ZMod 2) ≃*
      (V ≃ₗ[ZMod 2] V) :=
    (Matrix.GeneralLinearGroup.toLin' b).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) V)
  rw [← Nat.card_congr e.toEquiv]
  exact six_dvd_card_GL _ h3

theorem isSimpleGroup_linearEquiv (h3 : 3 ≤ finrank (ZMod 2) V) :
    IsSimpleGroup (V ≃ₗ[ZMod 2] V) := by
  haveI : FiniteDimensional (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  haveI := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_top_of_three_le (V := V) h3
  exact (Subgroup.topEquiv (G := V ≃ₗ[ZMod 2] V)).symm.isSimpleGroup

theorem exists_noncomm (h3 : 3 ≤ finrank (ZMod 2) V) :
    ∃ a b : V ≃ₗ[ZMod 2] V, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  haveI := isSimpleGroup_linearEquiv V h3
  letI : CommGroup (V ≃ₗ[ZMod 2] V) :=
    { (inferInstance : Group (V ≃ₗ[ZMod 2] V)) with mul_comm := hcon }
  have hprime := IsSimpleGroup.prime_card (α := V ≃ₗ[ZMod 2] V)
  have h6 := six_dvd_card V h3
  have h2 := hprime.eq_one_or_self_of_dvd 2 ((by norm_num : 2 ∣ 6).trans h6)
  have h3' := hprime.eq_one_or_self_of_dvd 3 ((by norm_num : 3 ∣ 6).trans h6)
  omega

theorem three_dvd_card (h3 : 3 ≤ finrank (ZMod 2) V) : 3 ∣ Nat.card (V ≃ₗ[ZMod 2] V) :=
  (by norm_num : 3 ∣ 6).trans (six_dvd_card V h3)

end Card

section Affine

variable (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem linearHom_surjective :
    Function.Surjective (AffineEquiv.linearHom (k := ZMod 2) (P₁ := V)) := fun L =>
  ⟨L.toAffineEquiv, rfl⟩

theorem mem_ker_linearHom_iff (f : V ≃ᵃ[ZMod 2] V) :
    f ∈ (AffineEquiv.linearHom (k := ZMod 2) (P₁ := V)).ker ↔
      ∃ w : V, f = AffineEquiv.constVAdd (ZMod 2) V w := by
  constructor
  · intro hf
    have hl : f.linear = LinearEquiv.refl (ZMod 2) V := hf
    refine ⟨f 0, AffineEquiv.ext fun x => ?_⟩
    have h := f.map_vadd 0 x
    simp only [AffineEquiv.constVAdd_apply, hl, LinearEquiv.refl_apply, vadd_eq_add,
      add_zero] at h ⊢
    rw [h, add_comm]
  · rintro ⟨w, rfl⟩
    exact LinearEquiv.ext fun _ => rfl

theorem conj_constVAdd (f : V ≃ᵃ[ZMod 2] V) (w : V) :
    f * AffineEquiv.constVAdd (ZMod 2) V w * f⁻¹ =
      AffineEquiv.constVAdd (ZMod 2) V (f.linear w) := by
  refine AffineEquiv.ext fun x => ?_
  have h := f.map_vadd (f.symm x) w
  simp only [AffineEquiv.coe_mul, Function.comp_apply, AffineEquiv.constVAdd_apply,
    AffineEquiv.inv_def, vadd_eq_add] at h ⊢
  rw [h, AffineEquiv.apply_symm_apply]

theorem aff_section (h3 : 3 ≤ finrank (ZMod 2) V) :
    S622IsSimpleSection (⊤ : Subgroup (V ≃ᵃ[ZMod 2] V))
      (AffineEquiv.linearHom (k := ZMod 2) (P₁ := V)).ker := by
  haveI : FiniteDimensional (ZMod 2) V := Module.finite_iff_finite.mpr inferInstance
  haveI := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_top_of_three_le (V := V) h3
  have hn : ∃ a b : ↥(⊤ : Subgroup (V ≃ₗ[ZMod 2] V)), a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := exists_noncomm V h3
    exact ⟨⟨a, trivial⟩, ⟨b, trivial⟩, fun h => hab (congrArg Subtype.val h)⟩
  have := L6LeavesNS.s622IsSimpleSection_comap
    (AffineEquiv.linearHom (k := ZMod 2) (P₁ := V)) (linearHom_surjective V) inferInstance hn
  rwa [Subgroup.comap_top] at this

theorem three_dvd_relIndex (h3 : 3 ≤ finrank (ZMod 2) V) :
    3 ∣ (AffineEquiv.linearHom (k := ZMod 2) (P₁ := V)).ker.relIndex
      (⊤ : Subgroup (V ≃ᵃ[ZMod 2] V)) := by
  rw [Subgroup.relIndex_top_right, Subgroup.index_ker]
  have hr : (AffineEquiv.linearHom (k := ZMod 2) (P₁ := V)).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (linearHom_surjective V)
  rw [hr, Subgroup.card_top]
  exact three_dvd_card V h3

def permHom : (V ≃ᵃ[ZMod 2] V) →* Equiv.Perm V where
  toFun f := f.toEquiv
  map_one' := rfl
  map_mul' _ _ := rfl

theorem permHom_injective : Function.Injective (permHom V) := fun f g h =>
  AffineEquiv.ext fun x => congrArg (fun e : Equiv.Perm V => e x) h

noncomputable def affToPerm {Ω : Type} (ι : V → Ω) (hι : Function.Injective ι) :
    (V ≃ᵃ[ZMod 2] V) →* Equiv.Perm Ω := by
  classical
  exact (Equiv.Perm.extendDomainHom (p := fun x => x ∈ Set.range ι)
    (Equiv.ofInjective ι hι)).comp (permHom V)

variable {V} {Ω : Type} {ι : V → Ω} (hι : Function.Injective ι)

theorem affToPerm_injective : Function.Injective (affToPerm V ι hι) := by
  classical
  unfold affToPerm
  exact (Equiv.Perm.extendDomainHom_injective _).comp (permHom_injective V)

theorem affToPerm_apply_ι (f : V ≃ᵃ[ZMod 2] V) (v : V) :
    affToPerm V ι hι f (ι v) = ι (f v) := by
  classical
  unfold affToPerm
  exact Equiv.Perm.extendDomain_apply_image (f.toEquiv) (Equiv.ofInjective ι hι) v

theorem affToPerm_apply_out (f : V ≃ᵃ[ZMod 2] V) {x : Ω} (hx : ∀ v, ι v ≠ x) :
    affToPerm V ι hι f x = x := by
  classical
  unfold affToPerm
  have hx' : ¬ (fun x => x ∈ Set.range ι) x := fun ⟨v, hv⟩ => hx v hv
  exact Equiv.Perm.extendDomain_apply_not_subtype (f.toEquiv) (Equiv.ofInjective ι hι) hx'

end Affine

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KG2024
