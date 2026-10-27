module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2TrComp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec2OutDefs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup
open scoped commutatorElement

variable {A P : Type} [Group A] [Group P]

private theorem fj_subgroupComap_ker_le_center {ρ : A →* P} (hker : ρ.ker ≤ center A)
    (X : Subgroup P) : (ρ.subgroupComap X).ker ≤ center ↥(X.comap ρ) := by
  intro p hp
  have hp1 : ρ (p : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hp)
  have hc : (p : A) ∈ center A := hker (MonoidHom.mem_ker.mpr hp1)
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_center_iff.mp hc (g : A))

theorem fj_map_coverDerived {ρ : A →* P} (hρ : Function.Surjective ρ) (hker : ρ.ker ≤ center A)
    {J : Subgroup P} (hJ : CFSG.IsQuasisimple ↥J) : (coverDerived ρ J).map ρ = J := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    exact coverDerived_le J
  · intro q hq
    obtain ⟨-, -, hsurj⟩ := CFSG.LocalCores.central_extension_derived_of_surjective
      (ρ.subgroupComap J) (MonoidHom.subgroupComap_surjective ρ J hρ)
      (fj_subgroupComap_ker_le_center hker J) hJ.1
    obtain ⟨c, hc⟩ := hsurj ⟨q, hq⟩
    exact Subgroup.mem_map.mpr ⟨((c : ↥(J.comap ρ)) : A),
      Subgroup.mem_map.mpr ⟨(c : ↥(J.comap ρ)), c.2, rfl⟩, congrArg Subtype.val hc⟩

theorem fj_isQuasisimple_coverDerived {ρ : A →* P} (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center A) {J : Subgroup P} (hJ : CFSG.IsQuasisimple ↥J) :
    CFSG.IsQuasisimple ↥(coverDerived ρ J) := by
  have h1 := CFSG.LocalCores.quasisimple_central_extension_derived_of_surjective
    (ρ.subgroupComap J) (MonoidHom.subgroupComap_surjective ρ J hρ)
    (fj_subgroupComap_ker_le_center hker J) hJ
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    ((commutator ↥(J.comap ρ)).equivMapOfInjective (J.comap ρ).subtype
      (J.comap ρ).subtype_injective) h1

private theorem fj_commutator_mul_central {a b u v : A} (hu : u ∈ center A) (hv : v ∈ center A) :
    ⁅a * u, b * v⁆ = ⁅a, b⁆ := by
  have hu' : ∀ g : A, g * u = u * g := Subgroup.mem_center_iff.mp hu
  have hv' : ∀ g : A, g * v = v * g := Subgroup.mem_center_iff.mp hv
  have cu : ∀ g : A, u * g * u⁻¹ = g := fun g => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hu' g).symm
  have cv : ∀ g : A, v * g * v⁻¹ = g := fun g => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (hv' g).symm
  rw [commutatorElement_def, commutatorElement_def]
  calc a * u * (b * v) * (a * u)⁻¹ * (b * v)⁻¹
      = (a * (u * (b * v) * u⁻¹) * a⁻¹) * (b * v)⁻¹ := by group
    _ = (a * (b * v) * a⁻¹) * (b * v)⁻¹ := by rw [cu]
    _ = a * b * (v * a⁻¹ * v⁻¹) * b⁻¹ := by group
    _ = a * b * a⁻¹ * b⁻¹ := by rw [cv]

theorem fj_coverDerived_le_fixSub {ρ : A →* P} {σ : MulAut A} {β : MulAut P}
    (hker : ρ.ker ≤ center A) (hσβ : ∀ a, ρ (σ a) = β (ρ a)) {J : Subgroup P}
    (hJ : J ≤ fixSub β) : coverDerived ρ J ≤ fixSub σ := by
  have hcen : ∀ a ∈ J.comap ρ, a⁻¹ * σ a ∈ center A := by
    intro a ha
    apply hker
    rw [MonoidHom.mem_ker, map_mul, map_inv, hσβ a, show β (ρ a) = ρ a from hJ ha,
      inv_mul_cancel]
  unfold coverDerived
  rw [Subgroup.map_le_iff_le_comap, commutator_def, Subgroup.commutator_le]
  intro a _ b _
  rw [Subgroup.mem_comap, mem_fixSub_iff]
  have hab : (((⁅a, b⁆ : ↥(J.comap ρ)) : ↥(J.comap ρ)) : A) = ⁅(a : A), (b : A)⁆ :=
    map_commutatorElement (J.comap ρ).subtype a b
  change σ (((⁅a, b⁆ : ↥(J.comap ρ)) : ↥(J.comap ρ)) : A) =
    (((⁅a, b⁆ : ↥(J.comap ρ)) : ↥(J.comap ρ)) : A)
  rw [hab, map_commutatorElement]
  calc ⁅σ (a : A), σ (b : A)⁆
      = ⁅(a : A) * ((a : A)⁻¹ * σ (a : A)), (b : A) * ((b : A)⁻¹ * σ (b : A))⁆ := by
        rw [mul_inv_cancel_left, mul_inv_cancel_left]
    _ = ⁅(a : A), (b : A)⁆ := fj_commutator_mul_central (hcen a a.2) (hcen b b.2)

theorem fj_isComponentIn_coverDerived {ρ : A →* P} (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ center A) {σ : MulAut A} {β : MulAut P} (hσβ : ∀ a, ρ (σ a) = β (ρ a))
    {J : Subgroup P} (hJ : IsComponentIn J (fixSub β)) :
    IsComponentIn (coverDerived ρ J) (fixSub σ) := by
  have hJfix : J ≤ fixSub β := hJ.1
  have hq := fj_isQuasisimple_coverDerived hρ hker hJ.isQuasisimple
  have hle : coverDerived ρ J ≤ fixSub σ := fj_coverDerived_le_fixSub hker hσβ hJfix
  have hHσ : fixSub σ ≤ (fixSub β).comap ρ := by
    intro c hc
    rw [Subgroup.mem_comap, mem_fixSub_iff, ← hσβ c, mem_fixSub_iff.mp hc]
  have hN : ((J.comap ρ).subgroupOf ((fixSub β).comap ρ)).IsSubnormal := by
    have h1 := hJ.2.2.comap (ρ.subgroupComap (fixSub β))
    convert h1 using 1
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    exact Iff.rfl
  have hsub : ((coverDerived ρ J).subgroupOf ((fixSub β).comap ρ)).IsSubnormal :=
    isSubnormal_subgroupOf_of_normal_le (coverDerived_le J) (Subgroup.comap_mono hJfix)
      (fun k hk h hh => conj_mem_coverDerived J hk hh) hN
  have hcomp : IsComponentIn (coverDerived ρ J) ((fixSub β).comap ρ) :=
    isComponentIn_of_subnormal ((coverDerived_le J).trans (Subgroup.comap_mono hJfix)) hq hsub
  exact hcomp.mono hle hHσ

end CFSG.OddStandard.SmallF3.Omega
