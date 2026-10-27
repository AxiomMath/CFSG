module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qMAModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5C3qMALin
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5CKPull

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5c3qma_fix_of_mem_sup {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    [FiniteDimensional (ZMod 3) V] {Q : QuadraticForm (ZMod 3) V} {t : OGroup Q}
    (D : Om6Par Q t) {g : OGroup Q} (hg : g ∈ D.L ⊔ D.R) {p : V} (hp : p ∈ fixSp t) :
    ((g : OGroup Q) : V ≃ₗ[ZMod 3] V) p = p := by
  rw [← D.map_omega] at hg
  obtain ⟨a, -, rfl⟩ := hg
  exact D.theta_apply_P a hp

theorem sec5c3qma_cent_of_const (hS : Asc82SchurU43) {G : Type} [Group G] [Finite G] {t : G}
    {L S : Subgroup G} {z r : G} {B A K₁ K₂ : Subgroup G}
    (c : Sec5KCtx G t L S z r B A K₁ K₂) :
    ∃ (φ : (Fin 6 → ZMod 2) → G) (ζ : Fin 6 → ZMod 2), Sec5Model58 t L z r A φ ∧ φ ζ = z ∧
      vecWeight ζ = 4 ∧ ∀ w : Fin 6 → ZMod 2, (∀ i j, ζ i = 1 → ζ j = 1 → w i = w j) →
        φ w ∈ centralizer ((K₁ ⊔ K₂ : Subgroup G) : Set G) := by
  obtain ⟨V, _, _, _, Q, hQ, fr, φc, φ, hφ, hm, hact, hmap⟩ := sec5c3qma_frame hS c.toSec5RCtx
  have hL : IsOm6Z2 L := c.toSec5Ctx.toSec5Setting.isOm6Z2
  have hodd : oddCoreIn L = ⊥ := sec5c_oddCoreIn_bot hL c.involution c.centre
  have hinj : Function.Injective φc := by
    have hker : CFSG.oddCore ↥L = ⊥ := by
      have h : (CFSG.oddCore ↥L).map L.subtype = ⊥ := hodd
      exact (Subgroup.map_eq_bot_iff_of_injective (CFSG.oddCore ↥L) L.subtype_injective).mp h
    rw [← MonoidHom.ker_eq_bot_iff, hφ.ker_eq, hker]
  have hsurj : Function.Surjective φc := hφ.surjective
  haveI : Finite (OGroup Q) := sec5c_finite_ogroup
  have hzL : z ∈ L := sec5c_mem_of_isI4PlusIn c.pocket
  obtain ⟨ζ, hζ4, hζz⟩ := hm.z_mem
  have hζL : φ ζ ∈ L := hζz ▸ hzL
  have hev : IsEvenVec ζ := (hm.mem_L ζ).mp hζL
  have hzcast : (⟨φ ζ, hζL⟩ : ↥L) = ⟨z, hzL⟩ := Subtype.ext hζz
  have hφz : sec5cdPhi φc ⟨z, hzL⟩ = fr.signChange (sec5c_supp ζ) := by
    rw [← hzcast]
    exact hmap ζ hζL hev
  obtain ⟨hztt, hzt4⟩ := sec5c_z_model hL hφ c.pocket hzL
  let D : Om6Par Q (sec5cdPhi φc ⟨z, hzL⟩) :=
    Om6Par.mk' hQ hφ.finrank_eq hφ.quadSign_eq hztt hzt4
  refine ⟨φ, ζ, hm, hζz, hζ4, fun w hw => ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hx0 : x ∈ K₁ ⊔ K₂ := hx
  have hx' : x ∈ twoRes (L ⊓ centralizer ({z} : Set G)) := by rwa [c.prod] at hx0
  have hxL : x ∈ L := sec5cd_twoRes_le inf_le_left hx'
  have hD : sec5cdPhi φc ⟨x, hxL⟩ ∈ D.L ⊔ D.R :=
    (sec5cd_mem_twoRes_iff_sup hinj hsurj hzL D ⟨x, hxL⟩).mp hx'
  have hcomm : sec5cdPhi φc ⟨x, hxL⟩ * fr.signChange (sec5c_supp ζ) =
      fr.signChange (sec5c_supp ζ) * sec5cdPhi φc ⟨x, hxL⟩ := by
    rw [← hφz]
    exact ((Subgroup.mem_centralizer_iff.mp (D.le_omega_cent hD).2) _
      (Set.mem_singleton _)).symm
  have hfix : ∀ j ∉ sec5c_supp ζ,
      ((sec5cdPhi φc ⟨x, hxL⟩ : OGroup Q) : V ≃ₗ[ZMod 3] V) (fr.b j) = fr.b j := by
    intro j hj
    refine sec5c3qma_fix_of_mem_sup D hD ?_
    rw [mem_fixSp_iff, hφz, fr.signChange_basis, if_neg hj]
  have hJ : ∀ i ∈ sec5c_supp ζ, ∀ j ∈ sec5c_supp ζ, (i ∈ sec5c_supp w ↔ j ∈ sec5c_supp w) := by
    intro i hi j hj
    have h1 : ζ i = 1 := by
      have := (sec5c_mem_supp ζ i).mp hi
      generalize ζ i = a at this ⊢
      revert a
      decide
    have h2 : ζ j = 1 := by
      have := (sec5c_mem_supp ζ j).mp hj
      generalize ζ j = a at this ⊢
      revert a
      decide
    rw [sec5c_mem_supp, sec5c_mem_supp, hw i j h1 h2]
  have hconj := sec5c3qma_signChange_conj fr hJ hcomm hfix
  have hN : φ w ∈ normalizer (L : Set G) := (hact w).1
  have hxN : φ w * x * (φ w)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hN x).mp hxL
  have h2 := (hact w).2 ⟨x, hxL⟩ ⟨φ w * x * (φ w)⁻¹, hxN⟩ rfl
  rw [simAct_orthToSim] at h2
  have h3 : ((φc ⟨φ w * x * (φ w)⁻¹, hxN⟩ : omegaGroup hQ) : OGroup Q) =
      ((φc ⟨x, hxL⟩ : omegaGroup hQ) : OGroup Q) := h2.trans hconj
  have h4 : (⟨φ w * x * (φ w)⁻¹, hxN⟩ : ↥L) = ⟨x, hxL⟩ := hinj (Subtype.ext h3)
  have h5 : φ w * x * (φ w)⁻¹ = x := congrArg Subtype.val h4
  calc x * φ w = (φ w * x * (φ w)⁻¹) * φ w := by rw [h5]
    _ = φ w * x := by group

end CFSG.OddStandard.SmallF3.Omega
