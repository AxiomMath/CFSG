module

public import CFSG.LargeExtraspecial.S3cFour
public import CFSG.LargeExtraspecial.S3cRad

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent AddSubgroupClass.instZModModule

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.Literature.FSmith
  CFSG.RankThree.OrthogonalInvolutions OrthoF2

universe u

namespace Setting

variable {G : Type u} [Group G] [Finite G] (S : Setting G)

theorem mem_fixLbar_iff_LbarLin {g : G} (x : S.Qt) :
    x ∈ S.fixLbar g ↔ ∀ t ∈ S.LbarLin g, t x = x := by
  rw [S.mem_fixLbar]
  constructor
  · intro h t ht
    obtain ⟨s, hs, rfl⟩ := S.mem_LbarLin_iff.mp ht
    exact h s hs
  · intro h s hs
    exact h _ (S.coe_mem_LbarLin hs)

theorem card_fixLbar_eq (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) :
    Nat.card (S.fixLbar g) = 2 * Nat.card {s : S.O // s ∈ S.Lbar g ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))} := by
  have C := S.transvectionConfig hTI hn haQ hne hno hirr
  obtain ⟨v, hv⟩ := S.exists_polar_cl_eq_one haQ hne
  have hW := S.finrank_clSub_of_irreducible hTI hn haQ hne hno hirr
  have hdim := C.finrank_fix_eq S.q_nondegenerate hv (by omega) (S.fixLbar g)
    S.mem_fixLbar_iff_LbarLin
  have hO : ∀ φ : C.K, C.sOf φ ∈ S.O := fun φ => C.mem_orthogonalGroup (C.sOf_mem φ)
  have hL : ∀ φ : C.K, (⟨C.sOf φ, hO φ⟩ : S.O) ∈ S.Lbar g := fun φ => by
    obtain ⟨s, hs, hse⟩ := S.mem_LbarLin_iff.mp (C.sOf_mem φ)
    rwa [show (⟨C.sOf φ, hO φ⟩ : S.O) = s from Subtype.ext hse.symm]
  let f : C.rad v → {s : S.O // s ∈ S.Lbar g ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))} := fun φ =>
    ⟨⟨C.sOf φ, hO φ⟩, hL φ,
      C.mem_pointRadical_of_theta_eq_zero S.q_nondegenerate hv (C.mem_rad.mp φ.2)⟩
  have hf : Function.Bijective f := by
    constructor
    · intro φ ψ h
      have h1 : C.sOf φ = C.sOf ψ := congrArg (fun x => ((x.1 : S.O) : S.Qt ≃ₗ[ZMod 2] S.Qt)) h
      exact Subtype.ext (C.sOf_injective h1)
    · rintro ⟨s, hs, hsN⟩
      obtain ⟨φ, hφ⟩ := C.exists_sOf_eq (S.coe_mem_LbarLin hs)
      have hφr : φ ∈ C.rad v :=
        C.mem_rad.mpr (C.theta_eq_zero_of_mem_pointRadical v (hφ ▸ hsN))
      exact ⟨⟨φ, hφr⟩, Subtype.ext (Subtype.ext hφ)⟩
  rw [← Nat.card_eq_of_bijective f hf, Module.natCard_eq_pow_finrank (K := ZMod 2),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := C.rad v), Nat.card_zmod, hdim, pow_succ]
  ring

theorem exists_mem_pointRadical_of_width_eq_five (hTI : WeaklyClosedTITransitive.{u})
    (hn : S.width = 5) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) :
    ∃ s ∈ S.Lbar g, s ≠ 1 ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) := by
  have C := S.transvectionConfig hTI (by omega) haQ hne hno hirr
  obtain ⟨v, hv⟩ := S.exists_polar_cl_eq_one haQ hne
  have hW := S.finrank_clSub_of_irreducible hTI (by omega) haQ hne hno hirr
  have hK : finrank (ZMod 2) C.K = 4 := by
    have := C.finrank_K_add_one
    omega
  obtain ⟨φ, hφ0, hφ⟩ := (C.isAltTrilin_theta v).exists_radical_of_finrank_eq_four hK
  have hN := C.mem_pointRadical_of_theta_eq_zero S.q_nondegenerate hv hφ
  obtain ⟨s, hs, hse⟩ := S.mem_LbarLin_iff.mp (C.sOf_mem φ)
  refine ⟨s, hs, fun h1 => hφ0 ((C.sOf_eq_one_iff φ).mp ?_), hse ▸ hN⟩
  rw [← hse, h1]
  rfl

theorem fixLbar_ne_span_of_width_eq_five (hTI : WeaklyClosedTITransitive.{u})
    (hn : S.width = 5) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hno : ¬ S.HasTypeAInL g) (hirr : ¬ S.IsReducible) :
    S.fixLbar g ≠ (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) := by
  intro h
  have hcard := S.card_fixLbar_eq hTI (by omega) haQ hne hno hirr
  obtain ⟨s, hs, hs1, hsN⟩ := S.exists_mem_pointRadical_of_width_eq_five hTI hn haQ hne hno hirr
  rw [h, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_span_singleton (S.cl_conj_z_ne_zero haQ hne), pow_one] at hcard
  have h1 : Nat.card {s : S.O // s ∈ S.Lbar g ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))} = 1 := by omega
  have h2 : (⟨s, hs, hsN⟩ : {s : S.O // s ∈ S.Lbar g ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))}) =
      ⟨1, one_mem _, one_mem _⟩ := by
    have : Subsingleton {s : S.O // s ∈ S.Lbar g ∧
        (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))} :=
      (Nat.card_eq_one_iff_unique.mp h1).1
    exact Subsingleton.elim _ _
  exact hs1 (congrArg Subtype.val h2)

theorem fixLbar_eq_span_iff (hTI : WeaklyClosedTITransitive.{u}) (hn : 3 ≤ S.width) {g : G}
    (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g)
    (hirr : ¬ S.IsReducible) :
    S.fixLbar g = (ZMod 2) ∙ S.cl (g * S.z * g⁻¹) ↔
      ∀ s ∈ S.Lbar g,
        (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹)) → s = 1 := by
  refine ⟨fun h s hs hsN => ?_, S.fixLbar_eq_span_of_pointRadical (by omega) haQ hne⟩
  have hcard := S.card_fixLbar_eq hTI hn haQ hne hno hirr
  rw [h, Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod,
    finrank_span_singleton (S.cl_conj_z_ne_zero haQ hne), pow_one] at hcard
  have h1 : Nat.card {s : S.O // s ∈ S.Lbar g ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))} = 1 := by omega
  have : Subsingleton {s : S.O // s ∈ S.Lbar g ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))} :=
    (Nat.card_eq_one_iff_unique.mp h1).1
  have h2 : (⟨s, hs, hsN⟩ : {s : S.O // s ∈ S.Lbar g ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) ∈ pointRadical S.q (S.cl (g * S.z * g⁻¹))}) =
      ⟨1, one_mem _, one_mem _⟩ := Subsingleton.elim _ _
  exact congrArg Subtype.val h2

end Setting

end CFSG.LargeExtraspecial
