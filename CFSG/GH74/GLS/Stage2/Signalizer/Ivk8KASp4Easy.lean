module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8KASp4Out

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ComponentClassification CFSG.ComponentClassification.CatFactsSp4
open CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

theorem ka_easy_scalar_sq {F : Type} [Field F] {z : StatedSp 2 F} (hz : z ∈ spScalars 2 F) :
    z * z = 1 := by
  apply sp_ext
  rcases (mem_spScalars_iff z).mp hz with h | h <;> simp [h]

theorem ka_odd_mem_map_fixOf {F : Type} [Field F] [Finite F] (θ : MulAut (StatedSp 2 F))
    (α : MulAut (StatedProj (StatedSp 2 F)))
    (hθα : ∀ g, α (proj 2 F g) = proj 2 F (θ g)) {c : StatedProj (StatedSp 2 F)}
    (hc : α c = c) (hodd : Odd (orderOf c)) : c ∈ (fixOf θ).map (proj 2 F) := by
  obtain ⟨B, rfl⟩ := proj_surjective (r := 2) (K := F) c
  obtain ⟨z, hzdef⟩ : ∃ z : StatedSp 2 F, z = θ B * B⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ spScalars 2 F := by
    rw [← ker_proj, MonoidHom.mem_ker, hzdef, map_mul, map_inv, ← hθα, hc, mul_inv_cancel]
  have hBz : B * z = z * B := Subgroup.mem_center_iff.mp (mem_center_of_mem_spScalars hz) B
  have hθB : θ B = z * B := by rw [hzdef]; group
  have hsq : θ (B * B) = B * B := by
    rw [map_mul, hθB]
    calc z * B * (z * B) = z * (B * z) * B := by group
      _ = z * (z * B) * B := by rw [hBz]
      _ = (z * z) * B * B := by group
      _ = B * B := by rw [ka_easy_scalar_sq hz, one_mul]
  have hmem : proj 2 F (B * B) ∈ (fixOf θ).map (proj 2 F) :=
    ⟨B * B, mem_fixOf.mpr hsq, rfl⟩
  rw [map_mul] at hmem
  exact ka_odd_mem_of_sq_mem hmem hodd

theorem kaAll_sp4_of_fix {F : Type} [Field F] [Finite F] (hodd : ringChar F ≠ 2)
    (θ : MulAut (StatedSp 2 F)) (α : MulAut (StatedProj (StatedSp 2 F)))
    (hθα : ∀ g, α (proj 2 F g) = proj 2 F (θ g))
    (hperf : ⁅fixOf θ, fixOf θ⁆ = fixOf θ)
    (hRp : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup (StatedProj (StatedSp 2 F)), IsPGroup p ↥X →
      X ≤ (fixOf θ).map (proj 2 F) →
      (∀ r ∈ (fixOf θ).map (proj 2 F), r ∈ normalizer (X : Set (StatedProj (StatedSp 2 F)))) →
        X = ⊥) :
    KAAll α := by
  have hR : ⁅(fixOf θ).map (proj 2 F), (fixOf θ).map (proj 2 F)⁆ =
      (fixOf θ).map (proj 2 F) := by
    rw [← Subgroup.map_commutator, hperf]
  have hRC : (fixOf θ).map (proj 2 F) ≤ fixSub α := fun y hy =>
    mem_fixSub.mpr (mem_fixOf.mp (map_fixOf_le θ hθα hy))
  exact ka_all_of_oddcore (ka_conj_inj_psp4 hodd) _ hRC (ka_gen_odd_of_perfect _ hR)
    (fun _ hc ho => ka_odd_mem_map_fixOf θ α hθα (mem_fixSub.mp hc) ho) hRp
    (ka_outCyc_psp4 hodd) (ka_outCentral_psp4 hodd α)

theorem ka_hRp_of_quasisimple {F : Type} [Field F] [Finite F] (_hodd : ringChar F ≠ 2)
    (θ : MulAut (StatedSp 2 F)) (hQ : CFSG.IsQuasisimple (fixOf θ))
    (hcent : ∀ z : StatedSp 2 F, (∀ g ∈ fixOf θ, g * z = z * g) → z ∈ spScalars 2 F) :
    ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ X : Subgroup (StatedProj (StatedSp 2 F)), IsPGroup p ↥X →
      X ≤ (fixOf θ).map (proj 2 F) →
      (∀ r ∈ (fixOf θ).map (proj 2 F), r ∈ normalizer (X : Set (StatedProj (StatedSp 2 F)))) →
        X = ⊥ := by
  intro p hp _ X hXp hXR hXn
  let φ : ↥(fixOf θ) →* StatedProj (StatedSp 2 F) := (proj 2 F).comp (fixOf θ).subtype
  let N : Subgroup ↥(fixOf θ) := X.comap φ
  have hNn : N.Normal := ⟨fun n hn g => by
    show φ (g * n * g⁻¹) ∈ X
    rw [map_mul, map_mul, map_inv]
    have hg : φ g ∈ (fixOf θ).map (proj 2 F) := ⟨g, g.2, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (hXn _ hg) (φ n)).1 hn⟩
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hQ N with hN | hN
  · rw [eq_bot_iff]
    intro x hx
    obtain ⟨e, he, rfl⟩ := hXR hx
    have hcen : (⟨e, he⟩ : ↥(fixOf θ)) ∈ center ↥(fixOf θ) := hN hx
    have hes : e ∈ spScalars 2 F := hcent e fun g hg =>
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨g, hg⟩)
    rw [Subgroup.mem_bot, ← MonoidHom.mem_ker, ker_proj]
    exact hes
  · have hRX : (fixOf θ).map (proj 2 F) ≤ X := by
      rintro _ ⟨e, he, rfl⟩
      have : (⟨e, he⟩ : ↥(fixOf θ)) ∈ N := hN ▸ Subgroup.mem_top _
      exact this
    have hXeq : X = (fixOf θ).map (proj 2 F) := le_antisymm hXR hRX
    have : Group.IsPerfect ↥(fixOf θ) := hQ.1
    have : Fact p.Prime := ⟨hp⟩
    subst hXeq
    have : Group.IsPerfect ↥((fixOf θ).map (proj 2 F)) := Group.IsPerfect.map _
    have hnil : Group.IsNilpotent ↥((fixOf θ).map (proj 2 F)) := hXp.isNilpotent
    by_contra hne
    have : Nontrivial ↥((fixOf θ).map (proj 2 F)) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    exact Group.IsPerfect.not_isNilpotent ↥((fixOf θ).map (proj 2 F)) hnil

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
