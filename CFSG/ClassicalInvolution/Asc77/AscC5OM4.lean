module

public import CFSG.ClassicalInvolution.Asc77.AscC5OM2

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O.M

open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.ClassicalInvolution.ModelFacts.Orth15.OuterSp4 (exists_conjAut_fieldAut_sp4)
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_apply mat_injective)
open scoped Matrix

variable {F : Type} [Field F] {Y : Type} [Group Y] {Φ : Set (Subgroup Y)} {A A' : Subgroup Y}
  {z' : Y}

theorem map_conj_L0_eq (h2 : (2 : F) ≠ 0) {h : StatedSp 2 F}
    (hc : h * longInv F 2 0 * h⁻¹ = longInv F 2 1) :
    (longRootSp2 F 2 0).map (MulAut.conj h).toMonoidHom = longRootSp2 F 2 1 := by
  have hL := (isLongRootSp2_standard (K := F) (n := 2) 0).conj h
  rw [hc] at hL
  rw [hL.eq_longRootGroup h2, (isLongRootSp2_standard (K := F) (n := 2) 1).eq_longRootGroup h2]

namespace Frame

variable (fr : Frame F Y Φ A A' z')
include fr

theorem ψ_negOne : fr.ψ (negOne F) = 1 := by
  rw [← MonoidHom.mem_ker, fr.ker]
  exact negOne_mem_spScalars

theorem lift_eq_iff {a b : StatedSp 2 F} : fr.ψ a = fr.ψ b ↔ a = b ∨ a = b * negOne F := by
  constructor
  · intro h
    have hk : b⁻¹ * a ∈ fr.ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
    rw [fr.ker, mem_spScalars_iff] at hk
    rcases hk with hk | hk
    · left
      calc a = b * (b⁻¹ * a) := by group
        _ = b := by rw [hk, mul_one]
    · right
      calc a = b * (b⁻¹ * a) := by group
        _ = b * negOne F := by rw [hk]
  · rintro (rfl | rfl)
    · rfl
    · rw [map_mul, ψ_negOne, mul_one]

theorem ψ_longInv_one : fr.ψ (longInv F 2 1) = z' := by
  have e1 : longInv F 2 1 = negOne F * longInv F 2 0 := longInv_rev_eq 0
  rw [e1, map_mul, ψ_negOne, one_mul, ← fr.hz]

@[expose] noncomputable def e : StatedProj (StatedSp 2 F) ≃* Y :=
  C25W.Sp.projEquiv fr.ψ fr.surj fr.ker

theorem e_proj (x : StatedSp 2 F) : fr.e (proj 2 F x) = fr.ψ x :=
  C25W.Sp.projEquiv_proj fr.ψ fr.surj fr.ker x

theorem exists_lift_aut [Finite F] (h2 : (2 : F) ≠ 0) (β : Y ≃* Y) :
    ∃ (M : gsp 2 F) (σ : F ≃+* F),
      ∀ x, β (fr.ψ x) = fr.ψ (conjSp 2 F M (fieldSp 2 F σ x)) := by
  let β' : MulAut (StatedProj (StatedSp 2 F)) := fr.e.trans (β.trans fr.e.symm)
  obtain ⟨M, σ, hβ'⟩ := exists_conjAut_fieldAut_sp4 h2 β'
  refine ⟨M, σ, fun x => ?_⟩
  have h1 : β' (proj 2 F x) = proj 2 F (conjSp 2 F M (fieldSp 2 F σ x)) := by
    rw [hβ', MulAut.mul_apply, fieldAut_proj, conjAut_proj]
  have h3 := congrArg fr.e h1
  have h4 : fr.e (β' (proj 2 F x)) = β (fr.e (proj 2 F x)) := by
    simp [β']
  rw [h4, e_proj, e_proj] at h3
  exact h3

theorem centerless [Finite F] (h4 : 4 ≤ Nat.card F) {y : Y} (hy : ∀ x : Y, y * x = x * y) :
    y = 1 := by
  obtain ⟨h, rfl⟩ := fr.surj y
  have hperf : Group.IsPerfect (StatedSp 2 F) :=
    (CFSG.LieType.Universal.Symplectic.isQuasisimple (n := 2) (F := F) (by norm_num)
      (Or.inl (Or.inr h4))).1
  have : Group.IsPerfect (MonoidHom.id (StatedSp 2 F)).range := Group.IsPerfect.range _
  have key := CFSG.ClassicalInvolution.ModelFacts.Orth15.ChainU.eq_of_central_ratio
    (MonoidHom.id (StatedSp 2 F)).range (MulAut.conj h).toMonoidHom (fun r _ => by
      rw [CFSG.LieType.Universal.Symplectic.center_eq]
      change h * r * h⁻¹ * r⁻¹ ∈ spScalars 2 F
      rw [← fr.ker, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hy (fr.ψ r)]
      group)
  have hc : h ∈ Subgroup.center (StatedSp 2 F) := by
    rw [Subgroup.mem_center_iff]
    intro r
    have e1 : h * r * h⁻¹ = r := key r ⟨r, rfl⟩
    calc r * h = h * r * h⁻¹ * h := by rw [e1]
      _ = h * r := by group
  rw [CFSG.LieType.Universal.Symplectic.center_eq] at hc
  change h ∈ spScalars 2 F at hc
  rw [← fr.ker] at hc
  exact hc

theorem conjSub_map_ψ (h : StatedSp 2 F) (H : Subgroup (StatedSp 2 F)) :
    conjSub (fr.ψ h) (H.map fr.ψ) = (H.map (MulAut.conj h).toMonoidHom).map fr.ψ := by
  rw [conjSub, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext x
  simp

theorem conj_longInv_cases {h : StatedSp 2 F} (hz : fr.ψ h * z' * (fr.ψ h)⁻¹ = z') :
    h * longInv F 2 0 * h⁻¹ = longInv F 2 0 ∨ h * longInv F 2 0 * h⁻¹ = longInv F 2 1 := by
  have e1 : longInv F 2 1 = negOne F * longInv F 2 0 := longInv_rev_eq 0
  rw [e1, negOne_comm, ← fr.lift_eq_iff, map_mul, map_mul, map_inv, ← fr.hz, hz]

theorem twinOfInner (h2 : (2 : F) ≠ 0) (hne : A ≠ A') (hzA : IsUniqueInvolution A z') {y : Y}
    (hy : conjSub y A = A) : ∃ g ∈ A, ∀ x ∈ A, y * x * y⁻¹ = g * x * g⁻¹ := by
  obtain ⟨h, rfl⟩ := fr.surj y
  have hz1 : fr.ψ h * z' * (fr.ψ h)⁻¹ = z' := by
    have := hzA.conj (fr.ψ h)
    rw [hy] at this
    exact (hzA.eq this).symm
  rcases fr.conj_longInv_cases hz1 with hc | hc
  · have hcomm : h * longInv F 2 0 = longInv F 2 0 * h := by
      calc h * longInv F 2 0 = h * longInv F 2 0 * h⁻¹ * h := by group
        _ = longInv F 2 0 * h := by rw [hc]
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_commute_longInv h2 0 hcomm
    rw [complGroup_longInv_two h2] at hb
    have haA : fr.ψ a ∈ (longRootSp2 F 2 0).map fr.ψ := Subgroup.mem_map_of_mem _ ha
    rw [← fr.hA] at haA
    refine ⟨fr.ψ a, haA, ?_⟩
    intro x hx
    have hx' : x ∈ (longRootSp2 F 2 0).map fr.ψ := fr.hA ▸ hx
    obtain ⟨r, hr, rfl⟩ := hx'
    have hbr : b * r = r * b := (commute_L 0 hr hb).symm
    rw [← map_inv, ← map_mul, ← map_mul, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    calc a * b * r * (a * b)⁻¹ = a * (b * r) * b⁻¹ * a⁻¹ := by group
      _ = a * r * a⁻¹ := by rw [hbr]; group
  · exfalso
    apply hne
    calc A = conjSub (fr.ψ h) A := hy.symm
      _ = conjSub (fr.ψ h) ((longRootSp2 F 2 0).map fr.ψ) := congrArg _ fr.hA
      _ = ((longRootSp2 F 2 0).map (MulAut.conj h).toMonoidHom).map fr.ψ :=
          fr.conjSub_map_ψ h _
      _ = (longRootSp2 F 2 1).map fr.ψ := by rw [map_conj_L0_eq h2 hc]
      _ = A' := fr.hA'.symm

theorem invFixFour (h2 : (2 : F) ≠ 0) {y : Y} (hy2 : y * y = 1) :
    ∃ J ∈ Φ, ∃ x ∈ J, x * x * x * x = 1 ∧ x * x ≠ 1 ∧ y * x = x * y := by
  obtain ⟨h, rfl⟩ := fr.surj y
  have hh : h * h ∈ spScalars 2 F := by
    rw [← fr.ker, MonoidHom.mem_ker, map_mul, hy2]
  obtain ⟨c', hc'1, hc⟩ : ∃ c' : F, c' * c' = 1 ∧ mat 2 F h * mat 2 F h = c' • 1 := by
    rcases mem_spScalars_iff.mp hh with h1 | h1
    · exact ⟨1, one_mul 1, by rw [← map_mul, h1, map_one, one_smul]⟩
    · exact ⟨-1, by ring, by rw [← map_mul, h1, mat_negOne, neg_one_smul]⟩
  have hmap : ∀ M : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F, M.map (RingEquiv.refl F) = M := by
    intro M
    ext
    simp
  obtain ⟨u, w, s, huw, hs, hs4, hsc, hcomm⟩ :=
    C25W.Sp.exists_stable_rotation (m := 0) (RingEquiv.refl F) (mat 2 F h) (fun _ => rfl) h2
      (mat_transpose_mul_gram_mul h) c' hc'1 (by rw [hmap]; exact hc)
  rw [hmap] at hcomm
  refine ⟨(planeGroup (Submodule.span F {u, w})).map fr.ψ, fr.mem' _ ⟨u, w, huw, rfl⟩,
    fr.ψ s, Subgroup.mem_map_of_mem _ hs, ?_, ?_, ?_⟩
  · rw [← map_mul, ← map_mul, ← map_mul, show s * s * s * s = s * s * (s * s) by group, hs4,
      map_one]
  · intro h1
    rw [← map_mul, ← MonoidHom.mem_ker, fr.ker] at h1
    exact hsc (C25W.Sp.scalar_of_mem_spScalars h1)
  · rw [← map_mul, ← map_mul]
    congr 1
    exact mat_injective (by rw [map_mul, map_mul, hcomm])

end Frame

end CFSG.ClassicalInvolution.Asc77.C5O.M
