module

public import CFSG.LargeExtraspecial.S14C12SmQ
public import CFSG.LargeExtraspecial.S10FourI

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14.SMK

open Subgroup CFSG.Open
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem not_nonempty_mulEquiv_psl (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    ¬ Nonempty (G ≃* PSL(S.width + 2, ZMod 2)) := by
  rintro ⟨e⟩
  have h2 := factorization_card_of_U6 S hw hU
  have h66 := SmithQ.factorization_card_psl (S.width + 2)
  rw [← Nat.card_congr e.toEquiv, hw] at h66
  omega

theorem not_nonempty_mulEquiv_psu (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    ¬ Nonempty (G ≃* timmesfeldPSU (S.width + 2)) := by
  rintro ⟨e⟩
  have h2 := factorization_card_of_U6 S hw hU
  rw [hw] at e
  have h38 : 2 ^ 38 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv]
    exact SmithQ.two_pow_dvd_card_timmesfeldPSU_twelve
  have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h38
  omega

theorem irreducible [IsSimpleGroup G] (hDW : DW.DW37Statement) (hw : S.width = 10)
    (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : ¬ S.IsReducible := fun hred =>
  not_nonempty_mulEquiv_psl hw hU (hDW G S g (by omega) haQ hne hred)

theorem exists_conj_mem_QG [IsSimpleGroup G] (hAS : AschbacherSmithWideInput)
    (hw : S.width = 10) (hU : Nonempty (Mbar0 S ≃* timmesfeldPSU 6)) :
    ∃ g : G, g * S.z * g⁻¹ ∈ S.QG ∧ g * S.z * g⁻¹ ≠ S.z := by
  by_contra h
  push Not at h
  exact not_nonempty_mulEquiv_psu hw hU (hAS G S (by omega) h)

variable (S) in
@[expose] noncomputable def cMbar (g : G) : Subgroup S.O :=
  S.Mbar ⊓ S10.vecStab S (S.cl (g * S.z * g⁻¹))

theorem mem_cMbar {g : G} {s : S.O} :
    s ∈ cMbar S g ↔ s ∈ S.Mbar ∧
      (s : S.Qt ≃ₗ[ZMod 2] S.Qt) (S.cl (g * S.z * g⁻¹)) = S.cl (g * S.z * g⁻¹) :=
  Iff.rfl

theorem card_Lbar_ge (hw : S.width = 10) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) : 2 ^ 9 ≤ Nat.card (S.Lbar g) := by
  have h := S.card_Lbar_ge haQ hne
  rwa [hw] at h

theorem Lbar_eq_of_cl_eq {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG) (hne : g * S.z * g⁻¹ ≠ S.z)
    (hbQ : h * S.z * h⁻¹ ∈ S.QG) (hcl : S.cl (h * S.z * h⁻¹) = S.cl (g * S.z * g⁻¹)) :
    S.Lbar h = S.Lbar g := by
  rcases (S.cl_eq_cl_iff haQ hbQ).mp hcl.symm with hb | hb
  · exact S.Lbar_eq_of_conj_eq hb
  · exact S.Lbar_eq_of_conj_eq_mul_z haQ hne hb

theorem cMbar_le_normalizer {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) :
    cMbar S g ≤ S.Mbar ⊓ normalizer (S.Lbar g : Set S.O) := by
  rintro s ⟨⟨m, rfl⟩, hs⟩
  refine ⟨⟨m, rfl⟩, ?_⟩
  have hmaQ : ((m : G) * g) * S.z * ((m : G) * g)⁻¹ ∈ S.QG := by
    simpa [mul_assoc] using S.conj_mem_QG m.2 haQ
  have hcl : S.cl (((m : G) * g) * S.z * ((m : G) * g)⁻¹) = S.cl (g * S.z * g⁻¹) := by
    rw [← S.ρ_cl_conj_z m.2 haQ]
    exact hs
  have hL := Lbar_eq_of_cl_eq haQ hne hmaQ hcl
  rw [S.Lbar_mul m.2] at hL
  change S.ρ m ∈ normalizer (S.Lbar g : Set S.O)
  rw [mem_normalizer_iff_map_conj_eq]
  exact hL

theorem cMbar_eq_normalizer_of_noA2 (h2 : 2 ≤ S.width) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) :
    cMbar S g = S.Mbar ⊓ normalizer (S.Lbar g : Set S.O) :=
  le_antisymm (cMbar_le_normalizer haQ hne) fun _ hs =>
    ⟨hs.1, S.fixes_of_mem_normalizer_Lbar h2 haQ hne hno hs.2⟩

theorem Lbar_eq_iff_cl_eq_of_noA2 (h2 : 2 ≤ S.width) {g h : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hno : ¬ S.HasTypeAInL g) (hbQ : h * S.z * h⁻¹ ∈ S.QG)
    (hbne : h * S.z * h⁻¹ ≠ S.z) :
    S.Lbar h = S.Lbar g ↔ S.cl (h * S.z * h⁻¹) = S.cl (g * S.z * g⁻¹) := by
  refine ⟨fun hL => ?_, Lbar_eq_of_cl_eq haQ hne hbQ⟩
  have hmem : S.cl (h * S.z * h⁻¹) ∈ S.fixLbar g := by
    have h1 := S.mem_fixLbar.mp (S.cl_mem_fixLbar_self hbQ)
    rw [hL] at h1
    exact S.mem_fixLbar.mpr h1
  rcases (S.lemma_3_9 h2 haQ hne).resolve_right hno _ hmem (S.q_cl_conj_z hbQ) with h0 | h1
  · exact absurd h0 (S.cl_conj_z_ne_zero hbQ hbne)
  · exact h1

end CFSG.LargeExtraspecial.S14.SMK
