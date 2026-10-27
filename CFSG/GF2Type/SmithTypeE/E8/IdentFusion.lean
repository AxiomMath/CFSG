module

public import CFSG.GF2Type.SmithTypeE.E8.Defs
public import CFSG.GF2Type.SmithTypeE.L6Ident.Fusion

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E8

open Subgroup CFSG.Blueprint CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.GF2Type.SmithTypeE.L6Ident (not_mem_conj_QG_of_orderOf_three commutator_eq_one_or_z
  conj_inv_mem_M_of_commute)

variable {G : Type} [Group G]

theorem mem_cent2 {t u x : G} : x ∈ cent2 t u ↔ Commute x t ∧ Commute x u := by
  rw [mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  exact ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.1, h.2⟩⟩

theorem z_mem_cent2 (S : Setting G) {t u : G} (htM : t ∈ S.M) (huM : u ∈ S.M) :
    S.z ∈ cent2 t u :=
  mem_cent2.mpr ⟨(S.mem_M_iff.mp htM).symm, (S.mem_M_iff.mp huM).symm⟩

theorem exists_not_commute_of_E23a (hE : E8.SmithE8E23a) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {t u : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htQ : t ∉ S.QG) (huQ : u ∉ S.QG) (htu : orderOf (t * u) = 3) {c : G} (hcQ : c ∈ S.QG)
    (hct : Commute c t) (hcu : Commute c u) (hc1 : c ≠ 1) (hcz : c ≠ S.z) :
    ∃ q ∈ S.QG, Commute q t ∧ Commute q u ∧ ¬ Commute q c := by
  obtain ⟨hext, -⟩ := hE G S hw hU t u ht hu htM huM htQ huQ htu
  have hmem : ∀ {x : G}, x ∈ S.QG ⊓ cent2 t u ↔ x ∈ S.QG ∧ Commute x t ∧ Commute x u :=
    fun {x} => by rw [mem_inf, mem_cent2]
  by_contra hall
  push Not at hall
  set E := S.QG ⊓ cent2 t u
  have hcE : c ∈ E := hmem.mpr ⟨hcQ, hct, hcu⟩
  have hzE : S.z ∈ E := hmem.mpr ⟨S.z_mem_QG, (S.z_comm htM).symm, (S.z_comm huM).symm⟩
  have hcen : ∀ x : E, (∀ y : E, y * x = x * y) → x ∈ center E := fun x hx =>
    Subgroup.mem_center_iff.mpr fun y => hx y
  have hc' : (⟨c, hcE⟩ : E) ∈ center E := hcen _ fun y => by
    obtain ⟨hyQ, hyt, hyu⟩ := hmem.mp y.2
    exact Subtype.ext (hall y hyQ hyt hyu)
  have hz' : (⟨S.z, hzE⟩ : E) ∈ center E := hcen _ fun y => by
    exact Subtype.ext (S.z_comm (S.QG_le_M (hmem.mp y.2).1))
  obtain ⟨x, y, hxy, hxyu⟩ := Nat.card_eq_two_iff.mp hext.2.2.2
  have hin : ∀ w : center E, w = x ∨ w = y := fun w => by
    have : w ∈ ({x, y} : Set (center E)) := hxyu ▸ Set.mem_univ w
    simpa using this
  have h1 : (1 : center E) ≠ ⟨⟨S.z, hzE⟩, hz'⟩ := fun h => S.z_ne_one
    (congrArg (fun w : center E => ((w : E) : G)) h).symm
  have h2 : (1 : center E) ≠ ⟨⟨c, hcE⟩, hc'⟩ := fun h => hc1
    (congrArg (fun w : center E => ((w : E) : G)) h).symm
  have h3 : (⟨⟨S.z, hzE⟩, hz'⟩ : center E) ≠ ⟨⟨c, hcE⟩, hc'⟩ := fun h => hcz
    (congrArg (fun w : center E => ((w : E) : G)) h).symm
  rcases hin 1 with ha | ha <;> rcases hin ⟨⟨S.z, hzE⟩, hz'⟩ with hb | hb <;>
    rcases hin ⟨⟨c, hcE⟩, hc'⟩ with hc | hc
  all_goals first
    | exact h1 (ha.trans hb.symm)
    | exact h2 (ha.trans hc.symm)
    | exact h3 (hb.trans hc.symm)

theorem exists_conj_eq_z_mul (hE : E8.SmithE8E23a) [Finite G] [IsSimpleGroup G]
    (S : Setting G) (hw : S.width = 28) (hU : LieModel S.Mbar .E7 0 2 1)
    {t u a : G} (ht : IsConj S.z t) (hu : IsConj S.z u) (htM : t ∈ S.M) (huM : u ∈ S.M)
    (htu : orderOf (t * u) = 3) (ha : IsConj S.z a) (haQ : a ∈ S.QG) (haz : a ≠ S.z)
    (hat : Commute a t) (hau : Commute a u) :
    ∃ q : G, Commute q t ∧ Commute q u ∧ q * S.z * q⁻¹ = S.z * a := by
  obtain ⟨g, rfl⟩ := isConj_iff.mp ha
  obtain ⟨htQ, huQ⟩ := not_mem_conj_QG_of_orderOf_three S ht hu htu hat hau
  have htM' := conj_inv_mem_M_of_commute S hat
  have huM' := conj_inv_mem_M_of_commute S hau
  have ht' : IsConj S.z (g⁻¹ * t * g) := ht.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have hu' : IsConj S.z (g⁻¹ * u * g) := hu.trans (isConj_iff.mpr ⟨g⁻¹, by group⟩)
  have htu' : orderOf ((g⁻¹ * t * g) * (g⁻¹ * u * g)) = 3 := by
    rw [show (g⁻¹ * t * g) * (g⁻¹ * u * g) = MulAut.conj g⁻¹ (t * u) by
      simp [MulAut.conj_apply]; group, MulEquiv.orderOf_eq]
    exact htu
  have hz'Q : g⁻¹ * S.z * g ∈ S.QG := (SME.mem_Qa_iff S g S.z).mp (S.z_mem_Qa haQ haz)
  have hzt : Commute S.z t := (mem_centralizer_singleton_iff.mp htM).symm
  have hzu : Commute S.z u := (mem_centralizer_singleton_iff.mp huM).symm
  have hcomm' : ∀ {x : G}, Commute S.z x → Commute (g⁻¹ * S.z * g) (g⁻¹ * x * g) :=
    fun {x} hx => by
      simp only [Commute, SemiconjBy] at hx ⊢
      calc g⁻¹ * S.z * g * (g⁻¹ * x * g) = g⁻¹ * (S.z * x) * g := by group
        _ = g⁻¹ * (x * S.z) * g := by rw [hx]
        _ = g⁻¹ * x * g * (g⁻¹ * S.z * g) := by group
  have hz'1 : g⁻¹ * S.z * g ≠ 1 := fun h => S.z_ne_one (by
    calc S.z = g * (g⁻¹ * S.z * g) * g⁻¹ := by group
      _ = 1 := by rw [h]; group)
  have hz'z : g⁻¹ * S.z * g ≠ S.z := fun h => haz (by
    calc g * S.z * g⁻¹ = g * (g⁻¹ * S.z * g) * g⁻¹ := by rw [h]
      _ = S.z := by group)
  obtain ⟨q, hqQ, hqt, hqu, hqz⟩ := exists_not_commute_of_E23a hE S hw hU ht' hu' htM' huM'
    htQ huQ htu' hz'Q (hcomm' hzt) (hcomm' hzu) hz'1 hz'z
  have hcz : q * (g⁻¹ * S.z * g) * q⁻¹ * (g⁻¹ * S.z * g)⁻¹ = S.z := by
    rcases commutator_eq_one_or_z S hqQ hz'Q with h | h
    · exfalso
      apply hqz
      simp only [Commute, SemiconjBy]
      calc q * (g⁻¹ * S.z * g) = q * (g⁻¹ * S.z * g) * q⁻¹ * (g⁻¹ * S.z * g)⁻¹ *
            ((g⁻¹ * S.z * g) * q) := by group
        _ = (g⁻¹ * S.z * g) * q := by rw [h, one_mul]
    · exact h
  refine ⟨g * q * g⁻¹, ?_, ?_, ?_⟩
  · simp only [Commute, SemiconjBy] at hqt ⊢
    calc g * q * g⁻¹ * t = g * (q * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * q) * g⁻¹ := by rw [hqt]
      _ = t * (g * q * g⁻¹) := by group
  · simp only [Commute, SemiconjBy] at hqu ⊢
    calc g * q * g⁻¹ * u = g * (q * (g⁻¹ * u * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * u * g) * q) * g⁻¹ := by rw [hqu]
      _ = u * (g * q * g⁻¹) := by group
  · have : q * (g⁻¹ * S.z * g) * q⁻¹ = S.z * (g⁻¹ * S.z * g) := by
      calc q * (g⁻¹ * S.z * g) * q⁻¹ =
            (q * (g⁻¹ * S.z * g) * q⁻¹ * (g⁻¹ * S.z * g)⁻¹) * (g⁻¹ * S.z * g) := by group
        _ = S.z * (g⁻¹ * S.z * g) := by rw [hcz]
    calc g * q * g⁻¹ * S.z * (g * q * g⁻¹)⁻¹ = g * (q * (g⁻¹ * S.z * g) * q⁻¹) * g⁻¹ := by group
      _ = g * (S.z * (g⁻¹ * S.z * g)) * g⁻¹ := by rw [this]
      _ = (g * S.z * g⁻¹) * S.z := by group
      _ = S.z * (g * S.z * g⁻¹) := by
          have := mem_centralizer_singleton_iff.mp (S.QG_le_M haQ)
          rw [this]

end CFSG.GF2Type.SmithTypeE.E8
