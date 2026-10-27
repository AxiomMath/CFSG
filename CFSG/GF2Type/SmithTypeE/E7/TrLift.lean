module

public import CFSG.LargeExtraspecial.S14SMKDeltaBasic
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.GF2Type.SmithTypeE.E7

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.S14
open CFSG.LargeExtraspecial.S14.SMK (commute_of_mem_Kz_Dl)

variable {G : Type} [Group G] [Finite G] (S : Setting G) {g : G}

omit [Finite G] in
theorem not_exists_conj_mul_z (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    ¬ ∃ y ∈ S.QG, y * (g * S.z * g⁻¹) * y⁻¹ = g * S.z * g⁻¹ * S.z := by
  rintro ⟨y, -, hy⟩
  apply hxz
  rw [← hy]
  exact (isConj_iff.mpr ⟨g, rfl⟩).trans (isConj_iff.mpr ⟨y, rfl⟩)

theorem fixQt_eq_of_not_isConj (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    S.fixQt (g * S.z * g⁻¹) = S.clSub (S.QG ⊓ centralizer ({g * S.z * g⁻¹} : Set G)) := by
  by_contra h
  exact not_exists_conj_mul_z S hxz (S.lemma_3_2_1 hxM h)

theorem Dl_le_commutator (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    S.QG ⊓ S.Qa g ≤ ⁅zpowers (g * S.z * g⁻¹), S.QG⁆ := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  rw [(S.commutator_eq_centralizer_centralizer hxM hxQ hx2
    (fixQt_eq_of_not_isConj S hxM hxz)).1]
  intro d hd
  exact ⟨hd.1, mem_centralizer_iff.mpr fun u hu => commute_of_mem_Kz_Dl S hxQ hu hd⟩

theorem clSub_Dl_le_commQt (hxM : g * S.z * g⁻¹ ∈ S.M) (hxQ : g * S.z * g⁻¹ ∉ S.QG)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) :
    S.clSub (S.QG ⊓ S.Qa g) ≤ S.commQt (g * S.z * g⁻¹) := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  intro v hv
  obtain ⟨d, hd, -, rfl⟩ := S.mem_clSub_iff.mp hv
  have h := Dl_le_commutator S hxM hxQ hxz hd
  rw [S.commutator_zpowers_eq_clPre hxM hxQ hx2] at h
  exact h.2

theorem exists_commute_rho_eq_of_not_isConj (hxM : g * S.z * g⁻¹ ∈ S.M)
    (hxz : ¬ IsConj S.z (g * S.z * g⁻¹ * S.z)) (m : S.M)
    (hm : S.ρ m * S.ρ ⟨_, hxM⟩ = S.ρ ⟨_, hxM⟩ * S.ρ m) :
    ∃ m' : S.M, Commute (m' : G) (g * S.z * g⁻¹) ∧ S.ρ m' = S.ρ m := by
  have hx2 : (g * S.z * g⁻¹) ^ 2 = 1 := by rw [conj_pow, S.z_sq, mul_one, mul_inv_cancel]
  have hfix := fixQt_eq_of_not_isConj S hxM hxz
  have hhM : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ * (g * S.z * g⁻¹)⁻¹ ∈ S.M :=
    S.M.mul_mem (S.M.mul_mem (S.M.mul_mem m.2 hxM) (S.M.inv_mem m.2)) (S.M.inv_mem hxM)
  have hhQ : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ * (g * S.z * g⁻¹)⁻¹ ∈ S.QG := by
    have e : (⟨_, hhM⟩ : S.M) = m * ⟨_, hxM⟩ * m⁻¹ * (⟨_, hxM⟩ : S.M)⁻¹ := Subtype.ext rfl
    have h1 : S.ρ ⟨_, hhM⟩ = 1 := by
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hm]
      group
    exact (S.ρ_eq_one_iff _).mp h1
  have hgh : (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ =
      (m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹ * (g * S.z * g⁻¹)⁻¹ * (g * S.z * g⁻¹) := by group
  rcases S.lemma_3_2_2 hxM hx2 hfix m.2 hhQ hgh with ⟨y, hy, hyx⟩ | ⟨y, hy, hyx⟩
  · have hyM : y⁻¹ ∈ S.M := S.QG_le_M (S.QG.inv_mem hy)
    refine ⟨⟨y⁻¹, hyM⟩ * m, ?_, ?_⟩
    · show y⁻¹ * (m : G) * (g * S.z * g⁻¹) = (g * S.z * g⁻¹) * (y⁻¹ * m)
      calc y⁻¹ * (m : G) * (g * S.z * g⁻¹) =
          y⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * m := by group
        _ = y⁻¹ * (y * (g * S.z * g⁻¹) * y⁻¹) * m := by rw [hgh, hyx]
        _ = (g * S.z * g⁻¹) * (y⁻¹ * m) := by group
    · have h1 : S.ρ ⟨y⁻¹, hyM⟩ = 1 := (S.ρ_eq_one_iff _).mpr (S.QG.inv_mem hy)
      rw [map_mul, h1, one_mul]
  · exfalso
    apply hxz
    have e : g * S.z * g⁻¹ * S.z =
        y⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * y := by
      rw [hgh, ← hyx]
      group
    rw [e]
    have h1 : IsConj S.z (g * S.z * g⁻¹) := isConj_iff.mpr ⟨g, rfl⟩
    have h2 : IsConj (g * S.z * g⁻¹) ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) :=
      isConj_iff.mpr ⟨(m : G), rfl⟩
    have h3 : IsConj ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹)
        (y⁻¹ * ((m : G) * (g * S.z * g⁻¹) * (m : G)⁻¹) * y) :=
      isConj_iff.mpr ⟨y⁻¹, by rw [inv_inv]⟩
    exact h1.trans (h2.trans h3)

omit [Finite G] in
theorem conj_mem_Dl {m : G} (hmM : m ∈ S.M) (hmx : Commute m (g * S.z * g⁻¹)) {d : G}
    (hd : d ∈ S.QG ⊓ S.Qa g) : m * d * m⁻¹ ∈ S.QG ⊓ S.Qa g := by
  have hmT : m ∈ (S.conjBy g).M := mem_centralizer_singleton_iff.mpr hmx.eq
  exact ⟨S.conj_mem_QG hmM hd.1, (S.conjBy g).conj_mem_QG hmT hd.2⟩

end CFSG.GF2Type.SmithTypeE.E7
