module

public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts

public noncomputable section

namespace CFSG.GorensteinWalter

theorem a7V_conjugation_in_centralizer_certificate :
    ∀ x : ASevenCertificateGroup, x * a7t = a7t * x →
      (x * a7t * x⁻¹ = 1 ∨ x * a7t * x⁻¹ = a7t ∨
        x * a7t * x⁻¹ = a7u ∨ x * a7t * x⁻¹ = a7t * a7u) ∧
      (x * a7u * x⁻¹ = 1 ∨ x * a7u * x⁻¹ = a7t ∨
        x * a7u * x⁻¹ = a7u ∨ x * a7u * x⁻¹ = a7t * a7u) := by
  decide +kernel

theorem a7V_le_t_centralizer :
    a7V ≤ Subgroup.centralizer ({a7t} : Set ASevenCertificateGroup) := by
  intro v hv
  change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
  rcases hv with rfl | rfl | rfl | rfl <;>
    rw [Subgroup.mem_centralizer_singleton_iff] <;> decide

theorem a7V_normalized_by_t_centralizer :
    Subgroup.centralizer ({a7t} : Set ASevenCertificateGroup) ≤
      Subgroup.normalizer (a7V : Set ASevenCertificateGroup) := by
  have hmem (x : ASevenCertificateGroup)
      (hx : x ∈ Subgroup.centralizer ({a7t} : Set ASevenCertificateGroup))
      (v : ASevenCertificateGroup) (hv : v ∈ a7V) : x * v * x⁻¹ ∈ a7V := by
    have hcert := a7V_conjugation_in_centralizer_certificate x
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
    have ht : x * a7t * x⁻¹ ∈ a7V := hcert.1
    have hu : x * a7u * x⁻¹ ∈ a7V := hcert.2
    change v = 1 ∨ v = a7t ∨ v = a7u ∨ v = a7t * a7u at hv
    rcases hv with rfl | rfl | rfl | rfl
    · simp
    · exact ht
    · exact hu
    · have h := a7V.mul_mem ht hu
      have heq : x * (a7t * a7u) * x⁻¹ =
          (x * a7t * x⁻¹) * (x * a7u * x⁻¹) := by group
      rwa [← heq] at h
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro v
  constructor
  · exact hmem x hx v
  · intro hv
    have h := hmem x⁻¹ ((Subgroup.centralizer _).inv_mem hx) (x * v * x⁻¹) hv
    have heq : x⁻¹ * (x * v * x⁻¹) * (x⁻¹)⁻¹ = v := by group
    rwa [heq] at h

theorem a7V_le_sylow_of_le_t_centralizer (T : Sylow 2 ASevenCertificateGroup)
    (hT : (T : Subgroup ASevenCertificateGroup) ≤
      Subgroup.centralizer ({a7t} : Set ASevenCertificateGroup)) :
    a7V ≤ (T : Subgroup ASevenCertificateGroup) := by
  let C := Subgroup.centralizer ({a7t} : Set ASevenCertificateGroup)
  let V := a7V.subgroupOf C
  let : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer a7V_le_t_centralizer).mpr
    a7V_normalized_by_t_centralizer
  have hVp : IsPGroup 2 V := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe a7V_le_t_centralizer).toEquiv,
      aSeven_structure_fact_1_8_ii_centralizer.2.2.2.card_four]
    decide
  have hle := hVp.le_sylow_of_normal (T.subtype hT)
  have h := Subgroup.map_mono (f := C.subtype) hle
  rwa [Subgroup.map_subgroupOf_eq_of_le a7V_le_t_centralizer,
    Sylow.coe_subtype, Subgroup.map_subgroupOf_eq_of_le hT] at h

end CFSG.GorensteinWalter
