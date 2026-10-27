module

public import CFSG.Dihedral.ASevenCyclingWords
import all CFSG.Dihedral.BlueprintDefs
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import CFSG.Dihedral.OriginalCosetModel

public noncomputable section

namespace CFSG.DihedralBlueprint

open GorensteinWalter

instance a7S_decidable : DecidablePred (fun x : ASevenCertificateGroup => x ∈ a7S) := by
  intro x
  change Decidable (x = 1 ∨ x = a7v ∨ x = a7v ^ 2 ∨ x = a7v ^ 3 ∨
    x = a7s ∨ x = a7s * a7v ∨ x = a7s * a7v ^ 2 ∨ x = a7s * a7v ^ 3)
  infer_instance

instance a7S_fintype : Fintype a7S := Subtype.fintype _

theorem a7_original_reflection_labels_certificate :
    ∀ r s : a7S, (r : ASevenCertificateGroup) ^ 2 = a7t →
      (s : ASevenCertificateGroup) ^ 2 = 1 → (s : ASevenCertificateGroup) ≠ 1 →
      (s : ASevenCertificateGroup) ≠ a7t →
      (((s : ASevenCertificateGroup) = a7s ∨ (s : ASevenCertificateGroup) = a7t * a7s) ∧
        ((s : ASevenCertificateGroup) * r = a7s * a7v ∨
          (s : ASevenCertificateGroup) * r = a7t * (a7s * a7v))) ∨
      (((s : ASevenCertificateGroup) = a7s * a7v ∨
          (s : ASevenCertificateGroup) = a7t * (a7s * a7v)) ∧
        ((s : ASevenCertificateGroup) * r = a7s ∨
          (s : ASevenCertificateGroup) * r = a7t * a7s)) := by
  decide +kernel

namespace OriginalData

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem V_map_eq_a7LocalFourgroup (f : G ≃* ASevenCertificateGroup)
    (ht : f d.t = a7t) (i k : Fin 2)
    (hreflection : f (d.s * d.r ^ i.val) = a7s * a7v ^ k.val ∨
      f (d.s * d.r ^ i.val) = a7t * (a7s * a7v ^ k.val)) :
    (d.V i).map f.toMonoidHom = a7LocalFourgroup k := by
  have hle : (d.V i).map f.toMonoidHom ≤ a7LocalFourgroup k := by
    change (Subgroup.closure ({d.t, d.s * d.r ^ i.val} : Set G)).map f.toMonoidHom ≤ _
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨v, hv, rfl⟩
    rcases hv with rfl | hv
    · change f d.t ∈ a7LocalFourgroup k
      rw [ht]
      change a7t ∈ ({a7t * (a7s * a7v ^ k.val), a7t, a7s * a7v ^ k.val, 1} : Set ASevenCertificateGroup)
      simp
    · rw [Set.mem_singleton_iff] at hv
      rw [hv]
      change f (d.s * d.r ^ i.val) ∈ ({a7t * (a7s * a7v ^ k.val), a7t, a7s * a7v ^ k.val, 1} : Set ASevenCertificateGroup)
      rcases hreflection with h | h <;> simp [h]
  apply Subgroup.eq_of_le_of_card_ge hle
  rw [(a7LocalFourgroup_isKleinFour k).card_four,
    Subgroup.card_map_of_injective f.injective, (d.V_isKleinFour_general i).card_four]

theorem original_fourgroup_labels_of_aSeven_alignment (f : G ≃* ASevenCertificateGroup)
    (ht : f d.t = a7t) (hS : (d.S : Subgroup G).map f.toMonoidHom = a7S) :
    (((d.V 0).map f.toMonoidHom = a7LocalFourgroup 0) ∧
      ((d.V 1).map f.toMonoidHom = a7LocalFourgroup 1)) ∨
    (((d.V 0).map f.toMonoidHom = a7LocalFourgroup 1) ∧
      ((d.V 1).map f.toMonoidHom = a7LocalFourgroup 0)) := by
  have hrS : f d.r ∈ a7S := by
    rw [← hS]
    exact Subgroup.mem_map_of_mem f.toMonoidHom d.r_mem_sylow
  have hsS : f d.s ∈ a7S := by
    rw [← hS]
    exact Subgroup.mem_map_of_mem f.toMonoidHom d.s_mem_sylow
  have hn : d.n = 3 := d.n_eq_three_of_aSeven_model f
  have hr2 : f d.r ^ 2 = a7t := by
    have hrt : d.r ^ 2 = d.t := by simp [t, hn]
    rw [← map_pow, hrt, ht]
  have hs2 : f d.s ^ 2 = 1 := by rw [← map_pow, d.s_sq, map_one]
  have hs1 : f d.s ≠ 1 := by
    intro h
    have hs := f.injective (h.trans f.map_one.symm)
    have hord := d.order_s
    rw [hs, orderOf_one] at hord
    omega
  have hst : f d.s ≠ a7t := by
    intro h
    have hs : d.s = d.t := f.injective (h.trans ht.symm)
    exact d.s_not_mem_rotation (hs ▸ (Subgroup.zpowers d.r).pow_mem (Subgroup.mem_zpowers _) _)
  rcases a7_original_reflection_labels_certificate ⟨f d.r, hrS⟩ ⟨f d.s, hsS⟩
    hr2 hs2 hs1 hst with h01 | h10
  · left
    refine ⟨d.V_map_eq_a7LocalFourgroup f ht 0 0 ?_,
      d.V_map_eq_a7LocalFourgroup f ht 1 1 ?_⟩
    · simpa only [Fin.val_zero, pow_zero, mul_one] using h01.1
    · simpa only [Fin.val_one, pow_one, map_mul] using h01.2
  · right
    refine ⟨d.V_map_eq_a7LocalFourgroup f ht 0 1 ?_,
      d.V_map_eq_a7LocalFourgroup f ht 1 0 ?_⟩
    · simpa only [Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one] using h10.1
    · simpa only [Fin.val_zero, pow_zero, mul_one, Fin.val_one, pow_one, map_mul] using h10.2

end OriginalData

end CFSG.DihedralBlueprint
