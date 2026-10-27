module

public import CFSG.Dihedral.ASevenOriginalFourgroupLabels
public import CFSG.Dihedral.ASevenOneCycleFixedKernel
public import CFSG.Dihedral.OriginalFixedKernelTrivial
public import CFSG.Dihedral.OriginalCyclingOddCore
import all CFSG.Dihedral.BlueprintDefs
import all CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ASevenStructureFacts
public import CFSG.Dihedral.OriginalASevenSylowAlignment

public noncomputable section

namespace CFSG.DihedralBlueprint.OriginalData

open GorensteinWalter

variable {G : Type} [Group G] [Finite G] (d : OriginalData G)

theorem E_inf_eq_bot_of_aSeven_labels (f : G ≃* ASevenCertificateGroup)
    (hS : (d.S : Subgroup G).map f.toMonoidHom = a7S)
    (hR : d.R.map f.toMonoidHom = a7U)
    (H : Subgroup G) (hSH : (d.S : Subgroup G) ≤ H)
    (i j k l : Fin 2) (hkl : k ≠ l)
    (hi : (d.V i).map f.toMonoidHom = a7LocalFourgroup k)
    (hj : (d.V j).map f.toMonoidHom = a7LocalFourgroup l)
    (hc : Cycles H (d.V i)) (hnc : ¬ Cycles H (d.V j)) : d.E j ⊓ H = ⊥ := by
  have hSHmap : a7S ≤ H.map f.toMonoidHom := by
    rw [← hS]
    exact Subgroup.map_mono hSH
  have hcmap : Cycles (H.map f.toMonoidHom) (a7LocalFourgroup k) := by
    rw [← hi]
    exact cycles_map_equiv f H (d.V i) hc
  have hncmap : ¬ Cycles (H.map f.toMonoidHom) (a7LocalFourgroup l) := by
    intro h
    apply hnc
    apply cycles_of_map_equiv f H (d.V j)
    rwa [hj]
  have hfixed := a7_one_cycle_opposite_fixed_eq_bot (H.map f.toMonoidHom)
    hSHmap k l hkl hcmap hncmap
  apply le_antisymm _ bot_le
  intro x hx
  have hxR : x ∈ d.R := hx.1.1
  have hxC : x ∈ Subgroup.centralizer (d.V j : Set G) := hx.1.2
  have hxmap : f x ∈ (a7U ⊓
      Subgroup.centralizer (a7LocalFourgroup l : Set ASevenCertificateGroup)) ⊓
      H.map f.toMonoidHom := by
    refine ⟨⟨?_, ?_⟩, Subgroup.mem_map_of_mem f.toMonoidHom hx.2⟩
    · rw [← hR]
      exact Subgroup.mem_map_of_mem f.toMonoidHom hxR
    · change f x ∈ Subgroup.centralizer (a7LocalFourgroup l : Set ASevenCertificateGroup)
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      rw [← hj] at hv
      obtain ⟨z, hz, hzv⟩ := Subgroup.mem_map.mp hv
      change f z = v at hzv
      rw [← hzv]
      simpa only [map_mul] using congrArg f (Subgroup.mem_centralizer_iff.mp hxC z hz)
  rw [hfixed] at hxmap
  change f x = 1 at hxmap
  change x = 1
  exact f.injective (hxmap.trans f.map_one.symm)

theorem one_cycle_opposite_fixed_eq_bot_of_aSeven_model
    (e : G ≃* alternatingGroup (Fin 7)) (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H) (i j : Fin 2) (hij : i ≠ j)
    (hc : Cycles H (d.V i)) (hnc : ¬ Cycles H (d.V j)) : d.E j ⊓ H = ⊥ := by
  by_cases hR : d.R = ⊥
  · simp only [E, hR, bot_inf_eq]
  obtain ⟨f, ht, hS, hRmap⟩ := d.aSeven_equiv_R_sylow_aligned hR e
  rcases d.original_fourgroup_labels_of_aSeven_alignment f ht hS with h01 | h10
  · fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact d.E_inf_eq_bot_of_aSeven_labels f hS hRmap H hSH 0 1 0 1
        (by decide) h01.1 h01.2 hc hnc
    · exact d.E_inf_eq_bot_of_aSeven_labels f hS hRmap H hSH 1 0 1 0
        (by decide) h01.2 h01.1 hc hnc
    · exact (hij rfl).elim
  · fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact d.E_inf_eq_bot_of_aSeven_labels f hS hRmap H hSH 0 1 1 0
        (by decide) h10.1 h10.2 hc hnc
    · exact d.E_inf_eq_bot_of_aSeven_labels f hS hRmap H hSH 1 0 0 1
        (by decide) h10.2 h10.1 hc hnc
    · exact (hij rfl).elim

theorem one_cycle_opposite_fixed_eq_bot [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H) (i j : Fin 2) (hij : i ≠ j)
    (hc : Cycles H (d.V i)) (hnc : ¬ Cycles H (d.V j)) : d.E j ⊓ H = ⊥ := by
  rcases gorenstein_walter G hnonab d.S
      ⟨2 ^ (d.n - 1), d.sylow_mulEquiv_dihedral⟩ with hA | hL
  · exact d.one_cycle_opposite_fixed_eq_bot_of_aSeven_model hA.some H hSH i j hij hc hnc
  · obtain ⟨r, k, hr, hrodd, hsize, ⟨e⟩⟩ := hL
    let _ : Fact r.Prime := hr
    have hk : k ≠ 0 := by
      intro h
      simp [h] at hsize
    have hK : IsOddPrimePower (Nat.card (GaloisField r k)) :=
      ⟨r, k, hr.out, hrodd, by omega, GaloisField.card r k hk⟩
    rw [d.E_eq_bot_of_psl2_model (GaloisField r k) hK e j, bot_inf_eq]

theorem one_cycle_fixed_intersection [IsSimpleGroup G]
    (hnonab : ∃ a b : G, a * b ≠ b * a) (H : Subgroup G)
    (hSH : (d.S : Subgroup G) ≤ H) (i j : Fin 2) (hij : i ≠ j)
    (hc : Cycles H (d.V i)) (hnc : ¬ Cycles H (d.V j)) :
    d.E j ⊓ H = d.commonE ⊓ H := by
  rw [d.one_cycle_opposite_fixed_eq_bot hnonab H hSH i j hij hc hnc,
    d.commonE_eq_bot hnonab, bot_inf_eq]

end CFSG.DihedralBlueprint.OriginalData
