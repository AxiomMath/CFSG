module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Types
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Invol
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open scoped commutatorElement
open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts CFSG.QuasithinUnique.Setup.X3Aut
  AutA6Three CFSG.QuasithinUnique.Out21.A6

namespace AutA6Types

theorem centralizer_check40 : AutA6Invol.invCodes.all (fun a => fixes3 a ||
    decide ((Core.autL.filter fun c => Core.cmul a c == Core.cmul c a).length ≤ 40)) = true := by
  decide +kernel

theorem invNoFix_ne_nil : invNoFix ≠ [] := by
  have : invNoFix.isEmpty = false := by decide +kernel
  intro h
  rw [h] at this
  simp at this

end AutA6Types

open AutA6Types

theorem card_centralizer_aut_le_forty (a : MulAut (alternatingGroup (Fin 6))) (h2 : a * a = 1)
    (h1 : a ≠ 1) (hfix : ∀ x : alternatingGroup (Fin 6), orderOf x = 3 → a x ≠ x) :
    Nat.card (Subgroup.centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6))))) ≤ 40 := by
  set x : AutA6 := thetaEquiv.symm a with hx
  have hxx : x * x = 1 := by
    apply thetaEquiv.injective
    rw [map_mul, map_one, hx, MulEquiv.apply_symm_apply, h2]
  have hx1 : x ≠ 1 := by
    intro h
    apply h1
    rw [← MulEquiv.apply_symm_apply thetaEquiv a, ← hx, h, map_one]
  have hmem := AutA6Invol.cd_involution hxx hx1
  have hcheck := List.all_eq_true.mp centralizer_check40 _ hmem
  have hnf : fixes3 (cd x) = false := by
    rw [Bool.eq_false_iff]
    intro h
    obtain ⟨y, hy3, hy⟩ := (fixes3_iff x).2 h
    rw [hx, MulEquiv.apply_symm_apply] at hy
    exact hfix y hy3 hy
  rw [hnf, Bool.false_or, decide_eq_true_eq] at hcheck
  set L := Core.autL.filter fun c => Core.cmul (cd x) c == Core.cmul c (cd x) with hL
  let f : ↥(Subgroup.centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6))))) →
      ↥L.toFinset := fun g => ⟨cd (thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6)))), by
    have hg := (Subgroup.mem_centralizer_iff.mp g.2) a (Set.mem_singleton a)
    have hc : x * thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) =
        thetaEquiv.symm (g : MulAut (alternatingGroup (Fin 6))) * x := by
      rw [hx, ← map_mul, ← map_mul, hg]
    rw [List.mem_toFinset, hL, List.mem_filter]
    refine ⟨cd_mem_autL _, ?_⟩
    rw [← cd_mul, ← cd_mul, hc]
    simp⟩
  have hf : Function.Injective f := by
    intro g g' h
    have h1 := cd_injective (congrArg Subtype.val h)
    exact Subtype.ext (thetaEquiv.symm.injective h1)
  calc Nat.card (Subgroup.centralizer ({a} : Set (MulAut (alternatingGroup (Fin 6)))))
      ≤ Nat.card ↥L.toFinset := Nat.card_le_card_of_injective f hf
    _ = L.toFinset.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ L.length := List.toFinset_card_le L
    _ ≤ 40 := hcheck

theorem exists_pgl_involution : ∃ α : MulAut (alternatingGroup (Fin 6)), α * α = 1 ∧
    α ∉ (MulAut.conj : alternatingGroup (Fin 6) →* MulAut (alternatingGroup (Fin 6))).range ∧
    ∀ x : alternatingGroup (Fin 6), orderOf x = 3 → α x ≠ x := by
  obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ invNoFix_ne_nil
  have hc' := hc
  unfold invNoFix at hc'
  rw [List.mem_filter] at hc'
  obtain ⟨hco, hcf⟩ := hc'
  unfold invOut at hco
  rw [List.mem_filter] at hco
  obtain ⟨hcA, hcsq⟩ := hco
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcsq
  obtain ⟨y, hy, hy2⟩ := AutA6Invol.exists_aut_of_mem hcA hcsq.1
  have hyP : y ∉ PslSub := by
    rw [mem_PslSub_iff_contains, hy]
    simpa using hcsq.2
  refine ⟨thetaEquiv y, ?_, ?_, ?_⟩
  · rw [← map_mul, hy2, map_one]
  · intro h
    rw [mem_inner_iff, MulEquiv.symm_apply_apply] at h
    exact hyP h
  · intro a ha3 ha
    have : fixes3 (cd y) = true := (fixes3_iff y).1 ⟨a, ha3, ha⟩
    rw [hy] at this
    simp at hcf
    rw [this] at hcf
    simp at hcf

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
