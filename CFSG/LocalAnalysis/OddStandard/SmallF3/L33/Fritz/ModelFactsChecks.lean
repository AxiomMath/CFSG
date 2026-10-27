module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.ModelFactsPassDefs

public section

namespace CFSG.OddStandard.SmallF3.L33

open CFSG.Sporadic.Schreier

theorem sqOneB_iff (g : Equiv.Perm (Fin 26)) : sqOneB g = true ↔ g ^ 2 = 1 := by
  simp only [sqOneB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  constructor
  · intro h
    rw [pow_two]
    exact Equiv.ext h
  · intro h i
    have := congrArg (fun f : Equiv.Perm (Fin 26) => f i) h
    simpa [pow_two, Equiv.Perm.mul_apply] using this

theorem isOneB_iff (g : Equiv.Perm (Fin 26)) : isOneB g = true ↔ g = 1 := by
  simp only [isOneB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  exact ⟨fun h => Equiv.ext fun i => by simpa using h i, fun h i => by rw [h]; rfl⟩

theorem commB_iff (a b : Equiv.Perm (Fin 26)) : commB a b = true ↔ a * b = b * a := by
  simp only [commB, List.all_eq_true, List.mem_finRange, true_implies, beq_iff_eq]
  constructor
  · intro h
    exact Equiv.ext h
  · intro h i
    have := congrArg (fun f : Equiv.Perm (Fin 26) => f i) h
    simpa [Equiv.Perm.mul_apply] using this

theorem img_eq_img_iff (a b : Equiv.Perm (Fin 26)) : img a = img b ↔ a = b := by
  have h : ∀ f : Equiv.Perm (Fin 26), img f = List.ofFn (f : Fin 26 → Fin 26) := by
    intro f
    rw [img]
    exact (List.ofFn_eq_map (f := (f : Fin 26 → Fin 26))).symm
  rw [h a, h b, List.ofFn_inj]
  exact Equiv.coe_fn_injective.eq_iff

theorem conjImg_eq_img_iff (n e f : Equiv.Perm (Fin 26)) :
    conjImg n e = img f ↔ n * e * n⁻¹ = f := by
  have h : conjImg n e = img (n * e * n⁻¹) := by
    have hfun : (fun i => n (e (n⁻¹ i))) = (fun i => (n * e * n⁻¹) i) := by
      funext i
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    rw [conjImg, img, hfun]
  rw [h]
  exact img_eq_img_iff _ f

theorem kTab_eq : kTab = modelK := by
  rw [kTab, tab_eq]

theorem zTab_eq : zTab = modelZ := by
  rw [zTab, tab_eq]

theorem yTab_eq : yTab = modelY := by
  rw [yTab, tab_eq]

theorem wTab_eq : wTab = modelX ^ 2 * modelY := by
  rw [wTab, tab_eq]

theorem zkTab_eq : zkTab = modelZ * modelK := by
  rw [zkTab, tab_eq]

end CFSG.OddStandard.SmallF3.L33
