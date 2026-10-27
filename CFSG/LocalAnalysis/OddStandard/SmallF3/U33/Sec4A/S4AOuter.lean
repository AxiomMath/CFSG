module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Hyp
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.FrameFacts

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4A

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L : Subgroup G}

private theorem L_le_invCent (h : Hyp G t L) : L ≤ invCent t := by
  intro l hl
  rw [invCent, Subgroup.mem_centralizer_singleton_iff]
  exact (Subgroup.mem_centralizer_iff.mp h.mem_centralizer) l hl

private theorem conj_mem_L (h : Hyp G t L) {g : G} (hg : g ∈ invCent t) {x : G} (hx : x ∈ L) :
    g * x * g⁻¹ ∈ L := by
  have hxH : x ∈ invCent t := L_le_invCent h hx
  have hmem : (⟨g, hg⟩ : ↥(invCent t)) * (⟨x, hxH⟩ : ↥(invCent t)) *
      (⟨g, hg⟩ : ↥(invCent t))⁻¹ ∈ L.subgroupOf (invCent t) :=
    h.normal.conj_mem ⟨x, hxH⟩ (Subgroup.mem_subgroupOf.mpr hx) ⟨g, hg⟩
  simpa using (Subgroup.mem_subgroupOf.mp hmem)

private noncomputable def conjAut (h : Hyp G t L) (g : ↥(invCent t)) : MulAut ↥L where
  toFun x := ⟨(g : G) * (x : G) * (g : G)⁻¹, conj_mem_L h g.2 x.2⟩
  invFun x := ⟨(g : G)⁻¹ * (x : G) * (g : G), by
    simpa using conj_mem_L h ((invCent t).inv_mem g.2) x.2⟩
  left_inv x := by
    apply Subtype.ext
    change (g : G)⁻¹ * ((g : G) * (x : G) * (g : G)⁻¹) * (g : G) = (x : G)
    group
  right_inv x := by
    apply Subtype.ext
    change (g : G) * ((g : G)⁻¹ * (x : G) * (g : G)) * (g : G)⁻¹ = (x : G)
    group
  map_mul' x y := by
    apply Subtype.ext
    change (g : G) * ((x : G) * (y : G)) * (g : G)⁻¹
      = ((g : G) * (x : G) * (g : G)⁻¹) * ((g : G) * (y : G) * (g : G)⁻¹)
    group

private theorem conjAut_apply (h : Hyp G t L) (g : ↥(invCent t)) (x : ↥L) :
    ((conjAut h g x : ↥L) : G) = (g : G) * (x : G) * (g : G)⁻¹ := rfl

private theorem conjAut_symm_apply (h : Hyp G t L) (g : ↥(invCent t)) (x : ↥L) :
    (((conjAut h g)⁻¹ x : ↥L) : G) = (g : G)⁻¹ * (x : G) * (g : G) := rfl

private theorem conjAut_mul (h : Hyp G t L) (g g' : ↥(invCent t)) :
    conjAut h g * conjAut h g' = conjAut h (g * g') := by
  ext x
  simp only [conjAut_apply, MulAut.mul_apply, Subgroup.coe_mul]
  group

private theorem conjAut_one (h : Hyp G t L) :
    conjAut h (1 : ↥(invCent t)) = 1 := by
  ext x
  simp only [conjAut_apply, MulAut.one_apply, Subgroup.coe_one]
  group

private theorem conjAut_inv (h : Hyp G t L) (g : ↥(invCent t)) :
    (conjAut h g)⁻¹ = conjAut h g⁻¹ := by
  ext x
  rw [conjAut_symm_apply, conjAut_apply, Subgroup.coe_inv]
  group

private theorem conjAut_coe (h : Hyp G t L) (l : ↥L) :
    conjAut h ⟨(l : G), L_le_invCent h l.2⟩ = MulAut.conj l := by
  ext x
  simp only [conjAut_apply, MulAut.conj_apply, Subtype.coe_mk, Subgroup.coe_mul,
    Subgroup.coe_inv]

private theorem mem_sup_of_conjAut_eq_conj (h : Hyp G t L) (g : ↥(invCent t)) {k : ↥L}
    (heq : conjAut h g = MulAut.conj k) : (g : G) ∈ twoCore t ⊔ L := by
  have hkH : (k : G) ∈ invCent t := L_le_invCent h k.2
  have hcH : (k : G)⁻¹ * (g : G) ∈ invCent t :=
    (invCent t).mul_mem ((invCent t).inv_mem hkH) g.2
  have hcC : (k : G)⁻¹ * (g : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxL : x ∈ L := hx
    have hconj : conjAut h g ⟨x, hxL⟩ = MulAut.conj k ⟨x, hxL⟩ := by rw [heq]
    have h1 : (g : G) * x * (g : G)⁻¹ = (k : G) * x * (k : G)⁻¹ := by
      have hc := congrArg (fun y : ↥L => (y : G)) hconj
      simpa [conjAut_apply, MulAut.conj_apply] using hc
    have h2 : (k : G)⁻¹ * (g : G) * x = x * ((k : G)⁻¹ * (g : G)) := by
      calc (k : G)⁻¹ * (g : G) * x
          = (k : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g : G) := by group
        _ = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * (g : G) := by rw [h1]
        _ = x * ((k : G)⁻¹ * (g : G)) := by group
    exact h2.symm
  have hcP : (k : G)⁻¹ * (g : G) ∈ twoCore t := by
    have hmem : (k : G)⁻¹ * (g : G) ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t :=
      ⟨hcC, hcH⟩
    rwa [h.centralizer_eq] at hmem
  have hmem : (g : G) ∈ L ⊔ twoCore t := by
    have hg : (g : G) = (k : G) * ((k : G)⁻¹ * (g : G)) := by group
    rw [hg]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left k.2) (Subgroup.mem_sup_right hcP)
  rwa [sup_comm] at hmem

private theorem mem_twoCore_of_conjAut_eq (h : Hyp G t L) (g g' : ↥(invCent t))
    (heq : conjAut h g = conjAut h g') : (g : G)⁻¹ * (g' : G) ∈ twoCore t := by
  have hdH : (g : G)⁻¹ * (g' : G) ∈ invCent t :=
    (invCent t).mul_mem ((invCent t).inv_mem g.2) g'.2
  have hdC : (g : G)⁻¹ * (g' : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxL : x ∈ L := hx
    have h1 : (g : G) * x * (g : G)⁻¹ = (g' : G) * x * (g' : G)⁻¹ := by
      have hc := congrArg (fun f : MulAut ↥L => (f ⟨x, hxL⟩ : G)) heq
      simpa [conjAut_apply] using hc
    have h2 : x * ((g : G)⁻¹ * (g' : G)) = ((g : G)⁻¹ * (g' : G)) * x := by
      calc x * ((g : G)⁻¹ * (g' : G))
          = (g : G)⁻¹ * ((g : G) * x * (g : G)⁻¹) * (g' : G) := by group
        _ = (g : G)⁻¹ * ((g' : G) * x * (g' : G)⁻¹) * (g' : G) := by rw [h1]
        _ = ((g : G)⁻¹ * (g' : G)) * x := by group
    exact h2
  have hmem : (g : G)⁻¹ * (g' : G) ∈ Subgroup.centralizer (L : Set G) ⊓ invCent t :=
    ⟨hdC, hdH⟩
  rwa [h.centralizer_eq] at hmem

theorem outer_coset_conj (h : Hyp G t L) {v w : G} (hv : v ∈ invCent t) (hv2 : v * v = 1)
    (hvL : v ∉ twoCore t ⊔ L) (hw : w ∈ invCent t) (hw2 : w * w = 1) (hwv : w * v⁻¹ ∈ L) :
    ∃ l ∈ L, w = l * v * l⁻¹ := by
  have hvAut2 : conjAut h ⟨v, hv⟩ * conjAut h ⟨v, hv⟩ = 1 := by
    rw [conjAut_mul]
    have h1 : (⟨v, hv⟩ * ⟨v, hv⟩ : ↥(invCent t)) = 1 := by
      apply Subtype.ext
      simpa using hv2
    rw [h1, conjAut_one]
  have hwAut2 : conjAut h ⟨w, hw⟩ * conjAut h ⟨w, hw⟩ = 1 := by
    rw [conjAut_mul]
    have h1 : (⟨w, hw⟩ * ⟨w, hw⟩ : ↥(invCent t)) = 1 := by
      apply Subtype.ext
      simpa using hw2
    rw [h1, conjAut_one]
  have hvNotInner : ∀ k : ↥L, conjAut h ⟨v, hv⟩ ≠ MulAut.conj k := by
    intro k hk
    exact hvL (mem_sup_of_conjAut_eq_conj h ⟨v, hv⟩ hk)
  have hwNotInner : ∀ k : ↥L, conjAut h ⟨w, hw⟩ ≠ MulAut.conj k := by
    intro k hk
    have hwPL : (w : G) ∈ twoCore t ⊔ L := mem_sup_of_conjAut_eq_conj h ⟨w, hw⟩ hk
    have haPL : w * v⁻¹ ∈ twoCore t ⊔ L := Subgroup.mem_sup_right hwv
    have hv_eq : v = (w * v⁻¹)⁻¹ * w := by group
    apply hvL
    rw [hv_eq]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ haPL) hwPL
  obtain ⟨k, hk⟩ := outer_invol_conj_of_psu33 (K := ↥L) h.lieModel
    (α := conjAut h ⟨v, hv⟩) (β := conjAut h ⟨w, hw⟩) hvAut2 hvNotInner hwAut2 hwNotInner
  have hkH : (k : G) ∈ invCent t := L_le_invCent h k.2
  have hkv : (k : G) * v * (k : G)⁻¹ ∈ invCent t :=
    (invCent t).mul_mem ((invCent t).mul_mem hkH hv) ((invCent t).inv_mem hkH)
  have hk' : conjAut h ⟨w, hw⟩ = conjAut h ⟨(k : G) * v * (k : G)⁻¹, hkv⟩ := by
    rw [hk, ← conjAut_coe h k, conjAut_inv, conjAut_mul, conjAut_mul]
    rfl
  have huP : (w : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) ∈ twoCore t :=
    mem_twoCore_of_conjAut_eq h ⟨w, hw⟩ ⟨(k : G) * v * (k : G)⁻¹, hkv⟩ hk'
  have huL : (w : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) ∈ L := by
    have hconj : v⁻¹ * ((w * v⁻¹)⁻¹ * (k : G)) * v ∈ L := by
      simpa using conj_mem_L h ((invCent t).inv_mem hv)
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ hwv) k.2)
    have hprod : (v⁻¹ * ((w * v⁻¹)⁻¹ * (k : G)) * v) * (k : G)⁻¹ ∈ L :=
      Subgroup.mul_mem _ hconj (Subgroup.inv_mem _ k.2)
    convert hprod using 1
    group
  have hu1 : (w : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) = 1 := by
    have hmem : (w : G)⁻¹ * ((k : G) * v * (k : G)⁻¹) ∈ twoCore t ⊓ L := ⟨huP, huL⟩
    rw [h.twoCore_inf] at hmem
    simpa using hmem
  refine ⟨(k : G), k.2, ?_⟩
  calc w = w * 1 := by group
    _ = w * ((w : G)⁻¹ * ((k : G) * v * (k : G)⁻¹)) := by rw [hu1]
    _ = (k : G) * v * (k : G)⁻¹ := by group

end CFSG.OddStandard.SmallF3.HarrisU33.S4A
