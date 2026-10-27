module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC

open CFSG.Open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V]

def trivSub (L : Subgroup (MulAut V)) (Zb : Subgroup V) : Subgroup V where
  carrier := {y | ∀ g ∈ L, g y * y⁻¹ ∈ Zb}
  one_mem' := by
    intro g _
    simp
  mul_mem' := by
    intro y y' hy hy' g hg
    have e : g (y * y') * (y * y')⁻¹ = (g y * y⁻¹) * (g y' * y'⁻¹) := by
      apply cg_eq_of_add
      simp only [map_mul, map_inv, ofMul_mul, ofMul_inv]
      abel
    rw [e]
    exact Zb.mul_mem (hy g hg) (hy' g hg)
  inv_mem' := by
    intro y hy g hg
    have e : g y⁻¹ * (y⁻¹)⁻¹ = (g y * y⁻¹)⁻¹ := by
      apply cg_eq_of_add
      simp only [map_inv, ofMul_mul, ofMul_inv, inv_inv]
      abel
    rw [e]
    exact Zb.inv_mem (hy g hg)

theorem mem_trivSub {L : Subgroup (MulAut V)} {Zb : Subgroup V} {y : V} :
    y ∈ trivSub L Zb ↔ ∀ g ∈ L, g y * y⁻¹ ∈ Zb :=
  Iff.rfl

theorem le_trivSub_iff {L : Subgroup (MulAut V)} {Zb W : Subgroup V} :
    W ≤ trivSub L Zb ↔ LTrivOn L Zb W :=
  ⟨fun h g hg z hz => mem_trivSub.mp (h hz) g hg,
    fun h z hz => mem_trivSub.mpr fun g hg => h g hg z hz⟩

theorem map_mem_trivSub {L : Subgroup (MulAut V)} {Zb : Subgroup V} {g : MulAut V}
    (hg : ∀ z ∈ Zb, g z ∈ Zb) (hc : ∀ h ∈ L, g⁻¹ * h * g ∈ L) {y : V}
    (hy : y ∈ trivSub L Zb) : g y ∈ trivSub L Zb := by
  rw [mem_trivSub] at hy ⊢
  intro h hh
  have e : h (g y) * (g y)⁻¹ = g ((g⁻¹ * h * g) y * y⁻¹) := by
    simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
  rw [e]
  exact hg _ (hy _ (hc h hh))

theorem mem_stabSub_trivSub {L : Subgroup (MulAut V)} {Zb : Subgroup V} {g : MulAut V}
    (hg : ∀ z ∈ Zb, g z ∈ Zb) (hg' : ∀ z ∈ Zb, g⁻¹ z ∈ Zb)
    (hc : ∀ h ∈ L, g⁻¹ * h * g ∈ L) (hc' : ∀ h ∈ L, g * h * g⁻¹ ∈ L) :
    g ∈ stabSub (trivSub L Zb) :=
  mem_stabSub_of_inv (fun _ hy => map_mem_trivSub hg hc hy)
    (fun _ hy => map_mem_trivSub (g := g⁻¹) hg' (fun h hh => by rw [inv_inv]; exact hc' h hh) hy)

theorem xInv_trivSub {L A : Subgroup (MulAut V)} {Zb : Subgroup V} (hZb : XInv L A Zb)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) : XInv L A (trivSub L Zb) := by
  have hA : ∀ a ∈ A, ∀ h ∈ L, a⁻¹ * h * a ∈ L := by
    intro a ha h hh
    have e : a * (a⁻¹ * h * a) * a⁻¹ = h := by group
    exact (Subgroup.mem_normalizer_iff.mp (hAL ha) (a⁻¹ * h * a)).mpr (by rw [e]; exact hh)
  refine ⟨fun x hx => mem_stabSub_trivSub (g := x) (fun z hz => mem_of_stab (hZb.1 hx) hz)
      (fun z hz => mem_of_stab (hZb.1 (L.inv_mem hx)) hz)
      (fun h hh => L.mul_mem (L.mul_mem (L.inv_mem hx) hh) hx)
      (fun h hh => L.mul_mem (L.mul_mem hx hh) (L.inv_mem hx)), ?_⟩
  intro a ha
  exact mem_stabSub_trivSub (g := a) (fun z hz => mem_of_stab (hZb.2 ha) hz)
    (fun z hz => mem_of_stab (hZb.2 (A.inv_mem ha)) hz)
    (fun h hh => hA a ha h hh)
    (fun h hh => (Subgroup.mem_normalizer_iff.mp (hAL ha) h).mp hh)

theorem exists_minimal_of_finite {α : Type} [PartialOrder α] [Finite α] (P : α → Prop) {x : α}
    (hx : P x) : ∃ z, P z ∧ ∀ w, P w → ¬ w < z := by
  obtain ⟨z, hz, hmin⟩ := (wellFounded_lt (α := α)).has_min {w | P w} ⟨x, hx⟩
  exact ⟨z, hz, fun w hw => hmin w hw⟩

theorem finite_subgroup_of_finite [Finite V] : Finite (Subgroup V) :=
  Finite.of_injective (fun H : Subgroup V => (H : Set V)) SetLike.coe_injective

theorem exists_noncentral_chief [Finite V] {L A : Subgroup (MulAut V)}
    (hperf : _root_.commutator ↥L = ⊤)
    (hAL : A ≤ Subgroup.normalizer (L : Set (MulAut V))) {Zb Y : Subgroup V}
    (hZb : XInv L A Zb) (hY : XInv L A Y) (hbY : Zb ≤ Y) (hnc : ¬ LTrivOn L Zb Y) :
    ∃ Z' Z : Subgroup V, XInv L A Z' ∧ XInv L A Z ∧ Zb ≤ Z' ∧ Z' < Z ∧ Z ≤ Y ∧
      (∀ W, XInv L A W → Z' ≤ W → W ≤ Z → W = Z' ∨ W = Z) ∧
      ¬ LTrivOn L Z' Z ∧ LTrivOn L Zb Z' := by
  haveI : Finite (Subgroup V) := finite_subgroup_of_finite
  obtain ⟨Z, ⟨hZinv, hbZ, hZY, hnZ⟩, hmin⟩ := exists_minimal_of_finite
    (fun W : Subgroup V => XInv L A W ∧ Zb ≤ W ∧ W ≤ Y ∧ ¬ LTrivOn L Zb W) (x := Y)
    ⟨hY, hbY, le_rfl, hnc⟩
  have hbC : Zb ≤ trivSub L Zb := le_trivSub_iff.mpr fun g hg z hz =>
    Zb.mul_mem (mem_of_stab (hZb.1 hg) hz) (Zb.inv_mem hz)
  have hbZ' : Zb ≤ Z ⊓ trivSub L Zb := le_inf hbZ hbC
  have hCinv : XInv L A (trivSub L Zb) := xInv_trivSub hZb hAL
  have hZ'lt : Z ⊓ trivSub L Zb < Z := by
    refine lt_of_le_of_ne inf_le_left fun heq => hnZ ?_
    have hZC : Z ≤ trivSub L Zb := by
      rw [← heq]
      exact inf_le_right
    exact le_trivSub_iff.mp hZC
  have htriv : LTrivOn L Zb (Z ⊓ trivSub L Zb) := le_trivSub_iff.mp inf_le_right
  refine ⟨Z ⊓ trivSub L Zb, Z, XInv.inf hZinv hCinv, hZinv, hbZ', hZ'lt, hZY, ?_, ?_, htriv⟩
  · intro W hW hZ'W hWZ
    by_cases hWZ' : W = Z
    · exact Or.inr hWZ'
    · refine Or.inl (le_antisymm (le_inf hWZ ?_) hZ'W)
      by_contra hnot
      have hPW : XInv L A W ∧ Zb ≤ W ∧ W ≤ Y ∧ ¬ LTrivOn L Zb W :=
        ⟨hW, le_trans hbZ' hZ'W, le_trans hWZ hZY, fun h => hnot (le_trivSub_iff.mpr h)⟩
      exact hmin W hPW (lt_of_le_of_ne hWZ hWZ')
  · intro h1
    exact hnZ (flag_trivial hperf (W₀ := Zb) (W₁ := Z ⊓ trivSub L Zb) (M := Z)
      (fun g hg m hm => mem_of_stab (hZinv.1 hg) hm)
      (fun g hg w hw => mem_of_stab (hZb.1 hg) hw) h1 htriv)

end CFSG.LocalAnalysis.RankThreeUC
