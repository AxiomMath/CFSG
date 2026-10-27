module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Co1CenterInputs
public import CFSG.Sporadic.Co1Block.CentQ
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.EvenSporadicStandard.Solomon78

open CFSG.Sporadic.Co1Schreier CFSG.Sporadic.Co1Block CFSG.Sporadic.Co1Schreier.Native
  CFSG.Sporadic.Co1.InvNative CFSG.Sporadic.Co1.TwoBNative

theorem forall₂_mem_right {α β : Type*} {P : α → β → Prop} {rs : List α} {gs : List β}
    (h : List.Forall₂ P rs gs) {r : α} (hr : r ∈ rs) : ∃ g ∈ gs, P r g := by
  induction h with
  | nil => simp at hr
  | cons hab _ ih =>
    rcases List.mem_cons.1 hr with rfl | hr
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨g, hg, hP⟩ := ih hr
      exact ⟨g, List.mem_cons_of_mem _ hg, hP⟩

theorem eq_one_or_of_centerFilter {tR : Rows} {t : GL24} (ht : MRep tR t) {B : List Rows}
    {BG : List GL24} (hB : List.Forall₂ MRep B BG) {pts : Array Rows}
    (h : centerFilterOf tR B pts = true) {i : ℕ} (hi : i < pts.size)
    (hv : validRows pts[i]! = true) {z : GL24} (hz : MRep pts[i]! z)
    (hc : ∀ g ∈ BG, z * g = g * z) : z = 1 ∨ z = t := by
  simp only [centerFilterOf, Bool.and_eq_true, Array.all_eq_true] at h
  obtain ⟨hvB, hall⟩ := h
  have hp := hall i hi
  rw [← getElem!_pos pts i hi] at hp
  have hcomm : commutesWithAll B pts[i]! = true := by
    unfold commutesWithAll
    rw [List.all_eq_true]
    intro g hg
    obtain ⟨G, hG, hgG⟩ := forall₂_mem_right hB hg
    have e1 : MRep (mul pts[i]! g) (z * G) := hz.mul hgG
    have e2 : MRep (mul g pts[i]!) (G * z) := hgG.mul hz
    rw [hc G hG] at e1
    have hvg : validRows g = true := List.all_eq_true.1 hvB g hg
    exact beq_iff_eq.2 (CFSG.Sporadic.Co1.Module.rowsMatrix_injective_of_valid
      (CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hv hvg)
      (CFSG.Sporadic.Co1.Module.TwoB.validRows_mulRows hvg hv) (e1.trans e2.symm))
  rw [hcomm] at hp
  simp only [Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq] at hp
  rcases hp with h1 | h1
  · left
    have : MRep pts[i]! 1 := by rw [h1]; exact MRep.one
    exact hz.eq this
  · right
    have : MRep pts[i]! t := by rw [h1]; exact ht
    exact hz.eq this

theorem exists_point_of_mem_Q {tR : Rows} {d₁ d₂ : List (List ℤ)} {bidx : List ℕ}
    {Qg : List Rows} {cap : ℕ} {roots : List Rows} {gens : List (List ℕ)} {sizes : List ℕ}
    {qgs : ℕ → GL24} (hQ : QRep Qg qgs)
    (h : Native.qCheckOf tR d₁ bidx d₂ Qg cap roots gens sizes = true) {y : GL24}
    (hy : y ∈ qSub qgs Qg.length) :
    ∃ i < (gtBFS Qg.toArray cap).pts.size, MRep (gtBFS Qg.toArray cap).pts[i]! y := by
  obtain ⟨f, hf, -, heq⟩ := prodTree_closure_eq valHom valHom_injective (qCheck_parts h).1 qgs
    (qRep_arr hQ)
  rw [qSub_eq] at hy
  have hy' : y ∈ ((Subgroup.closure (qgs '' {l | l < Qg.toArray.size}) : Subgroup GL24) :
      Set GL24) := hy
  rw [heq] at hy'
  obtain ⟨i, hi, rfl⟩ := hy'
  exact ⟨i, hi, (hf i hi).symm⟩

end CFSG.EvenSporadicStandard.Solomon78
