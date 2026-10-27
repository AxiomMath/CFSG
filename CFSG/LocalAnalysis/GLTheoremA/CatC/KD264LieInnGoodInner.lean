module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264LieInnGood
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Lie

open CFSG.Open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def PerfectCentralizerPlanes (p : ℕ) (S : Type) [Group S] : Prop :=
  ∀ E : Subgroup S, IsElemAbelian p E → Nat.card E = p ^ 2 → ∃ x ∈ E, x ≠ 1 ∧
    ∃ P : Subgroup S, P ≤ Subgroup.centralizer ({x} : Set S) ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P

theorem PerfectCentralizerPlanes.of_mulEquiv {p : ℕ} {S S' : Type} [Group S] [Group S']
    (e : S ≃* S') (h : PerfectCentralizerPlanes p S) : PerfectCentralizerPlanes p S' := by
  intro E' hE' hcard'
  let c : S →* S' := e
  let E : Subgroup S := E'.comap c
  have hc : Function.Injective c := fun _ _ h => e.injective h
  have hE : IsElemAbelian p E := hE'.comap hc
  have hmap : E.map c = E' := Subgroup.map_comap_eq_self_of_surjective e.surjective E'
  have hcard : Nat.card E = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hc, hmap, hcard']
  obtain ⟨x, hxE, hx1, P, hPcent, hPperf, hPdvd⟩ := h E hE hcard
  refine ⟨e x, ?_, fun h1 => hx1 (e.injective (h1.trans (map_one e).symm)),
    P.map c, ?_, ?_, ?_⟩
  · rw [← hmap]
    exact Subgroup.mem_map_of_mem c hxE
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e y * e x = e x * e y
    simpa only [map_mul] using
      congrArg e (Subgroup.mem_centralizer_singleton_iff.1 (hPcent hy))
  · rw [← Subgroup.map_commutator, hPperf]
  · rw [Subgroup.card_map_of_injective hc]
    exact hPdvd

theorem exists_good_of_le_inner {p : ℕ} {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    (h : PerfectCentralizerPlanes p S) {D : Subgroup (MulAut S)} (hD : IsElemAbelian p D)
    (hcard : Nat.card D = p ^ 2) (hDi : D ≤ inner S) :
    ∃ β ∈ D, β ≠ 1 ∧ ∃ P : Subgroup S, P ≤ fixSubgroup β ∧ ⁅P, P⁆ = P ∧ p ∣ Nat.card P := by
  let c : S →* MulAut S := MulAut.conj
  have hc : Function.Injective c := CFSG.mulAutConj_injective_of_center_eq_bot hZ
  let E : Subgroup S := D.comap c
  have hE : IsElemAbelian p E := hD.comap hc
  have hmap : E.map c = D := Subgroup.map_comap_eq_self hDi
  have hcardE : Nat.card E = p ^ 2 := by
    rw [← hcard, ← hmap, Subgroup.card_map_of_injective hc]
  obtain ⟨x, hxE, hx1, P, hPcent, hPperf, hPdvd⟩ := h E hE hcardE
  refine ⟨c x, ?_, fun h1 => hx1 (hc (h1.trans (map_one c).symm)), P, ?_, hPperf, hPdvd⟩
  · rw [← hmap]
    exact Subgroup.mem_map_of_mem c hxE
  · intro y hy
    rw [mem_fixSubgroup, MulAut.conj_apply]
    have hcomm := Subgroup.mem_centralizer_singleton_iff.1 (hPcent hy)
    rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]

theorem innGoodAt_of_inner_planes {p : ℕ} {S : Type} [Group S] (hZ : Subgroup.center S = ⊥)
    (hinner : ∀ β ∈ innAutDerived S, β ^ p = 1 → β ∈ inner S)
    (h : PerfectCentralizerPlanes p S) (d : TauCeti.LieTypeIndex) : InnGoodAt p d S := by
  intro D hD hcard hDle
  left
  refine exists_good_of_le_inner hZ h hD hcard fun β hβ => hinner β (hDle hβ) (hD.2 β hβ)

end CFSG.LocalAnalysis.GLTheoremA.KD264Lie

end
