module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K57StepB
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15Vocab
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.FiveThreeAlt.A6Clause
public import CFSG.Monster.B.TwoA.Census.PermClasses

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.RankThree.FFModules
open CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I542
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.McLaughlin.FiveThreeAlt
open scoped commutatorElement

section Linear

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W]

theorem le_of_sub_mem {ρ : G →* Module.End (ZMod 2) W} {z : G} (hz : z ^ 3 = 1)
    {P P' : Submodule (ZMod 2) W} (hP' : P' ≤ LinearMap.range (ρ z - 1))
    (hPz : ∀ w ∈ P, ρ z w ∈ P) (hcomm : ∀ w ∈ P', ρ z w - w ∈ P) : P' ≤ P := by
  intro p hp
  obtain ⟨v, hv⟩ := hP' hp
  have hv' : ρ z v - v = p := by simpa using hv
  have h3 : ρ z (ρ z (ρ z v)) = v := by
    have h := congrArg (fun x => ρ x v) (show z * (z * z) = 1 by rw [← pow_three]; exact hz)
    simpa [map_mul] using h
  have hs : p + ρ z p + ρ z (ρ z p) = 0 := by
    rw [← hv']
    simp only [map_sub, h3]
    abel
  obtain ⟨q, hqdef⟩ : ∃ q, q = ρ z p - p := ⟨_, rfl⟩
  have hq : q ∈ P := by rw [hqdef]; exact hcomm p hp
  have hzp : ρ z p = p + q := by rw [hqdef]; abel
  have hzzp : ρ z (ρ z p) = p + q + ρ z q := by rw [hzp, map_add, hzp]
  rw [hzzp, hzp] at hs
  have h1 : p + ρ z q = 0 := by
    have e : p + (p + q) + (p + q + ρ z q) = (p + ρ z q) + ((p + p) + (q + q)) := by abel
    rw [e, K57StepB.add_self_eq_zero, K57StepB.add_self_eq_zero, add_zero, add_zero] at hs
    exact hs
  have h2 : p = ρ z q := by
    calc p = (p + ρ z q) + ρ z q := by rw [add_assoc, K57StepB.add_self_eq_zero, add_zero]
      _ = ρ z q := by rw [h1, zero_add]
  rw [h2]
  exact hPz q hq

theorem isInv_range_of_commute (ρ : G →* Module.End (ZMod 2) W) {z : G} (S : Subgroup G)
    (hS : ∀ s ∈ S, s * z = z * s) : K57StepB.IsInv ρ S (LinearMap.range (ρ z - 1)) := by
  rintro s hs _ ⟨v, rfl⟩
  refine ⟨ρ s v, ?_⟩
  have h := K57StepB.apply_comm ρ (hS s hs) v
  simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
  rw [h]

end Linear

section Dictionary

variable {X : Type} [Group X] {T : Subgroup X} (hV : IsElemAbelian 2 (gnV T))
  [Module (ZMod 2) (Additive (IntMod (gnV T) hV))]

theorem comap_le_normalizer_subOf {Ls : Subgroup (X ⧸ gnC T)}
    {P : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))}
    (hP : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) Ls P) :
    Ls.comap (toStar T) ≤ Subgroup.normalizer (subOf hV P : Set X) := by
  have fwd : ∀ g ∈ Ls.comap (toStar T), ∀ y ∈ subOf hV P, g * y * g⁻¹ ∈ subOf hV P := by
    intro g hg y hy
    obtain ⟨w, hw, rfl⟩ := hy
    exact ⟨gnRep hV (QuotientGroup.mk g) w, hP _ hg w hw, elt_gnRep hV g w⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => fwd g hg h hh, fun hh => ?_⟩
  have := fwd g⁻¹ (Subgroup.inv_mem _ hg) _ hh
  simpa [mul_assoc] using this

theorem sub_mem_of_commutator_le {Ls : Subgroup (X ⧸ gnC T)} {z : X ⧸ gnC T} (hz : z ∈ Ls)
    {P P' : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))}
    (h : ⁅subOf hV P', Ls.comap (toStar T)⁆ ≤ subOf hV P) :
    ∀ w ∈ P', gnRep hV z w - w ∈ P := by
  intro w hw
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective z
  have hc := h (Subgroup.commutator_mem_commutator
    (show elt hV w ∈ subOf hV P' from ⟨w, hw, rfl⟩) (show g ∈ Ls.comap (toStar T) from hz))
  rw [commutatorElement_def] at hc
  refine (elt_mem_subOf hV).mp ?_
  rw [elt_sub, elt_gnRep]
  have e : g * elt hV w * g⁻¹ * (elt hV w)⁻¹ = (elt hV w * g * (elt hV w)⁻¹ * g⁻¹)⁻¹ := by
    group
  rw [e]
  exact (subOf hV P).inv_mem hc

theorem noChainThree_range {Ls : Subgroup (X ⧸ gnC T)} {z : X ⧸ gnC T} (hz : z ∈ Ls)
    (hz3 : z ^ 3 = 1)
    (hcount : ∀ P₀ P₁ P₂ P₃ : Subgroup X, P₀ < P₁ → P₁ < P₂ → P₂ < P₃ → P₃ ≤ gnV T →
      Ls.comap (toStar T) ≤ Subgroup.normalizer (P₀ : Set X) →
      Ls.comap (toStar T) ≤ Subgroup.normalizer (P₁ : Set X) →
      Ls.comap (toStar T) ≤ Subgroup.normalizer (P₂ : Set X) →
      Ls.comap (toStar T) ≤ Subgroup.normalizer (P₃ : Set X) →
      ⁅P₁, Ls.comap (toStar T)⁆ ≤ P₀ ∨ ⁅P₂, Ls.comap (toStar T)⁆ ≤ P₁ ∨
        ⁅P₃, Ls.comap (toStar T)⁆ ≤ P₂) :
    K57StepB.NoChainThree (gnRep hV) Ls (LinearMap.range (gnRep hV z - 1)) := by
  intro P₀ P₁ P₂ P₃ h01 h12 h23 h3U i0 i1 i2 i3
  have hlt : ∀ {N N' : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))}, N < N' →
      subOf hV N < subOf hV N' := fun h =>
    lt_of_le_not_ge ((subOf_le_subOf_iff hV).mpr h.le)
      fun h' => h.not_ge ((subOf_le_subOf_iff hV).mp h')
  have hstep : ∀ {N N' : Submodule (ZMod 2) (Additive (IntMod (gnV T) hV))}, N < N' →
      N' ≤ LinearMap.range (gnRep hV z - 1) → CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant (gnRep hV) Ls N →
      ¬ ⁅subOf hV N', Ls.comap (toStar T)⁆ ≤ subOf hV N := by
    intro N N' hlt' hN' hinv hle
    exact hlt'.not_ge (le_of_sub_mem (ρ := gnRep hV) hz3 hN' (hinv z hz)
      (sub_mem_of_commutator_le hV hz hle))
  rcases hcount (subOf hV P₀) (subOf hV P₁) (subOf hV P₂) (subOf hV P₃) (hlt h01) (hlt h12)
      (hlt h23) (subOf_le_gnV hV P₃) (comap_le_normalizer_subOf hV i0)
      (comap_le_normalizer_subOf hV i1) (comap_le_normalizer_subOf hV i2)
      (comap_le_normalizer_subOf hV i3) with h | h | h
  · exact hstep h01 (h12.le.trans (h23.le.trans h3U)) i0 h
  · exact hstep h12 (h23.le.trans h3U) i1 h
  · exact hstep h23 h3U i2 h

end Dictionary

end CFSG.LocalAnalysis.RankThreeUC.S15
