module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IBorel
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3IFix
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3FStable
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.LangNormalizerInvolutionTorus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinInteraction
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6OrderThreeTools
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.Lattice.SteinbergBIPoly

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.HardMathSupport.Lang.D4Three
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

section Main

variable {K : Type} [Field K] [Finite K]


theorem layerAct_f_ne_zero {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) (k : ℕ) (δ : UnitRoots Tag.D4 k) : la.f k δ ≠ 0 := by
  classical
  have hmap : (unitN Tag.D4 K k).map α.toMonoidHom = unitN Tag.D4 K k := by
    have hle : (unitN Tag.D4 K k).map α.toMonoidHom ≤ unitN Tag.D4 K k := by
      rintro _ ⟨x, hx, rfl⟩
      exact la.stable k x hx
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Subgroup.card_map_of_injective α.injective]
  have hpos := UnitRoots.pos Tag.D4 δ
  set y : ↥(adjointGroup Tag.D4 K) := ⟨pinnedX Tag.D4 K δ.1 1, pinnedX_mem_adjointGroup δ.1 1⟩ with hy
  have hyN : y ∈ unitN Tag.D4 K k := by
    rw [mem_unitN]
    have := pinnedX_mem_heightSeries_height (K := K) hpos 1
    rw [δ.2.2] at this
    exact this
  rw [← hmap] at hyN
  obtain ⟨x, hx, hαx⟩ := Subgroup.mem_map.1 hyN
  have h := la.coord k δ x hx
  have hαx' : ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) = pinnedX Tag.D4 K δ.1 1 := by
    have : α x = y := hαx
    rw [this]
  rw [hαx', rootCoord_self hpos] at h
  intro hf
  rw [hf, zero_mul] at h
  exact one_ne_zero h

theorem sign_perm_invariant {α : MulAut ↥(adjointGroup Tag.D4 K)} {σ : K ≃+* K}
    (la : LayerAct Tag.D4 α σ) {g : ↥(adjointGroup Tag.D4 K)}
    (hs : BorelScalar (g : ModGL Tag.D4 K)) (hαg : α g = g) (k : ℕ) (δ : UnitRoots Tag.D4 k) :
    σ (hs.s (la.r k δ).1) = hs.s δ.1 := by
  classical
  have hpos := UnitRoots.pos Tag.D4 δ
  have hpos' := UnitRoots.pos Tag.D4 (la.r k δ)
  have hh : height (la.r k δ).1 = ((k + 1 : ℕ) : ℤ) := (la.r k δ).2.2
  have hhδ : height δ.1 = ((k + 1 : ℕ) : ℤ) := δ.2.2
  set x : ↥(adjointGroup Tag.D4 K) :=
    ⟨pinnedX Tag.D4 K (la.r k δ).1 1, pinnedX_mem_adjointGroup (la.r k δ).1 1⟩ with hx
  have hxN : x ∈ unitN Tag.D4 K k := by
    rw [mem_unitN]
    have := pinnedX_mem_heightSeries_height (K := K) hpos' 1
    rw [hh] at this
    exact this
  have hxm : (x : ModGL Tag.D4 K) ∈ heightSeries Tag.D4 K (height (la.r k δ).1) := by
    rw [hh]; exact hxN
  have hzm : (g : ModGL Tag.D4 K) * (x : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K)⁻¹ ∈
      heightSeries Tag.D4 K (height (la.r k δ).1) :=
    (Subgroup.mem_normalizer_iff.1 (hs.1 _) _).1 hxm
  set z : ↥(adjointGroup Tag.D4 K) := g * x * g⁻¹ with hz
  have hzN : z ∈ unitN Tag.D4 K k := by
    rw [mem_unitN]
    rw [hh] at hzm
    exact hzm
  have h1 := la.coord k δ z hzN
  have hzc : rootCoord hpos' (z : ModGL Tag.D4 K) = hs.s (la.r k δ).1 := by
    have : (z : ModGL Tag.D4 K) = (g : ModGL Tag.D4 K) * (x : ModGL Tag.D4 K) * (g : ModGL Tag.D4 K)⁻¹ := rfl
    rw [this, hs.spec.2 _ hpos' _ hxm]
    change hs.s (la.r k δ).1 * rootCoord hpos' (pinnedX Tag.D4 K (la.r k δ).1 1) = _
    rw [rootCoord_self hpos', mul_one]
  have hαz : α z = g * α x * g⁻¹ := by
    rw [hz, map_mul, map_mul, map_inv, hαg]
  have hαxN : α x ∈ unitN Tag.D4 K k := la.stable k x hxN
  have hαxm : ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) ∈
      heightSeries Tag.D4 K (height δ.1) := by
    rw [hhδ]; exact hαxN
  have h2 : rootCoord hpos ((α z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
      hs.s δ.1 * (la.f k δ * σ 1) := by
    have : ((α z : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) =
        (g : ModGL Tag.D4 K) * ((α x : ↥(adjointGroup Tag.D4 K)) : ModGL Tag.D4 K) *
          (g : ModGL Tag.D4 K)⁻¹ := by rw [hαz]; rfl
    rw [this, hs.spec.2 _ hpos _ hαxm, la.coord k δ x hxN]
    have : rootCoord hpos' (x : ModGL Tag.D4 K) = 1 := rootCoord_self hpos' 1
    rw [this]
  rw [h1, hzc] at h2
  rw [map_one, mul_one] at h2
  have hf := layerAct_f_ne_zero la k δ
  have : la.f k δ * (σ (hs.s (la.r k δ).1) - hs.s δ.1) = 0 := by linear_combination h2
  exact sub_eq_zero.1 ((mul_eq_zero.1 this).resolve_left hf)

theorem sum_layer_filter_card_le (P : D4Vec → Prop) [DecidablePred P] (d : ℕ)
    (T : ∀ k, Finset (UnitRoots Tag.D4 k)) (hT : ∀ k, ∀ δ ∈ T k, P δ.1) :
    ∑ k ∈ Finset.range d, (T k).card ≤ ((d4RootsFrom 1).filter P).card := by
  classical
  rw [← Finset.card_sigma]
  refine Finset.card_le_card_of_injOn (fun p => p.2.1) ?_ ?_
  · intro p hp
    obtain ⟨hk, hδ⟩ := Finset.mem_sigma.1 hp
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨mem_d4RootsFrom.2 ⟨p.2.2.1, ?_, ?_⟩, hT _ _ hδ⟩
    · rw [p.2.2.2]; positivity
    · rw [p.2.2.2]; exact_mod_cast Nat.succ_le_succ (Nat.zero_le _)
  · intro p hp q hq hpq
    obtain ⟨hk1, -⟩ := Finset.mem_sigma.1 hp
    obtain ⟨hk2, -⟩ := Finset.mem_sigma.1 hq
    have hh : p.1 = q.1 := by
      have e1 := p.2.2.2
      have e2 := q.2.2.2
      have : ((p.1 + 1 : ℕ) : ℤ) = ((q.1 + 1 : ℕ) : ℤ) := by
        rw [← e1, ← e2]; exact congrArg height hpq
      omega
    obtain ⟨p1, p2⟩ := p
    obtain ⟨q1, q2⟩ := q
    simp only at hh
    subst hh
    have : p2 = q2 := Subtype.ext hpq
    rw [this]

end Main

end CFSG.LocalAnalysis.GLTheoremA
