module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeE6ToralCoreKerDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamOutBase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeBoundBase
public import CFSG.LocalAnalysis.StandardType.GGSixBstarE6ThreeFaithful
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S171Basic
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171ShapeFamClRed
public import CFSG.LocalAnalysis.GLTheoremA.S11.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T171Sh

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KE
open CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Lang.E6Descent
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.ComponentClassification.PerfectAutomorphisms CFSG.GroupActions
open scoped Pointwise

theorem e6RecipeConj_pow_three_eq_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K}
    {wd : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)}
    (hd : LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
      (e6RecipeConj wd)) :
    (e6RecipeConj wd) ^ 3 = 1 :=
  largeEvenInduces_pow_eq_one
    ((CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.d_mem)
    hd (hS.elem.2 d hS.d_mem)

theorem e6wd_pow_three_eq_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K}
    {wd : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)}
    (hd : LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
      (e6RecipeConj wd)) :
    wd ^ 3 = 1 := by
  let c : MulAut (adjointGroup Tag.E6 K) ≃*
      MulAut (TableBExc.RecipeGroup Tag.E6 K) :=
    MulAut.congr (TableBExc.recipeEquiv Tag.E6 K).symm
  have hφ3 : (e6RecipeConj wd) ^ 3 = 1 :=
    e6RecipeConj_pow_three_eq_one hS hd
  have hc : c (TableBExc.E6Three.hatAut Tag.E6 K (wd ^ 3)) = 1 := by
    calc c (TableBExc.E6Three.hatAut Tag.E6 K (wd ^ 3))
        = c ((TableBExc.E6Three.hatAut Tag.E6 K wd) ^ 3) := by rw [map_pow]
      _ = (c (TableBExc.E6Three.hatAut Tag.E6 K wd)) ^ 3 := by rw [map_pow]
      _ = (e6RecipeConj wd) ^ 3 := by rfl
      _ = 1 := hφ3
  have hhat : TableBExc.E6Three.hatAut Tag.E6 K (wd ^ 3) = 1 := by
    apply c.injective
    rw [hc, map_one]
  exact NoOffE6Three.hatAut_injective (by rw [hhat, map_one])

theorem e6wd_ne_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K}
    {wd : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)}
    (hd : LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
      (e6RecipeConj wd)) :
    wd ≠ 1 := by
  intro hwd1
  have hφ1 : e6RecipeConj wd = 1 := by
    rw [hwd1]
    ext x
    simp [e6RecipeConj]
  have hdL : d ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.d_mem
  have hcomm : ∀ l : ↥L, ∃ z ∈ Subgroup.center ↥L,
      d⁻¹ * (l : G) * d = (l : G) * (z : G) := by
    intro l
    have hl'mem : d⁻¹ * (l : G) * d ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hdL) (l : G)).mp l.2
      simpa using this
    let l' : ↥L := ⟨d⁻¹ * (l : G) * d, hl'mem⟩
    have hθeq : θ (QuotientGroup.mk l') = θ (QuotientGroup.mk l) := by
      have h := hd l l' rfl
      rw [hφ1] at h
      simpa using h.symm
    have hker : l'⁻¹ * l ∈ Subgroup.center ↥L :=
      QuotientGroup.eq.mp (θ.injective hθeq)
    refine ⟨(l'⁻¹ * l)⁻¹, Subgroup.inv_mem _ hker, ?_⟩
    show d⁻¹ * (l : G) * d = (l : G) * (((l'⁻¹ * l)⁻¹ : ↥L) : G)
    have hl' : (l' : ↥L) = l * (l'⁻¹ * l)⁻¹ := by group
    rw [show d⁻¹ * (l : G) * d = (l' : G) from rfl]
    simpa using congrArg (fun t : ↥L => (t : G)) hl' 
  have hcent : d ∈ Subgroup.centralizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.centralizes_of_conjRel_center hdL hcomm
      ⟨hS.qs.1⟩
  have hmem : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hcent⟩
  rw [hS.faithful] at hmem
  exact hS.d_ne (Subgroup.mem_bot.mp hmem)

theorem twRecipeConj_injective {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n) :
    Function.Injective (TwE6Transport.recipeConj σ ε :
      ↥(RecipeExcLang.twInndiagGroup K σ) → MulAut (TwE6Delta.RecipeR K n)) := by
  intro x y hxy
  exact NoOffTwE6Three.twConj_injective hn hK σ hσ
    ((MulAut.congr ε).injective hxy)

theorem twRecipeConj_pow_three_eq_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K] {n : ℕ}
    {σ : K ≃+* K} {ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃*
      TwE6Delta.RecipeR K n}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n}
    {wd : ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hd : LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
      (TwE6Transport.recipeConj σ ε wd)) :
    (TwE6Transport.recipeConj σ ε wd) ^ 3 = 1 :=
  largeEvenInduces_pow_eq_one
    ((CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.d_mem)
    hd (hS.elem.2 d hS.d_mem)

theorem twwd_pow_three_eq_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n}
    {wd : ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hd : LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
      (TwE6Transport.recipeConj σ ε wd)) :
    wd ^ 3 = 1 := by
  have hφ3 : (TwE6Transport.recipeConj σ ε wd) ^ 3 = 1 :=
    twRecipeConj_pow_three_eq_one hS hd
  have h1 : TwE6Transport.recipeConj σ ε (wd ^ 3) = 1 := by
    rw [map_pow, hφ3]
  exact twRecipeConj_injective hn hK σ hσ ε (by rw [h1, map_one])

theorem twwd_ne_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K] {n : ℕ}
    {σ : K ≃+* K} {ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃*
      TwE6Delta.RecipeR K n}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n}
    {wd : ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hd : LargeEvenInduces θ (fun l l' => (l' : G) = d⁻¹ * l * d)
      (TwE6Transport.recipeConj σ ε wd)) :
    wd ≠ 1 := by
  intro hwd1
  have hφ1 : TwE6Transport.recipeConj σ ε wd = 1 := by
    rw [hwd1]
    exact map_one _
  have hdL : d ∈ Subgroup.normalizer (L : Set G) :=
    (CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag) hS.d_mem
  have hcomm : ∀ l : ↥L, ∃ z ∈ Subgroup.center ↥L,
      d⁻¹ * (l : G) * d = (l : G) * (z : G) := by
    intro l
    have hl'mem : d⁻¹ * (l : G) * d ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hdL) (l : G)).mp l.2
      simpa using this
    let l' : ↥L := ⟨d⁻¹ * (l : G) * d, hl'mem⟩
    have hθeq : θ (QuotientGroup.mk l') = θ (QuotientGroup.mk l) := by
      have h := hd l l' rfl
      rw [hφ1] at h
      simpa using h.symm
    have hker : l'⁻¹ * l ∈ Subgroup.center ↥L :=
      QuotientGroup.eq.mp (θ.injective hθeq)
    refine ⟨(l'⁻¹ * l)⁻¹, Subgroup.inv_mem _ hker, ?_⟩
    show d⁻¹ * (l : G) * d = (l : G) * (((l'⁻¹ * l)⁻¹ : ↥L) : G)
    have hl' : (l' : ↥L) = l * (l'⁻¹ * l)⁻¹ := by group
    rw [show d⁻¹ * (l : G) * d = (l' : G) from rfl]
    simpa using congrArg (fun t : ↥L => (t : G)) hl' 
  have hcent : d ∈ Subgroup.centralizer (L : Set G) :=
    CFSG.LocalAnalysis.GLTheoremA.T171Sh.centralizes_of_conjRel_center hdL hcomm
      ⟨hS.qs.1⟩
  have hmem : d ∈ A ⊓ Subgroup.centralizer (L : Set G) := ⟨hS.d_mem, hcent⟩
  rw [hS.faithful] at hmem
  exact hS.d_ne (Subgroup.mem_bot.mp hmem)

theorem e6RecipeConj_pow_three_eq_one_of {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K}
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgpow : g ^ 3 = 1)
    {φ : MulAut (TableBExc.RecipeGroup Tag.E6 K)}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = g⁻¹ * l * g) φ) :
    φ ^ 3 = 1 :=
  largeEvenInduces_pow_eq_one hg h hgpow

theorem e6_hatAut_pow_three {K : Type} [Field K] [Finite K]
    {wd : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)}
    (hφ3 : (e6RecipeConj wd) ^ 3 = 1) : wd ^ 3 = 1 := by
  let c : MulAut (adjointGroup Tag.E6 K) ≃*
      MulAut (TableBExc.RecipeGroup Tag.E6 K) :=
    MulAut.congr (TableBExc.recipeEquiv Tag.E6 K).symm
  have hc : c (TableBExc.E6Three.hatAut Tag.E6 K (wd ^ 3)) = 1 := by
    calc c (TableBExc.E6Three.hatAut Tag.E6 K (wd ^ 3))
        = c ((TableBExc.E6Three.hatAut Tag.E6 K wd) ^ 3) := by rw [map_pow]
      _ = (c (TableBExc.E6Three.hatAut Tag.E6 K wd)) ^ 3 := by rw [map_pow]
      _ = (e6RecipeConj wd) ^ 3 := by rfl
      _ = 1 := hφ3
  have hhat : TableBExc.E6Three.hatAut Tag.E6 K (wd ^ 3) = 1 := by
    apply c.injective
    rw [hc, map_one]
  exact NoOffE6Three.hatAut_injective (by rw [hhat, map_one])

theorem e6wb_pow_three_eq_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K]
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TableBExc.RecipeGroup Tag.E6 K}
    {wb : ↥(TableBExc.E6Three.hatGroup Tag.E6 K)}
    (hb : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
      (e6RecipeConj wb)) :
    wb ^ 3 = 1 :=
  e6_hatAut_pow_three
    (e6RecipeConj_pow_three_eq_one_of hS
      ((CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag)
        hS.b_mem) (hS.elem.2 b hS.b_mem) hb)

theorem twRecipeConj_pow_three_eq_one_of {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K] {n : ℕ}
    {σ : K ≃+* K} {ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃*
      TwE6Delta.RecipeR K n}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n}
    {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G)) (hgpow : g ^ 3 = 1)
    {φ : MulAut (TwE6Delta.RecipeR K n)}
    (h : LargeEvenInduces θ (fun l l' => (l' : G) = g⁻¹ * l * g) φ) :
    φ ^ 3 = 1 :=
  largeEvenInduces_pow_eq_one hg h hgpow

theorem tw_recipeConj_pow_three {K : Type} [Field K] [Finite K] {n : ℕ}
    (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n}
    {wd : ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hφ3 : (TwE6Transport.recipeConj σ ε wd) ^ 3 = 1) : wd ^ 3 = 1 := by
  have h1 : TwE6Transport.recipeConj σ ε (wd ^ 3) = 1 := by
    rw [map_pow, hφ3]
  exact twRecipeConj_injective hn hK σ hσ ε (by rw [h1, map_one])

theorem twwb_pow_three_eq_one {G : Type} [Group G] [Finite G]
    {L J A : Subgroup G} {d b : G} (hS : Setup 3 L J A d b)
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ 2 ^ n)
    {ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n}
    {θ : ↥L ⧸ Subgroup.center ↥L ≃* TwE6Delta.RecipeR K n}
    {wb : ↥(RecipeExcLang.twInndiagGroup K σ)}
    (hb : LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b)
      (TwE6Transport.recipeConj σ ε wb)) :
    wb ^ 3 = 1 :=
  tw_recipeConj_pow_three (K := K) (n := n) (σ := σ) (ε := ε) (wd := wb)
    hn hK hσ
    (twRecipeConj_pow_three_eq_one_of (σ := σ) (ε := ε) hS
      ((CFSG.LocalAnalysis.GLTheoremA.S171.normalizer_of_innerDiagMarking hS.idiag)
        hS.b_mem) (hS.elem.2 b hS.b_mem) hb)

end CFSG.LocalAnalysis.GLTheoremA.T171Sh

end
