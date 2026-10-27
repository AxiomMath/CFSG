module

public import CFSG.LieType.Chevalley.LangRootRankOne
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartOne.CTP.SeitzField
public import CFSG.RankThree.PartOne.CTP.SeitzU5Eigen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.CTP
  CFSG.HardMathSupport.Lang.D4Three

section Abstract

variable {G : Type*} [Group G]

@[expose] def PairGenAt (α : MulAut G) : Prop :=
  ∀ x : G, x ^ 3 = 1 → x ≠ 1 → α x = x →
    Subgroup.closure ((Subgroup.centralizer ({x} : Set G) : Set G) ∪ (fixedSubgroup α : Set G)) = ⊤

theorem eq_top_of_closure_image (ψ : MulAut G) {S T : Set G} (hS : Subgroup.closure S = ⊤)
    (hST : ψ '' S ⊆ T) : Subgroup.closure T = ⊤ := by
  have h1 : (Subgroup.closure S).map ψ.toMonoidHom = ⊤ := by
    rw [hS]
    exact Subgroup.map_top_of_surjective _ ψ.surjective
  rw [MonoidHom.map_closure] at h1
  rw [eq_top_iff, ← h1]
  exact Subgroup.closure_mono hST

theorem pairGenAt_conj (ψ : MulAut G) {α : MulAut G} (h : PairGenAt α) :
    PairGenAt (ψ * α * ψ⁻¹) := by
  intro x hx3 hx1 hαx
  have hx' : α (ψ⁻¹ x) = ψ⁻¹ x := by
    have e : ψ (α (ψ⁻¹ x)) = x := hαx
    have e' := congrArg (fun y => ψ⁻¹ y) e
    simp only [MulAut.inv_apply_self G ψ] at e'
    exact e'
  have h3 : (ψ⁻¹ x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  have h1 : ψ⁻¹ x ≠ 1 := fun h0 => hx1 (by rw [← MulAut.apply_inv_self G ψ x, h0, map_one])
  refine eq_top_of_closure_image ψ (h _ h3 h1 hx') ?_
  rintro _ ⟨g, hg | hg, rfl⟩
  · left
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg ⊢
    have := congrArg ψ hg
    rwa [map_mul, map_mul, MulAut.apply_inv_self G ψ x] at this
  · right
    show ψ (α (ψ⁻¹ (ψ g))) = ψ g
    rw [MulAut.inv_apply_self G ψ g]
    exact congrArg ψ hg

theorem pairGenAt_congr {α β : MulAut G} (hαβ : fixedSubgroup α = fixedSubgroup β)
    (h : PairGenAt α) : PairGenAt β := by
  intro x hx3 hx1 hβx
  have hαx : α x = x := (SetLike.ext_iff.1 hαβ x).2 hβx
  rw [← hαβ]
  exact h x hx3 hx1 hαx

theorem fixedSubgroup_inv (α : MulAut G) : fixedSubgroup α⁻¹ = fixedSubgroup α := by
  ext g
  rw [mem_fixedSubgroup, mem_fixedSubgroup]
  constructor
  · intro h
    have e := congrArg α h
    rw [MulAut.apply_inv_self G α g] at e
    exact e.symm
  · intro h
    have e := congrArg (fun y => α⁻¹ y) h
    simp only [MulAut.inv_apply_self G α g] at e
    exact e.symm

theorem pairGenAt_inv {α : MulAut G} (h : PairGenAt α) : PairGenAt α⁻¹ :=
  pairGenAt_congr (fixedSubgroup_inv α).symm h

theorem closure_eq_top_of_conj {α : MulAut G} {x h : G} (hh : α h = h)
    (htop : Subgroup.closure ((Subgroup.centralizer ({h * x * h⁻¹} : Set G) : Set G) ∪
      (fixedSubgroup α : Set G)) = ⊤) :
    Subgroup.closure ((Subgroup.centralizer ({x} : Set G) : Set G) ∪
      (fixedSubgroup α : Set G)) = ⊤ := by
  set M := Subgroup.closure ((Subgroup.centralizer ({x} : Set G) : Set G) ∪
    (fixedSubgroup α : Set G)) with hM
  have hhM : h ∈ M := Subgroup.subset_closure (Or.inr hh)
  rw [eq_top_iff, ← htop, Subgroup.closure_le]
  rintro g (hg | hg)
  · rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
    have hg' : h⁻¹ * g * h ∈ Subgroup.centralizer ({x} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e : h⁻¹ * g * h * x = h⁻¹ * (g * (h * x * h⁻¹)) * h := by group
      have e' : x * (h⁻¹ * g * h) = h⁻¹ * ((h * x * h⁻¹) * g) * h := by group
      rw [e, e', hg]
    have hgM : h⁻¹ * g * h ∈ M := Subgroup.subset_closure (Or.inl hg')
    have : g = h * (h⁻¹ * g * h) * h⁻¹ := by group
    rw [SetLike.mem_coe, this]
    exact M.mul_mem (M.mul_mem hhM hgM) (M.inv_mem hhM)
  · exact Subgroup.subset_closure (Or.inr hg)

end Abstract

section D4


variable (K : Type) [Field K]

@[expose] noncomputable def sl2At (i : Fin Tag.D4.rank) : SL2 K →* ↥(adjointGroup Tag.D4 K) :=
  (simpleRootSL2 Tag.D4 K i).codRestrict (adjointGroup Tag.D4 K)
    (simpleRootSL2_mem_adjointGroup i)

variable {K}

theorem coe_sl2At (i : Fin Tag.D4.rank) (A : SL2 K) :
    (sl2At K i A : ModGL Tag.D4 K) = simpleRootSL2 Tag.D4 K i A :=
  rfl

variable (K)

@[expose] noncomputable def gammaP (B : SL2 K) : MulAut ↥(adjointGroup Tag.D4 K) :=
  MulAut.conj (sl2At K ⟨2, by decide⟩ B) * d4Graph K 1

variable {K}

@[expose] def IsG2Type (α : MulAut ↥(adjointGroup Tag.D4 K)) : Prop :=
  ∃ ψ : MulAut ↥(adjointGroup Tag.D4 K), ψ * α * ψ⁻¹ = d4Graph K 1 ∨ ψ * α * ψ⁻¹ = d4Graph K 2

@[expose] def IsA2Type (α : MulAut ↥(adjointGroup Tag.D4 K)) : Prop :=
  ∃ (ψ : MulAut ↥(adjointGroup Tag.D4 K)) (B : SL2 K), B ^ 3 = 1 ∧ B ≠ 1 ∧
    (ψ * α * ψ⁻¹ = gammaP K B ∨ ψ * α * ψ⁻¹ = (gammaP K B)⁻¹)

theorem pairGenAt_of_conj_eq {α β : MulAut ↥(adjointGroup Tag.D4 K)}
    (ψ : MulAut ↥(adjointGroup Tag.D4 K)) (hβ : PairGenAt β)
    (h : ψ * α * ψ⁻¹ = β ∨ ψ * α * ψ⁻¹ = β⁻¹) : PairGenAt α := by
  have hβ' : PairGenAt (ψ * α * ψ⁻¹) := by
    rcases h with h | h
    · rwa [h]
    · rw [h]
      exact pairGenAt_inv hβ
  have := pairGenAt_conj ψ⁻¹ hβ'
  rwa [show ψ⁻¹ * (ψ * α * ψ⁻¹) * ψ⁻¹⁻¹ = α by group] at this

end D4

end CFSG.LieType.SeitzGeneration.ExcWideThree.Parrott.D4Graph
