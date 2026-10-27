module

public import CFSG.Sporadic.Co1Patterson.Generation
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogG2EvenInvolutions
public import CFSG.GroupTheory.ABGLocalTools.PStabilityDefs
public import CFSG.LargeExtraspecial.GLRElimInv
public import CFSG.LargeExtraspecial.GLRTransfer
public import CFSG.LargeExtraspecial.OrthoF2
public import CFSG.LargeExtraspecial.S12FourteenB
public import CFSG.LargeExtraspecial.S14C10Apply
public import CFSG.LargeExtraspecial.S14W4LocInst
public import CFSG.LargeExtraspecial.S14W4LocRed
public import CFSG.LargeExtraspecial.S4EightA
public import CFSG.LargeExtraspecial.S4EightB
public import CFSG.LargeExtraspecial.S4EightC
public import CFSG.LargeExtraspecial.S4EightD
public import CFSG.LargeExtraspecial.S4EightE
public import CFSG.LargeExtraspecial.S4EightMain
public import CFSG.LargeExtraspecial.S4SevenB3
public import CFSG.LargeExtraspecial.S5Three
public import CFSG.LargeExtraspecial.S6SevenC
public import CFSG.LargeExtraspecial.S8FusE
public import CFSG.LargeExtraspecial.S8Lin
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataModelWitness
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearDataCompatibility
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherEvenOrthogonalModel
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureDatum
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Open.QuasithinDefs
public import CFSG.Sporadic.Co1Block.TwoBCent
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore
public import Certificates.Certificate43
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.HoltFree

open Subgroup CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.ComponentClassification.UnbalancedCatalog CFSG.LargeExtraspecial.S14
open CFSG.Blueprint (NativeSporadic.Co1)
open CFSG.Sporadic (Co1Patterson.isConj_of_isConj_of_mem Co1Patterson.exists_involution_classes
  Co1Block.card_centralizer_equiv)

@[expose] def Co1TwoBData (X : Type)
    [Group X] [Finite X] (t : X) : Prop :=
  ∃ A : Subgroup X, 13 ∣ Nat.card A ∧
    (∃ (K : Type) (_ : Field K) (_ : CharP K 2) (f : ↥(adjointGroup .G2 K) →* X),
      f.range = A ∧ ∃ g : ↥(adjointGroup .G2 K), f g = t ∧
        G2Conj (g : ModGL .G2 K) (pinnedX .G2 K g2c 1)) ∧
    (∀ r ∈ centralizer (A : Set X), orderOf r = 2 →
      centralizer ({r} : Set X) ≤ normalizer (A : Set X)) ∧
    Even (Nat.card (centralizer (A : Set X)))

section Group

variable {X : Type*} [Group X]

private theorem centralizer_conj_le {Y : Subgroup X} {x y : X} (hy : y ∈ Y)
    (hx : centralizer ({x} : Set X) ≤ Y) : centralizer ({y * x * y⁻¹} : Set X) ≤ Y := by
  intro w hw
  have hw' : y⁻¹ * w * y ∈ centralizer ({x} : Set X) := by
    rw [mem_centralizer_singleton_iff] at hw ⊢
    calc y⁻¹ * w * y * x = y⁻¹ * (w * (y * x * y⁻¹)) * y := by group
      _ = y⁻¹ * (y * x * y⁻¹ * w) * y := by rw [hw]
      _ = x * (y⁻¹ * w * y) := by group
  rw [show w = y * (y⁻¹ * w * y) * y⁻¹ by group]
  exact Y.mul_mem (Y.mul_mem hy (hx hw')) (Y.inv_mem hy)

private theorem card_centralizer_of_isConj {a b : X} (hab : IsConj a b) :
    Nat.card (centralizer ({a} : Set X)) = Nat.card (centralizer ({b} : Set X)) := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hab
  exact Co1Block.card_centralizer_equiv (MulAut.conj c) a

private theorem card_centralizer_subtype {Y : Subgroup X} (y : Y) :
    Nat.card (centralizer ({y} : Set Y)) = Nat.card ↥(Y ⊓ centralizer ({(y : X)} : Set X)) :=
  Nat.card_congr
    { toFun := fun w => ⟨w.1, mem_inf.2 ⟨w.1.2, mem_centralizer_singleton_iff.2
        (congrArg Subtype.val (mem_centralizer_singleton_iff.1 w.2))⟩⟩
      invFun := fun w => ⟨⟨w.1, (mem_inf.1 w.2).1⟩, mem_centralizer_singleton_iff.2
        (Subtype.ext (mem_centralizer_singleton_iff.1 (mem_inf.1 w.2).2))⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

end Group

private theorem reflect_g2ia_g2a : reflect .G2 g2ia g2a = -g2a :=
  List.ofFn_injective (by decide +kernel)

section G2

variable {K : Type} [Field K] [CharP K 2]

private theorem g2_commute_nr_c (s : K) :
    Commute (pinnedX .G2 K g2nr s) (pinnedX .G2 K g2c 1) := by
  have h := (commute_r_c s (1 : K)).map (MulAut.conj (weylElt .G2 K g2ir 1))
  rwa [MulAut.conj_apply, MulAut.conj_apply, weylElt_conj g2ir isRoot_g2r,
    weylElt_conj g2ir isRoot_g2c, reflect_r_r, reflect_r_c] at h

private theorem g2_commute_na_b (s : K) :
    Commute (pinnedX .G2 K (-g2a) s) (pinnedX .G2 K g2b 1) := by
  have h := (commute_a_c s (1 : K)).map (MulAut.conj (weylElt .G2 K g2ia 1))
  rwa [MulAut.conj_apply, MulAut.conj_apply, weylElt_conj g2ia isRoot_g2a,
    weylElt_conj g2ia isRoot_g2c, reflect_g2ia_g2a, reflect_a_c] at h

private theorem g2_commute_xUnit (i : Fin Tag.G2.rank) (s : K) :
    Commute (xUnit .G2 K i s) (pinnedX .G2 K g2c 1) := by
  rw [← pinnedX_single]
  rcases (by decide : ∀ i : Fin Tag.G2.rank, i = g2ia ∨ i = g2ir) i with rfl | rfl
  · rw [show (Pi.single g2ia 1 : Fin Tag.G2.rank → ℤ) = g2a by decide]
    exact commute_a_c s 1
  · rw [show (Pi.single g2ir 1 : Fin Tag.G2.rank → ℤ) = g2r by decide]
    exact commute_r_c s 1

private theorem g2_commute_yUnit (i : Fin Tag.G2.rank) (s : K) :
    Commute (yUnit .G2 K i s) (pinnedX .G2 K g2c 1) ∨
      Commute (yUnit .G2 K i s) (pinnedX .G2 K g2b 1) := by
  rw [← pinnedX_neg_single]
  rcases (by decide : ∀ i : Fin Tag.G2.rank, i = g2ia ∨ i = g2ir) i with rfl | rfl
  · rw [show (-Pi.single g2ia 1 : Fin Tag.G2.rank → ℤ) = -g2a by decide]
    exact Or.inr (g2_commute_na_b s)
  · rw [show (-Pi.single g2ir 1 : Fin Tag.G2.rank → ℤ) = g2nr by decide]
    exact Or.inl (g2_commute_nr_c s)

theorem g2_range_le_of_commute {Γ : Type*} [Group Γ] (φ : ↥(adjointGroup .G2 K) →* Γ)
    {Y : Subgroup Γ}
    (hc : ∀ g : ↥(adjointGroup .G2 K), Commute (g : ModGL .G2 K) (pinnedX .G2 K g2c 1) →
      φ g ∈ Y)
    (hb : ∀ g : ↥(adjointGroup .G2 K), Commute (g : ModGL .G2 K) (pinnedX .G2 K g2b 1) →
      φ g ∈ Y) :
    φ.range ≤ Y := by
  have hle : adjointGroup .G2 K ≤ (Y.comap φ).map (adjointGroup .G2 K).subtype := by
    refine (closure_le _).2 ?_
    rintro g ⟨i, s, hg | hg⟩
    · obtain rfl : g = xUnit .G2 K i s := Units.ext hg
      exact mem_map.2 ⟨⟨_, xUnit_mem_adjointGroup i s⟩, hc _ (g2_commute_xUnit i s), rfl⟩
    · obtain rfl : g = yUnit .G2 K i s := Units.ext hg
      let y : ↥(adjointGroup .G2 K) := ⟨_, yUnit_mem_adjointGroup i s⟩
      exact mem_map.2 ⟨y, (g2_commute_yUnit i s).elim (hc y) (hb y), rfl⟩
  rintro _ ⟨c, rfl⟩
  obtain ⟨c', hc', hcc'⟩ := mem_map.1 (hle c.2)
  obtain rfl : c' = c := Subtype.ext hcc'
  exact hc'

theorem g2_range_le_of_long {Γ : Type*} [Group Γ] (f : ↥(adjointGroup .G2 K) →* Γ)
    {Y : Subgroup Γ} {g : ↥(adjointGroup .G2 K)}
    (hg : G2Conj (g : ModGL .G2 K) (pinnedX .G2 K g2c 1))
    (hY : ∀ t' : Γ, Commute t' (f g) → IsConj (f g) t' → centralizer ({t'} : Set Γ) ≤ Y) :
    f.range ≤ Y := by
  obtain ⟨h, hh, hhg⟩ := hg
  obtain ⟨k, hk, hkb⟩ := G2Conj.b_one (K := K) one_ne_zero
  let c₀ : ↥(adjointGroup .G2 K) := ⟨_, pinnedX_mem_adjointGroup g2c 1⟩
  let b₀ : ↥(adjointGroup .G2 K) := ⟨_, pinnedX_mem_adjointGroup g2b 1⟩
  let φ := f.comp (MulAut.conj (⟨h, hh⟩ : ↥(adjointGroup .G2 K))⁻¹).toMonoidHom
  have hφ : φ c₀ = f g := by
    simp only [φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    congr 1
    refine Subtype.ext ?_
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, c₀]
    rw [← hhg]
    group
  have hcent : ∀ c d : ↥(adjointGroup .G2 K), Commute (c : ModGL .G2 K) (d : ModGL .G2 K) →
      φ c ∈ centralizer ({φ d} : Set Γ) := fun c d hcd =>
    mem_centralizer_singleton_iff.2 (((show Commute c d from Subtype.ext hcd.eq)).map φ).eq
  have hrange : φ.range = f.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top_of_surjective _ (MulEquiv.surjective _),
      ← MonoidHom.range_eq_map]
  rw [← hrange]
  refine g2_range_le_of_commute φ (fun c hc => ?_) (fun c hc => ?_)
  · refine hY (f g) (Commute.refl _) (IsConj.refl _) ?_
    rw [← hφ]
    exact hcent c c₀ hc
  · refine hY (φ b₀) ?_ ?_ (hcent c b₀ hc)
    · rw [← hφ]
      exact (show Commute b₀ c₀ from Subtype.ext (commute_b_c 1 1).eq).map φ
    · rw [← hφ]
      refine φ.map_isConj (isConj_iff.2 ⟨⟨k, hk⟩⁻¹, Subtype.ext ?_⟩)
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, c₀, b₀]
      rw [← hkb]
      group

end G2

section Co1


variable {X : Type} [Group X] [Finite X] {t : X}

theorem co1_centralizer_le (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y) {x : X} (hx : x ∈ Y)
    (hcx : IsConj t x) : centralizer ({x} : Set X) ≤ Y := by
  have htY : t ∈ Y := hCY (mem_centralizer_singleton_iff.2 rfl)
  obtain ⟨y, hy⟩ := isConj_iff.1
    (Co1Patterson.isConj_of_isConj_of_mem h e htY (y := ⟨x, hx⟩) hcx)
  rw [← show (y : X) * t * (y : X)⁻¹ = x from congrArg Subtype.val hy]
  exact centralizer_conj_le y.2 hCY

theorem co1_normalizer_le (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y) {A : Subgroup X}
    (htA : t ∈ A) (hAY : A ≤ Y) : normalizer (A : Set X) ≤ Y := by
  have htY : t ∈ Y := hCY (mem_centralizer_singleton_iff.2 rfl)
  intro n hn
  have h1 : n * t * n⁻¹ ∈ Y := hAY ((mem_normalizer_iff.1 hn t).1 htA)
  obtain ⟨y, hy⟩ := isConj_iff.1 (Co1Patterson.isConj_of_isConj_of_mem h e htY
    (y := ⟨_, h1⟩) (isConj_iff.2 ⟨n, rfl⟩))
  have hy' : (y : X) * t * (y : X)⁻¹ = n * t * n⁻¹ := congrArg Subtype.val hy
  have h2 : (y : X)⁻¹ * n ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc (y : X)⁻¹ * n * t = (y : X)⁻¹ * (n * t * n⁻¹) * n := by group
      _ = (y : X)⁻¹ * ((y : X) * t * (y : X)⁻¹) * n := by rw [hy']
      _ = t * ((y : X)⁻¹ * n) := by group
  rw [show n = y * ((y : X)⁻¹ * n) by group]
  exact Y.mul_mem y.2 (hCY h2)

section TwoB


theorem co1_range_le (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y) {K : Type} [Field K]
    [CharP K 2] (f : ↥(adjointGroup .G2 K) →* X) {g : ↥(adjointGroup .G2 K)} (hgt : f g = t)
    (hg : G2Conj (g : ModGL .G2 K) (pinnedX .G2 K g2c 1)) : f.range ≤ Y :=
  g2_range_le_of_long f hg fun t' h1 h2 => by
    rw [hgt] at h1 h2
    exact co1_centralizer_le h e hCY (hCY (mem_centralizer_singleton_iff.2 h1.eq)) h2

theorem twoB_centralizer_le (h : PattersonCo1Hyp X t) {Y : Subgroup X}
    (e : Y ≃* NativeSporadic.Co1) (hCY : centralizer ({t} : Set X) ≤ Y)
    (hB : Co1TwoBData X t) :
    ∀ r ∈ Y, orderOf r = 2 → Nat.card ↥(Y ⊓ centralizer ({r} : Set X)) = 2012774400 →
      centralizer ({r} : Set X) ≤ Y := by
  obtain ⟨A, h13, ⟨K, _, _, f, hfA, g, hgt, hg⟩, hNA, hev⟩ := hB
  have htA : t ∈ A := by
    rw [← hfA]
    exact ⟨g, hgt⟩
  have hAY : A ≤ Y := hfA ▸ co1_range_le h e hCY f hgt hg
  have hNY := co1_normalizer_le h e hCY htA hAY
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨r₀, hr₀⟩ := exists_prime_orderOf_dvd_card' (G := centralizer (A : Set X)) 2
    hev.two_dvd
  have hr₀2 : orderOf (r₀ : X) = 2 := (Subgroup.orderOf_coe r₀).trans hr₀
  have hr₀Y : (r₀ : X) ∈ Y :=
    hCY (mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 r₀.2 t htA).symm)
  have hC₀ : centralizer ({(r₀ : X)} : Set X) ≤ Y := (hNA _ r₀.2 hr₀2).trans hNY
  obtain ⟨a, b, c, hcls, -, -, -, -, -, -, hCa, hCb, hCc⟩ :=
    Co1Patterson.exists_involution_classes e
  have hB' : ∀ y : Y, orderOf y = 2 → 13 ∣ Nat.card (centralizer ({y} : Set Y)) →
      IsConj b y := by
    intro y hy h13y
    rcases hcls y hy with h' | h' | h'
    · rw [← card_centralizer_of_isConj h', hCa] at h13y
      norm_num at h13y
    · exact h'
    · rw [← card_centralizer_of_isConj h', hCc] at h13y
      norm_num at h13y
  have hb₀ : IsConj b ⟨r₀, hr₀Y⟩ := by
    refine hB' _ ((Subgroup.orderOf_coe _).symm.trans hr₀2) ?_
    rw [card_centralizer_subtype]
    exact h13.trans (card_dvd_of_le (le_inf hAY fun x hx =>
      mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 r₀.2 x hx)))
  intro r hr hr2 hcard
  have hbr : IsConj b ⟨r, hr⟩ := by
    refine hB' _ ((Subgroup.orderOf_coe _).symm.trans hr2) ?_
    rw [card_centralizer_subtype]
    exact hcard ▸ (by norm_num : 13 ∣ 2012774400)
  obtain ⟨y, hy⟩ := isConj_iff.1 (hb₀.symm.trans hbr)
  rw [← show (y : X) * r₀ * (y : X)⁻¹ = r from congrArg Subtype.val hy]
  exact centralizer_conj_le y.2 hC₀

end TwoB

end Co1

end CFSG.ComponentClassification.RankTwoExceptional.HoltFree
