module

public import CFSG.ClassicalInvolution.Asc77.AscT7FA
public import CFSG.ClassicalInvolution.ModelFacts.Orth15LieTwin
public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel


public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer AscE184Sect

namespace T7S2R

section Transport

variable {G : Type} [Group G]

@[expose] def OrbitFam (Φ : Set (Subgroup G)) (Y : Subgroup G) : Prop :=
  ∀ M ∈ quotFamily (restrictFamily Φ Y) (classicalInvolutionOddCore ↥Y),
    ∀ M' ∈ quotFamily (restrictFamily Φ Y) (classicalInvolutionOddCore ↥Y),
      ∃ g : ↥Y ⧸ classicalInvolutionOddCore ↥Y, conjSub g M = M'

theorem orbitFam_congr {Φ₁ Φ₂ : Set (Subgroup G)} {Y₁ Y₂ : Subgroup G} (hΦ : Φ₁ = Φ₂)
    (hY : Y₁ = Y₂) (h : OrbitFam Φ₁ Y₁) : OrbitFam Φ₂ Y₂ := by
  subst hΦ hY
  exact h

theorem dstarConnected_congr {Φ₁ Φ₂ : Set (Subgroup G)} {Y₁ Y₂ : Subgroup G} (hΦ : Φ₁ = Φ₂)
    (hY : Y₁ = Y₂) :
    T3.DStarConnected (quotFamily (restrictFamily Φ₁ Y₁) (classicalInvolutionOddCore ↥Y₁)) ↔
      T3.DStarConnected (quotFamily (restrictFamily Φ₂ Y₂) (classicalInvolutionOddCore ↥Y₂)) := by
  subst hΦ hY
  exact Iff.rfl

end Transport

section Trans

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}


theorem secFam_trans_of_not_connected (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    (hBelow : CITBelowU p f (Nat.card G)) (h3s : T3.Thm3SectBelow p f (Nat.card G))
    {B : Subgroup G} (hB : B ∈ tqMembers Ω c) (hdisc : ¬ SectionConnected Ω c) :
    ∀ K₁ ∈ secFam Ω c, ∀ L ∈ secFam Ω c, ∃ g, conjSub g K₁ = L := by
  have hBs : B ∈ sectionMembers Ω (Subgroup.zpowers c) := by
    rw [sectionMembers_zpowers]
    exact hB
  have hY : sectionHull Ω (Subgroup.zpowers c) ≠ ⊤ := by
    rw [sectionHull_zpowers hΩ hc2]
    exact exactLayer_ne_top hnc
  have horb := (section_connected_or_orbit hp hq hΩ hc2 hY hBelow h3s hBs).resolve_left hdisc
  have key : OrbitFam (sectionFamily Ω (Subgroup.zpowers c))
      (sectionHull Ω (Subgroup.zpowers c)) := by
    intro M hM M' hM'
    obtain ⟨y₁, h₁⟩ := horb M hM
    obtain ⟨y₂, h₂⟩ := horb M' hM'
    exact ⟨y₂ * y₁⁻¹, by rw [conjSub_mul, ← h₁, conjSub_inv_conjSub, h₂]⟩
  have hΦ : sectionFamily Ω (Subgroup.zpowers c) = centralizingMembers (exactFamily Ω c) {c} :=
    (sectionFamily_zpowers hΩ hc2).trans (centMembers_exactFamily Ω c).symm
  have hY' : sectionHull Ω (Subgroup.zpowers c) = centralizingLayer (exactFamily Ω c) {c} :=
    sectionHull_zpowers hΩ hc2
  exact orbitFam_congr hΦ hY' key

end Trans

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}


theorem vertexTwin' (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) {b : G} (hbB : b ∈ B) {M M' : Subgroup G} (hM : M ∈ tqMembers Ω c)
    (hM' : M' ∈ tqMembers Ω c) (hMb : IsClassicalMember p f M b)
    (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hM'j : modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hG2 : D.tag j ≠ .G2) (hD4 : D.tag j ≠ .trialityD4) :
    ∃ (hbC : b ∈ Subgroup.centralizer ({c} : Set G)) (R R' : Subgroup (compModel D j).K)
      (x x' : (compModel D j).K),
      TwinPairOn (D.tag j) (compModel D j)
        (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j) R R' x x' ∧
      TwinShape (D.tag j) (D.rank j) ∧
      R.map (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j) =
        modOdd c (exactCore c M) ∧
      R'.map (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j) =
        modOdd c (exactCore c M') ∧
      secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j x =
        oddQuotMk c ⟨b, hbC⟩ := by
  classical
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  have hmem : ∀ N ∈ tqMembers Ω c, exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    fun N hN => ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hbB
  obtain ⟨R, hR, hRM⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M hM) hMj
  obtain ⟨R', hR', hRM'⟩ := exists_fundamental_of_modOdd_le_sec hs' D j (hmem M' hM') hM'j
  obtain ⟨hbY, hK, hK', hneK, hzK, hzK'⟩ := secFam_twin hp hq hΩ hc2 hM hM' hMb hM'b hne
  have hRφ := map_hom_eq_modOddIn hs' D j (hmem M hM) hRM
  have hR'φ := map_hom_eq_modOddIn hs' D j (hmem M' hM') hRM'
  have hΦ : HypOmega p f (secFam Ω c) := hypOmega_secFam hp hq hΩ hc2 hs' D
  have hKR : R.map (D.hom j) ∈ secFam Ω c := by rw [hRφ]; exact hK
  have hK'R' : R'.map (D.hom j) ∈ secFam Ω c := by rw [hR'φ]; exact hK'
  have hzKR : IsUniqueInvolution (R.map (D.hom j)) (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (exactFamily Ω c) {c})) ⟨b, hbY⟩) := by rw [hRφ]; exact hzK
  have hzK'R' : IsUniqueInvolution (R'.map (D.hom j)) (QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (exactFamily Ω c) {c})) ⟨b, hbY⟩) := by rw [hR'φ]; exact hzK'
  have hneR : R.map (D.hom j) ≠ R'.map (D.hom j) := by rw [hRφ, hR'φ]; exact hneK
  obtain ⟨hshape, hneR, hcomm, x, hx, x', hx', hx2, hx1, hx'2, hx'1, hψx, hψx'⟩ :=
    twinShape_of_twin hp hq hΦ (LieSystemData.toOmegaLie D (omegaGen_secFam hs')) j hG2 hD4
      (R := R) (R' := R') hR hR' hKR hK'R' hzKR hzK'R' hneR
  have hψb : ∀ w : (compModel D j).K, D.hom j w = QuotientGroup.mk' (classicalInvolutionOddCore
      ↥(centralizingLayer (exactFamily Ω c) {c})) ⟨b, hbY⟩ →
      secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j w =
        oddQuotMk c ⟨b, hbC⟩ := by
    intro w hw
    show sectionQuotientHom (normalizesLayer_exactFamily hΩ.conjInvariant) (D.hom j w) = _
    rw [hw]
    rfl
  exact ⟨hbC, R, R', x, x',
    { ker := secComponentHom_ker_le_center (normalizesLayer_exactFamily hΩ.conjInvariant) D j
      mem := hR
      mem' := hR'
      ne := hneR
      comm := hcomm
      hx := hx
      hx2 := hx2
      hx1 := hx1
      hx' := hx'
      hx'2 := hx'2
      hx'1 := hx'1
      same := (hψb x hψx).trans (hψb x' hψx').symm },
    hshape, hRM, hRM', hψb x hψx⟩

end Vertex

section TransSec

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem sectionConnected_iff_secFam (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) :
    SectionConnected Ω c ↔ T3.DStarConnected (secFam Ω c) := by
  unfold SectionConnected
  exact dstarConnected_congr
    ((sectionFamily_zpowers hΩ hc2).trans (centMembers_exactFamily Ω c).symm)
    (sectionHull_zpowers hΩ hc2)


theorem transSection_secFam (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) (hnc : ¬ ({c} : Set G) ⊆ Subgroup.center G)
    (hBelow : CITBelowU p f (Nat.card G)) (h3s : T3.Thm3SectBelow p f (Nat.card G))
    {B : Subgroup G} (hB : B ∈ tqMembers Ω c) (hdisc : ¬ SectionConnected Ω c) :
    TransSection p f (secFam Ω c) := by
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨B, hB⟩
  have hΦ : HypOmegaMod p f (secFam Ω c) := hypOmegaMod_secFam hp hq hΩ hc2
  have hΛ : HypOmegaMod p f (restrictFamily (centralizingMembers (exactFamily Ω c) {c})
      (centralizingLayer (exactFamily Ω c) {c})) :=
    hypOmegaMod_restrictFamily_congr (centMembers_exactFamily Ω c).symm rfl
      (hypOmegaMod_exactPair hp hq hΩ hc2)
  have hlt : Nat.card (↥(centralizingLayer (exactFamily Ω c) {c})) < Nat.card G :=
    card_exactLayer_lt hnc
  have hdisc' : ¬ T3.DStarConnected (secFam Ω c) := fun h =>
    hdisc ((sectionConnected_iff_secFam hΩ hc2).mpr h)
  have hΛA := h3s hp hq _ hlt _ hΛ hdisc'
  exact
    { hyp := hΦ
      oddCore := CFSG.ComponentClassification.OddCore.quotient_corefree _
      gen := omegaGen_secFam hs'
      trans := secFam_trans_of_not_connected hp hq hΩ hc2 hnc hBelow h3s hB hdisc
      aEmpty := aEmpty_quotFamily hp hq hΛ hΦ (CFSG.ComponentClassification.OddCore.odd_card _)
        hΛA }

end TransSec

end T7S2R

end CFSG.ClassicalInvolution.Asc77
