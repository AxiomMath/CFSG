module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Section
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15LieTwin

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Asc77.ExactLayer

section Vertex

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {c : G}

theorem vertexTwin_mem (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    {M M' : Subgroup G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hM'b : IsClassicalMember p f M' b)
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card)
    (hmov : MovedByAll B c
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range) :
    modOdd c (exactCore c M') ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range := by
  have hs' : SecData p f c (exactFamily Ω c) :=
    secData_exactFamily hΩ.conjInvariant hΩ.classical hc2 ⟨M, hM⟩
  have hmem : ∀ N ∈ tqMembers Ω c, exactCore c N ∈ centMembers (exactFamily Ω c) c :=
    fun N hN => ⟨exactCore_mem_exactFamily hN, exactCore_le_centralizer c N⟩
  have hbC : b ∈ Subgroup.centralizer ({c} : Set G) :=
    Lemma52Proof.le_centralizer_of_mem hB hcB hbB
  have hbM' : b ∈ exactCore c M' := mem_exactCore hM'b hc2 hM'.2
  rcases SecComp.le_range_or_commute hs' D j (hmem M' hM') with h | hcomm
  · exact h
  · exfalso
    have hbar : oddQuotMk c ⟨b, hbC⟩ ∈ modOdd c B := oddQuotMk_mem_modOdd hbB hbC
    have hnot : oddQuotMk c ⟨b, hbC⟩ ∉ modOdd c (Subgroup.zpowers c) :=
      Lemma52Proof.oddQuotMk_not_mem_zpowers hB hcB hc1 hbB hb1 hbc hbC
    obtain ⟨y, hy, hxy⟩ := hmov _ hbar hnot
    exact hxy (hcomm _ (oddQuotMk_mem_modOdd hbM' hbC) y hy)

theorem vertexTwin (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (hc2 : IsPGroup 2 (Subgroup.zpowers c)) {B : Subgroup G} (hB : IsElemAbelian 2 B)
    (hcB : c ∈ B) (hc1 : c ≠ 1) {b : G} (hbB : b ∈ B) (hb1 : b ≠ 1) (hbc : b ≠ c)
    {M M' : Subgroup G} (hM : M ∈ tqMembers Ω c) (hM' : M' ∈ tqMembers Ω c)
    (hMb : IsClassicalMember p f M b) (hM'b : IsClassicalMember p f M' b) (hne : M' ≠ M)
    (D : LocalLieSystemAt p f (exactFamily Ω c) c) (j : Fin D.card)
    (hMj : modOdd c (exactCore c M) ≤
      (secComponentHom (normalizesLayer_exactFamily hΩ.conjInvariant) D j).range)
    (hmov : MovedByAll B c
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
  have hM'j := vertexTwin_mem hΩ hc2 hB hcB hc1 hbB hb1 hbc hM hM' hM'b D j hmov
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

end CFSG.ClassicalInvolution.Asc77
