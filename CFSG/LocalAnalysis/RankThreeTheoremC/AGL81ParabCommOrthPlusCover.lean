module

public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommOrthPlusDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommGeneric
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ParabCommLinTransferCover
public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthPlusMain
import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelMaximal
import CFSG.Fischer.Classification.Recognition.PSU6
import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit CFSG.LieType.Universal.Spin
  CFSG.AGLEmbedding CFSG.AGLEmbedding.LeviBlock
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
  (native_partialBorel_eq_fullBorel)
open scoped Pointwise
open CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm

variable {r : ℕ} {K : Type} [Field K]

theorem nonempty_of_map_eq_plusNodeStab {X : Type} [Group X] {P₀ : Subgroup X} (hne : P₀ ≠ ⊤)
    (hr : 3 ≤ r) (ψ : X ≃* ↥(orthElementaryGroup (quadPlus r K))) {I : Set (Fin r)}
    (hI : (P₀.map ψ.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype =
      plusNodeStab K hr I) : I.Nonempty := by
  by_contra hemp
  rw [Set.not_nonempty_iff_eq_empty] at hemp
  rw [hemp, plusNodeStab_empty] at hI
  apply hne
  refine eq_top_iff.2 fun y _ => ?_
  have hmem : ((ψ y : ↥(orthElementaryGroup (quadPlus r K))) :
      (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) ∈
        (P₀.map ψ.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype := by
    rw [hI]
    exact (ψ y).2
  obtain ⟨_, ⟨z, hz, rfl⟩, hzy⟩ := hmem
  have hzy' : z = y := ψ.injective (Subtype.ext hzy)
  rw [hzy'] at hz
  exact hz

theorem exists_plusNodeStab_of_parab [Finite K] [CharP K 2] (hr : 4 ≤ r) {X : Type} [Group X]
    [Finite X] {P₀ T₀ : Subgroup X} (hT₂ : IsPGroup 2 T₀) (hTi : ¬ 2 ∣ T₀.index)
    (hNT₀ : Subgroup.normalizer (T₀ : Set X) ≤ P₀) (hne : P₀ ≠ ⊤)
    (φ : X ≃* ↥(orthElementaryGroup (quadPlus r K))) :
    ∃ (ψ : X ≃* ↥(orthElementaryGroup (quadPlus r K))) (I : Set (Fin r)), I.Nonempty ∧
      ((⟨r - 2, by omega⟩ : Fin r) ∈ I → (⟨r - 1, by omega⟩ : Fin r) ∈ I) ∧
      (P₀.map ψ.toMonoidHom).map (orthElementaryGroup (quadPlus r K)).subtype =
        plusNodeStab K (by omega) I := by
  have hr3 : 3 ≤ r := by omega
  set E := orthElementaryGroup (quadPlus r K) with hE
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥E := Finite.of_equiv _ φ.toEquiv
  have hT₁ : IsPGroup 2 (T₀.map φ.toMonoidHom) := hT₂.map _
  have hT₁i : ¬ 2 ∣ (T₀.map φ.toMonoidHom).index := by
    rw [show φ.toMonoidHom = (φ : X →* ↥E) from rfl, Subgroup.index_map_equiv]
    exact hTi
  let S₁ : Sylow 2 ↥E := hT₁.toSylow hT₁i
  obtain ⟨⟨U, hU⟩, hN, -⟩ := orthogonal_geometry_split_Sylow_flag_normalizer (K := K) 2 hr3
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq ↥E U S₁
  let ψ₀ : X ≃* ↥E := φ.trans (MulAut.conj x⁻¹)
  have hψT : T₀.map ψ₀.toMonoidHom = (posUnip r K).subgroupOf E := by
    have h1 : ((x • U : Sylow 2 ↥E) : Subgroup ↥E) = T₀.map φ.toMonoidHom := by rw [hx]; rfl
    rw [Sylow.coe_subgroup_smul, hU] at h1
    have h1' : T₀.map φ.toMonoidHom =
        ((posUnip r K).subgroupOf E).map (MulAut.conj x).toMonoidHom := by
      rw [← h1]
      rfl
    have h2 : T₀.map ψ₀.toMonoidHom =
        (T₀.map φ.toMonoidHom).map (MulAut.conj x⁻¹).toMonoidHom := by
      rw [Subgroup.map_map]
      rfl
    have : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ := by
      refine MonoidHom.ext fun z => ?_
      change x⁻¹ * (x * z * x⁻¹) * x⁻¹⁻¹ = z
      group
    rw [h2, h1', Subgroup.map_map, this, Subgroup.map_id]
  set M₀ := (P₀.map ψ₀.toMonoidHom).map E.subtype with hM₀
  have hB₀ : borel r K ≤ M₀ := by
    intro b hb
    have hbE : b ∈ E := borel_le hb
    have h1 : (⟨b, hbE⟩ : ↥E) ∈ (flagStab r K).subgroupOf E := by
      rw [Subgroup.mem_subgroupOf, native_partialBorel_eq_fullBorel r K hr3]
      exact hb
    rw [← hN, ← hψT, ← Subgroup.map_normalizer_eq_of_bijective _ ψ₀.bijective] at h1
    exact ⟨_, Subgroup.map_mono hNT₀ h1, rfl⟩
  have hM₀E : M₀ ≤ E := Subgroup.map_subtype_le _
  by_cases htw : weylElt r K ⟨r - 2, by omega⟩ ∉ M₀ ∧ weylElt r K ⟨r - 1, by omega⟩ ∈ M₀
  ·
    set ψ := ψ₀.trans (plusGraphConj K (by omega)) with hψ
    set M := (P₀.map ψ.toMonoidHom).map E.subtype with hM
    have hmemM : ∀ g, g ∈ M ↔ swapPair K (⟨r - 1, by omega⟩ : Fin r) * g *
        swapPair K ⟨r - 1, by omega⟩ ∈ M₀ := by
      intro g
      constructor
      · rintro ⟨_, ⟨z, hz, rfl⟩, rfl⟩
        refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
        change ((ψ₀ z : ↥E) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) =
          swapPair K _ * ((plusGraphConj K (by omega) (ψ₀ z) : ↥E) :
            (Fin r ⊕ Fin r → K) ≃ₗ[K] _) * swapPair K _
        rw [coe_plusGraphConj]
        simp only [← mul_assoc, swapPair_mul_self, one_mul]
        rw [mul_assoc, swapPair_mul_self, mul_one]
      · rintro ⟨_, ⟨z, hz, rfl⟩, hzg⟩
        refine ⟨_, ⟨z, hz, rfl⟩, ?_⟩
        change ((plusGraphConj K (by omega) (ψ₀ z) : ↥E) : (Fin r ⊕ Fin r → K) ≃ₗ[K] _) = g
        change ((ψ₀ z : ↥E) : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K)) = _ at hzg
        rw [coe_plusGraphConj, hzg]
        simp only [← mul_assoc, swapPair_mul_self, one_mul]
        rw [mul_assoc, swapPair_mul_self, mul_one]
    have hBM : borel r K ≤ M := fun b hb => (hmemM b).2 (hB₀ (conj_swapPair_mem_borel hr3 hb))
    have hME : M ≤ E := Subgroup.map_subtype_le _
    have hM₀X : ∀ h ∈ M₀, h • Xstar r K (by omega) = Xstar r K (by omega) := by
      intro h hh
      rw [eq_plusNodeStab_of_borel_le hr3 hM₀E hB₀] at hh
      have := (mem_plusNodeStab.1 hh).2 ⟨r - 2, by omega⟩ htw.1
      simpa [plusNodeSpace, show ¬ r - 2 + 1 ≤ r - 2 by omega] using this
    have hnM : weylElt r K ⟨r - 1, by omega⟩ ∉ M := by
      intro hn
      have h := hM₀X _ ((hmemM _).1 hn)
      have hσ := swapPair_smul_flag_top (K := K) hr3
      rw [mul_smul, mul_smul, hσ.2, ← hσ.1] at h
      apply (weylElt_last_smul (K := K) hr3).1
      have h2 := congrArg (swapPair K (⟨r - 1, by omega⟩ : Fin r) • ·) h
      simpa only [smul_smul, ← mul_assoc, swapPair_mul_self, one_mul, one_smul] using h2
    refine ⟨ψ, {i | weylElt r K i ∉ M}, nonempty_of_map_eq_plusNodeStab hne hr3 ψ
      (eq_plusNodeStab_of_borel_le hr3 hME hBM), fun _ => hnM,
      eq_plusNodeStab_of_borel_le hr3 hME hBM⟩
  · refine ⟨ψ₀, {i | weylElt r K i ∉ M₀}, nonempty_of_map_eq_plusNodeStab hne hr3 ψ₀
      (eq_plusNodeStab_of_borel_le hr3 hM₀E hB₀), fun h2 => ?_,
      eq_plusNodeStab_of_borel_le hr3 hM₀E hB₀⟩
    by_contra h1
    exact htw ⟨h2, not_not.1 h1⟩

theorem exists_mulEquiv_plusElementary (hZ : OddCenterRest) {X : Type} [Group X] [Finite X]
    (hX : Open.IsQuasisimple X) (hodd : Odd (Nat.card (Subgroup.center X)))
    (hD : IsLieOf IdxD (X ⧸ Subgroup.center X)) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2), 4 ≤ r ∧
      Nonempty (X ≃* ↥(orthElementaryGroup (quadPlus r K))) := by
  have hL : IsComponentOf (⊤ : Subgroup X) ⊤ :=
    CFSG.LocalAnalysis.GLTheoremA.isComponentOf_top_of_isQuasisimple hX
  let eT : ↥(⊤ : Subgroup X) ≃* X := Subgroup.topEquiv
  have hcT : (Subgroup.center ↥(⊤ : Subgroup X)).map eT.toMonoidHom = Subgroup.center X :=
    Subgroup.map_center_eq eT
  have hcard : Nat.card (Subgroup.center ↥(⊤ : Subgroup X)) = Nat.card (Subgroup.center X) := by
    rw [← hcT]
    exact (Subgroup.card_map_of_injective eT.injective).symm
  let eQ : ↥(⊤ : Subgroup X) ⧸ Subgroup.center ↥(⊤ : Subgroup X) ≃* X ⧸ Subgroup.center X :=
    QuotientGroup.congr _ _ eT hcT
  obtain ⟨d, hd, ⟨e⟩⟩ := hD
  obtain ⟨r, K, _, _, _, hr, ⟨φ⟩⟩ := exists_mulEquiv_plusElementary_of_idxD hZ hL
    (hcard ▸ hodd) ⟨d, hd, ⟨eQ.trans e⟩⟩
  exact ⟨r, K, inferInstance, inferInstance, inferInstance, hr, ⟨eT.symm.trans φ⟩⟩

theorem exists_flag_setup (hZ : OddCenterRest) {A : Type} [Group A] [Finite A] {Y P : Subgroup A}
    (hY : Open.IsQuasisimple ↥Y) (h2 : pCoreOf 2 Y = ⊥)
    (hF : IsLieOf IdxD (↥Y ⧸ Subgroup.center ↥Y)) (hpar : IsParabolicTwo Y P) (hne : P ≠ Y) :
    ∃ (r : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (D : Finset ℕ)
      (ρ : ↥(orthElementaryGroup (quadPlus r K)) ≃* ↥Y), 4 ≤ r ∧
      (∀ d ∈ D, 1 ≤ d ∧ d ≤ r) ∧ (r - 1 ∈ D → r ∈ D) ∧
      ∀ x : ↥(orthElementaryGroup (quadPlus r K)),
        (x : GLV r K) ∈ plusFlagStab K r D ↔ ((ρ x : ↥Y) : A) ∈ P := by
  have hodd : Odd (Nat.card (Subgroup.center ↥Y)) :=
    Lin.odd_card_center_of_pCore_eq_bot (pCore_eq_bot_of_pCoreOf h2)
  obtain ⟨r, K, _, _, _, hr, ⟨φ⟩⟩ := exists_mulEquiv_plusElementary hZ hY hodd hF
  obtain ⟨hPY, T, ⟨hTY, hT2, hTi⟩, hNP⟩ := hpar
  set T₀ : Subgroup ↥Y := T.subgroupOf Y with hT₀
  have hNT₀ : Subgroup.normalizer (T₀ : Set ↥Y) ≤ P.subgroupOf Y := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hNP ⟨x.2, Subgroup.mem_normalizer_fintype fun s hs => ?_⟩
    have h1 : (⟨s, hTY hs⟩ : ↥Y) ∈ T₀ := Subgroup.mem_subgroupOf.2 hs
    have h2 := (Subgroup.mem_normalizer_iff.1 hx ⟨s, hTY hs⟩).1 h1
    simpa [T₀, Subgroup.mem_subgroupOf] using h2
  have hne' : P.subgroupOf Y ≠ ⊤ := by
    intro htop
    apply hne
    refine le_antisymm hPY fun y hy => ?_
    have : (⟨y, hy⟩ : ↥Y) ∈ P.subgroupOf Y := by rw [htop]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this
  obtain ⟨ψ, I, -, hI, hψ⟩ := exists_plusNodeStab_of_parab hr (hT2.comap_subtype (K := Y)) hTi
    hNT₀ hne' φ
  rw [plusNodeStab_eq_plusFlagStab (by omega) hI] at hψ
  obtain ⟨hD1, hD2⟩ := plusNodeDims_props (by omega) hI
  refine ⟨r, K, inferInstance, inferInstance, inferInstance, plusNodeDims I, ψ.symm, hr, hD1,
    hD2, fun x => ?_⟩
  constructor
  · intro hx
    rw [← hψ] at hx
    obtain ⟨_, ⟨z, hz, rfl⟩, hzx⟩ := hx
    have hzx' : ψ z = x := Subtype.ext hzx
    rw [← hzx', MulEquiv.symm_apply_apply]
    exact Subgroup.mem_subgroupOf.1 hz
  · intro hx
    rw [← hψ]
    refine ⟨ψ (ψ.symm x), ⟨ψ.symm x, Subgroup.mem_subgroupOf.2 hx, rfl⟩, ?_⟩
    rw [MulEquiv.apply_symm_apply]
    rfl

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThreeThree.ParabComm.OrthPlus
