module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Main
public import CFSG.ClassicalInvolution.Q3.M11Kernel
public import CFSG.GH74.Generic.GKFBridge
public import CFSG.GH74.Generic.GKFLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit35Rows
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitN36LieInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T23

open CFSG Subgroup Assembly.LowTwoRank
open scoped MatrixGroups

theorem oPrimeResidual_two_eq_top {Y : Type} [Group Y] [Finite Y] (hY : Group.IsPerfect Y) :
    GH74.GLS.oPrimeResidual 2 Y = ⊤ := by
  have : Group.IsPerfect Y := hY
  refine top_unique ?_
  rw [← primeResidual_eq_top_of_isPerfect (Y := Y)]
  refine sSup_le fun P hP x hx => ?_
  obtain ⟨k, hk⟩ := (hP : IsPGroup 2 P) ⟨x, hx⟩
  exact subset_closure ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem isChevalleyOver_of_mulEquiv {p : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsChevalleyOver p A) : IsChevalleyOver p B := by
  rcases h with ⟨hq, τ, n, f, hm⟩ | ⟨hp3, h⟩
  · refine .inl ⟨LocalCores.isQuasisimple_of_mulEquiv e hq, τ, n, f, ?_⟩
    exact GSThmB.OddQuot.lieModel_of_equiv
      (QuotientGroup.congr _ _ e (OuterAutomorphisms.center_map_equiv e)) hm
  · refine .inr ⟨hp3, ?_⟩
    rcases h with h | h
    · obtain ⟨e'⟩ := h
      exact .inl ⟨e.symm.trans e'⟩
    · obtain ⟨e'⟩ := h
      exact .inr ⟨e.symm.trans e'⟩

theorem theorem1_of_isTwoQuasisimple (hT1 : Harris82Theorem1Input) {Y : Type} [Group Y]
    [Finite Y] (hY : IsTwoQuasisimple Y) {z : Y} (hz : orderOf z = 2) {J : Subgroup Y}
    (hJ : IsTwoComponentIn J (centralizer {z})) (hzJ : z ∈ J) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hM : IsMTypeSchur p ↥J) :
    IsChevalleyOver p (Y ⧸ pPrimeCore 2 Y) ∨
      Nonempty (Y ⧸ pPrimeCore 2 Y ≃* ↥Blueprint.NativeSporadic.M11) := by
  have htop := oPrimeResidual_two_eq_top hY.1
  let e : ↥(GH74.GLS.oPrimeResidual 2 Y) ≃* Y :=
    (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  have hN : IsTwoQuasisimple ↥(GH74.GLS.oPrimeResidual 2 Y) :=
    isTwoQuasisimple_of_mulEquiv e.symm hY
  rcases hT1 Y hN z hz J (.inl hJ) hzJ p hp hp2 hM with h | h
  · exact .inl (isChevalleyOver_of_mulEquiv
      (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) h)
  · exact .inr h

theorem lieModel_of_theorem1 {Y : Type} [Group Y] [Finite Y] (hY : IsTwoQuasisimple Y) {p : ℕ}
    (hc : ∃ c ∈ center (Y ⧸ pPrimeCore 2 Y), c ≠ 1)
    (h : IsChevalleyOver p (Y ⧸ pPrimeCore 2 Y) ∨
      Nonempty (Y ⧸ pPrimeCore 2 Y ≃* ↥Blueprint.NativeSporadic.M11)) :
    ∃ (τ : StatedLieTag) (n f : ℕ), Blueprint.LieModel (Y ⧸ Open.fusionZStar Y) τ n p f := by
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv Y
  have hq := hY.2
  have : IsSimpleGroup ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) := hq.2.1
  have hnab : ∃ a b : Y ⧸ pPrimeCore 2 Y, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hq.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul])⟩
  rcases h with (⟨-, τ, n, f, hm⟩ | ⟨-, hS⟩) | hM11
  · exact ⟨τ, n, f, GSThmB.OddQuot.lieModel_of_equiv eZ.symm hm⟩
  · exfalso
    have h60 := GroupTheory.nonabelian_simple_order_at_least_sixty
      (G := (Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) hq.2.1 hq.2.2
    have hle : Nat.card ((Y ⧸ pPrimeCore 2 Y) ⧸ center (Y ⧸ pPrimeCore 2 Y)) ≤
        Nat.card (Y ⧸ pPrimeCore 2 Y) :=
      Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    have h24 : Nat.card (Y ⧸ pPrimeCore 2 Y) ≤ 24 := by
      rcases hS with hS | hS
      · obtain ⟨e⟩ := hS
        rw [Nat.card_congr e.toEquiv, card_specialLinearGroup_two_zmod_three]
      · obtain ⟨e⟩ := hS
        rw [Nat.card_congr e.toEquiv, ← card_specialLinearGroup_two_zmod_three]
        exact Nat.card_le_card_of_surjective _ QuotientGroup.mk_surjective
    omega
  · exfalso
    obtain ⟨eM⟩ := hM11
    have : IsSimpleGroup ↥Blueprint.NativeSporadic.M11 :=
      ClassicalInvolution.Q3.isSimpleGroup_m11_kernel
    have : IsSimpleGroup (Y ⧸ pPrimeCore 2 Y) := eM.isSimpleGroup
    obtain ⟨c, hcZ, hc1⟩ := hc
    rw [CatLeaf.center_eq_bot_of_simple hnab, mem_bot] at hcZ
    exact hc1 hcZ

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isTwoComponentIn_map_subtype {M : Subgroup G} {K₀ : Subgroup ↥M}
    (hK₀ : IsTwoComponent K₀) : IsTwoComponentIn (K₀.map M.subtype) M := by
  have hsg : (K₀.map M.subtype).subgroupOf M = K₀ :=
    comap_map_eq_self_of_injective M.subtype_injective K₀
  refine ⟨map_subtype_le K₀, ?_, ?_⟩
  · rw [hsg]
    exact hK₀.1
  · exact isTwoQuasisimple_of_mulEquiv (K₀.equivMapOfInjective M.subtype M.subtype_injective)
      hK₀.2

theorem exists_pumpup {w v : G} (hv2 : orderOf v = 2) (hvM : v ∈ centralizer {w})
    {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v})) :
    ∃ K₀ : Subgroup ↥(centralizer ({w} : Set G)), IsTwoComponent K₀ ∧
      GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w})) =
        (K₀ ⊔ K₀.map (MulAut.conj (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))).toMonoidHom).map
          (centralizer {w}).subtype ∧
      ((K₀.map (MulAut.conj (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))).toMonoidHom = K₀ ∧
          IsTwoComponentIn (L.subgroupOf (centralizer {w}))
            (K₀ ⊓ centralizer {(⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))})) ∨
        (K₀.map (MulAut.conj (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))).toMonoidHom ≠ K₀ ∧
          L.subgroupOf (centralizer {w}) = centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj
            (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))).toMonoidHom) ⟨v, hvM⟩)) := by
  set M := centralizer ({w} : Set G) with hMdef
  set v' : ↥M := ⟨v, hvM⟩
  have hv' : orderOf v' = 2 := by rw [Subgroup.orderOf_mk]; exact hv2
  have hLM : L ≤ M := hL.1.trans inf_le_left
  set L' : Subgroup ↥M := L.subgroupOf M
  have hCv : centralizer ({v'} : Set ↥M) =
      (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf M := by
    ext x
    rw [mem_subgroupOf, mem_inf]
    constructor
    · intro h
      have h' : x * v' = v' * x := mem_centralizer_singleton_iff.mp h
      exact ⟨x.2, mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h')⟩
    · rintro ⟨-, h⟩
      exact mem_centralizer_singleton_iff.mpr (Subtype.ext (mem_centralizer_singleton_iff.mp h))
  have hL' : IsTwoComponentIn L' (centralizer ({v'} : Set ↥M)) := by
    rw [hCv]
    have hle : L' ≤ (centralizer {w} ⊓ centralizer {v} : Subgroup G).subgroupOf M :=
      fun x hx => hL.1 hx
    rw [isTwoComponentIn_iff hle, UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left : centralizer {w} ⊓ centralizer {v} ≤ M) 2 Nat.prime_two]
    exact (isTwoComponentIn_iff hL.1).mp hL
  obtain ⟨K₀, hK₀, hcases, -, -, hsup⟩ := (harris82Lemma219Input_holds ↥M v' hv').2 L' hL'
  have hE : GSThmB.layerIn M = (twoLayer ↥M).map M.subtype := by
    rw [L35.twoLayer_eq_pLayer]
    rfl
  have hconj : ∀ g : ↥M, (L'.map (MulAut.conj g).toMonoidHom).map M.subtype =
      L.map (MulAut.conj (g : G)).toMonoidHom := fun g => Cor441.map_map_conj_subgroupOf hLM g
  have hiSup : (⨆ g : ↥(twoLayer ↥M), L'.map (MulAut.conj (g : ↥M)).toMonoidHom).map M.subtype =
      GSThmB.conjClosure L (GSThmB.layerIn M) := by
    rw [Subgroup.map_iSup]
    unfold GSThmB.conjClosure
    rw [hE]
    apply le_antisymm
    · refine iSup_le fun g => ?_
      refine le_iSup₂_of_le ((g : ↥M) : G)⁻¹ ⟨(g : ↥M)⁻¹, inv_mem g.2, rfl⟩ ?_
      rw [hconj]
      unfold conjugate
      rw [inv_inv]
    · refine iSup₂_le fun y hy => ?_
      obtain ⟨g, hg, rfl⟩ := hy
      refine le_iSup_of_le ⟨g⁻¹, inv_mem hg⟩ ?_
      rw [hconj]
      unfold conjugate
      rfl
  exact ⟨K₀, hK₀, by rw [← hiSup, hsup], hcases⟩

theorem exists_pumpup_of_mem {w v : G} (hv2 : orderOf v = 2) (hvM : v ∈ centralizer {w})
    {L : Subgroup G} (hL : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {v})) (hvL : v ∈ L) :
    ∃ K₀ : Subgroup ↥(centralizer ({w} : Set G)), IsTwoComponent K₀ ∧
      GSThmB.conjClosure L (GSThmB.layerIn (centralizer {w})) = K₀.map (centralizer {w}).subtype ∧
      K₀.map (MulAut.conj (⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))).toMonoidHom = K₀ ∧
      IsTwoComponentIn (L.subgroupOf (centralizer {w}))
        (K₀ ⊓ centralizer {(⟨v, hvM⟩ : ↥(centralizer ({w} : Set G)))}) := by
  obtain ⟨K₀, hK₀, hKeq, hcases⟩ := exists_pumpup hv2 hvM hL
  set v' : ↥(centralizer ({w} : Set G)) := ⟨v, hvM⟩
  rcases hcases with ⟨hfix, hLK⟩ | ⟨hne, hLeq⟩
  · refine ⟨K₀, hK₀, ?_, hfix, hLK⟩
    rw [hKeq, hfix, sup_idem]
  · exfalso
    apply hne
    have hK₀' := (L219.isTwoComponent_iff_twoComponents K₀).mp hK₀
    have hK₁' := (L219.isTwoComponent_iff_twoComponents _).mp (L219.isTwoComponent_map_conj hK₀ v')
    obtain ⟨hn, -, -⟩ := TwoComponentInteraction.mutual_normalization_core_commutation K₀ _ hK₀'
      hK₁' hne.symm
    have hvL' : v' ∈ L.subgroupOf (centralizer {w}) := hvL
    rw [hLeq] at hvL'
    have hv'N : v' ∈ normalizer (K₀ : Set ↥(centralizer ({w} : Set G))) :=
      sup_le le_normalizer hn (centralizerResidual_le.trans inf_le_left hvL')
    exact L35.map_conj_eq_of_mem_normalizer hv'N

theorem slTwo_of_lieModel (hGA : TBLit.GriessMultipliersAllModels) {L : Type} [Group L]
    [Finite L] (hL : IsTwoQuasisimple L) {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hm : Blueprint.LieModel (L ⧸ Open.fusionZStar L) .PSL 2 p k)
    (hc : center (L ⧸ pPrimeCore 2 L) ≠ ⊥) :
    1 ≤ k ∧ 5 ≤ p ^ k ∧ IsSLTwoOver (p ^ k) (L ⧸ pPrimeCore 2 L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv L
  have hmQ := GSThmB.OddQuot.lieModel_of_equiv eZ hm
  have hadm := N36.admissible_of_lieModel' hm
  have hk : 1 ≤ k := hadm.2.1
  have h3 : p ^ k ≠ 3 := fun h => hadm.2.2.2.2 (by rw [h])
  have h5 : 5 ≤ p ^ k := CatLeafProof.OddInner.five_le_pow hp hp2 hk h3
  rcases GH74.Generic.psl2_cover_of_griess hGA hp hp2 hL.2
      (N36.center_isPGroup (pPrimeCore_quotient_pPrimeCore_eq_bot 2))
      (GH74.Generic.models_of_blueprint_of_ne_zero (by norm_num) hmQ) with hbot | ⟨F, _, _, hF, he⟩
  · exact absurd hbot hc
  · obtain ⟨e⟩ := he
    let := Fintype.ofFinite F
    refine ⟨hk, h5, F, inferInstance, inferInstance, ?_,
      ⟨e.trans (specialLinearGroupEquivStatedSL 2 F).symm⟩⟩
    rw [Fintype.card_eq_nat_card, hF]

end CFSG.ComponentClassification.HarrisLit.T23
