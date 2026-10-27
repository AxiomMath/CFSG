module

public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Tools
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Proof
public import CFSG.LocalAnalysis.GLTheoremB.LayerTools
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools

public section

namespace CFSG.LocalAnalysis.GLTheoremB

open CFSG.Open

section Join

variable {G : Type*} [Group G]

theorem bConjJoin_le {B J X : Subgroup G} (hB : B ≤ Subgroup.normalizer (X : Set G))
    (hJ : J ≤ X) : bConjJoin B J ≤ X :=
  iSup₂_le fun x hx => (gLBConj_mono x hJ).trans (mem_normalizer_iff_gLBConj_eq.1 (hB hx)).le

theorem le_bConjJoin (B J : Subgroup G) : J ≤ bConjJoin B J := by
  refine le_iSup₂_of_le 1 B.one_mem ?_
  rw [gLBConj_one]

theorem gLBConj_perfect {J : Subgroup G} (hJ : ⁅J, J⁆ = J) (g : G) :
    ⁅GLBConj g J, GLBConj g J⁆ = GLBConj g J := by
  have h1 := Subgroup.map_commutator (H₁ := J) (H₂ := J) (MulAut.conj g⁻¹).toMonoidHom
  change GLBConj g ⁅J, J⁆ = ⁅GLBConj g J, GLBConj g J⁆ at h1
  rw [← h1, hJ]

theorem bConjJoin_perfect {B J : Subgroup G} (hJ : ⁅J, J⁆ = J) :
    ⁅bConjJoin B J, bConjJoin B J⁆ = bConjJoin B J := by
  refine le_antisymm ?_ ?_
  · refine Subgroup.commutator_le.2 fun a ha c hc => ?_
    rw [commutatorElement_def]
    exact (bConjJoin B J).mul_mem ((bConjJoin B J).mul_mem ((bConjJoin B J).mul_mem ha hc)
      ((bConjJoin B J).inv_mem ha)) ((bConjJoin B J).inv_mem hc)
  · refine iSup₂_le fun x hx => ?_
    calc GLBConj x J = ⁅GLBConj x J, GLBConj x J⁆ := (gLBConj_perfect hJ x).symm
      _ ≤ ⁅bConjJoin B J, bConjJoin B J⁆ := by
        have : GLBConj x J ≤ bConjJoin B J := le_iSup₂_of_le x hx le_rfl
        exact Subgroup.commutator_mono this this

theorem gLBConj_eq_of_normal {N : Subgroup G} [hN : N.Normal] (g : G) : GLBConj g N = N := by
  ext x
  rw [mem_gLBConj]
  constructor
  · intro h
    have := hN.conj_mem _ h g⁻¹
    rwa [show g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x by group] at this
  · intro h
    exact hN.conj_mem _ h g

end Join

section Setting

variable {G : Type} [Group G] [Finite G] {m p : ℕ}

theorem lambdaOf_le_of_isPreUniquenessTwoLocal {B M : Subgroup G}
    (hM : IsPreUniquenessTwoLocal p B M) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1) :
    lambdaOf p B b ≤ M :=
  ((le_sup_left.trans le_sup_left : lambdaOf p B b ≤ lambdaStar p B b).trans
    (le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl) : lambdaStar p B b ≤
      lambdaStarGroup p B)).trans hM.2.1

theorem lemma911_of_S (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hS : Lemma911S)
    (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23) : Lemma911 := by
  intro G _ _ m p hSt B M hB hM hp3 b hb hb1 J hJX
  have hp := hSt.prime
  have hp2 := hSt.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have := hSt.simple
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set X := alphaOf p M ⊓ C with hX
  have hBM : B ≤ M := le_of_isPreUniquenessTwoLocal hSt hB hM
  have hBC : B ≤ C := le_centralizer_of_mem hB.1.1 hb
  have hCtop : C ≠ ⊤ := centralizer_singleton_ne_top hSt hb1
  have hXC : X ≤ C := inf_le_right
  set H₀ := M ⊓ C with hH₀
  have hXH₀ : X ≤ H₀ := inf_le_inf_right C (alphaOf_le p M)
  have hH₀X : H₀ ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [mem_normalizer_iff_gLBConj_eq, hX, gLBConj_inf,
      mem_normalizer_iff_gLBConj_eq.1 (le_normalizer_alphaOf p M hg.1),
      mem_normalizer_iff_gLBConj_eq.1 (Subgroup.le_normalizer hg.2)]
  have hBX : B ≤ Subgroup.normalizer (X : Set G) := fun x hx => hH₀X ⟨hBM hx, hBC hx⟩
  have hJH₀ : IsSubnormal J H₀ :=
    isSubnormal_trans' hJX.2.1 (IsSubnormal.step hXH₀
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH₀).2 hH₀X) (IsSubnormal.refl H₀))
  obtain ⟨S, hS2, hBS, hSJ, hJS⟩ := hS G m p hSt B M hB hM hp3 b hb hb1 J hJX
  set Js := bConjJoin B J with hJs
  have hJsC : Js ≤ C := (bConjJoin_le hBX hJX.1).trans hXC
  have hSC : S ≤ C := hSJ.trans hJsC
  have hJsperf : ⁅Js, Js⁆ = Js := bConjJoin_perfect hJX.2.2.1
  set π := QuotientGroup.mk' (GLAPPrimeCore p ↥C) with hπ
  have hQcore : GLAPPrimeCore p (↥C ⧸ GLAPPrimeCore p ↥C) = ⊥ := glaPPrimeCore_quotient_eq_bot hp
  have hQ : CFSG.Open.IsKGroup (↥C ⧸ GLAPPrimeCore p ↥C) :=
    isKGroup_quotient' (isKGroup_of_isKProper hSt.kProper hCtop) _
  have hOut : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    fun K hK => outer_solvable_of_component hSch hQ hK
  obtain ⟨hSF, hSN⟩ := barX_two_subgroup_props i20 i11 l23 hSt hB hCtop hBC hSC hS2 hBS
  have hYperf : ⁅barX p C Js, barX p C Js⁆ = barX p C Js := barX_perfect p hJsC hJsperf
  have hYS : barX p C Js ≤ ⨆ y ∈ barX p C Js, GLBConj y (barX p C S) :=
    (barX_mono p hJS).trans (barX_iSup_conj_le p hJsC hSC)
  have hYN : ∀ K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C), IsComponentOf K ⊤ →
      barX p C Js ≤ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := fun K hK =>
    le_of_le_iSup_conj (F := fun K' => Subgroup.normalizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_normalizer g K') hYS
      (fun y _ => hSN _ (isComponentOf_gLBConj hK y⁻¹))
  have : (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C)).Normal :=
    CFSG.LieType.BorelTits.pCore_normal p
  have hYF : barX p C Js ≤ Subgroup.centralizer
      (CFSG.Open.pCore p (↥C ⧸ GLAPPrimeCore p ↥C) : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
    le_of_le_iSup_conj
      (F := fun K' => Subgroup.centralizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_centralizer g K') hYS
      (fun y _ => by rw [gLBConj_eq_of_normal]; exact hSF)
  have hYE : barX p C Js ≤ CFSG.ComponentClassification.Layer.subgroup
      (↥C ⧸ GLAPPrimeCore p ↥C) :=
    le_layer_of_perfect hp hQcore hOut hYperf hYF hYN
  have hB' : IsSCp p ⊤ (B.subgroupOf C) := isSCp_subgroupOf (l23 G m p hSt B hB) hBC
  have hrank : GLATwoLocalRank p ↥C ≤ CFSG.Open.pRank p (B.subgroupOf C) := by
    refine (glaTwoLocalRank_subgroup_le hp.one_lt C).trans ?_
    rw [hSt.rank_eq]
    refine CFSG.SectionRank.le_pRank hp.one_lt le_rfl hB'.2.1 ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv, hSt.card_eq hB]
  set 𝒦 : Set (Subgroup (↥C ⧸ GLAPPrimeCore p ↥C)) := {K | ∃ L : Subgroup G,
    GLAPComponent p C L ∧ IsStronglyLocallyOneBalanced p B b L ∧ barX p C L = K} with h𝒦
  have h𝒦c : ∀ K ∈ 𝒦, IsComponentOf K ⊤ := by
    rintro _ ⟨L, hL, -, rfl⟩
    exact hL.2.2.1
  have hSK : ∀ K ∈ 𝒦, barX p C S ≤
      Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    rintro _ ⟨L, hL, hbal, rfl⟩
    have hSL : S ≤ Subgroup.normalizer (L : Set G) :=
      le_normalizer_of_input11_6 i11 hSt.kProper hp hp2 hCtop hBC hSC (l23 G m p hSt B hB)
        hrank hS2 hBS hL
    have hcomm : ⁅L, S⁆ ≤ GLAPPrimeCoreOf p L :=
      hbal S (le_inf hSL hSC) (coprime_card_of_isPGroup_two hp hp2 hS2)
        (fun g hg => hBS hg.1)
    refine barX_le_centralizer fun s hs t ht _ _ => ?_
    have h3 : s * t * s⁻¹ * t⁻¹ ∈ ⁅S, L⁆ := Subgroup.commutator_mem_commutator hs ht
    rw [Subgroup.commutator_comm] at h3
    exact glaPPrimeCoreOf_le_of_isSubnormal hp hL.2.1 (hcomm h3)
  have hYK : ∀ K ∈ 𝒦, barX p C Js ≤
      Subgroup.centralizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) := by
    intro K hK
    refine le_of_le_iSup_conj
      (F := fun K' => Subgroup.centralizer (K' : Set (↥C ⧸ GLAPPrimeCore p ↥C)))
      (fun g K' => gLBConj_centralizer g K') hYS (fun y hy => ?_)
    have hyn : y⁻¹ ∈ Subgroup.normalizer (K : Set (↥C ⧸ GLAPPrimeCore p ↥C)) :=
      Subgroup.inv_mem _ (hYN K (h𝒦c K hK) hy)
    rw [mem_normalizer_iff_gLBConj_eq.1 hyn]
    exact hSK K hK
  have hYΛ := le_layer_diff_of_perfect 𝒦 h𝒦c hYperf hYE hYK
  have hlam : lambdaOf p B b ≤ M := lambdaOf_le_of_isPreUniquenessTwoLocal hM hb hb1
  have hΛ' : (⨆ K ∈ {K : Subgroup (↥C ⧸ GLAPPrimeCore p ↥C) | IsComponentOf K ⊤ ∧ K ∉ 𝒦}, K) ≤
      barX p C H₀ := by
    refine iSup₂_le fun K hK => ?_
    obtain ⟨L, hL, rfl⟩ := exists_glaPComponent_barX_eq C hK.1
    have hbal : ¬ IsStronglyLocallyOneBalanced p B b L := fun h => hK.2 ⟨L, hL, h, rfl⟩
    have hLM : L ≤ M := (le_sSup ⟨hL, hbal⟩ : L ≤ lambdaOf p B b).trans hlam
    exact barX_mono p (le_inf hLM hL.1)
  have hJbar : IsSubnormal (barX p C J) ⊤ :=
    isSubnormal_trans'
      (isSubnormal_of_le_of_le (isSubnormal_barX p hJH₀)
        ((barX_mono p (le_bConjJoin B J)).trans hYΛ) hΛ')
      (isSubnormal_iSup_components _ (fun K hK => hK.1))
  set P : Subgroup G := ((barX p C J).comap π).map C.subtype with hP
  have hPC : IsSubnormal P C := isSubnormal_preimage_barX p hJbar
  have hJP : J ≤ P := by
    intro j hj
    have hjC : j ∈ C := hXC (hJX.1 hj)
    exact ⟨⟨j, hjC⟩, ⟨⟨j, hjC⟩, (Subgroup.mem_subgroupOf).2 hj, rfl⟩, rfl⟩
  have hPH₀ : P ≤ H₀ := by
    rintro _ ⟨c, ⟨c', hc', hcc'⟩, rfl⟩
    have hker : c'⁻¹ * c ∈ GLAPPrimeCore p ↥C := QuotientGroup.eq.1 hcc'
    have hK0M : ((c'⁻¹ * c : ↥C) : G) ∈ M := lemma91_i hSt hB hM hb ⟨_, hker, rfl⟩
    have hc'M : (c' : G) ∈ M := alphaOf_le p M (hJX.1 ((Subgroup.mem_subgroupOf).1 hc')).1
    refine ⟨?_, c.2⟩
    have : (c : G) = (c' : G) * ((c'⁻¹ * c : ↥C) : G) := by simp
    rw [Subgroup.coe_subtype, this]
    exact M.mul_mem hc'M hK0M
  have hJC : IsSubnormal J C :=
    isSubnormal_trans' (isSubnormal_of_le_of_le hJH₀ hJP hPH₀) hPC
  exact isTwoPrimeComp_of_le hJX hXC hJC

theorem prop98_of_inputs_S (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier) (hS : Lemma911S)
    (i20 : Input20_1) (i11 : Input11_6) (l23 : Lemma23) (i19 : Input19Delta)
    (i19' : Input19_1_6) (h95 : Prop95Core) (h99 : Lemma99) (i22 : Input22_5)
    (iPi : InputPiGen) : Prop98 :=
  prop98_of_inputs i20 i11 l23 i19 i19' h95 h99 (lemma911_of_S hSch hS i20 i11 l23) i22 iPi

end Setting

end CFSG.LocalAnalysis.GLTheoremB
