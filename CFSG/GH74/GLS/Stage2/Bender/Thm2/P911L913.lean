module

public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911D1X
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.P911CaseC
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Sl2

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm2.P911

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage2.Signalizer
  CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped commutatorElement

section Fin

variable {G : Type} [Group G] [Finite G] {z : G} {k : Kind} {S M : Subgroup G} {p : ℕ}
  {X V N : Subgroup G}


omit [Finite G] in
theorem X_le_A1 (hXP : X ≤ Op p M) (hXc : ⁅X, zpowers z⁆ = X)
    (hXN : normalizer (X : Set G) ≤ N) : X ≤ L915.A1 z M N p := by
  have hXN' : X ≤ N := le_trans Subgroup.le_normalizer hXN
  conv_lhs => rw [← hXc]
  exact Subgroup.commutator_mono (le_inf hXP hXN') le_rfl

theorem sig4Sub_A1_of (hC : Ctx9 G z k S M p) (hN : IsCoatom N) (hzN : z ∈ N)
    (hX0 : X ≠ ⊥) (hXA : X ≤ L915.A1 z M N p) : Sig4Sub G z N p (L915.A1 z M N p) :=
  ⟨hN.1, ⟨hC.prime, hC.odd, hzN, (L915.A1_le hC hzN).trans inf_le_right,
    L915.isPGroup_A1 hC hzN, fun hb => hX0 (le_bot_iff.mp (hb ▸ hXA)),
    fun _ hcN hcz => L915.inv_A1 hC hcN hcz, L915.A1_comm hC hzN⟩⟩

theorem concl43E_X1 (h43E : Prop4_3E) (hC : Ctx9 G z k S M p) (hN : IsCoatom N) (hzN : z ∈ N)
    (hX0 : X ≠ ⊥) (hXA : X ≤ L915.A1 z M N p) (hXE : ¬ X ≤ centralizer (Em N : Set G)) :
    Concl43E k (zSec z N hzN (pCore p ↥N)) p (xBar p N (L915.A1 z M N p)) := by
  refine L64.prop4_3Esub_of h43E hC.ctx (sig4Sub_A1_of hC hN hzN hX0 hXA) ?_
  intro hb
  apply hXE
  have h1 : Em N ≤ centralizer ((L915.A1 z M N p : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hb
  exact hXA.trans (Subgroup.le_centralizer_iff.mp h1)


theorem layer_inf_centralizer_le_fitting (Y : Type*) [Group Y] [Finite Y] :
    layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) ≤ fittingSubgroup Y := by
  have : (layer Y).Characteristic := LocalCores.layer_characteristic
  have hWn : (layer Y ⊓ Subgroup.centralizer (layer Y : Set Y)).Normal :=
    Subgroup.normal_inf_normal _ _
  have hWcomm : IsMulCommutative (layer Y ⊓ Subgroup.centralizer (layer Y : Set Y) : Subgroup Y) :=
    ⟨⟨fun x y => Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 y y.2.1).symm⟩⟩
  exact LocalCores.fitting_characteristic.2.2 _ hWn inferInstance

theorem false_of_V_le_centralizer_layer (h512 : IG_5_12) (H : Hyp911 z k S M p X V N)
    (hVc : V.subgroupOf N ≤ centralizer ((layer ↥N : Subgroup ↥N) : Set ↥N)) : False := by
  have hp := H.ctx.prime
  have : Fact p.Prime := ⟨hp⟩
  have hntV : Nontrivial ↥V := (Finite.one_lt_card_iff_nontrivial).mp (by
    rw [H.hV2]; exact Nat.one_lt_pow two_ne_zero hp.one_lt)
  obtain ⟨⟨v, hvV⟩, hv1⟩ : ∃ w : ↥V, w ≠ 1 := exists_ne 1
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  have hvN : v ∈ N := (H.hV hvV).1.2
  have hvP : v ∈ Op p M := (H.hV hvV).1.1
  have hv'V : (⟨v, hvN⟩ : ↥N) ∈ V.subgroupOf N := Subgroup.mem_subgroupOf.mpr hvV
  have hvC : (⟨v, hvN⟩ : ↥N) ∈ centralizer ((layer ↥N : Subgroup ↥N) : Set ↥N) := hVc hv'V
  by_cases hR : Op p N = ⊥
  ·
    have hpc : pCore p ↥N = ⊥ := by
      have := hR
      rw [Op_eq_map, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
      exact le_bot_iff.mp this
    have hF : fittingSubgroup ↥N = ⊥ := by
      have h1 : (fittingSubgroup ↥N).map N.subtype = (pCore p ↥N).map N.subtype := by
        have := H.hFm
        rw [Fm, Op] at this
        exact this
      rw [hpc, Subgroup.map_bot] at h1
      exact (Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective).mp h1
    have hFs : generalizedFitting ↥N = layer ↥N := by
      rw [generalizedFitting, hF, bot_sup_eq]
    have hvL : (⟨v, hvN⟩ : ↥N) ∈ layer ↥N := by
      have := CFSG.centralizer_generalizedFitting_le ↥N
      rw [hFs] at this
      exact this hvC
    have hvF : (⟨v, hvN⟩ : ↥N) ∈ fittingSubgroup ↥N :=
      layer_inf_centralizer_le_fitting ↥N ⟨hvL, hvC⟩
    rw [hF, Subgroup.mem_bot] at hvF
    exact hv1' (congrArg Subtype.val hvF)
  ·
    obtain ⟨K, hK, -⟩ :=
      exists_component_not_le (N := N) (M := ⊥) (fun h => H.hEm (le_bot_iff.mp h))
    have hNR : normalizer ((Op p N : Subgroup G) : Set G) = N :=
      L915.normalizer_eq_of_normalized9 H.ctx H.hN hR (Op_le' p N) (le_normalizer_Op' p N)
    have hY : NN z p ⊤ (zpowers v) :=
      ⟨le_top, (H.hv v hvV hv1').2.1, (H.hv v hvV hv1').2.2.1, (H.hv v hvV hv1').2.2.2⟩
    have hvR : v ∈ normalizer ((Op p N : Subgroup G) : Set G) := hNR.ge hvN
    have hW : IsPGroup p ↥(Op p N ⊔ zpowers v) :=
      (op_isPGroup N).to_sup_of_normal_left'
        (H.ctx.P_pgroup.to_le (Subgroup.zpowers_le.mpr hvP))
        (Subgroup.zpowers_le.mpr hvR)
    obtain ⟨-, hE⟩ := lemma_9_3 h512 G z k S M p H.ctx N (Op p N) (zpowers v) H.hN hNR.le
      (Subgroup.zpowers_le.mpr hvN) hY hW
    set Y' : Subgroup ↥N := pCore p ↥N ⊔ zpowers (⟨v, hvN⟩ : ↥N) with hY'
    have hYmap : Y'.map N.subtype = Op p N ⊔ zpowers v := by
      rw [hY', Subgroup.map_sup, MonoidHom.map_zpowers]
      rfl
    refine no_component_of_Em_bot Y' (by rw [hYmap]; exact hE) K hK ?_
    rw [← Subgroup.le_centralizer_iff]
    refine sup_le ?_ ?_
    · exact L915.pCore_le_centralizer_component hp hK
    · have hKL : K ≤ layer ↥N := le_sSup hK
      exact Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr fun x hx =>
        Subgroup.mem_centralizer_iff.mp hvC x (hKL hx))

theorem false_of_sl2_case_X (hC : Ctx9 G z k S M p) (hXN' : X ≤ N)
    (hXA : X ≤ L915.A1 z M N p) (hO2 : Op 2 N = ⊥) (hXE : ¬ X ≤ centralizer (Em N : Set G))
    {q : ℕ} (hq : Odd q) (h4 : 4 ≤ q)
    (hK : HasSL2Model ↥(ncl (xBar p N (L915.A1 z M N p))) (fun q' => q' = q)) : False := by
  have hp := hC.prime
  have hp2 : p ≠ 2 := hC.odd
  have hO2' : pCore 2 ↥N = ⊥ := by
    have := hO2
    rw [Op_eq_map, Subgroup.map_eq_bot_iff, Subgroup.ker_subtype] at this
    exact le_bot_iff.mp this
  obtain ⟨J, hJ, hXJ⟩ := L915.exists_component_noncentral_of_Em hXN' hXE
  have hJ' : IsComponent (J.map (QuotientGroup.mk' (pCore p ↥N))) :=
    L915.isComponent_map_mk hp CFSG.pCore_normal hJ CFSG.pCore_isPGroup
  have hX₁ : X.subgroupOf N ≤ (L915.A1 z M N p).subgroupOf N := fun x hx => hXA hx
  have hnc : ¬ xBar p N (L915.A1 z M N p) ≤
      centralizer ((J.map (QuotientGroup.mk' (pCore p ↥N)) : Subgroup _) : Set _) :=
    L915.not_le_centralizer_map hp hJ hX₁ hXJ
  have : (ncl (xBar p N (L915.A1 z M N p))).Normal := Subgroup.normalClosure_normal
  have hJK : J.map (QuotientGroup.mk' (pCore p ↥N)) ≤ ncl (xBar p N (L915.A1 z M N p)) :=
    L915.component_le_of_noncentral inferInstance hJ' Subgroup.subset_normalClosure hnc
  exact L915.false_of_sl2_section hp hp2 hO2' hJ hJK hq h4 hK


theorem lemma913a_of (h43E : Prop4_3E) (h512 : IG_5_12) (h118 : IG_11_8) : Lemma913a := by
  intro G _ _ z k S M p X V N H
  by_contra hXE
  have hp := H.ctx.prime
  have hp2 : p ≠ 2 := H.ctx.odd
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hzN : z ∈ N := H.hXN H.hzX
  have hXN' : X ≤ N := le_trans Subgroup.le_normalizer H.hXN
  have hXA : X ≤ L915.A1 z M N p := X_le_A1 H.hXP H.hXc H.hXN
  have hO2 : Op 2 N = ⊥ := L915.lemma9_2a h118 H.ctx H.hXP H.hzX H.hXN
  rcases concl43E_X1 h43E H.ctx H.hN hzN H.hX0 hXA hXE with hb | hc | hd1 | he
  · obtain ⟨n, h3, hK, -⟩ := hb
    exact false_of_sl2_case_X H.ctx hXN' hXA hO2 hXE (q := p ^ n) hodd.pow (by omega) hK
  · exact false_of_V_le_centralizer_layer h512 H
      (V_le_centralizer_layer_of_caseC h118 H hzN hXA hXE hc)
  · exact false_of_d1_X h512 H hzN hXA hXE hd1
  · exact false_of_sl2_case_X H.ctx hXN' hXA hO2 hXE (q := 5) (by decide) (by norm_num) he.1

end Fin

end CFSG.GH74.GLS.Stage2.Bender.Thm2.P911
