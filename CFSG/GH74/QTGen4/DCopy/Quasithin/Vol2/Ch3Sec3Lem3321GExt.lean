module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3321Steps
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Statements
public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Stmt3313LT
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321GExt
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3321WH

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped IsMulCommutative

namespace L3321

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L D : Subgroup G}

theorem exists_alpha_ext_F4 (h9 : Stmt3_3_9) (h14 : Stmt3_3_14_F4) (hGA : GriessAllModelsStatement)
    (h : Hyp331 G T M L D)
    (e : ↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2))
    [IsMulCommutative ↥(vPlus L T)] (hmod : Mod3321Ext T L) :
    ∃ α : ↥L →* SL4, Function.Surjective α ∧ α.ker = CFSG.pCore 2 ↥L ∧
      ((T ⊓ L).subgroupOf L).map α = FLc.Ut 4 ∧
      L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) = L3316.liftPre α P2 := by
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨hVe, hLV, -, -, -, -, -⟩ := setting_facts h hTL
  obtain ⟨Z₀, hZ₀, -, π, hπ⟩ := hmod
  have hV2 : ∀ w : ↥(vPlus L T), w ^ 2 = 1 := fun w => Subtype.ext (by simpa using hVe.2 w w.2)
  obtain ⟨D₀⟩ := FLc.vmodelExtSq hπ (fun g hg z hz => (hZ₀.trans inf_le_left) hz g hg)
  have hcard : Nat.card ↥(autOn L (vPlus L T)) = 20160 := by
    rw [Nat.card_congr e.toEquiv, Ln2.card_specialLinear 4 (Or.inl rfl)]
    rfl
  have : Nontrivial ↥(autOn L (vPlus L T)) := Finite.one_lt_card_iff_nontrivial.1
    (by rw [hcard]; norm_num)
  obtain ⟨k, hk⟩ := exists_ne (1 : ↥(autOn L (vPlus L T)))
  obtain ⟨g₀, hg₀⟩ := FLc.rhoOf_surj hπ.1 k k.2
  have hne : ∃ g, FLc.rhoOf π g ≠ 1 := ⟨g₀, by rw [hg₀]; exact fun h1 => hk (Subtype.ext h1)⟩
  have hS := L3317.isSylowTwoOf_inf h hTL
  obtain ⟨h', hinj, hr1, hr2, hU⟩ := exists_normalized_eq hVe hLV hS (by norm_num)
    (FLc.rhoOf π) (FLc.rhoOf_surj hπ.1) (FLc.rhoOf_mem π) hne
  have D₁ := D₀.rtwist h'
  obtain ⟨α, hαs, hαk, hαU, hαv⟩ := exists_alpha_of_rho h hGA hTL e hinj hr1 hr2 hU
  refine ⟨α, hαs, hαk, hαU, ?_⟩
  have hP2C :
      L3316.liftPre α P2 ≤ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    rintro _ ⟨l, hl, rfl⟩
    refine mem_centralizer_of_fix h9 h hML l.2 fun v hvZ hvW => ?_
    have hvc : v ∈ commV (autOn L (vPlus L T)) := by
      rw [Ln2.commV_autOn_eq h]
      exact hvW
    have key := FLc.fixQ_of_model D₁ hV2 (by norm_num) (c := 2)
      (fun a ha i hi hic => FLc.fix_extSq4 a ha i hi hic) hvc
      (fun s hs => fix_of_mem_autOn_inf (by rw [← hU]; exact ⟨s, hs, rfl⟩) hvZ) (α l) hl
    rw [hαv l] at key
    exact key
  set Pz : Subgroup SL4 :=
    ((L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)).subgroupOf L).map α with hPz
  have hUPz : FLc.Ut 4 ≤ Pz := by
    rw [← hαU]
    refine Subgroup.map_mono (Subgroup.subgroupOf_mono L fun t ht => ⟨ht.2, ?_⟩)
    exact CFSG.QuasithinUnique.L246C127.le_centralizer_omegaOneCenter T ht.1
  have hP2Pz : P2 ≤ Pz := by
    intro g hg
    obtain ⟨l, rfl⟩ := hαs g
    exact ⟨l, Subgroup.mem_subgroupOf.2 (hP2C ⟨l, hg, rfl⟩), rfl⟩
  have hkerC : ∀ l : ↥L, α l = 1 →
      (l : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
    intro l hl
    refine mem_centralizer_of_fix h9 h hML l.2 fun v _ _ => ?_
    have key := hαv l
    rw [hl, map_one] at key
    rw [← key, MulAut.one_apply]
  have hcuts : FLc.cuts Pz = {2} := by
    have h1 : FLc.cuts Pz ⊆ {2} := by
      have := hP2Pz
      rw [FLc.eq_QI_cuts hUPz] at this
      exact (FLc.QI_le_QI_iff fun j hj => FLc.isNode_of_mem_cuts hj).1 this
    refine Set.Subset.antisymm h1 fun i hi => ?_
    rw [Set.mem_singleton_iff] at hi
    subst hi
    by_contra h2
    have hempty : FLc.cuts Pz = ∅ := by
      ext j
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hj
      have := h1 hj
      rw [Set.mem_singleton_iff] at this
      subst this
      exact h2 hj
    apply inf_centralizer_ne hML e
    intro l hl
    have hlPz : α ⟨l, hl⟩ ∈ Pz := by
      rw [FLc.eq_QI_cuts hUPz, hempty]
      show α ⟨l, hl⟩ ∈ flagStabilizer 4 (ZMod 2) ∅
      rw [flagStabilizer_empty]
      exact Subgroup.mem_top _
    obtain ⟨c, hc, hcl⟩ := hlPz
    have h3 := hkerC (c⁻¹ * ⟨l, hl⟩) (by rw [map_mul, map_inv, hcl, inv_mul_cancel])
    have h4 : (c : G) ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      Subgroup.mem_subgroupOf.1 hc
    have e1 : l = (c : G) * ((c⁻¹ * ⟨l, hl⟩ : ↥L) : G) := by simp
    rw [e1]
    exact (Subgroup.mul_mem _ h4 h3).2
  have hPzeq : Pz = P2 := by
    rw [FLc.eq_QI_cuts hUPz, hcuts]
  refine le_antisymm (fun x hx => ?_) hP2C
  have h1 : α ⟨x, hx.1⟩ ∈ Pz := ⟨⟨x, hx.1⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  rw [hPzeq] at h1
  exact ⟨⟨x, hx.1⟩, h1, rfl⟩

theorem step3_3_21gExt_of_F4 (h9 : Stmt3_3_9) (h13 : Stmt3_3_13LT_F4) (h14 : Stmt3_3_14_F4)
    (hGA : GriessAllModelsStatement) (hd : Step3_3_21d_F4) :
    ∀ (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T M L D : Subgroup G), Hyp331 G T M L D →
      Nonempty (↥(autOn L (vPlus L T)) ≃* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2)) →
      ∀ _ : IsMulCommutative ↥(vPlus L T), Mod3321Ext T L → InducesInnerOn T L := by
  intro G _ _ T M L D h ⟨e⟩ hc hmod
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hout
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  obtain ⟨α, hαs, hαk, hαU, hCZ⟩ := exists_alpha_ext_F4 h9 h14 hGA h e hmod
  have hW := nonempty_wreath hαs hαk hTL h.sylow.1 hαU hout
  rw [← hCZ] at hW
  set H := L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ⊔ T with hH
  have hInH : InH T H := by
    refine ⟨le_sup_right, fun hbot => h.toSetup331.pCoreOf_ne_bot ?_⟩
    have hOT : pCoreOf 2 (L ⊔ T) ≤ T :=
      EscapingLocal.pCoreOf_le_of_isSylowTwoOf h.toSetup331.isSylowTwoOf
    have hle : pCoreOf 2 (L ⊔ T) ≤ pCoreOf 2 H :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans le_sup_right)
        ((sup_le_sup_right (inf_le_left :
          L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) ≤ L) T).trans
          (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ T)))
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))
    rw [hbot] at hle
    exact le_bot_iff.1 hle
  have hDH := h13 G T M L D H h hInH (sup_le_sup_right inf_le_left T) hW
  have hDR : D ≤ Subgroup.normalizer ((pCoreOf 2 H) : Set G) := fun d hd =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 H (hDH hd)
  exact Hyp331.not_D_le h (hDR.trans (hd G T M L D h ⟨e⟩ ⟨hc, Or.inl hmod⟩))

end L3321

end CFSG.Quasithin.H13
