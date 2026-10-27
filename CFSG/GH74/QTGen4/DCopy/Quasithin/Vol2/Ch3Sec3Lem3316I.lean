module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch3Sec3Lem3316E
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParGen
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParL3
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316B
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316C
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316D
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316H

public section
namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)
open CFSG.QuasithinUnique.Setup.X7a CFSG.QuasithinUnique.Vol2Native.A312L
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (unitriangular)
open scoped IsMulCommutative

namespace L3316

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

theorem sl3_config_F4
    {T M L D : Subgroup G} (h : Hyp331 G T M L D) (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat)
    (h51 : AsB51) (h10 : Stmt3_3_10) (h14 : Stmt3_3_14_F4) (h15 : Step3_3_15RB_F4) {n : ℕ}
    (hn : 1 < n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (e : ↥(autOn L (vPlus L T)) ≃* ↥(StatedSL 3 K)) {F : Type} [Field F] [Fintype F]
    (hF : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) :
    ∃ (α₂ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F) (j : Fin 2) (Kc : Subgroup G),
      Function.Surjective α₂ ∧ α₂.ker = CFSG.pCore 2 ↥L ∧ Nat.card F = 4 ∧
      T ≤ Subgroup.normalizer (liftPre α₂ (Q3 F j) : Set G) ∧
      liftCore α₂ (Q3 F j) ∈ lFamilyOf L T ∧ InducesInnerOn T (liftCore α₂ (Q3 F j)) ∧
      pCoreOf 2 (liftCore α₂ (Q3 F j) ⊔ T ⊔ D) ≠ ⊥ ∧
      Kc ∈ cComp (liftCore α₂ (Q3 F j) ⊔ T ⊔ D) ∧ liftCore α₂ (Q3 F j) ≤ Kc ∧
      liftCore α₂ (Q3 F j) ⊔ T ⊔ D ≤ Subgroup.normalizer (Kc : Set G) ∧
      A312C15 (modO2Image (liftCore α₂ (Q3 F j) ⊔ T ⊔ D) (liftCore α₂ (Q3 F j)))
        (modO2Image (liftCore α₂ (Q3 F j) ⊔ T ⊔ D) Kc) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hML, hMN⟩ := h14 G T M L D h
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans hMN
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLTV : L ⊔ T ≤ Subgroup.normalizer (vPlus L T : Set G) := hred.2.2.2.1
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hLTV
  have hTV : T ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_right.trans hLTV
  have hS₀ : IsSylowTwoOf (T ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal h.toSetup331.isSylowTwoOf le_sup_left
      (sup_le Subgroup.le_normalizer hTL)
  have hFn : Nat.card F = 2 ^ n := by rw [Nat.card_eq_fintype_card, hF]
  have hn2 : 2 ≤ n := hn
  have : CharP F 2 := SzN15.charP_two_of_card hFn
  have hF4 : ∃ s : Finset F, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hF4' : 4 ≤ Nat.card F := by
    rw [hFn]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  obtain ⟨hVc, m, K', _, _, hK', hmod⟩ := sl3_module h h38 h39 h51 h10 hTL hn hK e
  have hgood := goodCoatom_sl3 hML hLV (Setup.isSylowTwoOf_autOn hS₀ hLV) hK' hmod
  have hlie : IsSL3Quot L ∨ IsSp4Quot L :=
    Or.inl ⟨n, F, inferInstance, inferInstance, hn, hF,
      ⟨(QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα.1)⟩⟩
  set α₁ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F :=
    (specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp α with hα₁
  have hα₁s : Function.Surjective α₁ := by
    rw [hα₁, MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hα.1
  have hα₁k : α₁.ker = CFSG.pCore 2 ↥L := by
    rw [hα₁, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hα.2]
  have hP₀ : IsSylowTwoOf ((T ⊓ L).subgroupOf L) ⊤ := by
    refine ⟨le_top, hS₀.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS₀.1).symm, fun h2 => ?_⟩
    apply hS₀.2.2
    rwa [show (((T ⊓ L).subgroupOf L).subgroupOf ⊤).index = ((T ⊓ L).subgroupOf L).index from
      Subgroup.relIndex_top_right _] at h2
  have hU₁ : IsSylowTwoOf (((T ⊓ L).subgroupOf L).map α₁) ⊤ := by
    have h1 := L3312.isSylowTwoOf_map_range α₁ hP₀
    rwa [MonoidHom.range_eq_top.mpr hα₁s] at h1
  have hU₀ : IsSylowTwoOf (unitriangular 3 F) ⊤ := SzN2.isSylowTwoOf_unitriangular (by norm_num)
  obtain ⟨k, -, hk⟩ := (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₁).exists_mem_conj
    (Setup.X6.isSylowTwoOf_iff_isSylowOf.1 hU₀)
  set α₂ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) F :=
    (MulAut.conj k).toMonoidHom.comp α₁ with hα₂def
  have hα₂ : Function.Surjective α₂ := by
    rw [hα₂def, MonoidHom.coe_comp]
    exact (MulEquiv.surjective _).comp hα₁s
  have hker : α₂.ker = CFSG.pCore 2 ↥L := by
    rw [hα₂def, MonoidHom.ker_comp_of_injective _ _ (MulEquiv.injective _), hα₁k]
  have hkp : IsPGroup 2 ↥α₂.ker := by
    rw [hker]
    exact CFSG.pCore_isPGroup
  have hmapU : ((T ⊓ L).subgroupOf L).map α₂ = unitriangular 3 F := by
    rw [hα₂def, ← Subgroup.map_map]
    ext x
    rw [Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    exact (hk x).symm
  have hR := Rk2.rank2Pkg_sl3 (K := F) hFn hn2
  have hP : ∀ j : Fin 2, IsMaxParabolic2 L (liftPre α₂ (Q3 F j)) ∧
      L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ≤ liftPre α₂ (Q3 F j) := fun j =>
    isMaxParabolic2_liftPre hS₀ hα₂ (hR.covBy j) (by rw [hmapU]; exact hR.norm j)
  have hTP : ∀ j : Fin 2, T ≤ Subgroup.normalizer (liftPre α₂ (Q3 F j) : Set G) := fun j =>
    le_normalizer_parabolic hlie hS₀ hLV hTL hTV hgood (hP j).1 (hP j).2
  have hY : ∀ j : Fin 2, liftCore α₂ (Q3 F j) ∈ lFamilyOf L T := fun j =>
    liftCore_mem_lFamilyOf h.sylow h.toSetup331.pCoreOf_ne_bot hα₂ hkp (hR.levi j) (hTP j)
  have hf : ∀ j : Fin 2, ∃ f : ↥(liftCore α₂ (Q3 F j)) →* Matrix.SpecialLinearGroup (Fin 2) F,
      Function.Surjective f ∧ IsPGroup 2 ↥f.ker := fun j =>
    exists_hom_sl2_of hα₂ hkp (blk3_surjective hF4 j) (blk3_ker_isPGroup ⟨n, hFn⟩ j)
  have htype : ∀ j : Fin 2,
      L3312.Type3312R (↥(liftCore α₂ (Q3 F j)) ⧸ CFSG.pCore 2 ↥(liftCore α₂ (Q3 F j))) := by
    intro j
    obtain ⟨f, hfs, hfk⟩ := hf j
    exact Or.inl ⟨n, hn2, isPSL2_quot_of_hom hn2 hFn hfs hfk⟩
  have hO : ∀ j : Fin 2, pCoreOf 2 (liftCore α₂ (Q3 F j) ⊔ T ⊔ D) ≠ ⊥ := by
    intro j
    obtain ⟨f, hfs, hfk⟩ := hf j
    exact pCoreOf_sup_ne_bot h10 h (fun t ht => mem_normalizer_perfectCore (hTP j ht))
      (hY j).2.2.2.2 hF4' hfs hfk
  have hkT : α₂.ker.map L.subtype ≤ T := by
    rw [hker]
    show pCoreOf 2 L ≤ T
    exact (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS₀).trans inf_le_left
  have hgen : perfectCore (Q3 F 0) ⊔ perfectCore (Q3 F 1) ⊔ (T.subgroupOf L).map α₂ = ⊤ := by
    rw [← Subgroup.inf_subgroupOf_right, hmapU]
    exact hR.sup_perfectCore_eq_top
  have hLT : L ⊔ T = liftCore α₂ (Q3 F 0) ⊔ liftCore α₂ (Q3 F 1) ⊔ T :=
    le_antisymm (sup_le (le_sup_liftCore hα₂ hkT hgen) le_sup_right)
      (sup_le (sup_le ((liftCore_le _ _).trans le_sup_left) ((liftCore_le _ _).trans le_sup_left))
        le_sup_right)
  obtain ⟨Y, hYY, -, hPSL, hinn, Kc, hKc, hYK, -, hHK, hc15⟩ :=
    h15 G T M L D _ _ h (hY 0) (hY 1) hLT (hO 0) (hO 1) (htype 0) (htype 1)
  have hcase : ∀ j : Fin 2, Y = liftCore α₂ (Q3 F j) → Nat.card F = 4 := by
    intro j hYj
    subst hYj
    obtain ⟨f, hfs, hfk⟩ := hf j
    have h1 := GoldS146R.card_isPSL_two_two hPSL
    have h2 := GoldS146R.card_isPSL_two_two (isPSL2_quot_of_hom hn2 hFn hfs hfk)
    rw [h1] at h2
    rw [hFn]
    rcases Nat.lt_or_ge n 3 with h3 | h3
    · obtain rfl : n = 2 := by omega
      rfl
    · have h8 : 8 ≤ 2 ^ n :=
        calc 8 = 2 ^ 3 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h3
      have h63 : 63 ≤ (2 ^ n) ^ 2 - 1 := by
        have : 64 ≤ (2 ^ n) ^ 2 := by nlinarith
        omega
      have := Nat.mul_le_mul h8 h63
      omega
  rcases hYY with rfl | rfl
  · exact ⟨α₂, 0, Kc, hα₂, hker, hcase 0 rfl, hTP 0, hY 0, hinn, hO 0, hKc, hYK, hHK, hc15⟩
  · exact ⟨α₂, 1, Kc, hα₂, hker, hcase 1 rfl, hTP 1, hY 1, hinn, hO 1, hKc, hYK, hHK, hc15⟩

end L3316

end CFSG.Quasithin.H13
