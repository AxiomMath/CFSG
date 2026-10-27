module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.MS93.ASC134
public import CFSG.Quasithin.EmptyFaithful.A38c10MSb
public import CFSG.Quasithin.EmptyFaithful.A38c10MSc

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzC4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.S1417
  CFSG.Quasithin.FLc CFSG.Quasithin CFSG.Quasithin.A38c10
open scoped commutatorElement Pointwise

theorem case4_of_msgat_F4 (hMS : MS93.AS_C_1_34_corr_F4) {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]
    {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : Ctx15316 T Mc M V₁ V₂ Yp I L t) (hYY : Yp = Y153 Mc M) (hYpL : Yp ≤ L)
    (hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G))
    (hodd1 : ∀ y ∈ Yp, Odd (orderOf y) → (∀ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ = z) → y = 1)
    {Vp Y₁ Y₂ : Subgroup G} (hVp2 : IsPGroup 2 ↥Vp) (hVpS : Vp ≤ Sgp153 T V₁)
    (hVL : L ≤ Subgroup.normalizer (Vp : Set G)) (hVS : Sgp153 T V₁ ≤ Subgroup.normalizer (Vp : Set G))
    (hY₁ : Y₁ ≤ Yp) (hY₂ : Y₂ ≤ Yp) (hY₁c : ∃ a, Nat.card ↥Y₁ = 2 ^ a * 3)
    (hY₂c : ∃ a, Nat.card ↥Y₂ = 2 ^ a * 3)
    (P : Subgroup G) (ψ : ↥P →* SLt 3) (q : G) (hPL : P ≤ L) (hSLP : Sgp153 T V₁ ⊓ L ≤ P)
    (hSP : ∀ s ∈ Sgp153 T V₁, ∀ p ∈ P, s * p * s⁻¹ ∈ P)
    (hmin : ∀ X : Subgroup G, Sgp153 T V₁ ⊓ L ≤ X → X ≤ L → X ≠ L → Yp ≤ X → ¬ P ≤ X)
    (hYP : Y₁ ≤ P ∨ Y₂ ≤ P) (hψs : Function.Surjective ψ)
    (hψk : ∀ x : ↥P, ψ x = 1 → (x : G) ∈ Sgp153 T V₁ ⊓ L) (hq1 : q ≠ 1)
    (hqP : ∀ a ∈ P, a * q * a⁻¹ = q) (hqK : q ∈ ⁅Vp, oTwoUpper P⁆) :
    MS93.IsC134Case4Corr (perfectCore P ⊔ Sgp153 T V₁) (Sgp153 T V₁) (perfectCore P) := by
  classical
  set S : Subgroup G := Sgp153 T V₁ with hSdef
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hyp : Hyp153 G T Mc M := hh.hyp
  obtain ⟨hLc, hLn, -, -, -, -⟩ := c.conc
  have hLI : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ hLc
  have hLle : L ≤ I := le_of_mem_cComp hLI
  have hSI : S ≤ I := c.facts.sylow.1
  have hS2 : IsPGroup 2 ↥S := hyp.qtfe.sylow.1.to_le inf_le_left
  have hST : S ≤ T := inf_le_left
  have hTM : T ≤ M := hyp.T_le
  have hcharL : CharTwo L :=
    charTwo_of_isSubnormal_of_charTwo c.ctx.charTwo (subnormal_of_mem_cComp hLI)

  have hPsi : MS.PsiData P S ψ := ⟨hS2, hψs, fun x hx => (hψk x hx).1⟩
  set K : Subgroup G := perfectCore P with hKdef
  have hKP : K ≤ P := perfectCore_le P
  have hKL : K ≤ L := hKP.trans hPL
  have hKI : K ≤ I := hKL.trans hLle
  have hSN : S ≤ Subgroup.normalizer (P : Set G) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨fun hp => hSP s hs p hp, fun hp => ?_⟩
    have h1 := hSP s⁻¹ (S.inv_mem hs) _ hp
    have e : s⁻¹ * (s * p * s⁻¹) * s⁻¹⁻¹ = p := by group
    rwa [e] at h1
  have hSK : S ≤ Subgroup.normalizer (K : Set G) := fun s hs =>
    normalizer_le_normalizer_perfectCore P (hSN hs)
  have hsupeq : K ⊔ S = P ⊔ S := MS.perfectCore_sup_eq hPsi
  have hPKS : P ≤ K ⊔ S := MS.le_perfectCore_sup hPsi
  have hoT : oTwoUpper P ≤ K := MS.oTwoUpper_le_perfectCore hPsi
  have hset : ((K ⊔ S : Subgroup G) : Set G) = (K : Set G) * (S : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K S hSK
  obtain ⟨α, hα⟩ := MS.exists_isModO2Surj hPsi
  have hq3 : IsLnTwoQuot K 3 :=
    ⟨(QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)⟩
  have hLie := SBd7.isRankTwoLie2Derived_of_modO2 α hα.1 hα.2
  have hcomp : K ∈ cComp (K ⊔ S) := SBd5.mem_cComp_sup' (MS.perfectCore_mem_cComp_self hPsi) hSK

  have hLSN : L ⊔ S ≤ Subgroup.normalizer (L : Set G) :=
    sup_le (fun x hx => Subgroup.le_normalizer hx) hSL
  have hsylLS : IsSylowTwoOf S (L ⊔ S) :=
    SBd7.isSylowTwoOf_of_le_of_le' c.facts.sylow le_sup_right (sup_le hLle hSI)
  have hOLS : pCoreOf 2 L ≤ S := by
    have hOL : pCoreOf 2 L ≤ pCoreOf 2 (L ⊔ S) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans le_sup_left)
        (fun g hg => normalizer_le_normalizer_pCoreOf 2 L (hLSN hg)) (pCoreOf_isPGroup 2 L)
    exact hOL.trans (pCoreOf_le_of_isSylowTwoOf hsylLS)
  have hOP : pCoreOf 2 L ≤ P := fun x hx => hSLP ⟨hOLS hx, pCoreOf_le 2 L hx⟩
  have hchar : CharTwo (K ⊔ S) := by
    rw [hsupeq]
    exact MS.charTwo_sup_of_le hcharL hS2 hSL hPL (hOP.trans le_sup_left)

  obtain ⟨y, hyYp, hyP, hy3⟩ := MS.exists_order_three hY₁ hY₂ hY₁c hY₂c hYP
  have hyodd : Odd (orderOf y) := by rw [hy3]; decide
  have hyK : y ∈ K := MS.mem_perfectCore_of_odd hPsi hyP hyodd
  have hy1 : y ≠ 1 := fun h => by rw [h, orderOf_one] at hy3; omega
  have hmove : ∃ z ∈ quasithinOmegaOneCenter T, y * z * y⁻¹ ≠ z := by
    by_contra hcon
    push Not at hcon
    exact hy1 (hodd1 y hyYp hyodd hcon)
  have hV' : ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ K)⁆ ≠ ⊥ := by
    obtain ⟨z, hzZ, hzy⟩ := hmove
    have hzV : z ∈ VZ T M := hyp.Z_le_VZ hzZ
    have hyO : y ∈ oTwoUpper (Y153 Mc M ⊓ K) :=
      mem_oTwoUpper_of_odd ⟨by rw [← hYY]; exact hyYp, hyK⟩ hyodd
    intro hb
    have hc' : ⁅z, y⁆ ∈ ⁅VZ T M, oTwoUpper (Y153 Mc M ⊓ K)⁆ :=
      Subgroup.commutator_mem_commutator hzV hyO
    rw [hb, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc'
    apply hzy
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [← hc']
      _ = z := by group

  have hKM : ¬ K ≤ M := by
    intro hKM
    have hSM : S ≤ M := hST.trans hTM
    have hPM : P ≤ M := hPKS.trans (sup_le hKM hSM)
    have hLM : ¬ L ≤ M := fun h => hLn (le_inf h hLle)
    refine hmin (M ⊓ L) (fun x hx => ⟨hSM hx.1, hx.2⟩) inf_le_right
      (fun h => hLM (h.symm.le.trans inf_le_left)) ?_ (le_inf hPM hPL)
    exact le_inf (by rw [hYY]; exact Y153_le Mc M) hYpL

  have hMSp : IsMSPair (K ⊔ S) S :=
    MS.isMSPair_sup_S_of_K c hKI hSK hchar hcomp hLie hKM hV'
  have hKSI : K ⊔ S ≤ I := sup_le hKI hSI
  have hsyl : IsSylowTwoOf S (K ⊔ S) :=
    SBd7.isSylowTwoOf_of_le_of_le' c.facts.sylow le_sup_right hKSI
  obtain ⟨i, hi⟩ := hMS G (K ⊔ S) S K hMSp hcomp hset
    ⟨1, ZMod 2, inferInstance, inferInstance, α, by simp, hα⟩

  have hVpH : Vp ≤ pCoreOf 2 (K ⊔ S) :=
    le_pCoreOf_of_le_normalizer 2 (hVpS.trans le_sup_right) (sup_le (hKL.trans hVL) hVS) hVp2
  have hqQ : q ∈ c134Q (K ⊔ S) K := Subgroup.commutator_mono hVpH hoT hqK
  have hqfix : ∀ a ∈ K, a * q * a⁻¹ = q := fun a ha => hqP a (hKP ha)
  have hOSyl : pCoreOf 2 (K ⊔ S) ≤ S := pCoreOf_le_of_isSylowTwoOf hsyl
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := fun l hl =>
    le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_left hl)
  have hSO : S ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ S) : Set G) := fun s hs =>
    le_normalizer_pCoreOf 2 (K ⊔ S) (Subgroup.mem_sup_right hs)
  have hQO : c134Q (K ⊔ S) K ≤ pCoreOf 2 (K ⊔ S) := by
    refine Subgroup.commutator_le.mpr fun x hx l hl => ?_
    have h1 : l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 (K ⊔ S) :=
      (Subgroup.mem_normalizer_iff.mp (hKO hl) _).mp ((pCoreOf 2 (K ⊔ S)).inv_mem hx)
    have e : x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) := by group
    rw [commutatorElement_def, e]
    exact (pCoreOf 2 (K ⊔ S)).mul_mem hx h1
  have hQS : c134Q (K ⊔ S) K ≤ S := hQO.trans hOSyl
  have hKQ : K ≤ Subgroup.normalizer (c134Q (K ⊔ S) K : Set G) := fun l hl =>
    SBd5.mem_normalizer_commutator_of (hKO hl) (Subgroup.le_normalizer hl)
  have hSQ : S ≤ Subgroup.normalizer (c134Q (K ⊔ S) K : Set G) := fun s hs =>
    SBd5.mem_normalizer_commutator_of (hSO hs) (hSK hs)
  match i, hi with
  | 0, hi => exact hi.elim
  | 1, hi =>
    exact (MS.false_of_case_one_two_three (show IsC134Case 1 (K ⊔ S) S K from hi) (Or.inl rfl) hqQ
      hq1 hqfix).elim
  | 2, hi =>
    exact (MS.false_of_case_one_two_three (show IsC134Case 2 (K ⊔ S) S K from hi)
      (Or.inr (Or.inl rfl)) hqQ hq1 hqfix).elim
  | 3, hi =>
    exact (MS.false_of_case_one_two_three (show IsC134Case 3 (K ⊔ S) S K from hi)
      (Or.inr (Or.inr rfl)) hqQ hq1 hqfix).elim
  | 4, hi => exact hi
  | 5, hi =>
    exfalso
    obtain ⟨-, h5⟩ := hi
    obtain ⟨hΩ, -⟩ := h5 S hsyl le_rfl
    have hV₁T : V₁ ≤ T := hh.decomp.le₁.trans hyp.VZ_le_T
    have hZΩ : quasithinOmegaOneCenter T ≤ omegaOneCenterOf S := by
      refine Subgroup.closure_mono ?_
      rintro z ⟨⟨hzT, hzC⟩, hz2⟩
      have hzS : z ∈ S := ⟨hzT, Subgroup.centralizer_le_normalizer (V₁ : Set G)
        (Subgroup.centralizer_le hV₁T hzC)⟩
      exact ⟨⟨hzS, Subgroup.centralizer_le hST hzC⟩, hz2⟩
    refine hy1 (hodd1 y hyYp hyodd fun z hz => ?_)
    have hzC := (hΩ (hZΩ hz)).2
    have h1 := Subgroup.mem_centralizer_iff.mp hzC y (Subgroup.mem_sup_left hyK)
    calc y * z * y⁻¹ = z * y * y⁻¹ := by rw [h1]
      _ = z := by group
  | n + 6, hi => exact hi.elim

end CFSG.Quasithin.SzC4
