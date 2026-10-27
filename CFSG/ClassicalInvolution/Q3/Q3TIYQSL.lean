module

public import CFSG.ClassicalInvolution.Q3.Q3TIYPKind
public import CFSG.ClassicalInvolution.Q3.Q3P21L1
public import CFSG.Sporadic.Schreier.J4SProfileNode
public import CFSG.ClassicalInvolution.Q3.Q3TIYSmall

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.Open hiding StatedLieTag StatedLieAdmissible
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.ClassicalInvolution.Q3.Q3W
  CFSG.ClassicalInvolution.Q3.Q3TC CFSG.ClassicalInvolution.Q3.Q3TIV
  CFSG.ClassicalInvolution.Q3.Q3TLK CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Models
  CFSG.ClassicalInvolution.ModelFacts.TG3
open CFSG.ClassicalInvolution.Phan (blockMat_apply)
open CFSG.ClassicalInvolution.RouteD.TwinY (TwinElt TwinElt.u IsTwinAt TwinRow TwinDatumOn)
open scoped MatrixGroups

local notation "𝔽₃" => GaloisField 3 1

@[expose] def TwinRowSL4 (t : StatedLieTag) (n : ℕ) : Prop := t = .PSL ∧ n = 4

theorem TwinRowSL4.twinRow {t : StatedLieTag} {n : ℕ} (h : TwinRowSL4 t n) : TwinRow t n := by
  obtain ⟨rfl, rfl⟩ := h
  exact Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)

section Matrix

noncomputable def sl4TransvT : SL(2, 𝔽₃) := ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩

noncomputable def sl4Transv : SL(4, 𝔽₃) := blockSL 𝔽₃ 4 2 0 (by omega) sl4TransvT

theorem coe_sl4Transv : (sl4Transv : Matrix (Fin 4) (Fin 4) 𝔽₃) =
    !![1, 1, 0, 0; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1] := by
  have h := coe_blockSL (K := 𝔽₃) (m := 4) (k := 2) (i := 0) (by omega) sl4TransvT
  show ((blockSL 𝔽₃ 4 2 0 (by omega) sl4TransvT : SL(4, 𝔽₃)) :
    Matrix (Fin 4) (Fin 4) 𝔽₃) = _
  rw [h]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [blockMat_apply, sl4TransvT]

theorem sl4Transv_mem_rootSL2 : sl4Transv ∈ rootSL2 𝔽₃ (show 2 ≤ 4 by norm_num) := ⟨_, rfl⟩

theorem false_of_comm_sl4Transv (U : Matrix (Fin 4) (Fin 4) 𝔽₃)
    (hc : U * (sl4Transv : Matrix (Fin 4) (Fin 4) 𝔽₃) =
      (sl4Transv : Matrix (Fin 4) (Fin 4) 𝔽₃) * U) (h2 : U * U = -1) : False := by
  rw [coe_sl4Transv] at hc
  have h10 := congrFun (congrFun hc 1) 1
  have h20 := congrFun (congrFun hc 2) 1
  have h30 := congrFun (congrFun hc 3) 1
  have e00 := congrFun (congrFun h2 0) 0
  simp [Matrix.mul_apply, Fin.sum_univ_four] at h10 h20 h30 e00
  rw [h10, h20, h30] at e00
  exact mul_self_ne_neg_one_three (U 0 0) (by simpa using e00)

end Matrix


theorem sl4_not_centralizes3 {U : SL(4, 𝔽₃)}
    (hU : ((U * U : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) = -1) {S : Subgroup SL(4, 𝔽₃)}
    (hS : S ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D)
    (hc : ∀ s ∈ S, U * s = s * U) : False := by
  have hL := RouteD.Exotic.fundamentalSubgroups_psl_eq (p := 3) (f := 1) (m := 3) (by omega)
  have hS' : S ∈ longRootSet (K := 𝔽₃) (by omega : 2 ≤ 3 + 1) := by
    rw [← hL]
    exact hS
  obtain ⟨i, g, hSg, -⟩ := hS'
  have hs : g * sl4Transv * g⁻¹ ∈ S := by
    rw [hSg]
    exact Subgroup.mem_map.mpr ⟨sl4Transv, sl4Transv_mem_rootSL2, by simp [MulAut.conj_apply]⟩
  have h1 : (g⁻¹ * U * g) * sl4Transv = sl4Transv * (g⁻¹ * U * g) := by
    have := hc _ hs
    calc (g⁻¹ * U * g) * sl4Transv = g⁻¹ * (U * (g * sl4Transv * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * sl4Transv * g⁻¹) * U) * g := by rw [this]
      _ = sl4Transv * (g⁻¹ * U * g) := by group
  have h2 : ((g⁻¹ * U * g) * (g⁻¹ * U * g) : SL(4, 𝔽₃)) = g⁻¹ * (U * U) * g := by group
  refine false_of_comm_sl4Transv ((g⁻¹ * U * g : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) ?_ ?_
  · have := congrArg (fun A : SL(4, 𝔽₃) => (A : Matrix (Fin 4) (Fin 4) 𝔽₃)) h1
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using this
  · rw [← Matrix.SpecialLinearGroup.coe_mul, h2, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hU, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul,
      ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel]
    simp


theorem twinMFNotCentralizing3_psl4
    {R R' : Subgroup SL(4, 𝔽₃)}
    {x x' : SL(4, 𝔽₃)}
    (hd : TwinDatumOn .PSL (modelUniv .PSL 4 3 1 Nat.prime_three) R R' x x')
    {a a' : SL(4, 𝔽₃)} (ha : a ∈ R) (ha' : a' ∈ R')
    (hsq : a * a * x⁻¹ ∈ Subgroup.center SL(4, 𝔽₃))
    (hsq' : a' * a' * x'⁻¹ ∈ Subgroup.center SL(4, 𝔽₃))
    {S : Subgroup SL(4, 𝔽₃)}
    (hS : S ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D)
    (hc : ∀ s ∈ S, (a * a') * s = s * (a * a')) : False := by
  have hadm : StatedLieAdmissible .PSL 4 3 1 := Q3TC.statedLieAdmissible_sl4_three
  have hnc := fundNoncentral_model3 (t := .PSL) (n := 4) trivial hadm (by decide)
  obtain ⟨e₁⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSL)
    (n := 4) (by norm_num) trivial hadm (by decide) (by decide) hd.mem
  obtain ⟨e₂⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := 3) (t := .PSL)
    (n := 4) (by norm_num) trivial hadm (by decide) (by decide) hd.mem'
  have hx : x = Asc77.sl2Inv e₁ := eq_sl2Inv_of_central3 e₁ hd.hx hd.cx hd.nx
  have hx' : x' = Asc77.sl2Inv e₂ := eq_sl2Inv_of_central3 e₂ hd.hx' hd.cx' hd.nx'
  have h₁ : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R x := by
    rw [hx]
    exact isLongRootSL2_sl2Inv_four hd.mem e₁
  have h₂ : IsLongRootSL2 (show 2 ≤ 4 by norm_num) R' x' := by
    rw [hx']
    exact isLongRootSL2_sl2Inv_four hd.mem' e₂
  have hxx : x * x = 1 := h₁.mul_self
  have hxx' : x' * x' = 1 := h₂.mul_self
  have hne : x ≠ x' := Q3P21.twinDatum_ne_psl4 hd
  have hrat : (x : Matrix (Fin 4) (Fin 4) 𝔽₃) = -(x' : Matrix (Fin 4) (Fin 4) 𝔽₃) := by
    rcases eq_or_coe_eq_neg_of_central_ratio (by norm_num : 1 ≤ 4) hxx' hxx hd.same with h | h
    · exact absurd h hne
    · exact h
  have haa : a * a = x := by
    have hmem : a * a * x⁻¹ ∈ R :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ha ha) (Subgroup.inv_mem _ hd.hx)
    exact mul_inv_eq_one.mp (hnc R hd.mem _ hmem hsq)
  have haa' : a' * a' = x' := by
    have hmem : a' * a' * x'⁻¹ ∈ R' :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ ha' ha') (Subgroup.inv_mem _ hd.hx')
    exact mul_inv_eq_one.mp (hnc R' hd.mem' _ hmem hsq')
  have hcomm : a * a' = a' * a := hd.comm a ha a' ha'
  have hU2 : (a * a') * (a * a') = x * x' := by
    calc (a * a') * (a * a') = a * (a' * a) * a' := by group
      _ = a * (a * a') * a' := by rw [← hcomm]
      _ = (a * a) * (a' * a') := by group
      _ = x * x' := by rw [haa, haa']
  have hU : (((a * a') * (a * a') : SL(4, 𝔽₃)) : Matrix (Fin 4) (Fin 4) 𝔽₃) = -1 := by
    rw [hU2, Matrix.SpecialLinearGroup.coe_mul]
    have h' : (x' : Matrix (Fin 4) (Fin 4) 𝔽₃) = -(x : Matrix (Fin 4) (Fin 4) 𝔽₃) := by
      rw [hrat, neg_neg]
    rw [h', Matrix.mul_neg, ← Matrix.SpecialLinearGroup.coe_mul, hxx,
      Matrix.SpecialLinearGroup.coe_one]
  exact sl4_not_centralizes3 hU hS hc

theorem card_fund_centralizing3_psl4
    {R R' : Subgroup SL(4, 𝔽₃)}
    {x x' ã ã' : SL(4, 𝔽₃)}
    (hd : TwinDatumOn .PSL (modelUniv .PSL 4 3 1 Nat.prime_three) R R' x x') (hãR : ã ∈ R)
    (hã'R : ã' ∈ R')
    (hsq : ã * ã * x⁻¹ ∈ Subgroup.center SL(4, 𝔽₃))
    (hsq' : ã' * ã' * x'⁻¹ ∈ Subgroup.center SL(4, 𝔽₃)) :
    Nat.card {S : Subgroup SL(4, 𝔽₃) //
      S ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D ∧
        S ≤ Subgroup.centralizer ({ã * ã'} :
          Set SL(4, 𝔽₃))} = 0 := by
  have : IsEmpty {S : Subgroup SL(4, 𝔽₃) //
      S ∈ fundamentalSubgroups .PSL (modelUniv .PSL 4 3 1 Nat.prime_three).D ∧
        S ≤ Subgroup.centralizer ({ã * ã'} :
          Set SL(4, 𝔽₃))} :=
    ⟨fun ⟨S, hS, hle⟩ => twinMFNotCentralizing3_psl4 hd hãR hã'R hsq hsq' hS fun s hs =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hle hs)).symm⟩
  exact Nat.card_of_isEmpty

section Setup

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {K T : Subgroup G} {z : G}

theorem rank_setup3_sl4 (h3 : OddThreeFreeInput) (hnab : ∃ x y : G, x * y ≠ y * x)
    (hR : RouteD3Setup K z)
    (hshape : LocalShapeC3 2 (CompData.model .PSL 4) (conjClass3 K) z)
    (hT : IsTwinAt (conjClass3 K) K T z) (clsT : IsClassicalMember3 T z) (e : TwinElt K T z) :
    ∃ (J : Subgroup G) (t : G) (A : AtT3 K T J z t .PSL 4),
      J ∈ centralizingMembers (conjClass3 K) {z} ∧ J ≠ K ∧ J ≠ T ∧
      J ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      A.J₂ ∈ centralizingMembers (conjClass3 K) {e.u} ∧
      Set.ncard {N : Subgroup G | N ∈ centralizingMembers (conjClass3 K) {e.u} ∧
        Commutes N J} = 1 := by
  obtain ⟨J, t, A, ã, ã', hJ, hJK, hJT, hJu, hJ₂u, hãR, hã'R, hsq, hsq', hcount⟩ :=
    rank_setup3_pair h3 hnab hR (TwinRowSL4.twinRow ⟨rfl, rfl⟩) hshape hT clsT e
  refine ⟨J, t, A, hJ, hJK, hJT, hJu, hJ₂u, ?_⟩
  rw [hcount]
  exact congrArg (fun n => 1 + n) (card_fund_centralizing3_psl4 A.hdat hãR hã'R hsq hsq')

end Setup

section NoCentral

theorem twinYNoCentral3_sl4 : TwinYNoCentral3On TwinRowSL4 := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow hP hshape T hT clsT e M hM
  obtain ⟨rfl, rfl⟩ := hP
  by_contra hno
  push Not at hno
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hncs := not_commutes_self_of_mem3 hR
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨J, hJ, hJK, hJT⟩ := c.exists_big_member (fun N hN hNK => hT.comm_K N hN hNK)
    (fun N hN hNT => hT.comm_T N hN hNT)
  obtain ⟨t, hJt⟩ := hR.inClass.classical J hJ.1
  have htz : t ≠ z := involution_ne_of_member3 h3 hnab hR hrow hshape hT hJ hJK hJT hJt
  obtain ⟨A⟩ := exists_atT3 h3 hR hrow hshape hT clsT hJ hJK hJT hJt htz
  have hMJ : Commutes M J := hno J hJ hJK hJT
  have hMJ₂ : Commutes M A.J₂ := hno A.J₂ A.hJ₂z A.hJ₂K A.hJ₂T
  have hMt : M ∈ centralizingMembers (conjClass3 K) {t} :=
    ⟨hM.1, fun y hy => Subgroup.mem_centralizer_singleton_iff.mpr (hMJ y hy t hJt.mem)⟩
  have hMJne : M ≠ J := fun h => hncs J hJ.1 (by rw [h] at hMJ; exact hMJ)
  have hMJ₂ne : M ≠ A.J₂ := fun h => hncs A.J₂ A.hJ₂t.1 (by rw [h] at hMJ₂; exact hMJ₂)
  obtain ⟨RM, hRM, hMR⟩ := A.c.big_of_ne A.hJt A.hJ₂t A.hJ₂J.symm A.hJiso A.hJ₂iso hMt hMJne
    hMJ₂ne
  obtain ⟨ã, hãR, ã', hã'R, hsq, hsq', huY, hψu⟩ := exists_lifts3 A e
  have h1 : locImg (conjClass3 K) t M ≤
      Subgroup.centralizer ({Gaps.locMk (conjClass3 K) t ⟨e.u, huY⟩} :
        Set (locQuot (conjClass3 K) t)) :=
    (le_centralizer_iff_locImg3 A.c.hΩ A.c.hex A.c.hP1 A.c.hO3 hMt ⟨e.u, huY⟩).mp hM.2
  have hcent : RM ≤ Subgroup.centralizer ({ã * ã'} :
      Set (modelUniv .PSL 4 3 1 Nat.prime_three).K) :=
    (le_centralizer_iff_map3 A.c.d.ψ A.c.d.ker_le A.c.ker_cop (A.c.rf.y.pow3 RM hRM)
      (ã * ã')).mpr (by
      rw [hψu, ← hMR]
      exact h1)
  exact twinMFNotCentralizing3_psl4 A.hdat hãR hã'R hsq hsq' hRM fun s hs =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcent hs)).symm

end NoCentral

section Kind

theorem twinYKind3_general : TwinYKind3On (fun _ _ => True) := by
  intro h3 G _ _ _ hnab K z hR tY nY hrow _ hshape T hT clsT e hP1u hO3u ι _ D hcard i
  classical
  obtain ⟨J, t, A, -, -, hJ, hJK, hJT, hJu, hJ₂u, -, -, -, -, -⟩ :=
    rank_setup3_pair h3 hnab hR hrow hshape hT clsT e
  have hΩ : InClass3 (conjClass3 K) := hR.inClass
  have hex : ExactMembers3 (conjClass3 K) := hR.setup.1
  have hKΩ : K ∈ conjClass3 K := ⟨1, conjSub_one K⟩
  have hKz : K ∈ centralizingMembers (conjClass3 K) {z} :=
    ⟨hKΩ, isSubnormal_le hR.cls.subnormal⟩
  have hKiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ K → Commutes K N :=
    fun N hN hNK => hT.comm_K N hN hNK
  have hTiso : ∀ N ∈ centralizingMembers (conjClass3 K) {z}, N ≠ T → Commutes T N :=
    fun N hN hNT => hT.comm_T N hN hNT
  obtain ⟨c⟩ := TwinLoc3.of_setup (twinRowFacts3_of_row hrow) h3 hR hshape
  obtain ⟨hft0, hG20, hD40, hE60, -⟩ := twinRow_tag_facts3 hrow
  have hCF := ModelFacts.commutingFundamentalGeneration3_nonTwisted hG20 hD40 hE60 hft0
    (twinRow_admissible3 hrow)
  have hxo : ∃ y ∈ locLayer (conjClass3 K) e.u, conjSub y J = A.J₂ :=
    c.xOrbit hCF e hKz hT.mem hT.ne.symm hKiso hTiso hJ hJK hJT A.hJ₂z A.hJ₂K A.hJ₂T
  have hJJ₂ : Commutes J A.J₂ := A.hJiso A.J₂ A.hJ₂t A.hJ₂J
  have hJJ₂ne : J ≠ A.J₂ := A.hJ₂J.symm
  obtain ⟨x₀, hx₀⟩ := Nat.card_eq_one_iff_exists.mp hcard
  have hone : ∀ j : ι, j = i := fun j => (hx₀ j).trans (hx₀ i).symm
  have h₁ := mem_comp_of_card_one3 D i hone hJu
  have h₂ := mem_comp_of_card_one3 D i hone hJ₂u
  rcases D.valid i with ⟨t', n', hft, hadm, hk⟩ | hk | hk
  · have hG2 : t' ≠ .G2 := fun h =>
      false_of_g2d4_pair3 hΩ hex hP1u hO3u D hone hJu hJ₂u A.clsJ A.clsJ₂ A.hJ₂J hxo hadm hk
        (Or.inl h)
    have hD4 : t' ≠ .trialityD4 := fun h =>
      false_of_g2d4_pair3 hΩ hex hP1u hO3u D hone hJu hJ₂u A.clsJ A.clsJ₂ A.hJ₂J hxo hadm hk
        (Or.inr h)
    have hnA1 := not_psl_two_of_admissible3 hadm
    have hsc := EX.singleClass_of_kind hk hft hadm hG2 hD4
    have hpc := EX.powCop3_of_kind hk hft hadm hG2 hD4
    obtain ⟨F, hF, hFinj, hFcomm, hFtwin⟩ := EX.twinFamily_of_family3 (ι' := Fin 2) hΩ hex hP1u
      hO3u D hsc hpc ![J, A.J₂]
      (fun k => by fin_cases k; exacts [h₁, h₂])
      (by
        intro a b hab
        fin_cases a <;> fin_cases b
        · rfl
        · exact absurd hab hJJ₂ne
        · exact absurd hab.symm hJJ₂ne
        · rfl)
      (by
        intro k l hkl
        fin_cases k <;> fin_cases l
        · exact absurd rfl hkl
        · exact hJJ₂
        · exact hJJ₂.symm
        · exact absurd rfl hkl)
      (by
        intro M hM k l
        have key := A.nbhd_iff hM
        fin_cases k <;> fin_cases l
        · exact Iff.rfl
        · exact key
        · exact key.symm
        · exact Iff.rfl)
    have hmtc := EX.modelTwinClass_of_compData hk F hF hFinj hFcomm hFtwin
    have hmf := EX.mfTwin3 t' n' 2 hft hG2 hD4 hadm hnA1 le_rfl hmtc
    refine ⟨t', n', hk, ?_⟩
    rcases hmf with h | ⟨rfl, rfl, -⟩
    · exact twinRow_of_shapeTable_two h
    · exact Or.inl ⟨rfl, rfl, le_rfl⟩
  · exact absurd (eq_of_mem_compMembers_a13 hΩ hex hP1u hO3u (D := D) (i := i) hk h₁ h₂)
      hJJ₂ne
  · exact absurd hJJ₂ (not_commutes_of_m11_comp3 hΩ hex hP1u hO3u hk h₁ h₂)


theorem twinYKind3_sl4 : TwinYKind3On TwinRowSL4 :=
  fun h3 G _ _ _ hnab K z hR t n hrow _ hshape =>
    twinYKind3_general h3 G hnab K z hR t n hrow trivial hshape

end Kind

end CFSG.ClassicalInvolution.Q3.Q3TIY
