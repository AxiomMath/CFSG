module

public import CFSG.LargeExtraspecial.S14C13Common
public import CFSG.LargeExtraspecial.S14C13Model
public import CFSG.LargeExtraspecial.S14C13Trans

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S14

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial.S4

@[expose] def Spin13Stmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] [IsSimpleGroup G] (S : Setting G) (g : G) (t : S.O),
    Stage S g t → Config.sp6.Occurs S g t → IsExtraspecialPGroup 2 (Nbar S g t) →
      Concl14_7 S g t → ∃ r ∈ Rbar S g t, orderOf r = 5 ∧ ∀ n ∈ Nbar S g t,
        (r * n * r⁻¹ = n ∨ r * n * r⁻¹ = n * t) → n = 1 ∨ n = t

theorem coe_centEquiv_symm {Y : Type} [Group Y] {M : Subgroup Y} (t0 : M)
    (x : ↥(M ⊓ centralizer ({(t0 : Y)} : Set Y))) :
    (((centEquiv t0).symm x : M) : Y) = (x : Y) :=
  rfl

variable {G : Type} [Group G] [Finite G] {S : Setting G} {g : G}

theorem partA_data {t : S.O} (hSt : Stage S g t) (hext : IsExtraspecialPGroup 2 (Nbar S g t))
    (hF : FCt S t = Nbar S g t) :
    ∃ htM : t ∈ S.Mbar, orderOf (⟨t, htM⟩ : S.Mbar) = 2 ∧ (∃ a b : S.Mbar, a * b ≠ b * a) ∧
      Nonempty (timmesfeldFStar (centralizer ({(⟨t, htM⟩ : S.Mbar)} : Set S.Mbar)) ≃*
        Nbar S g t) := by
  have haQ := hSt.hyp4.conj_mem
  have htN := S6.self_mem_Nbar hSt.hyp4 hSt.mem
  have htM : t ∈ S.Mbar := Rbar_le_Mbar (Nbar_le_Rbar htN)
  refine ⟨htM, orderOf_eq_prime ?_ fun h => hSt.ne_one (congrArg Subtype.val h), ?_,
    nonempty_fstar_equiv (M := S.Mbar) ⟨t, htM⟩ hF⟩
  · exact Subtype.ext (by simpa [pow_two] using mul_self_of_mem_Lbar S haQ hSt.mem)
  · obtain ⟨a, ha, b, hb, hab⟩ := exists_comm_eq_of_extraspecial hext htN hSt.ne_one
      fun y hy => (commute_of_mem_Rbar haQ (Nbar_le_Rbar hy)).symm
    refine exists_noncomm_of_mem' (Rbar_le_Mbar (Nbar_le_Rbar ha))
      (Rbar_le_Mbar (Nbar_le_Rbar hb)) fun h => hSt.ne_one ?_
    rw [← hab, h, mul_inv_cancel_right, mul_inv_cancel]

theorem isPlusType_of_rnPlus {t : S.O} {ht : t ∈ S.Lbar g} {Q : QuadraticForm (ZMod 2) (Vt S g t)}
    (horb : ∀ v : Vt S g t, v ≠ 0 → (Q v = 0 ↔ v ∈ orbitOf (RmodN S g t) (aV ht)))
    (hplus : RNPlus S g t) : CFSG.GroupTheory.WeirSylow.IsPlusType Q := by
  obtain ⟨ht', W, hW, hWo⟩ := hplus
  refine ⟨W, hW, fun w hw => ?_⟩
  by_cases h0 : w = 0
  · rw [h0, QuadraticMap.map_zero]
  · exact (horb w h0).mpr (hWo w hw h0)

theorem spin_of_spin13 {t : S.O} (htM : t ∈ S.Mbar) (hF : FCt S t = Nbar S g t) {r : S.O}
    (hrC : r ∈ Ct S t) (hr5 : orderOf r = 5)
    (hrfix : ∀ n ∈ Nbar S g t, (r * n * r⁻¹ = n ∨ r * n * r⁻¹ = n * t) → n = 1 ∨ n = t) :
    ∃ g' : centralizer ({(⟨t, htM⟩ : S.Mbar)} : Set S.Mbar), orderOf g' = 5 ∧
      ∀ y ∈ timmesfeldFStar (centralizer ({(⟨t, htM⟩ : S.Mbar)} : Set S.Mbar)),
        (g' * y * g'⁻¹ = y ∨ g' * y * g'⁻¹ = y * CFSG.Sporadic.Co2Smith.selfInCentralizer
          (⟨t, htM⟩ : S.Mbar)) →
          y = 1 ∨ y = CFSG.Sporadic.Co2Smith.selfInCentralizer (⟨t, htM⟩ : S.Mbar) := by
  let t' : S.Mbar := ⟨t, htM⟩
  have hst : ((CFSG.Sporadic.Co2Smith.selfInCentralizer (⟨t, htM⟩ : S.Mbar) : S.Mbar) : S.O) =
      t := rfl
  let ψ : centralizer ({t'} : Set S.Mbar) → S.O := fun z => ((z : S.Mbar) : S.O)
  have hψ : Function.Injective ψ := Subtype.val_injective.comp Subtype.val_injective
  refine ⟨(centEquiv t').symm ⟨r, hrC⟩, ?_, fun y hy hyc => ?_⟩
  · rw [MulEquiv.orderOf_eq, ← hr5]
    exact Subgroup.orderOf_mk r hrC
  · have h1 : centEquiv t' y ∈ timmesfeldFStar ↥(S.Mbar ⊓ centralizer ({t} : Set S.O)) :=
      (SetLike.ext_iff.mp (map_fstar_centEquiv t') _).mp ⟨y, hy, rfl⟩
    have hyN : ψ y ∈ Nbar S g t := (SetLike.ext_iff.mp hF _).mp ⟨_, h1, rfl⟩
    have hcond : r * ψ y * r⁻¹ = ψ y ∨ r * ψ y * r⁻¹ = ψ y * t := by
      rcases hyc with h | h
      · left
        have := congrArg ψ h
        simpa only [ψ, Subgroup.coe_mul, Subgroup.coe_inv, coe_centEquiv_symm] using this
      · right
        have := congrArg ψ h
        simpa only [ψ, Subgroup.coe_mul, Subgroup.coe_inv, coe_centEquiv_symm, hst] using this
    rcases hrfix _ hyN hcond with h | h
    · exact Or.inl (hψ h)
    · exact Or.inr (hψ h)

theorem quotientIso_of_RmodN {t : S.O} (haQ : g * S.z * g⁻¹ ∈ S.QG) (htM : t ∈ S.Mbar)
    (hCt : Ct S t = Rbar S g t) (hF : FCt S t = Nbar S g t) {X : Type} [Group X]
    (e : RmodN S g t ≃* X) :
    timmesfeldQuotientIso
      (timmesfeldFStar (centralizer ({(⟨t, htM⟩ : S.Mbar)} : Set S.Mbar))) X := by
  obtain ⟨ψ, hψ, hker⟩ := exists_quotient_of_eq hCt (resV haQ t)
    (fun r => resV_eq_one_iff haQ r) (range_resV haQ t) e hF
  exact quotientIso_centralizer (M := S.Mbar) ⟨t, htM⟩ hψ hker

theorem claim14_13A_of (hCE : CentralExtInput.{0}) (hspin : Spin13Stmt) : Claim14_13A := by
  intro G _ _ _ S g t c hSt hocc hext h6 h7 h8 hF
  have haQ := hSt.hyp4.conj_mem
  obtain ⟨htM, ht2, hnc, ⟨eF⟩⟩ := partA_data hSt hext hF
  have hextF := (Bridge.timmesfeldIsExtraspecial_congr eF).mpr
    ((Bridge.timmesfeldIsExtraspecial_iff _).mpr hext)
  have hcardF := Nat.card_congr eF.toEquiv
  refine ⟨fun hc => ?_, fun hc => ?_, fun hc => ?_⟩
  · subst hc
    obtain ⟨hCt, hsimple⟩ := partA_simple hCE hSt hocc hext (Or.inl rfl) h6 h7 h8 hF
    obtain ⟨H, C, ht, ht1, hVQ, hSp, hdim⟩ := hocc.1
    obtain ⟨e⟩ := nonempty_isometryGroup_equiv_statedSp (beta_isAlt H C ht ht1 hVQ)
      (beta_nondegenerate H C ht ht1 hVQ) hdim
    obtain ⟨r, hr, hr5, hrfix⟩ := hspin G S g t hSt hocc hext h7
    refine ⟨htM, ?_⟩
    exact
      { simple := hsimple
        noncomm := hnc
        orderOf_eq := ht2
        extraspecial := hextF
        card := hcardF.trans hocc.2.2
        quotient := quotientIso_of_RmodN haQ htM hCt hF
          ((MulEquiv.subgroupCongr hSp.eq_sp).trans e)
        spin := spin_of_spin13 htM hF (Rbar_le_Ct haQ hr) hr5 hrfix }
  · subst hc
    obtain ⟨hCt, hsimple⟩ := partA_simple hCE hSt hocc hext (Or.inr (Or.inl rfl)) h6 h7 h8 hF
    obtain ⟨⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩, hplus⟩ := hocc.1
    obtain ⟨Q, hQ, -, hX, -, horb⟩ := hΩ.exists_form
    obtain ⟨e⟩ := nonempty_omegaGroup_equiv_omegaPlus hQ (m := 4) (by rw [hdim]) (by norm_num)
      (isPlusType_of_rnPlus horb hplus)
    refine ⟨htM, ?_⟩
    exact
      { simple := hsimple
        noncomm := hnc
        orderOf_eq := ht2
        extraspecial := hextF
        card := hcardF.trans hocc.2.2
        quotient := quotientIso_of_RmodN haQ htM hCt hF ((MulEquiv.subgroupCongr hX).trans e) }
  · subst hc
    obtain ⟨hCt, hsimple⟩ := partA_simple hCE hSt hocc hext (Or.inr (Or.inr rfl)) h6 h7 h8 hF
    obtain ⟨⟨H, C, ht, ht1, hVQ, hΩ, hdim⟩, hplus⟩ := hocc.1
    obtain ⟨Q, hQ, -, hX, -, horb⟩ := hΩ.exists_form
    obtain ⟨e⟩ := nonempty_omegaGroup_equiv_omegaPlus hQ (m := 6) (by rw [hdim]) (by norm_num)
      (isPlusType_of_rnPlus horb hplus)
    exact ⟨hsimple, ⟨t, htM⟩, ht2, hextF, Or.inr ⟨hocc.2.1, hcardF.trans hocc.2.2,
      quotientIso_of_RmodN haQ htM hCt hF ((MulEquiv.subgroupCongr hX).trans e)⟩⟩

end CFSG.LargeExtraspecial.S14
