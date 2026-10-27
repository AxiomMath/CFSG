module

public import CFSG.GH74.Generic.BProg.B3.S45EvenN01
public import CFSG.GH74.Generic.BProg.B3.S45TableB
public import CFSG.GH74.Generic.BProg.B3.S45RankB
public import CFSG.GH74.Generic.BProg.B3.FalseCtxS45
public import CFSG.GH74.Generic.BProg.B3.LocBalRee
public import CFSG.GH74.Generic.BProg.B3.Thm9S45

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint
  CFSG.Assembly.LowTwoRank CFSG.LocalCores CFSG.ClassicalInvolution.Balance Subgroup
open CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.Generic.BProg.B3.FalseCtxS45
  CFSG.GH74.Generic.BProg.B3.S45TableA
open CFSG.GH74.GLS.TwoThin CFSG.LocalAnalysis.ComponentInitial CFSG.ComponentClassification

section Branch

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem table_data_of_ne_yAut (hc : Ctx21 G x K A a D J) (hax : a ≠ x)
    (hcen : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g : ↥K ⧸ pPrimeCore 2 ↥K, g * z = z * g) → z = 1)
    (hKC : KCentIn (↥K ⧸ pPrimeCore 2 ↥K))
    (hab : ∀ P : Sylow 2 ↥(centralizer ({x} : Set G)),
      IsMulCommutative ↥(P : Subgroup ↥(centralizer ({x} : Set G))))
    {H : Subgroup G} (hH : IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) H) (hHJ : H ≤ J)
    (hxY : x ∈ centralizer ({a} : Set G)) (hxJ : x ∈ normalizer (J : Set G)) :
    IsQuasisimple ↥(PumpCalc.bar a J) ∧ IsPGroup 2 ↥(Subgroup.center ↥(PumpCalc.bar a J)) ∧
      GHList (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) ∧
      orderOf (yAut hc.obs.comp.1 hxY hxJ) = 2 ∧
      Datum ↥(PumpCalc.bar a J) (yAut hc.obs.comp.1 hxY hxJ) ∧
      (∀ T : Subgroup ↥(PumpCalc.bar a J), IsPGroup 2 ↥T →
        (∀ t ∈ T, yAut hc.obs.comp.1 hxY hxJ t = t) → ∀ s ∈ T, ∀ r ∈ T, s * r = r * s) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJ : IsPCompIn 2 (centralizer ({a} : Set G)) J := hc.obs.comp
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hx2 : x * x = 1 := by
    have := pow_orderOf_eq_one x
    rwa [hx, pow_two] at this
  have hx1 : x ≠ 1 := fun h => by simp [h] at hx
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := exists_E hc hcen
  obtain ⟨e, heE, he2, hWe⟩ := exists_e hc hax hEK hAE hEel
  have heK : e ∈ K := hEK heE
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hnc : x ∉ centralizerSection J (pPrimeCoreOf 2 J) := fun hcs =>
    (hc.cA_eq x hxA hcs).elim hx1 (fun h => hax h.symm)
  have hq : IsQuasisimple ↥(PumpCalc.bar a J) := (FalseCtxS45Comp.isComponent_bar hJ).1
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥(PumpCalc.bar a J)) :=
    isPGroup_two_center_of_subnormal (pPrimeCore_quotient_eq_bot ↥(centralizer ({a} : Set G)))
      (FalseCtxS45Comp.isComponent_bar hJ).2
  have hGH : GHList (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) :=
    ghList_of_quasisimple hc.hyp.simple hc.hyp.nonab hc.hyp.kgh hc.obs.y_ord hq
  have hy := orderOf_yAut hJ hxY hxJ hx2 hnc
  have hHK : H ≤ K := hH.1.trans inf_le_left
  have hord := orderOf_psi heK he2
  obtain ⟨hS, hSn, hL2⟩ := hKC _ hord
  have hHe : IsPCompIn 2 (K ⊓ centralizer ({e} : Set G)) H := by rw [← hWe]; exact hH
  have hmap := FalseCtxS45K.map_eq_derived heK he2 hS hHe
  set S : Subgroup (↥K ⧸ pPrimeCore 2 ↥K) :=
    ⁅FalseCtxS45K.cent K e heK, FalseCtxS45K.cent K e heK⁆ with hSdef
  have hmem : ∀ v : ↥H, psiH hHK v ∈ S := fun v =>
    hmap ▸ ⟨⟨v, hHK v.2⟩, Subgroup.mem_subgroupOf.mpr v.2, rfl⟩
  have hsurj : ∀ s ∈ S, ∃ v : ↥H, psiH hHK v = s := by
    intro s hs
    rw [← hmap] at hs
    obtain ⟨k, hk, rfl⟩ := hs
    exact ⟨⟨k, Subgroup.mem_subgroupOf.mp hk⟩, rfl⟩
  have hker := ker_piH_le hHK hHJ hJ.1 hS hSn hmem hsurj
  have hKx : K ≤ centralizer ({x} : Set G) := hc.circ.1.1.1.2.2.1
  have hHx : ∀ h ∈ H, h * x = x * h := fun h hh =>
    Subgroup.mem_centralizer_singleton_iff.1 (hKx (hHK hh))
  have hsurj' : Function.Surjective ((psiH hHK).codRestrict S hmem) := by
    rintro ⟨s, hs⟩
    obtain ⟨w, hw⟩ := hsurj s hs
    exact ⟨w, Subtype.ext hw⟩
  have hL : Datum ↥(PumpCalc.bar a J) (yAut hc.obs.comp.1 hxY hxJ) := by
    refine ⟨↥H, ↥S, inferInstance, inferInstance, piH hHJ hJ.1, (psiH hHK).codRestrict S hmem,
      yAut_piH hHJ hJ.1 hxY hxJ hHx, ?_, hsurj', ?_, hL2⟩
    · rw [MonoidHom.ker_codRestrict]
      exact hker
    · rw [MonoidHom.ker_codRestrict]
      exact odd_card_ker_psiH hHK
  exact ⟨hq, hZ, hGH, hy, hL, fun T hT hfix => comm_of_fixed hJ hx hxY hxJ hab T hT hfix⟩

end Branch

section Glue

variable {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G} {D J : Subgroup G}

theorem N7_shape_of_ne_ea (hc : Ctx21 G x K A a D J) (hax : a ≠ x)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K))
    (hcen : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g : ↥K ⧸ pPrimeCore 2 ↥K, g * z = z * g) → z = 1)
    (hKC : KCentIn (↥K ⧸ pPrimeCore 2 ↥K)) (hTab : S45Table) (hEven : S45EvenTableEA)
    (hab : ∀ P : Sylow 2 ↥(centralizer ({x} : Set G)),
      IsMulCommutative ↥(P : Subgroup ↥(centralizer ({x} : Set G))))
    {H : Subgroup G} (hH : IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) H) (hHJ : H ≤ J)
    (hxJ : x ∈ normalizer (J : Set G)) :
    QShape4 (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) ∨
      QShape5 (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) ∨
        NativeSporadic.IsSporadic (↥(PumpCalc.bar a J) ⧸ Subgroup.center ↥(PumpCalc.bar a J)) .M12 := by
  classical
  obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := exists_E hc hcen
  have hxA : x ∈ A := hAE ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  obtain ⟨hAc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hc.src.2.1
  have hxY : x ∈ centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.2 (hAc x hxA a hc.a_mem)
  obtain ⟨hq, hZ, hGH, hy, hL, hfix⟩ := table_data_of_ne_yAut hc hax hcen hKC hab hH hHJ hxY hxJ
  by_cases hxb : L5U5.xbar a ∈ PumpCalc.bar a J
  · have hZne := center_ne_bot_of_xbar_mem hc hxb
    have hG4 : Gen4 ↥(PumpCalc.bar a J) :=
      Gen4.subgroup (PumpCalc.bar a J) (L5U5.gen4_centralizerBar hc.hyp.gen4 a)
    exact Or.inr (Or.inr (hEven ↥(PumpCalc.bar a J) hG4 hq hZ hZne hGH _ hy hL hfix
      (N1_evenEA hc hP hax hxY hxJ)))
  · have hrk := rank_of_xbar_not_mem hc hxb
    exact (hTab ↥(PumpCalc.bar a J) hrk hq hZ hGH _ hy hL hfix).elim Or.inl
      (fun h => Or.inr (Or.inl h))

theorem false_of_ctx_s45_glue_ea (hc : Ctx21 G x K A a D J)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K))
    (hcen : ∀ z : ↥K ⧸ pPrimeCore 2 ↥K, (∀ g : ↥K ⧸ pPrimeCore 2 ↥K, g * z = z * g) → z = 1)
    (hKC : KCentIn (↥K ⧸ pPrimeCore 2 ↥K))
    (hLoc : ∀ (Jt : Type) [Group Jt], (QShape4 Jt ∨ QShape5 Jt) → LocBal32All Jt)
    (hM12 : ∀ (Jt : Type) [Group Jt], NativeSporadic.IsSporadic Jt .M12 → LocBal32All Jt)
    (hTab : S45Table) (hEven : S45EvenTableEA)
    (hab : ∀ P : Sylow 2 ↥(centralizer ({x} : Set G)),
      IsMulCommutative ↥(P : Subgroup ↥(centralizer ({x} : Set G))))
    (hnot : ¬ pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) ≤ centralizerSection J (pPrimeCoreOf 2 J))
    (hbal : pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) ≤ pLayerOf 2 (centralizer ({a} : Set G)))
    (hPump : ∀ {K' : Subgroup G}, pLayerOf 2 (K' ⊓ centralizer ({a} : Set G)) ≤
      pLayerOf 2 (centralizer ({a} : Set G)) →
      ¬ pLayerOf 2 (K' ⊓ centralizer ({a} : Set G)) ≤ centralizerSection J (pPrimeCoreOf 2 J) →
      J ≤ pumpUp 2 K' a)
    (hT9 : a ≠ x → ∀ {H : Subgroup G}, IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) H →
      IsPCompIn 2 (centralizer ({a} : Set G)) (pumpUp 2 H a) ∧
        x ∈ normalizer ((pumpUp 2 H a : Subgroup G) : Set G))
    (hPself : ∀ {X L : Subgroup G}, IsPCompIn 2 X L → pLayerOf 2 L = L) : False := by
  classical
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hKx : K ≤ centralizer ({x} : Set G) := hK.1
  by_cases hax : a = x
  · have hnotK : ¬ K ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
      intro hle
      apply hnot
      have h1 : K ⊓ centralizer ({a} : Set G) = K := by rw [hax]; exact inf_eq_left.2 hKx
      rw [h1, hPself hK]
      exact hle
    obtain ⟨hAJ, hshape⟩ := qshape_of_eq hc hax hcen hP hnotK
    exact false_of_locBal hc hAJ fun B hB => hLoc _ hshape B hB
  ·
    obtain ⟨H, hH, hHn⟩ : ∃ H : Subgroup G, IsPCompIn 2 (K ⊓ centralizer ({a} : Set G)) H ∧
        ¬ H ≤ centralizerSection J (pPrimeCoreOf 2 J) := by
      by_contra hcon
      push Not at hcon
      exact hnot (sSup_le fun L hL => hcon L hL)
    have hHY : H ≤ centralizer ({a} : Set G) := hH.1.trans inf_le_right
    have hHself : pLayerOf 2 H = H := hPself hH
    have hHbal : pLayerOf 2 (H ⊓ centralizer ({a} : Set G)) ≤ pLayerOf 2 (centralizer ({a} : Set G)) := by
      rw [inf_eq_left.2 hHY, hHself]
      have hHle : H ≤ pLayerOf 2 (K ⊓ centralizer ({a} : Set G)) := le_sSup hH
      exact hHle.trans hbal
    have hHnot : ¬ pLayerOf 2 (H ⊓ centralizer ({a} : Set G)) ≤
        centralizerSection J (pPrimeCoreOf 2 J) := by
      rw [inf_eq_left.2 hHY, hHself]
      exact hHn
    have hJle := hPump hHbal hHnot
    obtain ⟨hJ', hxJ'⟩ := hT9 hax hH
    have hJeq : J = pumpUp 2 H a := FalseCtxS45Comp.eq_of_le hc.obs.comp hJ' hJle
    have hHJ : H ≤ J := by rw [hJeq]; exact le_pumpUp_self hHself hHY
    have hxJ : x ∈ normalizer (J : Set G) := by rw [hJeq]; exact hxJ'
    have hshape := N7_shape_of_ne_ea hc hax hP hcen hKC hTab hEven hab hH hHJ hxJ
    obtain ⟨E, hEK, hAE, hxE, hEel, hE4⟩ := exists_E hc hcen
    obtain ⟨e, heE, he2, hWe⟩ := exists_e hc hax hEK hAE hEel
    obtain ⟨hAc, -⟩ := C3.Layer1.Back.forall_of_isElementaryAbelian hc.src.2.1
    have hAJ : A ≤ normalizer (J : Set G) := by
      rw [hAE]
      refine sup_le (fun f hf => ?_) (Subgroup.zpowers_le.2 hxJ)
      have hfA : f ∈ A := hAE ▸ Subgroup.mem_sup_left hf
      exact mem_normalizer_of_pumpup hKC (hEK heE) he2 hWe hc.obs.comp hH hHJ (hEK hf)
        (Subgroup.mem_centralizer_singleton_iff.2 (hAc f hfA a hc.a_mem))
    rcases hshape with h4 | h5 | hM
    · exact false_of_locBal hc hAJ fun B hB => hLoc _ (Or.inl h4) B hB
    · exact false_of_locBal hc hAJ fun B hB => hLoc _ (Or.inr h5) B hB
    · exact false_of_locBal hc hAJ fun B hB => hM12 _ hM B hB

end Glue

section Main

theorem N8_false_of_ctx_s45_ea {G : Type} [Group G] [Finite G] {x : G} {K A : Subgroup G} {a : G}
    {D J : Subgroup G} (hNo : B2.NoJPrimeNonSD) (hEven : S45EvenTableEA) (hc : Ctx21 G x K A a D J)
    (hP : QShape4 (↥K ⧸ pPrimeCore 2 ↥K) ∨ QShape5 (↥K ⧸ pPrimeCore 2 ↥K)) : False := by
  classical
  have hx : orderOf x = 2 := hc.circ.1.1.1.1
  have hK : IsPCompIn 2 (centralizer ({x} : Set G)) K := hc.circ.1.1.1.2.2
  have hC1 : pRank 2 ↥(CxK x K) ≤ 1 := Ctx21.pRank_cxk_le_one hNo hc (Or.inr (Or.inr hP))
  have hab := Ctx21.sylow_cx_abelian hc hP hC1
  obtain ⟨n, hcen, -⟩ := Lemma212S45.shape45_data hP
  have hKC : KCentIn (↥K ⧸ pPrimeCore 2 ↥K) := S45.kCent_of_isJ1OrRee hP.symm
  have hLoc : ∀ (Jt : Type) [Group Jt], (QShape4 Jt ∨ QShape5 Jt) → LocBal32All Jt := by
    intro Jt _ hshape B hB
    rcases hshape with h4 | h5
    · exact locBal32_ree h4 B hB
    · exact locBal32_J1 h5 B hB
  have hnot := (lemma212a_s45 hc hP).1
  have hbal := Lemma212S45.pLayerOf_le_of_balance hx hK (hc.src.1 hc.a_mem)
  obtain ⟨E, hEK, hAE, -⟩ := exists_E hc hcen
  refine false_of_ctx_s45_glue_ea hc hP hcen hKC hLoc (fun _ _ hJ => locBal32_M12 hJ)
    S45TableB.s45Table_proved hEven hab hnot hbal
    (fun hb hn => Lemma212Aux.le_pumpUp_of_not_le_cSec hc.obs.comp hb hn) ?_
    (fun h => Lemma212S45.pLayerOf_self h)
  intro hax H hH
  have hyK : a ∈ K ⊔ zpowers x := by
    have : a ∈ E ⊔ zpowers x := hAE ▸ hc.a_mem
    exact sup_le_sup_right hEK _ this
  exact thm9_s45 hc.hyp hc.circ.1.2.2 hP hc.obs.y_ord hyK hax hH

theorem N8_stage1BalFor_shape4_ea (hNo : B2.NoJPrimeNonSD) (hEven : S45EvenTableEA) :
    Stage1BalFor QShape4 :=
  stage1BalFor_of_ctx fun _ _ _ _ _ _ _ _ _ hc hP => N8_false_of_ctx_s45_ea hNo hEven hc (Or.inl hP)

theorem N8_stage1BalFor_shape5_ea (hNo : B2.NoJPrimeNonSD) (hEven : S45EvenTableEA) :
    Stage1BalFor QShape5 :=
  stage1BalFor_of_ctx fun _ _ _ _ _ _ _ _ _ hc hP => N8_false_of_ctx_s45_ea hNo hEven hc (Or.inr hP)

end Main

end CFSG.GH74.Generic.BProg.B3
