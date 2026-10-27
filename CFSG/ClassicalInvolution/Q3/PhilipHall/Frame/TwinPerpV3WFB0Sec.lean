module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23PfSetup
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentResComp
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6Frame
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgtLift
public import CFSG.ClassicalInvolution.Q3.Q3MTAbel

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Balance CFSG.ClassicalInvolution.Disconnected
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinEdge
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinFrameTgt
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3CH CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf6
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12
open CFSG.ClassicalInvolution.Asc77.Thompson CFSG.ClassicalInvolution.Uniform
open scoped commutatorElement
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE

section B0Sec




variable {n : ℕ}

variable {Q : Type} [Group Q] [Finite Q]

theorem mem_DSet_of_normal {Φ : Set (Subgroup Q)} (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J) {V : Subgroup Q}
    (hVn : V.Normal) {J : Subgroup Q} (hJ : J ∈ Φ) : J ∈ DSet Φ V :=
  ⟨mem_RSet_iff.mpr ⟨J, hJ, le_rfl, h2 J hJ, fun R' hR'J _ hle => le_antisymm hR'J hle⟩,
    fun x _ => by rw [Subgroup.normalizer_eq_top_iff.mpr hVn]; exact Subgroup.mem_top x⟩

theorem exists_swap_of_local {Φ : Set (Subgroup Q)} (hP : Q3CL.PartIHypG Φ) {V : Subgroup Q}
    (hV : V ∈ WSet Φ) {K J : Subgroup Q} (hK : K ∈ Φ) (hJ : J ∈ omegaNbr Φ K)
    (hone : ∀ a ∈ omegaNbr Φ K, ∀ b ∈ omegaNbr Φ K, a = b)
    (hcomp : dComp Φ K ≠ dstarComp Φ K) :
    ∃ e : ↥(muGroup Φ V) ≃* Equiv.Perm (Fin 4),
      ∀ x, x ∈ Thompson.muDelta Φ V ↔ (e x).IsSwap := by
  have hnc : ¬ DbarConnected Φ V := Q3T6.Mu.thompsonGraphAll hP hK hcomp hV
  obtain ⟨g, ρ, σ, hρ, hσ⟩ := Q3MT.exists_rep_pair_of_omegaNbr hP hV hK hJ
  have hσρ : σ.K ∈ omegaNbr Φ ρ.K := by
    rw [hρ, hσ]
    exact omegaNbr_conj hP.hyp.conjInvariant hJ g
  have hne' : ρ.K ≠ σ.K := fun h => hσρ.2.1 h.symm
  have hle : (Star3T.cent (muDelta Φ V) (Asc77.MuTab.muTabElt ρ)).ncard ≤ 2 := by
    refine Q3T6.Mu.ncard_cent_le hP hV ρ (n := 1) ?_
    rw [Set.ncard_le_one_iff]
    intro a b ha hb
    rw [hρ] at ha hb
    have ha' := omegaNbr_conj hP.hyp.conjInvariant ha g⁻¹
    have hb' := omegaNbr_conj hP.hyp.conjInvariant hb g⁻¹
    rw [conjSub_inv_conjSub] at ha' hb'
    exact (conjSub_inj g⁻¹).mp (hone _ ha' _ hb')
  have hge : 2 ≤ (Star3T.cent (muDelta Φ V) (Asc77.MuTab.muTabElt ρ)).ncard := by
    have hd : Asc77.MuTab.muTabElt ρ ≠ Asc77.MuTab.muTabElt σ := fun h =>
      hne' ((Q3T6.Mu.muTabElt_eq_iff hP hV ρ σ).mp h)
    have hsub : ({Asc77.MuTab.muTabElt ρ, Asc77.MuTab.muTabElt σ} : Set ↥(muGroup Φ V)) ⊆
        Star3T.cent (muDelta Φ V) (Asc77.MuTab.muTabElt ρ) := by
      rintro y (rfl | rfl)
      · exact Star3T.self_mem_cent (Asc77.MuTab.muTabElt_mem ρ)
      · exact ⟨Asc77.MuTab.muTabElt_mem σ,
          ((Q3T6.Mu.muTab_commute_iff hP hV ρ σ hne').mpr hσρ).symm⟩
    calc 2 = ({Asc77.MuTab.muTabElt ρ, Asc77.MuTab.muTabElt σ} : Set ↥(muGroup Φ V)).ncard :=
          (Set.ncard_pair hd).symm
      _ ≤ _ := Set.ncard_le_ncard hsub (Set.toFinite _)
  have hk : (Star3T.cent (muDelta Φ V) (Asc77.MuTab.muTabElt ρ)).ncard = 2 := le_antisymm hle hge
  have hTT := Q3T6.Mu.isTT_muDelta hP hV
  have hS := Q3T6.Mu.isStar_muDelta (Q3CL.T8.ctxOf hP hV)
  obtain ⟨a, ha, hconn⟩ := Q3T6.Mu.exists_not_conn_at hP hV hnc (Asc77.MuTab.muTabElt ρ)
  exact Star3T.exists_mulEquiv_perm_four hTT hS (Asc77.MuTab.muTabElt_mem ρ) ha hconn hk

theorem sec_klein_involutions {Φ : Set (Subgroup Q)} (hP : Q3CL.PartIHypG Φ) {V : Subgroup Q}
    (hV : V ∈ WSet Φ) (hVn : V.Normal) (h2 : ∀ J ∈ Φ, IsPGroup 2 ↥J)
    {K K' : Subgroup Q} {z : Q} (hK : K ∈ Φ) (hz : IsUniqueInvolution K z)
    (hz' : IsUniqueInvolution K' z) (hK' : K' ∈ omegaNbr Φ K)
    {e : ↥(muGroup Φ V) ≃* Equiv.Perm (Fin 4)}
    (he : ∀ x, x ∈ Thompson.muDelta Φ V ↔ (e x).IsSwap) :
    ∃ j : Q, j * j = 1 ∧ j * z = z * j ∧
      ∀ J ∈ Φ, ∀ z' : Q, IsUniqueInvolution J z' → z' = z ∨ z' = j ∨ z' = z * j := by
  classical
  have hΩ : HypOmegaGen Φ := hP.hyp
  have hD : ∀ J ∈ Φ, J ∈ DSet Φ V := fun J hJ => mem_DSet_of_normal h2 hVn hJ
  have hsyl : ∀ J ∈ Φ, IsSylow2In J J := fun J hJ =>
    ⟨le_rfl, h2 J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  have c : Q3CL.Thompson.Ctx Φ V := Q3CL.T8.ctxOf hP hV
  have hK'Φ : K' ∈ Φ := hK'.1
  have hKK' : K' ≠ K := hK'.2.1
  obtain ⟨ρ, hρK⟩ : ∃ ρ : Thompson.Rep Φ V, ρ.K = K :=
    ⟨Q3CL.T8.mkRep hP hV hK (hD K hK) (hsyl K hK), rfl⟩
  obtain ⟨ρ', hρ'K⟩ : ∃ ρ' : Thompson.Rep Φ V, ρ'.K = K' :=
    ⟨Q3CL.T8.mkRep hP hV hK'Φ (hD K' hK'Φ) (hsyl K' hK'Φ), rfl⟩
  have hne : ρ.K ≠ ρ'.K := fun h => hKK' (by rw [← hρK, ← hρ'K]; exact h.symm)
  have hnbr : ρ'.K ∈ omegaNbr Φ ρ.K := by rw [hρK, hρ'K]; exact hK'
  have ha := Asc77.MuTab.muTabElt_mem ρ
  have hb := Asc77.MuTab.muTabElt_mem ρ'
  have hab : Asc77.MuTab.muTabElt ρ ≠ Asc77.MuTab.muTabElt ρ' := fun h =>
    hne ((Q3T6.Mu.muTabElt_eq_iff hP hV ρ ρ').mp h)
  have hcomm : Asc77.MuTab.muTabElt ρ * Asc77.MuTab.muTabElt ρ' =
      Asc77.MuTab.muTabElt ρ' * Asc77.MuTab.muTabElt ρ :=
    (Q3T6.Mu.muTab_commute_iff hP hV ρ ρ' hne).mpr hnbr
  obtain ⟨c₃, hc₃Δ, hac, hbc⟩ := S4.exists_third he ha hb hab hcomm
  obtain ⟨ρ₃, rfl⟩ := Asc77.MuTab.exists_rep_of_mem_muDelta hc₃Δ
  have hne₁ : ρ.K ≠ ρ₃.K := fun h => hac (by rw [(Q3T6.Mu.muTabElt_eq_iff hP hV ρ ρ₃).mpr h])
  have hn₁ : ρ₃.K ∉ omegaNbr Φ ρ.K := fun h =>
    hac ((Q3T6.Mu.muTab_commute_iff hP hV ρ ρ₃ hne₁).mpr h)
  have hne₂ : ρ'.K ≠ ρ₃.K := fun h => hbc (by rw [(Q3T6.Mu.muTabElt_eq_iff hP hV ρ' ρ₃).mpr h])
  have hn₂ : ρ₃.K ∉ omegaNbr Φ ρ'.K := fun h =>
    hbc ((Q3T6.Mu.muTab_commute_iff hP hV ρ' ρ₃ hne₂).mpr h)
  obtain ⟨j, hj⟩ := Sec6Gen.exists_uniqueInvolution hΩ ρ₃.hK
  have hzρ : IsUniqueInvolution ρ.K z := by rw [hρK]; exact hz
  have hzρ' : IsUniqueInvolution ρ'.K z := by rw [hρ'K]; exact hz'
  have hr1 : ρ.r * j * ρ.r⁻¹ = z * j := c.conj_involution ρ ρ₃ hne₁ hn₁ hzρ hj
  have hr2 : ρ'.r * j * ρ'.r⁻¹ = z * j := c.conj_involution ρ' ρ₃ hne₂ hn₂ hzρ' hj
  have hzc : ρ.r * z * ρ.r⁻¹ = z := by
    have h1 : z * ρ.r = ρ.r * z := e189_commute_of_mem hzρ (ρ.hRK.1 ρ.hr)
    calc ρ.r * z * ρ.r⁻¹ = (z * ρ.r) * ρ.r⁻¹ := by rw [h1]
      _ = z := mul_inv_cancel_right z ρ.r
  have hjz : j * z = z * j := by
    have h1 : (z * j) * (z * j) = 1 := by
      rw [← hr1]
      calc ρ.r * j * ρ.r⁻¹ * (ρ.r * j * ρ.r⁻¹) = ρ.r * (j * j) * ρ.r⁻¹ := by group
        _ = 1 := by rw [hj.sq]; group
    have h2' : z * j = (z * j)⁻¹ := eq_inv_of_mul_eq_one_left h1
    calc j * z = j⁻¹ * z⁻¹ := by
          rw [inv_eq_of_mul_eq_one_right hj.sq, inv_eq_of_mul_eq_one_right hz.sq]
      _ = (z * j)⁻¹ := (mul_inv_rev z j).symm
      _ = z * j := h2'.symm
  have hconjK : ∀ (m : Q), m ∈ Subgroup.normalizer (V : Set Q) → ∀ (σ' ρ₀ : Thompson.Rep Φ V),
      σ'.img = Thompson.piG V m * ρ₀.img * (Thompson.piG V m)⁻¹ → σ'.K = conjSub m ρ₀.K :=
    fun m hm σ' ρ₀ h =>
      c.K_eq_of_img_eq σ' (TwinPerp23.conjRep hΩ hm ρ₀)
        (by rw [TwinPerp23.conjRep_img]; exact h)
  have hinv_img : ∀ τ : Thompson.Rep Φ V, τ.img * τ.img = 1 := fun τ =>
    congrArg Subtype.val (Q3T6.Mu.muDelta_mul_self hΩ hV (Asc77.MuTab.muTabElt_mem τ))
  have hinv1 : ρ.img⁻¹ = ρ.img := inv_eq_of_mul_eq_one_right (hinv_img ρ)
  have hinv2 : ρ'.img⁻¹ = ρ'.img := inv_eq_of_mul_eq_one_right (hinv_img ρ')
  refine ⟨j, hj.sq, hjz, ?_⟩
  intro J hJ z' hz'J
  obtain ⟨σ, hσK⟩ : ∃ σ : Thompson.Rep Φ V, σ.K = J :=
    ⟨Q3CL.T8.mkRep hP hV hJ (hD J hJ) (hsyl J hJ), rfl⟩
  have hzσ : IsUniqueInvolution σ.K z' := by rw [hσK]; exact hz'J
  have hσΔ := Asc77.MuTab.muTabElt_mem σ
  rcases T7E.swap_word_cases he ha hb hc₃Δ hab hcomm hac hσΔ with h | h | h | h | h | h
  · have hK1 : σ.K = ρ.K := (Q3T6.Mu.muTabElt_eq_iff hP hV σ ρ).mp h
    rw [hK1] at hzσ
    exact Or.inl (hzρ.eq hzσ).symm
  · have hK1 : σ.K = ρ'.K := (Q3T6.Mu.muTabElt_eq_iff hP hV σ ρ').mp h
    rw [hK1] at hzσ
    exact Or.inl (hzρ'.eq hzσ).symm
  · have hK1 : σ.K = ρ₃.K := (Q3T6.Mu.muTabElt_eq_iff hP hV σ ρ₃).mp h
    rw [hK1] at hzσ
    exact Or.inr (Or.inl (hj.eq hzσ).symm)
  · have e1 : σ.img = ρ.img * ρ₃.img * ρ.img := congrArg Subtype.val h
    have hval : σ.img = Thompson.piG V ρ.r * ρ₃.img * (Thompson.piG V ρ.r)⁻¹ := by
      show σ.img = ρ.img * ρ₃.img * ρ.img⁻¹
      rw [hinv1]
      exact e1
    have hK := hconjK ρ.r ρ.r_mem_normalizer σ ρ₃ hval
    rw [hK] at hzσ
    exact Or.inr (Or.inr (((hj.conj ρ.r).eq hzσ).symm.trans hr1))
  · have e1 : σ.img = ρ'.img * ρ₃.img * ρ'.img := congrArg Subtype.val h
    have hval : σ.img = Thompson.piG V ρ'.r * ρ₃.img * (Thompson.piG V ρ'.r)⁻¹ := by
      show σ.img = ρ'.img * ρ₃.img * ρ'.img⁻¹
      rw [hinv2]
      exact e1
    have hK := hconjK ρ'.r ρ'.r_mem_normalizer σ ρ₃ hval
    rw [hK] at hzσ
    exact Or.inr (Or.inr (((hj.conj ρ'.r).eq hzσ).symm.trans hr2))
  · have e1 : σ.img = ρ.img * ρ'.img * ρ₃.img * ρ'.img * ρ.img := congrArg Subtype.val h
    have hm : ρ.r * ρ'.r ∈ Subgroup.normalizer (V : Set Q) :=
      Subgroup.mul_mem _ ρ.r_mem_normalizer ρ'.r_mem_normalizer
    have hpm : Thompson.piG V (ρ.r * ρ'.r) = ρ.img * ρ'.img :=
      Thompson.piG_mul ρ.r_mem_normalizer ρ'.r_mem_normalizer
    have hval : σ.img = Thompson.piG V (ρ.r * ρ'.r) * ρ₃.img *
        (Thompson.piG V (ρ.r * ρ'.r))⁻¹ := by
      rw [hpm, mul_inv_rev, hinv1, hinv2, e1]
      simp only [mul_assoc]
    have hK := hconjK (ρ.r * ρ'.r) hm σ ρ₃ hval
    rw [hK] at hzσ
    have hcalc : (ρ.r * ρ'.r) * j * (ρ.r * ρ'.r)⁻¹ = j := by
      calc (ρ.r * ρ'.r) * j * (ρ.r * ρ'.r)⁻¹ = ρ.r * (ρ'.r * j * ρ'.r⁻¹) * ρ.r⁻¹ := by group
        _ = ρ.r * (z * j) * ρ.r⁻¹ := by rw [hr2]
        _ = (ρ.r * z * ρ.r⁻¹) * (ρ.r * j * ρ.r⁻¹) := by group
        _ = z * (z * j) := by rw [hzc, hr1]
        _ = j := by rw [← mul_assoc, hz.sq, one_mul]
    exact Or.inr (Or.inl (((hj.conj (ρ.r * ρ'.r)).eq hzσ).symm.trans hcalc))

end B0Sec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.WF
