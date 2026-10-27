module

public import CFSG.LargeExtraspecial.AS35MAxB
public import CFSG.LargeExtraspecial.AS35HSixEightC
public import CFSG.LargeExtraspecial.AS35HSixEightB
public import CFSG.LargeExtraspecial.AS35MInd

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CQuotE

namespace S14

@[expose] def AschbacherSixSevenMbarStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (S : Setting G), S.SixHyp → S.SixFiveConcl →
    ∀ r ∈ S.DSet, ∀ t ∈ S.DSet, orderOf (r * t) = 3 → ∀ hxM : r * t ∈ S.M,
      S.MbarOddHyp hxM ∧ S.MbarOTwoHyp hxM

end S14

namespace Setting

variable {G : Type} [Group G] [Finite G] (S : Setting G)

omit [Finite G] in
theorem conj_zCxE_sq {E : Set G} {x : G} (hE : S.DescentSet E x) (c : Cx E) :
    (c * S.zCxE hE * c⁻¹) ^ (2 ^ 1) = 1 := by
  rw [pow_one, conj_pow, S.zCxE_sq, mul_one, mul_inv_cancel]

theorem commute_conj_z_of_sixEightE (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (h59 : S14.AschbacherFiveNineOneStmt) (hU : S14.AschTwoAutStmt) {r t h : G}
    (hr : r ∈ S.DSet) (ht : t ∈ S.DSet) (hh : h * S.z * h⁻¹ = t) (hrM : r ∈ S.M)
    (htM : t ∈ S.M) (h3 : orderOf (r * t) = 3) {E : Set G} (hE : S.DescentSet E (r * t))
    (htE : ∀ e ∈ E, t * e * t⁻¹ ∈ E) (htE' : ∀ e ∈ E, t⁻¹ * e * t ∈ E)
    (hfixne : fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥) (hcent : S.QuotCentHypE E)
    (hO2 : S.QuotOTwoHypE E) (hw : 2 ≤ (S.quotE hE h3 hfixne hcent hO2).width)
    (hA2 : (S.quotE hE h3 hfixne hcent hO2).AschTwo) (c : Cx E) :
    t * ((c : G) * S.z * (c : G)⁻¹) = (c : G) * S.z * (c : G)⁻¹ * t := by
  have hS4 := hS.sixFour
  set T := S.quotE hE h3 hfixne hcent hO2 with hT
  have hτQ : ∀ q ∈ T.QG, conjQ t htE htE' q = q := by
    intro q hq
    rw [quotE_QG] at hq
    obtain ⟨d, hdQ, rfl⟩ := (S.mem_QQE).mp hq
    rw [conjQ_mkQ]
    congr 1
    apply Subtype.ext
    rw [coe_conjCx]
    have hdx : (d : G) ∈ S.QG ⊓ centralizer ({r * t} : Set G) := by
      rw [← hE.QG_inf]
      exact mem_inf.mpr ⟨hdQ, d.2⟩
    exact S.commute_of_mem_cqx_rt hS hr ht hrM htM h3 hdQ
      (mem_centralizer_singleton_iff.mp (mem_inf.mp hdx).2)
  have hτ : ∀ c' : Cx E, conjQ t htE htE' (mkQ E c' * T.z * (mkQ E c')⁻¹) =
      mkQ E (conjCx t htE htE' (c' * S.zCxE hE * c'⁻¹)) := by
    intro c'
    rw [quotE_z, zQuotE, ← CQuotE.mkQ_conj, conjQ_mkQ]
  have hpow : ∀ w : Cx E, w ^ (2 ^ 1) = 1 → (conjCx t htE htE' w) ^ (2 ^ 1) = 1 := by
    intro w hw1
    rw [← map_pow, hw1, map_one]
  have hcoe : ∀ c' : Cx E, ((conjCx t htE htE' (c' * S.zCxE hE * c'⁻¹) : Cx E) : G) =
      t * ((c' : G) * S.z * (c' : G)⁻¹) * t⁻¹ := fun c' => rfl
  rcases (hU (GQ E) T hw hA2).1 (conjQ t htE htE') hτQ with h1 | h2
  · have e1 := h1 (mkQ E c)
    rw [hτ, quotE_z, zQuotE, ← CQuotE.mkQ_conj] at e1
    have e2 := eq_of_mkQ_eq (hpow _ (S.conj_zCxE_sq hE c)) (S.conj_zCxE_sq hE c) e1
    have e3 := congrArg (fun w : Cx E => (w : G)) e2
    simp only [hcoe] at e3
    calc t * ((c : G) * S.z * (c : G)⁻¹) = t * ((c : G) * S.z * (c : G)⁻¹) * t⁻¹ * t := by
          group
      _ = (c : G) * S.z * (c : G)⁻¹ * t := by
          rw [e3]
          rfl
  ·
    have e : ∀ c' : Cx E, t * ((c' : G) * S.z * (c' : G)⁻¹) * t⁻¹ =
        S.z * ((c' : G) * S.z * (c' : G)⁻¹) * S.z⁻¹ := by
      intro c'
      have e1 := h2 (mkQ E c')
      rw [hτ, quotE_z, zQuotE, ← CQuotE.mkQ_conj, ← CQuotE.mkQ_conj] at e1
      have hsq : (S.zCxE hE * (c' * S.zCxE hE * c'⁻¹) * (S.zCxE hE)⁻¹) ^ (2 ^ 1) = 1 := by
        rw [conj_pow, S.conj_zCxE_sq hE c', mul_one, mul_inv_cancel]
      have e2 := eq_of_mkQ_eq (hpow _ (S.conj_zCxE_sq hE c')) hsq e1
      have e3 := congrArg (fun w : Cx E => (w : G)) e2
      simp only [hcoe] at e3
      rw [e3]
      rfl
    have hd : h⁻¹ * S.z * h⁻¹⁻¹ ∈ S.DSet := by
      rw [inv_inv]
      exact S.mem_DAt.mp (S.z_mem_DAt hS4 ht hh)
    have htR : t ∈ oTwoCent (t * S.z) := by
      have h4 := CQuot.conj_mem_oTwoCent_conj h (h59 G S hS h65 _ hd)
      have h5 : h * (S.z * (h⁻¹ * S.z * h⁻¹⁻¹)) * h⁻¹ = t * S.z := by
        rw [← hh]
        group
      rwa [h5, hh] at h4
    have hcomm_tz : ∀ c' : Cx E, (t * S.z) * ((c' : G) * S.z * (c' : G)⁻¹) =
        ((c' : G) * S.z * (c' : G)⁻¹) * (t * S.z) := by
      intro c'
      have e1 := e c'
      have htz : t * S.z = S.z * t := S.z_comm htM
      have h6 : t * S.z * ((c' : G) * S.z * (c' : G)⁻¹) * (t * S.z)⁻¹ =
          (c' : G) * S.z * (c' : G)⁻¹ := by
        calc t * S.z * ((c' : G) * S.z * (c' : G)⁻¹) * (t * S.z)⁻¹ =
            S.z * (t * ((c' : G) * S.z * (c' : G)⁻¹) * t⁻¹) * S.z⁻¹ := by
              rw [htz]; group
          _ = S.z * (S.z * ((c' : G) * S.z * (c' : G)⁻¹) * S.z⁻¹) * S.z⁻¹ := by rw [e1]
          _ = (S.z * S.z) * ((c' : G) * S.z * (c' : G)⁻¹) * (S.z * S.z)⁻¹ := by group
          _ = (c' : G) * S.z * (c' : G)⁻¹ := by rw [S.z_mul_z]; group
      calc t * S.z * ((c' : G) * S.z * (c' : G)⁻¹) =
          t * S.z * ((c' : G) * S.z * (c' : G)⁻¹) * (t * S.z)⁻¹ * (t * S.z) := by group
        _ = ((c' : G) * S.z * (c' : G)⁻¹) * (t * S.z) := by rw [h6]
    have hXtz : ∀ a ∈ S.XCxE hE, (a : G) ∈ centralizer ({t * S.z} : Set G) := by
      intro a ha
      have hle : S.XCxE hE ≤ (centralizer ({t * S.z} : Set G)).comap (Cx E).subtype := by
        rw [XCxE, closure_le]
        rintro _ ⟨c', rfl⟩
        rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff]
        exact (hcomm_tz c').symm
      exact hle ha
    have hN : (oTwoCent (t * S.z)).comap (Cx E).subtype ⊓ S.XCxE hE = ⊥ :=
      S.eq_bot_of_normal_two_XCxE hE h3 hfixne hcent hO2 hA2 inf_le_right
        (fun a ha n hn => mem_inf.mpr ⟨conj_mem_oTwoCent (hXtz a ha) (mem_inf.mp hn).1,
          mul_mem (mul_mem ha (mem_inf.mp hn).2) (inv_mem ha)⟩)
        (((isPGroup_oTwoCent _).comap_of_injective _ (Cx E).subtype_injective).to_le
          inf_le_left)
    have hzX : S.zCxE hE ∈ S.XCxE hE := subset_closure ⟨1, by group⟩
    have hwX : c * S.zCxE hE * c⁻¹ ∈ S.XCxE hE := subset_closure ⟨c, rfl⟩
    have hy : conjCx t htE htE' (c * S.zCxE hE * c⁻¹) * (c * S.zCxE hE * c⁻¹)⁻¹ ∈
        (oTwoCent (t * S.z)).comap (Cx E).subtype ⊓ S.XCxE hE := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · change t * ((c : G) * S.z * (c : G)⁻¹) * t⁻¹ * ((c : G) * S.z * (c : G)⁻¹)⁻¹ ∈
          oTwoCent (t * S.z)
        rw [show t * ((c : G) * S.z * (c : G)⁻¹) * t⁻¹ * ((c : G) * S.z * (c : G)⁻¹)⁻¹ =
          t * (((c : G) * S.z * (c : G)⁻¹) * t⁻¹ * ((c : G) * S.z * (c : G)⁻¹)⁻¹) by group]
        exact mul_mem htR (conj_mem_oTwoCent (hXtz _ hwX) (inv_mem htR))
      · have h7 : conjCx t htE htE' (c * S.zCxE hE * c⁻¹) =
            S.zCxE hE * (c * S.zCxE hE * c⁻¹) * (S.zCxE hE)⁻¹ := Subtype.ext (by
          rw [hcoe]
          exact e c)
        rw [h7]
        exact mul_mem (mul_mem (mul_mem hzX hwX) (inv_mem hzX)) (inv_mem hwX)
    rw [hN, mem_bot, mul_inv_eq_one] at hy
    have e3 := congrArg (fun w : Cx E => (w : G)) hy
    simp only [hcoe] at e3
    calc t * ((c : G) * S.z * (c : G)⁻¹) = t * ((c : G) * S.z * (c : G)⁻¹) * t⁻¹ * t := by
          group
      _ = (c : G) * S.z * (c : G)⁻¹ * t := by
          rw [e3]
          rfl

theorem sixSevenE_hyps (hS : S.SixHyp) (h65 : S.SixFiveConcl)
    (h67 : S14.AschbacherSixSevenMbarStmt) {r t : G} (hr : r ∈ S.DSet) (ht : t ∈ S.DSet)
    (hrM : r ∈ S.M) (htM : t ∈ S.M) (h3 : orderOf (r * t) = 3) :
    ∃ hE : S.DescentSet (S.EOdd (r * t) : Set G) (r * t),
      (∀ e ∈ (S.EOdd (r * t) : Set G), t * e * t⁻¹ ∈ (S.EOdd (r * t) : Set G)) ∧
      (∀ e ∈ (S.EOdd (r * t) : Set G), t⁻¹ * e * t ∈ (S.EOdd (r * t) : Set G)) ∧
      fixSpace (S.rhoL hE.x_mem_M) ≠ ⊥ ∧ S.QuotCentHypE (S.EOdd (r * t) : Set G) ∧
      S.QuotOTwoHypE (S.EOdd (r * t) : Set G) ∧
      finrank (ZMod 2) (fixSpace (S.rhoL hE.x_mem_M)) + 4 = 2 * S.width := by
  have hxM : r * t ∈ S.M := S.M.mul_mem hrM htM
  have hxo : Odd (orderOf (r * t)) := by rw [h3]; decide
  have hE := S.descentSet_EOdd hxM hxo
  obtain ⟨hN1, hN2⟩ := h67 G S hS h65 r hr t ht h3 hxM
  have hrr := S.mul_self_of_isConj (S.isConj_of_mem_ESet hr.1)
  have htt := S.mul_self_of_isConj (S.isConj_of_mem_ESet ht.1)
  have htx : t * (r * t) * t⁻¹ = r * t ∨ t * (r * t) * t⁻¹ = (r * t)⁻¹ :=
    Or.inr (conj_rt_eq_inv hrr htt)
  obtain ⟨-, hdim⟩ := S.fixSpace_rt hS hr ht hrM htM h3
  have hn4 := h65.four_le_width
  refine ⟨hE, fun e he => S.conj_mem_EOdd htM htx he,
    fun e he => S.conj_inv_mem_EOdd htM htx he, ?_, S.quotCentHypE_EOdd hxM h3 hN1,
    S.quotOTwoHypE_EOdd hxM h3 hN2, hdim⟩
  intro h0
  rw [h0, finrank_bot] at hdim
  omega

theorem sixEightOneE (ih : S14.AschbacherBelow (Nat.card G)) (hS : S.SixHyp)
    (h65 : S.SixFiveConcl) (hT : S14.SixFiveTransvectionStmt)
    (h67 : S14.AschbacherSixSevenMbarStmt) (h59 : S14.AschbacherFiveNineOneStmt)
    (hU : S14.AschTwoAutStmt) {s : G} (hs : s ∈ S.DSet) {h : G}
    (ht : h * S.z * h⁻¹ ∈ S.DSet) (hst : s * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * s)
    (hne : s ≠ h * S.z * h⁻¹) : s ∈ S.DAt h := by
  have hS4 := hS.sixFour
  have hsM := S.mem_M_of_mem_ESet hS4 hs.1
  have htM := S.mem_M_of_mem_ESet hS4 ht.1
  by_cases hρ : S.ρ ⟨s, hsM⟩ = S.ρ ⟨h * S.z * h⁻¹, htM⟩
  · exact S.mem_DAt_of_mem_zConj' hS ht rfl (S.mem_zConj_of_rho_eq hS hs ht rfl hsM htM hρ) hne
  have hst' : S.ρ ⟨s, hsM⟩ * S.ρ ⟨h * S.z * h⁻¹, htM⟩ =
      S.ρ ⟨h * S.z * h⁻¹, htM⟩ * S.ρ ⟨s, hsM⟩ := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hst
  obtain ⟨_, ⟨r, hr, hrM, rfl⟩, hrs, hrt⟩ := (hT G S hS h65).1 _ (S.ρ_mem_DbarAsc hs hsM) _
    (S.ρ_mem_DbarAsc ht htM) hst' hρ
  have hrs' : S.ρ ⟨r, hrM⟩ ≠ S.ρ ⟨s, hsM⟩ := by
    intro h1
    apply hrt
    rw [h1, hst']
  have hrs2 : r * s = s * r := S.fiveThirteen hS h65 hr hs hrM hsM hrs hrs'
  have h3 := S.orderOf_mul_eq_three_of_not_commute hS h65 hr ht hrM htM hrt
  have hxM : r * (h * S.z * h⁻¹) ∈ S.M := S.M.mul_mem hrM htM
  have hx3 : (r * (h * S.z * h⁻¹)) ^ 3 = 1 := pow_three_of_orderOf h3
  have hxs : r * (h * S.z * h⁻¹) * s = s * (r * (h * S.z * h⁻¹)) := by
    rw [mul_assoc, ← hst, ← mul_assoc, hrs2, mul_assoc]
  have hfix := S.commSpace_le_fixSpace_rt h65 hr hs ht hrM hsM htM hrs hrs' hst'.symm
    (Ne.symm hρ)
  obtain ⟨⟨c, hcE, hcz⟩, hnc⟩ := S.exists_conj_eq_z_of_sixEightE hxM hx3 hsM hxs hfix hS hs
  obtain ⟨hE, htE, htE', hfixne, hcent, hO2, hdim⟩ :=
    S.sixSevenE_hyps hS h65 h67 hr ht hrM htM h3
  have hn4 := h65.four_le_width
  have hw : 2 ≤ (S.quotE hE h3 hfixne hcent hO2).width := by
    have := S.two_mul_quotE_width hE h3 hfixne hcent hO2
    omega
  have hA2 := S.quotE_aschTwo hE h3 hfixne hcent hO2 ih hw hS.weak hS.zInOTwo hnc
  obtain ⟨l₁, hl₁, hl₁e⟩ := (hU _ _ hw hA2).2.1 (mkQ _ (⟨c, hcE⟩ : Cx _))
  rw [← S.map_XCxE hE h3 hfixne hcent hO2] at hl₁
  obtain ⟨l, hlX, rfl⟩ := hl₁
  rw [quotE_z, zQuotE, ← CQuotE.mkQ_conj, ← CQuotE.mkQ_conj] at hl₁e
  have e2 := eq_of_mkQ_eq (S.conj_zCxE_sq hE _) (S.conj_zCxE_sq hE l) hl₁e
  have e3 : s = (l : G) * S.z * (l : G)⁻¹ := by
    have := congrArg (fun w : Cx (S.EOdd (r * (h * S.z * h⁻¹)) : Set G) => (w : G)) e2
    simp only [coe_mul, coe_inv] at this
    rw [← hcz]
    exact this
  have hXt : S.XCxE hE ≤ (centralizer ({h * S.z * h⁻¹} : Set G)).comap
      (Cx (S.EOdd (r * (h * S.z * h⁻¹)) : Set G)).subtype := by
    rw [XCxE, closure_le]
    rintro _ ⟨c', rfl⟩
    rw [SetLike.mem_coe, mem_comap, mem_centralizer_singleton_iff]
    exact (S.commute_conj_z_of_sixEightE hS h65 h59 hU hr ht rfl hrM htM h3 hE htE htE' hfixne
      hcent hO2 hw hA2 c').symm
  have hlt : (l : G) * (h * S.z * h⁻¹) = h * S.z * h⁻¹ * l :=
    mem_centralizer_singleton_iff.mp (hXt hlX)
  rw [e3]
  exact S.conj_mem_DAt_of_commute hlt (S.z_mem_DAt hS4 ht rfl)

end Setting

namespace S14

theorem aschbacherSixEightOneStmt_of' (hT : SixFiveTransvectionStmt)
    (h67 : AschbacherSixSevenMbarStmt) (h59 : AschbacherFiveNineOneStmt)
    (hU : AschTwoAutStmt) : AschbacherSixEightOneStmt :=
  fun _ _ _ S ih hS h65 _ hs _ ht hst hne => S.sixEightOneE ih hS h65 hT h67 h59 hU hs ht hst hne

end S14

end CFSG.LargeExtraspecial
