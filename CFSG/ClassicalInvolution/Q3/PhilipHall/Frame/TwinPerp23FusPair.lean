module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23FusLie
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf11Act

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDisc CFSG.ClassicalInvolution.Uniform
  CFSG.ClassicalInvolution.Q3.Q3NL CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge CFSG.ClassicalInvolution.Disconnected
open scoped commutatorElement

theorem mem_sup_of_commutes {X : Type} [Group X] {A B : Subgroup X}
    (h : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) {x : X} (hx : x ∈ A ⊔ B) :
    ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  rw [← Subgroup.closure_eq A, ← Subgroup.closure_eq B, ← Subgroup.closure_union] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a₁, ha₁, b₁, hb₁, rfl⟩ := hx
    obtain ⟨a₂, ha₂, b₂, hb₂, rfl⟩ := hy
    refine ⟨a₁ * a₂, A.mul_mem ha₁ ha₂, b₁ * b₂, B.mul_mem hb₁ hb₂, ?_⟩
    have h1 : a₂ * b₁ = b₁ * a₂ := h a₂ ha₂ b₁ hb₁
    calc a₁ * b₁ * (a₂ * b₂) = a₁ * (b₁ * a₂) * b₂ := by group
      _ = a₁ * (a₂ * b₁) * b₂ := by rw [h1]
      _ = a₁ * a₂ * (b₁ * b₂) := by group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨a⁻¹, A.inv_mem ha, b⁻¹, B.inv_mem hb, ?_⟩
    have h1 : a * b = b * a := h a ha b hb
    calc (a * b)⁻¹ = (b * a)⁻¹ := by rw [h1]
      _ = a⁻¹ * b⁻¹ := by group

theorem sq_eq_one_of_central_q8 {X : Type} [Group X] {J : Subgroup X} (e : ↥J ≃* QuaternionGroup 2)
    {j : X} (hj : j ∈ J) (hc : ∀ y ∈ J, j * y = y * j) : j * j = 1 := by
  have hq : ∀ q : QuaternionGroup 2, (∀ r, q * r = r * q) → q * q = 1 := by decide
  have h1 : (e ⟨j, hj⟩) * (e ⟨j, hj⟩) = 1 := hq _ (fun r => by
    obtain ⟨y, rfl⟩ := e.surjective r
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc y y.2))
  have h2 : (⟨j, hj⟩ : ↥J) * ⟨j, hj⟩ = 1 := by
    apply e.injective
    rw [map_mul, map_one]
    exact h1
  simpa using congrArg Subtype.val h2


section Pair

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem pair_members_two (hS : TwinDisc.Q8Section X Φ) {J₁ J₂ : Subgroup X} (h₁ : J₁ ∈ Φ)
    (h₂ : J₂ ∈ Φ) {w : X} (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w)
    (hpair : ∀ M ∈ Φ, M = J₁ ∨ M = J₂) : IsPGroup 2 ↥J₁ ∧ IsPGroup 2 ↥J₂ := by
  have hcentw : Subgroup.centralizer ({w} : Set X) = ⊤ := by
    rw [eq_top_iff, ← hS.gen]
    refine iSup₂_le fun M hM x hx => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hpair M hM with rfl | rfl
    · exact (hw₁.commute_of_mem hx).symm
    · exact (hw₂.commute_of_mem hx).symm
  have hodd : oddCoreImg (Subgroup.centralizer ({w} : Set X)) = ⊥ := by
    rw [hcentw]
    exact TwinExitPf12.oddCoreIn_top_eq_bot' hS.oddFree
  exact ⟨isPGroup_of_oddCent hS.hyp h₁ hw₁ hodd (hS.two _ h₁),
    isPGroup_of_oddCent hS.hyp h₂ hw₂ hodd (hS.two _ h₂)⟩

theorem pair_section_false
    (hS : TwinDisc.Q8Section X Φ) {J₁ J₂ : Subgroup X} (h₁ : J₁ ∈ Φ) (h₂ : J₂ ∈ Φ) {w : X}
    (hw₁ : IsUniqueInvolution J₁ w) (hw₂ : IsUniqueInvolution J₂ w)
    (hpair : ∀ M ∈ Φ, M = J₁ ∨ M = J₂) (hcomm : Commutes J₁ J₂) {z : X}
    (hz₁ : ∀ y ∈ J₁, z * y = y * z) (hz₂ : ∀ y ∈ J₂, z * y = y * z) : z = 1 ∨ z = w := by
  classical
  have hcentz : ∀ y : X, z * y = y * z := by
    have hle : (⊤ : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X) := by
      rw [← hS.gen]
      refine iSup₂_le fun M hM y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      rcases hpair M hM with rfl | rfl
      · exact (hz₁ y hy).symm
      · exact (hz₂ y hy).symm
    intro y
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top y))).symm
  have hsup : (⊤ : Subgroup X) ≤ J₁ ⊔ J₂ := by
    rw [← hS.gen]
    refine iSup₂_le fun M hM => ?_
    rcases hpair M hM with rfl | rfl
    · exact le_sup_left
    · exact le_sup_right
  obtain ⟨hA₁, hA₂⟩ := pair_members_two hS h₁ h₂ hw₁ hw₂ hpair
  obtain ⟨e₁⟩ := hS.q8 J₁ h₁ J₁ ⟨le_rfl, hA₁, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨e₂⟩ := hS.q8 J₂ h₂ J₂ ⟨le_rfl, hA₂, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨j, hj, j', hj', hzj⟩ := mem_sup_of_commutes hcomm (hsup (Subgroup.mem_top z))
  have hjc : ∀ y ∈ J₁, j * y = y * j := by
    intro y hy
    have h1 := hcentz y
    rw [hzj] at h1
    have h2 : y * j' = j' * y := hcomm y hy j' hj'
    have : (j * y) * j' = (y * j) * j' := by
      calc (j * y) * j' = j * (y * j') := by group
        _ = j * (j' * y) := by rw [h2]
        _ = j * j' * y := by group
        _ = y * (j * j') := h1
        _ = (y * j) * j' := by group
    exact mul_right_cancel this
  have hj'c : ∀ y ∈ J₂, j' * y = y * j' := by
    intro y hy
    have h1 := hcentz y
    rw [hzj] at h1
    have h2 : j * y = y * j := hcomm j hj y hy
    have : j * (j' * y) = j * (y * j') := by
      calc j * (j' * y) = j * j' * y := by group
        _ = y * (j * j') := h1
        _ = (y * j) * j' := by group
        _ = (j * y) * j' := by rw [h2]
        _ = j * (y * j') := by group
    exact mul_left_cancel this
  have hj2 := sq_eq_one_of_central_q8 e₁ hj hjc
  have hj'2 := sq_eq_one_of_central_q8 e₂ hj' hj'c
  rcases hw₁.unique j hj hj2 with rfl | rfl <;> rcases hw₂.unique j' hj' hj'2 with rfl | rfl
  · left; rw [hzj]; simp
  · right; rw [hzj]; simp
  · right; rw [hzj]; simp
  · left; rw [hzj]; exact hw₁.sq

end Pair

section PairY

variable {n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}
  {K' W : Subgroup Y} {u e g : Y}

theorem pair_impossible (hc : P23Cfg n Y R S t K' W u e g)
    (hpair : ∀ M ∈ TwinDisc.secFam (Om R) e,
      M = TwinDisc.secImg (Om R) e (tightCore R) ∨ M = TwinDisc.secImg (Om R) e K') : False := by
  classical
  obtain ⟨Q, Q', hTu, hTe⟩ := layerTwins_both hc
  have hd := hc.data
  have hC := CoreData.of_S hc.std.perp.core
  have hΩ : HypOmegaGen (Om R) := hC.hyp
  have hK : tightCore R ∈ Om R := CoreAssembly.mem_conjClass_self _
  have hc2' : IsPGroup 2 (Subgroup.zpowers e) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.he2
  have hu2' : IsPGroup 2 (Subgroup.zpowers u) :=
    CFSG.ClassicalInvolution.Asc77.ExactLayer.isPGroup_zpowers_of_sq_eq_one hd.hu2
  have he2' := hc2'
  have h2 : ∀ M ∈ Om R, IsPGroup 2 (↥M ⧸ classicalInvolutionOddCore ↥M) :=
    TwinADescent3.isPGroup_two_quotient_conjClass
      (TwinEdge.isPGroup_two_quotient_of_le (tightCore_le R) hC.datum.twoGroup)
  have hS := p23_q8Section hc.std.perp hd.he2
  obtain ⟨htC, htY, hzz1⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2' hTe.hJ hTe.hw
  obtain ⟨htC', htY', hzz2⟩ := TwinDisc.isUniqueInvolution_secImg hΩ hc2' hTe.hJ' hTe.hw'
  have hJ1 := TwinDisc.secImg_mem_secFam hTe.hJ
  have hJ2 := TwinDisc.secImg_mem_secFam hTe.hJ'
  have hne12 := TwinPerpV3.secImg_ne_of_twin hΩ hc2' hTe.hJ hTe.hJ' hTe.hne hTe.hw hTe.hw'
  obtain ⟨R₁, R₁', b₁, b', hR₁, hR₁', hRD, hR'D, hcommR, hb₁R, hb'R', ob₁, ob', hub, hne_ue⟩ :=
    e_decomp hc
  have hNe := normalizer_le_centralizer_e hd
  have hR₁e : R₁ ≤ Subgroup.centralizer ({e} : Set Y) := hRD.2.trans hNe
  have hR₁'e : R₁' ≤ Subgroup.centralizer ({e} : Set Y) := hR'D.2.trans hNe
  have hKtq : tightCore R ∈ tqMembers3 (Om R) e :=
    ⟨hK, TwinADescent3.mem_tq_of_sylCent hΩ h2 hK ⟨R₁, hR₁, hR₁e⟩⟩
  have hK'tq : K' ∈ tqMembers3 (Om R) e :=
    ⟨hc.std.hK'.1, TwinADescent3.mem_tq_of_sylCent hΩ h2 hc.std.hK'.1 ⟨R₁', hR₁', hR₁'e⟩⟩
  have hpair' : ∀ M ∈ TwinDisc.secFam (Om R) e,
      M = TwinDisc.secImg (Om R) e (conjSub g (tightCore R)) ∨
        M = TwinDisc.secImg (Om R) e (conjSub g K') := by
    intro M hM
    rcases hpair M hM with hM' | hM' <;> rcases hpair _ hJ1 with h1 | h1 <;>
      rcases hpair _ hJ2 with h2 | h2 <;>
      first
        | exact Or.inl (hM'.trans h1.symm)
        | exact Or.inr (hM'.trans h2.symm)
        | exact absurd (h1.trans h2.symm) hne12
  obtain ⟨hP1, hP2⟩ := pair_members_two hS hJ1 hJ2 hzz1 hzz2 hpair'
  have hu_core : u ∈ TwinDisc.coreLayer (Om R) e := by
    have hR₁c : R₁ ≤ TwinADescent.coreAt e (tightCore R) :=
      ((TwinADescent.isSylow2In_coreAt_iff hc2' hKtq.2).mpr ⟨hR₁, hR₁e⟩).1
    have hR₁'c : R₁' ≤ TwinADescent.coreAt e K' :=
      ((TwinADescent.isSylow2In_coreAt_iff hc2' hK'tq.2).mpr ⟨hR₁', hR₁'e⟩).1
    rw [hub]
    exact (TwinDisc.coreLayer (Om R) e).mul_mem
      (TwinDisc.coreAt_le_coreLayer hKtq (hR₁c hb₁R))
      (TwinDisc.coreAt_le_coreLayer hK'tq (hR₁'c hb'R'))
  obtain ⟨uC, huC, huCe0⟩ := hu_core
  have huCe : (uC : Y) = u := huCe0
  set uH : ↥(TwinDisc.coreHull (Om R) e) := ⟨uC, huC⟩ with huH
  set ub : SecQ R e := QuotientGroup.mk uH with hub'
  have hcommQ : ∀ {Z : Subgroup Y}, Z ≤ Subgroup.centralizer ({u} : Set Y) →
      ∀ a : ↥(TwinDisc.coreHull (Om R) e),
        (((a : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) ∈ Z) → uH * a = a * uH := by
    intro Z hZ a ha
    have h1 : ((a : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) * u =
        u * ((a : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hZ ha)
    exact Subtype.ext (Subtype.ext (by
      show (uC : Y) * ((a : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) =
        ((a : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) * (uC : Y)
      rw [huCe]; exact h1.symm))
  have hz₁ : ∀ y ∈ TwinDisc.secImg (Om R) e (conjSub g (tightCore R)), ub * y = y * ub := by
    intro y hy
    obtain ⟨a, haQ, rfl⟩ := exists_of_mem_secImg_syl hc2' hTe.hJ hTe.hQ hTe.hQc hP1 hy
    show QuotientGroup.mk uH * QuotientGroup.mk a = QuotientGroup.mk a * QuotientGroup.mk uH
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommQ hTu.hQc a haQ]
  have hz₂ : ∀ y ∈ TwinDisc.secImg (Om R) e (conjSub g K'), ub * y = y * ub := by
    intro y hy
    obtain ⟨a, haQ, rfl⟩ := exists_of_mem_secImg_syl hc2' hTe.hJ' hTe.hQ' hTe.hQ'c hP2 hy
    show QuotientGroup.mk uH * QuotientGroup.mk a = QuotientGroup.mk a * QuotientGroup.mk uH
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hcommQ hTu.hQ'c a haQ]
  have hcomm12 : Commutes (TwinDisc.secImg (Om R) e (conjSub g (tightCore R)))
      (TwinDisc.secImg (Om R) e (conjSub g K')) := by
    intro y₁ hy₁ y₂ hy₂
    obtain ⟨a, haQ, rfl⟩ := exists_of_mem_secImg_syl hc2' hTe.hJ hTe.hQ hTe.hQc hP1 hy₁
    obtain ⟨b, hbQ, rfl⟩ := exists_of_mem_secImg_syl hc2' hTe.hJ' hTe.hQ' hTe.hQ'c hP2 hy₂
    show QuotientGroup.mk a * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (Subtype.ext (hTe.hcomm _ haQ _ hbQ))
  have hcases := pair_section_false hS hJ1 hJ2 hzz1 hzz2 hpair' hcomm12 hz₁ hz₂
  have hu1 := hd.hu1
  rcases hcases with h1 | h1
  ·
    have hmem : uH ∈ classicalInvolutionOddCore ↥(TwinDisc.coreHull (Om R) e) :=
      (QuotientGroup.eq_one_iff _).mp h1
    have := TwinDisc.coe_mem_oddCoreOf_coreLayer (c := e) (Ω := Om R) hmem
    have hu0 : u = 1 := eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _)
      (by rw [← huCe]; exact this) hu2'
    exact hu1 hu0
  ·
    have hmem := QuotientGroup.eq.mp h1
    have h3 := TwinDisc.coe_mem_oddCoreOf_coreLayer (c := e) (Ω := Om R) hmem
    have h4 : ((((uH⁻¹ * (⟨⟨u * e, htC⟩, htY⟩ : ↥(TwinDisc.coreHull (Om R) e))) :
        ↥(TwinDisc.coreHull (Om R) e)) : ↥(Subgroup.centralizer ({e} : Set Y))) : Y) = e := by
      show (uC : Y)⁻¹ * (u * e) = e
      rw [huCe]; group
    rw [h4] at h3
    exact hd.he1 (eq_one_of_isPGroup_of_mem_odd (oddCoreOf_odd_natCard _) h3 he2')

end PairY


end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp23.Fus
