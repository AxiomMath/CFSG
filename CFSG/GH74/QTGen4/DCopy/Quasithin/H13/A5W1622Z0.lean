module

public import CFSG.Quasithin.H13.A5W1622s
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622F4Proof
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5W1622v

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise commutatorElement

theorem lem13622Case4Z0_of_F4 (h1222 : Stmt12_2_2_F4)
    (h517 : Stmt5_1_7_one_F4) (h132two : Stmt13_3_2_two_F4) (h132fsu : Stmt13_3_2_three_fsu_F4)
    (h132A5 : Stmt13_3_2_three_A5_F4) (h331 : Stmt3_3_1_F4) (h1327 : Stmt13_2_7_F4)
    (h37 : Vol2Native.A37ForSQTKCat) (h39 : Vol2Native.A39ForSQTKCat)
    (h45 : C134Case4Lemma45Corr_F4) : Lem13622Case4Z0_F4 := by
  have hF4 : C134Case4F_F4 := c134Case4F_of_lemma45_F4 h45
  intro G _ _ T L V S hH K₀ hK₀G hK₀ hTK₀ hz _ ⟨F, _, _, α, hF2, hα⟩ hi4 hvCQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK₀p : ⁅K₀, K₀⁆ = K₀ := perfect_of_mem_cComp hK₀

  have hchar : CharTwo (K₀ ⊔ S.Tv) :=
    C1GN.charTwo_of_le hH.hF (S.isSylowTwoOf_Tv_F4 h1222 h517) le_sup_right (sup_le hK₀G S.Tv_le_Gv)
  have hcard2 : Fintype.card F = Fintype.card (ZMod 2) := by rw [hF2, ZMod.card]
  let ε : F ≃+* ZMod 2 := FiniteField.ringEquivOfCardEq hcard2
  let eK : (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
    (QuotientGroup.quotientMulEquivOfEq hα.2.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hα.1)
  have hl : IsPSL 3 2 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := Vol2Native.A312L.Seven.isPSL_three_two
    (eK.trans ((CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F).symm.trans
      (slMulEquivOfRingEquiv ε 3)))
  have hlist : IsPSL 3 2 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∨ IsAlt 6 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ∨
      IsPSU 3 3 1 (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := Or.inl hl
  have hRk := SBc11.isRankTwoLie2Derived_of_list
    (isList_of_mulEquiv (quotCenterEquivOfEqBot (SBc11.center_eq_bot_of_list hlist)).symm hlist)
  have hMS := S.isMSPair_of_F4 h1222 h517 h132two h132fsu h132A5 h331 h1327 h37 h39 hK₀G hK₀ hTK₀ hz
    hchar hRk
  have hset : ((K₀ ⊔ S.Tv : Subgroup G) : Set G) = (K₀ : Set G) * (S.Tv : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left K₀ S.Tv hTK₀
  have hZQ := hF4 G (K₀ ⊔ S.Tv) S.Tv K₀ hMS hK₀ hset hi4 S.v12 hvCQ

  set O := pCoreOf 2 K₀ with hOdef
  set Q := c134Q (K₀ ⊔ S.Tv) K₀ with hQdef
  set Z₀ := z0Of S.v12 K₀ with hZ₀def
  obtain ⟨hQO, -, hKQ, -⟩ := S.c134Q_facts_F4 h1222 h517 hK₀G hTK₀
  have hOK : O ≤ K₀ := CFSG.LieType.BorelTits.pCoreOf_le 2 K₀
  have hKO : K₀ ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀
  have hnorm : (K₀.subgroupOf (K₀ ⊔ S.Tv)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).2
      (sup_le Subgroup.le_normalizer hTK₀)
  have hOG : O ≤ pCoreOf 2 (K₀ ⊔ S.Tv) :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 K₀ (K₀ ⊔ S.Tv)
      le_sup_left hnorm
  have hvc : ∀ g ∈ K₀, g * S.v12 = S.v12 * g := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.mp (hK₀G hg)
  have hvz : ∀ g ∈ K₀, ∀ c ∈ Subgroup.zpowers S.v12, g * c = c * g := by
    intro g hg c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((Commute.zpow_right (hvc g hg) i)).eq

  have hZ₀prop : ∀ x ∈ Z₀, x ∈ O ∧ ∀ r ∈ O, x * r * x⁻¹ * r⁻¹ ∈ Subgroup.zpowers S.v12 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hx
    | one => exact ⟨O.one_mem, fun r _ => by simp⟩
    | mul x y _ _ hx hy =>
      refine ⟨O.mul_mem hx.1 hy.1, fun r hr => ?_⟩
      have h1 := hy.2 r hr
      have h2 := hx.2 r hr
      have e : x * y * r * (x * y)⁻¹ * r⁻¹ =
          x * (y * r * y⁻¹ * r⁻¹) * x⁻¹ * (x * r * x⁻¹ * r⁻¹) := by group
      rw [e, hvz x (hOK hx.1) _ h1, mul_inv_cancel_right]
      exact Subgroup.mul_mem _ h1 h2
    | inv x _ hx =>
      refine ⟨O.inv_mem hx.1, fun r hr => ?_⟩
      have h1 := hx.2 r hr
      have e : x⁻¹ * r * x⁻¹⁻¹ * r⁻¹ = x⁻¹ * (x * r * x⁻¹ * r⁻¹)⁻¹ * x := by group
      rw [e, hvz x⁻¹ (K₀.inv_mem (hOK hx.1)) _ (Subgroup.inv_mem _ h1), inv_mul_cancel_right]
      exact Subgroup.inv_mem _ h1
  have hZ₀conj : ∀ x ∈ Z₀, ∀ k ∈ K₀, k * x * k⁻¹ ∈ Z₀ := by
    intro x hx k hk
    obtain ⟨hxO, hxr⟩ := hZ₀prop x hx
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp (hKO hk) x).mp hxO, ?_⟩
    intro r hr
    have hr' : k⁻¹ * r * k ∈ O := by
      have := (Subgroup.mem_normalizer_iff.mp (hKO (K₀.inv_mem hk)) r).mp hr
      simpa using this
    have h1 := hxr _ hr'
    have e : k * x * k⁻¹ * r * (k * x * k⁻¹)⁻¹ * r⁻¹ =
        k * (x * (k⁻¹ * r * k) * x⁻¹ * (k⁻¹ * r * k)⁻¹) * k⁻¹ := by group
    rw [e, hvz k hk _ h1, mul_inv_cancel_right]
    exact h1

  have hcZQ : ∀ x ∈ Z₀, ∀ k ∈ K₀, k⁻¹ * x * k * x⁻¹ ∈ centerOf Q := by
    intro x hx k hk
    have hxQ : k⁻¹ * x * k * x⁻¹ ∈ Q := by
      have h1 : ⁅x, k⁻¹⁆ ∈ Q :=
        Subgroup.commutator_mem_commutator (hOG (hZ₀prop x hx).1) (K₀.inv_mem hk)
      have h2 : k⁻¹ * x * k * x⁻¹ = (⁅x, k⁻¹⁆)⁻¹ := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact Q.inv_mem h1
    have hxZ : k⁻¹ * x * k * x⁻¹ ∈ Z₀ := by
      have := hZ₀conj x hx k⁻¹ (K₀.inv_mem hk)
      rw [inv_inv] at this
      exact Z₀.mul_mem this (Z₀.inv_mem hx)
    exact hZQ _ hxQ fun q hq => (hZ₀prop _ hxZ).2 q (hQO hq)

  obtain ⟨⟨n, F₄, _, _, α₄, -, hα₄, -, -, -, hU, -, -, -⟩, -⟩ := hi4
  obtain ⟨-, -, β, -, hβk, hβe⟩ := hU
  have hZQK : centerOf Q ≤ K₀ := inf_le_left.trans (hQO.trans hOK)
  have hKZQ : K₀ ≤ Subgroup.normalizer ((centerOf Q : Subgroup G) : Set G) :=
    Setting.le_normalizer_centerOf hKQ
  have hUQ : ⁅centerOf Q, K₀⁆ ≤ Q := by
    rw [Subgroup.commutator_le]
    intro q hq k hk
    have hqQ : q ∈ Q := hq.1
    have h1 : k * q⁻¹ * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKQ hk) _).mp (Q.inv_mem hqQ)
    rw [commutatorElement_def, show q * k * q⁻¹ * k⁻¹ = q * (k * q⁻¹ * k⁻¹) by group]
    exact Q.mul_mem hqQ h1
  have hUO : ⁅centerOf Q, K₀⁆ ≤ centerOf O := by
    intro u hu
    refine ⟨hQO (hUQ hu), Subgroup.mem_centralizer_iff.mpr fun o ho => ?_⟩

    have hoK := hOK ho
    have hoker : (⟨o, hoK⟩ : ↥K₀) ∈ α₄.ker := by
      rw [hα₄.2]
      rw [hOdef, pCoreOf] at ho
      obtain ⟨o', ho', ho'eq⟩ := ho
      have e : (⟨o, hoK⟩ : ↥K₀) = o' := Subtype.ext ho'eq.symm
      rw [e, CFSG.pCore_eq_open]
      exact ho'
    have hu' : o * u * o⁻¹ ∈ ⁅centerOf Q, K₀⁆ :=
      (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_commutator hKZQ Subgroup.le_normalizer hoK) u).mp hu
    have h1 := hβe ⟨o, hoK⟩ ⟨u, hu⟩ ⟨o * u * o⁻¹, hu'⟩ rfl
    have h2 : β ⟨o * u * o⁻¹, hu'⟩ = β ⟨u, hu⟩ := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [h1 i, MonoidHom.mem_ker.mp hoker]
      simp [moduleAct]
    have h4 : (⟨o * u * o⁻¹, hu'⟩ : ↥⁅centerOf Q, K₀⁆) * ⟨u, hu⟩⁻¹ ∈ β.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h2, mul_inv_cancel]
    rw [hβk, Subgroup.mem_subgroupOf, Subgroup.mem_bot] at h4
    have h5 : o * u * o⁻¹ = u := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h4
      exact mul_inv_eq_one.mp h4
    calc o * u = o * u * o⁻¹ * o := by group
      _ = u * o := by rw [h5]
  have hZOK : centerOf O ≤ K₀ := inf_le_left.trans hOK
  have hKZO : K₀ ≤ Subgroup.normalizer ((centerOf O : Subgroup G) : Set G) :=
    Setting.le_normalizer_centerOf hKO

  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro x hx k hk
    have hxN : x ∈ Subgroup.normalizer (K₀ : Set G) :=
      Subgroup.le_normalizer (hOK (hZ₀prop x hx).1)
    have hU1 := comm_mem_commutator_of_perfect hZQK hKZQ hK₀p hxN (hcZQ x hx)
    have hU2 := comm_mem_commutator_of_perfect hZOK hKZO hK₀p hxN fun k hk => hUO (hU1 k hk)
    have h1 := hU2 k⁻¹ (K₀.inv_mem hk)
    rw [inv_inv] at h1
    have h2 : ⁅x, k⁆ = (k * x * k⁻¹ * x⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [h2]
    exact Subgroup.inv_mem _ h1
  · refine Subgroup.commutator_mono (fun c hc => Subgroup.subset_closure ⟨hc.1, fun r hr => ?_⟩)
      le_rfl
    rw [← Subgroup.mem_centralizer_iff.mp hc.2 r hr, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _

end CFSG.Quasithin.H13.A5
