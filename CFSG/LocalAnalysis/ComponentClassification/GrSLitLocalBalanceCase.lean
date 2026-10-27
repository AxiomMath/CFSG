module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitGWBridge
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitBalance

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.GSLit
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem solomon_normalizes (hSol : SolomonCommutingCoreInput) {G : Type} [Group G] [Finite G]
    {e x : G} (he : orderOf e = 2) (hx : orderOf x = 2) (hex : e * x = x * e) {L : Subgroup G}
    (hLC : L ≤ centralizer ({x} : Set G))
    (hL : IsPComponent 2 (L.subgroupOf (centralizer ({x} : Set G)))) :
    (pPrimeCore 2 (centralizer ({e} : Set G))).map (centralizer ({e} : Set G)).subtype ⊓
      centralizer ({x} : Set G) ≤ normalizer (L : Set G) := by
  have he1 : e ≠ 1 := fun h => by rw [h, orderOf_one] at he; exact absurd he (by norm_num)
  have hx1 : x ≠ 1 := fun h => by rw [h, orderOf_one] at hx; exact absurd hx (by norm_num)
  have he2 : e * e = 1 := by rw [← pow_two, ← he, pow_orderOf_eq_one]
  have hx2 : x * x = 1 := by rw [← pow_two, ← hx, pow_orderOf_eq_one]
  have hS := isElemTwo_zpowers he2
  have hT := isElemTwo_zpowers hx2
  have hST : ∀ y ∈ zpowers e, ∀ z ∈ zpowers x, y * z = z * y := by
    intro y hy z hz
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.mp hz
    exact ((Commute.zpow_zpow (show Commute e x from hex) i j)).eq
  have h := hSol G (zpowers e) (zpowers x)
    (fun hb => he1 (by rw [← mem_bot, ← hb]; exact mem_zpowers e))
    (fun hb => hx1 (by rw [← mem_bot, ← hb]; exact mem_zpowers x))
    hS.1 hS.2 hT.1 hT.2 hST
  obtain ⟨-, h2, -⟩ := h
  let Q : Subgroup G → Subgroup G → Prop := fun A K =>
    ∀ M : Subgroup G, M ≤ K → IsPComponent 2 (M.subgroupOf K) →
      (pPrimeCore 2 A).map A.subtype ⊓ K ≤ normalizer (M : Set G)
  have h2' : Q (centralizer (zpowers e : Set G)) (centralizer (zpowers x : Set G)) :=
    fun M hMC hM => (h2 M hMC hM).1
  rw [centralizer_zpowers_eq, centralizer_zpowers_eq] at h2'
  exact h2' L hLC hL

theorem ordA_one_ne_held_of_odd {m : ℕ} (hm : Odd m) : Open.ordA 1 m ≠ 4030387200 := by
  unfold Open.ordA
  rw [show 1 * (1 + 1) / 2 = 1 by rfl, pow_one, show Finset.Icc 2 (1 + 1) = {2} by rfl,
    Finset.prod_singleton]
  obtain ⟨k, rfl⟩ := hm
  have hg : Nat.gcd (1 + 1) (2 * k + 1 - 1) = 2 := by
    rw [show 2 * k + 1 - 1 = 2 * k by omega]
    simp
  rw [hg]
  intro h
  have hmod := Nat.div_add_mod ((2 * k + 1) * ((2 * k + 1) ^ 2 - 1)) 2
  have hlt := Nat.mod_lt ((2 * k + 1) * ((2 * k + 1) ^ 2 - 1)) (show 2 > 0 by norm_num)
  rw [h] at hmod
  rcases Nat.lt_or_ge (2 * k + 1) 2006 with hk | hk
  · have h1 : (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) ≤ 2005 * (2005 ^ 2 - 1) :=
      Nat.mul_le_mul (by omega) (Nat.sub_le_sub_right (Nat.pow_le_pow_left (by omega) 2) 1)
    norm_num at h1
    omega
  · have h1 : 2006 * (2006 ^ 2 - 1) ≤ (2 * k + 1) * ((2 * k + 1) ^ 2 - 1) :=
      Nat.mul_le_mul hk (Nat.sub_le_sub_right (Nat.pow_le_pow_left hk 2) 1)
    norm_num at h1
    omega

theorem fusionZStar_ne_top_of_card {K : Type*} [Group K]
    (h : Nat.card (K ⧸ Open.fusionZStar K) ≠ 1) : Open.fusionZStar K ≠ ⊤ := by
  intro htop
  apply h
  rw [htop]
  exact Nat.card_eq_one_iff_unique.mpr ⟨QuotientGroup.subsingleton_quotient_top, inferInstance⟩

theorem commutator_wGroup_le_of_alternating_seven (hCorC : GSThmB.CorollaryCStatement)
    (hSol : SolomonCommutingCoreInput)
    {X : Type} [Group X] [Finite X] [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a)
    (hK : Assembly.KProper Blueprint.Catalog X)
    (hz : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hU : ¬ OutcomeLocal.UOutcome X) {a : X} {J E : Subgroup X} (ha : orderOf a = 2)
    (hJa : J ≤ centralizer ({a} : Set X))
    (hJ : IsPComponent 2 (J.subgroupOf (centralizer ({a} : Set X))))
    (h7 : Nonempty (J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin 7)))
    (hE : E ≤ normalizer (J : Set X) ⊓ centralizer ({a} : Set X))
    (hE4 : Nonempty (E ≃* Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :
    ⁅J, wGroup E ⊓ centralizer ({a} : Set X)⁆ ≤
      (pPrimeCore 2 (centralizer ({a} : Set X))).map (centralizer ({a} : Set X)).subtype := by
  obtain ⟨φ⟩ := id hE4
  have h4 : Nat.card E = 4 := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_eq_fintype_card]
    rfl
  have h2 : ∀ e ∈ E, e * e = 1 := by
    intro e he
    have hm : ∀ y : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), y * y = 1 := by decide
    have : (⟨e, he⟩ : E) * ⟨e, he⟩ = 1 := φ.injective (by rw [map_mul, map_one, hm])
    exact congrArg Subtype.val this
  have hE' : E ≤ centralizer ({a} : Set X) ⊓ normalizer (J : Set X) :=
    fun g hg => mem_inf.mpr ⟨(mem_inf.mp (hE hg)).2, (mem_inf.mp (hE hg)).1⟩
  obtain ⟨e, heE, he1⟩ : ∃ e ∈ E, e ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : E = ⊥ := eq_bot_iff.mpr fun g hg => (mem_bot).mpr (h g hg)
    rw [hbot, card_bot] at h4
    omega
  have he : orderOf e = 2 := orderOf_eq_prime (by rw [pow_two]; exact h2 e heE) he1
  have hea : e * a = a * e := mem_centralizer_singleton_iff.mp (mem_inf.mp (hE heE)).2
  have hΔ : centralizer ({a} : Set X) ⊓ ⨅ (g : X) (_ : g ∈ E) (_ : g ≠ 1),
      (pPrimeCore 2 (centralizer ({g} : Set X))).map (centralizer ({g} : Set X)).subtype ≤
      normalizer (J : Set X) := by
    intro d hd
    obtain ⟨hdC, hdΔ⟩ := mem_inf.mp hd
    have hle : (⨅ (g : X) (_ : g ∈ E) (_ : g ≠ 1),
        (pPrimeCore 2 (centralizer ({g} : Set X))).map (centralizer ({g} : Set X)).subtype) ≤
        (pPrimeCore 2 (centralizer ({e} : Set X))).map (centralizer ({e} : Set X)).subtype :=
      (iInf_le _ e).trans ((iInf_le _ heE).trans (iInf_le _ he1))
    have hdO := hle hdΔ
    exact solomon_normalizes hSol he ha hea hJa hJ (mem_inf.mpr ⟨hdO, hdC⟩)
  have h := commutator_le_oddCore_of_alternating_seven hCorC hnonab hK hz hU ha hJa hJ h7 hE' hE4
    hΔ
  rw [wGroup_eq_iInf_of_four h4 h2, inf_comm]
  exact h.trans (GSLit.map_pPrimeCore_le_of_isPComponent hJa hJ)

end CFSG.ComponentClassification.GrSLit
