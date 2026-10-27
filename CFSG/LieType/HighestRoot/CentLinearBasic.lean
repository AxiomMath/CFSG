module

public import CFSG.LieType.HighestRoot.Defs
public import CFSG.LieType.HighestRoot.CentChevalleySLThree

public section

namespace CFSG.LieType.HighestRoot

open scoped MatrixGroups

theorem eq_one_or_neg_one_of_mul_self_SL23 : ∀ x : SL23, x * x = 1 → x = 1 ∨ x = -1 := by
  decide

variable {K : Type} [Field K] [Finite K]

theorem eq_of_orderOf_eq_two_of_mulEquiv (hK : Nat.card K = 3) {J : Type*} [Group J]
    (e : J ≃* SL(2, K)) {x y : J} (hx : orderOf x = 2) (hy : orderOf y = 2) : x = y := by
  set φ := e.trans (slEquivSL23 hK)
  have key : ∀ {w : J}, orderOf w = 2 → φ w = -1 := fun {w} hw => by
    have hw2 : w ^ 2 = 1 := by
      rw [← hw]
      exact pow_orderOf_eq_one w
    have h1 : φ w * φ w = 1 := by
      rw [← map_mul, ← pow_two, hw2, map_one]
    rcases eq_one_or_neg_one_of_mul_self_SL23 _ h1 with h | h
    · exfalso
      have : w = 1 := φ.injective (by rw [h, map_one])
      rw [this, orderOf_one] at hw
      exact absurd hw (by decide)
    · exact h
  exact φ.injective ((key hx).trans (key hy).symm)

variable {G : Type*} [Group G]

theorem eq_of_normal_of_orderOf_three (hK : Nat.card K = 3) {z : G} (hz : orderOf z = 2)
    {R Cc L : Subgroup G} (hR : Nonempty (R ≃* SL(2, K)))
    (hCc : Cc ≤ Subgroup.centralizer ({z} : Set G))
    (hCcn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Cc : Set G))
    (hzCc : z ∉ Cc)
    (h3 : ∀ x ∈ Subgroup.centralizer ({z} : Set G), orderOf x = 3 →
      (∀ y ∈ Cc, Commute x y) → x ∈ R)
    (hL : L ≤ Subgroup.centralizer ({z} : Set G))
    (hLn : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hLe : Nonempty (L ≃* SL(2, K))) (hzL : z ∈ L) : L = R := by
  obtain ⟨e⟩ := hLe
  obtain ⟨eR⟩ := hR
  have hzL' : orderOf (⟨z, hzL⟩ : L) = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact hz
  have hdisj : ∀ y ∈ L, y ∈ Cc → y = 1 := by
    intro y hyL hyC
    have hNn : (Cc.subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hCcn (hL g.2)) n).1 hn⟩
    by_cases hNZ : Cc.subgroupOf L ≤ Subgroup.center L
    · have hc := (mem_center_iff_of_mulEquiv hK e _).1
        (hNZ (show (⟨y, hyL⟩ : L) ∈ Cc.subgroupOf L from hyC))
      rcases hc with h1 | h1
      · have : (⟨y, hyL⟩ : L) = 1 :=
          (e.trans (slEquivSL23 hK)).injective (by rw [h1, map_one])
        exact congrArg Subtype.val this
      · exfalso
        have hy2 : orderOf (⟨y, hyL⟩ : L) = 2 := by
          rw [← orderOf_injective (e.trans (slEquivSL23 hK)).toMonoidHom
            (e.trans (slEquivSL23 hK)).injective]
          simp only [MulEquiv.coe_toMonoidHom]
          rw [h1, orderOf_neg_one_SL23]
        have hyz : y = z := congrArg Subtype.val (eq_of_orderOf_eq_two_of_mulEquiv hK e hy2 hzL')
        exact hzCc (hyz ▸ hyC)
    · exfalso
      have h8 := eight_le_card_of_normal hK e _ hNZ
      have h24 := card_eq_24 hK e
      have : Finite L := Nat.finite_of_card_ne_zero (by omega)
      have hdvd : Nat.card (Cc.subgroupOf L) ∣ 24 := h24 ▸ Subgroup.card_subgroup_dvd_card _
      have h2 : 2 ∣ Nat.card (Cc.subgroupOf L) := by
        obtain ⟨k, hk⟩ := hdvd
        rcases (by omega : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ 4 ≤ k) with rfl | rfl | rfl | rfl | hk4
        · omega
        · exact ⟨12, by omega⟩
        · exact ⟨6, by omega⟩
        · exact ⟨4, by omega⟩
        · nlinarith
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 h2
      have hw' : orderOf (w : L) = 2 := by
        rw [Subgroup.orderOf_coe]
        exact hw
      have hwz : ((w : L) : G) = z :=
        congrArg Subtype.val (eq_of_orderOf_eq_two_of_mulEquiv hK e hw' hzL')
      have hwC : ((w : L) : G) ∈ Cc := Subgroup.mem_subgroupOf.1 w.2
      rw [hwz] at hwC
      exact hzCc hwC
  have hcomm : ∀ x ∈ L, ∀ y ∈ Cc, Commute x y := by
    intro x hx y hy
    have h1 : x * y * x⁻¹ * y⁻¹ ∈ L := by
      have : y * x⁻¹ * y⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (hLn (hCc hy)) _).1 (inv_mem hx)
      rw [mul_assoc, mul_assoc]
      exact mul_mem hx (by rwa [← mul_assoc])
    have h2 : x * y * x⁻¹ * y⁻¹ ∈ Cc :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (hCcn (hL hx)) y).1 hy) (inv_mem hy)
    have h3' := hdisj _ h1 h2
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3'
    exact h3'
  have hLR : L ≤ R := by
    intro x hx
    have hx' : (⟨x, hx⟩ : L) ∈ Subgroup.closure {y : L | orderOf y = 3} := by
      rw [closure_orderOf_three_eq_top_of_mulEquiv hK e]
      exact Subgroup.mem_top _
    have hle : Subgroup.closure {y : L | orderOf y = 3} ≤ R.comap L.subtype := by
      rw [Subgroup.closure_le]
      intro y hy
      have hy3 : orderOf (y : G) = 3 := by
        rw [Subgroup.orderOf_coe]
        exact hy
      exact h3 y (hL y.2) hy3 fun c hc => hcomm y y.2 c hc
    exact hle hx'
  have hRfin : Finite R := Nat.finite_of_card_ne_zero (by rw [card_eq_24 hK eR]; norm_num)
  exact Subgroup.eq_of_le_of_card_ge hLR (by rw [card_eq_24 hK eR, card_eq_24 hK e])

theorem centralizerCondition_map {G' : Type*} [Group G'] (φ : G ≃* G') {F : Type*} [Field F]
    {R : Subgroup G} (h : CentralizerCondition F R) :
    CentralizerCondition F (R.map φ.toMonoidHom) := by
  have hc : ∀ z : G, (Subgroup.centralizer ({z} : Set G)).map φ.toMonoidHom =
      Subgroup.centralizer ({φ z} : Set G') := fun z => by
    ext y
    obtain ⟨y, rfl⟩ := φ.surjective y
    simp only [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      rw [← map_mul, ← map_mul, h]
    · intro h
      exact φ.injective (by rw [map_mul, map_mul, h])
  have hn : ∀ S : Subgroup G, (Subgroup.normalizer (S : Set G)).map φ.toMonoidHom =
      Subgroup.normalizer ((S.map φ.toMonoidHom : Subgroup G') : Set G') := fun S =>
    (Subgroup.map_equiv_normalizer_eq S φ)
  intro z' hz' hz2'
  obtain ⟨z, hz, rfl⟩ := hz'
  have hz2 : orderOf z = 2 := by
    rw [← orderOf_injective φ.toMonoidHom φ.injective z]
    exact hz2'
  obtain ⟨h1, h2⟩ := h z hz hz2
  refine ⟨?_, fun hF L hLc hLn hLe hzL => ?_⟩
  · rw [MulEquiv.coe_toMonoidHom, ← hc z, ← hn R]
    exact Subgroup.map_mono h1
  · set L₀ := L.map φ.symm.toMonoidHom with hL₀
    have hLL₀ : L = L₀.map φ.toMonoidHom := by
      rw [hL₀, Subgroup.map_map]
      convert (Subgroup.map_id L).symm
      ext x
      simp
    rw [hLL₀] at hLc hLn hLe hzL ⊢
    rw [MulEquiv.coe_toMonoidHom, ← hc z] at hLc hLn
    rw [← hn L₀] at hLn
    have hLc' : L₀ ≤ Subgroup.centralizer ({z} : Set G) :=
      (Subgroup.map_le_map_iff_of_injective φ.injective).1 hLc
    have hLn' : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (L₀ : Set G) :=
      (Subgroup.map_le_map_iff_of_injective φ.injective).1 hLn
    have hLe' : Nonempty (L₀ ≃* SL(2, F)) := by
      obtain ⟨e⟩ := hLe
      exact ⟨(L₀.equivMapOfInjective φ.toMonoidHom φ.injective).trans e⟩
    have hzL' : z ∈ L₀ := by
      obtain ⟨w, hw, hwz⟩ := hzL
      rw [show w = z from φ.injective hwz] at hw
      exact hw
    rw [h2 hF L₀ hLc' hLn' hLe' hzL']

theorem centralizerCondition_of_ringEquiv {F F' : Type*} [Field F] [Field F'] (e : F ≃+* F')
    {R : Subgroup G} (h : CentralizerCondition F R) : CentralizerCondition F' R := by
  intro z hz hz2
  obtain ⟨h1, h2⟩ := h z hz hz2
  refine ⟨h1, fun hF L hLc hLn hLe hzL => h2 ?_ L hLc hLn ?_ hzL⟩
  · rw [Nat.card_congr e.toEquiv, hF]
  · obtain ⟨φ⟩ := hLe
    exact ⟨φ.trans (slMapEquiv e.symm)⟩

end CFSG.LieType.HighestRoot
