module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6ThreeCore
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Helpers
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Lemma35
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.QuasithinUnique.DoubleA3

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts Subgroup Equiv

section A6

theorem factorization_three_360 : (360 : ℕ).factorization 3 = 2 := by
  have h : (360 : ℕ) = 3 ^ 2 * 40 := by norm_num
  rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 40)]

theorem exists_isElemAbelian_nine {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6)) :
    ∃ A : Subgroup K, IsElemAbelian 3 A ∧ Nat.card A = 9 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKcard : Nat.card K = 360 := (Nat.card_congr e₀.toEquiv).trans card_alt6'
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hKcard]; norm_num)
  obtain ⟨P⟩ : Nonempty (Sylow 3 K) := inferInstance
  have hP : Nat.card (P : Subgroup K) = 3 ^ 2 := by
    have h := P.card_eq_multiplicity
    rw [hKcard, factorization_three_360] at h
    exact h
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let φ : K ≃* ↥A6Models.psl29 := e₀.trans ψ.symm
  refine ⟨(P : Subgroup K), ⟨IsPGroup.isMulCommutative_of_card_eq_prime_sq hP, ?_⟩,
    by rw [hP]; norm_num⟩
  intro x hx
  have h9 : x ^ 9 = 1 := by
    have h1 : orderOf (⟨x, hx⟩ : (P : Subgroup K)) ∣ Nat.card (P : Subgroup K) :=
      orderOf_dvd_natCard _
    rw [hP] at h1
    have h2 := orderOf_dvd_iff_pow_eq_one.mp
      (by simpa using h1 : orderOf (⟨x, hx⟩ : (P : Subgroup K)) ∣ 9)
    simpa using congrArg Subtype.val h2
  have h9' : ((φ x : ↥A6Models.psl29) : P10) ^ 9 = 1 := by
    have h : (φ x) ^ 9 = 1 := by rw [← map_pow, h9, map_one]
    simpa using congrArg (fun y : ↥A6Models.psl29 => (y : P10)) h
  have hmem : code ((φ x : ↥A6Models.psl29) : P10) ∈ Core.pslLit := (mem_psl29_iff _).mp (φ x).2
  have hchk := pow_nine_check
  rw [List.all_eq_true] at hchk
  have h1 := hchk _ hmem
  have hc9 : (Core.cpow (code ((φ x : ↥A6Models.psl29) : P10)) 9 != Core.cid) = false := by
    rw [← code_pow, h9', code_one]; simp
  rw [hc9, Bool.false_or, beq_iff_eq] at h1
  have h3 : ((φ x : ↥A6Models.psl29) : P10) ^ 3 = 1 := by
    apply code_injective
    rw [code_pow, h1, code_one]
  have h3' : (φ x) ^ 3 = 1 := Subtype.ext (by simpa using h3)
  have h4 : φ (x ^ 3) = 1 := by rw [map_pow]; exact h3'
  exact φ.injective (by rw [h4, map_one])

theorem exists_inner_of_pow_three {K : Type*} [Group K] (e₀ : K ≃* alternatingGroup (Fin 6))
    (γ : MulAut K) (hγ : ∀ k, γ (γ (γ k)) = k) : ∃ k₀ : K, ∀ a : K, γ a = k₀ * a * k₀⁻¹ := by
  obtain ⟨ψ, -⟩ := exists_psl_equiv
  let φ : K ≃* ↥A6Models.psl29 := e₀.trans ψ.symm
  obtain ⟨b, hbA, hb⟩ := exists_aut_model φ γ
  have hb3 : b ^ 3 = 1 := by
    have hc : b ^ 3 ∈ A6Models.autA6 := A6Models.autA6.pow_mem hbA 3
    refine centralizer_psl29 hc fun x hx => ?_
    rw [pow_three']
    set k := φ.symm ⟨x, hx⟩ with hkdef
    have hk : ((φ k : ↥A6Models.psl29) : P10) = x := by simp [hkdef]
    have h1 := hb k
    have h2 := hb (γ k)
    have h3 := hb (γ (γ k))
    rw [hγ k] at h3
    rw [h2, h1, hk] at h3
    calc b * b * b * x = (b * (b * (b * x * b⁻¹) * b⁻¹) * b⁻¹) * (b * b * b) := by group
      _ = x * (b * b * b) := by rw [← h3]
  have hbpsl : b ∈ A6Models.psl29 := by
    have hchk := aut_three_check
    rw [List.all_eq_true] at hchk
    have h1 := hchk _ (code_mem_autL hbA)
    have hc3 : (Core.cpow (code b) 3 != Core.cid) = false := by
      rw [← code_pow, hb3, code_one]; simp
    rw [hc3, Bool.false_or, List.contains_iff_mem] at h1
    exact (mem_psl29_iff _).mpr h1
  refine ⟨φ.symm ⟨b, hbpsl⟩, fun a => ?_⟩
  apply φ.injective
  apply Subtype.ext
  rw [hb a]
  simp

end A6

section Rank

variable {G : Type} [Group G] [Finite G]

theorem card_isElemAbelian_three_le (he : CFSG.Assembly.evenRank G ≤ 2) {H : Subgroup G}
    (hH : IsTwoLocal H) {E : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian 3 E) :
    Nat.card E ≤ 9 := by
  have hp3 : IsPGroup 3 ↥E := by
    rw [IsPGroup.iff_orderOf]
    intro g
    have h1 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one (by
      apply Subtype.ext
      simpa using hE.2 (g : G) g.2)
    rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by simpa using h⟩
  obtain ⟨k, hk⟩ := hp3.exists_card_eq
  have hk' : k ≤ CFSG.Open.pRank 3 H := CFSG.SectionRank.le_pRank (by norm_num) hEH hE hk
  have h2 : CFSG.Open.pRank 3 H ≤ CFSG.Assembly.evenRank G :=
    CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three (by norm_num) H hH
  have hk2 : k ≤ 2 := by omega
  rw [hk]
  calc 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
    _ = 9 := by norm_num

omit [Finite G] in
theorem isTwoLocal_centralizerElem {z : G} (hz : z ≠ 1) (hz2 : z ^ 2 = 1) :
    IsTwoLocal (centralizerElem z) :=
  Lin2.isTwoLocal_centralizer_of_sq_eq_one hz2 hz

omit [Finite G] in
theorem isElemAbelian_three_sup_of_commute {X Y : Subgroup G} (hX : IsElemAbelian 3 X)
    (hY : IsElemAbelian 3 Y) (hXY : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    IsElemAbelian 3 (X ⊔ Y) := CFSG.Open.IsElemAbelian.sup_of_commute hX hY hXY

end Rank

section ThreeElements

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem eq_one_of_mem_centralizer {A : Subgroup G} (e : ↥A ≃* alternatingGroup (Fin 6)) {x : G}
    (hxA : x ∈ A) (hxc : ∀ a ∈ A, a * x = x * a) : x = 1 := by
  have hcenter : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have hmem : e ⟨x, hxA⟩ ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h := hxc (e.symm y : G) (e.symm y).2
    have h' : (e.symm y) * ⟨x, hxA⟩ = ⟨x, hxA⟩ * (e.symm y) := Subtype.ext h
    have h'' := congrArg e h'
    simpa using h''
  rw [hcenter, Subgroup.mem_bot] at hmem
  have h1 : (⟨x, hxA⟩ : ↥A) = 1 := e.injective (hmem.trans (map_one e).symm)
  exact congrArg Subtype.val h1

omit [Finite G] in
theorem isElemAbelian_map_subtype {p : ℕ} {A : Subgroup G} {E : Subgroup ↥A}
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map A.subtype) := CFSG.Open.IsElemAbelian.map hE _

omit [Finite G] in
theorem exists_isElemAbelian_nine_le {A : Subgroup G} (e : ↥A ≃* alternatingGroup (Fin 6)) :
    ∃ E : Subgroup G, E ≤ A ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, hcard⟩ := exists_isElemAbelian_nine e
  refine ⟨E.map A.subtype, Subgroup.map_subtype_le E, isElemAbelian_map_subtype hE, ?_⟩
  rw [Subgroup.card_map_of_injective A.subtype_injective]
  exact hcard

theorem false_of_centralizing_order_three {A N : Subgroup G} (e : ↥A ≃* alternatingGroup (Fin 6))
    (hAN : A ≤ N) (hrank : ∀ E : Subgroup G, E ≤ N → IsElemAbelian 3 E → Nat.card E ≤ 9)
    {b : G} (hbN : b ∈ N) (hb3 : b ^ 3 = 1) (hb1 : b ≠ 1) (hbC : ∀ a ∈ A, a * b = b * a) :
    False := by
  obtain ⟨E₉, hE₉A, hE₉, hE₉c⟩ := exists_isElemAbelian_nine_le e
  have hbord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hZ : IsElemAbelian 3 (Subgroup.zpowers b) := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨i, hi⟩ := (Subgroup.mem_zpowers_iff.mp x.2)
      obtain ⟨j, hj⟩ := (Subgroup.mem_zpowers_iff.mp y.2)
      apply Subtype.ext
      show (x : G) * y = y * x
      rw [← hi, ← hj]
      exact ((Commute.refl b).zpow_zpow i j).eq
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hb3, one_zpow]
  have hEb : ∀ x ∈ E₉, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hxb : Commute x b := hbC x (hE₉A hx)
    exact (hxb.zpow_right i).eq
  have hEsup : IsElemAbelian 3 (E₉ ⊔ Subgroup.zpowers b) :=
    isElemAbelian_three_sup_of_commute hE₉ hZ hEb
  have hinf : E₉ ⊓ Subgroup.zpowers b = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyb⟩
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyb
    have hyA : b ^ i ∈ A := hE₉A hyE
    have h1 := eq_one_of_mem_centralizer e hyA (fun a ha => by
      have hab : Commute a b := hbC a ha
      exact (hab.zpow_right i).eq)
    rw [h1]; exact one_mem _
  have hnorm : E₉ ≤ normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) :=
    C5.le_normalizer_of_commute hEb
  have hcard := C5.card_sup_mul_card_inf_of_le_normalizer hnorm
  rw [hinf, Subgroup.card_bot, mul_one, hE₉c, Nat.card_zpowers, hbord] at hcard
  have hle := hrank (E₉ ⊔ Subgroup.zpowers b)
    (sup_le (hE₉A.trans hAN) (Subgroup.zpowers_le.mpr hbN)) hEsup
  omega

theorem mem_of_orderThree_normalizing {A N : Subgroup G} (e : ↥A ≃* alternatingGroup (Fin 6))
    (hAN : A ≤ N) (hNn : N ≤ normalizer (A : Set G))
    (hrank : ∀ E : Subgroup G, E ≤ N → IsElemAbelian 3 E → Nat.card E ≤ 9)
    {c : G} (hc : c ∈ N) (hc3 : c ^ 3 = 1) : c ∈ A := by
  obtain ⟨γ, hγ⟩ := exists_conjAut (hNn hc)
  have hccc : c * c * c = 1 := by rw [← pow_three']; exact hc3
  have hγ3 : ∀ a, γ (γ (γ a)) = a := by
    intro a
    apply Subtype.ext
    rw [hγ, hγ, hγ]
    calc c⁻¹ * (c⁻¹ * (c⁻¹ * (a : G) * c) * c) * c = (c * c * c)⁻¹ * (a : G) * (c * c * c) := by
          group
      _ = a := by rw [hccc]; group
  obtain ⟨k₀, hk₀⟩ := exists_inner_of_pow_three e γ hγ3
  set k : G := (k₀ : G) with hk
  have hkA : k ∈ A := k₀.2
  set b : G := c * k with hb
  have hbC : ∀ a ∈ A, a * b = b * a := by
    intro a ha
    have h1 := congrArg Subtype.val (hk₀ ⟨a, ha⟩)
    rw [hγ] at h1
    have h2 : c⁻¹ * a * c = k * a * k⁻¹ := h1
    have h3 : a * c = c * (k * a * k⁻¹) := by rw [← h2]; group
    calc a * b = (a * c) * k := by rw [hb]; group
      _ = (c * (k * a * k⁻¹)) * k := by rw [h3]
      _ = b * a := by rw [hb]; group
  have hcb : c = b * k⁻¹ := by rw [hb]; group
  have hcomm : ∀ a ∈ A, Commute a b := fun a ha => hbC a ha
  have hb3k : b ^ 3 = k ^ 3 := by
    have h1 : Commute b k⁻¹ := (hcomm k⁻¹ (A.inv_mem hkA)).symm
    have h2 : c ^ 3 = b ^ 3 * (k⁻¹) ^ 3 := by rw [hcb]; exact h1.mul_pow 3
    rw [hc3, inv_pow] at h2
    exact mul_inv_eq_one.mp h2.symm
  have hk3 : k ^ 3 = 1 :=
    eq_one_of_mem_centralizer e (A.pow_mem hkA 3) (fun a ha => by
      rw [← hb3k]; exact ((hcomm a ha).pow_right 3).eq)
  have hb3 : b ^ 3 = 1 := by rw [hb3k, hk3]
  by_cases hb1 : b = 1
  · rw [hcb, hb1, one_mul]; exact A.inv_mem hkA
  · exfalso
    have hbN : b ∈ N := N.mul_mem hc (hAN hkA)
    exact false_of_centralizing_order_three e hAN hrank hbN hb3 hb1 hbC

end ThreeElements

end CFSG.QuasithinUnique.DoubleA3
