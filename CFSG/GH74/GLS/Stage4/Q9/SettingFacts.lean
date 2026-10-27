module

public import CFSG.GH74.GLS.Stage4.Q9.Setting
public import CFSG.GH74.GLS.Stage4.Q9.Lemma82
public import CFSG.GH74.GLS.Stage4.Q9.OddPackage
public import CFSG.GH74.GLS.C3.Layer3.Basic
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureRootQuotientClassesBasic

public section

namespace CFSG.GH74.GLS.Stage4.Q9

open Subgroup
open scoped MatrixGroups

section SL2

variable {F : Type*} [Field F]

theorem exists_scalar_of_commute_sl2 {M : Matrix (Fin 2) (Fin 2) F}
    (hM : ∀ g : SL(2, F),
      (g : Matrix (Fin 2) (Fin 2) F) * M = M * (g : Matrix (Fin 2) (Fin 2) F)) :
    ∃ s : F, Matrix.scalar (Fin 2) s = M :=
  Matrix.mem_range_scalar_of_commute_transvectionStruct fun t => hM t.toSpecialLinearGroup

theorem det_scalar_fin_two (s : F) : (Matrix.scalar (Fin 2) s).det = s * s := by
  simp [Matrix.scalar_apply, sq]

theorem eq_one_or_eq_of_commute_of_mulEquiv_sl2 {G : Type*} [Group G] (hF : (2 : F) ≠ 0)
    {K : Subgroup G} (φ : K ≃* SL(2, F)) {z : G} (hzK : z ∈ K) (hz : orderOf z = 2)
    {k : G} (hk : k ∈ K) (hc : ∀ w ∈ K, k * w = w * k) : k = 1 ∨ k = z := by
  have hcomm : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) *
      (φ ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) =
      (φ ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F) * (g : Matrix (Fin 2) (Fin 2) F) := by
    intro g
    have h1 : φ.symm g * (⟨k, hk⟩ : K) = (⟨k, hk⟩ : K) * φ.symm g :=
      Subtype.ext (hc _ (φ.symm g).2).symm
    have h2 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) (congrArg φ h1)
    simpa using h2
  obtain ⟨s, hs⟩ := exists_scalar_of_commute_sl2 hcomm
  have hdet : (φ ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) F).det = 1 := (φ ⟨k, hk⟩).2
  rw [← hs, det_scalar_fin_two] at hdet
  have hsq : φ ⟨k, hk⟩ * φ ⟨k, hk⟩ = 1 := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    rw [← hs, ← map_mul, hdet, map_one]
  have hkk : k * k = 1 := by
    have h1 : φ (⟨k, hk⟩ * ⟨k, hk⟩) = φ 1 := by rw [map_mul, hsq, map_one]
    simpa using congrArg Subtype.val (φ.injective h1)
  exact Lemma82.eq_one_or_eq_of_sq_eq_one_of_mulEquiv_sl2 hF φ hzK hz k hk hkk

private theorem mul_comm_aux {M : Type*} [Monoid M] {P B B' g : M} (hB : B' * B = 1)
    (h : P * (B * g * B') = g * P) : g * (P * B) = P * B * g := by
  calc g * (P * B) = (g * P) * B := by rw [mul_assoc]
    _ = (P * (B * g * B')) * B := by rw [h]
    _ = P * B * g := by simp only [mul_assoc, hB, mul_one]

theorem false_of_twisted_commute {G : Type*} [Group G] {K : Subgroup G} (φ : K ≃* SL(2, F)) (t : G)
    (B : GL (Fin 2) F)
    (hB : ∀ k k' : K, (k' : G) = t * k * t⁻¹ →
      ((φ k' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (B : Matrix (Fin 2) (Fin 2) F) * (φ k : Matrix (Fin 2) (Fin 2) F) *
          ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (hdet : ¬ IsSquare (Matrix.det (B : Matrix (Fin 2) (Fin 2) F)))
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    {m : G} (hm : m ∈ K) (h : ∀ w ∈ K, m * (t * w * t⁻¹) = w * m) : False := by
  have hBinv : ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *
      (B : Matrix (Fin 2) (Fin 2) F) = 1 := Units.inv_mul B
  have hM' : ∀ w : K, ((φ w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) *
      ((φ ⟨m, hm⟩ : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) =
      ((φ ⟨m, hm⟩ : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) *
        ((φ w : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) := by
    intro w
    have hw' : t * (w : G) * t⁻¹ ∈ K := hnorm _ w.2
    have h1 : (⟨m, hm⟩ : K) * ⟨t * (w : G) * t⁻¹, hw'⟩ = w * ⟨m, hm⟩ := Subtype.ext (h w w.2)
    have h2 := congrArg (fun x : SL(2, F) => (x : Matrix (Fin 2) (Fin 2) F)) (congrArg φ h1)
    have h3 := hB w ⟨t * (w : G) * t⁻¹, hw'⟩ rfl
    simp only [map_mul, Matrix.SpecialLinearGroup.coe_mul] at h2
    rw [h3] at h2
    exact mul_comm_aux hBinv h2
  have hM : ∀ g : SL(2, F), (g : Matrix (Fin 2) (Fin 2) F) *
      ((φ ⟨m, hm⟩ : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) =
      ((φ ⟨m, hm⟩ : Matrix (Fin 2) (Fin 2) F) * (B : Matrix (Fin 2) (Fin 2) F)) *
        (g : Matrix (Fin 2) (Fin 2) F) := fun g => by
    simpa using hM' (φ.symm g)
  obtain ⟨s, hs⟩ := exists_scalar_of_commute_sl2 hM
  have hdetP : (φ ⟨m, hm⟩ : Matrix (Fin 2) (Fin 2) F).det = 1 := (φ ⟨m, hm⟩).2
  have hd : (Matrix.det (B : Matrix (Fin 2) (Fin 2) F)) = s * s := by
    have := congrArg Matrix.det hs
    rw [det_scalar_fin_two, Matrix.det_mul, hdetP, one_mul] at this
    exact this.symm
  exact hdet ⟨s, hd⟩

theorem mem_of_centralizes_sl2_of_nonsquare {G : Type*} [Group G] (hF : (2 : F) ≠ 0) {z t : G}
    {K K' : Subgroup G} (φ : K ≃* SL(2, F)) (B : GL (Fin 2) F) (hz : orderOf z = 2) (hzK : z ∈ K)
    (hzK' : z ∈ K') (hcomm : ∀ x ∈ K', ∀ y ∈ K, x * y = y * x)
    (hnorm : ∀ k ∈ K, t * k * t⁻¹ ∈ K)
    (hB : ∀ k k' : K, (k' : G) = t * k * t⁻¹ →
      ((φ k' : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) =
        (B : Matrix (Fin 2) (Fin 2) F) * (φ k : Matrix (Fin 2) (Fin 2) F) *
          ((B⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F))
    (hdet : ¬ IsSquare (Matrix.det (B : Matrix (Fin 2) (Fin 2) F))) {c : G}
    (hc : (∃ k' ∈ K', ∃ k ∈ K, c = k' * k) ∨ (∃ k' ∈ K', ∃ k ∈ K, c = k' * k * t))
    (hcK : ∀ w ∈ K, c * w = w * c) : c ∈ K' := by
  rcases hc with ⟨k', hk', k, hk, rfl⟩ | ⟨k', hk', k, hk, rfl⟩
  · have hkc : ∀ w ∈ K, k * w = w * k := by
      intro w hw
      have h1 := hcK w hw
      refine mul_left_cancel (a := k') ?_
      calc k' * (k * w) = k' * k * w := (mul_assoc _ _ _).symm
        _ = w * (k' * k) := h1
        _ = (w * k') * k := (mul_assoc _ _ _).symm
        _ = (k' * w) * k := by rw [hcomm k' hk' w hw]
        _ = k' * (w * k) := mul_assoc _ _ _
    rcases eq_one_or_eq_of_commute_of_mulEquiv_sl2 hF φ hzK hz hk hkc with rfl | rfl
    · simpa using hk'
    · exact K'.mul_mem hk' hzK'
  · exfalso
    refine false_of_twisted_commute φ t B hB hdet hnorm hk ?_
    intro w hw
    have h1 := hcK w hw
    refine mul_left_cancel (a := k') (mul_right_cancel (b := t) ?_)
    calc k' * (k * (t * w * t⁻¹)) * t = k' * k * (t * w) := by group
      _ = k' * k * t * w := by group
      _ = w * (k' * k * t) := h1
      _ = (w * k') * k * t := by group
      _ = (k' * w) * k * t := by rw [hcomm k' hk' w hw]
      _ = k' * (w * k) * t := by group

end SL2

namespace Q9Setting

theorem card_centralizer_eq_of_isConj {X : Type*} [Group X] {a b : X} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set X)) = Nat.card (centralizer ({b} : Set X)) :=
  CFSG.GH74.GLS.Layer3.card_centralizer_eq_of_isConj h

section Facts

variable {G : Type} [Group G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁] [Field F₂]
variable (S : Q9Setting G z K₁ K₂ F₁ F₂)
include S

theorem z_mem₁ : z ∈ K₁ := by
  have : z ∈ K₁ ⊓ K₂ := by rw [S.inter_eq]; exact Subgroup.mem_zpowers z
  exact this.1

theorem z_mem₂ : z ∈ K₂ := by
  have : z ∈ K₁ ⊓ K₂ := by rw [S.inter_eq]; exact Subgroup.mem_zpowers z
  exact this.2

theorem card_K₁ : Nat.card K₁ = 720 := by
  have : Finite F₁ := Nat.finite_of_card_ne_zero (by rw [S.card₁]; norm_num)
  rw [Nat.card_congr S.φ₁.toEquiv]
  exact card_specialLinearGroup_two_nine S.card₁

theorem card_K₂ : Nat.card K₂ = 720 := by
  have : Finite F₂ := Nat.finite_of_card_ne_zero (by rw [S.card₂]; norm_num)
  rw [Nat.card_congr S.φ₂.toEquiv]
  exact card_specialLinearGroup_two_nine S.card₂

theorem card_sup : Nat.card ↥(K₁ ⊔ K₂) = 259200 := by
  have hle' : K₁ ≤ centralizer (K₂ : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.mpr fun y hy => (S.comm x hx y hy).symm
  have hle : K₁ ≤ normalizer (K₂ : Set G) := hle'.trans (Subgroup.centralizer_le_normalizer (K₂ : Set G))
  have h := CFSG.ShultStronglyClosedTI.LinearChain.RootQuotientClasses.card_sup_mul_card_inf hle
  rw [S.inter_eq, Nat.card_zpowers, S.z_ord, S.card_K₁, S.card_K₂] at h
  omega

theorem card_C : Nat.card ↥(centralizer ({z} : Set G)) = 518400 := by
  have h := Subgroup.relIndex_mul_card (K₁ ⊔ K₂) (centralizer ({z} : Set G))
  rw [S.index_two, inf_eq_left.mpr (sup_le S.le_centralizer₁ S.le_centralizer₂), S.card_sup] at h
  omega

theorem card_C_three : (Nat.card ↥(centralizer ({z} : Set G))).factorization 3 = 4 := by
  rw [S.card_C]; norm_num [Nat.factorization]

theorem card_C_five : (Nat.card ↥(centralizer ({z} : Set G))).factorization 5 = 2 := by
  rw [S.card_C]; norm_num [Nat.factorization]

theorem card_C_prime_dvd : ∀ r : ℕ, r.Prime → r ∣ Nat.card ↥(centralizer ({z} : Set G)) →
    r = 2 ∨ r = 3 ∨ r = 5 := by
  intro r hr hdvd
  rw [S.card_C, show (518400 : ℕ) = 2 ^ 8 * 3 ^ 4 * 5 ^ 2 by norm_num] at hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h2))
    · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
        (hr.dvd_of_dvd_pow h2)))
  · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_five).mp
      (hr.dvd_of_dvd_pow h1)))

theorem card_G_three : (Nat.card G).factorization 3 = 4 := S.card3.trans S.card_C_three

theorem mem_C_cases : ∀ c ∈ centralizer ({z} : Set G),
    c ∈ K₁ ⊔ K₂ ∨ ∃ k ∈ K₁ ⊔ K₂, c = k * S.t := by
  intro c hc
  by_cases hcK : c ∈ K₁ ⊔ K₂
  · exact Or.inl hcK
  · right
    refine ⟨c * S.t⁻¹, ?_, by simp⟩
    have hidx : ((K₁ ⊔ K₂).subgroupOf (centralizer ({z} : Set G))).index = 2 := S.index_two
    have key := (Subgroup.mul_mem_iff_of_index_two hidx
      (a := (⟨c, hc⟩ : centralizer ({z} : Set G)))
      (b := (⟨S.t⁻¹, Subgroup.inv_mem _ S.t_mem⟩ : centralizer ({z} : Set G)))).mpr ?_
    · exact key
    · refine iff_of_false ?_ ?_
      · exact hcK
      · intro h
        have h' : S.t⁻¹ ∈ K₁ ⊔ K₂ := h
        exact S.t_notin (by simpa using inv_mem h')

theorem mem_C_cases_prod : ∀ c ∈ centralizer ({z} : Set G),
    (∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, c = k₁ * k₂) ∨ (∃ k₁ ∈ K₁, ∃ k₂ ∈ K₂, c = k₁ * k₂ * S.t) := by
  intro c hc
  rcases S.mem_C_cases c hc with h | ⟨k, hk, rfl⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Lemma82.mem_sup_of_commute S.comm h
    exact Or.inl ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  · obtain ⟨k₁, hk₁, k₂, hk₂, rfl⟩ := Lemma82.mem_sup_of_commute S.comm hk
    exact Or.inr ⟨k₁, hk₁, k₂, hk₂, rfl⟩

theorem centralizer_K₂_le_K₁ : ∀ c ∈ centralizer ({z} : Set G),
    (∀ k ∈ K₂, c * k = k * c) → c ∈ K₁ := by
  intro c hc hcK
  exact mem_of_centralizes_sl2_of_nonsquare (Lemma82.two_ne_zero_of_natCard_eq_nine S.card₂) S.φ₂
    S.B S.z_ord S.z_mem₂ S.z_mem₁ S.comm (fun k hk => S.normal₂ S.t S.t_mem k hk) S.B_act S.B_det
    (S.mem_C_cases_prod c hc) hcK

theorem centralizer_K₁_le_K₂ : ∀ c ∈ centralizer ({z} : Set G),
    (∀ k ∈ K₁, c * k = k * c) → c ∈ K₂ := by
  intro c hc hcK
  refine mem_of_centralizes_sl2_of_nonsquare (Lemma82.two_ne_zero_of_natCard_eq_nine S.card₁) S.φ₁
    S.A S.z_ord S.z_mem₁ S.z_mem₂ (fun x hx y hy => (S.comm y hy x hx).symm)
    (fun k hk => S.normal₁ S.t S.t_mem k hk) S.A_act S.A_det ?_ hcK
  rcases S.mem_C_cases_prod c hc with ⟨k₁, hk₁, k₂, hk₂, rfl⟩ | ⟨k₁, hk₁, k₂, hk₂, rfl⟩
  · exact Or.inl ⟨k₂, hk₂, k₁, hk₁, S.comm k₁ hk₁ k₂ hk₂⟩
  · exact Or.inr ⟨k₂, hk₂, k₁, hk₁, by rw [S.comm k₁ hk₁ k₂ hk₂]⟩

theorem K₁_center : ∀ k ∈ K₁, (∀ w ∈ K₁, k * w = w * k) → k = 1 ∨ k = z := fun _ hk hc =>
  eq_one_or_eq_of_commute_of_mulEquiv_sl2 (Lemma82.two_ne_zero_of_natCard_eq_nine S.card₁) S.φ₁
    S.z_mem₁ S.z_ord hk hc

theorem K₁_sq_eq_one : ∀ k ∈ K₁, k * k = 1 → k = 1 ∨ k = z :=
  Lemma82.eq_one_or_eq_of_sq_eq_one_of_mulEquiv_sl2
    (Lemma82.two_ne_zero_of_natCard_eq_nine S.card₁) S.φ₁ S.z_mem₁ S.z_ord

theorem K₂_sq_eq_one : ∀ k ∈ K₂, k * k = 1 → k = 1 ∨ k = z :=
  Lemma82.eq_one_or_eq_of_sq_eq_one_of_mulEquiv_sl2
    (Lemma82.two_ne_zero_of_natCard_eq_nine S.card₂) S.φ₂ S.z_mem₂ S.z_ord

theorem K₁_involution : ∀ k ∈ K₁, orderOf k = 2 → k = z := by
  intro k hk hko
  have hkk : k * k = 1 := by rw [← sq, ← hko]; exact pow_orderOf_eq_one k
  rcases S.K₁_sq_eq_one k hk hkk with rfl | h
  · simp at hko
  · exact h

theorem K₂_involution : ∀ k ∈ K₂, orderOf k = 2 → k = z := by
  intro k hk hko
  have hkk : k * k = 1 := by rw [← sq, ← hko]; exact pow_orderOf_eq_one k
  rcases S.K₂_sq_eq_one k hk hkk with rfl | h
  · simp at hko
  · exact h

end Facts

section OddFacts

variable {G : Type} [Group G] [Finite G] {z : G} {K₁ K₂ : Subgroup G} {F₁ F₂ : Type} [Field F₁]
  [Field F₂]
variable (S : Q9Setting G z K₁ K₂ F₁ F₂)
include S

theorem K₂_odd_normal : ∀ O : Subgroup G, (∀ k ∈ K₂, ∀ o ∈ O, k * o * k⁻¹ ∈ O) →
    Odd (Nat.card O) → ∀ x ∈ K₂, x ∈ O → x = 1 := by
  intro O hO hodd
  have : Finite F₂ := Nat.finite_of_card_ne_zero (by rw [S.card₂]; norm_num)
  exact sl2_nine_inf_odd_normal_trivial K₂ O hO hodd S.card₂ S.φ₂

end OddFacts

end Q9Setting

end CFSG.GH74.GLS.Stage4.Q9
