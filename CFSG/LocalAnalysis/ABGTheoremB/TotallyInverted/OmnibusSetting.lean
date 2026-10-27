module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.OmnibusTools
public import CFSG.CharacterTheory.Wreathed.InvertedOddCyclingLiftSupport
public import CFSG.LocalAnalysis.ABGTheoremB.SettingAPI
public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.Statements

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Omnibus

open CFSG.ABGLocalTools CFSG.QuasiDihedralFusion
open scoped Pointwise

variable {G : Type} [Group G] {σ : Setting G} {r : ℕ}

section FourGroup

theorem mem_zpowers_of_orderOf_two {x g : G} (hx : orderOf x = 2)
    (hg : g ∈ Subgroup.zpowers x) : g = 1 ∨ g = x := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  rw [← zpow_mod_orderOf, hx]
  push_cast
  rcases Int.emod_two_eq_zero_or_one k with h | h <;> simp [h]

@[simp] theorem xs_zero : σ.xs 0 = σ.x := rfl
@[simp] theorem xs_one : σ.xs 1 = σ.x₂ := rfl
@[simp] theorem xs_two : σ.xs 2 = σ.x * σ.x₂ := rfl

theorem xs_mem_T (i : Fin 3) : σ.xs i ∈ σ.T := by
  fin_cases i
  · exact σ.x_mem_T
  · exact σ.x₂_mem_T
  · exact σ.T.mul_mem σ.x_mem_T σ.x₂_mem_T

theorem succ_ne_self (i : Fin 3) : i + 1 ≠ i := by
  fin_cases i <;> decide

theorem comm_of_mem_C {c : G} (hc : c ∈ σ.C) {t : G} (ht : t ∈ σ.T) : t * c = c * t :=
  (Subgroup.mem_centralizer_iff.mp hc) t ht

theorem C_le_Ns (i : Fin 3) : σ.C ≤ σ.Ns i := by
  intro c hc
  rw [Setting.Ns, Subgroup.mem_centralizer_singleton_iff]
  exact (comm_of_mem_C hc (xs_mem_T i)).symm

theorem mem_Ns_iff {i : Fin 3} {g : G} : g ∈ σ.Ns i ↔ σ.xs i * g = g * σ.xs i := by
  rw [Setting.Ns, Subgroup.mem_centralizer_singleton_iff]
  exact eq_comm

theorem C_le_normalizer_T : σ.C ≤ Subgroup.normalizer ((σ.T : Subgroup G) : Set G) :=
  Subgroup.centralizer_le_normalizer _

theorem C_le_M : σ.C ≤ σ.M := Subgroup.le_normalizer

theorem normalizer_T_le_M : Subgroup.normalizer ((σ.T : Subgroup G) : Set G) ≤ σ.M := by
  intro g hg
  apply mem_normalizer_of_conjSub_eq
  have hT : conjSub g σ.T = σ.T := conjSub_eq_self hg
  ext y
  rw [mem_conjSub, Setting.C, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  constructor
  · intro h t ht
    have ht' : g⁻¹ * t * g ∈ σ.T := by
      have ht2 : t ∈ conjSub g σ.T := by rw [hT]; exact ht
      exact mem_conjSub.mp ht2
    have := h _ ht'
    calc t * y = g * ((g⁻¹ * t * g) * (g⁻¹ * y * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * y * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [this]
      _ = y * t := by group
  · intro h t ht
    have ht' : g * t * g⁻¹ ∈ σ.T := by
      rw [← hT]
      exact conj_mem_conjSub ht
    have := h _ ht'
    calc t * (g⁻¹ * y * g) = g⁻¹ * ((g * t * g⁻¹) * y) * g := by group
      _ = g⁻¹ * (y * (g * t * g⁻¹)) * g := by rw [this]
      _ = g⁻¹ * y * g * t := by group

variable [Finite G]

theorem T_isKleinFour (hσ : σ.IsValid) : IsKleinFour σ.T := by
  apply CFSG.Wreathed.isKleinFour_closure_pair hσ.x_order hσ.x₂_order hσ.commute
  rw [Subgroup.disjoint_def]
  intro g hg hg'
  rcases mem_zpowers_of_orderOf_two hσ.x_order hg with h | h
  · exact h
  rcases mem_zpowers_of_orderOf_two hσ.x₂_order hg' with h' | h'
  · exact h'
  exact absurd (h.symm.trans h') hσ.x_ne_x₂

theorem T_isPGroup (hσ : σ.IsValid) : IsPGroup 2 σ.T := by
  have := T_isKleinFour hσ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact IsPGroup.iff_card.mpr ⟨2, by rw [IsKleinFour.card_four]; norm_num⟩

theorem x_ne_one (hσ : σ.IsValid) : σ.x ≠ 1 := by
  intro h
  have := hσ.x_order
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem x₂_ne_one (hσ : σ.IsValid) : σ.x₂ ≠ 1 := by
  intro h
  have := hσ.x₂_order
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

theorem x_mul_x₂_ne_one (hσ : σ.IsValid) : σ.x * σ.x₂ ≠ 1 := by
  intro h
  have hx : σ.x⁻¹ = σ.x := by
    have hx2 : σ.x ^ 2 = 1 := by rw [← hσ.x_order]; exact pow_orderOf_eq_one _
    rw [inv_eq_iff_mul_eq_one, ← pow_two, hx2]
  apply hσ.x_ne_x₂
  rw [← hx]
  exact inv_eq_of_mul_eq_one_right h

theorem xs_ne_one (hσ : σ.IsValid) (i : Fin 3) : σ.xs i ≠ 1 := by
  fin_cases i
  · exact x_ne_one hσ
  · exact x₂_ne_one hσ
  · exact x_mul_x₂_ne_one hσ

theorem xs_injective (hσ : σ.IsValid) : Function.Injective σ.xs := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [xs_zero, xs_one, xs_two, Fin.mk_zero,
    Fin.mk_one, Fin.reduceFinMk] at hij ⊢ <;> try rfl
  · exact absurd hij hσ.x_ne_x₂
  · exact absurd (by simpa using hij) (x₂_ne_one hσ)
  · exact absurd hij.symm hσ.x_ne_x₂
  · exact absurd (by simpa using hij.symm) (x_ne_one hσ)
  · exact absurd (by simpa using hij.symm) (x₂_ne_one hσ)
  · exact absurd (by simpa using hij) (x_ne_one hσ)

theorem xs_orderOf (hσ : σ.IsValid) (i : Fin 3) : orderOf (σ.xs i) = 2 := by
  have := T_isKleinFour hσ
  exact kleinFour_orderOf (xs_mem_T i) (xs_ne_one hσ i)

theorem mem_T_iff (hσ : σ.IsValid) {g : G} : g ∈ σ.T ↔ g = 1 ∨ ∃ i, g = σ.xs i := by
  have := T_isKleinFour hσ
  constructor
  · intro hg
    rcases kleinFour_mem_cases σ.x_mem_T σ.x₂_mem_T hg (x_ne_one hσ) (x₂_ne_one hσ)
      hσ.x_ne_x₂ with h | h | h | h
    · exact Or.inl h
    · exact Or.inr ⟨0, h⟩
    · exact Or.inr ⟨1, h⟩
    · exact Or.inr ⟨2, h⟩
  · rintro (rfl | ⟨i, rfl⟩)
    · exact σ.T.one_mem
    · exact xs_mem_T i

theorem T_le_Ns (hσ : σ.IsValid) (i : Fin 3) : σ.T ≤ σ.Ns i :=
  (σ.T_le_C hσ).trans (C_le_Ns i)

theorem Ns_inf_Ns (hσ : σ.IsValid) {i j : Fin 3} (hij : i ≠ j) : σ.Ns i ⊓ σ.Ns j = σ.C := by
  have := T_isKleinFour hσ
  rw [Setting.Ns, Setting.Ns, Setting.C,
    centralizer_kleinFour_eq (xs_mem_T i) (xs_mem_T j) (xs_ne_one hσ i) (xs_ne_one hσ j)
      (fun h => hij (xs_injective hσ h))]

theorem T_le_normalizer_Ns (hσ : σ.IsValid) (i : Fin 3) :
    σ.T ≤ Subgroup.normalizer ((σ.Ns i : Subgroup G) : Set G) :=
  (T_le_Ns hσ i).trans Subgroup.le_normalizer

theorem exists_conj_xs_eq (hσ : σ.IsValid) {g : G}
    (hg : g ∈ Subgroup.normalizer ((σ.T : Subgroup G) : Set G)) (i : Fin 3) :
    ∃ j, g * σ.xs i * g⁻¹ = σ.xs j := by
  have hmem : g * σ.xs i * g⁻¹ ∈ σ.T := (Subgroup.mem_normalizer_iff.mp hg _).mp (xs_mem_T i)
  rcases (mem_T_iff hσ).mp hmem with h | ⟨j, hj⟩
  · exfalso
    apply xs_ne_one hσ i
    have : σ.xs i = g⁻¹ * (g * σ.xs i * g⁻¹) * g := by group
    rw [this, h]
    group
  · exact ⟨j, hj⟩

end FourGroup

variable [Finite G]

section F₀

theorem T_le_F₀ (hσ : σ.IsValid) : σ.T ≤ σ.F₀ :=
  le_inf (σ.T_le_D hσ) (σ.T_le_C hσ)

omit [Finite G] in
theorem F₀_le_C : σ.F₀ ≤ σ.C := inf_le_right

theorem mem_T_of_mem_C_of_sq (Δ : Data σ r) {c : G} (hc : c ∈ σ.C) (hc2 : c ^ 2 = 1) : c ∈ σ.T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcp : IsPGroup 2 (Subgroup.zpowers c) := by
    rintro ⟨y, hy⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, show ((2 : ℕ) : ℤ) = (2 : ℕ) by rfl,
      zpow_natCast, hc2, one_zpow]
  obtain ⟨k, hk, hle⟩ := exists_le_conjSub_of_isSylowOf Δ.F₀_sylow
    ((Subgroup.zpowers_le).mpr hc) hcp
  have hck : c ∈ conjSub k σ.F₀ := hle (Subgroup.mem_zpowers c)
  rw [mem_conjSub] at hck
  have hT : k⁻¹ * c * k ∈ σ.T := Δ.F₀_omega _ hck (by
    rw [show (k⁻¹ * c * k) ^ 2 = k⁻¹ * c ^ 2 * k by rw [pow_two, pow_two]; group, hc2]
    group)
  have hTk : conjSub k σ.T = σ.T := conjSub_eq_self (C_le_normalizer_T hk)
  rw [← hTk, mem_conjSub]
  exact hT

end F₀

section ThreeElement

variable (Δ : Data σ r)

theorem a_pow_conj_x (i : Fin 3) : Δ.a ^ (i : ℕ) * σ.x * (Δ.a ^ (i : ℕ))⁻¹ = σ.xs i := by
  fin_cases i
  · simp
  · simpa using Δ.a_cycle 0
  · have h1 := Δ.a_cycle 0
    have h2 := Δ.a_cycle 1
    simp only [xs_zero, xs_one, Fin.zero_add, Fin.reduceAdd] at h1 h2
    simp only [Fin.reduceFinMk, xs_two]
    rw [show Δ.a ^ 2 * σ.x * (Δ.a ^ 2)⁻¹ = Δ.a * (Δ.a * σ.x * Δ.a⁻¹) * Δ.a⁻¹ by
      rw [pow_two]; group, h1, h2]
    rfl

theorem conjSub_a_pow_N (i : Fin 3) : conjSub (Δ.a ^ (i : ℕ)) σ.N = σ.Ns i := by
  rw [Setting.N, conjSub_centralizer, a_pow_conj_x, Setting.Ns]

theorem a_pow_mem_M (k : ℕ) : Δ.a ^ k ∈ σ.M := σ.M.pow_mem Δ.a_mem k

theorem conjSub_a_pow_C (k : ℕ) : conjSub (Δ.a ^ k) σ.C = σ.C :=
  conjSub_eq_self (a_pow_mem_M Δ k)

theorem not_dvd_card_C_inf_L (i : Fin 3) :
    ¬ r ∣ Nat.card (σ.C ⊓ conjSub (Δ.a ^ (i : ℕ)) σ.L : Subgroup G) := by
  have h : σ.C ⊓ conjSub (Δ.a ^ (i : ℕ)) σ.L = conjSub (Δ.a ^ (i : ℕ)) (σ.C ⊓ σ.L) := by
    rw [conjSub_inf, conjSub_a_pow_C]
  rw [h, card_conjSub]
  exact Δ.totallyInverted

theorem J_le_N (hσ : σ.IsValid) : Δ.J ≤ σ.N := Δ.J_le.trans hσ.L₀_le_N

theorem J_le_L : Δ.J ≤ σ.L := Δ.J_le.trans le_sup_left

theorem Q_le_Ns (hσ : σ.IsValid) (i : Fin 3) : Δ.Q i ≤ σ.Ns i ∧ Δ.Qs i ≤ σ.Ns i := by
  have h : conjSub (Δ.a ^ (i : ℕ)) Δ.J ≤ σ.Ns i := by
    rw [← conjSub_a_pow_N Δ i]
    exact conjSub_mono (J_le_N Δ hσ)
  exact ⟨(Δ.Q_le i).1.trans h, (Δ.Q_le i).2.trans h⟩

theorem Q_le_L (i : Fin 3) :
    Δ.Q i ≤ conjSub (Δ.a ^ (i : ℕ)) σ.L ∧ Δ.Qs i ≤ conjSub (Δ.a ^ (i : ℕ)) σ.L :=
  ⟨(Δ.Q_le i).1.trans (conjSub_mono (J_le_L Δ)), (Δ.Q_le i).2.trans (conjSub_mono (J_le_L Δ))⟩

end ThreeElement

section Blocks

variable (Δ : Data σ r)

structure IsBlock (σ : Setting G) (r : ℕ) (i : Fin 3) (Y : Subgroup G) : Prop where
  isPGroup : IsPGroup r Y
  normalized : σ.C ≤ Subgroup.normalizer (Y : Set G)
  le_Ns : Y ≤ σ.Ns i
  inverted : ∀ u ∈ Y, σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹

theorem Q_inverted (hσ : σ.IsValid) (i : Fin 3) :
    (∀ u ∈ Δ.Q i, σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹) ∧
      ∀ u ∈ Δ.Qs i, σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹ := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  by_cases hq : σ.DeltaEpsMinus ∧ r ∣ σ.q
  · obtain ⟨-, hcardQ, hcardQs, -, -, -, hirrQ, hirrQs, -, -⟩ := Δ.Q_cases hq i
    have key : ∀ Q' : Subgroup G, IsPGroup r Q' → Nat.card Q' = σ.q → Q' ≤ σ.Ns i →
        Q' ≤ conjSub (Δ.a ^ (i : ℕ)) σ.L → σ.C ≤ Subgroup.normalizer (Q' : Set G) →
        (∀ X : Subgroup G, X ≤ Q' → σ.C ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = Q') →
        ∀ u ∈ Q', σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹ := by
      intro Q' hQp hcard hQN hQL hQC hirr u hu
      set Z : Subgroup G := Q' ⊓ σ.Ns (i + 1) with hZ
      have hCZ : σ.C ≤ Subgroup.normalizer (Z : Set G) := fun c hc =>
        mem_normalizer_inf (hQC hc) (Subgroup.le_normalizer (C_le_Ns (i + 1) hc))
      rcases hirr Z inf_le_left hCZ with hZbot | hZQ
      ·
        have hodd : Odd (Nat.card Q') := odd_card_of_isPGroup Δ.prime Δ.ne_two hQp
        have hx : σ.xs (i + 1) ∈ Subgroup.normalizer (Q' : Set G) :=
          hQC ((σ.T_le_C hσ) (xs_mem_T (i + 1)))
        obtain ⟨hdec, -⟩ := odd_fixed_mul_inverted hodd (xs_orderOf hσ (i + 1)) hx
        have hZ' : Q' ⊓ Subgroup.centralizer {σ.xs (i + 1)} = ⊥ := hZbot
        have hu' : u ∈ (Q' : Set G) := hu
        rw [hdec] at hu'
        obtain ⟨z, hz, v, hv, rfl⟩ := hu'
        have hz1 : z = 1 := by
          have : z ∈ (⊥ : Subgroup G) := hZ' ▸ hz
          exact Subgroup.mem_bot.mp this
        subst hz1
        simp only [one_mul]
        exact (OddInversion.mem_invertedSet.mp hv).2
      · exfalso
        have hQC' : Q' ≤ σ.C := by
          rw [← Ns_inf_Ns hσ (succ_ne_self i).symm]
          exact le_inf hQN (hZQ ▸ inf_le_right)
        have hdvd : Nat.card Q' ∣ Nat.card (σ.C ⊓ conjSub (Δ.a ^ (i : ℕ)) σ.L : Subgroup G) :=
          Subgroup.card_dvd_of_le (le_inf hQC' hQL)
        exact not_dvd_card_C_inf_L Δ i ((hcard ▸ hq.2).trans hdvd)
    exact ⟨key _ (Δ.Q_pgroup i).1 hcardQ (Q_le_Ns Δ hσ i).1 (Q_le_L Δ i).1 (Δ.Q_C i).1 hirrQ,
      key _ (Δ.Q_pgroup i).2 hcardQs (Q_le_Ns Δ hσ i).2 (Q_le_L Δ i).2 (Δ.Q_C i).2 hirrQs⟩
  · obtain ⟨hQ, hQs⟩ := Δ.Q_trivial hq i
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [hQ, Subgroup.mem_bot] at hu
      subst hu
      group
    · rw [hQs, Subgroup.mem_bot] at hu
      subst hu
      group

include Δ in
theorem isBlock_Ps (i : Fin 3) : IsBlock σ r i (σ.Ps r i) where
  isPGroup := isPGroup_pCoreIn r _
  normalized := (C_le_Ns i).trans (le_normalizer_pCoreIn r _)
  le_Ns := pCoreIn_le r _
  inverted := Δ.P_inverted i (i + 1) (succ_ne_self i)

omit [Finite G] in
theorem isBlock_sup {i : Fin 3} {Q' : Subgroup G} (hQp : IsPGroup r Q')
    (hQC : σ.C ≤ Subgroup.normalizer (Q' : Set G)) (hQN : Q' ≤ σ.Ns i)
    (hQinv : ∀ u ∈ Q', σ.xs (i + 1) * u * (σ.xs (i + 1))⁻¹ = u⁻¹)
    (hQP : Q' ≤ Subgroup.centralizer (σ.Ps r i : Set G)) (hP : IsBlock σ r i (σ.Ps r i)) :
    IsBlock σ r i (Q' ⊔ σ.Ps r i) where
  isPGroup := IsPGroup.to_sup_of_normal_right' hQp hP.isPGroup
    (hQP.trans (Subgroup.centralizer_le_normalizer _))
  normalized := fun c hc => mem_normalizer_sup (hQC hc) (hP.normalized hc)
  le_Ns := sup_le hQN hP.le_Ns
  inverted := by
    intro g hg
    have hg' : g ∈ ((Q' ⊔ σ.Ps r i : Subgroup G) : Set G) := hg
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _
      (hQP.trans (Subgroup.centralizer_le_normalizer _))] at hg'
    obtain ⟨q, hq, p, hp, rfl⟩ := hg'
    have hqp : q * p = p * q := (Subgroup.mem_centralizer_iff.mp (hQP hq)) p hp |>.symm
    change σ.xs (i + 1) * (q * p) * (σ.xs (i + 1))⁻¹ = (q * p)⁻¹
    rw [show σ.xs (i + 1) * (q * p) * (σ.xs (i + 1))⁻¹ =
      (σ.xs (i + 1) * q * (σ.xs (i + 1))⁻¹) * (σ.xs (i + 1) * p * (σ.xs (i + 1))⁻¹) by group,
      hQinv q hq, hP.inverted p hp, ← mul_inv_rev, hqp]

theorem isBlock_R (hσ : σ.IsValid) (i : Fin 3) : IsBlock σ r i (R Δ i) := by
  have hP := isBlock_Ps Δ i
  by_cases hq : σ.DeltaEpsMinus ∧ r ∣ σ.q
  · obtain ⟨-, -, -, -, -, -, -, -, hQP, -⟩ := Δ.Q_cases hq i
    exact isBlock_sup (Δ.Q_pgroup i).1 (Δ.Q_C i).1 (Q_le_Ns Δ hσ i).1 (Q_inverted Δ hσ i).1
      hQP hP
  · rw [R, (Δ.Q_trivial hq i).1, bot_sup_eq]
    exact hP

theorem isBlock_Rs (hσ : σ.IsValid) (i : Fin 3) : IsBlock σ r i (Rs Δ i) := by
  have hP := isBlock_Ps Δ i
  by_cases hq : σ.DeltaEpsMinus ∧ r ∣ σ.q
  · obtain ⟨-, -, -, -, -, -, -, -, -, hQP⟩ := Δ.Q_cases hq i
    exact isBlock_sup (Δ.Q_pgroup i).2 (Δ.Q_C i).2 (Q_le_Ns Δ hσ i).2 (Q_inverted Δ hσ i).2
      hQP hP
  · rw [Rs, (Δ.Q_trivial hq i).2, bot_sup_eq]
    exact hP

omit Δ in
theorem IsBlock.eq_one_of_mem_C {i : Fin 3} {Y : Subgroup G} (hY : IsBlock σ r i Y)
    (hr : r.Prime) (hr2 : r ≠ 2) {y : G} (hy : y ∈ Y) (hyC : y ∈ σ.C) : y = 1 := by
  have hodd : Odd (orderOf y) := odd_orderOf_of_mem (odd_card_of_isPGroup hr hr2 hY.isPGroup) hy
  apply eq_one_of_sq_eq_one hodd
  have h1 := hY.inverted y hy
  rw [show σ.xs (i + 1) * y * (σ.xs (i + 1))⁻¹ = y by
    rw [comm_of_mem_C hyC (xs_mem_T (i + 1))]; group] at h1
  rw [pow_two]
  nth_rewrite 2 [h1]
  exact mul_inv_cancel y

end Blocks

end CFSG.ABGTheoremB.TotallyInverted.Omnibus
