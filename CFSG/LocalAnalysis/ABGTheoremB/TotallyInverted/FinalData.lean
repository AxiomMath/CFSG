module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalJ

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

section T

omit [Finite G] in
theorem mem_C_iff (g : G) : g ∈ σ.C ↔ g * σ.x = σ.x * g ∧ g * σ.x₂ = σ.x₂ * g := by
  rw [Setting.C, Setting.T, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h σ.x (Set.mem_insert _ _)).symm,
      (h σ.x₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _))).symm⟩
  · rintro ⟨h1, h2⟩ t (rfl | rfl)
    · exact h1.symm
    · exact h2.symm

omit [Finite G] in
theorem mem_C_of_conj (g : G) (h1 : g * σ.x * g⁻¹ = σ.x) (h2 : g * σ.x₂ * g⁻¹ = σ.x₂) :
    g ∈ σ.C := by
  rw [mem_C_iff]
  constructor
  · calc g * σ.x = g * σ.x * g⁻¹ * g := by group
      _ = σ.x * g := by rw [h1]
  · calc g * σ.x₂ = g * σ.x₂ * g⁻¹ * g := by group
      _ = σ.x₂ * g := by rw [h2]

omit [Finite G] in
theorem conj_xs_of_mem_C {c : G} (hc : c ∈ σ.C) (i : Fin 3) : c * σ.xs i * c⁻¹ = σ.xs i := by
  rw [(Subgroup.mem_centralizer_iff.mp hc _ (xs_mem_T i)).symm, mul_inv_cancel_right]

theorem mem_T_cases (hσ : σ.IsValid) {t : G} (ht : t ∈ σ.T) :
    t = 1 ∨ t = σ.xs 0 ∨ t = σ.xs 1 ∨ t = σ.xs 2 := by
  have := isKleinFour_T hσ
  by_cases h1 : t = 1
  · exact Or.inl h1
  by_cases h2 : t = σ.x
  · exact Or.inr (Or.inl h2)
  by_cases h3 : t = σ.x₂
  · exact Or.inr (Or.inr (Or.inl h3))
  right; right; right
  have key := IsKleinFour.eq_mul_of_ne_all (G := σ.T) (x := ⟨σ.x, σ.x_mem_T⟩)
    (y := ⟨σ.x₂, σ.x₂_mem_T⟩) (z := ⟨t, ht⟩) (fun h => x_ne_one hσ (congrArg Subtype.val h))
    (fun h => x₂_ne_one hσ (congrArg Subtype.val h))
    (fun h => hσ.x_ne_x₂ (congrArg Subtype.val h)) (fun h => h1 (congrArg Subtype.val h))
    (fun h => h2 (congrArg Subtype.val h)) (fun h => h3 (congrArg Subtype.val h))
  exact congrArg Subtype.val key

theorem exists_conj_xs_eq (hσ : σ.IsValid) {g : G} (hg : g ∈ Subgroup.normalizer (σ.T : Set G))
    (i : Fin 3) : ∃ j : Fin 3, g * σ.xs i * g⁻¹ = σ.xs j := by
  have hmem : g * σ.xs i * g⁻¹ ∈ σ.T :=
    (Subgroup.mem_normalizer_iff.mp hg _).mp (xs_mem_T i)
  rcases mem_T_cases hσ hmem with h | h | h | h
  · exfalso
    apply xs_ne_one hσ i
    have : σ.xs i = g⁻¹ * (g * σ.xs i * g⁻¹) * g := by group
    rw [this, h]
    group
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem Ns_ne_iff (hσ : σ.IsValid) {i j : Fin 3} : σ.xs i = σ.xs j ↔ i = j := by
  constructor
  · intro h
    by_contra hij
    have h' : j = i + 1 ∨ j = i + 2 := by
      fin_cases i <;> fin_cases j <;> simp_all
    rcases h' with rfl | rfl
    · exact xs_ne_xs_succ hσ i h
    · have e := xs_add_two hσ i
      rw [← h, ← mul_one (σ.xs i), mul_assoc, one_mul] at e
      exact xs_ne_one hσ (i + 1) (mul_left_cancel e.symm)
  · rintro rfl
    rfl

end T

section A

variable (Δ : Data σ r)

theorem conjSub_a_C : conjSub Δ.a σ.C = σ.C := conjSub_eq_self_iff.mpr Δ.a_mem

theorem conjSub_a_T : conjSub Δ.a σ.T = σ.T := conjSub_eq_self_iff.mpr (a_mem_normalizer_T Δ)

theorem conjSub_a_pow_C (k : ℕ) : conjSub (Δ.a ^ k) σ.C = σ.C := by
  induction k with
  | zero => rw [pow_zero, conjSub_one]
  | succ k ih => rw [pow_succ, ← conjSub_conjSub, conjSub_a_C, ih]

theorem conjSub_a_pow_T (k : ℕ) : conjSub (Δ.a ^ k) σ.T = σ.T := by
  induction k with
  | zero => rw [pow_zero, conjSub_one]
  | succ k ih => rw [pow_succ, ← conjSub_conjSub, conjSub_a_T, ih]

theorem a_pow_mem_normalizer_C (k : ℕ) : Δ.a ^ k ∈ Subgroup.normalizer (σ.C : Set G) :=
  Subgroup.pow_mem _ Δ.a_mem k

theorem a_pow_mem_normalizer_T (k : ℕ) : Δ.a ^ k ∈ Subgroup.normalizer (σ.T : Set G) :=
  Subgroup.pow_mem _ (a_mem_normalizer_T Δ) k

theorem a_pow_conj_xs (k i : Fin 3) :
    Δ.a ^ (k : ℕ) * σ.xs i * (Δ.a ^ (k : ℕ))⁻¹ = σ.xs (i + k) := by
  match k with
  | 0 => simp
  | 1 => simpa using Δ.a_cycle i
  | 2 =>
    rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_two, mul_inv_rev,
      show Δ.a * Δ.a * σ.xs i * (Δ.a⁻¹ * Δ.a⁻¹) = Δ.a * (Δ.a * σ.xs i * Δ.a⁻¹) * Δ.a⁻¹ by group,
      Δ.a_cycle, Δ.a_cycle, add_assoc]
    rfl

theorem conjSub_a_pow_Ns (k i : Fin 3) :
    conjSub (Δ.a ^ (k : ℕ)) (σ.Ns i) = σ.Ns (i + k) := by
  rw [Setting.Ns, conjSub_centralizer_singleton, a_pow_conj_xs]
  rfl

theorem conjSub_a_pow_of_succ {X : Fin 3 → Subgroup G}
    (hX : ∀ i, conjSub Δ.a (X i) = X (i + 1)) (k i : Fin 3) :
    conjSub (Δ.a ^ (k : ℕ)) (X i) = X (i + k) := by
  match k with
  | 0 => simp [conjSub_one]
  | 1 => simpa using hX i
  | 2 =>
    rw [show ((2 : Fin 3) : ℕ) = 2 from rfl, pow_two, ← conjSub_conjSub, hX, hX, add_assoc]
    rfl

theorem conjSub_a_pow_Ps (k i : Fin 3) :
    conjSub (Δ.a ^ (k : ℕ)) (σ.Ps r i) = σ.Ps r (i + k) :=
  conjSub_a_pow_of_succ Δ (X := σ.Ps r) Δ.P_conj k i

theorem conjSub_a_pow_Q (k i : Fin 3) : conjSub (Δ.a ^ (k : ℕ)) (Δ.Q i) = Δ.Q (i + k) :=
  conjSub_a_pow_of_succ Δ (X := Δ.Q) (fun i => (Δ.Q_conj i).1) k i

theorem conjSub_a_pow_Qs (k i : Fin 3) : conjSub (Δ.a ^ (k : ℕ)) (Δ.Qs i) = Δ.Qs (i + k) :=
  conjSub_a_pow_of_succ Δ (X := Δ.Qs) (fun i => (Δ.Q_conj i).2) k i

theorem conjSub_a_pow_R (k i : Fin 3) : conjSub (Δ.a ^ (k : ℕ)) (R Δ i) = R Δ (i + k) :=
  conjSub_a_pow_of_succ Δ (X := R Δ) (conjSub_R Δ) k i

theorem conjSub_a_pow_Rs (k i : Fin 3) : conjSub (Δ.a ^ (k : ℕ)) (Rs Δ i) = Rs Δ (i + k) :=
  conjSub_a_pow_of_succ Δ (X := Rs Δ) (conjSub_Rs Δ) k i

theorem zero_add_fin (i : Fin 3) : (0 : Fin 3) + i = i := zero_add i

end A

section Subgroups

variable (Δ : Data σ r)

omit [Finite G] in
theorem Ps_le_Ns (i : Fin 3) : σ.Ps r i ≤ σ.Ns i := pCoreIn_le r _

omit [Finite G] in
theorem isPGroup_Ps (i : Fin 3) : IsPGroup r (σ.Ps r i) := isPGroup_pCoreIn r _

theorem Ps_zero_le_ON (Δ : Data σ r) : σ.Ps r 0 ≤ σ.ON :=
  le_oddCoreIn (Ps_le_Ns 0) (le_normalizer_pCoreIn r _)
    (odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_Ps 0))

theorem Ps_zero_ne_bot (Δ : Data σ r) : σ.Ps r 0 ≠ ⊥ := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  intro h
  have hc := Δ.P_sylow.card_eq
  rw [h, Subgroup.card_bot] at hc
  have hpos : 0 < (Nat.card σ.ON).factorization r :=
    Nat.Prime.factorization_pos_of_dvd Δ.prime Nat.card_pos.ne' Δ.dvd
  exact (Nat.one_lt_pow hpos.ne' Δ.prime.one_lt).ne' hc.symm

theorem Ps_ne_bot (Δ : Data σ r) (i : Fin 3) : σ.Ps r i ≠ ⊥ := by
  rw [← zero_add_fin i, ← conjSub_a_pow_Ps Δ, Ne, conjSub_eq_bot_iff]
  exact Ps_zero_ne_bot Δ

theorem J_le_L : Δ.J ≤ σ.L := Δ.J_le.trans le_sup_left

theorem ON_le_L (hσ : σ.IsValid) : σ.ON ≤ σ.L := hσ.ON_le_L₀.trans le_sup_left

theorem Q_le_J_conj (i : Fin 3) : Δ.Q i ≤ conjSub (Δ.a ^ (i : ℕ)) Δ.J := (Δ.Q_le i).1

theorem Qs_le_J_conj (i : Fin 3) : Δ.Qs i ≤ conjSub (Δ.a ^ (i : ℕ)) Δ.J := (Δ.Q_le i).2

theorem J_conj_le_Ns (hσ : σ.IsValid) (i : Fin 3) :
    conjSub (Δ.a ^ (i : ℕ)) Δ.J ≤ σ.Ns i := by
  rw [← zero_add_fin i, ← conjSub_a_pow_Ns Δ, zero_add_fin i]
  exact conjSub_mono (J_le_N hσ Δ)

theorem Q_le_Ns (hσ : σ.IsValid) (i : Fin 3) : Δ.Q i ≤ σ.Ns i :=
  (Q_le_J_conj Δ i).trans (J_conj_le_Ns Δ hσ i)

theorem Qs_le_Ns (hσ : σ.IsValid) (i : Fin 3) : Δ.Qs i ≤ σ.Ns i :=
  (Qs_le_J_conj Δ i).trans (J_conj_le_Ns Δ hσ i)

theorem R_le_Ns (hσ : σ.IsValid) (i : Fin 3) : R Δ i ≤ σ.Ns i :=
  sup_le (Q_le_Ns Δ hσ i) (Ps_le_Ns i)

theorem Rs_le_Ns (hσ : σ.IsValid) (i : Fin 3) : Rs Δ i ≤ σ.Ns i :=
  sup_le (Qs_le_Ns Δ hσ i) (Ps_le_Ns i)

theorem isPGroup_R (hσ : σ.IsValid) (i : Fin 3) : IsPGroup r (R Δ i) :=
  IsPGroup.to_sup_of_normal_right' (Δ.Q_pgroup i).1 (isPGroup_Ps i)
    ((Q_le_Ns Δ hσ i).trans (le_normalizer_pCoreIn r _))

theorem isPGroup_Rs (hσ : σ.IsValid) (i : Fin 3) : IsPGroup r (Rs Δ i) :=
  IsPGroup.to_sup_of_normal_right' (Δ.Q_pgroup i).2 (isPGroup_Ps i)
    ((Qs_le_Ns Δ hσ i).trans (le_normalizer_pCoreIn r _))

theorem Ps_le_R (i : Fin 3) : σ.Ps r i ≤ R Δ i := le_sup_right

theorem Ps_le_Rs (i : Fin 3) : σ.Ps r i ≤ Rs Δ i := le_sup_right

theorem Q_le_R (i : Fin 3) : Δ.Q i ≤ R Δ i := le_sup_left

theorem Qs_le_Rs (i : Fin 3) : Δ.Qs i ≤ Rs Δ i := le_sup_left

theorem eq_bot_of_isPGroup_of_le {X Y : Subgroup G} (hX : IsPGroup r X) (hXY : X ≤ Y)
    (hr : r.Prime) (hY : ¬ r ∣ Nat.card Y) : X = ⊥ := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  rcases k with _ | k
  · exact Subgroup.card_eq_one.mp (by simpa using hk)
  · exfalso
    apply hY
    have := Subgroup.card_dvd_of_le hXY
    rw [hk, pow_succ] at this
    exact (Dvd.intro_left _ rfl).trans this

theorem inf_C_eq_bot_of_le_L (Δ : Data σ r) {X : Subgroup G} (hX : IsPGroup r X) (hXL : X ≤ σ.L) :
    X ⊓ σ.C = ⊥ := by
  apply eq_bot_of_isPGroup_of_le (hX.to_le inf_le_left) _ Δ.prime Δ.totallyInverted
  rw [inf_comm]
  exact inf_le_inf_left _ hXL

theorem R_zero_le_L (hσ : σ.IsValid) : R Δ 0 ≤ σ.L :=
  sup_le ((Q_le_J_conj Δ 0).trans (by simpa [conjSub_one] using J_le_L Δ))
    ((Ps_zero_le_ON Δ).trans (ON_le_L hσ))

theorem Rs_zero_le_L (hσ : σ.IsValid) : Rs Δ 0 ≤ σ.L :=
  sup_le ((Qs_le_J_conj Δ 0).trans (by simpa [conjSub_one] using J_le_L Δ))
    ((Ps_zero_le_ON Δ).trans (ON_le_L hσ))

theorem R_inf_C (hσ : σ.IsValid) (i : Fin 3) : R Δ i ⊓ σ.C = ⊥ := by
  rw [← zero_add_fin i, ← conjSub_a_pow_R Δ, ← conjSub_a_pow_C Δ (i : ℕ), ← conjSub_inf,
    inf_C_eq_bot_of_le_L Δ (isPGroup_R Δ hσ 0) (R_zero_le_L Δ hσ), conjSub_bot]

theorem Rs_inf_C (hσ : σ.IsValid) (i : Fin 3) : Rs Δ i ⊓ σ.C = ⊥ := by
  rw [← zero_add_fin i, ← conjSub_a_pow_Rs Δ, ← conjSub_a_pow_C Δ (i : ℕ), ← conjSub_inf,
    inf_C_eq_bot_of_le_L Δ (isPGroup_Rs Δ hσ 0) (Rs_zero_le_L Δ hσ), conjSub_bot]

theorem C_le_normalizer_Q (i : Fin 3) : σ.C ≤ Subgroup.normalizer (Δ.Q i : Set G) :=
  (Δ.Q_C i).1

theorem C_le_normalizer_Qs (i : Fin 3) : σ.C ≤ Subgroup.normalizer (Δ.Qs i : Set G) :=
  (Δ.Q_C i).2

theorem T_le_normalizer_of_C_le (hσ : σ.IsValid) {X : Subgroup G}
    (hX : σ.C ≤ Subgroup.normalizer (X : Set G)) : σ.T ≤ Subgroup.normalizer (X : Set G) :=
  (σ.T_le_C hσ).trans hX

theorem eq_one_of_mem_comp_of_mem_Ns (hσ : σ.IsValid) {U : Subgroup G} {k i : Fin 3} {u : G}
    (hu : u ∈ comp σ U k) (huN : u ∈ σ.Ns i) (hki : k ≠ i) (hodd : Odd (orderOf u)) :
    u = 1 := by
  have hc : σ.xs i * u = u * σ.xs i := (Subgroup.mem_centralizer_singleton_iff.mp huN).symm
  have h' : i = k + 1 ∨ i = k + 2 := by
    fin_cases k <;> fin_cases i <;> simp_all
  rcases h' with rfl | rfl
  · exact eq_one_of_conj_eq_inv_of_commute hodd hu.2.2 hc
  · exact eq_one_of_conj_eq_inv_of_commute hodd (conj_xs_add_two_of_mem_comp hσ hu) hc

theorem mem_comp_of_le_Ns (hσ : σ.IsValid) {Y : Subgroup G} (hY : Odd (Nat.card Y))
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) (hYC : Y ⊓ σ.C = ⊥) {i : Fin 3}
    (hYN : Y ≤ σ.Ns i) {u : G} (hu : u ∈ Y) : u ∈ comp σ Y i := by
  obtain ⟨u₀, h₀, u₁, h₁, u₂, h₂, u₃, h₃, rfl⟩ := exists_mul_comp hσ hY hTY hu
  rw [hYC, Subgroup.mem_bot] at h₀
  subst h₀
  have hodd : ∀ {v : G}, v ∈ Y → Odd (orderOf v) := fun hv => odd_orderOf_of_mem hY hv
  have e : ∀ {k : Fin 3} {v : G}, v ∈ comp σ Y k → k ≠ i → v = 1 := fun hv hki =>
    eq_one_of_mem_comp_of_mem_Ns hσ hv (hYN hv.1) hki (hodd hv.1)
  match i with
  | 0 =>
    rw [e h₂ (by decide), e h₃ (by decide)]
    simpa using h₁
  | 1 =>
    rw [e h₁ (by decide), e h₃ (by decide)]
    simpa using h₂
  | 2 =>
    rw [e h₁ (by decide), e h₂ (by decide)]
    simpa using h₃

theorem inverted_of_le_Ns (hσ : σ.IsValid) {Y : Subgroup G} (hY : Odd (Nat.card Y))
    (hTY : σ.T ≤ Subgroup.normalizer (Y : Set G)) (hYC : Y ⊓ σ.C = ⊥) {i : Fin 3}
    (hYN : Y ≤ σ.Ns i) {j : Fin 3} (hji : j ≠ i) {u : G} (hu : u ∈ Y) :
    σ.xs j * u * (σ.xs j)⁻¹ = u⁻¹ := by
  have hc := mem_comp_of_le_Ns hσ hY hTY hYC hYN hu
  have h' : j = i + 1 ∨ j = i + 2 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases h' with rfl | rfl
  · exact hc.2.2
  · exact conj_xs_add_two_of_mem_comp hσ hc

theorem odd_card_R (hσ : σ.IsValid) (i : Fin 3) : Odd (Nat.card (R Δ i)) :=
  odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_R Δ hσ i)

theorem odd_card_Rs (hσ : σ.IsValid) (i : Fin 3) : Odd (Nat.card (Rs Δ i)) :=
  odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_Rs Δ hσ i)

theorem R_inverted (hσ : σ.IsValid) {i j : Fin 3} (hji : j ≠ i) {u : G} (hu : u ∈ R Δ i) :
    σ.xs j * u * (σ.xs j)⁻¹ = u⁻¹ :=
  inverted_of_le_Ns hσ (odd_card_R Δ hσ i)
    (T_le_normalizer_of_C_le hσ (C_le_normalizer_R Δ i)) (R_inf_C Δ hσ i) (R_le_Ns Δ hσ i)
    hji hu

theorem Rs_inverted (hσ : σ.IsValid) {i j : Fin 3} (hji : j ≠ i) {u : G} (hu : u ∈ Rs Δ i) :
    σ.xs j * u * (σ.xs j)⁻¹ = u⁻¹ :=
  inverted_of_le_Ns hσ (odd_card_Rs Δ hσ i)
    (T_le_normalizer_of_C_le hσ (C_le_normalizer_Rs Δ i)) (Rs_inf_C Δ hσ i) (Rs_le_Ns Δ hσ i)
    hji hu

theorem R_subset_comp (hσ : σ.IsValid) {i : Fin 3} {V : Subgroup G} (hV : R Δ i ≤ V) :
    (R Δ i : Set G) ⊆ comp σ V i := fun _ hu =>
  comp_mono hV i (mem_comp_of_le_Ns hσ (odd_card_R Δ hσ i)
    (T_le_normalizer_of_C_le hσ (C_le_normalizer_R Δ i)) (R_inf_C Δ hσ i) (R_le_Ns Δ hσ i) hu)

theorem Rs_subset_comp (hσ : σ.IsValid) {i : Fin 3} {V : Subgroup G} (hV : Rs Δ i ≤ V) :
    (Rs Δ i : Set G) ⊆ comp σ V i := fun _ hu =>
  comp_mono hV i (mem_comp_of_le_Ns hσ (odd_card_Rs Δ hσ i)
    (T_le_normalizer_of_C_le hσ (C_le_normalizer_Rs Δ i)) (Rs_inf_C Δ hσ i)
    (Rs_le_Ns Δ hσ i) hu)

theorem R_centralized (hσ : σ.IsValid) (i : Fin 3) {u : G} (hu : u ∈ R Δ i) :
    σ.xs i * u = u * σ.xs i :=
  (Subgroup.mem_centralizer_singleton_iff.mp (R_le_Ns Δ hσ i hu)).symm

theorem Rs_centralized (hσ : σ.IsValid) (i : Fin 3) {u : G} (hu : u ∈ Rs Δ i) :
    σ.xs i * u = u * σ.xs i :=
  (Subgroup.mem_centralizer_singleton_iff.mp (Rs_le_Ns Δ hσ i hu)).symm

end Subgroups

end CFSG.ABGTheoremB.TotallyInverted.Sec11
