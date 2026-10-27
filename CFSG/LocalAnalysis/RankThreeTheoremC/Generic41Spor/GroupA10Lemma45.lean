module

public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Defs
public import CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor

open CFSG.Open Subgroup

theorem a10l45_pow_mod {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) (n : ℕ) :
    σ ^ n = σ ^ (n % 5) := by
  conv_lhs => rw [← Nat.div_add_mod n 5, pow_add, pow_mul, h5, one_pow, one_mul]

theorem a10l45_orb_inj {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) (hfix : ∀ x, σ x ≠ x)
    (x : Fin 10) {i j : ℕ} (h : (σ ^ i) x = (σ ^ j) x) : i % 5 = j % 5 := by
  have key : ∀ (i d : ℕ), (σ ^ i) x = (σ ^ (i + d)) x → i % 5 = (i + d) % 5 := by
    intro i d h
    have h' : (σ ^ d) ((σ ^ i) x) = (σ ^ i) x := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, add_comm, ← h]
    have := a10_pow_fixed h5 hfix h'
    omega
  rcases le_total i j with hij | hij
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact key i d h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
    exact (key j d h.symm).symm

theorem a10l45_cross {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) {b b' : Fin 10}
    (hb' : ∀ n : ℕ, (σ ^ n) b ≠ b') (i j : ℕ) : (σ ^ i) b ≠ (σ ^ j) b' := by
  intro h
  apply hb' (4 * j + i)
  have h1 : (σ ^ (4 * j)) ((σ ^ i) b) = (σ ^ (4 * j)) ((σ ^ j) b') := by rw [h]
  rw [← Equiv.Perm.mul_apply, ← Equiv.Perm.mul_apply, ← pow_add, ← pow_add] at h1
  have h2 : σ ^ (4 * j + j) = 1 := by
    rw [show 4 * j + j = 5 * j by ring, pow_mul, h5, one_pow]
  rw [h1, h2, Equiv.Perm.one_apply]

theorem a10l45_cover {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) (hfix : ∀ x, σ x ≠ x)
    {b b' : Fin 10} (hb' : ∀ n : ℕ, (σ ^ n) b ≠ b') (x : Fin 10) :
    (∃ n : ℕ, (σ ^ n) b = x) ∨ (∃ n : ℕ, (σ ^ n) b' = x) := by
  classical
  have horb := a10l45_orb_inj h5 hfix
  have hcross := a10l45_cross h5 hb'
  have hAc : ∀ c : Fin 10, ((Finset.range 5).image (fun n : ℕ => (σ ^ n) c)).card = 5 := by
    intro c
    rw [Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    have := horb c hij
    rwa [Nat.mod_eq_of_lt (Finset.mem_range.mp hi), Nat.mod_eq_of_lt (Finset.mem_range.mp hj)]
      at this
  have hdisj : Disjoint ((Finset.range 5).image (fun n : ℕ => (σ ^ n) b))
      ((Finset.range 5).image (fun n : ℕ => (σ ^ n) b')) := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hy'
    exact hcross i j hj.symm
  have hU : ((Finset.range 5).image (fun n : ℕ => (σ ^ n) b)) ∪
      ((Finset.range 5).image (fun n : ℕ => (σ ^ n) b')) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [Finset.card_union_of_disjoint hdisj, hAc b, hAc b']
    simp
  have hx : x ∈ ((Finset.range 5).image (fun n : ℕ => (σ ^ n) b)) ∪
      ((Finset.range 5).image (fun n : ℕ => (σ ^ n) b')) := by
    rw [hU]
    exact Finset.mem_univ x
  rcases Finset.mem_union.mp hx with h | h
  · obtain ⟨n, -, hn⟩ := Finset.mem_image.mp h
    exact Or.inl ⟨n, hn⟩
  · obtain ⟨n, -, hn⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨n, hn⟩

theorem a10l45_exists_col {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) (hfix : ∀ x, σ x ≠ x) :
    ∃ col : Fin 10 → Bool, (∀ x, col (σ x) = col x) ∧
      (∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y) ∧ ∃ b b', col b ≠ col b' := by
  classical
  have hmod := a10l45_pow_mod h5
  obtain ⟨b⟩ : Nonempty (Fin 10) := inferInstance
  obtain ⟨b', hb'⟩ : ∃ b' : Fin 10, ∀ n : ℕ, (σ ^ n) b ≠ b' := by
    have hlt : ((Finset.range 5).image (fun n => (σ ^ n) b)).card <
        (Finset.univ : Finset (Fin 10)).card := by
      calc _ ≤ (Finset.range 5).card := Finset.card_image_le
        _ = 5 := Finset.card_range 5
        _ < 10 := by norm_num
        _ = _ := by simp
    obtain ⟨b', -, hb'⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    refine ⟨b', fun n hn => hb' ?_⟩
    rw [Finset.mem_image]
    exact ⟨n % 5, Finset.mem_range.mpr (Nat.mod_lt n (by norm_num)), by rw [← hmod n]; exact hn⟩
  have hcov := a10l45_cover h5 hfix hb'
  have hrel : ∀ c x y : Fin 10, (∃ n : ℕ, (σ ^ n) c = x) → (∃ n : ℕ, (σ ^ n) c = y) →
      ∃ n : ℕ, (σ ^ n) x = y := by
    rintro c x y ⟨i, rfl⟩ ⟨j, rfl⟩
    refine ⟨4 * i + j, ?_⟩
    rw [← Equiv.Perm.mul_apply, ← pow_add, show 4 * i + j + i = j + 5 * i by ring, pow_add,
      pow_mul, h5, one_pow, mul_one]
  refine ⟨fun x => decide (∃ n : ℕ, (σ ^ n) b = x), ?_, ?_, b, b', ?_⟩
  · intro x
    simp only [decide_eq_decide]
    constructor
    · rintro ⟨n, hn⟩
      refine ⟨4 + n, ?_⟩
      have h1 : (σ ^ 4) (σ x) = x := by
        rw [← Equiv.Perm.mul_apply, ← pow_succ, show 4 + 1 = 5 by norm_num, h5, Equiv.Perm.one_apply]
      rw [pow_add, Equiv.Perm.mul_apply, hn, h1]
    · rintro ⟨n, hn⟩
      exact ⟨n + 1, by rw [pow_succ', Equiv.Perm.mul_apply, hn]⟩
  · intro x y hxy
    simp only [decide_eq_decide] at hxy
    by_cases hx : ∃ n : ℕ, (σ ^ n) b = x
    · exact hrel b x y hx (hxy.mp hx)
    · have hy : ¬ ∃ n : ℕ, (σ ^ n) b = y := fun hy => hx (hxy.mpr hy)
      exact hrel b' x y ((hcov x).resolve_left hx) ((hcov y).resolve_left hy)
  · have h1 : (∃ n : ℕ, (σ ^ n) b = b) := ⟨0, by simp⟩
    have h2 : ¬ ∃ n : ℕ, (σ ^ n) b = b' := fun ⟨n, hn⟩ => hb' n hn
    simp [h1, h2]

theorem a10l45_col_pow {σ : Equiv.Perm (Fin 10)} {col : Fin 10 → Bool}
    (h1 : ∀ x, col (σ x) = col x) (n : ℕ) (x : Fin 10) : col ((σ ^ n) x) = col x := by
  induction n generalizing x with
  | zero => simp
  | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, h1, ih]

theorem a10l45_comm_pow {σ π : Equiv.Perm (Fin 10)} (hc : π * σ = σ * π) (n : ℕ) (x : Fin 10) :
    π ((σ ^ n) x) = (σ ^ n) (π x) := by
  have h : π * σ ^ n = σ ^ n * π := Commute.pow_right hc n
  have := congrArg (fun f : Equiv.Perm (Fin 10) => f x) h
  simpa [Equiv.Perm.mul_apply] using this

theorem a10l45_col_comm {σ π : Equiv.Perm (Fin 10)} {col : Fin 10 → Bool}
    (h1 : ∀ x, col (σ x) = col x) (h2 : ∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y)
    (hc : π * σ = σ * π) {x y : Fin 10} (hxy : col x = col y) : col (π x) = col (π y) := by
  obtain ⟨n, rfl⟩ := h2 x y hxy
  rw [a10l45_comm_pow hc, a10l45_col_pow h1]

theorem a10l45_col_inj {σ π : Equiv.Perm (Fin 10)} {col : Fin 10 → Bool}
    (h1 : ∀ x, col (σ x) = col x) (h2 : ∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y)
    (h3 : ∃ x y, col x ≠ col y) (hc : π * σ = σ * π) {x y : Fin 10} (hxy : col x ≠ col y) :
    col (π x) ≠ col (π y) := by
  intro h
  obtain ⟨p, q, hpq⟩ := h3
  have hz : ∀ z, col (π z) = col (π x) := by
    intro z
    by_cases hzx : col z = col x
    · exact a10l45_col_comm h1 h2 hc hzx
    · have hzy : col z = col y := by
        revert hzx hxy; cases col z <;> cases col x <;> cases col y <;> simp
      rw [a10l45_col_comm h1 h2 hc hzy, ← h]
  apply hpq
  have e1 := hz (π.symm p)
  have e2 := hz (π.symm q)
  simp only [Equiv.apply_symm_apply] at e1 e2
  rw [e1, e2]

theorem a10l45_col_dichotomy {σ π : Equiv.Perm (Fin 10)} {col : Fin 10 → Bool}
    (h1 : ∀ x, col (σ x) = col x) (h2 : ∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y)
    (h3 : ∃ x y, col x ≠ col y) (hc : π * σ = σ * π) :
    (∀ x, col (π x) = col x) ∨ (∀ x, col (π x) = !col x) := by
  obtain ⟨p, q, hpq⟩ := h3
  have h3' : ∃ x y, col x ≠ col y := ⟨p, q, hpq⟩
  have bool1 : ∀ a b c : Bool, a ≠ b → c ≠ b → c = a := by decide
  have bool2 : ∀ a b : Bool, a ≠ b → a = !b := by decide
  have bool3 : ∀ a b c d : Bool, a ≠ b → c ≠ d → d ≠ b → c = !a := by decide
  by_cases hp : col (π p) = col p
  · left
    intro x
    by_cases hx : col x = col p
    · rw [a10l45_col_comm h1 h2 hc hx, hp, hx]
    · have hx' : col (π x) ≠ col (π p) := a10l45_col_inj h1 h2 h3' hc hx
      rw [hp] at hx'
      exact bool1 _ _ _ hx hx'
  · right
    intro x
    by_cases hx : col x = col p
    · rw [a10l45_col_comm h1 h2 hc hx, hx]
      exact bool2 _ _ hp
    · exact bool3 _ _ _ _ hx (a10l45_col_inj h1 h2 h3' hc hx) hp

theorem a10l45_col_pres {σ π : Equiv.Perm (Fin 10)} {col : Fin 10 → Bool}
    (h1 : ∀ x, col (σ x) = col x) (h2 : ∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y)
    (h3 : ∃ x y, col x ≠ col y) (hc : π * σ = σ * π) (h5 : π ^ 5 = 1) :
    ∀ x, col (π x) = col x := by
  rcases a10l45_col_dichotomy h1 h2 h3 hc with h | h
  · exact h
  · exfalso
    obtain ⟨p, -, -⟩ := h3
    have e : (π ^ 5) p = π (π (π (π (π p)))) := by
      simp [pow_succ, Equiv.Perm.mul_apply]
    have hh : col p = !col p := by
      calc col p = col ((π ^ 5) p) := by rw [h5]; rfl
        _ = col (π (π (π (π (π p))))) := by rw [e]
        _ = !col p := by simp only [h, Bool.not_not]
    revert hh; cases col p <;> simp

theorem a10l45_cycle {σ π : Equiv.Perm (Fin 10)} {col : Fin 10 → Bool} (h5 : σ ^ 5 = 1)
    (h2 : ∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y)
    (hc : π * σ = σ * π) (hπ : ∀ x, col (π x) = col x) {x₀ : Fin 10} (hx₀ : π x₀ ≠ x₀)
    {y : Fin 10} (hy : col y = col x₀) : ∃ k : ℕ, (π ^ k) x₀ = y := by
  obtain ⟨n, hn⟩ := h2 x₀ (π x₀) (hπ x₀).symm
  have hpow : ∀ k : ℕ, (π ^ k) x₀ = (σ ^ (n * k)) x₀ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, ih, a10l45_comm_pow hc, ← hn,
        ← Equiv.Perm.mul_apply, ← pow_add, show n * (k + 1) = n * k + n by ring]
  obtain ⟨m, hm⟩ := h2 x₀ y hy.symm
  have hn5 : ¬ 5 ∣ n := by
    intro hdvd
    apply hx₀
    rw [← hn, a10l45_pow_mod h5 n, Nat.mod_eq_zero_of_dvd hdvd]
    simp
  have hcop : Nat.Coprime n 5 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_five).mpr hn5)
  obtain ⟨a, -, ha⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by norm_num)
  refine ⟨a * m, ?_⟩
  have hmod : (n * (a * m)) % 5 = m % 5 := by
    rw [← mul_assoc, Nat.mul_mod, ha]
    simp
  rw [hpow, ← hm, a10l45_pow_mod h5 (n * (a * m)), hmod, ← a10l45_pow_mod h5 m]

theorem a10l45_conj_pres {σ γ β β' : Equiv.Perm (Fin 10)} {col : Fin 10 → Bool}
    (h5 : σ ^ 5 = 1) (h1 : ∀ x, col (σ x) = col x)
    (h2 : ∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y) (h3 : ∃ x y, col x ≠ col y)
    (hβ : β * σ = σ * β) (hβ5 : β ^ 5 = 1) (hβ' : β' * σ = σ * β') (hβ'5 : β' ^ 5 = 1)
    (hγ : γ * β * γ⁻¹ = β') (hβ1 : β ≠ 1) :
    (∀ x, col (γ x) = col x) ∨ (∀ x, col (γ x) = !col x) := by
  have hcβ := a10l45_col_pres h1 h2 h3 hβ hβ5
  have hcβ' := a10l45_col_pres h1 h2 h3 hβ' hβ'5
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, β x₀ ≠ x₀ := by
    by_contra hcon
    push_neg at hcon
    exact hβ1 (Equiv.ext hcon)
  have hpowγ : ∀ (k : ℕ) (x : Fin 10), γ ((β ^ k) x) = (β' ^ k) (γ x) := by
    intro k x
    rw [← hγ, conj_pow]
    simp [Equiv.Perm.mul_apply]
  have hx₀' : β' (γ x₀) ≠ γ x₀ := by
    intro h
    apply hx₀
    have h' := hpowγ 1 x₀
    simp only [pow_one] at h'
    rw [h] at h'
    exact γ.injective h'
  have key : ∀ y, col y = col x₀ ↔ col (γ y) = col (γ x₀) := by
    intro y
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := a10l45_cycle h5 h2 hβ hcβ hx₀ hy
      rw [← hk, hpowγ, a10l45_col_pow hcβ']
    · intro hy
      obtain ⟨k, hk⟩ := a10l45_cycle h5 h2 hβ' hcβ' hx₀' hy
      rw [← hpowγ] at hk
      rw [← γ.injective hk, a10l45_col_pow hcβ]
  have bool4 : ∀ a a₀ c c₀ : Bool, (a = a₀ ↔ c = c₀) →
      (c₀ = a₀ → c = a) ∧ (c₀ ≠ a₀ → c = !a) := by decide
  by_cases hs : col (γ x₀) = col x₀
  · left
    intro x
    exact (bool4 _ _ _ _ (key x)).1 hs
  · right
    intro x
    exact (bool4 _ _ _ _ (key x)).2 hs

@[expose] def a10l45_stab (col : Fin 10 → Bool) : Subgroup (Equiv.Perm (Fin 10)) where
  carrier := {π | (∀ x, col (π x) = col x) ∨ (∀ x, col (π x) = !col x)}
  mul_mem' := by
    rintro π π' (h | h) (h' | h')
    · left; intro x; rw [Equiv.Perm.mul_apply, h, h']
    · right; intro x; rw [Equiv.Perm.mul_apply, h, h']
    · right; intro x; rw [Equiv.Perm.mul_apply, h, h']
    · left; intro x; rw [Equiv.Perm.mul_apply, h, h', Bool.not_not]
  one_mem' := Or.inl (fun x => rfl)
  inv_mem' := by
    rintro π (h | h)
    · left; intro x
      have := h (π⁻¹ x)
      rw [show π (π⁻¹ x) = x by simp] at this
      exact this.symm
    · right; intro x
      have := h (π⁻¹ x)
      rw [show π (π⁻¹ x) = x by simp] at this
      rw [this]
      simp

theorem a10l45_mem_stab {col : Fin 10 → Bool} {π : Equiv.Perm (Fin 10)} :
    π ∈ a10l45_stab col ↔ (∀ x, col (π x) = col x) ∨ (∀ x, col (π x) = !col x) := Iff.rfl

theorem a10l45_core {σ : Equiv.Perm (Fin 10)} (h5 : σ ^ 5 = 1) (hfix : ∀ x, σ x ≠ x) :
    ∃ (col : Fin 10 → Bool) (V : Subgroup (Equiv.Perm (Fin 10))),
      (∀ x, col (σ x) = col x) ∧ (∀ x y, col x = col y → ∃ n : ℕ, (σ ^ n) x = y) ∧
      (∃ x y, col x ≠ col y) ∧ (∀ g ∈ V, g ^ 2 = 1) ∧ (∀ g ∈ V, σ * g * σ⁻¹ ∈ V) ∧
      ∃ v ∈ V, Equiv.Perm.sign v = 1 ∧ v ∉ a10l45_stab col := by
  have hmod := a10l45_pow_mod h5
  have horb := a10l45_orb_inj h5 hfix
  obtain ⟨col, h1, h2, b, b', hbb'⟩ := a10l45_exists_col h5 hfix
  have hb' : ∀ n : ℕ, (σ ^ n) b ≠ b' := by
    intro n hn
    apply hbb'
    rw [← hn, a10l45_col_pow h1]
  have hcross := a10l45_cross h5 hb'
  have hne : ∀ i j : ℕ, i % 5 ≠ j % 5 → (σ ^ i) b ≠ (σ ^ j) b := fun i j hij h => hij (horb b h)
  obtain ⟨τ, hτ⟩ : ∃ τ : ℕ → Equiv.Perm (Fin 10),
      ∀ k, τ k = Equiv.swap ((σ ^ k) b) ((σ ^ k) b') := ⟨_, fun k => rfl⟩
  have hτσ : ∀ k, σ * τ k * σ⁻¹ = τ (k + 1) := by
    intro k
    rw [hτ, hτ, ← Equiv.swap_apply_apply]
    simp [pow_succ']
  have hτper : ∀ k, τ k = τ (k % 5) := by
    intro k
    rw [hτ, hτ, hmod k]
  have hτsq : ∀ k, τ k ^ 2 = 1 := by
    intro k
    rw [hτ, sq, Equiv.swap_mul_self]
  have hcomm : ∀ i j, Commute (τ i) (τ j) := by
    intro i j
    by_cases hij : i % 5 = j % 5
    · rw [hτper i, hτper j, hij]
    · have hd : Equiv.Perm.Disjoint (τ i) (τ j) := by
        intro x
        by_cases hx : x = (σ ^ i) b ∨ x = (σ ^ i) b'
        · right
          rw [hτ j]
          apply Equiv.swap_apply_of_ne_of_ne
          · rcases hx with rfl | rfl
            · exact fun h => hij (horb b h)
            · exact fun h => hcross j i h.symm
          · rcases hx with rfl | rfl
            · exact fun h => hcross i j h
            · exact fun h => hij (horb b' h)
        · left
          rw [hτ i]
          apply Equiv.swap_apply_of_ne_of_ne
          · exact fun h => hx (Or.inl h)
          · exact fun h => hx (Or.inr h)
      exact hd.commute
  let S : Set (Equiv.Perm (Fin 10)) := Set.range fun k : ℕ => τ k * τ (k + 1)
  have hS_comm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨k, rfl⟩ _ ⟨l, rfl⟩
    exact (((hcomm k l).mul_right (hcomm k (l + 1))).mul_left
      ((hcomm (k + 1) l).mul_right (hcomm (k + 1) (l + 1)))).eq
  have hS_sq : ∀ x ∈ S, x ^ 2 = 1 := by
    rintro _ ⟨k, rfl⟩
    show (τ k * τ (k + 1)) ^ 2 = 1
    rw [(hcomm k (k + 1)).mul_pow, hτsq, hτsq, one_mul]
  have e0 : τ 0 b = b' := by rw [hτ]; simp
  have e1 : τ 1 b = b := by
    rw [hτ]
    exact Equiv.swap_apply_of_ne_of_ne (by simpa using hne 1 0 (by norm_num) |>.symm)
      (hcross 0 1)
  have f1 : τ 1 ((σ ^ 2) b) = (σ ^ 2) b := by
    rw [hτ]
    exact Equiv.swap_apply_of_ne_of_ne (hne 2 1 (by norm_num)) (hcross 2 1)
  have f0 : τ 0 ((σ ^ 2) b) = (σ ^ 2) b := by
    rw [hτ]
    exact Equiv.swap_apply_of_ne_of_ne (hne 2 0 (by norm_num)) (hcross 2 0)
  refine ⟨col, Subgroup.closure S, h1, h2, ⟨b, b', hbb'⟩,
    a10_sq_eq_one_of_closure_comm hS_comm hS_sq, ?_, τ 0 * τ 1,
    Subgroup.subset_closure ⟨0, rfl⟩, ?_, ?_⟩
  · intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨k, rfl⟩ := hx
      apply Subgroup.subset_closure
      refine ⟨k + 1, ?_⟩
      have h : σ * (τ k * τ (k + 1)) * σ⁻¹ = (σ * τ k * σ⁻¹) * (σ * τ (k + 1) * σ⁻¹) := by
        group
      show τ (k + 1) * τ (k + 1 + 1) = σ * (τ k * τ (k + 1)) * σ⁻¹
      rw [h, hτσ k, hτσ (k + 1)]
    | one => simp
    | mul x y hx hy ihx ihy =>
      have : σ * (x * y) * σ⁻¹ = (σ * x * σ⁻¹) * (σ * y * σ⁻¹) := by group
      rw [this]
      exact mul_mem ihx ihy
    | inv x hx ihx =>
      have : σ * x⁻¹ * σ⁻¹ = (σ * x * σ⁻¹)⁻¹ := by group
      rw [this]
      exact inv_mem ihx
  · rw [Equiv.Perm.sign_mul, hτ 0, hτ 1, Equiv.Perm.sign_swap (hcross 0 0),
      Equiv.Perm.sign_swap (hcross 1 1)]
    rfl
  · intro hv
    have hvb : (τ 0 * τ 1) b = b' := by rw [Equiv.Perm.mul_apply, e1, e0]
    have hvc : (τ 0 * τ 1) ((σ ^ 2) b) = (σ ^ 2) b := by rw [Equiv.Perm.mul_apply, f1, f0]
    rcases a10l45_mem_stab.mp hv with h | h
    · apply hbb'
      rw [← h b, hvb]
    · have h' := h ((σ ^ 2) b)
      rw [hvc] at h'
      revert h'
      cases col ((σ ^ 2) b) <;> simp

@[expose] def a10l45_emb {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 10)) :
    K →* Equiv.Perm (Fin 10) :=
  (alternatingGroup (Fin 10)).subtype.comp e.toMonoidHom

theorem a10l45_emb_apply {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 10)) (g : K) :
    a10l45_emb e g = ((e g : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)) := rfl

theorem a10l45_emb_injective {K : Type} [Group K] (e : K ≃* alternatingGroup (Fin 10)) :
    Function.Injective (a10l45_emb e) :=
  Subtype.val_injective.comp e.injective

theorem a10l45_sylow_perm {K : Type} [Group K] [Finite K] (hK : IsA10Type 5 K) (S : Sylow 5 K)
    (e : K ≃* alternatingGroup (Fin 10)) {u : K} (hu : u ∈ (S : Subgroup K)) {s : K}
    (hs : s ∈ (S : Subgroup K)) :
    a10l45_emb e s * a10l45_emb e u = a10l45_emb e u * a10l45_emb e s ∧
      (a10l45_emb e s) ^ 5 = 1 := by
  obtain ⟨⟨hcomm, hexp⟩, -⟩ := a10_sylow K hK S
  refine ⟨?_, ?_⟩
  · have h : s * u = u * s :=
      congrArg Subtype.val (hcomm.is_comm.comm (⟨s, hs⟩ : (S : Subgroup K)) ⟨u, hu⟩)
    rw [← map_mul, ← map_mul, h]
  · rw [← map_pow, hexp s hs, map_one]

theorem a10l45_gamma_le {K : Type} [Group K] [Finite K] (hK : IsA10Type 5 K) (S : Sylow 5 K)
    (e : K ≃* alternatingGroup (Fin 10)) {u : K} (hu : u ∈ (S : Subgroup K))
    {col : Fin 10 → Bool} (h1 : ∀ x, col (a10l45_emb e u x) = col x)
    (h2 : ∀ x y, col x = col y → ∃ n : ℕ, ((a10l45_emb e u) ^ n) x = y)
    (h3 : ∃ x y, col x ≠ col y) :
    A10Gamma K (S : Subgroup K) ≤ (a10l45_stab col).comap (a10l45_emb e) := by
  unfold A10Gamma
  rw [Subgroup.closure_le]
  rintro g ⟨B, hBS, hB1, hgB⟩
  obtain ⟨⟨b, hb⟩, hb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hB1
  have hgb : g * b * g⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp hgB b).mp hb
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  obtain ⟨hc1, hp1⟩ := a10l45_sylow_perm hK S e hu (hBS hb)
  obtain ⟨hc2, hp2⟩ := a10l45_sylow_perm hK S e hu (hBS hgb)
  obtain ⟨-, hpu⟩ := a10l45_sylow_perm hK S e hu hu
  have h5 : (a10l45_emb e u) ^ 5 = 1 := hpu
  have hconj : a10l45_emb e g * a10l45_emb e b * (a10l45_emb e g)⁻¹ =
      a10l45_emb e (g * b * g⁻¹) := by simp [map_mul, map_inv]
  have hβ1 : a10l45_emb e b ≠ 1 := by
    intro h
    apply hb1'
    apply a10l45_emb_injective e
    rw [h, map_one]
  have := a10l45_conj_pres h5 h1 h2 h3 hc1 hp1 hc2 hp2 hconj hβ1
  exact a10l45_mem_stab.mpr this

theorem a10_lemma45Gamma_holds :
    ∀ (K : Type) [Group K] [Finite K], IsA10Type 5 K → ∀ (S : Sylow 5 K) (u : K),
      u ∈ (S : Subgroup K) →
      (∃ e : K ≃* alternatingGroup (Fin 10),
        ((e u : alternatingGroup (Fin 10)) : Equiv.Perm (Fin 10)).cycleType = {5, 5}) →
      ∃ V : Subgroup K, IsPGroup 2 V ∧ u ∈ Subgroup.normalizer (V : Set K) ∧
        ¬ V ≤ A10Gamma K (S : Subgroup K) := by
  intro K _ _ hK S u huS hct
  obtain ⟨e, he⟩ := hct
  obtain ⟨h5, hfix⟩ := a10_of_cycleType he
  obtain ⟨col, V, h1, h2, h3, hV2, hVn, v, hvV, hvsign, hvstab⟩ := a10l45_core h5 hfix
  refine ⟨V.comap (a10l45_emb e), ?_, ?_, ?_⟩
  · intro g
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply a10l45_emb_injective e
    have h := hV2 _ g.2
    simpa [map_pow] using h
  · apply Subgroup.mem_normalizer_fintype
    intro n hn
    show a10l45_emb e (u * n * u⁻¹) ∈ V
    rw [map_mul, map_mul, map_inv]
    exact hVn _ hn
  · intro hle
    have hvA : v ∈ alternatingGroup (Fin 10) := Equiv.Perm.mem_alternatingGroup.mpr hvsign
    have hk : a10l45_emb e (e.symm ⟨v, hvA⟩) = v := by simp [a10l45_emb_apply]
    have hkV : e.symm ⟨v, hvA⟩ ∈ V.comap (a10l45_emb e) := by
      rw [Subgroup.mem_comap, hk]
      exact hvV
    have := a10l45_gamma_le hK S e huS h1 h2 h3 (hle hkV)
    rw [Subgroup.mem_comap, hk] at this
    exact hvstab this

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor
