module

public import CFSG.RankThree.PartOne.KLC.ThreePoint
public import Mathlib.GroupTheory.OrderOfElement

public section

namespace CFSG.AGLEmbedding.TwoGenInner

open MulAction
open scoped commutatorElement

section Pigeonhole

variable {A : Type*} [Group A] {X : Type*} [MulAction A X]

theorem coprime_pow_of_lt_prime {p n : ℕ} (hp : p.Prime) (hn0 : 0 < n) (hnp : n < p) (k : ℕ) :
    Nat.Coprime n (p ^ k) :=
  Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd hp).2
    (fun hd => absurd (Nat.le_of_dvd hn0 hd) (not_le.2 hnp))).symm

theorem smul_eq_of_pow_fixes_gen {S : Finset X} {r : ℕ} (hS : S.card ≤ r) {q : ℕ}
    (hq : ∀ n : ℕ, 0 < n → n ≤ r → Nat.Coprime n q) {α : A} {x : X}
    (hx : ∀ i : ℕ, α ^ i • x ∈ S) (hqx : ∀ i : ℕ, α ^ q • (α ^ i • x) = α ^ i • x) :
    α • x = x := by
  classical
  obtain ⟨i, hi, j, hj, hij, hxij⟩ := Finset.exists_ne_map_eq_of_card_lt_of_maps_to
    (s := Finset.range (r + 1)) (t := S) (f := fun k : ℕ => α ^ k • x)
    (by simpa using lt_of_le_of_lt hS (Nat.lt_succ_self r)) (fun k _ => by simpa using hx k)
  have key : ∀ i j : ℕ, i < j → j < r + 1 → α ^ i • x = α ^ j • x → α • x = x := by
    intro i j hlt hjr h
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    have hm : α ^ (m + 1) • (α ^ i • x) = α ^ i • x := by
      rw [smul_smul, ← pow_add]
      have : m + 1 + i = i + m + 1 := by omega
      rw [this]
      exact h.symm
    have hcop : Nat.Coprime (m + 1) q := hq (m + 1) (by omega) (by omega)
    obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * ((m + 1 : ℕ) : ℤ) + v * (q : ℤ) = 1 := by
      have hg : Int.gcd ((m + 1 : ℕ) : ℤ) (q : ℤ) = 1 := by
        rw [Int.gcd_natCast_natCast]
        exact hcop
      have h := Int.gcd_eq_gcd_ab ((m + 1 : ℕ) : ℤ) (q : ℤ)
      rw [hg] at h
      exact ⟨Int.gcdA _ _, Int.gcdB _ _, by push_cast at h ⊢; linarith⟩
    have hstab : α ∈ stabilizer A (α ^ i • x) := by
      have h1 : α ^ (m + 1) ∈ stabilizer A (α ^ i • x) := hm
      have h2 : α ^ q ∈ stabilizer A (α ^ i • x) := hqx i
      have : α = (α ^ (m + 1)) ^ u * (α ^ q) ^ v := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
        have : ((m + 1 : ℕ) : ℤ) * u + (q : ℤ) * v = 1 := by linarith
        rw [this, zpow_one]
      have hmem : (α ^ (m + 1)) ^ u * (α ^ q) ^ v ∈ stabilizer A (α ^ i • x) :=
        (stabilizer A (α ^ i • x)).mul_mem ((stabilizer A (α ^ i • x)).zpow_mem h1 u)
          ((stabilizer A (α ^ i • x)).zpow_mem h2 v)
      rwa [← this] at hmem
    have hfix : α • (α ^ i • x) = α ^ i • x := hstab
    have h3 : α ^ i • (α • x) = α ^ i • x :=
      calc α ^ i • (α • x) = (α ^ i * α) • x := smul_smul _ _ _
        _ = (α * α ^ i) • x := by rw [← pow_succ, pow_succ']
        _ = α • (α ^ i • x) := (smul_smul _ _ _).symm
        _ = α ^ i • x := hfix
    exact smul_left_cancel (α ^ i) h3
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h (by simpa using hj) hxij
  · exact key j i h (by simpa using hi) hxij.symm

end Pigeonhole

section ThreePoint

open CFSG.RankThree.PartOne.KLC

variable {A : Type*} [Group A] {X : Type*} [MulAction A X]

theorem commutator_mem_of_three_point_orbit_gen (N : Subgroup A) [N.Normal] {F y z : X}
    (hO : ∀ a : A, a • F = F ∨ a • F = y ∨ a • F = z)
    {κ : A} (hκF : κ • F = F) (hκy : κ • y = z) (hκz : κ • z = y) (hyz : y ≠ z)
    (hN : ∀ n ∈ N, n • F = F)
    {p : ℕ} (hE : ∀ a b : A, a • F = F → b • F = F → (∃ k : ℕ, b ^ p ^ k ∈ N) → ⁅a, b⁆ ∈ N)
    (hp : p.Prime) (hp5 : 5 ≤ p) {α : A} {k : ℕ} (hα : α ^ p ^ k ∈ N) (γ : A) : ⁅γ, α⁆ ∈ N := by
  classical
  have hfix : ∀ a : A, α • (a • F) = a • F := by
    intro a
    have hcard : ({F, y, z} : Finset X).card ≤ 3 := Finset.card_le_three
    refine smul_eq_of_pow_fixes_gen (S := {F, y, z}) (r := 3) hcard
      (fun n hn0 hn3 => coprime_pow_of_lt_prime hp hn0 (by omega) k) (fun i => ?_) (fun i => ?_)
    · rw [smul_smul]
      have := hO (α ^ i * a)
      simpa [Finset.mem_insert, Finset.mem_singleton] using this
    · simpa [mul_smul] using smul_orbit_of_normal hN hα (α ^ i * a)
  have hstab : ∀ a γ : A, γ • (a • F) = a • F → ⁅γ, α⁆ ∈ N := by
    intro a γ hγ
    have h1 : (a⁻¹ * γ * a) • F = F := by
      calc (a⁻¹ * γ * a) • F = a⁻¹ • (γ • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hγ]
        _ = F := inv_smul_smul a F
    have h2 : (a⁻¹ * α * a) • F = F := by
      calc (a⁻¹ * α * a) • F = a⁻¹ • (α • (a • F)) := by simp [mul_smul]
        _ = a⁻¹ • (a • F) := by rw [hfix a]
        _ = F := inv_smul_smul a F
    have h2' : (a⁻¹ * α * a) ^ p ^ k ∈ N := by
      have e : (a⁻¹ * α * a) ^ p ^ k = a⁻¹ * α ^ p ^ k * a := by
        have := conj_pow (a := a⁻¹) (b := α) (i := p ^ k)
        simpa using this
      rw [e]
      have := Subgroup.Normal.conj_mem ‹N.Normal› _ hα a⁻¹
      simpa using this
    have h3 := hE _ _ h1 h2 ⟨k, h2'⟩
    have e : ⁅a⁻¹ * γ * a, a⁻¹ * α * a⁆ = a⁻¹ * ⁅γ, α⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e] at h3
    have h4 := Subgroup.Normal.conj_mem ‹N.Normal› _ h3 a
    have e2 : a * (a⁻¹ * ⁅γ, α⁆ * a) * a⁻¹ = ⁅γ, α⁆ := by group
    rwa [e2] at h4
  set S := commModSubgroup N α with hS
  have hSstab : ∀ a γ : A, γ • (a • F) = a • F → γ ∈ S := fun a γ h => hstab a γ h
  have hFy : F ≠ y := by
    intro h
    apply hyz
    have h1 : κ • y = y := by rw [← h, hκF]
    rw [← h1, hκy]
  have hFz : F ≠ z := by
    intro h
    apply hyz
    have h1 : κ • z = z := by rw [← h, hκF]
    rw [← hκz, h1]
  have hz : ∀ γ₁ : A, γ₁ • F = y → ∃ s ∈ S, s • F = z := by
    intro γ₁ hγ₁
    have hκ₁ : (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • F := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • F) = γ₁ • (κ • F) := by simp [mul_smul]
        _ = γ₁ • F := by rw [hκF]
    refine ⟨γ₁ * κ * γ₁⁻¹, hSstab γ₁ _ hκ₁, ?_⟩
    have hu : γ₁ • y = F ∨ γ₁ • y = y ∨ γ₁ • y = z := by
      have := hO (γ₁ * γ₁)
      rwa [mul_smul, hγ₁] at this
    have hv : γ₁ • z = F ∨ γ₁ • z = y ∨ γ₁ • z = z := by
      have := hO (γ₁ * (κ * γ₁))
      rwa [mul_smul, mul_smul, hγ₁, hκy] at this
    have hu_y : γ₁ • y ≠ y := fun h =>
      hFy (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have hv_y : γ₁ • z ≠ y := fun h =>
      hFz (smul_left_cancel γ₁ (h.trans hγ₁.symm)).symm
    have huv : γ₁ • y ≠ γ₁ • z := fun h => hyz (smul_left_cancel γ₁ h)
    have hκu : (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • z := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) = γ₁ • (κ • y) := by simp [mul_smul]
        _ = γ₁ • z := by rw [hκy]
    have hκv : (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • y := by
      calc (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) = γ₁ • (κ • z) := by simp [mul_smul]
        _ = γ₁ • y := by rw [hκz]
    rcases hu with hu | hu | hu
    · have hvz : γ₁ • z = z := by
        rcases hv with hv | hv | hv
        · exact absurd (hu.trans hv.symm) huv
        · exact absurd hv hv_y
        · exact hv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • y) := by rw [hu]
        _ = γ₁ • z := hκu
        _ = z := hvz
    · exact absurd hu hu_y
    · have hvF : γ₁ • z = F := by
        rcases hv with hv | hv | hv
        · exact hv
        · exact absurd hv hv_y
        · exact absurd (hu.trans hv.symm) huv
      calc (γ₁ * κ * γ₁⁻¹) • F = (γ₁ * κ * γ₁⁻¹) • (γ₁ • z) := by rw [hvF]
        _ = γ₁ • y := hκv
        _ = z := hu
  have hκS : κ ∈ S := hSstab 1 κ (by simpa using hκF)
  rcases hO γ with h | h | h
  · exact hSstab 1 γ (by simpa using h)
  · obtain ⟨s, hs, hsF⟩ := hz γ h
    have hksF : (κ * s) • F = y := by rw [mul_smul, hsF, hκz]
    have h1 : ((κ * s)⁻¹ * γ) • F = F := by
      calc ((κ * s)⁻¹ * γ) • F = (κ * s)⁻¹ • (γ • F) := mul_smul _ _ _
        _ = (κ * s)⁻¹ • ((κ * s) • F) := by rw [h, hksF]
        _ = F := inv_smul_smul _ _
    have h2 : (κ * s)⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem (S.mul_mem hκS hs) h2
    have e3 : κ * s * ((κ * s)⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3
  · obtain ⟨s, hs, hsF⟩ := hz (κ * γ) (by rw [mul_smul, h, hκz])
    have h1 : (s⁻¹ * γ) • F = F := by
      calc (s⁻¹ * γ) • F = s⁻¹ • (γ • F) := mul_smul _ _ _
        _ = s⁻¹ • (s • F) := by rw [h, hsF]
        _ = F := inv_smul_smul _ _
    have h2 : s⁻¹ * γ ∈ S := hSstab 1 _ (by simpa using h1)
    have h3 := S.mul_mem hs h2
    have e3 : s * (s⁻¹ * γ) = γ := by group
    rw [e3] at h3
    exact h3

end ThreePoint

section Layers

variable {G : Type*} [Group G]

theorem central_of_layers [Finite G] {K D E : Subgroup G}
    (hKE : ∀ e ∈ E, ∀ k ∈ K, e * k * e⁻¹ ∈ K) (hDE' : ∀ e ∈ E, ∀ d ∈ D, e * d * e⁻¹ ∈ D)
    (hK4 : Nat.card K ≤ 4) (hD2 : K.relIndex D ≤ 2) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hDp : ¬ p ∣ Nat.card D) {u : G} (hcyc : ∀ e ∈ E, ∃ j : ℤ, u ^ j * e ∈ D)
    {a b : G} (ha : a ∈ E) (hb : b ∈ E) {m : ℕ} (hbm : b ^ p ^ m = 1) : ⁅a, b⁆ = 1 := by
  classical
  have hA : ∀ k ∈ K, b * k * b⁻¹ = k := by
    intro k hk
    have : Fintype G := Fintype.ofFinite G
    let S : Finset G := Finset.univ.filter (· ∈ K)
    have hS : S.card = Nat.card K := by
      rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    have hconj : ∀ i : ℕ, (MulAut.conj b ^ i) • k = b ^ i * k * (b ^ i)⁻¹ := by
      intro i
      rw [← map_pow, MulAut.smul_def, MulAut.conj_apply]
    have := smul_eq_of_pow_fixes_gen (A := MulAut G) (S := S) (r := 4) (q := p ^ m)
      (hS.le.trans hK4) (fun n hn0 hn4 => coprime_pow_of_lt_prime hp hn0 (by omega) m)
      (α := MulAut.conj b) (x := k)
      (fun i => by
        rw [hconj]
        simpa [S] using hKE _ (E.pow_mem hb i) k hk)
      (fun i => by
        rw [← map_pow, hbm]
        simp)
    simpa [MulAut.smul_def, MulAut.conj_apply] using this
  have hB : ∀ d ∈ D, b * d * b⁻¹ * d⁻¹ ∈ K := by
    intro d hd
    by_cases hdK : d ∈ K
    · exact K.mul_mem (hKE b hb d hdK) (K.inv_mem hdK)
    · have hdD : b * d * b⁻¹ ∈ D := hDE' b hb d hd
      have hdK' : b * d * b⁻¹ ∉ K := fun h => hdK (by
        have h1 := hKE b⁻¹ (E.inv_mem hb) _ h
        have e : b⁻¹ * (b * d * b⁻¹) * b⁻¹⁻¹ = d := by group
        rwa [e] at h1)
      have hne1 : K.relIndex D ≠ 1 := fun h1 => hdK (Subgroup.relIndex_eq_one.1 h1 hd)
      have hne0 : K.relIndex D ≠ 0 := Subgroup.index_ne_zero_of_finite
      have h2 : (K.subgroupOf D).index = 2 := by
        have : K.relIndex D = 2 := by omega
        exact this
      have key := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨b * d * b⁻¹, hdD⟩ : D))
        (b := (⟨d⁻¹, D.inv_mem hd⟩ : D))).2 (by
          constructor
          · intro h; exact absurd (Subgroup.mem_subgroupOf.1 h) hdK'
          · intro h; exact absurd (by simpa using Subgroup.mem_subgroupOf.1 h) hdK)
      exact Subgroup.mem_subgroupOf.1 key
  have hC : ∀ d ∈ D, b * d * b⁻¹ = d := by
    intro d hd
    obtain ⟨c, hc⟩ : ∃ c, c = b * d * b⁻¹ * d⁻¹ := ⟨_, rfl⟩
    have hcK : c ∈ K := hc ▸ hB d hd
    have hbc : b * c * b⁻¹ = c := hA c hcK
    have hbd : b * d * b⁻¹ = c * d := by rw [hc]; group
    have hpow : ∀ j : ℕ, b ^ j * d * (b ^ j)⁻¹ = c ^ j * d := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc b ^ (j + 1) * d * (b ^ (j + 1))⁻¹
            = b * (b ^ j * d * (b ^ j)⁻¹) * b⁻¹ := by group
          _ = b * (c ^ j * d) * b⁻¹ := by rw [ih]
          _ = (b * c ^ j * b⁻¹) * (b * d * b⁻¹) := by group
          _ = c ^ j * (c * d) := by rw [← conj_pow, hbc, hbd]
          _ = c ^ (j + 1) * d := by group
    have h1 : c ^ p ^ m * d = d := by
      have := hpow (p ^ m)
      rw [hbm] at this
      simpa using this.symm
    have h2 : c ^ p ^ m = 1 := by simpa using h1
    have hord : orderOf c ∣ Nat.card K := Subgroup.orderOf_dvd_natCard K hcK
    have hle : orderOf c ≤ 4 := (Nat.le_of_dvd Nat.card_pos hord).trans hK4
    have hcop : Nat.Coprime (orderOf c) (p ^ m) :=
      coprime_pow_of_lt_prime hp (orderOf_pos c) (by omega) m
    have h3 : orderOf c = 1 := Nat.Coprime.eq_one_of_dvd hcop (orderOf_dvd_of_pow_eq_one h2)
    have hc1 : c = 1 := orderOf_eq_one_iff.1 h3
    rw [hbd, hc1, one_mul]
  have hCD : ∀ d ∈ D, Commute b d := by
    intro d hd
    show b * d = d * b
    calc b * d = b * d * b⁻¹ * b := by group
      _ = d * b := by rw [hC d hd]
  obtain ⟨j, hj⟩ := hcyc b hb
  obtain ⟨d₀, hd₀⟩ : ∃ d₀, d₀ = u ^ j * b := ⟨_, rfl⟩
  have hd₀D : d₀ ∈ D := hd₀ ▸ hj
  have hw : u ^ j = d₀ * b⁻¹ := by rw [hd₀]; group
  have hn : orderOf d₀ ∣ Nat.card D := Subgroup.orderOf_dvd_natCard D hd₀D
  have hcop : Nat.Coprime (orderOf d₀) (orderOf b⁻¹) := by
    have h1 : ¬ p ∣ orderOf d₀ := fun hdv => hDp (hdv.trans hn)
    have h2 : Nat.Coprime (p ^ m) (orderOf d₀) :=
      Nat.Coprime.pow_left m ((Nat.Prime.coprime_iff_not_dvd hp).2 h1)
    have h3 : orderOf b⁻¹ ∣ p ^ m := by
      rw [orderOf_inv]
      exact orderOf_dvd_of_pow_eq_one hbm
    exact Nat.Coprime.coprime_dvd_right h3 h2.symm
  obtain ⟨M, hM⟩ := exists_pow_eq_self_of_coprime (x := b⁻¹) hcop
  have hcomm : Commute d₀ b⁻¹ := (hCD d₀ hd₀D).symm.inv_right
  have hwn : (u ^ j) ^ orderOf d₀ = b⁻¹ ^ orderOf d₀ := by
    rw [hw, hcomm.mul_pow, pow_orderOf_eq_one, one_mul]
  have hbinv : b⁻¹ = u ^ (j * ((orderOf d₀ : ℤ) * (M : ℤ))) := by
    calc b⁻¹ = (b⁻¹ ^ orderOf d₀) ^ M := hM.symm
      _ = ((u ^ j) ^ orderOf d₀) ^ M := by rw [hwn]
      _ = u ^ (j * ((orderOf d₀ : ℤ) * (M : ℤ))) := by
        rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  have hub : Commute u b := by
    have h : Commute u b⁻¹ := by
      rw [hbinv]
      exact Commute.self_zpow u _
    simpa using h.inv_right
  have hCen : ∀ e ∈ E, Commute b e := by
    intro e he
    obtain ⟨j', hj'⟩ := hcyc e he
    have h1 : Commute b (u ^ j') := (hub.symm).zpow_right j'
    have h2 : Commute b (u ^ j' * e) := hCD _ hj'
    have h3 : e = (u ^ j')⁻¹ * (u ^ j' * e) := by group
    rw [h3]
    exact h1.inv_right.mul_right h2
  exact commutatorElement_eq_one_iff_mul_comm.2 (hCen a ha).symm.eq

end Layers

end CFSG.AGLEmbedding.TwoGenInner
