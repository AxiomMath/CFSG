module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67UnForm

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1.Un

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.OddAut

section Rho

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Matrix ι ι K}

theorem exists_gramSU_of_unipotent [Nonempty ι] [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2)
    (M : Matrix ι ι K) (hM : (M - 1) ^ 3 = 0) (hiso : (M.map h.bar)ᵀ * G * M = G) :
    ∃ g : gramSU h G, mx (g : GL ι K) = M := by
  have hp3 : 3 ≤ p := by
    have := (Fact.out : p.Prime).two_le
    omega
  have hNp : (M - 1) ^ p = 0 := by
    rw [show p = 3 + (p - 3) by omega, pow_add, hM, zero_mul]
  have hMp : M ^ p = 1 := by
    have h1 : M = (M - 1) + 1 := by abel
    rw [h1, add_pow_char_of_commute p (Commute.one_right _), hNp, one_pow, zero_add]
  have hp1 : 1 ≤ p := by omega
  have hu1 : M * M ^ (p - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel hp1, hMp]
  have hu2 : M ^ (p - 1) * M = 1 := by
    rw [← pow_succ, Nat.sub_add_cancel hp1, hMp]
  have hdet : M.det = 1 := by
    have h1 : M.det ^ p = 1 := by rw [← Matrix.det_pow, hMp, Matrix.det_one]
    apply frobenius_inj K p
    rw [frobenius_def, map_one]
    exact h1
  exact ⟨⟨⟨M, M ^ (p - 1), hu1, hu2⟩, mem_gramSU.mpr ⟨hiso, hdet⟩⟩, rfl⟩

@[expose] noncomputable def rhoLin (h : UnitaryFieldData p f K) (G : Matrix ι ι K)
    (e w : ι → K) (c : K) : (ι → K) →ₗ[K] (ι → K) :=
  LinearMap.id + (gramForm h G e).smulRight w - (gramForm h G w).smulRight e +
    c • (gramForm h G e).smulRight e

omit [DecidableEq ι] in
theorem rhoLin_apply (e w : ι → K) (c : K) (x : ι → K) :
    rhoLin h G e w c x = x + gramForm h G e x • w - gramForm h G w x • e +
      (c * gramForm h G e x) • e := by
  simp [rhoLin, mul_smul]

theorem rhoLin_isometry (hG : HermGram h G) {e w : ι → K} {c : K}
    (hee : gramForm h G e e = 0) (hew : gramForm h G e w = 0)
    (hc : c + h.bar c + gramForm h G w w = 0) (x y : ι → K) :
    gramForm h G (rhoLin h G e w c x) (rhoLin h G e w c y) = gramForm h G x y := by
  have hwe : gramForm h G w e = 0 := B_eq_zero_comm hG hew
  have hxe : gramForm h G x e = h.bar (gramForm h G e x) := (B_herm hG e x).symm
  have hxw : gramForm h G x w = h.bar (gramForm h G w x) := (B_herm hG w x).symm
  rw [rhoLin_apply, rhoLin_apply]
  simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, map_smulₛₗ,
    LinearMap.smul_apply, smul_eq_mul, hee, hew, hwe, hxe, hxw, mul_zero, map_mul, mul_zero,
    sub_zero, add_zero]
  have hB : gramForm h G e y = gramForm h G e y := rfl
  linear_combination (h.bar (gramForm h G e x) * gramForm h G e y) * hc

theorem exists_rho [Nonempty ι] [Fact p.Prime] [CharP K p] (hp2 : p ≠ 2) (hG : HermGram h G)
    {e w : ι → K} {c : K} (hee : gramForm h G e e = 0) (hew : gramForm h G e w = 0)
    (hc : c + h.bar c + gramForm h G w w = 0) :
    ∃ x : gramSU h G, ∀ v, act x v = v + gramForm h G e v • w - gramForm h G w v • e +
      (c * gramForm h G e v) • e := by
  have hwe : gramForm h G w e = 0 := B_eq_zero_comm hG hew
  set M : Matrix ι ι K := LinearMap.toMatrix' (rhoLin h G e w c) with hM
  have hMv : ∀ v, M *ᵥ v = rhoLin h G e w c v := fun v => by
    rw [← Matrix.toLin'_apply, hM, Matrix.toLin'_toMatrix']
  have hNv : ∀ v, (M - 1) *ᵥ v = gramForm h G e v • w - gramForm h G w v • e +
      (c * gramForm h G e v) • e := fun v => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, hMv, rhoLin_apply]
    abel
  have hnil : (M - 1) ^ 3 = 0 := by
    by_contra hne
    obtain ⟨v, hv⟩ := exists_mulVec_ne_zero hne
    apply hv
    have e1 : (M - 1) ^ 3 *ᵥ v = (M - 1) *ᵥ ((M - 1) *ᵥ ((M - 1) *ᵥ v)) := by
      rw [pow_succ_mulVec, pow_succ_mulVec, pow_succ_mulVec, pow_zero, Matrix.one_mulVec]
    have h1 : gramForm h G e ((M - 1) *ᵥ v) = 0 := by
      rw [hNv]
      simp only [map_add, map_sub, map_smul, smul_eq_mul, hee, hew, mul_zero, sub_zero, add_zero]
    have h2 : gramForm h G w ((M - 1) *ᵥ v) = gramForm h G e v * gramForm h G w w := by
      rw [hNv]
      simp only [map_add, map_sub, map_smul, smul_eq_mul, hwe, mul_zero, sub_zero, add_zero]
    have h3 : (M - 1) *ᵥ ((M - 1) *ᵥ v) = (-(gramForm h G e v * gramForm h G w w)) • e := by
      rw [hNv ((M - 1) *ᵥ v), h1, h2]
      simp
    rw [e1, h3, Matrix.mulVec_smul, hNv e]
    simp [hee, hwe]
  have hiso : (M.map h.bar)ᵀ * G * M = G :=
    (gramForm_isometry_iff h G M).mp (fun x y => by
      rw [hMv, hMv]
      exact rhoLin_isometry hG hee hew hc x y)
  obtain ⟨g, hg⟩ := exists_gramSU_of_unipotent hp2 M hnil hiso
  exact ⟨g, fun v => by
    change mx (g : GL ι K) *ᵥ v = _
    rw [hg, hMv, rhoLin_apply]⟩

theorem inQ_of_rho (hG : HermGram h G) {E : Submodule K (ι → K)} {e w : ι → K} {c : K}
    (heE : e ∈ E) (heo : e ∈ orthU h G E) (hwE : w ∈ E) {x : gramSU h G}
    (hx : ∀ v, act x v = v + gramForm h G e v • w - gramForm h G w v • e +
      (c * gramForm h G e v) • e) : InQ E x := by
  have hact : ∀ v, act x v - v = gramForm h G e v • w - gramForm h G w v • e +
      (c * gramForm h G e v) • e := fun v => by rw [hx]; abel
  refine ⟨fun v => ?_, fun v hv => ?_⟩
  · rw [hact]
    exact E.add_mem (E.sub_mem (E.smul_mem _ hwE) (E.smul_mem _ heE)) (E.smul_mem _ heE)
  · rw [hact]
    have hve : gramForm h G e v = 0 := B_eq_zero_comm hG ((mem_orthU.mp heo) v hv)
    have : (0 : K) • w - gramForm h G w v • e + (c * 0) • e = (-gramForm h G w v) • e := by
      rw [zero_smul, mul_zero, zero_smul, neg_smul]
      abel
    rw [hve, this]
    exact (orthU h G E).smul_mem _ heo

end Rho

section Key

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {ι : Type} [Fintype ι]
  [DecidableEq ι] {G : Matrix ι ι K}

theorem exists_traceZero_ne_zero (h : UnitaryFieldData p f K) :
    ∃ i0 : K, i0 ≠ 0 ∧ i0 + h.bar i0 = 0 := by
  obtain ⟨c, hc⟩ := h.exists_bar_ne
  refine ⟨c - h.bar c, sub_ne_zero.mpr (Ne.symm hc), ?_⟩
  rw [map_sub, h.bar_bar]
  ring

theorem exists_B_eq_one (hG : HermGram h G) {e : ι → K} (he0 : e ≠ 0) :
    ∃ v0, gramForm h G e v0 = 1 := by
  by_contra hcon
  push Not at hcon
  have h0 : ∀ v, gramForm h G e v = 0 := by
    intro v
    by_contra hv
    apply hcon ((gramForm h G e v)⁻¹ • v)
    rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]
  exact he0 (gramForm_separatingLeft h hG.det_ne e h0)

theorem sigma_sq_of_fixed (σ : K ≃+* K) (hσ : ∀ t, h.bar t = t → σ t = t) (c : K) :
    σ (σ c) = c := by
  have ht : σ (c + h.bar c) = c + h.bar c := hσ _ (by rw [map_add, h.bar_bar, add_comm])
  have hn : σ (c * h.bar c) = c * h.bar c :=
    hσ _ (by rw [map_mul, h.bar_bar, mul_comm])
  have hq : (σ c - c) * (σ c - h.bar c) = 0 := by
    have h1 : σ (c * c - (c + h.bar c) * c + c * h.bar c) = 0 := by
      have : c * c - (c + h.bar c) * c + c * h.bar c = 0 := by ring
      rw [this, map_zero]
    rw [map_add, map_sub, map_mul, map_mul, ht, hn] at h1
    linear_combination h1
  rcases mul_eq_zero.mp hq with h1 | h1
  · rw [sub_eq_zero.mp h1]
    exact sub_eq_zero.mp h1
  · have h2 : σ c = h.bar c := sub_eq_zero.mp h1
    rw [h2, map_bar_comm h σ c, h2, h.bar_bar]

section KeyT

variable [Fact p.Prime] [CharP K p] [Nonempty ι]

theorem step_T (hG : HermGram h G) (hp2 : p ≠ 2) {E : Submodule K (ι → K)} {e : ι → K}
    (heE : e ∈ E) (heo : e ∈ orthU h G E) (he0 : e ≠ 0) (A : GL ι K) (σ : K ≃+* K) {μ : K}
    (hA : ((mx A).map h.bar)ᵀ * G * mx A = μ • G)
    (hΦQ : ∀ x : gramSU h G, InQ E x → ∀ v, semi A σ (act x v) = act x (semi A σ v)) :
    ∃ l : K, l ≠ 0 ∧ semi A σ e = l • e ∧ (∀ t, h.bar t = t → σ t = t) ∧
      ∀ c, c + h.bar c = 0 → σ c * (l * h.bar l) = c * μ := by
  have hee : gramForm h G e e = 0 := (mem_orthU.mp heo) e heE
  obtain ⟨i0, hi0, hi0t⟩ := exists_traceZero_ne_zero h
  obtain ⟨v0, hv0⟩ := exists_B_eq_one hG he0
  have htv : ∀ c, c + h.bar c = 0 → ∀ v, σ (c * gramForm h G e v) • semi A σ e =
      (c * gramForm h G e (semi A σ v)) • e := by
    intro c hc v
    obtain ⟨x, hx⟩ := exists_rho hp2 hG (e := e) (w := 0) (c := c) hee (by rw [map_zero])
      (by simp [hc])
    have hxQ : InQ E x := inQ_of_rho hG heE heo E.zero_mem hx
    have h1 := hΦQ x hxQ v
    rw [hx, hx] at h1
    simp only [map_zero, smul_zero, LinearMap.zero_apply, zero_smul, sub_zero, add_zero] at h1
    rw [semi_add, semi_smul] at h1
    exact add_left_cancel h1
  have hΦe_ne : semi A σ e ≠ 0 := fun h0 => he0 ((semi_eq_zero_iff A σ e).mp h0)
  have hσi0 : σ i0 ≠ 0 := fun h0 => hi0 (σ.injective (by rw [h0, map_zero]))
  obtain ⟨l, hΦe⟩ : ∃ l : K, semi A σ e = l • e := by
    refine ⟨(σ i0)⁻¹ * (i0 * gramForm h G e (semi A σ v0)), ?_⟩
    have h1 := htv i0 hi0t v0
    rw [hv0, mul_one] at h1
    rw [← smul_smul, ← h1, smul_smul, inv_mul_cancel₀ hσi0, one_smul]
  have hl0 : l ≠ 0 := by
    rintro rfl
    exact hΦe_ne (by rw [hΦe, zero_smul])
  have hsim : ∀ v, h.bar l * gramForm h G e (semi A σ v) = μ * σ (gramForm h G e v) := by
    intro v
    have := B_semi hG A σ hA e v
    rw [hΦe, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul] at this
    exact this
  have hN : ∀ c, c + h.bar c = 0 → σ c * (l * h.bar l) = c * μ := by
    intro c hc
    have h1 := htv c hc v0
    rw [hv0, mul_one, hΦe, smul_smul] at h1
    have h2 : σ c * l = c * gramForm h G e (semi A σ v0) :=
      smul_left_injective K he0 h1
    have h3 := hsim v0
    rw [hv0, map_one, mul_one] at h3
    calc σ c * (l * h.bar l) = (σ c * l) * h.bar l := by ring
      _ = c * (h.bar l * gramForm h G e (semi A σ v0)) := by rw [h2]; ring
      _ = c * μ := by rw [h3]
  refine ⟨l, hl0, hΦe, fun t ht => ?_, hN⟩
  have hbarl : h.bar l ≠ 0 := fun h0 => hl0 ((UnitaryFieldData.bar_eq_zero_iff h).mp h0)
  have hNl : l * h.bar l ≠ 0 := mul_ne_zero hl0 hbarl
  have h1 := hN (i0 * t) (by rw [map_mul, ht, ← add_mul, hi0t, zero_mul])
  have h2 := hN i0 hi0t
  rw [map_mul] at h1
  have h3 : (σ i0 * (l * h.bar l)) * σ t = (σ i0 * (l * h.bar l)) * t := by
    calc (σ i0 * (l * h.bar l)) * σ t = σ i0 * σ t * (l * h.bar l) := by ring
      _ = i0 * t * μ := h1
      _ = (i0 * μ) * t := by ring
      _ = (σ i0 * (l * h.bar l)) * t := by rw [h2]
  have hne : σ i0 * (l * h.bar l) ≠ 0 := mul_ne_zero hσi0 hNl
  exact mul_left_cancel₀ hne h3

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
theorem one_apply_ringEquiv (c : K) : (1 : K ≃+* K) c = c := rfl

theorem two_ne_zero_of_char (hp2 : p ≠ 2) : (2 : K) ≠ 0 := by
  intro h2
  apply hp2
  have : ((2 : ℕ) : K) = 0 := by exact_mod_cast h2
  exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp
    ((CharP.cast_eq_zero_iff K p 2).mp this))

theorem step_E (hG : HermGram h G) (hp2 : p ≠ 2) {E : Submodule K (ι → K)} {e : ι → K}
    (heE : e ∈ E) (heo : e ∈ orthU h G E) (he0 : e ≠ 0) (A : GL ι K) {μ : K}
    (hA : ((mx A).map h.bar)ᵀ * G * mx A = μ • G) {l : K} (hl0 : l ≠ 0)
    (hΦe : semi A 1 e = l • e) (hN : l * h.bar l = μ)
    (hΦQ : ∀ x : gramSU h G, InQ E x → ∀ v, semi A 1 (act x v) = act x (semi A 1 v))
    {w : ι → K} (hwE : w ∈ E) : ∃ κ : K, semi A 1 w = l • w + κ • e := by
  have hee : gramForm h G e e = 0 := (mem_orthU.mp heo) e heE
  have hwe : gramForm h G w e = 0 := (mem_orthU.mp heo) w hwE
  have hew : gramForm h G e w = 0 := B_eq_zero_comm hG hwe
  obtain ⟨v0, hv0⟩ := exists_B_eq_one hG he0
  have h2K : (2 : K) ≠ 0 := two_ne_zero_of_char hp2
  have hww : h.bar (gramForm h G w w) = gramForm h G w w := B_herm hG w w
  have hbarc : h.bar (-(gramForm h G w w) / 2) = -(gramForm h G w w) / 2 := by
    rw [map_div₀, map_neg, hww, map_ofNat]
  have hcc : -(gramForm h G w w) / 2 + h.bar (-(gramForm h G w w) / 2) + gramForm h G w w = 0 := by
    rw [hbarc]
    field_simp
    ring
  obtain ⟨x, hx⟩ := exists_rho hp2 hG hee hew hcc
  have hxQ : InQ E x := inQ_of_rho hG heE heo hwE hx
  have h1 := hΦQ x hxQ v0
  rw [hx, hx] at h1
  have hbarl : h.bar l ≠ 0 := fun h0 => hl0 ((UnitaryFieldData.bar_eq_zero_iff h).mp h0)
  have hBe : gramForm h G e (semi A 1 v0) = l := by
    have := B_semi hG A 1 hA e v0
    rw [hΦe, map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, hv0] at this
    apply mul_left_cancel₀ hbarl
    rw [this]
    simp only [one_apply_ringEquiv, mul_one]
    rw [← hN]
    ring
  refine ⟨gramForm h G w v0 * l - gramForm h G w (semi A 1 v0), ?_⟩
  simp only [semi_add, semi_sub, semi_smul, hΦe, hv0, hBe, one_apply_ringEquiv] at h1
  linear_combination (norm := module) h1

omit [Nonempty ι] in
theorem step_F {M N : Matrix ι ι K} {e : ι → K} {l : K} {s n : ℕ} (hl0 : l ≠ 0) (he0 : e ≠ 0)
    (hNp : N ^ n = 0) (hMN : M * N = N * M) (hMe : M *ᵥ e = l • e)
    (hker : ∀ w, N *ᵥ w = 0 → ∃ κ : K, M *ᵥ w = l • w + κ • e)
    (hMs : ∃ c : K, M ^ s = c • (1 : Matrix ι ι K)) (hs : (s : K) ≠ 0) :
    M = l • (1 : Matrix ι ι K) := by
  obtain ⟨c, hc⟩ := hMs
  set A' : Matrix ι ι K := l⁻¹ • M with hA'
  have hA'e : A' *ᵥ e = e := by
    rw [hA', Matrix.smul_mulVec, hMe, smul_smul, inv_mul_cancel₀ hl0, one_smul]
  have hA'w : ∀ w, N *ᵥ w = 0 → ∃ κ : K, A' *ᵥ w = w + κ • e := by
    intro w hw
    obtain ⟨κ, hκ⟩ := hker w hw
    refine ⟨l⁻¹ * κ, ?_⟩
    rw [hA', Matrix.smul_mulVec, hκ, smul_add, smul_smul, smul_smul, inv_mul_cancel₀ hl0,
      one_smul]
  have hpow_e : ∀ k : ℕ, A' ^ k *ᵥ e = e := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ, ← Matrix.mulVec_mulVec, hA'e, ih]
  have hc' : A' ^ s = (l⁻¹ ^ s * c) • (1 : Matrix ι ι K) := by
    rw [hA', smul_pow, hc, smul_smul]
  have hc1 : l⁻¹ ^ s * c = 1 := by
    have h1 := hpow_e s
    rw [hc', Matrix.smul_mulVec, Matrix.one_mulVec] at h1
    have : (l⁻¹ ^ s * c - 1) • e = 0 := by rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right he0)
  have hA's : A' ^ s = 1 := by rw [hc', hc1, one_smul]
  have hker' : ∀ w, N *ᵥ w = 0 → A' *ᵥ w = w := by
    intro w hw
    obtain ⟨κ, hκ⟩ := hA'w w hw
    have hpow_w : ∀ k : ℕ, A' ^ k *ᵥ w = w + ((k : K) * κ) • e := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        rw [pow_succ, ← Matrix.mulVec_mulVec, hκ, Matrix.mulVec_add, Matrix.mulVec_smul, hpow_e,
          ih]
        push_cast
        module
    have h1 := hpow_w s
    rw [hA's, Matrix.one_mulVec] at h1
    have h2 : ((s : K) * κ) • e = 0 := by
      have := congrArg (fun x => x - w) h1
      simpa using this.symm
    have hκ0 : κ = 0 := by
      have := (smul_eq_zero.mp h2).resolve_right he0
      exact (mul_eq_zero.mp this).resolve_left hs
    rw [hκ, hκ0, zero_smul, add_zero]
  have hA'N : A' * N = N * A' := by rw [hA', smul_mul_assoc, mul_smul_comm, hMN]
  have hA1 : A' = 1 := eq_one_of_commute_nilpotent_ker hA'N hNp hker' hA's hs
  have hMA : M = l • A' := by rw [hA', smul_smul, mul_inv_cancel₀ hl0, one_smul]
  rw [hMA, hA1]

omit [Nonempty ι] in
theorem mat_eq_of_mulVec_eq {M M' : Matrix ι ι K} (hMM : ∀ v, M *ᵥ v = M' *ᵥ v) : M = M' := by
  ext i j
  have := congrFun (hMM (Pi.single j 1)) i
  simpa using this

theorem key_prop (hG : HermGram h G) (hp2 : p ≠ 2) {u : gramSU h G} (hup : u ^ p = 1)
    (hu1 : u ≠ 1) (A : GL ι K) (σ : K ≃+* K) {μ : K}
    (hA : ((mx A).map h.bar)ᵀ * G * mx A = μ • G)
    (hΦu : ∀ v, semi A σ (act u v) = act u (semi A σ v))
    (hΦQ : ∀ x : gramSU h G, InQ (fixU u) x → ∀ v, semi A σ (act x v) = act x (semi A σ v))
    {s : ℕ} (hs : Odd s) (hsp : ¬ p ∣ s) (hσs : σ ^ s = 1)
    (hAs : σ = 1 → ∃ c : K, (mx A) ^ s = c • (1 : Matrix ι ι K)) :
    σ = 1 ∧ ∃ l : K, l ≠ 0 ∧ mx A = l • (1 : Matrix ι ι K) := by
  set U : Matrix ι ι K := mx (u : GL ι K) with hU
  set N : Matrix ι ι K := U - 1 with hN
  have hUp : U ^ p = 1 := by
    have := congrArg (fun g : gramSU h G => mx (g : GL ι K)) hup
    simpa [hU, mx] using this
  have hNp : N ^ p = 0 := by
    rw [hN, sub_pow_char_of_commute p (Commute.one_right U), hUp, one_pow, sub_self]
  have hNne : N ≠ 0 := by
    intro h0
    apply hu1
    have : U = 1 := sub_eq_zero.mp h0
    apply Subtype.ext
    apply Units.ext
    simpa [hU, mx] using this
  have hNv : ∀ v, N *ᵥ v = act u v - v := fun v => mx_sub_one_mulVec u v
  obtain ⟨e, he0, hNe, v, hv⟩ := exists_mem_ker_range_of_nilpotent hNp hNne
  have heE : e ∈ fixU u := by
    rw [mem_fixU]
    have := hNv e
    rw [hNe] at this
    exact sub_eq_zero.mp this.symm
  have heo : e ∈ orthU h G (fixU u) := by
    rw [← hv, hNv]
    exact act_sub_mem_orthU_fixU u v
  obtain ⟨l, hl0, hΦe, hσF, hNl⟩ := step_T hG hp2 heE heo he0 A σ hA hΦQ
  have hσsq : σ * σ = 1 := RingEquiv.ext fun c => sigma_sq_of_fixed σ hσF c
  have hσ1 : σ = 1 := by
    obtain ⟨k, hk⟩ := hs
    have h1 : σ ^ s = σ := by
      rw [hk, pow_succ, pow_mul, sq, hσsq, one_pow, one_mul]
    rw [← h1, hσs]
  subst hσ1
  obtain ⟨i0, hi0, hi0t⟩ := exists_traceZero_ne_zero h
  have hNl' : l * h.bar l = μ := by
    have := hNl i0 hi0t
    rw [one_apply_ringEquiv] at this
    exact mul_left_cancel₀ hi0 this
  have hker : ∀ w, N *ᵥ w = 0 → ∃ κ : K, mx A *ᵥ w = l • w + κ • e := by
    intro w hw
    have hwE : w ∈ fixU u := by
      rw [mem_fixU]
      have := hNv w
      rw [hw] at this
      exact sub_eq_zero.mp this.symm
    exact step_E hG hp2 heE heo he0 A hA hl0 hΦe hNl' hΦQ hwE
  have hMU : mx A * U = U * mx A := mat_eq_of_mulVec_eq fun v => by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact hΦu v
  have hMN : mx A * N = N * mx A := by
    rw [hN, mul_sub, sub_mul, hMU, mul_one, one_mul]
  have hs' : (s : K) ≠ 0 := fun h0 => hsp ((CharP.cast_eq_zero_iff K p s).mp h0)
  obtain ⟨c, hc⟩ := hAs rfl
  exact ⟨rfl, l, hl0, step_F hl0 he0 hNp hMN hΦe hker ⟨c, hc⟩ hs'⟩

end KeyT

end Key

end CFSG.GH74.GLS.Stage2.Bender.Thm1.Un
