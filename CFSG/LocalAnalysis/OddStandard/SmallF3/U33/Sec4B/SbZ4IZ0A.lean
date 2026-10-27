module
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IZ0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4IK1

public section
namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B
open Subgroup
open scoped commutatorElement
variable {H : Type} [Group H] [Finite H]
@[expose] def z4iT3 (t τ l : H) : Subgroup H := closure {t, τ, l}
private lemma z4i_pow_add_fin {G : Type*} [Group G] (x : G) (hx : x * x = 1)
    (a a' : Fin 2) : x ^ (a : ℕ) * x ^ (a' : ℕ) = x ^ ((a + a' : Fin 2) : ℕ) := by
  rw [← pow_add, pow_eq_pow_mod (n := 2) ((a : ℕ) + (a' : ℕ))
      (by simpa [pow_two] using hx), ← Fin.val_add]
private lemma z4i_mul_three_comm {G : Type*} [Group G] {a₁ a₂ a₃ b₁ b₂ b₃ : G}
    (h31 : Commute a₃ b₁) (h21 : Commute a₂ b₁) (h32 : Commute a₃ b₂) :
    a₁ * a₂ * a₃ * (b₁ * b₂ * b₃) = (a₁ * b₁) * (a₂ * b₂) * (a₃ * b₃) := by
  calc a₁ * a₂ * a₃ * (b₁ * b₂ * b₃)
      = a₁ * a₂ * (a₃ * b₁) * b₂ * b₃ := by group
    _ = a₁ * a₂ * (b₁ * a₃) * b₂ * b₃ := by rw [h31.eq]
    _ = a₁ * (a₂ * b₁) * a₃ * b₂ * b₃ := by group
    _ = a₁ * (b₁ * a₂) * a₃ * b₂ * b₃ := by rw [h21.eq]
    _ = a₁ * b₁ * a₂ * (a₃ * b₂) * b₃ := by group
    _ = a₁ * b₁ * a₂ * (b₂ * a₃) * b₃ := by rw [h32.eq]
    _ = (a₁ * b₁) * (a₂ * b₂) * (a₃ * b₃) := by group
namespace ZEData
variable {Q Y V V' B K : Subgroup H} {ρ t τ l : H}
private lemma word_mul (h : ZEData Q Y V V' B K ρ t τ l) (a b c a' b' c' : Fin 2) :
    (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)) *
      (t ^ (a' : ℕ) * τ ^ (b' : ℕ) * l ^ (c' : ℕ)) =
    t ^ ((a + a' : Fin 2) : ℕ) * τ ^ ((b + b' : Fin 2) : ℕ) *
      l ^ ((c + c' : Fin 2) : ℕ) := by
  have ctl : Commute t l := h.t_l
  have ctt : Commute t τ := h.t_tau
  have cτl : Commute τ l := h.tau_l
  rw [z4i_mul_three_comm (ctl.symm.pow_pow c a') (ctt.symm.pow_pow b a')
    (cτl.symm.pow_pow c b')]
  rw [z4i_pow_add_fin t h.t_sq a a', z4i_pow_add_fin τ h.tau_sq b b',
    z4i_pow_add_fin l h.l_sq c c']
private lemma word_sq (h : ZEData Q Y V V' B K ρ t τ l) (a b c : Fin 2) :
    (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)) *
      (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)) = 1 := by
  rw [word_mul h a b c a b c]
  have ha : (a + a : Fin 2) = 0 := by fin_cases a <;> decide
  have hb : (b + b : Fin 2) = 0 := by fin_cases b <;> decide
  have hc : (c + c : Fin 2) = 0 := by fin_cases c <;> decide
  rw [ha, hb, hc]
  simp
private lemma word_inv (h : ZEData Q Y V V' B K ρ t τ l) (a b c : Fin 2) :
    (t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ))⁻¹ =
      t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) :=
  inv_eq_of_mul_eq_one_right (word_sq h a b c)
private lemma T3_commute (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ x ∈ z4iT3 t τ l, ∀ y ∈ z4iT3 t τ l, Commute x y := by
  intro x hx y hy
  refine Subgroup.closure_induction₂ (p := fun x y _ _ => Commute x y)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ hx hy
  · intro x y hx hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx hy
    rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl <;>
      first
        | exact Commute.refl _
        | exact h.t_tau
        | exact h.t_tau.symm
        | exact h.t_l
        | exact h.t_l.symm
        | exact h.tau_l
        | exact h.tau_l.symm
  · intro x _; exact Commute.one_left x
  · intro x _; exact Commute.one_right x
  · intro x y z _ _ _ hxz hyz; exact hxz.mul_left hyz
  · intro y z x _ _ _ hxy hxz; exact hxy.mul_right hxz
  · intro x y _ _ hxy; exact hxy.inv_left
  · intro x y _ _ hxy; exact hxy.inv_right
private lemma gen_mem_normalizer (h : ZEData Q Y V V' B K ρ t τ l) {g : H}
    (hg : g ∈ ({t, τ, l} : Set H)) : g ∈ Subgroup.normalizer (K : Set H) := by
  have hg' : g = t ∨ g = τ ∨ g = l := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg
  have hg2 : g * g = 1 := by
    rcases hg' with ht | hτ | hl
    · rw [ht]; exact h.t_sq
    · rw [hτ]; exact h.tau_sq
    · rw [hl]; exact h.l_sq
  have hnf : ∀ k : H, k ∈ K → g * k * g⁻¹ ∈ K := by
    intro k hk
    rcases hg' with ht | hτ | hl
    · rw [ht]; exact h.t_norm_K k hk
    · rw [hτ]; exact h.tau_norm_K k hk
    · rw [hl]; exact h.l_norm_K k hk
  rw [Subgroup.mem_set_normalizer_iff]
  intro k
  constructor
  · exact hnf k
  · intro hk
    have hconj : g * (g * k * g⁻¹) * g⁻¹ = k := by
      calc g * (g * k * g⁻¹) * g⁻¹ = (g * g) * k * (g * g)⁻¹ := by group
        _ = k := by rw [hg2]; simp
    have hk' : g * (g * k * g⁻¹) * g⁻¹ ∈ K := hnf (g * k * g⁻¹) hk
    rwa [hconj] at hk'
private lemma fin2_add_eq_zero {a a' : Fin 2} (h : a + a' = 0) : a = a' := by
  revert h
  fin_cases a <;> fin_cases a' <;> decide
theorem t_mem_T3 (t τ l : H) : t ∈ z4iT3 t τ l :=
  Subgroup.subset_closure (by simp)
theorem tau_mem_T3 (t τ l : H) : τ ∈ z4iT3 t τ l :=
  Subgroup.subset_closure (by simp)
theorem l_mem_T3 (t τ l : H) : l ∈ z4iT3 t τ l :=
  Subgroup.subset_closure (by simp)
theorem mem_T3_iff (h : ZEData Q Y V V' B K ρ t τ l) {x : H} :
    x ∈ z4iT3 t τ l ↔
      ∃ a b c : Fin 2, x = t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) := by
  let W : Subgroup H :=
    { carrier := {x | ∃ a b c : Fin 2, x = t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ)}
      one_mem' := ⟨0, 0, 0, by simp⟩
      mul_mem' := by
        rintro x y ⟨a, b, c, rfl⟩ ⟨a', b', c', rfl⟩
        exact ⟨a + a', b + b', c + c', word_mul h a b c a' b' c'⟩
      inv_mem' := by
        rintro x ⟨a, b, c, rfl⟩
        exact ⟨a, b, c, word_inv h a b c⟩ }
  constructor
  · intro hx
    refine (Subgroup.closure_le (k := ({t, τ, l} : Set H)) W).mpr ?_ hx
    intro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  · rintro ⟨a, b, c, rfl⟩
    have ht : t ∈ z4iT3 t τ l :=
      Subgroup.subset_closure (show t ∈ ({t, τ, l} : Set H) from by simp)
    have hτ : τ ∈ z4iT3 t τ l :=
      Subgroup.subset_closure (show τ ∈ ({t, τ, l} : Set H) from by simp)
    have hl : l ∈ z4iT3 t τ l :=
      Subgroup.subset_closure (show l ∈ ({t, τ, l} : Set H) from by simp)
    exact (z4iT3 t τ l).mul_mem
      ((z4iT3 t τ l).mul_mem
        (Subgroup.pow_mem (K := z4iT3 t τ l) ht (a : ℕ))
        (Subgroup.pow_mem (K := z4iT3 t τ l) hτ (b : ℕ)))
      (Subgroup.pow_mem (K := z4iT3 t τ l) hl (c : ℕ))
theorem T3_comm (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ x ∈ z4iT3 t τ l, ∀ y ∈ z4iT3 t τ l, x * y = y * x :=
  fun x hx y hy => (T3_commute h x hx y hy).eq
theorem T3_sq (h : ZEData Q Y V V' B K ρ t τ l) : ∀ x ∈ z4iT3 t τ l, x * x = 1 := by
  intro x hx
  obtain ⟨a, b, c, rfl⟩ := (mem_T3_iff h).mp hx
  exact word_sq h a b c
theorem T3_cent_t (h : ZEData Q Y V V' B K ρ t τ l) :
    z4iT3 t τ l ≤ centralizer ({t} : Set H) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  rw [hy]
  exact (T3_commute h x hx t (t_mem_T3 t τ l)).eq.symm
theorem T3_norm_K (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ s ∈ z4iT3 t τ l, ∀ k ∈ K, s * k * s⁻¹ ∈ K := by
  have hle : z4iT3 t τ l ≤ Subgroup.normalizer (K : Set H) :=
    (Subgroup.closure_le (k := ({t, τ, l} : Set H))
      (Subgroup.normalizer (K : Set H))).mpr fun g hg => gen_mem_normalizer h hg
  intro s hs k hk
  exact ((Subgroup.mem_set_normalizer_iff (S := (K : Set H))).mp (hle hs) k).mp hk
theorem T3_norm_B (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ s ∈ z4iT3 t τ l, ∀ b ∈ B, s * b * s⁻¹ ∈ B := by
  intro s hs b hb
  have hsQ : s * b * s⁻¹ ∈ Q := h.normal_Q s b (h.B_le_Q hb)
  have hcomm : t * (s * b * s⁻¹) = (s * b * s⁻¹) * t := by
    have h1 : Commute s t := T3_commute h s hs t (t_mem_T3 t τ l)
    have h2 : Commute b t := (h.B_cent_t b hb).symm
    exact ((h1.mul_left h2).mul_left h1.inv_left).eq.symm
  exact h.cent_t_Q (s * b * s⁻¹) hsQ hcomm
theorem rho_ne_one (h : ZEData Q Y V V' B K ρ t τ l) : ρ ≠ 1 := by
  intro hρ
  have hQbot : Q = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro q hq
    exact h.rho_fpf_Q q hq (by rw [hρ]; group)
  have hcard : Nat.card Q = 1 := by rw [hQbot, Subgroup.card_bot]
  rw [h.card_Q] at hcard
  norm_num at hcard
theorem t_not_mem_K (h : ZEData Q Y V V' B K ρ t τ l) : t ∉ K := by
  intro htK
  have hYV : Y ≤ V := by
    intro y hy
    exact h.Y_cent_t y hy (h.K_cent_Y t htK y hy)
  have hcard := Subgroup.card_le_of_le hYV
  rw [h.card_Y, h.card_V] at hcard
  omega
private lemma rho_ne_one_contra (h : ZEData Q Y V V' B K ρ t τ l) (hρ2K : ρ ^ 2 ∈ K) :
    False := by
  have h256 : (ρ ^ 2) ^ Nat.card K = 1 := by
    have h1 : (⟨ρ ^ 2, hρ2K⟩ : K) ^ Nat.card K = 1 := pow_card_eq_one'
    have h2 : ((⟨ρ ^ 2, hρ2K⟩ : K) ^ Nat.card K : H) = 1 := congrArg Subtype.val h1
    simpa only [Subgroup.coe_pow] using h2
  have h512 : ρ ^ 512 = 1 := by
    have h2 : (ρ ^ 2) ^ 256 = 1 := by rwa [h.card_K] at h256
    have h3 : ρ ^ (2 * 256) = 1 := by rwa [← pow_mul] at h2
    rwa [show (2 : ℕ) * 256 = 512 by norm_num] at h3
  have h2 : ρ ^ 2 = 1 := by
    have hmod : ρ ^ 512 = ρ ^ 2 := by
      rw [pow_eq_pow_mod 512 h.rho_pow_three]
    rw [← hmod]; exact h512
  have hρ1 : ρ = 1 := by
    calc ρ = ρ * 1 := (mul_one ρ).symm
      _ = ρ * ρ ^ 2 := by rw [h2]
      _ = ρ ^ 3 := by rw [← (pow_succ' ρ 2)]
      _ = 1 := h.rho_pow_three
  exact h.rho_ne_one hρ1
private lemma rho_sq_mem_of_mem_K (h : ZEData Q Y V V' B K ρ t τ l) {a b : Fin 2}
    (hmem : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ∈ K) : ρ ^ 2 ∈ K := by
  set w : H := t ^ (a : ℕ) * τ ^ (b : ℕ) with hw
  have hwρ : w * ρ = ρ * w := by
    have h1 : Commute (t ^ (a : ℕ)) ρ := (show Commute t ρ from h.t_rho).pow_left (a : ℕ)
    have h2 : Commute (τ ^ (b : ℕ)) ρ := (show Commute τ ρ from h.tau_rho).pow_left (b : ℕ)
    exact (h1.mul_left h2).eq
  have hlρ : l * ρ⁻¹ * l = ρ := by
    have h1 : l * ρ * l = ρ⁻¹ := by
      rw [← h.l_rho, inv_eq_of_mul_eq_one_right h.l_sq]
    calc l * ρ⁻¹ * l = (l * ρ * l)⁻¹ := by
          rw [mul_inv_rev, mul_inv_rev, inv_eq_of_mul_eq_one_right h.l_sq]; group
      _ = ρ := by rw [h1, inv_inv]
  have hs : t ^ (a : ℕ) * τ ^ (b : ℕ) * l = w * l := by rw [hw]
  have hsK : w * l ∈ K := by rw [← hs]; exact hmem
  have hs_inv : (w * l)⁻¹ = l * w⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right h.l_sq]
  have hmain : ρ * (w * l) * ρ⁻¹ * (w * l)⁻¹ = ρ ^ 2 := by
    rw [hs_inv]
    rw [show ρ * (w * l) * ρ⁻¹ * (l * w⁻¹) =
      (ρ * w) * (l * ρ⁻¹ * l) * w⁻¹ by group]
    rw [hlρ]
    calc (ρ * w) * ρ * w⁻¹ = ρ * (w * ρ) * w⁻¹ := by group
      _ = ρ * (ρ * w) * w⁻¹ := by rw [hwρ]
      _ = (ρ * ρ) * w * w⁻¹ := by group
      _ = ρ ^ 2 := by rw [← pow_two, mul_assoc, mul_inv_cancel, mul_one]
  have hmem2 : ρ * (w * l) * ρ⁻¹ * (w * l)⁻¹ ∈ K :=
    K.mul_mem (h.rho_norm_K (w * l) hsK) (K.inv_mem hsK)
  rwa [hmain] at hmem2
private lemma word_mem_K_of_l (h : ZEData Q Y V V' B K ρ t τ l) {a b : Fin 2}
    (hmem : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ∈ K) : False :=
  rho_ne_one_contra h (rho_sq_mem_of_mem_K h hmem)
private lemma Y_le_V_of_mem_K (h : ZEData Q Y V V' B K ρ t τ l) {b : Fin 2}
    (hmem : t * τ ^ (b : ℕ) ∈ K) : Y ≤ V := by
  intro y hy
  have hsy : (t * τ ^ (b : ℕ)) * y = y * (t * τ ^ (b : ℕ)) := h.K_cent_Y _ hmem y hy
  have hty : t * y = y * t := by
    fin_cases b
    · simpa using hsy
    · have hτy : τ * y = y * τ := by
        have h1 : τ * y * τ⁻¹ = y⁻¹ := h.tau_inv y (h.Y_le_Q hy)
        have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (h.Y_sq y hy)
        rw [hyinv] at h1
        calc τ * y = (τ * y * τ⁻¹) * τ := by group
          _ = y * τ := by rw [h1]
      have hsy' : (t * τ) * y = y * (t * τ) := by simpa using hsy
      apply mul_right_cancel (b := τ)
      calc t * y * τ = t * (y * τ) := by group
        _ = t * (τ * y) := by rw [← hτy]
        _ = (t * τ) * y := by group
        _ = y * (t * τ) := hsy'
        _ = y * t * τ := by group
  exact h.Y_cent_t y hy hty
private lemma Y_le_V_contra (h : ZEData Q Y V V' B K ρ t τ l) (hYV : Y ≤ V) : False := by
  have hcard := Subgroup.card_le_of_le hYV
  rw [h.card_Y, h.card_V] at hcard
  omega
private lemma tau_mem_K_contra (h : ZEData Q Y V V' B K ρ t τ l) (hmem : τ ∈ K) : False := by
  have h1 : ρ * τ * ρ⁻¹ * τ⁻¹ = 1 := by rw [h.tau_rho.symm]; group
  exact h.tau_not_mem_Q (h.rho_fpf_KQ τ hmem (by rw [h1]; exact Q.one_mem))
theorem word_mem_K (h : ZEData Q Y V V' B K ρ t τ l) {a b c : Fin 2}
    (hmem : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) ∈ K) : a = 0 ∧ b = 0 ∧ c = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases c
  · exact ⟨rfl, rfl, rfl⟩
  · exact (word_mem_K_of_l h (a := 0) (b := 0) (by simpa using hmem)).elim
  · exact (tau_mem_K_contra h (by simpa using hmem)).elim
  · exact (word_mem_K_of_l h (a := 0) (b := 1) (by simpa using hmem)).elim
  · exact (Y_le_V_contra h (Y_le_V_of_mem_K h (b := 0) (by simpa using hmem))).elim
  · exact (word_mem_K_of_l h (a := 1) (b := 0) (by simpa using hmem)).elim
  · exact (Y_le_V_contra h (Y_le_V_of_mem_K h (b := 1) (by simpa using hmem))).elim
  · exact (word_mem_K_of_l h (a := 1) (b := 1) (by simpa using hmem)).elim
theorem T3_inf_K (h : ZEData Q Y V V' B K ρ t τ l) :
    ∀ s ∈ z4iT3 t τ l, s ∈ K → s = 1 := by
  intro s hs hsK
  obtain ⟨a, b, c, rfl⟩ := (mem_T3_iff h).mp hs
  obtain ⟨ha, hb, hc⟩ := word_mem_K h hsK
  rw [ha, hb, hc]
  simp
theorem card_T3 (h : ZEData Q Y V V' B K ρ t τ l) : Nat.card (z4iT3 t τ l) = 8 := by
  classical
  let f : Fin 2 × Fin 2 × Fin 2 → z4iT3 t τ l := fun p =>
    ⟨t ^ (p.1 : ℕ) * τ ^ (p.2.1 : ℕ) * l ^ (p.2.2 : ℕ),
      (mem_T3_iff h).mpr ⟨p.1, p.2.1, p.2.2, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ heq
      have hwords : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) =
          t ^ (a' : ℕ) * τ ^ (b' : ℕ) * l ^ (c' : ℕ) := congrArg Subtype.val heq
      have hunit : t ^ (a : ℕ) * τ ^ (b : ℕ) * l ^ (c : ℕ) *
          (t ^ (a' : ℕ) * τ ^ (b' : ℕ) * l ^ (c' : ℕ)) = 1 := by
        rw [hwords, word_sq h a' b' c']
      have hword : t ^ ((a + a' : Fin 2) : ℕ) * τ ^ ((b + b' : Fin 2) : ℕ) *
          l ^ ((c + c' : Fin 2) : ℕ) = 1 := by
        rw [← word_mul h a b c a' b' c']
        exact hunit
      have hK : t ^ ((a + a' : Fin 2) : ℕ) * τ ^ ((b + b' : Fin 2) : ℕ) *
          l ^ ((c + c' : Fin 2) : ℕ) ∈ K := by
        rw [hword]; exact K.one_mem
      obtain ⟨haa, hbb, hcc⟩ := word_mem_K h hK
      exact Prod.ext (fin2_add_eq_zero haa)
        (Prod.ext (fin2_add_eq_zero hbb) (fin2_add_eq_zero hcc))
    · rintro ⟨x, hx⟩
      obtain ⟨a, b, c, rfl⟩ := (mem_T3_iff h).mp hx
      exact ⟨(a, b, c), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card]
  norm_num [Fintype.card_prod]
end ZEData
end CFSG.OddStandard.SmallF3.HarrisU33.S4B
