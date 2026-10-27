module

public import CFSG.GH74.GLS.Stage4.T6Fields

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

structure T6RFacts (N : T2N3 G) (p : ℕ) : Prop where
  card : Nat.card ↥(R₂ N p) = N.q₁ ^ 2 * N.q₂ ^ 3
  center : ∀ y ∈ R₂ N p, (∀ x ∈ R₂ N p, x * y = y * x) ↔ y ∈ N.X₂
  irred : ∀ V : Subgroup G, N.X₂ ≤ V → V ≤ R₂ N p → (∀ x ∈ N.K₁, ∀ v ∈ V, x * v * x⁻¹ ∈ V) →
    V = N.X₂ ∨ V = R₂ N p

theorem t6RFacts_of (h11b : IVK_11_1b_nat) (h : T6Ctx N u p) {y : G} {R : Subgroup G}
    (hTS : T6TSdata N p y R) (hRle : R ≤ R₂ N p) : T6RFacts N p := by
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  have hMod := t6Mod_of h11b h hm
  have hy1 : y ≠ 1 := fun e => hTS.y_ne (e ▸ Subgroup.one_mem _)
  exact ⟨R₂_order h hm hn hMod hTS.yK hy1 hTS.y_ord hRle hTS.R_card hTS.y_cent,
    R₂_center_of h hm hn hMod hTS.yK hy1 hTS.y_ord hRle hTS.R_card hTS.y_cent hTS.X_comm,
    K₁_irred_of h hm hn hMod hTS.yK hy1 hTS.y_ord hRle hTS.R_card hTS.y_cent⟩

omit [Finite G] in
theorem t6_mem_sup_of_le_normalizer {A B : Subgroup G} (hB : B ≤ Subgroup.normalizer (A : Set G))
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, x = a * b := by
  have hn : ∀ b ∈ B, ∀ a ∈ A, b * a * b⁻¹ ∈ A := fun b hb a ha =>
    (Subgroup.mem_normalizer_iff.1 (hB hb) a).1 ha
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact ⟨y, hy, 1, B.one_mem, by simp⟩
    · exact ⟨1, A.one_mem, y, hy, by simp⟩
  | one => exact ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hy
    refine ⟨a * (b * a' * b⁻¹), A.mul_mem ha (hn b hb a' ha'), b * b', B.mul_mem hb hb', ?_⟩
    group
  | inv x _ hx =>
    obtain ⟨a, ha, b, hb, rfl⟩ := hx
    refine ⟨b⁻¹ * a⁻¹ * b, ?_, b⁻¹, B.inv_mem hb, ?_⟩
    · have := hn b⁻¹ (B.inv_mem hb) a⁻¹ (A.inv_mem ha)
      simpa using this
    · group

theorem F_cent_z (h : T6Ctx N u p) {f : G} (hf : f ∈ N.F) : f * N.z = N.z * f :=
  h.FS f hf _ h.sec5.loc.z_mem_S

theorem F_cent_u (h : T6Ctx N u p) {f : G} (hf : f ∈ N.F) : f * u = u * f :=
  h.FS f hf _ h.sec5.loc.u_mem_S

theorem X₂_le_K₂ (h : T6Ctx N u p) : N.X₂ ≤ N.K₂ := by
  rw [h.sec5.loc.K₂_eq]; exact le_sup_left

theorem z_cent_X₁ (h : T6Ctx N u p) {x : G} (hx : x ∈ N.X₁) : x * N.z = N.z * x :=
  h.zK x (Subgroup.mem_sup_left (X₁_le_K₁ h hx))

theorem z_cent_X₂ (h : T6Ctx N u p) {x : G} (hx : x ∈ N.X₂) : x * N.z = N.z * x :=
  h.zK x (Subgroup.mem_sup_right (X₂_le_K₂ h hx))

theorem X₁_inf_X₂ (h : T6Ctx N u p) : N.X₁ ⊓ N.X₂ = ⊥ := by
  have hX₁p : IsPGroup p ↥N.X₁ := by
    obtain ⟨m, hm⟩ := h.q₁_pow
    exact IsPGroup.of_card (n := m) (by rw [h.sec5.loc.card_X₁, hm])
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  rcases t2C_zpowers_cases h.ctx.zz (h.sec5.loc.K_inter ⟨X₁_le_K₁ h hx.1, X₂_le_K₂ h hx.2⟩) with h1 | h1
  · exact h1
  · exact absurd (h1 ▸ hx.1) (z_not_mem_pGroup h hX₁p)

theorem U_cases (h : T6Ctx N u p) {g : G} (hg : g ∈ t2U N.z u) :
    g = 1 ∨ g = N.z ∨ g = u ∨ g = N.z * u := by
  obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
  exact (t2U_mem hz2 hu2 hzu).1 hg

theorem U_norm_X₁ (h : T6Ctx N u p) {g : G} (hg : g ∈ t2U N.z u) {x : G} (hx : x ∈ N.X₁) :
    g * x * g⁻¹ ∈ N.X₁ := by
  have hz2 := h.ctx.zz
  have hzx := z_cent_X₁ h hx
  have hzc : N.z * x * N.z⁻¹ = x := by
    calc N.z * x * N.z⁻¹ = (x * N.z) * N.z⁻¹ := by rw [hzx]
      _ = x := by group
  have hui := h.sec5.loc.u_inv_X₁ x hx
  rcases U_cases h hg with rfl | rfl | rfl | rfl
  · simpa using hx
  · rw [hzc]; exact hx
  · rw [hui]; exact N.X₁.inv_mem hx
  · have : N.z * u * x * (N.z * u)⁻¹ = N.z * (u * x * u⁻¹) * N.z⁻¹ := by group
    rw [this, hui]
    have : N.z * x⁻¹ * N.z⁻¹ = x⁻¹ := by
      calc N.z * x⁻¹ * N.z⁻¹ = (N.z * x * N.z⁻¹)⁻¹ := by group
        _ = x⁻¹ := by rw [hzc]
    rw [this]; exact N.X₁.inv_mem hx

theorem U_cent_F (h : T6Ctx N u p) {g : G} (hg : g ∈ t2U N.z u) {f : G} (hf : f ∈ N.F) :
    g * f * g⁻¹ = f := by
  have hz := F_cent_z h hf
  have hu := F_cent_u h hf
  have hzc : N.z * f * N.z⁻¹ = f := by
    calc N.z * f * N.z⁻¹ = (f * N.z) * N.z⁻¹ := by rw [hz]
      _ = f := by group
  have huc : u * f * u⁻¹ = f := by
    calc u * f * u⁻¹ = (f * u) * u⁻¹ := by rw [hu]
      _ = f := by group
  rcases U_cases h hg with rfl | rfl | rfl | rfl
  · simp
  · exact hzc
  · exact huc
  · have : N.z * u * f * (N.z * u)⁻¹ = N.z * (u * f * u⁻¹) * N.z⁻¹ := by group
    rw [this, huc, hzc]

theorem X₁_le_normalizer_R₂ (h : T6Ctx N u p) : N.X₁ ≤ Subgroup.normalizer (R₂ N p : Set G) :=
  fun _ hg => Subgroup.mem_normalizer_fintype
    (fun _ hn => R₂_norm N p (K₁_le_M₂ h (X₁_le_K₁ h hg)) hn)

theorem R₂_disjoint_X₁ (h : T6Ctx N u p) : Disjoint (R₂ N p) N.X₁ := by
  rw [disjoint_iff, eq_bot_iff, ← R₂_inf_K₁ h]
  exact inf_le_inf_left _ (X₁_le_K₁ h)

theorem P_card (h : T6Ctx N u p) (hR : T6RFacts N p) :
    Nat.card ↥(R₂ N p ⊔ N.X₁) = N.q₁ ^ 3 * N.q₂ ^ 3 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (X₁_le_normalizer_R₂ h) (R₂_disjoint_X₁ h), hR.card, h.sec5.loc.card_X₁]
  ring

theorem F_norm_P (h : T6Ctx N u p) {f : G} (hf : f ∈ N.F) :
    ∀ x ∈ R₂ N p ⊔ N.X₁, f * x * f⁻¹ ∈ R₂ N p ⊔ N.X₁ :=
  t6_norm_sup (fun _ hr => R₂_norm N p (F_le_M₂ h hf) hr)
    (fun x hx => h.sec5.F5.F_normX₁ f hf x hx)

theorem P_inf_F (h : T6Ctx N u p) : (R₂ N p ⊔ N.X₁) ⊓ N.F = ⊥ := by
  rw [eq_bot_iff]
  rintro f ⟨hfP, hfF⟩
  rw [Subgroup.mem_bot]
  obtain ⟨r, hr, x, hx, rfl⟩ := t6_mem_sup_of_le_normalizer (X₁_le_normalizer_R₂ h) hfP
  have hzf := F_cent_z h hfF
  have hzx := z_cent_X₁ h hx
  have hrz : N.z * r * N.z⁻¹ = r := by
    have h1 : N.z * (r * x) * N.z⁻¹ = r * x := by
      calc N.z * (r * x) * N.z⁻¹ = (r * x * N.z) * N.z⁻¹ := by rw [← hzf]
        _ = r * x := by group
    have hzxc : N.z * x * N.z⁻¹ = x := by
      calc N.z * x * N.z⁻¹ = (x * N.z) * N.z⁻¹ := by rw [hzx]
        _ = x := by group
    have h2 : N.z * (r * x) * N.z⁻¹ = (N.z * r * N.z⁻¹) * x := by
      calc N.z * (r * x) * N.z⁻¹ = (N.z * r * N.z⁻¹) * (N.z * x * N.z⁻¹) := by group
        _ = (N.z * r * N.z⁻¹) * x := by rw [hzxc]
    rw [h2] at h1
    exact mul_right_cancel h1
  have hrX : r ∈ N.X₂ := R₂_Cz h r hr hrz
  have hK : r * x ∈ N.K₁ ⊔ N.K₂ :=
    Subgroup.mul_mem _ (Subgroup.mem_sup_right (X₂_le_K₂ h hrX))
      (Subgroup.mem_sup_left (X₁_le_K₁ h hx))
  have : r * x ∈ N.F ⊓ (N.K₁ ⊔ N.K₂) := ⟨hfF, hK⟩
  rw [h.sec5.F5.F_inter_K, Subgroup.mem_bot] at this
  exact this

theorem Pst_card (h : T6Ctx N u p) (hR : T6RFacts N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) :
    Nat.card ↥(R₂ N p ⊔ N.X₁ ⊔ P₀) = N.q₁ ^ 3 * N.q₂ ^ 3 * Nat.card ↥P₀ := by
  have hnorm : P₀ ≤ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ : Subgroup G) : Set G) := fun f hf =>
    Subgroup.mem_normalizer_fintype (fun x hx => F_norm_P h (hP₀F hf) x hx)
  have hdisj : Disjoint (R₂ N p ⊔ N.X₁) P₀ := by
    rw [disjoint_iff, eq_bot_iff]
    intro x hx
    have h1 : x ∈ (R₂ N p ⊔ N.X₁) ⊓ N.F := ⟨hx.1, hP₀F hx.2⟩
    rw [P_inf_F h] at h1
    exact h1
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _ hnorm hdisj, P_card h hR]

theorem Pst_pGroup (h : T6Ctx N u p) (hR : T6RFacts N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    (hP₀p : IsPGroup p ↥P₀) : IsPGroup p ↥(R₂ N p ⊔ N.X₁ ⊔ P₀) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := hP₀p.exists_card_eq
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  refine IsPGroup.of_card (n := 3 * m + 3 * n + k) ?_
  rw [Pst_card h hR hP₀F, hk, hm, hn]
  ring

theorem P_normU (h : T6Ctx N u p) {g : G} (hg : g ∈ t2U N.z u) :
    ∀ k ∈ R₂ N p ⊔ N.X₁, g * k * g⁻¹ ∈ R₂ N p ⊔ N.X₁ :=
  t6_norm_sup (fun _ hr => R₂_norm N p (U_le_M₂ h hg) hr) (fun _ hx => U_norm_X₁ h hg hx)

theorem Pst_normU (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {g : G}
    (hg : g ∈ t2U N.z u) : ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, g * k * g⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀ := by
  refine t6_norm_sup (P_normU h hg) (fun f hf => ?_)
  rw [U_cent_F h hg (hP₀F hf)]; exact hf

theorem X₁_faithful (h : T6Ctx N u p) (hR : T6RFacts N p) {x : G} (hx : x ∈ N.X₁)
    (hxc : ∀ s ∈ R₂ N p, x * s * x⁻¹ * s⁻¹ ∈ N.X₂) : x = 1 := by
  have hpR := R₂_pGroup N h.prime
  have hX₂R := X₂_le_R₂ h
  have hX₁p : IsPGroup p ↥N.X₁ := by
    obtain ⟨m, hm⟩ := h.q₁_pow
    exact IsPGroup.of_card (n := m) (by rw [h.sec5.loc.card_X₁, hm])
  let Kker : Subgroup G :=
    { carrier := {k | k ∈ N.K₁ ∧ ∀ s ∈ R₂ N p, k * s * k⁻¹ * s⁻¹ ∈ N.X₂}
      mul_mem' := by
        rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
        refine ⟨N.K₁.mul_mem haK hbK, fun s hs => ?_⟩
        have h1 := hb s hs
        have h2 := ha s hs
        have h3 : a * (b * s * b⁻¹ * s⁻¹) * a⁻¹ = b * s * b⁻¹ * s⁻¹ := by
          rw [K₁_cent_X₂ h haK h1]
        have e : a * b * s * (a * b)⁻¹ * s⁻¹ =
            (a * (b * s * b⁻¹ * s⁻¹) * a⁻¹) * (a * s * a⁻¹ * s⁻¹) := by group
        rw [e, h3]
        exact N.X₂.mul_mem h1 h2
      one_mem' := ⟨N.K₁.one_mem, fun s _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haK, ha⟩
        refine ⟨N.K₁.inv_mem haK, fun s hs => ?_⟩
        have hs' : a⁻¹ * s * a ∈ R₂ N p := by
          have := R₂_norm N p (K₁_le_M₂ h (N.K₁.inv_mem haK)) hs
          simpa using this
        have h1 := ha _ hs'
        have e : a * (a⁻¹ * s * a) * a⁻¹ * (a⁻¹ * s * a)⁻¹ = (a⁻¹ * s * a * s⁻¹)⁻¹ := by group
        rw [e] at h1
        have := N.X₂.inv_mem h1
        simpa using this }
  have hKker : ∀ k ∈ Kker, k ∈ N.K₁ := fun k hk => hk.1
  have hQ := h.ctx.C.Q₁ Kker (fun k hk => hk.1) (fun k hk n hn => by
    refine ⟨N.K₁.mul_mem (N.K₁.mul_mem hk N.K₁.one_mem) (N.K₁.inv_mem hk) |> fun _ => ?_, fun s hs => ?_⟩
    · exact N.K₁.mul_mem (N.K₁.mul_mem hk hn.1) (N.K₁.inv_mem hk)
    · have hs' : k⁻¹ * s * k ∈ R₂ N p := by
        have := R₂_norm N p (K₁_le_M₂ h (N.K₁.inv_mem hk)) hs
        simpa using this
      have h1 := hn.2 _ hs'
      have h2 : k * (n * (k⁻¹ * s * k) * n⁻¹ * (k⁻¹ * s * k)⁻¹) * k⁻¹ = k * n * k⁻¹ * s * (k * n * k⁻¹)⁻¹ * s⁻¹ := by
        group
      rw [← h2, K₁_cent_X₂ h hk h1]
      exact h1)
  rcases hQ with hle | hle
  ·
    have hxK : x ∈ Kker := ⟨X₁_le_K₁ h hx, hxc⟩
    rcases t2C_zpowers_cases h.ctx.zz (hle hxK) with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ hx) (z_not_mem_pGroup h hX₁p)
  ·
    exfalso
    have hz : N.z ∈ Kker := hle h.sec5.loc.z_mem_K₁
    have hsq : ∀ s ∈ R₂ N p, s ∈ N.X₂ := by
      intro s hs
      have h1 := hz.2 s hs
      have h2 := (R₂_inv_comm h).1 s hs
      have h3 : s * s ∈ N.X₂ := by
        have := N.X₂.mul_mem (N.X₂.inv_mem h1) h2
        have e : (N.z * s * N.z⁻¹ * s⁻¹)⁻¹ * (N.z * s * N.z⁻¹ * s) = s * s := by group
        rwa [e] at this
      have hp := R₂_exp h s hs
      have hpodd : Odd p := h.prime.odd_of_ne_two h.p_ne_two
      obtain ⟨j, hj⟩ := hpodd
      have e : s = s ^ p * (s * s) ^ (-(j : ℤ)) := by
        rw [hj, zpow_neg, zpow_natCast, ← pow_two, ← pow_mul]
        have : s ^ (2 * j + 1) = s ^ (2 * j) * s := pow_succ s (2 * j)
        rw [this]
        group
      rw [e]
      exact N.X₂.mul_mem hp (N.X₂.zpow_mem h3 _)
    have hle2 : R₂ N p ≤ N.X₂ := hsq
    have := Subgroup.card_le_of_le hle2
    rw [hR.card, h.sec5.loc.card_X₂] at this
    have h5 := h.sec5.loc.q₁_ge
    have h3 := h.sec5.loc.q₂_ge
    have hq : 0 < N.q₁ := by omega
    have h2 : N.q₂ < N.q₂ ^ 3 := by
      calc N.q₂ = N.q₂ ^ 1 := (pow_one _).symm
        _ < N.q₂ ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    have h4 : N.q₂ ^ 3 ≤ N.q₁ ^ 2 * N.q₂ ^ 3 := Nat.le_mul_of_pos_left _ (pow_pos hq 2)
    omega

omit [Finite G] in
theorem t6_sq_root {x : G} (hx : Odd (orderOf x)) : ∃ k : ℕ, x ^ k * x ^ k = x := by
  obtain ⟨j, hj⟩ := hx
  refine ⟨j + 1, ?_⟩
  have h1 : x ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
  rw [← pow_add, show j + 1 + (j + 1) = (2 * j + 1) + 1 by ring, pow_succ, h1, one_mul]

omit [Finite G] in
theorem t6_conj_mem_commutator {A B : Subgroup G} {x : G} (hA : ∀ a ∈ A, x * a * x⁻¹ ∈ A)
    (hB : ∀ b ∈ B, x * b * x⁻¹ ∈ B) {l : G} (hl : l ∈ ⁅A, B⁆) : x * l * x⁻¹ ∈ ⁅A, B⁆ := by
  let f : G →* G := (MulAut.conj x).toMonoidHom
  have h1 : f l ∈ (⁅A, B⁆).map f := Subgroup.mem_map_of_mem f hl
  rw [Subgroup.map_commutator] at h1
  have hAf : A.map f ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA a ha
  have hBf : B.map f ≤ B := by
    rintro _ ⟨b, hb, rfl⟩
    exact hB b hb
  exact Subgroup.commutator_mono hAf hBf h1

theorem X₁_le_comm (h : T6Ctx N u p) {P₀ : Subgroup G} :
    N.X₁ ≤ ⁅R₂ N p ⊔ N.X₁ ⊔ P₀, t2U N.z u⁆ := by
  have hX₁p : IsPGroup p ↥N.X₁ := by
    obtain ⟨m, hm⟩ := h.q₁_pow
    exact IsPGroup.of_card (n := m) (by rw [h.sec5.loc.card_X₁, hm])
  intro x hx
  obtain ⟨k, hk⟩ := t6_sq_root (t6_odd_of_pGroup h.prime h.p_ne_two hX₁p hx)
  have hxk : x ^ k ∈ N.X₁ := N.X₁.pow_mem hx k
  have hinv := h.sec5.loc.u_inv_X₁ _ hxk
  have hu : u ∈ t2U N.z u := by
    obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
    exact (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hc : ⁅x ^ k, u⁆ = x := by
    rw [commutatorElement_def]
    calc x ^ k * u * (x ^ k)⁻¹ * u⁻¹ = x ^ k * (u * x ^ k * u⁻¹)⁻¹ := by group
      _ = x ^ k * x ^ k := by rw [hinv, inv_inv]
      _ = x := hk
  rw [← hc]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left (Subgroup.mem_sup_right hxk)) hu

theorem X₂_le_comm (h : T6Ctx N u p) {P₀ : Subgroup G} :
    N.X₂ ≤ ⁅R₂ N p ⊔ N.X₁ ⊔ P₀, t2U N.z u⁆ := by
  intro x hx
  obtain ⟨k, hk⟩ := t6_sq_root (t6_odd_of_pGroup h.prime h.p_ne_two (R₂_pGroup N h.prime) (X₂_le_R₂ h hx))
  have hxk : x ^ k ∈ N.X₂ := N.X₂.pow_mem hx k
  have hinv := h.sec5.loc.u_inv_X₂ _ hxk
  have hu : u ∈ t2U N.z u := by
    obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
    exact (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inr (Or.inl rfl)))
  have hc : ⁅x ^ k, u⁆ = x := by
    rw [commutatorElement_def]
    calc x ^ k * u * (x ^ k)⁻¹ * u⁻¹ = x ^ k * (u * x ^ k * u⁻¹)⁻¹ := by group
      _ = x ^ k * x ^ k := by rw [hinv, inv_inv]
      _ = x := hk
  rw [← hc]
  exact Subgroup.commutator_mem_commutator
    (Subgroup.mem_sup_left (Subgroup.mem_sup_left (X₂_le_R₂ h hxk))) hu

theorem R₂_le_comm (h : T6Ctx N u p) {P₀ : Subgroup G} :
    R₂ N p ≤ ⁅R₂ N p ⊔ N.X₁ ⊔ P₀, t2U N.z u⁆ := by
  intro r hr
  have hz : N.z ∈ t2U N.z u := by
    obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
    exact (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inl rfl))
  obtain ⟨j, hj⟩ := h.prime.odd_of_ne_two h.p_ne_two
  have hr' : r ^ (j + 1) ∈ R₂ N p := (R₂ N p).pow_mem hr _
  have ha : r ^ p ∈ N.X₂ := R₂_exp h r hr
  have hb := (R₂_inv_comm h).1 _ ((R₂ N p).inv_mem hr')
  set r' := r ^ (j + 1) with hr'def
  set b : G := N.z * r'⁻¹ * N.z⁻¹ * r'⁻¹ with hbdef
  have hbc : r' * b = b * r' := by
    have := R₂_cent h r' hr' b hb
    calc r' * b = (r' * b * r'⁻¹) * r' := by group
      _ = b * r' := by rw [this]
  have hrr : r' * r' = r ^ p * r := by
    rw [hr'def, ← pow_add, hj, ← pow_succ]
    congr 1
    ring
  have e1 : N.z * r'⁻¹ * N.z⁻¹ = b * r' := by rw [hbdef]; group
  have hcomm : ⁅r', N.z⁆ = (b * r ^ p) * r := by
    calc ⁅r', N.z⁆ = r' * (N.z * r'⁻¹ * N.z⁻¹) := by rw [commutatorElement_def]; group
      _ = r' * (b * r') := by rw [e1]
      _ = b * (r' * r') := by rw [← mul_assoc, hbc, mul_assoc]
      _ = (b * r ^ p) * r := by rw [hrr]; group
  have hL : ⁅r', N.z⁆ ∈ ⁅R₂ N p ⊔ N.X₁ ⊔ P₀, t2U N.z u⁆ :=
    Subgroup.commutator_mem_commutator
      (Subgroup.mem_sup_left (Subgroup.mem_sup_left hr')) hz
  have hX := X₂_le_comm h (P₀ := P₀) (N.X₂.mul_mem hb ha)
  have : r = (b * r ^ p)⁻¹ * ⁅r', N.z⁆ := by rw [hcomm]; group
  rw [this]
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hX) hL

theorem comm_le_P (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) :
    ⁅R₂ N p ⊔ N.X₁ ⊔ P₀, t2U N.z u⁆ ≤ R₂ N p ⊔ N.X₁ := by
  rw [Subgroup.commutator_le]
  intro g hg v hv
  have hnorm : P₀ ≤ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ : Subgroup G) : Set G) := fun f hf =>
    Subgroup.mem_normalizer_fintype (fun x hx => F_norm_P h (hP₀F hf) x hx)
  obtain ⟨a, ha, f, hf, rfl⟩ := t6_mem_sup_of_le_normalizer hnorm hg
  have hvf := U_cent_F h hv (hP₀F hf)
  have hfv : f * v * f⁻¹ = v := by
    have h1 : v * f = f * v := by
      calc v * f = (v * f * v⁻¹) * v := by group
        _ = f * v := by rw [hvf]
    rw [← h1]; group
  have hc : ⁅a * f, v⁆ = a * (v * a⁻¹ * v⁻¹) := by
    rw [commutatorElement_def]
    calc a * f * v * (a * f)⁻¹ * v⁻¹ = a * (f * v * f⁻¹) * a⁻¹ * v⁻¹ := by group
      _ = a * v * a⁻¹ * v⁻¹ := by rw [hfv]
      _ = a * (v * a⁻¹ * v⁻¹) := by group
  rw [hc]
  exact Subgroup.mul_mem _ ha (P_normU h hv a⁻¹ ((R₂ N p ⊔ N.X₁).inv_mem ha))

theorem comm_eq_P (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) :
    ⁅R₂ N p ⊔ N.X₁ ⊔ P₀, t2U N.z u⁆ = R₂ N p ⊔ N.X₁ :=
  le_antisymm (comm_le_P h hP₀F) (sup_le (R₂_le_comm h) (X₁_le_comm h))

theorem norm_P_of (h : T6Ctx N u p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {x : G}
    (hxP : ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, x * k * x⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀)
    (hxU : ∀ g ∈ t2U N.z u, x * g * x⁻¹ ∈ t2U N.z u) :
    ∀ k ∈ R₂ N p ⊔ N.X₁, x * k * x⁻¹ ∈ R₂ N p ⊔ N.X₁ := by
  intro k hk
  rw [← comm_eq_P h hP₀F] at hk ⊢
  exact t6_conj_mem_commutator hxP hxU hk

theorem P_center_eq (h : T6Ctx N u p) (hR : T6RFacts N p) :
    ∀ y ∈ R₂ N p ⊔ N.X₁, (∀ x ∈ R₂ N p ⊔ N.X₁, x * y = y * x) ↔ y ∈ N.X₂ := by
  intro y hy
  constructor
  · intro hcen
    obtain ⟨r, hr, x₀, hx₀, rfl⟩ := t6_mem_sup_of_le_normalizer (X₁_le_normalizer_R₂ h) hy
    have hx₀1 : x₀ = 1 := by
      refine X₁_faithful h hR hx₀ (fun s hs => ?_)
      have hys : r * x₀ * s = s * (r * x₀) :=
        (hcen s (Subgroup.mem_sup_left hs)).symm
      have h1 : (r * x₀) * s * (r * x₀)⁻¹ = s := by
        calc (r * x₀) * s * (r * x₀)⁻¹ = (s * (r * x₀)) * (r * x₀)⁻¹ := by rw [hys]
          _ = s := by group
      have h2 : x₀ * s * x₀⁻¹ * s⁻¹ = ⁅r⁻¹, s⁆ := by
        rw [commutatorElement_def]
        calc x₀ * s * x₀⁻¹ * s⁻¹ = r⁻¹ * ((r * x₀) * s * (r * x₀)⁻¹) * r * s⁻¹ := by group
          _ = r⁻¹ * s * r⁻¹⁻¹ * s⁻¹ := by rw [h1]; group
      rw [h2]
      exact (R₂_inv_comm h).2 _ ((R₂ N p).inv_mem hr) s hs
    subst hx₀1
    rw [mul_one] at hcen ⊢
    exact (hR.center r hr).1 (fun x hx => hcen x (Subgroup.mem_sup_left hx))
  · intro hyX x hx
    obtain ⟨a, ha, w, hw, rfl⟩ := t6_mem_sup_of_le_normalizer (X₁_le_normalizer_R₂ h) hx
    have h1 : a * y = y * a := by
      have := R₂_cent h a ha y hyX
      calc a * y = (a * y * a⁻¹) * a := by group
        _ = y * a := by rw [this]
    have h2 : w * y = y * w := by
      have hwK := X₁_le_K₁ h hw
      have hyK : y ∈ N.K₂ := X₂_le_K₂ h hyX
      exact h.sec5.loc.K_comm w hwK y hyK
    calc a * w * y = a * (w * y) := by group
      _ = a * (y * w) := by rw [h2]
      _ = (a * y) * w := by group
      _ = (y * a) * w := by rw [h1]
      _ = y * (a * w) := by group

theorem norm_X₂_of (h : T6Ctx N u p) (hR : T6RFacts N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {x : G}
    (hxP : x ∈ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hxU : x ∈ Subgroup.normalizer ((t2U N.z u : Subgroup G) : Set G)) :
    ∀ w ∈ N.X₂, x * w * x⁻¹ ∈ N.X₂ := by
  have hxP1 : ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, x * k * x⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀ := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 hxP k).1 hk
  have hxU1 : ∀ g ∈ t2U N.z u, x * g * x⁻¹ ∈ t2U N.z u := fun g hg =>
    (Subgroup.mem_normalizer_iff.1 hxU g).1 hg
  have hxP2 : ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, x⁻¹ * k * x⁻¹⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀ := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hxP) k).1 hk
  have hxU2 : ∀ g ∈ t2U N.z u, x⁻¹ * g * x⁻¹⁻¹ ∈ t2U N.z u := fun g hg =>
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hxU) g).1 hg
  have hP := norm_P_of h hP₀F hxP1 hxU1
  have hP' := norm_P_of h hP₀F hxP2 hxU2
  intro w hw
  have hwP : w ∈ R₂ N p ⊔ N.X₁ := Subgroup.mem_sup_left (X₂_le_R₂ h hw)
  refine (P_center_eq h hR _ (hP w hwP)).1 (fun k hk => ?_)
  have hk' : x⁻¹ * k * x⁻¹⁻¹ ∈ R₂ N p ⊔ N.X₁ := hP' k hk
  have hwc := (P_center_eq h hR w hwP).2 hw _ hk'
  simp only [inv_inv] at hk' hwc
  calc k * (x * w * x⁻¹) = x * ((x⁻¹ * k * x) * w) * x⁻¹ := by group
    _ = x * (w * (x⁻¹ * k * x)) * x⁻¹ := by rw [hwc]
    _ = (x * w * x⁻¹) * k := by group

end CFSG.GH74.GLS.Stage4.Rest.T6
