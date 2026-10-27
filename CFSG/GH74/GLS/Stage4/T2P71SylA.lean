module

public import CFSG.GH74.GLS.Stage4.T6SylM

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

structure RCard (N : T2N3 G) (p : ℕ) : Prop where
  card : Nat.card ↥(R₂ N p) = N.q₁ ^ 2 * N.q₂ ^ 3

theorem P_card (h : T6Ctx N u p) (hR : RCard N p) :
    Nat.card ↥(R₂ N p ⊔ N.X₁) = N.q₁ ^ 3 * N.q₂ ^ 3 := by
  rw [CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ _
    (X₁_le_normalizer_R₂ h) (R₂_disjoint_X₁ h), hR.card, h.sec5.loc.card_X₁]
  ring


theorem Pst_card (h : T6Ctx N u p) (hR : RCard N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) :
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


theorem Pst_pGroup (h : T6Ctx N u p) (hR : RCard N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    (hP₀p : IsPGroup p ↥P₀) : IsPGroup p ↥(R₂ N p ⊔ N.X₁ ⊔ P₀) := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨k, hk⟩ := hP₀p.exists_card_eq
  obtain ⟨m, hm⟩ := h.q₁_pow
  obtain ⟨n, hn⟩ := h.q₂_pow
  refine IsPGroup.of_card (n := 3 * m + 3 * n + k) ?_
  rw [Pst_card h hR hP₀F, hk, hm, hn]
  ring


theorem X₁_faithful (h : T6Ctx N u p) (hR : RCard N p) {x : G} (hx : x ∈ N.X₁)
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


theorem card_RA (h : T6Ctx N u p) (hR : RCard N p) : Nat.card ↥(RA N p u) = N.q₁ * N.q₂ := by
  have h1 : N.q₂ * Nat.card ↥(RA N p u) ^ 2 = N.q₁ ^ 2 * N.q₂ ^ 3 := by
    rw [← R₂_card_RA h, hR.card]
  have hq₂ : 0 < N.q₂ := by have := h.sec5.loc.q₂_ge; omega
  have h2 : Nat.card ↥(RA N p u) ^ 2 = (N.q₁ * N.q₂) ^ 2 := by
    apply Nat.eq_of_mul_eq_mul_left hq₂
    calc N.q₂ * Nat.card ↥(RA N p u) ^ 2 = N.q₁ ^ 2 * N.q₂ ^ 3 := h1
      _ = N.q₂ * (N.q₁ * N.q₂) ^ 2 := by ring
  exact Nat.pow_left_injective (by norm_num) h2


theorem card_RB (h : T6Ctx N u p) (hR : RCard N p) : Nat.card ↥(RB N p u) = N.q₁ * N.q₂ := by
  rw [RA_card_eq_RB h, card_RA h hR]


theorem exists_sub_Cv (h : T6Ctx N u p) (hR : RCard N p) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    {v : G} (hv : v = N.z ∨ v = u ∨ v = N.z * u) :
    ∃ D : Subgroup G, D ≤ R₂ N p ⊔ N.X₁ ⊔ P₀ ∧ D ≤ Subgroup.centralizer ({v} : Set G) ∧
      Nat.card ↥D = N.q₁ * N.q₂ * Nat.card ↥P₀ := by
  have hR₂P : R₂ N p ≤ R₂ N p ⊔ N.X₁ ⊔ P₀ := le_sup_left.trans le_sup_left
  rcases hv with hv | hv | hv
  · subst v
    refine ⟨N.X₁ ⊔ N.X₂ ⊔ P₀, ?_, ?_, card_Y h hP₀F⟩
    · refine sup_le (sup_le ?_ ?_) le_sup_right
      · exact (le_sup_right : N.X₁ ≤ R₂ N p ⊔ N.X₁).trans le_sup_left
      · exact (X₂_le_R₂ h).trans hR₂P
    · refine sup_le (sup_le ?_ ?_) ?_
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₁ h hx)
      · intro x hx
        exact Subgroup.mem_centralizer_singleton_iff.2 (z_cent_X₂ h hx)
      · intro f hf
        exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_z h (hP₀F hf))
  · subst v
    refine ⟨RA N p u ⊔ P₀, sup_le (inf_le_left.trans hR₂P) le_sup_right, ?_, ?_⟩
    · refine sup_le inf_le_right ?_
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_u h (hP₀F hf))
    · rw [card_sup_P₀ h hP₀F (fun f hf => F_cent_u h hf)]
      exact congrArg (· * Nat.card ↥P₀) (card_RA h hR)
  · subst v
    refine ⟨RB N p u ⊔ P₀, sup_le (inf_le_left.trans hR₂P) le_sup_right, ?_, ?_⟩
    · refine sup_le inf_le_right ?_
      intro f hf
      exact Subgroup.mem_centralizer_singleton_iff.2 (F_cent_zu h (hP₀F hf))
    · rw [card_sup_P₀ h hP₀F (fun f hf => F_cent_zu h hf)]
      exact congrArg (· * Nat.card ↥P₀) (card_RB h hR)


theorem card_Cv_Pst (h : T6Ctx N u p) (hR : RCard N p) {m n : ℕ} (hm : N.q₁ = p ^ m)
    (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) {v : G}
    (hv : v = N.z ∨ v = u ∨ v = N.z * u) :
    Nat.card ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G)) =
      N.q₁ * N.q₂ * Nat.card ↥P₀ := by
  obtain ⟨D, hDP, hDC, hDc⟩ := exists_sub_Cv h hR hP₀F hv
  have h1 : Nat.card ↥D ≤ Nat.card ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G)) :=
    Subgroup.card_le_of_le (le_inf hDP hDC)
  have h2 := card_pSub_Cv_le h hm hn hP₀c hv (inf_le_right :
    (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G) ≤ _)
    ((Pst_pGroup h hR hP₀F hP₀p).to_le inf_le_left)
  omega


theorem Pst_max_U (h : T6Ctx N u p) (hR : RCard N p) {m n : ℕ} (hm : N.q₁ = p ^ m)
    (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) {Q : Subgroup G}
    (hQp : IsPGroup p ↥Q)
    (hQM : Q ≤ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hQU : ∀ g ∈ t2U N.z u, ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) : Q ≤ R₂ N p ⊔ N.X₁ ⊔ P₀ := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hPp := Pst_pGroup h hR hP₀F hP₀p
  have hQ'p : IsPGroup p ↥(Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) := hQp.to_sup_of_normal_right' hPp hQM
  have hodd : ∀ K : Subgroup G, IsPGroup p ↥K → Odd (Nat.card ↥K) := by
    intro K hK
    obtain ⟨k, hk⟩ := hK.exists_card_eq
    rw [hk]
    exact (h.prime.odd_of_ne_two h.p_ne_two).pow
  have hQ'U : ∀ g ∈ t2U N.z u, ∀ k ∈ Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀),
      g * k * g⁻¹ ∈ Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀) := fun g hg =>
    t6_norm_sup (hQU g hg) (Pst_normU h hP₀F hg)
  have hPU : ∀ g ∈ t2U N.z u, ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, g * k * g⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀ :=
    fun g hg => Pst_normU h hP₀F hg
  have hle : R₂ N p ⊔ N.X₁ ⊔ P₀ ≤ Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀) := le_sup_right
  have hcent : ∀ v : G, (v = N.z ∨ v = u ∨ v = N.z * u) →
      (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓ Subgroup.centralizer ({v} : Set G) =
        (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G) := by
    intro v hv
    have h1 := card_Cv_Pst h hR hm hn hP₀F hP₀p hP₀c hv
    have h2 := card_pSub_Cv_le h hm hn hP₀c hv (inf_le_right :
      (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓ Subgroup.centralizer ({v} : Set G) ≤ _)
      (hQ'p.to_le inf_le_left)
    refine (Subgroup.eq_of_le_of_card_ge (inf_le_inf_right _ hle) ?_).symm
    rw [h1]
    exact h2
  have hcentU : (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓
      Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G) =
      (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G) := by
    apply le_antisymm
    · intro x ⟨hxQ', hxC⟩
      have hz : N.z ∈ t2U N.z u := by
        obtain ⟨hz2, hu2, hzu, -⟩ := zu_facts h
        exact (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inl rfl))
      have hxz : x ∈ (Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) ⊓ Subgroup.centralizer ({N.z} : Set G) :=
        ⟨hxQ', Subgroup.mem_centralizer_singleton_iff.2 (by
          have := Subgroup.mem_centralizer_iff.1 hxC N.z hz
          exact this.symm)⟩
      rw [hcent N.z (Or.inl rfl)] at hxz
      exact ⟨hxz.1, hxC⟩
    · exact inf_le_inf_right _ hle
  have hBW₁ := U_card_decomp h (hodd _ hQ'p) hQ'U
  have hBW₂ := U_card_decomp h (hodd _ hPp) hPU
  rw [hcentU, hcent N.z (Or.inl rfl), hcent u (Or.inr (Or.inl rfl)),
    hcent (N.z * u) (Or.inr (Or.inr rfl))] at hBW₁
  have hpos : 0 < Nat.card ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓
      Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G)) ^ 2 := by
    have := Nat.card_pos (α := ↥((R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓
      Subgroup.centralizer ((t2U N.z u : Subgroup G) : Set G)))
    positivity
  have hcard : Nat.card ↥(Q ⊔ (R₂ N p ⊔ N.X₁ ⊔ P₀)) = Nat.card ↥(R₂ N p ⊔ N.X₁ ⊔ P₀) :=
    Nat.eq_of_mul_eq_mul_right hpos (hBW₁.trans hBW₂.symm)
  have heq := Subgroup.eq_of_le_of_card_ge hle hcard.le
  exact le_sup_left.trans heq.symm.le


theorem card_two_sub_Cv_le (h : T6Ctx N u p) (hR : RCard N p) {m n : ℕ} (hm : N.q₁ = p ^ m)
    (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) (hP₀p : IsPGroup p ↥P₀)
    (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) {v : G}
    (hv : v = N.z ∨ v = u ∨ v = N.z * u) {E : Subgroup G}
    (hEC : E ≤ Subgroup.centralizer ({v} : Set G))
    (hEM : E ≤ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hE2 : IsPGroup 2 ↥E) :
    Nat.card ↥E ≤ 2 ^ ((N.q₁ - 1).factorization 2 + (N.q₂ - 1).factorization 2) := by
  set Q : Subgroup G := (R₂ N p ⊔ N.X₁ ⊔ P₀) ⊓ Subgroup.centralizer ({v} : Set G) with hQ
  have hQc : Nat.card ↥Q = N.q₁ * N.q₂ * Nat.card ↥P₀ :=
    card_Cv_Pst h hR hm hn hP₀F hP₀p hP₀c hv
  have hQp : IsPGroup p ↥Q := (Pst_pGroup h hR hP₀F hP₀p).to_le inf_le_left
  have hYc : Nat.card ↥(N.X₁ ⊔ N.X₂ ⊔ P₀) = N.q₁ * N.q₂ * Nat.card ↥P₀ := card_Y h hP₀F
  have hYp := Y_pGroup h hP₀F hP₀p
  obtain ⟨g, hg⟩ := exists_conj_to_z h hv
  set Q₁ : Subgroup G := Q.map (MulAut.conj g).toMonoidHom with hQ₁
  have hQ₁C : Q₁ ≤ Subgroup.centralizer ({N.z} : Set G) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 hq.2
    show g * q * g⁻¹ * N.z = N.z * (g * q * g⁻¹)
    rw [← hg]
    calc g * q * g⁻¹ * (g * v * g⁻¹) = g * (q * v) * g⁻¹ := by group
      _ = g * (v * q) * g⁻¹ := by rw [h1]
      _ = g * v * g⁻¹ * (g * q * g⁻¹) := by group
  have hQ₁p : IsPGroup p ↥Q₁ := hQp.map _
  have hQ₁c : Nat.card ↥Q₁ = N.q₁ * N.q₂ * Nat.card ↥P₀ := by
    rw [hQ₁, Subgroup.card_map_of_injective (MulAut.conj g).injective, hQc]
  have hmax : ∀ E' : Subgroup G, E' ≤ Subgroup.centralizer ({N.z} : Set G) → IsPGroup p ↥E' →
      Nat.card ↥E' ≤ N.q₁ * N.q₂ * Nat.card ↥P₀ := fun E' hE'C hE'p =>
    card_pSub_C_le h hm hn hP₀c hE'C hE'p
  obtain ⟨c, hcC, hc⟩ := t6_sylow_conj_of_max h.prime hQ₁C (Y_le_cent_z h hP₀F) hQ₁p hYp
    (fun E' h1 h2 => by rw [hQ₁c]; exact hmax E' h1 h2)
    (fun E' h1 h2 => by rw [hYc]; exact hmax E' h1 h2)
  have hcz : c * N.z = N.z * c := Subgroup.mem_centralizer_singleton_iff.1 hcC
  have hk1 : ∀ q ∈ Q, c * g * q * (c * g)⁻¹ ∈ N.X₁ ⊔ N.X₂ ⊔ P₀ := by
    intro q hq
    have h1 : g * q * g⁻¹ ∈ Q₁ := ⟨q, hq, rfl⟩
    have := (hc _).1 h1
    have e : c * g * q * (c * g)⁻¹ = c * (g * q * g⁻¹) * c⁻¹ := by group
    rw [e]; exact this
  have hk2 : ∀ y ∈ N.X₁ ⊔ N.X₂ ⊔ P₀, (c * g)⁻¹ * y * (c * g) ∈ Q := by
    intro y hy
    have h1 : c⁻¹ * y * c ∈ Q₁ := by
      rw [hc]
      have e : c * (c⁻¹ * y * c) * c⁻¹ = y := by group
      rw [e]; exact hy
    obtain ⟨q, hq, hqe⟩ := h1
    have : (c * g)⁻¹ * y * (c * g) = q := by
      have hqe' : g * q * g⁻¹ = c⁻¹ * y * c := hqe
      calc (c * g)⁻¹ * y * (c * g) = g⁻¹ * (c⁻¹ * y * c) * g := by group
        _ = g⁻¹ * (g * q * g⁻¹) * g := by rw [hqe']
        _ = q := by group
    rw [this]; exact hq
  have hEQ : ∀ e ∈ E, ∀ q ∈ Q, e * q * e⁻¹ ∈ Q := by
    intro e he q hq
    exact ⟨(Subgroup.mem_normalizer_iff.1 (hEM he) q).1 hq.1,
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (hEC he) hq.2) (Subgroup.inv_mem _ (hEC he))⟩
  set E' : Subgroup G := E.map (MulAut.conj (c * g)).toMonoidHom with hE'
  have hE'z : ∀ e ∈ E, (c * g) * e * (c * g)⁻¹ * N.z = N.z * ((c * g) * e * (c * g)⁻¹) := by
    intro e he
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hEC he)
    have hz' : (c * g) * v * (c * g)⁻¹ = N.z := by
      calc (c * g) * v * (c * g)⁻¹ = c * (g * v * g⁻¹) * c⁻¹ := by group
        _ = N.z := by rw [hg, hcz]; group
    rw [← hz']
    calc (c * g) * e * (c * g)⁻¹ * ((c * g) * v * (c * g)⁻¹) = (c * g) * (e * v) * (c * g)⁻¹ := by group
      _ = (c * g) * (v * e) * (c * g)⁻¹ := by rw [h1]
      _ = (c * g) * v * (c * g)⁻¹ * ((c * g) * e * (c * g)⁻¹) := by group
  have hE'C : E' ≤ Subgroup.centralizer ({N.z} : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hE'z e he)
  have hE'N : ∀ e' ∈ E', ∀ y ∈ N.X₁ ⊔ N.X₂ ⊔ P₀, e' * y * e'⁻¹ ∈ N.X₁ ⊔ N.X₂ ⊔ P₀ := by
    rintro _ ⟨e, he, rfl⟩ y hy
    have hq := hk2 y hy
    have hq' := hEQ e he _ hq
    have h1 := hk1 _ hq'
    have e1 : (c * g) * ((e * ((c * g)⁻¹ * y * (c * g)) * e⁻¹)) * (c * g)⁻¹ =
        ((c * g) * e * (c * g)⁻¹) * y * ((c * g) * e * (c * g)⁻¹)⁻¹ := by group
    rw [e1] at h1
    exact h1
  have hcard := card_two_sub_le h hP₀F hE'C (hE2.map _) hE'N
  rwa [hE', Subgroup.card_map_of_injective (MulAut.conj (c * g)).injective] at hcard


theorem T_relIndex_odd (h : T6Ctx N u p) (hR : RCard N p) (hΩ : T6Omega1 N u) {m n : ℕ}
    (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    (hP₀p : IsPGroup p ↥P₀) (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) :
    ¬ 2 ∣ (twoPart N.H h.sec5.loc.H_comm).relIndex
      (Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  set T : Subgroup G := twoPart N.H h.sec5.loc.H_comm with hT
  set M : Subgroup G := Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G) with hM
  have hTM : T ≤ M := fun t ht => twoPart_norm_Pst h hΩ hP₀F ht
  have hTp : IsPGroup 2 ↥T := twoPart_isPGroup _ _
  obtain ⟨S₂, hS₂⟩ := (hTp.of_equiv (Subgroup.subgroupOfEquivOfLe hTM).symm).exists_le_sylow
  set T'' : Subgroup G := (S₂ : Subgroup ↥M).map M.subtype with hT''
  have hT''p : IsPGroup 2 ↥T'' := S₂.isPGroup'.map _
  have hT''M : T'' ≤ M := Subgroup.map_subtype_le _
  have hTT'' : T ≤ T'' := fun t ht => ⟨⟨t, hTM ht⟩, hS₂ (Subgroup.mem_subgroupOf.2 ht), rfl⟩
  have hT''T : T'' ≤ T := by
    by_contra hcon
    have hne' : T ≠ T'' := fun e => hcon (e ▸ le_rfl)
    obtain ⟨x, hxT'', hxT, hxN⟩ := t6_exists_normalizer_elt hT''p hTT'' hne'
    have hx2 : ∃ k : ℕ, x ^ (2 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hT''p ⟨x, hxT''⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hxU := norm_U_of_norm_T h hΩ hxN
    have hfix := t6_fixed_pt_klein hz2 hu2 hzu hz1 hu1 hne (fun g hg => by
      have hgU : g ∈ t2U N.z u := (t2U_mem hz2 hu2 hzu).2 hg
      exact (t2U_mem hz2 hu2 hzu).1 (hxU g hgU)) hx2
    have hE : ∀ v : G, (v = N.z ∨ v = u ∨ v = N.z * u) → x * v * x⁻¹ = v → False := by
      intro v hv hxv
      set E : Subgroup G := T ⊔ Subgroup.zpowers x with hE
      have hEle : E ≤ T'' := sup_le hTT'' (Subgroup.zpowers_le.2 hxT'')
      have hEC : E ≤ Subgroup.centralizer ({v} : Set G) := by
        refine sup_le (twoPart_le_cent h hv) ?_
        rw [Subgroup.zpowers_le]
        refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        calc x * v = (x * v * x⁻¹) * x := by group
          _ = v * x := by rw [hxv]
      have hcard := card_two_sub_Cv_le h hR hm hn hP₀F hP₀p hP₀c hv hEC (hEle.trans hT''M)
        (hT''p.to_le hEle)
      have hge := card_twoPart_ge' h
      have hTE : T ≤ E := le_sup_left
      have heq : T = E := Subgroup.eq_of_le_of_card_ge hTE (hcard.trans hge)
      exact hxT (heq ▸ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x) : x ∈ E))
    rcases hfix with hf | hf | hf
    · exact hE _ (Or.inl rfl) hf
    · exact hE _ (Or.inr (Or.inl rfl)) hf
    · exact hE _ (Or.inr (Or.inr rfl)) hf
  have hsub : T.subgroupOf M = (S₂ : Subgroup ↥M) := by
    apply le_antisymm hS₂
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    exact hT''T ⟨x, hx, rfl⟩
  show ¬ 2 ∣ (T.subgroupOf M).index
  rw [hsub]
  exact S₂.not_dvd_index


end CFSG.GH74.GLS.Stage4.Rest.T6.P71
