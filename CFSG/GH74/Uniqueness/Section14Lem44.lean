module

public import CFSG.GH74.Uniqueness.Section14Lem43
public import CFSG.GH74.Uniqueness.Section14Tools
public import CFSG.Timmesfeld.Orders.Bang

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X] {Z : Set X} {M : Subgroup X}

namespace Sec14

variable {c : Ctx12 Z M} {n : ℕ} {Q : Sylow 2 ↥c.L} {U : Subgroup X}

theorem one_lt_card_K (h : LData c n 2) : 1 < Nat.card ↥(kGrp M c.t) := by
  rw [h.k_eq', h.k_card]
  have : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (n_odd h).2
  omega

theorem odd_card_K (h : LData c n 2) : Odd (Nat.card ↥(kGrp M c.t)) := by
  rw [h.k_eq', h.k_card]
  have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have h2 : Even (2 ^ n) := (Nat.even_pow' (by have := (n_odd h).2; omega)).mpr even_two
  obtain ⟨m, hm⟩ := h2
  exact ⟨m - 1, by omega⟩

theorem cent_K_M (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h : LData c n 2) :
    ∀ x ∈ kGrp M c.t, x ≠ 1 → centralizer ({x} : Set X) ⊓ M ≤ c.D := by
  intro x hx hx1 g hg
  obtain ⟨hgx, hgM⟩ := mem_inf.mp hg
  have hΩ := h12.p1213 c n 2 h x hx hx1
  set β := conjugate M c.t with hβ
  have hβΩ : β ∈ omega M := ⟨c.t, rfl⟩
  have hβM : β ≠ M := by
    intro heq
    exact c.htM ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M) (u := c.t)).mp heq)
  have hxβ : conjugate β x = β := by
    have : β ∈ omegaFix M ({x} : Set X) := by rw [hΩ]; exact Or.inr rfl
    exact this.2 x rfl
  have hgx' : g * x = x * g := mem_centralizer_singleton_iff.mp hgx
  have hβ' : conjugate β g ∈ omegaFix M ({x} : Set X) := by
    refine ⟨conjugate_mem_omega hβΩ g, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff] at hy
    rw [hy, conjugate_conjugate, hgx', ← conjugate_conjugate, hxβ]
  rw [hΩ] at hβ'
  rcases hβ' with h1 | h1
  · exfalso
    apply hβM
    have hgM' : conjugate M g⁻¹ = M :=
      (S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M)).mpr (M.inv_mem hgM)
    calc β = conjugate (conjugate β g) g⁻¹ := by
          rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
      _ = M := by rw [h1, hgM']
  · exact mem_inf.mpr ⟨hgM, (S.prodDisc.conjugate_eq_iff_mem hβΩ).mp h1⟩

theorem conj_D (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h : LData c n 2) :
    ∀ g : X, kGrp M c.t ≤ conjugate c.D g → conjugate c.D g = c.D := by
  intro g hg
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ kGrp M c.t, x ≠ 1 := by
    have h1 := one_lt_card_K h
    by_contra hcon
    push Not at hcon
    have : kGrp M c.t = ⊥ := eq_bot_iff.mpr fun y hy => mem_bot.mpr (hcon y hy)
    rw [this, card_bot] at h1
    omega
  have hΩ := h12.p1213 c n 2 h x hx hx1
  set β := conjugate M c.t with hβ
  have hβΩ : β ∈ omega M := ⟨c.t, rfl⟩
  have hβM : β ≠ M := by
    intro heq
    exact c.htM ((S.prodDisc.conjugate_eq_iff_mem (self_mem_omega M) (u := c.t)).mp heq)
  have hcD : conjugate c.D g = conjugate M g ⊓ conjugate β g := conjugate_inf M β g
  rw [hcD] at hg ⊢
  have hxa : x ∈ conjugate M g := (mem_inf.mp (hg hx)).1
  have hxb : x ∈ conjugate β g := (mem_inf.mp (hg hx)).2
  have hfix : ∀ γ ∈ omega M, x ∈ γ → γ ∈ omegaFix M ({x} : Set X) := by
    intro γ hγ hxγ
    refine ⟨hγ, fun y hy => ?_⟩
    rw [Set.mem_singleton_iff.mp hy]
    exact (S.prodDisc.conjugate_eq_iff_mem hγ).mpr hxγ
  have ha := hfix _ (conjugate_mem_omega (self_mem_omega M) g) hxa
  have hb := hfix _ (conjugate_mem_omega hβΩ g) hxb
  rw [hΩ] at ha hb
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
  have hne : conjugate M g ≠ conjugate β g := fun heq => hβM (conjugate_injective g heq).symm
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact absurd (ha.trans hb.symm) hne
  · rw [ha, hb]
  · rw [ha, hb, inf_comm]
  · exact absurd (ha.trans hb.symm) hne

theorem M_le_normalizer_C0 (h : LData c n 2) :
    M ≤ normalizer (centralizer (zHull Z M : Set X) : Set X) := by
  have key : ∀ g ∈ M, ∀ x, x ∈ centralizer (zHull Z M : Set X) →
      g * x * g⁻¹ ∈ centralizer (zHull Z M : Set X) := by
    intro g hg x hx
    rw [mem_centralizer_iff] at hx ⊢
    intro m hm
    have hm' : g⁻¹ * m * g⁻¹⁻¹ ∈ zHull Z M := h.m_normal _ (M.inv_mem hg) m hm
    rw [inv_inv] at hm'
    have := hx _ hm'
    calc m * (g * x * g⁻¹) = g * (g⁻¹ * m * g * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * m * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * m := by group
  intro g hg
  rw [mem_normalizer_iff]
  intro x
  constructor
  · exact key g hg x
  · intro hx
    have := key g⁻¹ (M.inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem C0_le_M (S : ZDSetup X Z M) : centralizer (zHull Z M : Set X) ≤ M := by
  obtain ⟨z, hz, hzM⟩ := S.exists_mem_inter
  intro g hg
  exact S.prodDisc.centralizer_le_of_mem hz hzM
    (mem_centralizer_singleton_iff.mpr
      ((mem_centralizer_iff.mp hg) z (subset_closure ⟨hz, hzM⟩)).symm)

theorem K_inf_P (h : LData c n 2) {x : X} (hxK : x ∈ kGrp M c.t) (hxP : x ∈ pGrp c Q) : x = 1 :=
  Bender.eq_one_of_isPGroup_two_of_odd isPGroup_P (odd_card_K h) hxP hxK

theorem D_inf_C0 (S : ZDSetup X Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    c.D ⊓ centralizer (zHull Z M : Set X) = centralizer (c.L : Set X) := by
  apply le_antisymm
  · intro g hg
    obtain ⟨hgD, hgC⟩ := mem_inf.mp hg
    have hgPJ : g ∈ pGrp c Q ⊔ centralizer (c.L : Set X) := by
      rw [← cent_Mo_NL S h hQ]
      exact mem_inf.mpr ⟨hgC, D_le_N h hgD⟩
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _
      J_le_normalizer_P] at hgPJ
    obtain ⟨p, hp, j, hj, hpj⟩ := Set.mem_mul.mp hgPJ
    have hpD : p ∈ c.D := by
      have := c.D.mul_mem hgD (c.D.inv_mem (h.centralizer_le hj))
      rw [← hpj] at this
      simpa using this
    have hpK : p ∈ kGrp M c.t := by
      rw [h.k_eq']
      exact mem_inf.mpr ⟨hpD, P_le_L hp⟩
    rw [← hpj, K_inf_P h hpK hp, one_mul]
    exact hj
  · intro g hg
    refine mem_inf.mpr ⟨h.centralizer_le hg, ?_⟩
    rw [mem_centralizer_iff]
    intro m hm
    exact (mem_centralizer_iff.mp hg) m (h.m_le hm)

theorem cent_K_C0
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    ∀ x ∈ kGrp M c.t, x ≠ 1 →
      centralizer ({x} : Set X) ⊓ centralizer (zHull Z M : Set X) = centralizer (c.L : Set X) := by
  intro x hx hx1
  apply le_antisymm
  · intro g hg
    obtain ⟨hgx, hgC⟩ := mem_inf.mp hg
    have hgD := cent_K_M S h12 h x hx hx1 (mem_inf.mpr ⟨hgx, C0_le_M S hgC⟩)
    rw [← D_inf_C0 S h hQ]
    exact mem_inf.mpr ⟨hgD, hgC⟩
  · intro g hg
    refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
    · exact ((mem_centralizer_iff.mp hg) x (c.kGrp_le_L hx)).symm
    · rw [mem_centralizer_iff]
      intro m hm
      exact (mem_centralizer_iff.mp hg) m (h.m_le hm)

theorem exists_zsigmondy {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ (6 * n) - 1 ∧ ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1 :=
  CFSG.Timmesfeld.exists_primitive_prime_dvd_two_pow_sub_one (6 * n) (by omega) (by omega)

section Zsig

variable {r : ℕ}

theorem zsig_ne_two (hn : 1 ≤ n) (hdvd : r ∣ 2 ^ (6 * n) - 1) : r ≠ 2 := by
  rintro rfl
  have h1 : 1 ≤ 2 ^ (6 * n) := Nat.one_le_two_pow
  have h2 : 2 ∣ 2 ^ (6 * n) - 1 + 1 := by
    rw [Nat.sub_add_cancel h1]
    exact dvd_pow_self 2 (by omega)
  omega

theorem zsig_gt (hn : 1 ≤ n) (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) : 6 * n < r := by
  by_contra hle
  have hr2 := zsig_ne_two hn hdvd
  have hcop : Nat.Coprime 2 r := (Nat.coprime_primes Nat.prime_two hr).mpr (Ne.symm hr2)
  have hferm : 2 ^ (r - 1) ≡ 1 [MOD r] := by
    have := Nat.ModEq.pow_totient hcop
    rwa [Nat.totient_prime hr] at this
  have h1 : r ∣ 2 ^ (r - 1) - 1 := (Nat.modEq_iff_dvd' Nat.one_le_two_pow).mp hferm.symm
  exact hprim (r - 1) (by have := hr.two_le; omega) (by omega) h1

theorem zsig_dvd (hn : 1 ≤ n) (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) :
    r ∣ 2 ^ (2 * n) - 2 ^ n + 1 := by
  have hQ : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  set Q := 2 ^ n with hQdef
  have e6 : 2 ^ (6 * n) = Q ^ 6 := by rw [hQdef, ← pow_mul, mul_comm]
  have e3 : 2 ^ (3 * n) = Q ^ 3 := by rw [hQdef, ← pow_mul, mul_comm]
  have e2 : 2 ^ (2 * n) = Q ^ 2 := by rw [hQdef, ← pow_mul, mul_comm]
  have hQ2 : Q ≤ Q ^ 2 := Nat.le_self_pow (by norm_num) Q
  have hQ3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ (by omega)
  have hQ6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ (by omega)
  have hfac : 2 ^ (6 * n) - 1 = (2 ^ (3 * n) - 1) * ((Q + 1) * (2 ^ (2 * n) - Q + 1)) := by
    rw [e6, e3, e2]
    zify [hQ2, hQ3, hQ6]
    ring
  rw [hfac] at hdvd
  rcases (Nat.Prime.dvd_mul hr).mp hdvd with h3 | h3
  · exact absurd h3 (hprim (3 * n) (by omega) (by omega))
  rcases (Nat.Prime.dvd_mul hr).mp h3 with h4 | h4
  · exfalso
    apply hprim (2 * n) (by omega) (by omega)
    have hQ2' : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ (by omega)
    have : 2 ^ (2 * n) - 1 = (Q - 1) * (Q + 1) := by
      rw [e2]
      zify [hQ, hQ2']
      ring
    rw [this]
    exact dvd_mul_of_dvd_right h4 _
  · rw [e2] at h4 ⊢
    exact h4

theorem zsig_not_dvd_q1 (hn : 1 ≤ n) (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) :
    ¬ r ∣ 2 ^ n - 1 := hprim n (by omega) (by omega)

theorem zsig_not_dvd_q2 (hn : 1 ≤ n) (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) :
    ¬ r ∣ 2 ^ (2 * n) + 1 := by
  intro h1
  apply hprim (4 * n) (by omega) (by omega)
  have hQ : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
  have e : 2 ^ (4 * n) = (2 ^ (2 * n)) ^ 2 := by rw [← pow_mul]; ring_nf
  have hQ2 : 1 ≤ (2 ^ (2 * n)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  have : 2 ^ (4 * n) - 1 = (2 ^ (2 * n) - 1) * (2 ^ (2 * n) + 1) := by
    rw [e]
    zify [hQ, hQ2]
    ring
  rw [this]
  exact dvd_mul_of_dvd_right h1 _

theorem zsig_ne_three (hn : 1 ≤ n) (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) : r ≠ 3 := by
  have := zsig_gt hn hr hdvd hprim
  omega

end Zsig

theorem r_not_dvd_D
    (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M) (h : LData c n 2)
    {r : ℕ} (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) :
    ¬ r ∣ Nat.card c.D := by
  have hn : 1 ≤ n := by have := (n_odd h).2; omega
  have hr2 := zsig_ne_two hn hdvd
  have hrgt := zsig_gt hn hr hdvd hprim
  obtain ⟨d, hd, hdn, hdodd⟩ := card_D h
  obtain ⟨f, hf⟩ := exists_injective_J h12 h131 h
  have hJL : Nat.card (centralizer (c.L : Set X)) ∣ Nat.card c.L :=
    Subgroup.card_dvd_of_injective f hf
  have hL : Nat.card c.L = (2 ^ (2 * n) + 1) * (2 ^ (2 * n) * (2 ^ n - 1)) := by
    rw [h.bender.card_eq, ← pow_mul, mul_comm n 2]
    ring
  have hrL : ¬ r ∣ Nat.card c.L := by
    rw [hL]
    intro h1
    rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
    · exact zsig_not_dvd_q2 hn hprim h2
    rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
    · exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h3))
    · exact zsig_not_dvd_q1 hn hprim h3
  rw [hd]
  intro h1
  rcases (Nat.Prime.dvd_mul hr).mp h1 with h2 | h2
  · rcases (Nat.Prime.dvd_mul hr).mp h2 with h3 | h3
    · exact zsig_not_dvd_q1 hn hprim h3
    · exact hrL (h3.trans hJL)
  · have hd0 : 0 < d := hdodd.pos
    have := Nat.le_of_dvd hd0 h2
    have := Nat.le_of_dvd (by omega) hdn
    omega

theorem card_C0_dvd
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) :
    Nat.card (centralizer (zHull Z M : Set X)) ∣
      2 ^ (3 * n) * (2 ^ (2 * n) - 2 ^ n + 1) * Nat.card (centralizer (c.L : Set X)) := by
  have hDN : c.D ≤ normalizer (centralizer (zHull Z M : Set X) : Set X) :=
    (inf_le_left : c.D ≤ M).trans (M_le_normalizer_C0 h)
  have hprod := card_sup_mul_card_inf' hDN
  rw [inf_comm, D_inf_C0 S h hQ] at hprod
  have hsupM : c.D ⊔ centralizer (zHull Z M : Set X) ≤ M := sup_le inf_le_left (C0_le_M S)
  have hdvdM : Nat.card ↥(c.D ⊔ centralizer (zHull Z M : Set X)) ∣ Nat.card M :=
    Subgroup.card_dvd_of_le hsupM
  rw [card_M S h12 h] at hdvdM
  have hD0 : 0 < Nat.card c.D := Nat.card_pos
  have h1 : Nat.card (centralizer (zHull Z M : Set X)) * Nat.card c.D ∣
      2 ^ (3 * n) * (2 ^ (2 * n) - 2 ^ n + 1) * Nat.card (centralizer (c.L : Set X)) *
        Nat.card c.D := by
    rw [← hprod]
    calc Nat.card ↥(c.D ⊔ centralizer (zHull Z M : Set X)) *
          Nat.card ↥(centralizer (c.L : Set X)) ∣
        2 ^ (3 * n) * (2 ^ (2 * n) - 2 ^ n + 1) * Nat.card c.D *
          Nat.card ↥(centralizer (c.L : Set X)) := Nat.mul_dvd_mul_right hdvdM _
      _ = _ := by ring
  exact Nat.dvd_of_mul_dvd_mul_right hD0 h1

theorem centralizes_Mo_of_r (h : LData c n 2) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ 2 ^ (6 * n) - 1) (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1)
    {x : X} (hxM : x ∈ M) {j : ℕ} (hx : x ^ r ^ j = 1) : x ∈ centralizer (zHull Z M : Set X) := by
  have hn : 1 ≤ n := by have := (n_odd h).2; omega
  rw [mem_centralizer_iff]
  intro v hv
  exact (centralizes_of_pow_prime hr (zsig_ne_two hn hdvd) h.m_card
    (fun k hk hkn => hprim k hk (by omega)) j x hx (fun v hv => h.m_normal x hxM v hv) v hv).symm

theorem sylow_r_le_C0 (h : LData c n 2) {r : ℕ} (hr : r.Prime)
    (hdvd : r ∣ 2 ^ (6 * n) - 1) (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1)
    {R : Subgroup X} (hR : ABGLocalTools.IsSylowOf r R M) :
    R ≤ centralizer (zHull Z M : Set X) := by
  intro x hx
  obtain ⟨j, hj⟩ := hR.isPGroup ⟨x, hx⟩
  exact centralizes_Mo_of_r h hr hdvd hprim (hR.le hx)
    (by simpa using congrArg Subtype.val hj)

theorem lemma144a
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    (h : LData c n 2) {r : ℕ} (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) (R : Subgroup X)
    (hR : ABGLocalTools.IsSylowOf r R M) : ¬ kGrp M c.t ≤ normalizer (R : Set X) := by
  have : Fact r.Prime := ⟨hr⟩
  have hn : 1 ≤ n := by have := (n_odd h).2; omega
  have hr2 := zsig_ne_two hn hdvd
  have hrD := r_not_dvd_D h12 h131 h hr hdvd hprim
  have hrA := zsig_dvd hn hr hdvd hprim
  set A := 2 ^ (2 * n) - 2 ^ n + 1 with hAdef
  have hA0 : A ≠ 0 := by omega
  have hRcard : Nat.card R = r ^ A.factorization r := by
    rw [hR.card_eq, card_M S h12 h]
    have h3 : ¬ r ∣ 2 ^ (3 * n) := fun h1 =>
      hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow h1))
    rw [Nat.factorization_mul (by positivity) Nat.card_pos.ne',
      Nat.factorization_mul (by positivity) hA0, Finsupp.add_apply, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd h3, Nat.factorization_eq_zero_of_not_dvd hrD,
      zero_add, add_zero]
  have hRA : Nat.card R ∣ A := by
    rw [hRcard]
    exact Nat.ordProj_dvd A r
  have hR1 : 1 < Nat.card R := by
    rw [hRcard]
    exact Nat.one_lt_pow (hr.factorization_pos_of_dvd hA0 hrA).ne' hr.one_lt
  intro hKR
  have hfpf : ∀ k ∈ kGrp M c.t, k ≠ 1 → ∀ x ∈ R, k * x = x * k → x = 1 := by
    intro k hk hk1 x hx hkx
    have hxD : x ∈ c.D :=
      cent_K_M S h12 h k hk hk1 (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hkx.symm,
        hR.le hx⟩)
    exact eq_one_of_isPGroup_of_not_dvd hr hR.isPGroup hrD hx hxD
  have hKdvd := card_dvd_card_sub_one_of_fpf_conj hKR hfpf
  rw [h.k_eq', h.k_card] at hKdvd
  have hQ8 : 2 ≤ 2 ^ n := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have e2 : 2 ^ (2 * n) = (2 ^ n) ^ 2 := by rw [← pow_mul, mul_comm]
  rw [hAdef, e2] at hRA
  have heq := arith_144 hQ8 hR1 hRA hKdvd
  have h3 : 3 ∣ Nat.card R := heq ▸ three_dvd_of_odd (n_odd h).1
  rw [hRcard] at h3
  have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp
    (Nat.prime_three.dvd_of_dvd_pow h3)
  exact zsig_ne_three hn hr hdvd hprim this.symm

theorem lemma144b
    (S : ZDSetup X Z M) (h12 : Sec12Results Z M) (h131 : Prop131Stmt Z M)
    (h : LData c n 2)
    (hQ : (M ⊓ c.L).subgroupOf c.L = normalizer ((Q : Subgroup c.L) : Set c.L)) {r : ℕ}
    (hr : r.Prime) (hdvd : r ∣ 2 ^ (6 * n) - 1)
    (hprim : ∀ k : ℕ, 0 < k → k < 6 * n → ¬ r ∣ 2 ^ k - 1) :
    ¬ Nat.Coprime (Nat.card (centralizer (c.L : Set X))) (2 ^ n - 1) := by
  have : Fact r.Prime := ⟨hr⟩
  intro hcop
  have hn : 1 ≤ n := by have := (n_odd h).2; omega
  have hq1 : Odd (2 ^ n - 1) := by
    rw [← h.k_card, ← h.k_eq']
    exact odd_card_K h
  have hcop2 : Nat.Coprime (2 ^ (3 * n) * (2 ^ (2 * n) - 2 ^ n + 1) *
      Nat.card (centralizer (c.L : Set X))) (2 ^ n - 1) := by
    refine Nat.Coprime.mul_left (Nat.Coprime.mul_left ?_ ?_) hcop
    · exact Nat.Coprime.pow_left _ (Nat.coprime_two_left.mpr hq1)
    · have hQ : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have e : 2 ^ (2 * n) - 2 ^ n + 1 = (2 ^ n - 1) * 2 ^ n + 1 := by
        rw [show 2 * n = n + n by ring, pow_add]
        zify [hQ, Nat.le_mul_of_pos_left (2 ^ n) (by positivity : 0 < 2 ^ n)]
        ring
      rw [e, Nat.coprime_comm, Nat.coprime_mul_left_add_right]
      exact Nat.coprime_one_right _
  have hcopC0 : Nat.Coprime (Nat.card ↥(kGrp M c.t))
      (Nat.card (centralizer (zHull Z M : Set X))) := by
    rw [h.k_eq', h.k_card, Nat.coprime_comm]
    exact Nat.Coprime.coprime_dvd_left (card_C0_dvd S h12 h hQ) hcop2
  have hKsolv : Group.IsSolvable ↥(kGrp M c.t) := by
    have : IsCyclic ↥(kGrp M c.t) := by rw [h.k_eq']; exact h.k_cyclic
    have : IsMulCommutative ↥(kGrp M c.t) := IsCyclic.isMulCommutative
    infer_instance
  have hKC0 : kGrp M c.t ≤ normalizer (centralizer (zHull Z M : Set X) : Set X) := by
    rw [h.k_eq']
    exact (inf_le_left.trans (inf_le_left : c.D ≤ M)).trans (M_le_normalizer_C0 h)
  obtain ⟨R, hR, hKR⟩ := exists_sylow_normalized_of_coprime hKC0 hcopC0 r
  obtain ⟨R', hR'⟩ := ABGLocalTools.exists_isSylowOf r M
  have hR'C : R' ≤ centralizer (zHull Z M : Set X) := sylow_r_le_C0 h hr hdvd hprim hR'
  have hRM : ABGLocalTools.IsSylowOf r R M := by
    apply ABGLocalTools.isSylowOf_of_card (hR.le.trans (C0_le_M S))
    rw [hR.card_eq]
    congr 1
    apply le_antisymm
    · exact (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mpr
        (Subgroup.card_dvd_of_le (C0_le_M S)) r
    · have h1 : Nat.card R' ∣ Nat.card (centralizer (zHull Z M : Set X)) :=
        Subgroup.card_dvd_of_le hR'C
      rw [hR'.card_eq] at h1
      exact (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h1
  exact lemma144a S h12 h131 h hr hdvd hprim R hRM hKR

end Sec14

end CFSG.GH74.Uniqueness
