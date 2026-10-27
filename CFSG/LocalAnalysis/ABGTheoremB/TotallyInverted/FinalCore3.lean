module

public import CFSG.LocalAnalysis.ABGTheoremB.TotallyInverted.FinalCore2

public section

namespace CFSG.ABGTheoremB.TotallyInverted.Sec11

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {σ : Setting G} {r : ℕ}

theorem pow_eq_one_of_irred {p : ℕ} [hp : Fact p.Prime] {X C : Subgroup G}
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) (hab : ∀ g ∈ X, ∀ h ∈ X, g * h = h * g)
    (hC : C ≤ Subgroup.normalizer (X : Set G))
    (hirr : ∀ Y : Subgroup G, Y ≤ X → C ≤ Subgroup.normalizer (Y : Set G) → Y = ⊥ ∨ Y = X) :
    ∀ g ∈ X, g ^ p = 1 := by
  let Ω : Subgroup G :=
    { carrier := {g | g ∈ X ∧ g ^ p = 1}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨X.mul_mem ha hb, ?_⟩
        rw [(show Commute a b from hab a ha b hb).mul_pow, ha', hb', one_mul]
      one_mem' := ⟨X.one_mem, one_pow p⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        exact ⟨X.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
  have hΩX : Ω ≤ X := fun g hg => hg.1
  have hCΩ : C ≤ Subgroup.normalizer (Ω : Set G) := by
    intro c hc
    apply mem_normalizer_of_conj_mem
    rintro g ⟨hg, hg'⟩
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hC hc) g).mp hg,
      by rw [conj_pow, hg', mul_one, mul_inv_cancel]⟩
  have hΩ1 : Ω ≠ ⊥ := by
    have hdvd : p ∣ Nat.card X := by
      obtain ⟨k, hk⟩ := hX.exists_card_eq
      rcases k with _ | k
      · exact absurd (Subgroup.card_eq_one.mp (by simpa using hk)) hX1
      · rw [hk, pow_succ]
        exact Dvd.intro_left _ rfl
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := X) p hdvd
    intro hb
    have hgΩ : (g : G) ∈ Ω := ⟨g.2, by
      rw [← Subgroup.orderOf_coe] at hg
      rw [← hg, pow_orderOf_eq_one]⟩
    rw [hb, Subgroup.mem_bot] at hgΩ
    have : orderOf (g : G) = 1 := by rw [hgΩ, orderOf_one]
    rw [Subgroup.orderOf_coe, hg] at this
    exact hp.out.one_lt.ne' this
  rcases hirr Ω hΩX hCΩ with h | h
  · exact absurd h hΩ1
  · intro g hg
    have : g ∈ Ω := h ▸ hg
    exact this.2

omit [Finite G] in
theorem mem_centralizer_sup {g : G} {A B : Subgroup G}
    (hA : g ∈ Subgroup.centralizer (A : Set G)) (hB : g ∈ Subgroup.centralizer (B : Set G)) :
    g ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  have hle : A ⊔ B ≤ Subgroup.centralizer ({g} : Set G) := by
    refine sup_le (fun a ha => ?_) (fun b hb => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hA a ha)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hB b hb)
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hh))

theorem R0_le_centralizer_Ps0 (Δ : Data σ r) :
    R Δ 0 ≤ Subgroup.centralizer (σ.Ps r 0 : Set G) :=
  sup_le ((Q_zero_le_J Δ).trans (J_le_centralizer_Ps Δ)) (Ps_le_centralizer_of_le Δ 0 le_rfl)

namespace CoreHyp

variable {Δ : Data σ r} {V U : Subgroup G} {z : G} (h : CoreHyp Δ V U z)
include h

theorem Q_pow_eq_one (i : Fin 3) : ∀ g ∈ Δ.Q i, g ^ r = 1 := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  exact pow_eq_one_of_irred (Δ.Q_pgroup i).1 (Q_ne_bot Δ h.deltaEps h.valid i)
    (Q_abelian Δ h.deltaEps h.valid i) (C_le_normalizer_Q Δ i)
    (fun _ hY hCY => Q_irred Δ h.deltaEps i hY hCY)

theorem Qs_pow_eq_one (i : Fin 3) : ∀ g ∈ Δ.Qs i, g ^ r = 1 := by
  have : Fact r.Prime := ⟨Δ.prime⟩
  exact pow_eq_one_of_irred (Δ.Q_pgroup i).2 (Qs_ne_bot Δ h.deltaEps h.valid i)
    (Qs_abelian Δ h.deltaEps h.valid i) (C_le_normalizer_Qs Δ i)
    (fun _ hY hCY => Qs_irred Δ h.deltaEps i hY hCY)

theorem Ps_le_Y : σ.Ps r 0 ≤ V ⊓ oddCoreIn (Kp σ r) :=
  le_inf ((Ps_le_R Δ 0).trans h.R_le_V) (Ps_le_oddCore_Kp Δ)

theorem Y_le_normalizer_Ps :
    V ⊓ oddCoreIn (Kp σ r) ≤ Subgroup.normalizer (σ.Ps r 0 : Set G) :=
  inf_le_left.trans (V_le_Kp h.maxV)

theorem Y_inf_N_le : V ⊓ oddCoreIn (Kp σ r) ⊓ σ.N ≤ σ.Ps r 0 := fun _ hg =>
  V_inf_N_inf_oddCore_le Δ h.maxV ⟨⟨hg.1.1, hg.2⟩, hg.1.2⟩

theorem Y_decomp {y : G} (hy : y ∈ V ⊓ oddCoreIn (Kp σ r)) :
    ∃ p ∈ σ.Ps r 0, ∃ q₁ ∈ Δ.Qs 1, ∃ q₂ ∈ Δ.Q 2, y = p * q₁ * q₂ := by
  obtain ⟨y₀, h₀, y₁, h₁, y₂, h₂, y₃, h₃, rfl⟩ := exists_mul_comp h.valid h.odd_Y h.Y_T hy
  have hy₀ : y₀ = 1 := by
    have := h.Y_inf_C.le h₀
    exact this
  refine ⟨y₁, h.Y_inf_N_le ⟨h₁.1, Subgroup.mem_centralizer_singleton_iff.mpr h₁.2.1.symm⟩,
    y₂, ?_, y₃, ?_, by rw [hy₀, one_mul]⟩
  · have : y₂ ∈ comp σ V 1 := ⟨h₂.1.1, h₂.2⟩
    rw [h.comp_V_one] at this
    exact this
  · have : y₃ ∈ comp σ V 2 := ⟨h₃.1.1, h₃.2⟩
    rw [h.comp_V_two] at this
    exact this

theorem mul_conj_x_mem {y : G} (hy : y ∈ V ⊓ oddCoreIn (Kp σ r)) :
    y * (σ.x * y * σ.x⁻¹) ∈ σ.Ps r 0 := by
  have hσ := h.valid
  set Y : Subgroup G := V ⊓ oddCoreIn (Kp σ r) with hY
  have hdec := (odd_fixed_mul_inverted h.odd_Y hσ.x_order (h.Y_T σ.x_mem_T)).1
  have hy' : y ∈ (Y : Set G) := hy
  rw [hdec] at hy'
  obtain ⟨f, hf, i, hi, rfl⟩ := hy'
  have hfP : f ∈ σ.Ps r 0 := h.Y_inf_N_le ⟨hf.1, hf.2⟩
  obtain ⟨hiY, hinv⟩ := OddInversion.mem_invertedSet.mp hi
  have hfx : σ.x * f * σ.x⁻¹ = f := by
    rw [← (Subgroup.mem_centralizer_singleton_iff.mp hf.2), mul_inv_cancel_right]
  have e : f * i * (σ.x * (f * i) * σ.x⁻¹) = f * (i * f * i⁻¹) := by
    calc f * i * (σ.x * (f * i) * σ.x⁻¹) = f * i * ((σ.x * f * σ.x⁻¹) * (σ.x * i * σ.x⁻¹)) := by
          group
      _ = f * (i * f * i⁻¹) := by rw [hfx, hinv]; group
  rw [e]
  exact (σ.Ps r 0).mul_mem hfP
    ((Subgroup.mem_normalizer_iff.mp (h.Y_le_normalizer_Ps hiY) f).mp hfP)

theorem commutator_mem {y y' : G} (hy : y ∈ V ⊓ oddCoreIn (Kp σ r))
    (hy' : y' ∈ V ⊓ oddCoreIn (Kp σ r)) : y * y' * y⁻¹ * y'⁻¹ ∈ σ.Ps r 0 := by
  set Y : Subgroup G := V ⊓ oddCoreIn (Kp σ r) with hY
  set P := σ.Ps r 0
  set a := σ.x * y * σ.x⁻¹
  set b := σ.x * y' * σ.x⁻¹
  have hb : b ∈ Y := (Subgroup.mem_normalizer_iff.mp (h.Y_T σ.x_mem_T) y').mp hy'
  have h1 : y * a ∈ P := h.mul_conj_x_mem hy
  have h2 : y' * b ∈ P := h.mul_conj_x_mem hy'
  have h3 : y * y' * (a * b) ∈ P := by
    have := h.mul_conj_x_mem (Y.mul_mem hy hy')
    have e : σ.x * (y * y') * σ.x⁻¹ = a * b := by simp only [a, b]; group
    rwa [e] at this
  have hbn : b⁻¹ * (y * a)⁻¹ * b ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (h.Y_le_normalizer_Ps (Y.inv_mem hb)) _).mp (P.inv_mem h1)
      |> fun h' => by simpa [mul_assoc] using h'
  have e : y * y' * y⁻¹ * y'⁻¹ =
      (y * y' * (a * b)) * ((b⁻¹ * (y * a)⁻¹ * b) * (y' * b)⁻¹) := by group
  rw [e]
  exact P.mul_mem h3 (P.mul_mem hbn (P.inv_mem h2))

theorem pow_mem {y : G} (hy : y ∈ V ⊓ oddCoreIn (Kp σ r)) : y ^ r ∈ σ.Ps r 0 := by
  set Y : Subgroup G := V ⊓ oddCoreIn (Kp σ r) with hY
  set P := σ.Ps r 0
  have hPn : (P.subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.Ps_le_Y).mpr h.Y_le_normalizer_Ps
  set φ : Y →* Y ⧸ P.subgroupOf Y := QuotientGroup.mk' (P.subgroupOf Y)
  have hcomm : ∀ a b : Y, Commute (φ a) (φ b) := by
    intro a b
    show φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have := h.commutator_mem (Y.inv_mem b.2) (Y.inv_mem a.2)
    simpa [mul_assoc] using this
  obtain ⟨p, hp, q₁, hq₁, q₂, hq₂, rfl⟩ := h.Y_decomp hy
  set a : Y := ⟨p, h.Ps_le_Y hp⟩
  set b : Y := ⟨q₁, h.Qs1_le_Y hq₁⟩
  set c : Y := ⟨q₂, h.Q2_le_Y hq₂⟩
  have e : (⟨p * q₁ * q₂, hy⟩ : Y) = a * b * c := rfl
  have hb : b ^ r = 1 := Subtype.ext (by simpa [b] using h.Qs_pow_eq_one 1 q₁ hq₁)
  have hc : c ^ r = 1 := Subtype.ext (by simpa [c] using h.Q_pow_eq_one 2 q₂ hq₂)
  have key : φ ((⟨p * q₁ * q₂, hy⟩ : Y) ^ r) = φ (a ^ r) := by
    rw [e, map_pow, map_mul, map_mul, ((hcomm a c).mul_left (hcomm b c)).mul_pow,
      (hcomm a b).mul_pow, ← map_pow, ← map_pow, ← map_pow, hb, hc, map_one, mul_one, mul_one]
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at key
  have har : a ^ r ∈ P.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
    exact P.pow_mem hp r
  have hmem := (P.subgroupOf Y).mul_mem har ((P.subgroupOf Y).inv_mem key)
  rw [Subgroup.mem_subgroupOf] at hmem
  have e2 : (a ^ r * (((⟨p * q₁ * q₂, hy⟩ : Y) ^ r)⁻¹ * a ^ r)⁻¹ : Y) =
      (⟨p * q₁ * q₂, hy⟩ : Y) ^ r := by group
  rw [e2, Subgroup.coe_pow] at hmem
  exact hmem

theorem Qs1_le_normalizer_Ps : Δ.Qs 1 ≤ Subgroup.normalizer (σ.Ps r 0 : Set G) :=
  h.Qs1_le_Y.trans h.Y_le_normalizer_Ps

theorem Ps_inf_Qs1 : σ.Ps r 0 ⊓ Δ.Qs 1 = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  exact eq_one_of_conj_eq_inv_of_commute
    (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (isPGroup_Ps 0)) hg.1)
    (Rs_inverted Δ h.valid (i := 1) (j := 0) (by decide) (Qs_le_Rs Δ 1 hg.2))
    (Subgroup.mem_centralizer_singleton_iff.mp (Δ.P_centralized 0 hg.1)).symm

theorem x₃_inverts_Qs1_sup_Ps {g : G} (hg : g ∈ Δ.Qs 1 ⊔ σ.Ps r 0) :
    σ.xs 2 * g * (σ.xs 2)⁻¹ = g⁻¹ := by
  obtain ⟨q, hq, p, hp, rfl⟩ := (mem_sup_iff_of_le_normalizer h.Qs1_le_normalizer_Ps).mp hg
  have h1 := Rs_inverted Δ h.valid (i := 1) (j := 2) (by decide) (Qs_le_Rs Δ 1 hq)
  have h2 := Δ.P_inverted 0 2 (by decide) p hp
  have hcomm : q * p = p * q :=
    (Subgroup.mem_centralizer_iff.mp (h.Qs1_le_centralizer_Ps0 hq) p hp).symm
  calc σ.xs 2 * (q * p) * (σ.xs 2)⁻¹ =
        (σ.xs 2 * q * (σ.xs 2)⁻¹) * (σ.xs 2 * p * (σ.xs 2)⁻¹) := by group
    _ = (p * q)⁻¹ := by rw [h1, h2, mul_inv_rev]
    _ = (q * p)⁻¹ := by rw [hcomm]

theorem Qs1_sup_Ps_inf_Q2 : (Δ.Qs 1 ⊔ σ.Ps r 0) ⊓ Δ.Q 2 = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  exact eq_one_of_conj_eq_inv_of_commute
    (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 2).1) hg.2)
    (h.x₃_inverts_Qs1_sup_Ps hg.1)
    (Subgroup.mem_centralizer_singleton_iff.mp (Q_le_Ns Δ h.valid 2 hg.2)).symm

theorem card_Qs1_sup_Ps : Nat.card (Δ.Qs 1 ⊔ σ.Ps r 0 : Subgroup G) =
    σ.q * Nat.card (σ.Ps r 0) := by
  rw [card_sup_of_inf_eq_bot h.Qs1_le_normalizer_Ps (by rw [inf_comm]; exact h.Ps_inf_Qs1),
    card_Qs Δ h.deltaEps]

theorem Y_eq : V ⊓ oddCoreIn (Kp σ r) = Δ.Q 2 ⊔ (Δ.Qs 1 ⊔ σ.Ps r 0) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨p, hp, q₁, hq₁, q₂, hq₂, rfl⟩ := h.Y_decomp hy
    have e : p * q₁ * q₂ = q₂ * (q₂⁻¹ * (p * q₁) * q₂) := by group
    rw [e]
    refine Subgroup.mul_mem_sup hq₂ ?_
    have hpq : p * q₁ ∈ Δ.Qs 1 ⊔ σ.Ps r 0 := by
      have e' : p * q₁ = q₁ * (q₁⁻¹ * p * q₁) := by group
      rw [e']
      refine Subgroup.mul_mem_sup hq₁ ?_
      have := (Subgroup.mem_normalizer_iff.mp
        (h.Qs1_le_normalizer_Ps ((Δ.Qs 1).inv_mem hq₁)) p).mp hp
      simpa using this
    have hq₂n : q₂⁻¹ ∈ Subgroup.normalizer
        ((Δ.Qs 1 ⊔ σ.Ps r 0 : Subgroup G) : Set G) := by
      apply mem_normalizer_of_conj_mem
      intro b hb
      have hbY : b ∈ V ⊓ oddCoreIn (Kp σ r) := sup_le h.Qs1_le_Y h.Ps_le_Y hb
      have hc := h.commutator_mem ((V ⊓ oddCoreIn (Kp σ r)).inv_mem (h.Q2_le_Y hq₂)) hbY
      have e'' : q₂⁻¹ * b * q₂⁻¹⁻¹ = (q₂⁻¹ * b * q₂⁻¹⁻¹ * b⁻¹) * b := by group
      rw [e'']
      exact (Δ.Qs 1 ⊔ σ.Ps r 0).mul_mem
        ((le_sup_right : σ.Ps r 0 ≤ Δ.Qs 1 ⊔ σ.Ps r 0) hc) hb
    have := (Subgroup.mem_normalizer_iff.mp hq₂n (p * q₁)).mp hpq
    simpa [mul_assoc] using this
  · exact sup_le h.Q2_le_Y (sup_le h.Qs1_le_Y h.Ps_le_Y)

theorem card_Y : Nat.card (V ⊓ oddCoreIn (Kp σ r) : Subgroup G) =
    σ.q ^ 2 * Nat.card (σ.Ps r 0) := by
  have hn : Δ.Q 2 ≤ Subgroup.normalizer ((Δ.Qs 1 ⊔ σ.Ps r 0 : Subgroup G) : Set G) := by
    intro u hu
    apply mem_normalizer_of_conj_mem
    intro b hb
    have hbY : b ∈ V ⊓ oddCoreIn (Kp σ r) := sup_le h.Qs1_le_Y h.Ps_le_Y hb
    have hc := h.commutator_mem (h.Q2_le_Y hu) hbY
    have e : u * b * u⁻¹ = (u * b * u⁻¹ * b⁻¹) * b := by group
    rw [e]
    exact (Δ.Qs 1 ⊔ σ.Ps r 0).mul_mem ((le_sup_right : σ.Ps r 0 ≤ Δ.Qs 1 ⊔ σ.Ps r 0) hc) hb
  rw [h.Y_eq, card_sup_of_inf_eq_bot hn (by rw [inf_comm]; exact h.Qs1_sup_Ps_inf_Q2),
    h.card_Qs1_sup_Ps, card_Q Δ h.deltaEps, pow_two, mul_assoc]

theorem J_faithful : ∀ j ∈ Δ.J, (∀ y ∈ V ⊓ oddCoreIn (Kp σ r),
    j * y * j⁻¹ * y⁻¹ ∈ σ.Ps r 0) → j = 1 := by
  have hσ := h.valid
  have hδq := h.deltaEps
  set Y : Subgroup G := V ⊓ oddCoreIn (Kp σ r) with hY
  set P := σ.Ps r 0
  have hJY := h.J_le_normalizer_Y
  have hJP : Δ.J ≤ Subgroup.normalizer (P : Set G) := (J_le_N hσ Δ).trans N_le_Kp
  let K₀ : Subgroup G :=
    { carrier := {j | j ∈ Δ.J ∧ ∀ y ∈ Y, j * y * j⁻¹ * y⁻¹ ∈ P}
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨Δ.J.mul_mem ha hb, fun y hy => ?_⟩
        have hby : b * y * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hJY hb) y).mp hy
        have e : a * b * y * (a * b)⁻¹ * y⁻¹ =
            a * (b * y * b⁻¹ * y⁻¹) * a⁻¹ * (a * y * a⁻¹ * y⁻¹) := by group
        rw [e]
        exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hJP ha) _).mp (hb' y hy))
          (ha' y hy)
      one_mem' := ⟨Δ.J.one_mem, fun y _ => by simp⟩
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨Δ.J.inv_mem ha, fun y hy => ?_⟩
        have hy' : a⁻¹ * y * a ∈ Y := by
          have := (Subgroup.mem_normalizer_iff.mp (hJY (Δ.J.inv_mem ha)) y).mp hy
          rwa [inv_inv] at this
        have h1 := ha' _ hy'
        have e : a * (a⁻¹ * y * a) * a⁻¹ * (a⁻¹ * y * a)⁻¹ = (a⁻¹ * y * a * y⁻¹)⁻¹ := by group
        rw [e] at h1
        have := P.inv_mem h1
        simpa using this }
  have hK₀J : K₀ ≤ Δ.J := fun j hj => hj.1
  have hJK₀ : Δ.J ≤ Subgroup.normalizer (K₀ : Set G) := by
    intro g hg
    apply mem_normalizer_of_conj_mem
    rintro j ⟨hj, hj'⟩
    refine ⟨Δ.J.mul_mem (Δ.J.mul_mem hg hj) (Δ.J.inv_mem hg), fun y hy => ?_⟩
    have hy' : g⁻¹ * y * g ∈ Y := by
      have := (Subgroup.mem_normalizer_iff.mp (hJY (Δ.J.inv_mem hg)) y).mp hy
      rwa [inv_inv] at this
    have e : g * j * g⁻¹ * y * (g * j * g⁻¹)⁻¹ * y⁻¹ =
        g * (j * (g⁻¹ * y * g) * j⁻¹ * (g⁻¹ * y * g)⁻¹) * g⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hJP hg) _).mp (hj' _ hy')
  have hxK : σ.x ∉ K₀ := by
    rintro ⟨-, hx⟩
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (Q_ne_bot Δ hδq hσ 2)
    have hinv : σ.xs 0 * (u : G) * (σ.xs 0)⁻¹ = (u : G)⁻¹ :=
      R_inverted Δ hσ (i := 2) (j := 0) (by decide) (Q_le_R Δ 2 u.2)
    have h1 := hx u (h.Q2_le_Y u.2)
    have e : σ.x * (u : G) * σ.x⁻¹ * (u : G)⁻¹ = ((u : G) ^ 2)⁻¹ := by
      rw [show σ.x * (u : G) * σ.x⁻¹ = (u : G)⁻¹ from hinv, pow_two, mul_inv_rev]
    rw [e] at h1
    have h2 : (u : G) ^ 2 ∈ σ.Ps r 0 ⊓ Δ.Q 2 :=
      ⟨by simpa using P.inv_mem h1, (Δ.Q 2).pow_mem u.2 2⟩
    have hPQ : σ.Ps r 0 ⊓ Δ.Q 2 = ⊥ := eq_bot_iff.mpr
      ((inf_le_inf_right _ (le_sup_right : σ.Ps r 0 ≤ Δ.Qs 1 ⊔ σ.Ps r 0)).trans
        h.Qs1_sup_Ps_inf_Q2.le)
    rw [hPQ, Subgroup.mem_bot] at h2
    apply hu1
    apply Subtype.ext
    exact mem_of_sq_mem (X := ⊥)
      (odd_orderOf_of_mem (odd_card_of_isPGroup Δ.prime Δ.ne_two (Δ.Q_pgroup 2).1) u.2)
      (by rw [h2]; exact Subgroup.one_mem _)
  rcases normal_eq_or_le hσ Δ (J_inf_ON Δ hδq) hK₀J hJK₀ with hK | hK
  · exact absurd (hK ▸ x_mem_J hσ Δ (J_inf_ON Δ hδq)) hxK
  · intro j hj hj'
    rcases hK j ⟨hj, hj'⟩ with h1 | h1
    · exact h1
    · exact absurd (h1 ▸ (⟨hj, hj'⟩ : j ∈ K₀)) hxK

theorem Y_le_Vstar : V ⊓ oddCoreIn (Kp σ r) ≤ pCoreIn r (V ⊔ σ.C) := by
  refine le_of_comp_subset h.valid h.odd_Y h.Y_T (by rw [h.Y_inf_C]; exact bot_le) ?_
  intro i
  match i with
  | 0 =>
    intro u hu
    have hP : u ∈ σ.Ps r 0 := h.Y_inf_N_le
      ⟨hu.1, Subgroup.mem_centralizer_singleton_iff.mpr hu.2.1.symm⟩
    apply h.comp_V_subset_Vstar 0
    rw [h.comp_V_zero]
    exact Ps_le_R Δ 0 hP
  | 1 => exact fun u hu => h.comp_V_subset_Vstar 1 ⟨hu.1.1, hu.2⟩
  | 2 => exact fun u hu => h.comp_V_subset_Vstar 2 ⟨hu.1.1, hu.2⟩

theorem T_le_normalizer_Vstar : σ.T ≤ Subgroup.normalizer (pCoreIn r (V ⊔ σ.C) : Set G) :=
  h.T_le_C'.trans (C_le_normalizer_pCoreIn_sup V)

theorem Vstar_le_centralizer_Ps0 :
    pCoreIn r (V ⊔ σ.C) ≤ Subgroup.centralizer (σ.Ps r 0 : Set G) := by
  refine le_of_comp_subset h.valid (odd_card_pCoreIn Δ _) h.T_le_normalizer_Vstar
    (by rw [h.Vstar_inf_C]; exact bot_le) ?_
  intro i
  match i with
  | 0 =>
    intro u hu
    have : u ∈ comp σ V 0 := comp_mono h.Vstar_le_V 0 hu
    rw [h.comp_V_zero] at this
    exact R0_le_centralizer_Ps0 Δ this
  | 1 =>
    intro u hu
    have : u ∈ comp σ V 1 := comp_mono h.Vstar_le_V 1 hu
    rw [h.comp_V_one] at this
    exact h.Qs1_le_centralizer_Ps0 this
  | 2 =>
    intro u hu
    have : u ∈ comp σ V 2 := comp_mono h.Vstar_le_V 2 hu
    rw [h.comp_V_two] at this
    exact h.Q2_le_centralizer_Ps0 this

theorem le_Zv : Δ.Qs 1 ⊔ σ.Ps r 0 ≤ pCoreIn r (V ⊔ σ.C) ⊓
    Subgroup.centralizer (pCoreIn r (V ⊔ σ.C) : Set G) := by
  refine le_inf (sup_le (fun u hu => h.comp_V_subset_Vstar 1 (h.Qs1_subset hu))
    (fun u hu => h.comp_V_subset_Vstar 0 (by rw [h.comp_V_zero]; exact Ps_le_R Δ 0 hu))) ?_
  rw [Subgroup.le_centralizer_iff]
  intro g hg
  exact mem_centralizer_sup
    (Subgroup.le_centralizer_iff.mp h.Qs1_le_centralizer_Ustar (h.Vstar_le_Ustar hg))
    (h.Vstar_le_centralizer_Ps0 hg)

theorem Zv_eq : pCoreIn r (V ⊔ σ.C) ⊓ Subgroup.centralizer (pCoreIn r (V ⊔ σ.C) : Set G) =
    Δ.Qs 1 ⊔ σ.Ps r 0 := by
  have hσ := h.valid
  set Vs := pCoreIn r (V ⊔ σ.C) with hVs
  set Zv : Subgroup G := Vs ⊓ Subgroup.centralizer (Vs : Set G) with hZv
  set Y : Subgroup G := V ⊓ oddCoreIn (Kp σ r) with hY
  set P := σ.Ps r 0
  set S₀ : Set G := {y | y ∈ Y ∧ ∀ u ∈ Δ.Q 0, u * y * u⁻¹ * y⁻¹ ∈ P} with hS₀
  have hbound : Nat.card S₀ ≤ σ.q * Nat.card P :=
    h.inputs.ii_4_18 h.deltaEps Y P h.Ps_le_Y h.Y_le_normalizer_Ps h.J_le_normalizer_Y
      ((J_le_N hσ Δ).trans N_le_Kp) (fun y hy y' hy' => h.commutator_mem hy hy')
      (fun y hy => h.pow_mem hy) h.card_Y h.J_faithful (Δ.Q 0) (Set.mem_insert _ _)
  have hsub : (Zv : Set G) ⊆ S₀ := by
    intro v hv
    have hvVs : v ∈ Vs := hv.1
    have hvc : ∀ w ∈ Vs, w * v = v * w := Subgroup.mem_centralizer_iff.mp hv.2
    obtain ⟨v₀, h₀, v₁, h₁, v₂, h₂, v₃, h₃, rfl⟩ :=
      exists_mul_comp hσ (odd_card_pCoreIn Δ _) h.T_le_normalizer_Vstar hvVs
    have hv₀ : v₀ = 1 := by
      have := h.Vstar_inf_C.le h₀
      exact this
    have hv₁ : v₁ ∈ R Δ 0 := by
      have := comp_mono h.Vstar_le_V 0 h₁
      rw [h.comp_V_zero] at this
      exact this
    have hv₂ : v₂ ∈ Δ.Qs 1 := by
      have := comp_mono h.Vstar_le_V 1 h₂
      rw [h.comp_V_one] at this
      exact this
    have hv₃ : v₃ ∈ Δ.Q 2 := by
      have := comp_mono h.Vstar_le_V 2 h₃
      rw [h.comp_V_two] at this
      exact this
    obtain ⟨q₀, hq₀, p₀, hp₀, hv₁e⟩ := (mem_sup_iff_of_le_normalizer
      ((Q_le_Ns Δ hσ 0).trans (le_normalizer_pCoreIn r _))).mp hv₁
    set y' := p₀ * v₂ * v₃ with hy'
    have hy'Y : y' ∈ Y := Y.mul_mem (Y.mul_mem (h.Ps_le_Y hp₀) (h.Qs1_le_Y hv₂)) (h.Q2_le_Y hv₃)
    have hve : v₀ * v₁ * v₂ * v₃ = q₀ * y' := by rw [hv₀, ← hv₁e, hy']; group
    have hq₀J : q₀ ∈ Δ.J := Q_zero_le_J Δ hq₀
    have hq₀1 : q₀ = 1 := by
      apply h.J_faithful q₀ hq₀J
      intro y hy
      have hw : y'⁻¹ * y * y' ∈ Vs :=
        h.Y_le_Vstar (Y.mul_mem (Y.mul_mem (Y.inv_mem hy'Y) hy) hy'Y)
      have hq₀e : q₀ = (v₀ * v₁ * v₂ * v₃) * y'⁻¹ := by rw [hve]; group
      have hcw := hvc _ hw
      have e : q₀ * y * q₀⁻¹ * y⁻¹ = y'⁻¹ * y * y'⁻¹⁻¹ * y⁻¹ := by
        rw [hq₀e]
        calc v₀ * v₁ * v₂ * v₃ * y'⁻¹ * y * (v₀ * v₁ * v₂ * v₃ * y'⁻¹)⁻¹ * y⁻¹ =
              (v₀ * v₁ * v₂ * v₃) * (y'⁻¹ * y * y') * (v₀ * v₁ * v₂ * v₃)⁻¹ * y⁻¹ := by group
          _ = (y'⁻¹ * y * y') * (v₀ * v₁ * v₂ * v₃) * (v₀ * v₁ * v₂ * v₃)⁻¹ * y⁻¹ := by
              rw [← hcw]
          _ = y'⁻¹ * y * y'⁻¹⁻¹ * y⁻¹ := by group
      rw [e]
      exact h.commutator_mem (Y.inv_mem hy'Y) hy
    rw [hve, hq₀1, one_mul]
    refine ⟨hy'Y, fun u hu => ?_⟩
    have huVs : u ∈ Vs :=
      h.comp_V_subset_Vstar 0 (by rw [h.comp_V_zero]; exact Q_le_R Δ 0 hu)
    have hcu := hvc u huVs
    rw [hve, hq₀1, one_mul] at hcu
    rw [hcu, mul_inv_cancel_right, mul_inv_cancel]
    exact P.one_mem
  have hcard : Nat.card Zv ≤ Nat.card (Δ.Qs 1 ⊔ σ.Ps r 0 : Subgroup G) := by
    rw [h.card_Qs1_sup_Ps]
    calc Nat.card Zv = Nat.card (Zv : Set G) := rfl
      _ ≤ Nat.card S₀ := Nat.card_mono (Set.toFinite _) hsub
      _ ≤ σ.q * Nat.card P := hbound
  exact (Subgroup.eq_of_le_of_card_ge h.le_Zv hcard).symm

end CoreHyp

end CFSG.ABGTheoremB.TotallyInverted.Sec11
