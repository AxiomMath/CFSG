module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySemilinearCoords

public section

namespace CFSG.SeitzReduction.RankOne

open Subgroup

namespace U3R2

variable {G : Type} [Group G] [Finite G] {L T₁ R₂ : Subgroup G} {t : G} {f : ℕ}

theorem conj_t_mul_t_mem (hR : U3R2 G L T₁ R₂ t f) {w : G} (hw : w ∈ T₁ ⊔ R₂) :
    w * t * w⁻¹ * t ∈ szA₁ T₁ := by
  obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hw
  have hρ := hR.rho_mem r hr
  have hyρ : y * (r * t * r⁻¹ * t) = (r * t * r⁻¹ * t) * y :=
    (mem_centralizer_iff.mp (mem_szA₁.mp hρ).2 y hy)
  have hyt : y * t = t * y := hR.t_comm y hy
  have hti : t⁻¹ = t := hR.t_inv
  have e : y * r * t * (y * r)⁻¹ * t = y * (r * t * r⁻¹ * t) * (t⁻¹ * y⁻¹ * t) := by group
  rw [e, hyρ, show t⁻¹ * y⁻¹ * t = y⁻¹ by
    rw [hti]
    calc t * y⁻¹ * t = t * (y⁻¹ * t) := by group
      _ = t * (t * y⁻¹) := by
        rw [show y⁻¹ * t = t * y⁻¹ by
          calc y⁻¹ * t = y⁻¹ * (t * y) * y⁻¹ := by group
            _ = y⁻¹ * (y * t) * y⁻¹ := by rw [hyt]
            _ = t * y⁻¹ := by group]
      _ = (t * t) * y⁻¹ := by group
      _ = y⁻¹ := by rw [← sq, hR.t_sq, one_mul]]
  rw [mul_inv_cancel_right]
  exact hρ

theorem mem_T₁_of_comm_t (hR : U3R2 G L T₁ R₂ t f) {w : G} (hw : w ∈ T₁ ⊔ R₂)
    (hwt : w * t = t * w) : w ∈ T₁ := by
  obtain ⟨y, hy, r, hr, rfl⟩ := hR.mem_sup_iff.mp hw
  have hyt : y * t = t * y := hR.t_comm y hy
  have hrt : r * t = t * r := by
    have h1 : y * (r * t) = y * (t * r) := by
      calc y * (r * t) = y * r * t := by group
        _ = t * (y * r) := hwt
        _ = (t * y) * r := by group
        _ = (y * t) * r := by rw [hyt]
        _ = y * (t * r) := by group
    exact mul_left_cancel h1
  exact mul_mem hy (szA₁_le T₁ (hR.rho_ker r hr hrt))

theorem card_centralizer_sup_le (hR : U3R2 G L T₁ R₂ t f) {x : G} (hxt : x * t = t * x) :
    Nat.card ((T₁ ⊔ R₂) ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
      Nat.card (T₁ ⊓ centralizer ({x} : Set G) : Subgroup G) *
        Nat.card (szA₁ T₁ ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  set H := (T₁ ⊔ R₂) ⊓ centralizer ({x} : Set G) with hH
  set K := szA₁ T₁ ⊓ centralizer ({x} : Set G) with hK
  have hti : t⁻¹ = t := hR.t_inv
  have hmemK : ∀ w : H, (w : G) * t * (w : G)⁻¹ * t ∈ K := by
    intro w
    obtain ⟨hw1, hw2⟩ := mem_inf.mp w.2
    refine mem_inf.mpr ⟨hR.conj_t_mul_t_mem hw1, mem_centralizer_singleton_iff.mpr ?_⟩
    have hwx : (w : G) * x = x * w := mem_centralizer_singleton_iff.mp hw2
    have hwx' : (w : G)⁻¹ * x = x * (w : G)⁻¹ := by
      calc (w : G)⁻¹ * x = (w : G)⁻¹ * (x * w) * (w : G)⁻¹ := by group
        _ = (w : G)⁻¹ * (w * x) * (w : G)⁻¹ := by rw [hwx]
        _ = x * (w : G)⁻¹ := by group
    calc (w : G) * t * (w : G)⁻¹ * t * x = (w : G) * t * (w : G)⁻¹ * (t * x) := by group
      _ = (w : G) * t * (w : G)⁻¹ * (x * t) := by rw [hxt]
      _ = (w : G) * t * ((w : G)⁻¹ * x) * t := by group
      _ = (w : G) * t * (x * (w : G)⁻¹) * t := by rw [hwx']
      _ = (w : G) * (t * x) * (w : G)⁻¹ * t := by group
      _ = (w : G) * (x * t) * (w : G)⁻¹ * t := by rw [hxt]
      _ = ((w : G) * x) * t * (w : G)⁻¹ * t := by group
      _ = (x * w) * t * (w : G)⁻¹ * t := by rw [hwx]
      _ = x * ((w : G) * t * (w : G)⁻¹ * t) := by group
  have hmul : ∀ w w' : H, ((w : G) * w') * t * ((w : G) * w')⁻¹ * t =
      ((w : G) * t * (w : G)⁻¹ * t) * ((w' : G) * t * (w' : G)⁻¹ * t) := by
    intro w w'
    have hw := (mem_inf.mp w.2).1
    have hw' := (mem_inf.mp w'.2).1
    have hρ' := hR.conj_t_mul_t_mem hw'
    have hρ := hR.conj_t_mul_t_mem hw
    have hc1 : (w : G) * ((w' : G) * t * (w' : G)⁻¹ * t) =
        ((w' : G) * t * (w' : G)⁻¹ * t) * w := (hR.comm_of_mem_sup (hR.le hρ') hw).symm
    have hc2 := hR.comm _ (hR.le hρ) _ (hR.le hρ')
    calc ((w : G) * w') * t * ((w : G) * w')⁻¹ * t =
        (w : G) * ((w' : G) * t * (w' : G)⁻¹ * t) * t⁻¹ * (w : G)⁻¹ * t := by group
      _ = ((w' : G) * t * (w' : G)⁻¹ * t) * ((w : G) * t * (w : G)⁻¹ * t) := by
        rw [hc1, hti]
        group
      _ = ((w : G) * t * (w : G)⁻¹ * t) * ((w' : G) * t * (w' : G)⁻¹ * t) := hc2.symm
  let Ψ : H →* K :=
    { toFun := fun w => ⟨(w : G) * t * (w : G)⁻¹ * t, hmemK w⟩
      map_one' := by
        apply Subtype.ext
        show (1 : G) * t * (1 : G)⁻¹ * t = 1
        rw [one_mul, inv_one, mul_one, ← sq, hR.t_sq]
      map_mul' := fun w w' => by
        apply Subtype.ext
        exact hmul w w' }
  have hker : Nat.card Ψ.ker ≤ Nat.card (T₁ ⊓ centralizer ({x} : Set G) : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun w => ⟨((w : H) : G), ?_⟩) ?_
    · have hw := (w : H).2
      have h1 : Ψ w = 1 := w.2
      have h2 : ((w : H) : G) * t * ((w : H) : G)⁻¹ * t = 1 := congrArg Subtype.val h1
      have hwt : ((w : H) : G) * t = t * ((w : H) : G) := by
        have h3 : ((w : H) : G) * t * ((w : H) : G)⁻¹ = t⁻¹ := eq_inv_of_mul_eq_one_left h2
        rw [hti] at h3
        calc ((w : H) : G) * t = ((w : H) : G) * t * ((w : H) : G)⁻¹ * ((w : H) : G) := by group
          _ = t * ((w : H) : G) := by rw [h3]
      exact mem_inf.mpr ⟨hR.mem_T₁_of_comm_t (mem_inf.mp hw).1 hwt, (mem_inf.mp hw).2⟩
    · intro w w' hww'
      have := congrArg Subtype.val hww'
      exact Subtype.ext (Subtype.ext this)
  calc Nat.card H = Nat.card Ψ.ker * Nat.card Ψ.range := (Subgroup.card_ker_mul_card_range Ψ).symm
    _ ≤ Nat.card (T₁ ⊓ centralizer ({x} : Set G) : Subgroup G) * Nat.card K :=
      Nat.mul_le_mul hker (Subgroup.card_le_card_group _)

end U3R2

theorem coprime_two_pow_sq_sub_one {f : ℕ} (hf : 1 ≤ f) (n : ℕ) :
    Nat.Coprime (2 ^ n) ((2 ^ f) ^ 2 - 1) := by
  refine Nat.Coprime.pow_left n (Nat.coprime_two_left.mpr ?_)
  have hev : Even ((2 ^ f) ^ 2) :=
    Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩
  have h1 : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  exact Nat.Even.sub_odd h1 hev odd_one

namespace U3SemilinearCoords

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G} {T : Subgroup G}
  {E : Type} [Field E] [Finite E] [CharP E 2] {σ : E →+* E} {u v : G → E}
  (hS : U3SemilinearCoords L T f σ u v)
include hS

omit [CharP E 2] in
theorem mem_sup_of_u_conj_eq_mul (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T)
    {μ : E} (hx : ∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = μ * u y) : x ∈ szT₁ L T ⊔ zpowers t := by
  classical
  have hc := hS.coords
  have : Fintype E := Fintype.ofFinite E
  obtain ⟨-, -, -, hTN₁, -⟩ := h.start_of_card_sylow hS2
  have hxN := hTN₁ hxT
  obtain ⟨n, hn⟩ := h.isPGroup ⟨x, hxT⟩
  have hxn : x ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  obtain ⟨y₁, hy₁, hy₁u⟩ := hc.u_surj 1
  have h1 := U3RootCoords.u_conj_pow hxN hx (2 ^ n) y₁ hy₁
  rw [hxn, one_mul, inv_one, mul_one, hy₁u, mul_one] at h1
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at h1
    exact one_ne_zero h1
  have hμq : μ ^ ((2 ^ f) ^ 2 - 1) = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one μ hμ0
    rwa [← Nat.card_eq_fintype_card, hS.card] at this
  have hμ1 : μ = 1 := by
    have := (pow_gcd_eq_one (a := μ)).mpr ⟨h1.symm, hμq⟩
    rwa [coprime_two_pow_sq_sub_one (by have := h.two_le; omega) n, pow_one] at this
  subst hμ1
  obtain ⟨μ', -, τ', e', hx'⟩ := hS.semilinear x (h.le_normalizer hxT) hxN
  have hτ' : ∀ a, μ' * τ' a = a := by
    intro a
    obtain ⟨y, hy, rfl⟩ := hc.u_surj a
    rw [← (hx' y hy).1, hx y hy, one_mul]
  have hμ' : μ' = 1 := by have := hτ' 1; rwa [map_one, mul_one] at this
  have hτ'1 : ∀ a, τ' a = a := fun a => by have := hτ' a; rwa [hμ', one_mul] at this
  refine h.mem_sup_of_forall_mem_szA₁_of_card_sylow hS2 ?_ fun y hy => ?_
  · have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (h.le hxT)
    have hle : szA L T t ≤ centralizer ({x} : Set G) := by
      refine sup_le (fun a ha => mem_centralizer_singleton_iff.mpr ?_)
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hxt.symm))
      have haT := szA₁_le _ ha
      have hu0 := (hS.mem_szA₁_iff a haT).mp ha
      have hxa : x * a * x⁻¹ = a := by
        refine hc.inj _ ((mem_normalizer_iff.mp hxN a).mp haT) _ haT ?_ ?_
        · rw [hx a haT, one_mul]
        · rw [(hx' a haT).2, hu0, map_zero, mul_zero, hμ', hτ'1, map_one, mul_one, one_mul]
          simp [TraceForm.form]
      calc a * x = x * a * x⁻¹ * x := by rw [hxa]
        _ = x * a := by group
    exact mem_centralizer_iff.mpr fun a ha => mem_centralizer_singleton_iff.mp (hle ha)
  · have hxy : x * y * x⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hxN y).mp hy
    refine (hS.mem_szA₁_iff _ (mul_mem (inv_mem hy) hxy)).mpr ?_
    rw [hc.u_mul_inv hy hxy, hx y hy, one_mul, sub_self]

theorem sigma_of_sq_mem (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T)
    (hx : x ∉ szT₁ L T ⊔ zpowers t) (hx2 : x ^ 2 ∈ szT₁ L T ⊔ zpowers t) {μ : E}
    {τ : E →+* E} {e : E}
    (hxd : ∀ y ∈ szT₁ L T, u (x * y * x⁻¹) = μ * τ (u y) ∧
      v (x * y * x⁻¹) = μ * σ μ * τ (v y) + TraceForm.form σ e (μ * τ (u y))) :
    (∀ a, τ a = σ a) ∧ μ * σ μ = 1 := by
  have hc := hS.coords
  obtain ⟨-, -, -, hTN₁, -⟩ := h.start_of_card_sylow hS2
  have hxN := hTN₁ hxT
  obtain ⟨y₁, hy₁, z, hz, hyz⟩ := exists_mul_eq_of_mem_sup_zpowers h.mem_centralizer_szT₁ hx2
  have hx2u : ∀ y ∈ szT₁ L T, u (x ^ 2 * y * (x ^ 2)⁻¹) = u y := by
    intro y hy
    have hzy : y * z = z * y :=
      commute_of_mem_zpowers hz (mem_centralizer_iff.mp h.mem_centralizer_szT₁ y hy)
    have e : x ^ 2 * y * (x ^ 2)⁻¹ = y₁ * y * y₁⁻¹ := by
      rw [← hyz]
      calc y₁ * z * y * (y₁ * z)⁻¹ = y₁ * (z * y) * z⁻¹ * y₁⁻¹ := by group
        _ = y₁ * (y * z) * z⁻¹ * y₁⁻¹ := by rw [hzy]
        _ = y₁ * y * y₁⁻¹ := by group
    rw [e]
    exact (hc.conj_coords hy₁ hy).1
  have hττ : ∀ a, μ * τ μ * τ (τ a) = a := by
    intro a
    obtain ⟨y, hy, rfl⟩ := hc.u_surj a
    have hxy : x * y * x⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hxN y).mp hy
    have e : x ^ 2 * y * (x ^ 2)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by rw [pow_two]; group
    have h1 := hx2u y hy
    rw [e, (hxd _ hxy).1, (hxd y hy).1, map_mul] at h1
    linear_combination h1
  have hμτ : μ * τ μ = 1 := by have := hττ 1; rwa [map_one, map_one, mul_one] at this
  have hinv : ∀ a, τ (τ a) = a := fun a => by have := hττ a; rwa [hμτ, one_mul] at this
  have hne : ∃ a, τ a ≠ a := by
    by_contra hall
    push Not at hall
    exact hx (hS.mem_sup_of_u_conj_eq_mul h hS2 hxT (μ := μ) fun y hy => by
      rw [(hxd y hy).1, hall])
  have hτσ := SemilinearField.eq_sigma_of_involutive hS.sigma hS.card hS.card_fixed τ hinv hne
  refine ⟨hτσ, ?_⟩
  rw [← hτσ μ]
  exact hμτ

theorem comm_szA₁_and_exists_u_of_sq_mem (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T)
    (hx : x ∉ szT₁ L T ⊔ zpowers t) (hx2 : x ^ 2 ∈ szT₁ L T ⊔ zpowers t) :
    (∀ a ∈ szA₁ (szT₁ L T), x * a = a * x) ∧
      ∃ a₁ : E, ∀ y ∈ szT₁ L T, x * y = y * x → u y = 0 ∨ u y = a₁ := by
  have hc := hS.coords
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  obtain ⟨-, -, -, hTN₁, -⟩ := h.start_of_card_sylow hS2
  have hxN := hTN₁ hxT
  obtain ⟨μ, -, τ, e, hxd⟩ := hS.semilinear x (h.le_normalizer hxT) hxN
  obtain ⟨hτ, hN⟩ := hS.sigma_of_sq_mem h hS2 hxT hx hx2 hxd
  have hfix : ∀ y ∈ szT₁ L T, x * y = y * x →
      μ * σ (u y) = u y ∧ u y * σ (u y) + TraceForm.form σ e (u y) = 0 := by
    intro y hy hxy
    have hconj : x * y * x⁻¹ = y := by rw [hxy, mul_inv_cancel_right]
    obtain ⟨h1, h3⟩ := hxd y hy
    rw [hconj] at h1 h3
    simp only [hτ] at h1 h3
    rw [hN, one_mul, ← h1] at h3
    have hr := hc.rel y hy
    exact ⟨h1.symm, by linear_combination hr - h3 - σ (v y) * h2⟩
  refine ⟨fun a ha => ?_, ?_⟩
  · have haT := szA₁_le _ ha
    have hu0 := (hS.mem_szA₁_iff a haT).mp ha
    obtain ⟨h1, h3⟩ := hxd a haT
    simp only [hτ, hu0, map_zero, mul_zero] at h1 h3
    have hxa : x * a * x⁻¹ = a := by
      refine hc.inj _ ((mem_normalizer_iff.mp hxN a).mp haT) _ haT (by rw [h1, hu0]) ?_
      rw [h3, hN, one_mul, hc.sigma_v_of_u_eq_zero haT hu0]
      simp [TraceForm.form]
    calc x * a = x * a * x⁻¹ * x := by group
      _ = a * x := by rw [hxa]
  · by_cases hex : ∃ y ∈ szT₁ L T, x * y = y * x ∧ u y ≠ 0
    · obtain ⟨y₀, hy₀, hxy₀, hu₀⟩ := hex
      refine ⟨u y₀, fun y hy hxy => ?_⟩
      by_cases hu : u y = 0
      · exact Or.inl hu
      right
      obtain ⟨hl₀, hq₀⟩ := hfix y₀ hy₀ hxy₀
      obtain ⟨hl, hq⟩ := hfix y hy hxy
      have hσa₀ : σ (u y₀) ≠ 0 := (map_ne_zero σ).mpr hu₀
      have hlam : σ (u y / u y₀) = u y / u y₀ := by
        rw [map_div₀, div_eq_div_iff hσa₀ hu₀]
        calc σ (u y) * u y₀ = σ (u y) * (μ * σ (u y₀)) := by rw [hl₀]
          _ = (μ * σ (u y)) * σ (u y₀) := by ring
          _ = u y * σ (u y₀) := by rw [hl]
      have ha : u y = u y / u y₀ * u y₀ := by rw [div_mul_cancel₀ _ hu₀]
      rw [ha, TraceForm.form_mul_right hlam, map_mul, hlam] at hq
      have hquad : u y / u y₀ * (u y / u y₀ + 1) * (u y₀ * σ (u y₀)) = 0 := by
        linear_combination hq - (u y / u y₀) * hq₀ + (u y / u y₀) * (u y₀ * σ (u y₀)) * h2
      have hl0 : u y / u y₀ ≠ 0 := div_ne_zero hu hu₀
      have hN₀ : u y₀ * σ (u y₀) ≠ 0 := mul_ne_zero hu₀ hσa₀
      rcases mul_eq_zero.mp hquad with h' | h'
      · rcases mul_eq_zero.mp h' with h'' | h''
        · exact absurd h'' hl0
        · have hl1 : u y / u y₀ = 1 := by linear_combination h'' - h2
          rw [ha, hl1, one_mul]
      · exact absurd h' hN₀
    · push Not at hex
      exact ⟨0, fun y hy hxy => Or.inl (hex y hy hxy)⟩

theorem exists_not_comm_of_sq_not_mem (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T)
    (hx2 : x ^ 2 ∉ szT₁ L T ⊔ zpowers t) : ∃ a ∈ szA₁ (szT₁ L T), x * a ≠ a * x := by
  by_contra hall
  push Not at hall
  have hc := hS.coords
  have hσσ : ∀ z, σ (σ z) = z := TraceForm.sigma_sigma hS.sigma hS.card
  obtain ⟨-, -, -, hTN₁, -⟩ := h.start_of_card_sylow hS2
  have hxN := hTN₁ hxT
  obtain ⟨μ, -, τ, e, hxd⟩ := hS.semilinear x (h.le_normalizer hxT) hxN
  have hA : ∀ c, σ c = c → μ * σ μ * τ c = c := by
    intro c hc'
    obtain ⟨a, haT, ha0, hac⟩ :=
      hc.surj 0 c (by rw [hc', CharTwo.add_self_eq_zero, zero_mul, add_zero])
    have haA := (hS.mem_szA₁_iff a haT).mpr ha0
    have hxa : x * a * x⁻¹ = a := by rw [hall a haA, mul_inv_cancel_right]
    have h3 := (hxd a haT).2
    rw [hxa, ha0, map_zero, mul_zero, hac] at h3
    simp only [TraceForm.form, map_zero, mul_zero, add_zero] at h3
    exact h3.symm
  have hN : μ * σ μ = 1 := by
    have := hA 1 (map_one σ)
    rwa [map_one, mul_one] at this
  have hτF : ∀ c, σ c = c → τ c = c := fun c hc' => by
    have := hA c hc'
    rwa [hN, one_mul] at this
  have hinv := SemilinearField.apply_apply_of_fixed hS.sigma hσσ τ hτF
  apply hx2
  refine hS.mem_sup_of_u_conj_eq_mul h hS2 (pow_mem hxT 2) (μ := μ * τ μ) fun y hy => ?_
  have hxy : x * y * x⁻¹ ∈ szT₁ L T := (mem_normalizer_iff.mp hxN y).mp hy
  have e : x ^ 2 * y * (x ^ 2)⁻¹ = x * (x * y * x⁻¹) * x⁻¹ := by rw [pow_two]; group
  rw [e, (hxd _ hxy).1, (hxd y hy).1, map_mul, hinv]
  ring

theorem card_centralizer_le (h : U3Start G L f t T)
    (hS2 : ∀ S : Sylow 2 (centralizer (L : Set G)), Nat.card S = 2) {x : G} (hxT : x ∈ T)
    (hx : x ∉ szT₁ L T ⊔ zpowers t) :
    Nat.card (szT₁ L T ⊓ centralizer ({x} : Set G) : Subgroup G) ≤
      2 * Nat.card (szA₁ (szT₁ L T) ⊓ centralizer ({x} : Set G) : Subgroup G) := by
  classical
  have hc := hS.coords
  obtain ⟨n, hn⟩ := h.isPGroup ⟨x, hxT⟩
  have hxn : x ^ (2 ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  have hP : ∃ j, x ^ (2 ^ j) ∈ szT₁ L T ⊔ zpowers t := ⟨n, by rw [hxn]; exact one_mem _⟩
  have hj := Nat.find_spec hP
  have hj0 : Nat.find hP ≠ 0 := by
    intro h0
    rw [h0, pow_zero, pow_one] at hj
    exact hx hj
  have hjm : x ^ (2 ^ (Nat.find hP - 1)) ∉ szT₁ L T ⊔ zpowers t :=
    Nat.find_min hP (by omega)
  have hx'2 : (x ^ (2 ^ (Nat.find hP - 1))) ^ 2 ∈ szT₁ L T ⊔ zpowers t := by
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega)]
    exact hj
  obtain ⟨-, a₁, ha₁⟩ :=
    hS.comm_szA₁_and_exists_u_of_sq_mem h hS2 (pow_mem hxT _) hjm hx'2
  set B := szT₁ L T ⊓ centralizer ({x} : Set G) with hB
  have hBT : B ≤ szT₁ L T := inf_le_left
  obtain ⟨ψ, hψ⟩ := hc.exists_hom hBT
  rw [U3RootCoords.card_eq_mul_card_range hS.mem_szA₁_iff hBT hψ, mul_comm]
  refine Nat.mul_le_mul ?_ (card_le_of_le (le_inf inf_le_right (inf_le_left.trans inf_le_right)))
  have hval : ∀ z ∈ ψ.range, Multiplicative.toAdd z = 0 ∨ Multiplicative.toAdd z = a₁ := by
    rintro _ ⟨b, rfl⟩
    rw [hψ, toAdd_ofAdd]
    have hbx : (b : G) * x = x * b := mem_centralizer_singleton_iff.mp (mem_inf.mp b.2).2
    have hbx' : x ^ (2 ^ (Nat.find hP - 1)) * b = b * x ^ (2 ^ (Nat.find hP - 1)) :=
      ((Commute.pow_left (show Commute x (b : G) from hbx.symm) _)).eq
    exact ha₁ b (hBT b.2) hbx'
  calc Nat.card ψ.range ≤ Nat.card Bool := by
        refine Nat.card_le_card_of_injective (fun z => decide (Multiplicative.toAdd
          (z : Multiplicative E) = 0)) fun z z' hzz' => ?_
        apply Subtype.ext
        rcases hval z z.2 with h1 | h1 <;> rcases hval z' z'.2 with h2 | h2
        · exact Multiplicative.toAdd.injective (h1.trans h2.symm)
        · simp only [h1, h2, decide_true] at hzz'
          by_cases ha : a₁ = 0
          · exact Multiplicative.toAdd.injective (h1.trans (h2.trans ha).symm)
          · simp [ha] at hzz'
        · simp only [h1, h2, decide_true] at hzz'
          by_cases ha : a₁ = 0
          · exact Multiplicative.toAdd.injective ((h1.trans ha).trans h2.symm)
          · simp [ha] at hzz'
        · exact Multiplicative.toAdd.injective (h1.trans h2.symm)
    _ = 2 := Nat.card_eq_two_iff' false |>.mpr ⟨true, by simp, fun b hb => by simpa using hb⟩

end U3SemilinearCoords

end CFSG.SeitzReduction.RankOne
