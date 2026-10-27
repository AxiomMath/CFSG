module

public import CFSG.GH74.GLS.Stage4.T2P71SylA

public section

namespace CFSG.GH74.GLS.Stage4.Rest.T6.P71

open Subgroup CFSG.GH74.GLS.Stage4.Hex CFSG.GH74.GLS.Stage4.Rest.T2 CFSG.GH74.GLS.IVK.Proofs2
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {N : T2N3 G} {u : G} {p : ℕ}

abbrev ZR (N : T2N3 G) (p : ℕ) : Subgroup G := R₂ N p ⊓ Subgroup.centralizer (R₂ N p : Set G)

theorem mem_X₂_of_sq (h : T6Ctx N u p) {s : G} (hs : s ∈ R₂ N p) (h3 : s * s ∈ N.X₂) : s ∈ N.X₂ := by
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

theorem X₂_le_ZR (h : T6Ctx N u p) : N.X₂ ≤ ZR N p := by
  intro w hw
  refine ⟨X₂_le_R₂ h hw, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
  have := R₂_cent h r hr w hw
  calc r * w = (r * w * r⁻¹) * r := by group
    _ = w * r := by rw [this]

theorem norm_ZR {g : G} (hg : g ∈ M₂ N) {y : G} (hy : y ∈ ZR N p) : g * y * g⁻¹ ∈ ZR N p := by
  refine ⟨R₂_norm N p hg hy.1, Subgroup.mem_centralizer_iff.2 fun r hr => ?_⟩
  have hr' : g⁻¹ * r * g ∈ R₂ N p := by simpa using R₂_norm N p ((M₂ N).inv_mem hg) hr
  have := Subgroup.mem_centralizer_iff.1 hy.2 _ hr'
  calc r * (g * y * g⁻¹) = g * ((g⁻¹ * r * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * r * g)) * g⁻¹ := by rw [this]
    _ = (g * y * g⁻¹) * r := by group

theorem card_ZR_le (h : T6Ctx N u p) {m : ℕ} (hMod : T6Mod N p m) (hm : N.q₁ = p ^ m) (hR : RCard N p)
    (hnab : ∃ x ∈ R₂ N p, ∃ y ∈ R₂ N p, x * y ≠ y * x) : Nat.card ↥(ZR N p) ≤ N.q₂ ^ 3 := by
  have hXZ := X₂_le_ZR h
  have hne : ZR N p ≠ R₂ N p := by
    intro heq
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    apply hab
    have haZ : a ∈ ZR N p := by rw [heq]; exact ha
    exact (Subgroup.mem_centralizer_iff.1 haZ.2 b hb).symm
  have hle := hMod.card (R₂ N p) (ZR N p) inf_le_left
    (fun k hk a ha => R₂_norm N p (K₁_le_M₂ h hk) ha)
    (fun k hk b hb => norm_ZR (K₁_le_M₂ h hk) hb)
    (fun a ha a' ha' => hXZ ((R₂_inv_comm h).2 a ha a' ha'))
    (fun a ha => hXZ (R₂_exp h a ha))
    (fun a ha => hXZ ((R₂_inv_comm h).1 a ha)) hne
  have hrel : (ZR N p).relIndex (R₂ N p) * Nat.card ↥(ZR N p) = Nat.card ↥(R₂ N p) := by
    have := Subgroup.relIndex_mul_card (ZR N p) (R₂ N p)
    rwa [inf_eq_left.2 (inf_le_left : ZR N p ≤ R₂ N p)] at this
  have hpos : 0 < Nat.card ↥(ZR N p) := Nat.card_pos
  have h1 : p ^ (2 * m) * Nat.card ↥(ZR N p) ≤ N.q₁ ^ 2 * N.q₂ ^ 3 := by
    rw [← hR.card, ← hrel]
    exact Nat.mul_le_mul_right _ hle
  have h2 : p ^ (2 * m) = N.q₁ ^ 2 := by rw [hm, ← pow_mul, mul_comm, pow_mul]
  rw [h2] at h1
  have hq : 0 < N.q₁ ^ 2 := by
    have := h.sec5.loc.q₁_ge
    positivity
  exact Nat.le_of_mul_le_mul_left (by rw [mul_comm] at h1; linarith) hq

theorem center_le_R₂ (h : T6Ctx N u p) (hR : RCard N p) {y : G} (hy : y ∈ R₂ N p ⊔ N.X₁)
    (hcen : ∀ x ∈ R₂ N p ⊔ N.X₁, x * y = y * x) : y ∈ R₂ N p := by
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
  simpa using hr

omit [Finite G] in
theorem norm_center {P : Subgroup G} {g : G} (h1 : ∀ k ∈ P, g * k * g⁻¹ ∈ P)
    (h2 : ∀ k ∈ P, g⁻¹ * k * g ∈ P) :
    ∀ y ∈ P ⊓ Subgroup.centralizer (P : Set G), g * y * g⁻¹ ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
  intro y hy
  refine ⟨h1 y hy.1, Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
  have hs' := h2 s hs
  have := Subgroup.mem_centralizer_iff.1 hy.2 _ hs'
  calc s * (g * y * g⁻¹) = g * ((g⁻¹ * s * g) * y) * g⁻¹ := by group
    _ = g * (y * (g⁻¹ * s * g)) * g⁻¹ := by rw [this]
    _ = (g * y * g⁻¹) * s := by group

omit [Finite G] in
theorem odd_conj_fix {x z : G} (hodd : Odd (orderOf x)) (h : x * x * z * (x * x)⁻¹ = z) :
    x * z * x⁻¹ = z := by
  obtain ⟨j, hj⟩ := hodd
  have h1 : x ^ (2 * j + 1) = 1 := by rw [← hj]; exact pow_orderOf_eq_one x
  have hA : ∀ i : ℕ, x ^ (2 * i) * z * (x ^ (2 * i))⁻¹ = z := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      have e : x ^ (2 * (i + 1)) = x ^ (2 * i) * (x * x) := by
        rw [mul_add, mul_one, pow_add, pow_two]
      rw [e]
      calc x ^ (2 * i) * (x * x) * z * (x ^ (2 * i) * (x * x))⁻¹
          = x ^ (2 * i) * (x * x * z * (x * x)⁻¹) * (x ^ (2 * i))⁻¹ := by group
        _ = x ^ (2 * i) * z * (x ^ (2 * i))⁻¹ := by rw [h]
        _ = z := ih
  have hx : x = x ^ (2 * (j + 1)) := by
    have : x ^ (2 * (j + 1)) = x ^ (2 * j + 1) * x := by rw [show 2 * (j + 1) = (2 * j + 1) + 1 by ring, pow_succ]
    rw [this, h1, one_mul]
  have := hA (j + 1)
  rw [← hx] at this
  exact this

theorem no_cycle' (h : T6Ctx N u p) {m : ℕ} (hMod : T6Mod N p m) (hm : N.q₁ = p ^ m) (hR : RCard N p)
    (hnab : ∃ x ∈ R₂ N p, ∃ y ∈ R₂ N p, x * y ≠ y * x) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {x : G}
    (hxP : x ∈ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hxU : x ∈ Subgroup.normalizer ((t2U N.z u : Subgroup G) : Set G)) (hodd : Odd (orderOf x)) :
    x * N.z * x⁻¹ = N.z := by
  by_contra hxz
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  have hxP1 : ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, x * k * x⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀ := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 hxP k).1 hk
  have hxP2 : ∀ k ∈ R₂ N p ⊔ N.X₁ ⊔ P₀, x⁻¹ * k * x⁻¹⁻¹ ∈ R₂ N p ⊔ N.X₁ ⊔ P₀ := fun k hk =>
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hxP) k).1 hk
  have hxU1 : ∀ g ∈ t2U N.z u, x * g * x⁻¹ ∈ t2U N.z u := fun g hg =>
    (Subgroup.mem_normalizer_iff.1 hxU g).1 hg
  have hxU2 : ∀ g ∈ t2U N.z u, x⁻¹ * g * x⁻¹⁻¹ ∈ t2U N.z u := fun g hg =>
    (Subgroup.mem_normalizer_iff.1 ((Subgroup.normalizer _).inv_mem hxU) g).1 hg
  have hPx := norm_P_of h hP₀F hxP1 hxU1
  have hPx' := norm_P_of h hP₀F hxP2 hxU2
  set P : Subgroup G := R₂ N p ⊔ N.X₁ with hPdef
  set Z : Subgroup G := P ⊓ Subgroup.centralizer (P : Set G) with hZdef
  have hZR : Z ≤ R₂ N p := fun y hy =>
    center_le_R₂ h hR hy.1 (fun s hs => Subgroup.mem_centralizer_iff.1 hy.2 s hs)
  have hX₂Z : N.X₂ ≤ Z := by
    intro w hw
    refine ⟨Subgroup.mem_sup_left (X₂_le_R₂ h hw), Subgroup.mem_centralizer_iff.2 fun s hs => ?_⟩
    obtain ⟨r, hr, x₁, hx₁, rfl⟩ := t6_mem_sup_of_le_normalizer (X₁_le_normalizer_R₂ h) hs
    have hwK₂ : w ∈ N.K₂ := by rw [h.sec5.loc.K₂_eq]; exact Subgroup.mem_sup_left hw
    have h1 : r * w = w * r := by
      have := R₂_cent h r hr w hw
      calc r * w = (r * w * r⁻¹) * r := by group
        _ = w * r := by rw [this]
    have h2 : x₁ * w = w * x₁ := h.sec5.loc.K_comm x₁ (X₁_le_K₁ h hx₁) w hwK₂
    calc r * x₁ * w = r * (x₁ * w) := by group
      _ = r * (w * x₁) := by rw [h2]
      _ = (r * w) * x₁ := by group
      _ = (w * r) * x₁ := by rw [h1]
      _ = w * (r * x₁) := by group
  have hZU : ∀ g ∈ t2U N.z u, ∀ y ∈ Z, g * y * g⁻¹ ∈ Z := fun g hg y hy =>
    norm_center (P_normU h hg) (fun k hk => by simpa using P_normU h ((t2U N.z u).inv_mem hg) k hk) y hy
  have hZx : ∀ y ∈ Z, x * y * x⁻¹ ∈ Z := fun y hy =>
    norm_center hPx (fun k hk => by simpa using hPx' k hk) y hy
  have hZx' : ∀ y ∈ Z, x⁻¹ * y * x ∈ Z := fun y hy => by
    have := norm_center (P := P) (g := x⁻¹) hPx' (fun k hk => by simpa using hPx k hk) y hy
    rwa [inv_inv] at this
  have hBW := card_four_decomp h hX₂Z hZR hZU
  have hczX : Z ⊓ Subgroup.centralizer {N.z} = N.X₂ := by
    apply le_antisymm
    · intro y hy
      have : y ∈ R₂ N p ⊓ Subgroup.centralizer {N.z} := ⟨hZR hy.1, hy.2⟩
      rwa [R₂_inf_cent_z h] at this
    · intro y hy
      have : y ∈ R₂ N p ⊓ Subgroup.centralizer {N.z} := (R₂_inf_cent_z h).ge hy
      exact ⟨hX₂Z hy, this.2⟩
  have hcz : Nat.card ↥(Z ⊓ Subgroup.centralizer {N.z}) = N.q₂ := by
    rw [hczX, h.sec5.loc.card_X₂]
  have hz : N.z ∈ t2U N.z u := (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inl rfl))
  have hv₁U : x * N.z * x⁻¹ ∈ t2U N.z u := hxU1 _ hz
  have hv₂U : x * (x * N.z * x⁻¹) * x⁻¹ ∈ t2U N.z u := hxU1 _ hv₁U
  have hc1 := t6_card_cent_conj (R := Z) (w := x) hZx hZx' N.z
  have hc2 := t6_card_cent_conj (R := Z) (w := x) hZx hZx' (x * N.z * x⁻¹)
  have hv₂z : x * (x * N.z * x⁻¹) * x⁻¹ ≠ N.z := by
    intro hv
    apply hxz
    refine odd_conj_fix hodd ?_
    calc x * x * N.z * (x * x)⁻¹ = x * (x * N.z * x⁻¹) * x⁻¹ := by group
      _ = N.z := hv
  have hv₂v₁ : x * (x * N.z * x⁻¹) * x⁻¹ ≠ x * N.z * x⁻¹ := by
    intro hv
    apply hxz
    calc x * N.z * x⁻¹ = x⁻¹ * (x * (x * N.z * x⁻¹) * x⁻¹) * x := by group
      _ = x⁻¹ * (x * N.z * x⁻¹) * x := by rw [hv]
      _ = N.z := by group
  have hcu : Nat.card ↥(Z ⊓ Subgroup.centralizer {u}) = N.q₂ ∧
      Nat.card ↥(Z ⊓ Subgroup.centralizer {N.z * u}) = N.q₂ := by
    rcases U_cases h hv₁U with h1 | h1 | h1 | h1
    · exfalso; apply hz1
      calc N.z = x⁻¹ * (x * N.z * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    · exact absurd h1 hxz
    ·
      rcases U_cases h hv₂U with h2 | h2 | h2 | h2
      · exfalso; apply hz1
        calc N.z = x⁻¹ * (x⁻¹ * (x * (x * N.z * x⁻¹) * x⁻¹) * x) * x := by group
          _ = 1 := by rw [h2]; group
      · exact absurd h2 hv₂z
      · exact absurd (h2.trans h1.symm) hv₂v₁
      · rw [h2] at hc2
        rw [h1] at hc1 hc2
        exact ⟨by rw [← hcz]; exact hc1.symm, by rw [← hcz, hc1, ← hc2]⟩
    ·
      rcases U_cases h hv₂U with h2 | h2 | h2 | h2
      · exfalso; apply hz1
        calc N.z = x⁻¹ * (x⁻¹ * (x * (x * N.z * x⁻¹) * x⁻¹) * x) * x := by group
          _ = 1 := by rw [h2]; group
      · exact absurd h2 hv₂z
      · rw [h2] at hc2
        rw [h1] at hc1 hc2
        exact ⟨by rw [← hcz, hc1, ← hc2], by rw [← hcz]; exact hc1.symm⟩
      · exact absurd (h2.trans h1.symm) hv₂v₁
  have hZc : Nat.card ↥Z = N.q₂ ^ 3 := by
    rw [hBW, hcu.1, hcu.2]; ring
  have hZZR : Z ≤ ZR N p := fun y hy =>
    ⟨hZR hy, Subgroup.mem_centralizer_iff.2 fun s hs =>
      Subgroup.mem_centralizer_iff.1 hy.2 s (Subgroup.mem_sup_left hs)⟩
  have hcard := card_ZR_le h hMod hm hR hnab
  have hZeq : Z = ZR N p := Subgroup.eq_of_le_of_card_ge hZZR (by rw [hZc]; exact hcard)
  have hX₁C : N.X₁ ≤ Subgroup.centralizer (ZR N p : Set G) := by
    intro x₁ hx₁
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    have hyZ : y ∈ Z := hZeq ▸ hy
    exact (Subgroup.mem_centralizer_iff.1 hyZ.2 x₁ (Subgroup.mem_sup_right hx₁)).symm
  have hX₁'C : N.X₁' ≤ Subgroup.centralizer (ZR N p : Set G) := by
    intro y' hy'
    refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
    have hx := h.sec5.loc.w₁_swap' y' hy'
    have hw₁M : N.w₁ ∈ M₂ N := K₁_le_M₂ h h.sec5.loc.w₁_mem
    have hc' : N.w₁ * c * N.w₁⁻¹ ∈ ZR N p := norm_ZR hw₁M hc
    have h1 := Subgroup.mem_centralizer_iff.1 (hX₁C hx) _ hc'
    calc c * y' = N.w₁⁻¹ * ((N.w₁ * c * N.w₁⁻¹) * (N.w₁ * y' * N.w₁⁻¹)) * N.w₁ := by group
      _ = N.w₁⁻¹ * ((N.w₁ * y' * N.w₁⁻¹) * (N.w₁ * c * N.w₁⁻¹)) * N.w₁ := by rw [h1]
      _ = y' * c := by group
  have hzC : N.z ∈ Subgroup.centralizer (ZR N p : Set G) := by
    have : N.K₁ ≤ Subgroup.centralizer (ZR N p : Set G) := by
      rw [h.sec5.loc.K₁_eq]; exact sup_le hX₁C hX₁'C
    exact this h.sec5.loc.z_mem_K₁
  have hZRX : ZR N p ≤ N.X₂ := by
    intro y hy
    have hzy : N.z * y * N.z⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.1 hzC y hy
      calc N.z * y * N.z⁻¹ = (y * N.z) * N.z⁻¹ := by rw [this]
        _ = y := by group
    have h1 := (R₂_inv_comm h).1 y hy.1
    rw [hzy] at h1
    exact mem_X₂_of_sq h hy.1 h1
  have hle := Subgroup.card_le_of_le hZRX
  rw [h.sec5.loc.card_X₂] at hle
  rw [← hZeq, hZc] at hle
  have hq : 3 ≤ N.q₂ := h.sec5.loc.q₂_ge
  have h3 : N.q₂ < N.q₂ ^ 3 := by
    calc N.q₂ = N.q₂ ^ 1 := (pow_one _).symm
      _ < N.q₂ ^ 3 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem odd_normalizer_cent_T' (h : T6Ctx N u p) {m : ℕ} (hMod : T6Mod N p m) (hm : N.q₁ = p ^ m)
    (hR : RCard N p) (hnab : ∃ x ∈ R₂ N p, ∃ y ∈ R₂ N p, x * y ≠ y * x) (hΩ : T6Omega1 N u)
    {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F) {x : G}
    (hxM : x ∈ Subgroup.normalizer ((R₂ N p ⊔ N.X₁ ⊔ P₀ : Subgroup G) : Set G))
    (hxT : ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, x * t * x⁻¹ ∈ twoPart N.H h.sec5.loc.H_comm)
    (hodd : Odd (orderOf x)) : ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, x * t = t * x := by
  obtain ⟨hz2, hu2, hzu, hz1, hu1, hne⟩ := zu_facts h
  have hxU := norm_U_of_norm_T h hΩ hxT
  have hxUn : x ∈ Subgroup.normalizer ((t2U N.z u : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_fintype hxU
  have hxz := no_cycle' h hMod hm hR hnab hP₀F hxM hxUn hodd
  have hxu : x * u * x⁻¹ = u := by
    have hu' : u ∈ t2U N.z u := (t2U_mem hz2 hu2 hzu).2 (Or.inr (Or.inr (Or.inl rfl)))
    rcases U_cases h (hxU u hu') with h1 | h1 | h1 | h1
    · exfalso
      apply hu1
      calc u = x⁻¹ * (x * u * x⁻¹) * x := by group
        _ = 1 := by rw [h1]; group
    · exfalso
      apply hne
      calc N.z = x⁻¹ * (x * N.z * x⁻¹) * x := by group
        _ = x⁻¹ * (x * u * x⁻¹) * x := by rw [hxz, h1]
        _ = u := by group
    · exact h1
    · exact (t6_odd_swap_false hz2 hz1 hxz h1 hodd).elim
  have hinv : ∀ t ∈ twoPart N.H h.sec5.loc.H_comm, t * t = 1 → x * t * x⁻¹ = t := by
    intro t ht ht2
    rcases hΩ t ht.1 ht2 with rfl | rfl | rfl | rfl
    · group
    · exact hxz
    · exact hxu
    · calc x * (N.z * u) * x⁻¹ = (x * N.z * x⁻¹) * (x * u * x⁻¹) := by group
        _ = N.z * u := by rw [hxz, hxu]
  have hcent := t6_cent_of_cent_invols (T := twoPart N.H h.sec5.loc.H_comm)
    (fun a ha b hb => h.sec5.loc.H_comm a ha.1 b hb.1) (fun t ht => ht.2) hxT hodd hinv
  intro t ht
  calc x * t = (x * t * x⁻¹) * x := by group
    _ = t * x := by rw [hcent t ht]


theorem Pst_sylow' (h : T6Ctx N u p) (hR : RCard N p) (hnab : ∃ x ∈ R₂ N p, ∃ y ∈ R₂ N p, x * y ≠ y * x)
    (hΩ : T6Omega1 N u) {m n : ℕ} (hMod : T6Mod N p m)
    (hm : N.q₁ = p ^ m) (hn : N.q₂ = p ^ n) {P₀ : Subgroup G} (hP₀F : P₀ ≤ N.F)
    (hP₀p : IsPGroup p ↥P₀) (hP₀c : Nat.card ↥P₀ = p ^ (Nat.card ↥N.F).factorization p) :
    ∃ S : Sylow p G, (S : Subgroup G) = R₂ N p ⊔ N.X₁ ⊔ P₀ := by
  have : Fact p.Prime := ⟨h.prime⟩
  set T : Subgroup G := twoPart N.H h.sec5.loc.H_comm with hT
  set Ps : Subgroup G := R₂ N p ⊔ N.X₁ ⊔ P₀ with hPs
  set M : Subgroup G := Subgroup.normalizer (Ps : Set G) with hM
  have hPp : IsPGroup p ↥Ps := Pst_pGroup h hR hP₀F hP₀p
  have hTM : T ≤ M := fun t ht => twoPart_norm_Pst h hΩ hP₀F ht
  have hTp : IsPGroup 2 ↥T := twoPart_isPGroup _ _
  have hTidx : ¬ 2 ∣ T.relIndex M := T_relIndex_odd h hR hΩ hm hn hP₀F hP₀p hP₀c
  have hab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb => h.sec5.loc.H_comm a ha.1 b hb.1
  obtain ⟨K, hKM, hKn, hKodd, hKcard⟩ := t6_two_complement M T hTM hTp hTidx hab
    (fun x hx hxT hodd => odd_normalizer_cent_T' h hMod hm hR hnab hΩ hP₀F hx hxT hodd)
  have hPsM : Ps ≤ M := Subgroup.le_normalizer
  have hKn' : (K.subgroupOf M).Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    exact hKn g g.2 k hk⟩
  have hTcard : Nat.card ↥T = 2 ^ (Nat.card ↥T).factorization 2 := by
    obtain ⟨b, hb⟩ := hTp.exists_card_eq
    rw [hb, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hrelK : K.relIndex M = Nat.card ↥T := by
    have := Subgroup.relIndex_mul_card K M
    rw [inf_eq_left.2 hKM] at this
    have hpos := Nat.card_pos (α := ↥K)
    exact Nat.eq_of_mul_eq_mul_right hpos (this.trans (hKcard.trans (mul_comm _ _)))
  have hPsK : Ps ≤ K := by
    intro x hx
    have hxM : x ∈ M := hPsM hx
    have h1 : (⟨x, hxM⟩ : ↥M) ^ (K.subgroupOf M).index ∈ K.subgroupOf M :=
      Subgroup.pow_index_mem (K.subgroupOf M) _
    have h2 : x ^ Nat.card ↥T ∈ K := by
      rw [← hrelK]
      have := (Subgroup.mem_subgroupOf).1 h1
      simpa [Subgroup.relIndex] using this
    have hord : ∃ j : ℕ, orderOf x = p ^ j := by
      have := (IsPGroup.iff_orderOf (p := p)).1 hPp ⟨x, hx⟩
      obtain ⟨j, hj⟩ := this
      exact ⟨j, by simpa [Subgroup.orderOf_coe] using hj⟩
    have hcop : Nat.Coprime p (Nat.card ↥T) := by
      obtain ⟨b, hb⟩ := hTp.exists_card_eq
      rw [hb]
      exact Nat.Coprime.pow_right b ((Nat.coprime_primes h.prime Nat.prime_two).2 h.p_ne_two)
    exact t6_mem_of_pow hord hcop h2
  have hUM : ∀ g ∈ t2U N.z u, g ∈ M := fun g hg => hTM (U_le_twoPart h hg)
  have hKodd' : Odd (Nat.card ↥K) := Nat.odd_iff.2 (by omega)
  obtain ⟨Q, hQK, hQp, hQc, hQU⟩ := t6_exists_invariant_sylow (hTp.to_le (U_le_twoPart h)) hKodd'
    (fun g hg k hk => hKn g (hUM g hg) k hk) h.prime
  have hQPs : Q ≤ Ps := Pst_max_U h hR hm hn hP₀F hP₀p hP₀c hQp (hQK.trans hKM) hQU
  have hcardPs : Nat.card ↥Ps = p ^ (Nat.card ↥K).factorization p :=
    le_antisymm (card_pSub_le_vp h.prime hPsK hPp) (hQc ▸ Subgroup.card_le_of_le hQPs)
  have hrel : Ps.relIndex M * Nat.card ↥Ps = Nat.card ↥M := by
    have := Subgroup.relIndex_mul_card Ps M
    rwa [inf_eq_left.2 hPsM] at this
  have hN : ¬ p ∣ Ps.relIndex M := by
    intro hd
    have hKpos : Nat.card ↥K ≠ 0 := (Nat.card_pos).ne'
    have h1 : p ^ ((Nat.card ↥K).factorization p + 1) ∣ Nat.card ↥K * Nat.card ↥T := by
      rw [← hKcard, ← hrel, hcardPs, pow_succ']
      exact Nat.mul_dvd_mul_right hd _
    have hcop : Nat.Coprime (p ^ ((Nat.card ↥K).factorization p + 1)) (Nat.card ↥T) := by
      obtain ⟨b, hb⟩ := hTp.exists_card_eq
      rw [hb]
      exact Nat.Coprime.pow _ _ ((Nat.coprime_primes h.prime Nat.prime_two).2 h.p_ne_two)
    have h2 := hcop.dvd_of_dvd_mul_right h1
    have h3 := (Nat.Prime.pow_dvd_iff_le_factorization h.prime hKpos).1 h2
    omega
  have hidx := t6_sylow_of_normalizer h.prime hPp hN
  exact ⟨hPp.toSylow hidx, rfl⟩


end CFSG.GH74.GLS.Stage4.Rest.T6.P71
