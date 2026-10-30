module

public import CFSG.GH74.SectionalRank

public section

namespace CFSG.GH74.QTGen4.Leaves

open CFSG.GH74 in
theorem five_fixed {G : Type} [Group G] [Finite G] (hG : Gen4 G) (W : Subgroup G)
    (hW : CFSG.Open.IsElemAbelian 2 W) (x : G) (hx : orderOf x = 5)
    (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W) (hnt : ∃ w ∈ W, x * w * x⁻¹ ≠ w) :
    ∀ w ∈ W, x * w * x⁻¹ = w → w = 1 := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  letI : Fintype W := Fintype.ofFinite W
  have hcard : Nat.card W ≤ 16 := by
    have := SectionalTwoRankLE.card_le_of_elementary (r := 4) hG W hW
    simpa using this
  have hP : IsPGroup 2 W := fun g => ⟨1, Subtype.ext (by simpa using hW.2 g g.2)⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hP
  let f : Function.End W := fun w => ⟨x * w * x⁻¹, hxW w w.2⟩
  have hfk : ∀ k : ℕ, ∀ w : W, ((f ^ k) w : G) = x ^ k * w * (x ^ k)⁻¹ := by
    intro k
    induction k with
    | zero => intro w; show ((w : W) : G) = _; simp
    | succ k ih =>
      intro w
      rw [pow_succ]
      show ((f ^ k) (f w) : G) = _
      rw [ih]
      show x ^ k * (x * w * x⁻¹) * (x ^ k)⁻¹ = x ^ (k + 1) * w * (x ^ (k + 1))⁻¹
      rw [pow_succ', mul_inv_rev]; group
  have hf5 : f ^ 5 ^ 1 = 1 := by
    funext w
    apply Subtype.ext
    have h5 : x ^ (5 ^ 1) = 1 := by rw [pow_one, ← hx]; exact pow_orderOf_eq_one x
    show ((f ^ 5 ^ 1) w : G) = (w : G)
    rw [hfk, h5]
    simp
  have hmod := Equiv.Perm.card_fixedPoints_modEq (p := 5) (n := 1) hf5
  let C : Subgroup W :=
    { carrier := {w | f w = w}
      mul_mem' := by
        intro a b ha hb
        apply Subtype.ext
        have ha' : x * (a : G) * x⁻¹ = a := congrArg Subtype.val ha
        have hb' : x * (b : G) * x⁻¹ = b := congrArg Subtype.val hb
        show x * ((a : G) * b) * x⁻¹ = (a : G) * b
        calc x * ((a : G) * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) := by group
          _ = a * b := by rw [ha', hb']
      one_mem' := by apply Subtype.ext; simp [f]
      inv_mem' := by
        intro a ha
        apply Subtype.ext
        have ha' : x * (a : G) * x⁻¹ = a := congrArg Subtype.val ha
        show x * (a : G)⁻¹ * x⁻¹ = (a : G)⁻¹
        calc x * (a : G)⁻¹ * x⁻¹ = (x * a * x⁻¹)⁻¹ := by group
          _ = (a : G)⁻¹ := by rw [ha'] }
  have hfix : Fintype.card f.fixedPoints = Nat.card C := by
    rw [← Nat.card_eq_fintype_card]
    exact Nat.card_congr (Equiv.refl _)
  rw [hfix, ← Nat.card_eq_fintype_card, hn] at hmod
  have hdvd : Nat.card C ∣ 2 ^ n := by
    rw [← hn]; exact Subgroup.card_subgroup_dvd_card C
  obtain ⟨m, hm, hCm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hCne : C ≠ ⊤ := by
    intro h
    obtain ⟨w, hw, hwx⟩ := hnt
    have : (⟨w, hw⟩ : W) ∈ C := h ▸ Subgroup.mem_top _
    exact hwx (congrArg Subtype.val this)
  have hmn : m < n := by
    by_contra hmn
    have hm' : m = n := le_antisymm hm (not_lt.1 hmn)
    apply hCne
    apply Subgroup.eq_top_of_card_eq
    rw [hCm, hm', hn]
  have hn4 : n ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hm0 : m = 0 := by
    rw [hCm] at hmod
    interval_cases n <;> interval_cases m <;> simp_all [Nat.ModEq]
  intro w hw hwf
  have : (⟨w, hw⟩ : W) ∈ C := Subtype.ext hwf
  have h1 : Nat.card C = 1 := by rw [hCm, hm0]; rfl
  have hsub : Subsingleton C := (Nat.card_eq_one_iff_unique.1 h1).1
  have := hsub.elim ⟨⟨w, hw⟩, this⟩ 1
  exact congrArg Subtype.val (congrArg Subtype.val this)

theorem exists_five_acting {G : Type} [Group G] [Finite G] (K W : Subgroup G)
    (φ : K →* alternatingGroup (Fin 5)) (hφ : Function.Surjective φ)
    (hker2 : ∀ k : K, φ k = 1 → ∃ n : ℕ, orderOf k = 2 ^ n)
    (hkerC : ∀ k : K, φ k = 1 → ∀ w ∈ W, w * (k : G) = (k : G) * w)
    (hKW : ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ ∈ W)
    (hnt : ∃ k ∈ K, ∃ w ∈ W, w * k ≠ k * w) :
    ∃ x ∈ K, orderOf x = 5 ∧ ∃ w ∈ W, x * w * x⁻¹ ≠ w := by
  classical
  let C : Subgroup K := Subgroup.comap K.subtype (Subgroup.centralizer (W : Set G))
  have hmemC : ∀ k : K, k ∈ C ↔ ∀ w ∈ W, w * (k : G) = (k : G) * w := fun k => by
    simp only [C, Subgroup.mem_comap, Subgroup.coe_subtype, Subgroup.mem_centralizer_iff,
      SetLike.mem_coe]
  have hCn : C.Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [hmemC] at hc ⊢
    intro w hw
    have hw' : (g : G)⁻¹ * w * g ∈ W := by
      have := hKW (g : G)⁻¹ (g⁻¹ : K).2 w hw
      simpa using this
    have hcw := hc _ hw'
    show w * ((g : G) * c * (g : G)⁻¹) = ((g : G) * c * (g : G)⁻¹) * w
    calc w * ((g : G) * c * (g : G)⁻¹)
        = (g : G) * (((g : G)⁻¹ * w * g) * c) * (g : G)⁻¹ := by group
      _ = (g : G) * (c * ((g : G)⁻¹ * w * g)) * (g : G)⁻¹ := by rw [hcw]
      _ = ((g : G) * c * (g : G)⁻¹) * w := by group
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  haveI hmapn : (C.map φ).Normal := Subgroup.Normal.map hCn φ hφ
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal (C.map φ)) with hbot | htop
  swap
  · exfalso
    obtain ⟨k, hk, w, hw, hne⟩ := hnt
    have hkC : (⟨k, hk⟩ : K) ∈ C := by
      have hmem : φ ⟨k, hk⟩ ∈ C.map φ := htop ▸ Subgroup.mem_top _
      obtain ⟨c, hc, hcφ⟩ := hmem
      have h1 : φ (c⁻¹ * ⟨k, hk⟩) = 1 := by rw [map_mul, map_inv, hcφ, inv_mul_cancel]
      have hC' : c⁻¹ * ⟨k, hk⟩ ∈ C := (hmemC _).2 (hkerC _ h1)
      have := C.mul_mem hc hC'
      simpa using this
    exact hne ((hmemC _).1 hkC w hw)
  ·
    have hCφ : ∀ c ∈ C, φ c = 1 := fun c hc => by
      have : φ c ∈ C.map φ := ⟨c, hc, rfl⟩
      rw [hbot] at this
      exact this
    have h5 : 5 ∣ Nat.card (alternatingGroup (Fin 5)) := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup]; decide
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' 5 h5
    obtain ⟨x₀, hx₀⟩ := hφ σ
    have hσ1 : σ ≠ 1 := fun h => by rw [h, orderOf_one] at hσ; omega
    have h5dvd : 5 ∣ orderOf x₀ := by
      have := orderOf_map_dvd φ x₀
      rw [hx₀, hσ] at this; exact this
    have hσ5 : σ ^ 5 = 1 := by
      have := pow_orderOf_eq_one σ
      rwa [hσ] at this
    have hx5 : φ (x₀ ^ 5) = 1 := by rw [map_pow, hx₀]; exact hσ5
    obtain ⟨a, ha⟩ := hker2 _ hx5
    have hord : orderOf x₀ = 5 * 2 ^ a := by
      have := orderOf_pow_of_dvd (x := x₀) (n := 5) (by norm_num) h5dvd
      rw [ha] at this
      omega
    set x₁ : K := x₀ ^ (2 ^ a) with hx₁
    have hord1 : orderOf x₁ = 5 := by
      rw [hx₁, orderOf_pow_of_dvd (by positivity) (by rw [hord]; exact Dvd.intro_left _ rfl), hord]
      exact Nat.mul_div_cancel 5 (by positivity)
    refine ⟨(x₁ : G), x₁.2, by rw [Subgroup.orderOf_coe]; exact hord1, ?_⟩
    by_contra hcon
    push Not at hcon
    have hxC : x₁ ∈ C := (hmemC _).2 fun w hw => by
      have h := hcon w hw
      calc w * (x₁ : G) = (x₁ : G) * w * (x₁ : G)⁻¹ * (x₁ : G) := by rw [h]
        _ = (x₁ : G) * w := by group
    have h1 := hCφ x₁ hxC
    rw [hx₁, map_pow, hx₀] at h1
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hσ] at this
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow (by norm_num) this
    omega

end CFSG.GH74.QTGen4.Leaves
