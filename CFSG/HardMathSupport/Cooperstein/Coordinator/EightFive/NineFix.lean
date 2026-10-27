module

public import CFSG.Quasithin.Background.FixVZPowers
public import CFSG.HardMathSupport.Cooperstein.Proving.OrderThreeFix
public import CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive.EightFixFree

public section

namespace CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive

open CFSG.Quasithin

variable {V : Type} [CommGroup V]

section Bridge

variable [Module (ZMod 2) (Additive V)]

theorem card_fixV_natAct (S : Subgroup (MulAut V)) :
    Nat.card ↥(H13.CTK.L5.fixV (K := ZMod 2) (Proving.natAct (V := V)) S) =
      Nat.card ↥(fixV S) :=
  Nat.card_congr (Equiv.subtypeEquiv Additive.toMul fun w =>
    Proving.mem_fixV_iff S (Additive.toMul w))

theorem fixV_natAct_eq_bot_iff (S : Subgroup (MulAut V)) :
    H13.CTK.L5.fixV (K := ZMod 2) (Proving.natAct (V := V)) S = ⊥ ↔ fixV S = ⊥ := by
  rw [Proving.fixV_eq_bot_iff, Subgroup.eq_bot_iff_forall]
  rfl

end Bridge

private abbrev zmodTwo (hV : ∀ v : V, v ^ 2 = 1) : Module (ZMod 2) (Additive V) :=
  AddCommGroup.zmodModule (n := 2) fun w => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hV _

theorem card_fixV_zpowers_conj (g y : MulAut V) :
    Nat.card (fixV (Subgroup.zpowers (g * y * g⁻¹))) = Nat.card (fixV (Subgroup.zpowers y)) :=
  CFSG.Quasithin.card_fixV_zpowers_conj g y

theorem fixV_zpowers_le {S : Subgroup (MulAut V)} {g : MulAut V} (hg : g ∈ S) :
    fixV S ≤ fixV (Subgroup.zpowers g) :=
  fun _ hv _ hx => hv _ (Subgroup.zpowers_le.2 hg hx)

theorem ne_one_of_fixV_eq_bot [Finite V] (hV1 : 1 < Nat.card V) {x : MulAut V}
    (hx : fixV (Subgroup.zpowers x) = ⊥) : x ≠ 1 := by
  rintro rfl
  have htop : fixV (Subgroup.zpowers (1 : MulAut V)) = ⊤ :=
    eq_top_iff.2 fun v _ => mem_fixV_zpowers_iff.2 rfl
  rw [hx] at htop
  have h1 := congrArg (fun S : Subgroup V => Nat.card S) htop
  simp only [Subgroup.card_bot, Subgroup.card_top] at h1
  omega

theorem eq_one_of_pow_three_of_pow_two {G : Type*} [Group G] {x : G} (h3 : x ^ 3 = 1)
    (h2 : x ^ 2 = 1) : x = 1 := by
  calc x = x ^ 3 * (x ^ 2)⁻¹ := by group
    _ = 1 := by rw [h3, h2, inv_one, one_mul]

theorem notMem_zpowers_of_conj {G : Type*} [Group G] {g x y : G} (hy3 : y ^ 3 = 1) (hy1 : y ≠ 1)
    (hgx : g * x * g⁻¹ = x) (hgy : g * y * g⁻¹ = y⁻¹) : y ∉ Subgroup.zpowers x := by
  intro hy
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
  apply hy1
  refine eq_one_of_pow_three_of_pow_two hy3 ?_
  have h1 : g * y * g⁻¹ = y := by rw [← hk, ← conj_zpow, hgx]
  rw [hgy] at h1
  rw [pow_two]
  nth_rewrite 1 [← h1]
  exact inv_mul_cancel y

theorem card_fixV_zpowers_sq_eq [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {t x : MulAut V}
    (ht : t ^ 2 = 1) (hx3 : x ^ 3 = 1) (hinv : t * x * t⁻¹ = x⁻¹)
    (hx : fixV (Subgroup.zpowers x) = ⊥) :
    Nat.card (fixV (Subgroup.zpowers t)) ^ 2 = Nat.card V := by
  let _ : Module (ZMod 2) (Additive V) := zmodTwo hV
  rw [← card_fixV_natAct]
  exact Proving.card_fixV_sq_eq_of_inverts hV t x ht hx3 hinv ((fixV_natAct_eq_bot_iff _).2 hx)

theorem card_eq_card_fixV_mul_card_fixV (hV : ∀ v : V, v ^ 2 = 1) {x y : MulAut V}
    (hx3 : x ^ 3 = 1) (hy3 : y ^ 3 = 1) (hxy : x * y = y * x) (hx1 : x ≠ 1)
    (hy : y ∉ Subgroup.zpowers x) (hyf : fixV (Subgroup.zpowers y) = ⊥) :
    Nat.card V = Nat.card (fixV (Subgroup.zpowers x)) *
      Nat.card (fixV (Subgroup.zpowers (x * y))) *
      Nat.card (fixV (Subgroup.zpowers (x * y ^ 2))) := by
  have hyS : y ∈ Subgroup.closure ({x, y} : Set (MulAut V)) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton y))
  have hE : fixV (Subgroup.closure ({x, y} : Set (MulAut V))) = ⊥ :=
    le_bot_iff.1 (hyf ▸ fixV_zpowers_le hyS)
  let _ : Module (ZMod 2) (Additive V) := zmodTwo hV
  have h := Proving.card_eq_mul_fixV_of_three_sq x y hx3 hy3 hxy hx1 hy
    ((fixV_natAct_eq_bot_iff _).2 hE)
  rw [card_fixV_natAct, card_fixV_natAct, card_fixV_natAct, card_fixV_natAct, hyf,
    Subgroup.card_bot, mul_one] at h
  exact h

theorem two_pow_eight_le_card_of_three [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {x₁ x₂ x₃ g g' : MulAut V} (h₁ : x₁ ^ 3 = 1) (h₂ : x₂ ^ 3 = 1) (h₃ : x₃ ^ 3 = 1)
    (c₁₂ : x₁ * x₂ = x₂ * x₁) (c₁₃ : x₁ * x₃ = x₃ * x₁) (c₂₃ : x₂ * x₃ = x₃ * x₂)
    (f₁ : fixV (Subgroup.zpowers x₁) = ⊥) (f₂ : fixV (Subgroup.zpowers x₂) = ⊥)
    (f₃ : fixV (Subgroup.zpowers x₃) = ⊥) (hx₁ : x₁ ≠ 1)
    (g₁ : g * x₁ * g⁻¹ = x₁) (g₂ : g * x₂ * g⁻¹ = x₂⁻¹)
    (g'₁ : g' * x₁ * g'⁻¹ = x₂) (g'₂ : g' * x₂ * g'⁻¹ = x₁) (g'₃ : g' * x₃ * g'⁻¹ = x₃⁻¹) :
    2 ^ 8 ≤ Nat.card V := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hV1 : 1 < Nat.card V := by
    by_contra hle
    have : Subsingleton V := (Finite.card_le_one_iff_subsingleton).1 (by omega)
    exact hx₁ (MulEquiv.ext fun v => Subsingleton.elim _ _)
  have hx₂1 : x₂ ≠ 1 := ne_one_of_fixV_eq_bot hV1 f₂
  have hx₃1 : x₃ ≠ 1 := ne_one_of_fixV_eq_bot hV1 f₃
  have hy₂ : x₂ ∉ Subgroup.zpowers x₁ := notMem_zpowers_of_conj h₂ hx₂1 g₁ g₂
  have hA := card_eq_card_fixV_mul_card_fixV hV h₁ h₂ c₁₂ hx₁ hy₂ f₂
  have hconj₁ : g * (x₁ * x₂) * g⁻¹ = x₁ * x₂ ^ 2 := by
    have hinv : x₂⁻¹ = x₂ ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', h₂]
    calc g * (x₁ * x₂) * g⁻¹ = (g * x₁ * g⁻¹) * (g * x₂ * g⁻¹) := by group
      _ = x₁ * x₂ ^ 2 := by rw [g₁, g₂, hinv]
  rw [f₁, Subgroup.card_bot, one_mul, ← hconj₁, card_fixV_zpowers_conj] at hA
  have hz3 : (x₁ * x₂) ^ 3 = 1 := by
    have hc : Commute x₁ x₂ := c₁₂
    rw [hc.mul_pow, h₁, h₂, one_mul]
  have hz1 : x₁ * x₂ ≠ 1 := by
    intro h
    apply hy₂
    rw [show x₂ = x₁⁻¹ from (eq_inv_of_mul_eq_one_right h)]
    exact Subgroup.inv_mem _ (Subgroup.mem_zpowers x₁)
  have hzc : x₁ * x₂ * x₃ = x₃ * (x₁ * x₂) := by
    rw [mul_assoc, c₂₃, ← mul_assoc, c₁₃, mul_assoc]
  have hg'z : g' * (x₁ * x₂) * g'⁻¹ = x₁ * x₂ := by
    calc g' * (x₁ * x₂) * g'⁻¹ = (g' * x₁ * g'⁻¹) * (g' * x₂ * g'⁻¹) := by group
      _ = x₁ * x₂ := by rw [g'₁, g'₂, c₁₂]
  have hy₃ : x₃ ∉ Subgroup.zpowers (x₁ * x₂) := notMem_zpowers_of_conj h₃ hx₃1 hg'z g'₃
  have hB := card_eq_card_fixV_mul_card_fixV hV hz3 h₃ hzc hz1 hy₃ f₃
  have hconj₂ : g' * (x₁ * x₂ * x₃) * g'⁻¹ = x₁ * x₂ * x₃ ^ 2 := by
    have hinv : x₃⁻¹ = x₃ ^ 2 := by
      rw [inv_eq_iff_mul_eq_one, ← pow_succ', h₃]
    calc g' * (x₁ * x₂ * x₃) * g'⁻¹ = (g' * (x₁ * x₂) * g'⁻¹) * (g' * x₃ * g'⁻¹) := by group
      _ = x₁ * x₂ * x₃ ^ 2 := by rw [hg'z, g'₃, hinv]
  rw [← hconj₂, card_fixV_zpowers_conj] at hB
  set a := Nat.card (fixV (Subgroup.zpowers (x₁ * x₂)))
  set c := Nat.card (fixV (Subgroup.zpowers (x₁ * x₂ * x₃)))
  have ha0 : 0 < a := Nat.card_pos
  have hac : a = c * c := by
    have h1 : a * a = a * (c * c) := by rw [← hA, hB]; ring
    exact Nat.eq_of_mul_eq_mul_left ha0 h1
  have hVc : Nat.card V = c ^ 4 := by rw [hA, hac]; ring
  have hP3 : IsPGroup 3 (Subgroup.zpowers x₁) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_prime h₁ hx₁, pow_one])
  have hst : Subgroup.zpowers x₁ ≤ stabSub (fixV (Subgroup.zpowers (x₁ * x₂ * x₃))) := by
    refine B1.le_stabSub_of_invariant fun k hk w hw => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
    rw [mem_fixV_zpowers_iff] at hw ⊢
    have hcomm : Commute (x₁ ^ j) (x₁ * x₂ * x₃) :=
      (((Commute.refl x₁).mul_right c₁₂).mul_right c₁₃).zpow_left j
    have h1 : (x₁ ^ j) ((x₁ * x₂ * x₃) w) = (x₁ * x₂ * x₃) ((x₁ ^ j) w) :=
      congrArg (fun φ : MulAut V => φ w) hcomm.eq
    rw [hw] at h1
    exact h1.symm
  have hmod := card_modEq_card_inf_fixV hP3 hst
  rw [f₁, inf_bot_eq, Subgroup.card_bot] at hmod
  have hdvd : c ∣ 2 ^ rk V := by
    rw [← card_eq_two_pow_rk hV]
    exact Subgroup.card_subgroup_dvd_card _
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have hev : Even i := Proving.two_pow_mod_three_even i (by rw [← hi]; exact hmod)
  obtain ⟨k, rfl⟩ := hev
  have hk : 1 ≤ k := by
    by_contra hk0
    rw [show k = 0 by omega] at hi
    rw [hVc, hi] at hV1
    norm_num at hV1
  rw [hVc, hi]
  calc 2 ^ 8 = (2 ^ (1 + 1)) ^ 4 := by norm_num
    _ ≤ (2 ^ (k + k)) ^ 4 := Nat.pow_le_pow_left (Nat.pow_le_pow_right (by norm_num) (by omega)) 4

theorem false_of_fixV_eq [Finite V] {B : Subgroup (MulAut V)} (hB16 : Nat.card B ≤ 16)
    (hV8 : 2 ^ 8 ≤ Nat.card V) (hoff : Nat.card V ≤ Nat.card B * Nat.card (fixV B))
    {t b x : MulAut V} (htB : t ∈ B) (hbB : b ∈ B)
    (hb : Nat.card (fixV (Subgroup.zpowers b)) ^ 2 = Nat.card V)
    (hx3 : x ^ 3 = 1) (hxf : fixV (Subgroup.zpowers x) = ⊥) (hinv : t * x * t⁻¹ = x⁻¹)
    (hxb : x * b = b * x) : False := by
  have hle : fixV B ≤ fixV (Subgroup.zpowers b) := fixV_zpowers_le hbB
  set c := Nat.card (fixV (Subgroup.zpowers b))
  have hc16 : 16 ≤ c := by
    by_contra h
    have h1 : c ^ 2 ≤ 15 ^ 2 := Nat.pow_le_pow_left (by omega) 2
    omega
  have hcle : c ≤ Nat.card (fixV B) := by
    have h1 : c * c ≤ c * Nat.card (fixV B) :=
      calc c * c = Nat.card V := by rw [← hb]; ring
        _ ≤ Nat.card B * Nat.card (fixV B) := hoff
        _ ≤ 16 * Nat.card (fixV B) := Nat.mul_le_mul_right _ hB16
        _ ≤ c * Nat.card (fixV B) := Nat.mul_le_mul_right _ hc16
    exact Nat.le_of_mul_le_mul_left h1 (by omega)
  have heq : fixV B = fixV (Subgroup.zpowers b) := Subgroup.eq_of_le_of_card_ge hle hcle
  have hbot : fixV B = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have hby : b y = y := mem_fixV_zpowers_iff.1 (hle hy)
    have hxy : x y ∈ fixV B := by
      rw [heq, mem_fixV_zpowers_iff]
      have h1 := congrArg (fun φ : MulAut V => φ y) hxb
      simp only [MulAut.mul_apply] at h1
      rw [← h1, hby]
    have hty : t y = y := hy t htB
    have htxy : t (x y) = x y := hxy t htB
    have htx : t * x = x⁻¹ * t := by
      calc t * x = t * x * t⁻¹ * t := by group
        _ = x⁻¹ * t := by rw [hinv]
    have h2 : x⁻¹ y = x y := by
      have h1 := congrArg (fun φ : MulAut V => φ y) htx
      simp only [MulAut.mul_apply] at h1
      rw [hty] at h1
      rw [← h1, htxy]
    have h5 : y = x (x y) := by
      have h1 := congrArg x h2
      rwa [MulAut.apply_inv_self] at h1
    have h3 : x y = y := by
      have h6 : x (x (x y)) = y := by
        have h1 := congrArg (fun φ : MulAut V => φ y) hx3
        simpa [pow_succ, MulAut.mul_apply] using h1
      calc x y = x (x (x y)) := by rw [← h5]
        _ = y := h6
    have : y ∈ fixV (Subgroup.zpowers x) := mem_fixV_zpowers_iff.2 h3
    rw [hxf] at this
    exact this
  rw [hbot, Subgroup.card_bot, mul_one] at hoff
  omega

end CFSG.HardMathSupport.Cooperstein.Coordinator.EightFive
