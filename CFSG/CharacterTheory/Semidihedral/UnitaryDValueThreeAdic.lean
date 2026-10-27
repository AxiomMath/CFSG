module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.CharacterTheory.Semidihedral.UnitaryDValueLine
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.Semidihedral.UnitaryDValue

section General

variable {G : Type*} [Group G]

theorem zpow_mul_zpow_eq_one_iff_of_disjoint {a b : G}
    (hdisj : ∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1) (i j : ℤ) :
    a ^ i * b ^ j = 1 ↔ (orderOf a : ℤ) ∣ i ∧ (orderOf b : ℤ) ∣ j := by
  constructor
  · intro h
    have h1 : a ^ i = b ^ (-j) := by
      rw [zpow_neg]
      exact eq_inv_of_mul_eq_one_left h
    have hai : a ^ i = 1 := hdisj i (-j) h1
    have hbj : b ^ j = 1 := by rw [hai, one_mul] at h; exact h
    exact ⟨orderOf_dvd_iff_zpow_eq_one.mpr hai, orderOf_dvd_iff_zpow_eq_one.mpr hbj⟩
  · rintro ⟨hi, hj⟩
    rw [orderOf_dvd_iff_zpow_eq_one.mp hi, orderOf_dvd_iff_zpow_eq_one.mp hj, one_mul]

theorem zpow_mul_zpow_eq_iff {a b : G} (hab : Commute a b)
    (hdisj : ∀ i j : ℤ, a ^ i = b ^ j → a ^ i = 1) (i j i' j' : ℤ) :
    a ^ i * b ^ j = a ^ i' * b ^ j' ↔
      (orderOf a : ℤ) ∣ i - i' ∧ (orderOf b : ℤ) ∣ j - j' := by
  rw [← zpow_mul_zpow_eq_one_iff_of_disjoint hdisj]
  constructor
  · intro h
    calc a ^ (i - i') * b ^ (j - j') = a ^ i * b ^ j * (a ^ (-i') * b ^ (-j')) := by
          rw [zpow_mul_zpow_mul_zpow_mul_zpow hab, sub_eq_add_neg, sub_eq_add_neg]
      _ = a ^ i' * b ^ j' * (a ^ (-i') * b ^ (-j')) := by rw [h]
      _ = 1 := by
          rw [zpow_mul_zpow_mul_zpow_mul_zpow hab, add_neg_cancel, add_neg_cancel, zpow_zero,
            zpow_zero, mul_one]
  · intro h
    calc a ^ i * b ^ j = a ^ (i - i') * b ^ (j - j') * (a ^ i' * b ^ j') := by
          rw [zpow_mul_zpow_mul_zpow_mul_zpow hab, sub_add_cancel, sub_add_cancel]
      _ = a ^ i' * b ^ j' := by rw [h, one_mul]

theorem exists_hom_units_apply_ne_one_of_comm {T : Type*} [Group T] [Finite T]
    (hcomm : ∀ a b : T, a * b = b * a) {g : T} (hg : g ≠ 1) : ∃ θ : T →* ℂˣ, θ g ≠ 1 := by
  let _ : CommGroup T := { (inferInstance : Group T) with mul_comm := hcomm }
  obtain ⟨ψ, hψ⟩ := (AddChar.exists_apply_ne_zero (α := Additive T)
    (a := Additive.ofMul g)).mpr (by simpa using hg)
  refine ⟨(ψ.toMonoidHom).toHomUnits, ?_⟩
  intro h
  apply hψ
  have h1 := congrArg Units.val h
  exact h1

theorem eq_one_of_pow_eq_one_of_pow_three {M : Type*} [Monoid M] {a : M} {m v : ℕ}
    (hm : a ^ m = 1) (hv : a ^ (3 ^ v) = 1) (hm3 : ¬ 3 ∣ m) : a = 1 := by
  have hcop : Nat.Coprime m (3 ^ v) :=
    Nat.Coprime.pow_right v ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm3).symm
  have h1 : a ^ Nat.gcd m (3 ^ v) = 1 := pow_gcd_eq_one.mpr ⟨hm, hv⟩
  rwa [hcop.gcd_eq_one, pow_one] at h1

end General

section Arith

theorem three_dvd_sub_one_of_dvd {d : ℤ} (h : (3 : ℤ) ∣ 2 * d ^ 2 - d - 1) : (3 : ℤ) ∣ d - 1 := by
  have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast h)
  have goal : ((d - 1 : ℤ) : ZMod 3) = 0 := by
    push_cast at h' ⊢
    generalize (d : ZMod 3) = x at h' ⊢
    revert x
    decide
  exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mp goal

theorem three_dvd_of_pow_dvd {n : ℕ} (hn : 1 ≤ n) {x : ℤ} (h : (3 : ℤ) ^ n ∣ x) : (3 : ℤ) ∣ x :=
  (dvd_pow_self 3 (by omega)).trans h

theorem three_adic_cases {h k : ℕ} (hk1 : 1 ≤ k) (hkh : k ≤ h) {α β γ₀ δ : ℤ}
    (E1 : (3 : ℤ) ^ h ∣ 2 * α ^ 2 - α - 1) (E2 : (3 : ℤ) ^ k ∣ 2 * δ ^ 2 - δ - 1)
    (E5 : (3 : ℤ) ^ h ∣ α - α ^ 2 - β * (3 ^ (h - k) * γ₀))
    (F1 : ¬ (3 : ℤ) ∣ γ₀) (F2 : (3 : ℤ) ∣ δ - 1 → ¬ (3 : ℤ) ∣ β) :
    h = k + 1 ∨ (k = 1 ∧ 3 ≤ h ∧ ∃ s₀ : ℤ, ¬ (3 : ℤ) ∣ s₀ ∧ α = 1 + 3 ^ (h - 1) * s₀ ∧
      (3 : ℤ) ∣ β * γ₀ + s₀) := by
  have hp := Int.prime_three
  have hδ := three_dvd_sub_one_of_dvd (three_dvd_of_pow_dvd hk1 E2)
  have hα := three_dvd_sub_one_of_dvd (three_dvd_of_pow_dvd (hk1.trans hkh) E1)
  have hβ := F2 hδ
  have hβγ : ¬ (3 : ℤ) ∣ β * γ₀ := fun h' => (hp.dvd_or_dvd h').elim hβ F1
  by_cases hh1 : h = k + 1
  · exact Or.inl hh1
  right
  obtain ⟨s, hs⟩ := hα
  have hαs : α = 1 + 3 * s := by linarith
  have hhk : k + 2 ≤ h := by
    rcases (show h = k ∨ k + 2 ≤ h by omega) with h' | h'
    · exfalso
      subst h'
      rw [Nat.sub_self, pow_zero, one_mul] at E5
      apply hβγ
      have h3 := three_dvd_of_pow_dvd (hk1.trans hkh) E5
      have e : α - α ^ 2 - β * γ₀ = -(3 * (s * (1 + 3 * s))) - β * γ₀ := by rw [hαs]; ring
      rw [e] at h3
      have h4 : (3 : ℤ) ∣ -(3 * (s * (1 + 3 * s))) := ⟨-(s * (1 + 3 * s)), by ring⟩
      have h5 := dvd_sub h4 h3
      rw [show -(3 * (s * (1 + 3 * s))) - (-(3 * (s * (1 + 3 * s))) - β * γ₀) = β * γ₀ by ring]
        at h5
      exact h5
    · exact h'
  have hE1 : (3 : ℤ) ^ (h - 2) ∣ s * (1 + 2 * s) := by
    have e : 2 * α ^ 2 - α - 1 = 9 * (s * (1 + 2 * s)) := by rw [hαs]; ring
    rw [e, show h = (h - 2) + 2 by omega, pow_add, mul_comm] at E1
    exact (mul_dvd_mul_iff_left (by norm_num)).mp E1
  by_cases hs3 : (3 : ℤ) ∣ s
  ·
    have hcop : IsCoprime ((3 : ℤ) ^ (h - 2)) (1 + 2 * s) := by
      refine (hp.coprime_iff_not_dvd.mpr ?_).pow_left
      intro h'
      have h2 := dvd_sub h' (dvd_mul_of_dvd_right hs3 2)
      rw [show 1 + 2 * s - 2 * s = 1 by ring] at h2
      exact absurd (Int.eq_one_of_dvd_one (by norm_num) h2) (by norm_num)
    obtain ⟨s₀, hs₀⟩ := hcop.dvd_of_dvd_mul_right hE1
    have hα' : α = 1 + 3 ^ (h - 1) * s₀ := by
      rw [hαs, hs₀, show h - 1 = (h - 2) + 1 by omega, pow_succ]
      ring
    have hsq : (3 : ℤ) ^ h ∣ (3 ^ (h - 1) * s₀) ^ 2 := by
      rw [mul_pow, ← pow_mul]
      exact dvd_mul_of_dvd_left (pow_dvd_pow 3 (by omega)) _
    have e : α - α ^ 2 - β * (3 ^ (h - k) * γ₀) =
        -(3 ^ (h - 1) * s₀) - (3 ^ (h - 1) * s₀) ^ 2 - 3 ^ (h - k) * (β * γ₀) := by
      rw [hα']; ring
    rw [e] at E5
    have E6 : (3 : ℤ) ^ h ∣ 3 ^ (h - 1) * s₀ + 3 ^ (h - k) * (β * γ₀) := by
      have := dvd_add E5 hsq
      rw [show -(3 ^ (h - 1) * s₀) - (3 ^ (h - 1) * s₀) ^ 2 - 3 ^ (h - k) * (β * γ₀) +
        (3 ^ (h - 1) * s₀) ^ 2 = -(3 ^ (h - 1) * s₀ + 3 ^ (h - k) * (β * γ₀)) by ring] at this
      exact (dvd_neg).mp this
    rcases (show k = 1 ∨ 2 ≤ k by omega) with hk | hk
    · subst hk
      refine ⟨rfl, by omega, s₀, ?_, hα', ?_⟩
      · intro hs₀3
        apply hβγ
        rw [show h = (h - 1) + 1 by omega, pow_succ, ← mul_add] at E6
        have h7 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp E6
        have h8 := dvd_sub h7 hs₀3
        rwa [show s₀ + β * γ₀ - s₀ = β * γ₀ by ring] at h8
      · rw [show h = (h - 1) + 1 by omega, pow_succ, ← mul_add] at E6
        have h7 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp E6
        rwa [add_comm] at h7
    · exfalso
      apply hβγ
      have e2 : (3 : ℤ) ^ (h - 1) * s₀ + 3 ^ (h - k) * (β * γ₀) =
          3 ^ (h - k) * (3 ^ (k - 1) * s₀ + β * γ₀) := by
        rw [show (3 : ℤ) ^ (h - 1) = 3 ^ (h - k) * 3 ^ (k - 1) by
          rw [← pow_add]; congr 1; omega]
        ring
      have E7 : (3 : ℤ) ^ (h - k) * 3 ^ k ∣ 3 ^ (h - k) * (3 ^ (k - 1) * s₀ + β * γ₀) := by
        rw [← pow_add, Nat.sub_add_cancel hkh, ← e2]
        exact E6
      have h7 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp E7
      have h8 := three_dvd_of_pow_dvd hk1 h7
      have h9 : (3 : ℤ) ∣ 3 ^ (k - 1) * s₀ := dvd_mul_of_dvd_left (dvd_pow_self 3 (by omega)) _
      have h10 := dvd_sub h8 h9
      rwa [show 3 ^ (k - 1) * s₀ + β * γ₀ - 3 ^ (k - 1) * s₀ = β * γ₀ by ring] at h10
  ·
    exfalso
    have hcop : IsCoprime ((3 : ℤ) ^ (h - 2)) s := (hp.coprime_iff_not_dvd.mpr hs3).pow_left
    have h1 := hcop.dvd_of_dvd_mul_left hE1
    have h2 : (3 : ℤ) ∣ 1 + 2 * s := three_dvd_of_pow_dvd (by omega) h1
    have h9 : (9 : ℤ) ∣ α - α ^ 2 := by
      have h3 : (9 : ℤ) ∣ α - α ^ 2 - β * (3 ^ (h - k) * γ₀) :=
        (show (9 : ℤ) = 3 ^ 2 by norm_num) ▸ (pow_dvd_pow 3 (by omega)).trans E5
      have h4 : (9 : ℤ) ∣ β * (3 ^ (h - k) * γ₀) := by
        refine dvd_mul_of_dvd_right (dvd_mul_of_dvd_left ?_ _) _
        exact (show (9 : ℤ) = 3 ^ 2 by norm_num) ▸ pow_dvd_pow 3 (by omega)
      have := dvd_add h3 h4
      rwa [sub_add_cancel] at this
    have e : α - α ^ 2 = 3 * (-(s * (1 + 3 * s))) := by rw [hαs]; ring
    rw [e, show (9 : ℤ) = 3 * 3 by norm_num] at h9
    have h10 := (mul_dvd_mul_iff_left (by norm_num)).mp h9
    rw [dvd_neg] at h10
    rcases hp.dvd_or_dvd h10 with h11 | h11
    · exact hs3 h11
    · have h12 := dvd_sub h11 (dvd_mul_right 3 s)
      rw [show 1 + 3 * s - 3 * s = 1 by ring] at h12
      exact absurd (Int.eq_one_of_dvd_one (by norm_num) h12) (by norm_num)

end Arith

namespace DValueData

variable {G : Type} [Group G] [Fintype G] (D : DValueData G)

theorem false_of_invariant_line (hext : D.CharacterExtend) (htriv : D.CharacterTrivial)
    {u₀ u₁ : G} (hu₀ : D.PW 3 = Subgroup.zpowers u₀) (hu₁ : D.PA 3 = Subgroup.zpowers u₁)
    (hk : 1 ≤ (Nat.card D.A).factorization 3) {α β γ δ : ℤ}
    (htu₀ : D.t * u₀ * D.t⁻¹ = u₀ ^ α * u₁ ^ β) (htu₁ : D.t * u₁ * D.t⁻¹ = u₀ ^ γ * u₁ ^ δ)
    (hβ : (3 : ℤ) ∣ β) (hδ : (3 : ℤ) ∣ δ - 1) : False := by
  set k := (Nat.card D.A).factorization 3 with hkdef
  have hu₁o : orderOf u₁ = 3 ^ k := by rw [← Nat.card_zpowers, ← hu₁, D.card_PA]
  have hu₀P : u₀ ∈ D.PW 3 := hu₀ ▸ Subgroup.mem_zpowers u₀
  have hu₁P : u₁ ∈ D.PA 3 := hu₁ ▸ Subgroup.mem_zpowers u₁
  have hu₀W : u₀ ∈ D.W := D.PW_le_W hu₀P
  have hu₁A : u₁ ∈ D.A := D.PA_le_A hu₁P
  have hustarA : u₁ ^ (3 ^ (k - 1)) ∈ D.A := D.A.pow_mem hu₁A _
  have hustar1 : u₁ ^ (3 ^ (k - 1)) ≠ 1 := by
    intro h1
    have h2 := orderOf_dvd_of_pow_eq_one h1
    rw [hu₁o] at h2
    have h3 := Nat.le_of_dvd (by positivity) h2
    have h4 : 3 ^ (k - 1) < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨θ₁, hθ₁⟩ := exists_hom_units_apply_ne_one_of_comm (T := D.A)
    (fun a b => Subtype.ext (D.A_comm a a.2 b b.2)) (g := ⟨u₁ ^ (3 ^ (k - 1)), hustarA⟩)
    (fun h => hustar1 (congrArg Subtype.val h))
  set θ₀ : D.A →* ℂˣ := (powMonoidHom (3 ^ (k - 1))).comp θ₁ with hθ₀def
  have hθ₀u₁ : θ₀ ⟨u₁, hu₁A⟩ = θ₁ ⟨u₁ ^ (3 ^ (k - 1)), hustarA⟩ := by
    show θ₁ ⟨u₁, hu₁A⟩ ^ (3 ^ (k - 1)) = _
    rw [← map_pow]
    rfl
  have hθ₀u₁3 : θ₀ ⟨u₁, hu₁A⟩ ^ 3 = 1 := by
    show (θ₁ ⟨u₁, hu₁A⟩ ^ (3 ^ (k - 1))) ^ 3 = 1
    rw [← pow_mul, ← map_pow]
    have h1 : (⟨u₁, hu₁A⟩ : D.A) ^ (3 ^ (k - 1) * 3) = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one, ← pow_succ, Nat.sub_add_cancel hk, ← hu₁o,
        pow_orderOf_eq_one]
    rw [h1, map_one]
  obtain ⟨θ₂, hθ₂S, hθ₂A⟩ := hext θ₀
  set n := Nat.card D.N with hn
  set v := n.factorization 3 with hv
  set n' := n / 3 ^ v with hn'
  have hn'3 : ¬ 3 ∣ n' := Nat.not_dvd_ordCompl Nat.prime_three Nat.card_pos.ne'
  set θ : D.N →* ℂˣ := (powMonoidHom (n' ^ 2)).comp θ₂ with hθdef
  have hθapp : ∀ c : D.N, θ c = θ₂ c ^ (n' ^ 2) := fun c => rfl
  have hθpow : ∀ c : D.N, θ c ^ (3 ^ v) = 1 := by
    intro c
    rw [hθapp, ← pow_mul, ← map_pow]
    have hsplit : 3 ^ v * n' = n := Nat.ordProj_mul_ordCompl_eq_self n 3
    have h1 : c ^ (n' ^ 2 * 3 ^ v) = 1 := by
      rw [show n' ^ 2 * 3 ^ v = n' * (3 ^ v * n') by ring, hsplit, pow_mul', hn,
        pow_card_eq_one', one_pow]
    rw [h1, map_one]
  have hθS : ∀ c : D.N, (c : G) ∈ (D.S : Subgroup G) → θ c = 1 := by
    intro c hc
    rw [hθapp, hθ₂S c hc, one_pow]
  have hθu₁ : θ ⟨u₁, D.A_le_C hu₁A |> D.C_le_N⟩ ≠ 1 := by
    rw [hθapp, hθ₂A _ hu₁A]
    have he : n' ^ 2 % 3 = 1 := sq_mod_three_of_not_dvd hn'3
    have h1 : θ₀ ⟨u₁, hu₁A⟩ ^ (n' ^ 2) = θ₀ ⟨u₁, hu₁A⟩ := by
      rw [← Nat.div_add_mod (n' ^ 2) 3, he, pow_add, pow_mul, hθ₀u₁3, one_pow, one_mul,
        pow_one]
    rw [h1, hθ₀u₁]
    exact hθ₁
  classical
  obtain ⟨f, hf⟩ : ∃ f : G → ℂˣ, ∀ g (hg : g ∈ D.N), f g = θ ⟨g, hg⟩ :=
    ⟨fun g => if hg : g ∈ D.N then θ ⟨g, hg⟩ else 1, fun g hg => by simp only [hg, dite_true]⟩
  have hfmul : ∀ a ∈ D.N, ∀ b ∈ D.N, f (a * b) = f a * f b := by
    intro a ha b hb
    rw [hf (a * b) (D.N.mul_mem ha hb), hf a ha, hf b hb, ← map_mul]
    rfl
  have hfinv : ∀ a ∈ D.N, f a⁻¹ = (f a)⁻¹ := by
    intro a ha
    rw [hf a⁻¹ (D.N.inv_mem ha), hf a ha, ← map_inv]
    rfl
  have hfzpow : ∀ a ∈ D.N, ∀ i : ℤ, f (a ^ i) = f a ^ i := by
    intro a ha i
    rw [hf (a ^ i) (D.N.zpow_mem ha i), hf a ha, ← map_zpow]
    rfl
  have hfpow : ∀ a ∈ D.N, ∀ i : ℕ, f (a ^ i) = f a ^ i := by
    intro a ha i
    rw [hf (a ^ i) (D.N.pow_mem ha i), hf a ha, ← map_pow]
    rfl
  have hf3 : ∀ a ∈ D.N, f a ^ (3 ^ v) = 1 := fun a ha => by rw [hf a ha]; exact hθpow _
  have hfW : ∀ w ∈ D.W, f w = 1 := by
    intro w hw
    have hwN : w ∈ D.N := D.C_le_N (D.W_le hw)
    have h1 : f (D.y * w * D.y⁻¹) = f w := by
      rw [hfmul _ (D.N.mul_mem D.y_mem_N hwN) _ (D.N.inv_mem D.y_mem_N),
        hfmul _ D.y_mem_N _ hwN, hfinv _ D.y_mem_N, mul_comm (f D.y), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [D.y_W w hw, hfinv _ hwN] at h1
    have h2 : f w ^ 2 = 1 := by
      rw [pow_two]
      nth_rw 1 [← h1]
      exact inv_mul_cancel _
    exact eq_one_of_pow_eq_one_of_pow_three h2 (hf3 w hwN) (by norm_num)
  have hu₁N : u₁ ∈ D.N := D.C_le_N (D.A_le_C hu₁A)
  have hu₀N : u₀ ∈ D.N := D.C_le_N (D.W_le hu₀W)
  have hfu₁3 : f u₁ ^ 3 = 1 := by
    rw [hf u₁ hu₁N, hθapp, hθ₂A _ hu₁A, ← pow_mul, mul_comm, pow_mul, hθ₀u₁3, one_pow]
  have hfu₁z : ∀ i j : ℤ, (3 : ℤ) ∣ i - j → f u₁ ^ i = f u₁ ^ j := by
    intro i j hij
    obtain ⟨c, hc⟩ := hij
    have h3 : f u₁ ^ ((3 : ℤ) * c) = 1 := by
      rw [zpow_mul, show ((3 : ℤ)) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hfu₁3, one_zpow]
    rw [show i = j + 3 * c by linarith, zpow_add, h3, mul_one]
  have hfP : ∀ i j : ℤ, f (u₀ ^ i * u₁ ^ j) = f u₁ ^ j := by
    intro i j
    rw [hfmul _ (D.N.zpow_mem hu₀N i) _ (D.N.zpow_mem hu₁N j), hfzpow _ hu₀N,
      hfzpow _ hu₁N, hfW u₀ hu₀W, one_zpow, one_mul]
  have hPC : ∀ u ∈ D.primaryPart 3, u ∈ D.C := fun u hu => D.primaryPart_le_C 3 hu
  have hab : Commute u₀ u₁ :=
    D.C_comm u₀ (D.W_le hu₀W) u₁ (D.A_le_C hu₁A)
  have htP : ∀ u ∈ D.primaryPart 3, f (D.t * u * D.t⁻¹) = f u := by
    intro u hu
    obtain ⟨w, hw, a, ha, rfl⟩ := D.exists_mul_eq (by norm_num) hu
    rw [hu₀] at hw
    rw [hu₁] at ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    rw [conj_zpow_mul_zpow hab htu₀ htu₁, hfP, hfP]
    apply hfu₁z
    obtain ⟨b, hb⟩ := hβ
    obtain ⟨d, hd⟩ := hδ
    exact ⟨b * i + d * j, by rw [hb, show δ = 3 * d + 1 by linarith]; ring⟩
  have htC : ∀ u ∈ D.C, f (D.t * u * D.t⁻¹) = f u := by
    intro u hu
    have huN : u ∈ D.N := D.C_le_N hu
    have htuC : D.t * u * D.t⁻¹ ∈ D.C := D.conj_mem_C D.t_mem_normalizer_T hu
    have htuN : D.t * u * D.t⁻¹ ∈ D.N := D.C_le_N htuC
    set m := orderOf u / 3 ^ (orderOf u).factorization 3 with hm
    have hm3 : ¬ 3 ∣ m := Nat.not_dvd_ordCompl Nat.prime_three (orderOf_pos u).ne'
    have humP : u ^ m ∈ D.primaryPart 3 :=
      ⟨D.C.pow_mem hu m, _, orderOf_pow_orderOf_div (orderOf_pos u).ne' (Nat.ordProj_dvd _ _)⟩
    have h1 := htP _ humP
    rw [← conj_pow, hfpow _ htuN, hfpow _ huN] at h1
    have h2 : (f (D.t * u * D.t⁻¹) * (f u)⁻¹) ^ m = 1 := by
      rw [mul_pow, inv_pow, h1, mul_inv_cancel]
    have h3 : (f (D.t * u * D.t⁻¹) * (f u)⁻¹) ^ (3 ^ v) = 1 := by
      rw [mul_pow, inv_pow, hf3 _ htuN, hf3 _ huN, inv_one, one_mul]
    have h4 := eq_one_of_pow_eq_one_of_pow_three h2 h3 hm3
    exact mul_inv_eq_one.mp h4
  have htpow : ∀ i : ℕ, ∀ u ∈ D.C, f (D.t ^ i * u * (D.t ^ i)⁻¹) = f u := by
    intro i
    induction i with
    | zero => intro u _; simp
    | succ i ih =>
      intro u hu
      rw [pow_succ', conj_mul_eq, htC _ (D.conj_mem_C (pow_mem D.t_mem_normalizer_T i) hu),
        ih u hu]
  have hyC : ∀ u ∈ D.C, f (D.y * u * D.y⁻¹) = f u := by
    intro u hu
    have huN : u ∈ D.N := D.C_le_N hu
    rw [hfmul _ (D.N.mul_mem D.y_mem_N huN) _ (D.N.inv_mem D.y_mem_N),
      hfmul _ D.y_mem_N _ huN, hfinv _ D.y_mem_N, mul_comm (f D.y), mul_assoc,
      mul_inv_cancel, mul_one]
  have hypow : ∀ j : ℕ, ∀ u ∈ D.C, f (D.y ^ j * u * (D.y ^ j)⁻¹) = f u := by
    intro j
    induction j with
    | zero => intro u _; simp
    | succ j ih =>
      intro u hu
      rw [pow_succ', conj_mul_eq, hyC _ (D.conj_mem_C (pow_mem D.y_mem_normalizer_T j) hu),
        ih u hu]
  have hinv : ∀ g ∈ Subgroup.normalizer (D.T : Set G), ∀ u ∈ D.C,
      f (g * u * g⁻¹) = f u := by
    intro g hg u hu
    obtain ⟨i, j, -, -, hc⟩ := D.normalizer_T_cases hg
    have hg' : g = D.t ^ i * (D.y ^ j * ((D.t ^ i * D.y ^ j)⁻¹ * g)) := by group
    rw [hg', conj_mul_eq, conj_mul_eq, D.C_conj hc hu,
      htpow i _ (D.conj_mem_C (pow_mem D.y_mem_normalizer_T j) hu), hypow j u hu]
  apply hθu₁
  refine htriv θ hθS ?_ _
  intro g hg c c' hc hcc'
  rw [D.centralizer_T] at hc
  rw [← hf _ c'.2, ← hf _ c.2, hcc']
  exact hinv g hg c hc

theorem three_adic (hext : D.CharacterExtend) (htriv : D.CharacterTrivial)
    (h3A : 3 ∣ Nat.card D.A) :
    (D.q + 1).factorization 3 = (Nat.card D.A).factorization 3 + 1 ∨
      ((Nat.card D.A).factorization 3 = 1 ∧ 3 ≤ (D.q + 1).factorization 3 ∧
        ∃ u₀ u₁ : G, ∃ s₀ : ℤ, D.PW 3 = Subgroup.zpowers u₀ ∧
          orderOf u₀ = 3 ^ (D.q + 1).factorization 3 ∧ D.PA 3 = Subgroup.zpowers u₁ ∧
          orderOf u₁ = 3 ∧ ¬ (3 : ℤ) ∣ s₀ ∧
          D.t * u₀ * D.t⁻¹ = u₀ ^ (1 + 3 ^ ((D.q + 1).factorization 3 - 1) * s₀) * u₁ ∧
          D.t * u₁ * D.t⁻¹ = u₀ ^ (-(3 ^ ((D.q + 1).factorization 3 - 1) * s₀)) * u₁) := by
  set h := (D.q + 1).factorization 3 with hhdef
  set k := (Nat.card D.A).factorization 3 with hkdef
  have hk1 : 1 ≤ k := (Nat.prime_three.dvd_iff_one_le_factorization D.card_A_pos.ne').mp h3A
  have hkh : k ≤ h :=
    (Nat.factorization_le_iff_dvd D.card_A_pos.ne' (by omega)).mpr D.card_A_dvd 3
  obtain ⟨u₀, hu₀, hu₀o⟩ := D.exists_generator_PW (r := 3) (by norm_num)
  obtain ⟨u₁, hu₁, hu₁o⟩ := D.exists_generator_PA (r := 3)
  rw [← hhdef] at hu₀o
  rw [← hkdef] at hu₁o
  have hu₀P : u₀ ∈ D.PW 3 := hu₀ ▸ Subgroup.mem_zpowers u₀
  have hu₁P : u₁ ∈ D.PA 3 := hu₁ ▸ Subgroup.mem_zpowers u₁
  have hu₀W : u₀ ∈ D.W := D.PW_le_W hu₀P
  have hu₁A : u₁ ∈ D.A := D.PA_le_A hu₁P
  have hu₀C : u₀ ∈ D.C := D.W_le hu₀W
  have hu₁C : u₁ ∈ D.C := D.A_le_C hu₁A
  have hab : Commute u₀ u₁ := D.C_comm u₀ hu₀C u₁ hu₁C
  have hdisj : ∀ i j : ℤ, u₀ ^ i = u₁ ^ j → u₀ ^ i = 1 := by
    intro i j hij
    have h1 : u₀ ^ i ∈ D.PW 3 ⊓ D.PA 3 :=
      ⟨(D.PW 3).zpow_mem hu₀P i, hij ▸ (D.PA 3).zpow_mem hu₁P j⟩
    rw [D.disjoint_PW_PA.eq_bot] at h1
    exact h1
  have hcoord := zpow_mul_zpow_eq_iff hab hdisj
  have hcoord1 := zpow_mul_zpow_eq_one_iff_of_disjoint hdisj
  rw [hu₀o, hu₁o] at hcoord hcoord1
  push_cast at hcoord hcoord1
  have hPcoord : ∀ u ∈ D.primaryPart 3, ∃ i j : ℤ, u = u₀ ^ i * u₁ ^ j := by
    intro u hu
    obtain ⟨w, hw, a, ha, rfl⟩ := D.exists_mul_eq (by norm_num) hu
    rw [hu₀] at hw
    rw [hu₁] at ha
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact ⟨i, j, rfl⟩
  have hu₀P3 : u₀ ∈ D.primaryPart 3 := D.PW_le hu₀P
  have hu₁P3 : u₁ ∈ D.primaryPart 3 := D.PA_le hu₁P
  obtain ⟨α, β, hTa⟩ := hPcoord _ (D.t_conj_primaryPart hu₀P3)
  obtain ⟨γ, δ, hTb⟩ := hPcoord _ (D.t_conj_primaryPart hu₁P3)
  have hYa : D.y * u₀ * D.y⁻¹ = u₀ ^ (-1 : ℤ) * u₁ ^ (0 : ℤ) := by
    rw [D.y_W u₀ hu₀W, zpow_zero, mul_one, zpow_neg_one]
  have hYb : D.y * u₁ * D.y⁻¹ = u₀ ^ (0 : ℤ) * u₁ ^ (1 : ℤ) := by
    rw [D.y_conj_A hu₁A, zpow_zero, one_mul, zpow_one]
  have hYia : D.y⁻¹ * u₀ * D.y⁻¹⁻¹ = u₀ ^ (-1 : ℤ) * u₁ ^ (0 : ℤ) := by
    rw [inv_inv, D.y_inv_conj_W hu₀W, zpow_zero, mul_one, zpow_neg_one]
  have hYib : D.y⁻¹ * u₁ * D.y⁻¹⁻¹ = u₀ ^ (0 : ℤ) * u₁ ^ (1 : ℤ) := by
    rw [conj_eq_of_comm (D.A_central u₁ hu₁A _ (D.N.inv_mem D.y_mem_N)), zpow_zero, one_mul,
      zpow_one]
  have hA1 : u₀ = u₀ ^ (1 : ℤ) * u₁ ^ (0 : ℤ) := by rw [zpow_one, zpow_zero, mul_one]
  have hB1 : u₁ = u₀ ^ (0 : ℤ) * u₁ ^ (1 : ℤ) := by rw [zpow_zero, zpow_one, one_mul]
  have he : D.y * D.t * D.y⁻¹ * D.t = D.y * (D.t * (D.y⁻¹ * D.t)) := by group
  have hea := D.C_conj D.y_t_y_inv_t_mem_C hu₀C
  have heb := D.C_conj D.y_t_y_inv_t_mem_C hu₁C
  rw [he, conj_mul_eq, conj_mul_eq, conj_mul_eq, hTa, conj_zpow_mul_zpow hab hYia hYib,
    conj_zpow_mul_zpow hab hTa hTb, conj_zpow_mul_zpow hab hYa hYb] at hea
  rw [he, conj_mul_eq, conj_mul_eq, conj_mul_eq, hTb, conj_zpow_mul_zpow hab hYia hYib,
    conj_zpow_mul_zpow hab hTa hTb, conj_zpow_mul_zpow hab hYa hYb] at heb
  have hR2 : ∀ u ∈ D.C, (D.y * D.t * D.y⁻¹) * u * (D.y * D.t * D.y⁻¹)⁻¹ =
      D.t * (D.t * u * D.t⁻¹) * D.t⁻¹ := by
    intro u hu
    have hu' : D.t⁻¹ * u * D.t⁻¹⁻¹ ∈ D.C := D.conj_mem_C (inv_mem D.t_mem_normalizer_T) hu
    have h2 := D.C_conj D.y_t_y_inv_t_mem_C hu'
    have h3 := D.C_conj D.t_cube_mem_C hu'
    calc (D.y * D.t * D.y⁻¹) * u * (D.y * D.t * D.y⁻¹)⁻¹
        = (D.y * D.t * D.y⁻¹ * D.t) * (D.t⁻¹ * u * D.t⁻¹⁻¹) *
            (D.y * D.t * D.y⁻¹ * D.t)⁻¹ := by group
      _ = D.t⁻¹ * u * D.t⁻¹⁻¹ := h2
      _ = D.t ^ 3 * (D.t⁻¹ * u * D.t⁻¹⁻¹) * (D.t ^ 3)⁻¹ := h3.symm
      _ = D.t * (D.t * u * D.t⁻¹) * D.t⁻¹ := by
          rw [pow_three]
          simp only [mul_assoc, mul_inv_rev, inv_inv, mul_inv_cancel_left]
  have hra := hR2 u₀ hu₀C
  have hrb := hR2 u₁ hu₁C
  rw [conj_mul_eq, conj_mul_eq, hYia, conj_zpow_mul_zpow hab hTa hTb,
    conj_zpow_mul_zpow hab hYa hYb, hTa, conj_zpow_mul_zpow hab hTa hTb] at hra
  rw [conj_mul_eq, conj_mul_eq, hYib, conj_zpow_mul_zpow hab hTa hTb,
    conj_zpow_mul_zpow hab hYa hYb, hTb, conj_zpow_mul_zpow hab hTa hTb] at hrb
  have c1 := (hcoord _ _ _ _).mp (hea.trans hA1)
  have c2 := (hcoord _ _ _ _).mp (heb.trans hB1)
  have c3 := (hcoord _ _ _ _).mp hra
  have c4 := (hcoord _ _ _ _).mp hrb
  have E1 : (3 : ℤ) ^ h ∣ 2 * α ^ 2 - α - 1 := by
    have := dvd_sub c1.1 c3.1
    convert this using 1
    ring
  have E2 : (3 : ℤ) ^ k ∣ 2 * δ ^ 2 - δ - 1 := by
    have := dvd_sub c2.2 c4.2
    convert this using 1
    ring
  have hγ : (3 : ℤ) ^ (h - k) ∣ γ := by
    have h1 : (D.t * u₁ * D.t⁻¹) ^ ((3 : ℤ) ^ k) = 1 := by
      rw [conj_zpow, show ((3 : ℤ) ^ k) = ((3 ^ k : ℕ) : ℤ) by push_cast; rfl, zpow_natCast,
        ← hu₁o, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    rw [hTb, zpow_mul_zpow_zpow hab] at h1
    have h2 := ((hcoord1 _ _).mp h1).1
    rw [show (3 : ℤ) ^ h = 3 ^ (h - k) * 3 ^ k by rw [← pow_add, Nat.sub_add_cancel hkh]]
      at h2
    exact (mul_dvd_mul_iff_right (pow_ne_zero _ (by norm_num))).mp h2
  obtain ⟨γ₀, hγ₀⟩ := hγ
  have E5 : (3 : ℤ) ^ h ∣ α - α ^ 2 - β * (3 ^ (h - k) * γ₀) := by
    have := c3.1
    rw [← hγ₀]
    convert this using 1
    ring
  have F1 : ¬ (3 : ℤ) ∣ γ₀ := by
    rintro ⟨γ₁, hγ₁⟩
    have hustarA : u₁ ^ (3 ^ (k - 1)) ∈ D.A := D.A.pow_mem hu₁A _
    have hustar1 : u₁ ^ (3 ^ (k - 1)) ≠ 1 := by
      intro h1
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hu₁o] at h2
      have h3 := Nat.le_of_dvd (by positivity) h2
      have h4 : 3 ^ (k - 1) < 3 ^ k := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega
    have ht : D.t * u₁ ^ (3 ^ (k - 1)) * D.t⁻¹ = u₁ ^ ((δ : ℤ) * (3 ^ (k - 1) : ℕ)) := by
      rw [← conj_pow, hTb, ← zpow_natCast, zpow_mul_zpow_zpow hab]
      have h1 : u₀ ^ (γ * ((3 ^ (k - 1) : ℕ) : ℤ)) = 1 := by
        rw [← orderOf_dvd_iff_zpow_eq_one, hu₀o, hγ₀, hγ₁]
        refine ⟨γ₁, ?_⟩
        push_cast
        rw [show (3 : ℤ) ^ h = 3 ^ (h - k) * 3 * 3 ^ (k - 1) by
          rw [mul_assoc, ← pow_succ', ← pow_add]; congr 1; omega]
        ring
      rw [h1, one_mul]
    have htA : D.t * u₁ ^ (3 ^ (k - 1)) * D.t⁻¹ ∈ D.A := ht ▸ D.A.zpow_mem hu₁A _
    have hfix := D.conj_eq_of_mem_A hustarA htA
    apply D.t_not_mem_N
    apply D.A_confine _ hustarA hustar1
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact comm_of_conj_eq hfix
  have F2 : (3 : ℤ) ∣ δ - 1 → ¬ (3 : ℤ) ∣ β := fun hδ hβ =>
    D.false_of_invariant_line hext htriv hu₀ hu₁ hk1 hTa hTb hβ hδ
  rcases three_adic_cases hk1 hkh E1 E2 E5 F1 F2 with hcase | ⟨hk, hh3, s₀, hs₀, hα, hβγ⟩
  · exact Or.inl hcase
  right
  refine ⟨hk, hh3, ?_⟩
  have hδ := three_dvd_sub_one_of_dvd (three_dvd_of_pow_dvd hk1 E2)
  have hβ3 : ¬ (3 : ℤ) ∣ β := F2 hδ
  rw [hk, pow_one] at hu₁o
  have hu₁β3 : (u₁ ^ β) ^ 3 = 1 := by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hu₁o,
      pow_orderOf_eq_one, one_zpow]
  have hu₁β1 : u₁ ^ β ≠ 1 := by
    intro h1
    apply hβ3
    have := orderOf_dvd_iff_zpow_eq_one.mpr h1
    rwa [hu₁o] at this
  have hu₁βo : orderOf (u₁ ^ β) = 3 := orderOf_eq_prime hu₁β3 hu₁β1
  have hzp : D.PA 3 = Subgroup.zpowers (u₁ ^ β) := by
    rw [hu₁]
    refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
    · rw [Subgroup.zpowers_le]
      exact Subgroup.zpow_mem_zpowers u₁ β
    · rw [Nat.card_zpowers, Nat.card_zpowers, hu₁o, hu₁βo]
  refine ⟨u₀, u₁ ^ β, s₀, hu₀, hu₀o, hzp, hu₁βo, hs₀, ?_, ?_⟩
  · rw [hTa, hα]
  · rw [← conj_zpow, hTb, zpow_mul_zpow_zpow hab]
    apply (hcoord _ _ _ _).mpr
    constructor
    · rw [hγ₀, hk]
      obtain ⟨c, hc⟩ := hβγ
      refine ⟨c, ?_⟩
      rw [show (3 : ℤ) ^ h = 3 ^ (h - 1) * 3 by rw [← pow_succ]; congr 1; omega]
      linear_combination (3 ^ (h - 1) : ℤ) * hc
    · rw [hk, pow_one]
      obtain ⟨d, hd⟩ := hδ
      exact ⟨d * β, by rw [show δ = 3 * d + 1 by linarith]; ring⟩

theorem factorization_three_card_A (hext : D.CharacterExtend) (htriv : D.CharacterTrivial)
    (h3 : 3 ∣ Nat.card D.A) :
    (D.q + 1).factorization 3 = (Nat.card D.A).factorization 3 + 1 ∨
      ((Nat.card D.A).factorization 3 = 1 ∧ 3 ≤ (D.q + 1).factorization 3) := by
  rcases D.three_adic hext htriv h3 with h | ⟨h1, h2, -⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, h2⟩

end DValueData

end CFSG.Semidihedral.UnitaryDValue

