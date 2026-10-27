module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneUnitarySmallTwoLines
public import Mathlib.GroupTheory.PGroup
public import Mathlib.FieldTheory.Finite.Basic

public section

namespace CFSG.SeitzReduction.RankOne

namespace LineCount

variable {E : Type*} [Field E]

theorem card_erase_zero_of_isPrimitiveRoot [Fintype E] [DecidableEq E] {ζ : E} {n : ℕ}
    (hζ : IsPrimitiveRoot ζ n) (hn : 0 < n) {S : Finset E} (hS : ∀ z ∈ S, ζ * z ∈ S) :
    (S.erase 0).card = ((S.erase 0).image fun z => z ^ n).card * n := by
  have : NeZero n := ⟨hn.ne'⟩
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hn.ne'
  have hpow : ∀ i : ℕ, ∀ z ∈ S, ζ ^ i * z ∈ S := by
    intro i
    induction i with
    | zero => intro z hz; rwa [pow_zero, one_mul]
    | succ i ih => intro z hz; rw [pow_succ', mul_assoc]; exact hS _ (ih z hz)
  rw [Finset.card_eq_sum_card_image (fun z => z ^ n) (S.erase 0)]
  have hfib : ∀ b ∈ (S.erase 0).image fun z => z ^ n,
      ((S.erase 0).filter fun z => z ^ n = b).card = n := by
    intro b hb
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hb
    have hz₀0 := (Finset.mem_erase.mp hz₀).1
    have e : ((S.erase 0).filter fun z => z ^ n = z₀ ^ n) =
        (Finset.range n).image fun i => ζ ^ i * z₀ := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_image, Finset.mem_range]
      constructor
      · rintro ⟨⟨hz0, -⟩, hzn⟩
        have h1 : (z / z₀) ^ n = 1 := by rw [div_pow, hzn, div_self (pow_ne_zero _ hz₀0)]
        obtain ⟨i, hi, hie⟩ := hζ.eq_pow_of_pow_eq_one h1
        exact ⟨i, hi, by rw [hie, div_mul_cancel₀ _ hz₀0]⟩
      · rintro ⟨i, -, rfl⟩
        refine ⟨⟨mul_ne_zero (pow_ne_zero _ hζ0) hz₀0, hpow i z₀ (Finset.mem_erase.mp hz₀).2⟩,
          ?_⟩
        rw [mul_pow, ← pow_mul, mul_comm i n, pow_mul, hζ.pow_eq_one, one_pow, one_mul]
    rw [e, Finset.card_image_of_injOn, Finset.card_range]
    intro i hi j hj hij
    exact hζ.pow_inj (Finset.mem_range.mp (Finset.mem_coe.mp hi))
      (Finset.mem_range.mp (Finset.mem_coe.mp hj)) (mul_right_cancel₀ hz₀0 hij)
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]

end LineCount

namespace TraceForm

variable {E : Type*} [Field E] {σ : E →+* E}

@[expose] def form (σ : E →+* E) (a b : E) : E := a * σ b + σ a * b

theorem form_sub_left (a a' b : E) : form σ (a - a') b = form σ a b - form σ a' b := by
  simp only [form, map_sub]
  ring

theorem form_mul_left {l : E} (hl : σ l = l) (a b : E) : form σ (l * a) b = l * form σ a b := by
  simp only [form, map_mul, hl]
  ring

theorem form_mul_right {l : E} (hl : σ l = l) (a b : E) : form σ a (l * b) = l * form σ a b := by
  simp only [form, map_mul, hl]
  ring

theorem form_add_right (a b b' : E) : form σ a (b + b') = form σ a b + form σ a b' := by
  simp only [form, map_add]
  ring

theorem form_sub_right (a b b' : E) : form σ a (b - b') = form σ a b - form σ a b' := by
  simp only [form, map_sub]
  ring

theorem form_self [CharP E 2] (a : E) : form σ a a = 0 := by
  rw [form, mul_comm (σ a) a]
  exact CharTwo.add_self_eq_zero _

theorem eq_mul_of_form_eq_zero [CharP E 2] {v₀ x : E} (hv₀ : v₀ ≠ 0)
    (h : form σ v₀ x = 0) : ∃ l : E, σ l = l ∧ x = l * v₀ := by
  have hσv₀ : σ v₀ ≠ 0 := (map_ne_zero σ).mpr hv₀
  have h1 : v₀ * σ x = σ v₀ * x := by
    have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
    rw [form] at h
    linear_combination h - σ v₀ * x * h2
  refine ⟨x / v₀, ?_, by rw [div_mul_cancel₀ _ hv₀]⟩
  rw [map_div₀, div_eq_div_iff hσv₀ hv₀]
  linear_combination h1

theorem sigma_sigma [Finite E] {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hE : Nat.card E = q ^ 2)
    (x : E) : σ (σ x) = x := by
  have : Fintype E := Fintype.ofFinite E
  rw [hσ, hσ, ← pow_mul, ← sq]
  have h1 : x ^ Fintype.card E = x := FiniteField.pow_card x
  rwa [← Nat.card_eq_fintype_card, hE] at h1

theorem exists_form_ne_zero [Finite E] [CharP E 2] {q : ℕ} (hσ : ∀ x, σ x = x ^ q)
    (hq : 2 ≤ q) (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) {a : E}
    (ha : a ≠ 0) : ∃ b : E, form σ a b ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x : E, σ x ≠ x := by
    by_contra hall
    push Not at hall
    have h1 : Nat.card {x : E // σ x = x} = Nat.card E :=
      Nat.card_congr (Equiv.subtypeUnivEquiv hall)
    rw [hF, hE] at h1
    have : q < q ^ 2 := by nlinarith
    omega
  refine ⟨σ (x / a), fun h0 => hx ?_⟩
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  rw [form, sigma_sigma hσ hE, ← map_mul, mul_div_cancel₀ _ ha] at h0
  linear_combination h0 - x * h2

theorem map_mul_of_form [Finite E] [CharP E 2] {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hq : 2 ≤ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) (φ : E →+ E)
    (hφs : Function.Surjective φ) (hφ : ∀ a b, form σ (φ a) (φ b) = form σ a b) {l : E}
    (hl : σ l = l) (a : E) : φ (l * a) = l * φ a := by
  by_contra hne
  have hne' : φ (l * a) - l * φ a ≠ 0 := sub_ne_zero.mpr hne
  obtain ⟨z, hz⟩ := exists_form_ne_zero hσ hq hE hF hne'
  obtain ⟨b, rfl⟩ := hφs z
  apply hz
  rw [form_sub_left, form_mul_left hl, hφ, hφ, form_mul_left hl, sub_self]

theorem card_le_of_form [Finite E] [CharP E 2] {q : ℕ} (hσ : ∀ x, σ x = x ^ q) (hq : 2 ≤ q)
    (hqe : Even q) (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) {P : Type*}
    [Group P] [Finite P] (hP : IsPGroup 2 P) (ρ : P →* Equiv.Perm E) (hρ : Function.Injective ρ)
    (hadd : ∀ g a b, ρ g (a + b) = ρ g a + ρ g b)
    (hform : ∀ g a b, form σ (ρ g a) (ρ g b) = form σ a b) : Nat.card P ≤ q := by
  classical
  let : MulAction P E := MulAction.compHom E ρ
  have hsmul : ∀ (g : P) (x : E), g • x = ρ g x := fun g x => rfl
  let ρa : P → (E →+ E) := fun g => AddMonoidHom.mk' (ρ g) (hadd g)
  have hρa : ∀ g x, ρa g x = ρ g x := fun g x => rfl
  obtain ⟨v₀, hv₀, hv₀0⟩ : ∃ v₀ : E, (∀ g : P, ρ g v₀ = v₀) ∧ v₀ ≠ 0 := by
    have hmod := hP.card_modEq_card_fixedPoints E
    have hEev : Nat.card E % 2 = 0 := by
      obtain ⟨r, hr⟩ := hqe
      rw [hE, hr, show (r + r) ^ 2 = 2 * (2 * r ^ 2) by ring, Nat.mul_mod_right]
    have : Fintype E := Fintype.ofFinite E
    have h0 : (0 : E) ∈ MulAction.fixedPoints P E := fun g => by
      rw [hsmul, ← hρa, map_zero]
    have hfix : Nat.card (MulAction.fixedPoints P E) % 2 = 0 := by
      have := hmod.symm
      rw [Nat.ModEq] at this
      omega
    by_contra hall
    push Not at hall
    have hsub : MulAction.fixedPoints P E = {0} := by
      ext x
      simp only [Set.mem_singleton_iff]
      constructor
      · intro hx
        by_contra hx0
        exact hx0 (hall x (fun g => hx g))
      · rintro rfl
        exact h0
    rw [hsub, Nat.card_unique] at hfix
    omega
  obtain ⟨w₀, hw₀⟩ := exists_form_ne_zero hσ hq hE hF hv₀0
  have hlam : ∀ g : P, ∃ l : E, σ l = l ∧ ρ g w₀ - w₀ = l * v₀ := by
    intro g
    refine eq_mul_of_form_eq_zero hv₀0 ?_
    rw [form_sub_right, ← hform g v₀ w₀, hv₀ g, sub_self]
  choose lam hlamσ hlamv using hlam
  have hw₀0 : w₀ ≠ 0 := by
    rintro rfl
    apply hw₀
    simp [form]
  have hind : v₀ ^ (q - 1) ≠ w₀ ^ (q - 1) := by
    intro h1
    obtain ⟨l, hl, hlw⟩ := (LineCount.exists_eq_mul_iff hσ (by omega) hv₀0 w₀).mpr (Or.inr h1.symm)
    apply hw₀
    rw [hlw, form_mul_right hl, form_self, mul_zero]
  have hlin : ∀ (g : P) (l a : E), σ l = l → ρ g (l * a) = l * ρ g a := fun g l a hl =>
    map_mul_of_form hσ hq hE hF (ρa g) (ρ g).surjective (hform g) hl a
  refine (Nat.card_le_card_of_injective (fun g => (⟨lam g, hlamσ g⟩ : {x : E // σ x = x}))
    fun g g' hgg' => hρ ?_).trans hF.le
  have hl : lam g = lam g' := congrArg Subtype.val hgg'
  have hgw : ρ g w₀ = ρ g' w₀ := by
    have h1 := hlamv g
    have h2 := hlamv g'
    rw [hl] at h1
    linear_combination h1 - h2
  ext x
  obtain ⟨α, β, hα, hβ, rfl⟩ := LineCount.exists_eq_add_mul hσ (by omega) hE hF hv₀0 hw₀0 hind x
  rw [hadd, hadd, hlin g α v₀ hα, hlin g β w₀ hβ, hlin g' α v₀ hα, hlin g' β w₀ hβ,
    hv₀ g, hv₀ g', hgw]

end TraceForm

end CFSG.SeitzReduction.RankOne
