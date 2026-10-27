module

public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Data.Sym.Sym2.Init
public import Mathlib.RingTheory.LocalRing.Basic
public import Mathlib.Tactic.ContinuousFunctionalCalculus
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Positivity.Finset

public section

namespace CFSG.SeitzReduction.RankOne

namespace LineCount

variable {E : Type*} [Field E] {σ : E →+* E} {q : ℕ}

theorem pow_pred_eq_iff (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q) {z w : E} (hz : z ≠ 0)
    (hw : w ≠ 0) : z ^ (q - 1) = w ^ (q - 1) ↔ σ (w / z) = w / z := by
  rw [hσ]
  have hwz : w / z ≠ 0 := div_ne_zero hw hz
  have e : (w / z) ^ q = (w / z) ^ (q - 1) * (w / z) := by
    rw [← pow_succ]
    congr 1
    omega
  rw [e]
  constructor
  · intro h
    rw [div_pow, ← h, div_self (pow_ne_zero _ hz), one_mul]
  · intro h
    have h1 : (w / z) ^ (q - 1) = 1 := mul_right_cancel₀ hwz (h.trans (one_mul _).symm)
    rw [div_pow] at h1
    exact ((div_eq_one_iff_eq (pow_ne_zero _ hz)).mp h1).symm

theorem pow_pred_eq_one (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q) {l : E} (hl : σ l = l)
    (hl0 : l ≠ 0) : l ^ (q - 1) = 1 := by
  have h1 : (1 : E) ^ (q - 1) = l ^ (q - 1) := by
    rw [pow_pred_eq_iff hσ hq one_ne_zero hl0, div_one, hl]
  rw [← h1, one_pow]

theorem mul_pow_pred (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q) {l : E} (hl : σ l = l) (hl0 : l ≠ 0)
    (z : E) : (l * z) ^ (q - 1) = z ^ (q - 1) := by
  rw [mul_pow, pow_pred_eq_one hσ hq hl hl0, one_mul]

theorem exists_eq_add_mul [Finite E] (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) {z₀ w₀ : E} (hz₀ : z₀ ≠ 0)
    (hw₀ : w₀ ≠ 0) (hne : z₀ ^ (q - 1) ≠ w₀ ^ (q - 1)) (s : E) :
    ∃ α β : E, σ α = α ∧ σ β = β ∧ s = α * z₀ + β * w₀ := by
  let f : {x : E // σ x = x} × {x : E // σ x = x} → E := fun p => p.1.1 * z₀ + p.2.1 * w₀
  have hinj : Function.Injective f := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ h
    have e : (a - a') * z₀ = (b' - b) * w₀ := by
      simp only [f] at h
      linear_combination h
    by_cases hbb : b' - b = 0
    · have h0 : (a - a') * z₀ = 0 := by rw [e, hbb, zero_mul]
      have haa : a - a' = 0 := (mul_eq_zero.mp h0).resolve_right hz₀
      have h1 : a = a' := sub_eq_zero.mp haa
      have h2 : b = b' := (sub_eq_zero.mp hbb).symm
      subst h1 h2
      rfl
    · exfalso
      apply hne
      rw [pow_pred_eq_iff hσ hq hz₀ hw₀]
      have hw : w₀ / z₀ = (a - a') / (b' - b) := by
        rw [div_eq_div_iff hz₀ hbb]
        linear_combination -e
      rw [hw, map_div₀, map_sub, map_sub, ha, ha', hb, hb']
  have : Fintype E := Fintype.ofFinite E
  have hcard : Nat.card ({x : E // σ x = x} × {x : E // σ x = x}) = Nat.card E := by
    rw [Nat.card_prod, hF, hE, sq]
  have hbij : Function.Bijective f := by
    rw [Nat.bijective_iff_injective_and_card]
    exact ⟨hinj, hcard⟩
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hp⟩ := hbij.2 s
  exact ⟨a, b, ha, hb, hp.symm⟩

theorem exists_eq_mul_iff (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q) {z₀ : E} (hz₀ : z₀ ≠ 0) (z : E) :
    (∃ l : E, σ l = l ∧ z = l * z₀) ↔ (z = 0 ∨ z ^ (q - 1) = z₀ ^ (q - 1)) := by
  constructor
  · rintro ⟨l, hl, rfl⟩
    by_cases hl0 : l = 0
    · left; rw [hl0, zero_mul]
    · right; exact mul_pow_pred hσ hq hl hl0 z₀
  · rintro (rfl | h)
    · exact ⟨0, map_zero σ, (zero_mul z₀).symm⟩
    · by_cases hz : z = 0
      · exact ⟨0, map_zero σ, by rw [hz, zero_mul]⟩
      · refine ⟨z / z₀, ((pow_pred_eq_iff hσ hq hz₀ hz).mp h.symm), ?_⟩
        rw [div_mul_cancel₀ _ hz₀]

section Count

variable [Fintype E] [DecidableEq E]

@[expose] def line (q : ℕ) (z₀ : E) : Finset E :=
  Finset.univ.filter fun z => z = 0 ∨ z ^ (q - 1) = z₀ ^ (q - 1)

theorem mem_line {z₀ z : E} : z ∈ line q z₀ ↔ z = 0 ∨ z ^ (q - 1) = z₀ ^ (q - 1) := by
  simp [line]

theorem card_line (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q) (hF : Nat.card {x : E // σ x = x} = q)
    {z₀ : E} (hz₀ : z₀ ≠ 0) : (line q z₀).card = q := by
  have hFc : (Finset.univ.filter fun x : E => σ x = x).card = q := by
    rw [← hF, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have e : (Finset.univ.filter fun x : E => σ x = x).card = (line q z₀).card := by
    refine Finset.card_nbij (fun l => l * z₀) (fun l hl => ?_) (fun a _ b _ hab => ?_) ?_
    · have hl' : σ l = l := (Finset.mem_filter.mp hl).2
      exact mem_line.mpr ((exists_eq_mul_iff hσ hq hz₀ _).mp ⟨l, hl', rfl⟩)
    · exact mul_right_cancel₀ hz₀ hab
    · intro z hz
      obtain ⟨l, hl, rfl⟩ := (exists_eq_mul_iff hσ hq hz₀ z).mpr (mem_line.mp hz)
      exact ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl⟩, rfl⟩
  rw [← e, hFc]

theorem line_subset {S : Finset E} (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q)
    (hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S) {z₀ : E} (hz₀ : z₀ ≠ 0) (hz₀S : z₀ ∈ S) :
    line q z₀ ⊆ S := by
  intro z hz
  obtain ⟨l, hl, rfl⟩ := (exists_eq_mul_iff hσ hq hz₀ z).mpr (mem_line.mp hz)
  exact hSF l hl z₀ hz₀S

@[expose] def lines (q : ℕ) (S : Finset E) : Finset E := (S.erase 0).image fun z => z ^ (q - 1)

theorem card_erase_zero (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q)
    (hF : Nat.card {x : E // σ x = x} = q) {S : Finset E}
    (hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S) :
    (S.erase 0).card = (lines q S).card * (q - 1) := by
  rw [Finset.card_eq_sum_card_image (fun z => z ^ (q - 1)) (S.erase 0)]
  have hfib : ∀ b ∈ (S.erase 0).image fun z => z ^ (q - 1),
      ((S.erase 0).filter fun z => z ^ (q - 1) = b).card = q - 1 := by
    intro b hb
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp hb
    have hz₀0 : z₀ ≠ 0 := (Finset.mem_erase.mp hz₀).1
    have e : ((S.erase 0).filter fun z => z ^ (q - 1) = z₀ ^ (q - 1)) = (line q z₀).erase 0 := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_erase, mem_line]
      constructor
      · rintro ⟨⟨hz0, -⟩, h⟩
        exact ⟨hz0, Or.inr h⟩
      · rintro ⟨hz0, h⟩
        have h' : z ^ (q - 1) = z₀ ^ (q - 1) := h.resolve_left hz0
        refine ⟨⟨hz0, line_subset hσ hq hSF hz₀0 (Finset.mem_erase.mp hz₀).2 ?_⟩, h'⟩
        exact mem_line.mpr (Or.inr h')
    rw [e, Finset.card_erase_of_mem (mem_line.mpr (Or.inl rfl)), card_line hσ hq hF hz₀0]
  rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul]
  rfl

theorem pow_pred_mem_lines_iff (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q) {S : Finset E}
    (hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S) {s : E} (hs : s ≠ 0) :
    s ^ (q - 1) ∈ lines q S ↔ s ∈ S := by
  constructor
  · intro h
    obtain ⟨z, hz, hzs⟩ := Finset.mem_image.mp h
    exact line_subset hσ hq hSF (Finset.mem_erase.mp hz).1 (Finset.mem_erase.mp hz).2
      (mem_line.mpr (Or.inr hzs.symm))
  · intro h
    exact Finset.mem_image.mpr ⟨s, Finset.mem_erase.mpr ⟨hs, h⟩, rfl⟩

theorem card_filter_line [CharP E 2] (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q)
    (hF : Nat.card {x : E // σ x = x} = q) {S : Finset E}
    (hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S) {s : E} (hs : s ≠ 0) :
    ((S.filter fun z => s + z ∈ S).filter fun z => z ∈ line q s).card =
      if s ∈ S then q else 0 := by
  split_ifs with hsS
  · have e : ((S.filter fun z => s + z ∈ S).filter fun z => z ∈ line q s) = line q s := by
      ext z
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨⟨-, -⟩, hz⟩
        exact hz
      · intro hz
        refine ⟨⟨line_subset hσ hq hSF hs hsS hz, line_subset hσ hq hSF hs hsS ?_⟩, hz⟩
        obtain ⟨l, hl, rfl⟩ := (exists_eq_mul_iff hσ hq hs z).mpr (mem_line.mp hz)
        exact mem_line.mpr ((exists_eq_mul_iff hσ hq hs _).mp
          ⟨1 + l, by rw [map_add, map_one, hl], by ring⟩)
    rw [e, card_line hσ hq hF hs]
  · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro z hz hzl
    obtain ⟨hzS, hszS⟩ := Finset.mem_filter.mp hz
    obtain ⟨l, hl, rfl⟩ := (exists_eq_mul_iff hσ hq hs z).mpr (mem_line.mp hzl)
    by_cases hl0 : l = 0
    · rw [hl0, zero_mul, add_zero] at hszS
      exact hsS hszS
    · apply hsS
      have := hSF l⁻¹ (by rw [map_inv₀, hl]) _ hzS
      rwa [← mul_assoc, inv_mul_cancel₀ hl0, one_mul] at this

theorem card_filter_not_line [CharP E 2] (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) {S : Finset E}
    (hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S) {s : E} (hs : s ≠ 0) :
    ((S.filter fun z => s + z ∈ S).filter fun z => z ∉ line q s).card =
      (((lines q S).erase (s ^ (q - 1))).offDiag).card := by
  have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
  have hoff : ∀ z, z ∉ line q s → z ≠ 0 ∧ z ^ (q - 1) ≠ s ^ (q - 1) := fun z hz => by
    rw [mem_line, not_or] at hz
    exact hz
  have honl : ∀ z₀ l, σ l = l → z₀ ≠ 0 → l * z₀ ∈ line q z₀ := fun z₀ l hl hz₀ =>
    mem_line.mpr ((exists_eq_mul_iff hσ hq hz₀ _).mp ⟨l, hl, rfl⟩)
  have key : ∀ z, z ≠ 0 → ∀ l, σ l = l → s + z = l * z → z ∈ line q s := by
    intro z hz l hl he
    have hl1 : l + 1 ≠ 0 := by
      intro h0
      apply hs
      have : s = (l + 1) * z := by linear_combination he - z * h2
      rw [this, h0, zero_mul]
    have : z = (l + 1)⁻¹ * s := by
      field_simp
      linear_combination -he + z * h2
    rw [this]
    exact honl s _ (by rw [map_inv₀, map_add, map_one, hl]) hs
  refine Finset.card_nbij (fun z => (z ^ (q - 1), (s + z) ^ (q - 1))) ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_coe, Finset.mem_filter] at hz
    obtain ⟨⟨hzS, hszS⟩, hzl⟩ := hz
    obtain ⟨hz0, hzs⟩ := hoff z hzl
    have hsz0 : s + z ≠ 0 := by
      intro h0
      apply hzl
      have : z = s := by linear_combination h0 - s * h2
      rw [this]
      exact mem_line.mpr (Or.inr rfl)
    have hszs : (s + z) ^ (q - 1) ≠ s ^ (q - 1) := by
      intro h1
      apply hzl
      obtain ⟨l, hl, hl'⟩ := (exists_eq_mul_iff hσ hq hs _).mpr (Or.inr h1)
      have : z = (l + 1) * s := by linear_combination hl' - s * h2
      rw [this]
      exact honl s _ (by rw [map_add, map_one, hl]) hs
    have hzsz : z ^ (q - 1) ≠ (s + z) ^ (q - 1) := by
      intro h1
      obtain ⟨l, hl, hl'⟩ := (exists_eq_mul_iff hσ hq hz0 _).mpr (Or.inr h1.symm)
      exact hzl (key z hz0 l hl hl')
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe, Finset.mem_erase]
    exact ⟨⟨hzs, Finset.mem_image.mpr ⟨z, Finset.mem_erase.mpr ⟨hz0, hzS⟩, rfl⟩⟩,
      ⟨hszs, Finset.mem_image.mpr ⟨s + z, Finset.mem_erase.mpr ⟨hsz0, hszS⟩, rfl⟩⟩, hzsz⟩
  · intro z hz z' hz' he
    simp only [Finset.mem_coe, Finset.mem_filter] at hz hz'
    obtain ⟨hz0, -⟩ := hoff z hz.2
    simp only [Prod.mk.injEq] at he
    obtain ⟨e1, e2⟩ := he
    obtain ⟨l, hl, hz'l⟩ := (exists_eq_mul_iff hσ hq hz0 z').mpr (Or.inr e1.symm)
    have hsz0 : s + z ≠ 0 := by
      intro h0
      apply hz.2
      have : z = s := by linear_combination h0 - s * h2
      rw [this]
      exact mem_line.mpr (Or.inr rfl)
    obtain ⟨l', hl', hl'e⟩ := (exists_eq_mul_iff hσ hq hsz0 (s + z')).mpr (Or.inr e2.symm)
    by_cases h1 : 1 + l' = 0
    · have hl'1 : l' = 1 := by linear_combination h1 - h2
      rw [hl'1, one_mul] at hl'e
      linear_combination -hl'e
    · exfalso
      have e3 : (1 + l') * s = (l' + l) * z := by
        rw [hz'l] at hl'e
        linear_combination hl'e + (l' * s - l * z) * h2
      by_cases h3 : l' + l = 0
      · rw [h3, zero_mul] at e3
        exact hs ((mul_eq_zero.mp e3).resolve_left h1)
      · apply hz.2
        have : z = ((1 + l') / (l' + l)) * s := by
          field_simp
          linear_combination -e3
        rw [this]
        exact honl s _ (by rw [map_div₀, map_add, map_add, map_one, hl, hl']) hs
  · rintro ⟨a, b⟩ hab
    simp only [Finset.coe_offDiag, Set.mem_offDiag, Finset.mem_coe, Finset.mem_erase] at hab
    obtain ⟨⟨has, ha⟩, ⟨hbs, hb⟩, hab⟩ := hab
    obtain ⟨z₀, hz₀, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w₀, hw₀, rfl⟩ := Finset.mem_image.mp hb
    have hz₀0 := (Finset.mem_erase.mp hz₀).1
    have hw₀0 := (Finset.mem_erase.mp hw₀).1
    obtain ⟨α, β, hα, hβ, hsαβ⟩ := exists_eq_add_mul hσ hq hE hF hz₀0 hw₀0 hab s
    have hα0 : α ≠ 0 := by
      intro h0
      apply hbs
      rw [h0, zero_mul, zero_add] at hsαβ
      have hβ0 : β ≠ 0 := by
        intro h0'
        rw [h0', zero_mul] at hsαβ
        exact hs hsαβ
      rw [hsαβ, mul_pow_pred hσ hq hβ hβ0]
    have hβ0 : β ≠ 0 := by
      intro h0
      apply has
      rw [h0, zero_mul, add_zero] at hsαβ
      rw [hsαβ, mul_pow_pred hσ hq hα hα0]
    refine ⟨α * z₀, ?_, ?_⟩
    · simp only [Finset.mem_coe, Finset.mem_filter]
      have hsz : s + α * z₀ = β * w₀ := by linear_combination hsαβ + α * z₀ * h2
      refine ⟨⟨hSF α hα z₀ (Finset.mem_erase.mp hz₀).2, ?_⟩, ?_⟩
      · rw [hsz]; exact hSF β hβ w₀ (Finset.mem_erase.mp hw₀).2
      · rw [mem_line, not_or]
        exact ⟨mul_ne_zero hα0 hz₀0, by rw [mul_pow_pred hσ hq hα hα0]; exact has⟩
    · have hsz : s + α * z₀ = β * w₀ := by linear_combination hsαβ + α * z₀ * h2
      simp only [Prod.mk.injEq]
      rw [hsz, mul_pow_pred hσ hq hα hα0, mul_pow_pred hσ hq hβ hβ0]
      exact ⟨rfl, rfl⟩

theorem card_filter_add_mem [CharP E 2] (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) {S : Finset E}
    (hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S) {s : E} (hs : s ≠ 0) :
    (S.filter fun z => s + z ∈ S).card = (if s ∈ S then q else 0) +
      (((lines q S).erase (s ^ (q - 1))).card * ((lines q S).erase (s ^ (q - 1))).card -
        ((lines q S).erase (s ^ (q - 1))).card) := by
  rw [← Finset.card_filter_add_card_filter_not (s := S.filter fun z => s + z ∈ S)
    (fun z => z ∈ line q s), card_filter_line hσ hq hF hSF hs,
    card_filter_not_line hσ hq hE hF hSF hs, Finset.offDiag_card]

omit [Fintype E] in
theorem card_filter_add_mem_map {S : Finset E} (φ : E →+ E) (hφ : Function.Injective φ)
    (c : E) (hg : ∀ z ∈ S, φ z + c ∈ S) (s : E) :
    (S.filter fun z => φ s + z ∈ S).card = (S.filter fun z => s + z ∈ S).card := by
  have hginj : Function.Injective fun z => φ z + c := fun a b hab =>
    hφ (add_right_cancel hab)
  have hgS : S.image (fun z => φ z + c) = S :=
    Finset.eq_of_subset_of_card_le (fun w hw => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact hg z hz) (Finset.card_image_of_injective S hginj).ge
  have hmem : ∀ x, φ x + c ∈ S → x ∈ S := by
    intro x hx
    rw [← hgS] at hx
    obtain ⟨z, hz, hzx⟩ := Finset.mem_image.mp hx
    rwa [← hginj hzx]
  symm
  refine Finset.card_nbij (fun z => φ z + c) (fun z hz => ?_) (fun a _ b _ hab => hginj hab)
    (fun w hw => ?_)
  · simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
    refine ⟨hg z hz.1, ?_⟩
    have e : φ s + (φ z + c) = φ (s + z) + c := by rw [map_add, add_assoc]
    rw [e]
    exact hg _ hz.2
  · simp only [Finset.mem_coe, Finset.mem_filter] at hw
    have hw' := hw.1
    rw [← hgS] at hw'
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw'
    refine ⟨z, ?_, rfl⟩
    simp only [Finset.mem_coe, Finset.mem_filter]
    have e : φ s + (φ z + c) = φ (s + z) + c := by rw [map_add, add_assoc]
    rw [e] at hw
    exact ⟨hz, hmem _ hw.2⟩

theorem add_two_eq_of_count {q m : ℕ} (h : q + (m * m - m) = (m + 1) * (m + 1) - (m + 1)) :
    q + 2 = 2 * (m + 1) := by
  have hm : m ≤ m * m := Nat.le_mul_self m
  have e1 : (m + 1) * (m + 1) = m * m + m + (m + 1) := by ring
  rw [e1] at h
  omega

theorem add_mem_of_affine [CharP E 2] (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q)
    (hE : Nat.card E = q ^ 2) (hF : Nat.card {x : E // σ x = x} = q) {S : Finset E}
    (hSF : ∀ l, σ l = l → ∀ z ∈ S, l * z ∈ S) (h0 : 0 ∈ S)
    (hk : q + 2 ≠ 2 * (lines q S).card) (φ : E →+ E) (hφ : Function.Injective φ) (c : E)
    (hg : ∀ z ∈ S, φ z + c ∈ S) : ∀ z ∈ S, z + c ∈ S := by
  have hφS : ∀ s ∈ S, φ s ∈ S := by
    intro s hs
    by_cases hs0 : s = 0
    · rw [hs0, map_zero]
      exact h0
    by_contra hφs
    have hφs0 : φ s ≠ 0 := fun h1 => hs0 (hφ (h1.trans (map_zero φ).symm))
    have h1 := card_filter_add_mem_map φ hφ c hg s
    rw [card_filter_add_mem hσ hq hE hF hSF hs0, card_filter_add_mem hσ hq hE hF hSF hφs0,
      ite_eq_left hs, ite_eq_right hφs, zero_add,
      Finset.erase_eq_of_notMem (fun h => hφs ((pow_pred_mem_lines_iff hσ hq hSF hφs0).mp h)),
      Finset.card_erase_of_mem ((pow_pred_mem_lines_iff hσ hq hSF hs0).mpr hs)] at h1
    have hk1 : 1 ≤ (lines q S).card :=
      Finset.card_pos.mpr ⟨_, (pow_pred_mem_lines_iff hσ hq hSF hs0).mpr hs⟩
    obtain ⟨m, hm⟩ : ∃ m, (lines q S).card = m + 1 := ⟨_, (Nat.sub_add_cancel hk1).symm⟩
    rw [hm, Nat.add_sub_cancel] at h1
    exact hk (by rw [hm]; exact add_two_eq_of_count h1.symm)
  have hφim : S.image φ = S :=
    Finset.eq_of_subset_of_card_le (fun w hw => by
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hw
      exact hφS z hz) (Finset.card_image_of_injective S hφ).ge
  intro z hz
  rw [← hφim] at hz
  obtain ⟨z', hz', rfl⟩ := Finset.mem_image.mp hz
  exact hg z' hz'

theorem card_fixed_of_orderOf (hσ : ∀ x, σ x = x ^ q) (hq : 2 ≤ q) {ζ : E}
    (hζ : orderOf ζ = q - 1) : Nat.card {x : E // σ x = x} = q := by
  have hprim : IsPrimitiveRoot ζ (q - 1) := hζ ▸ IsPrimitiveRoot.orderOf ζ
  have hq1 : 0 < q - 1 := by omega
  have e : (Finset.univ.filter fun x : E => σ x = x) =
      insert 0 (Polynomial.nthRootsFinset (q - 1) (1 : E)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Polynomial.mem_nthRootsFinset hq1, hσ]
    constructor
    · intro h
      by_cases hx : x = 0
      · exact Or.inl hx
      · right
        have h1 : x ^ (q - 1) * x = 1 * x := by
          rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ q), h, one_mul]
        exact mul_right_cancel₀ hx h1
    · rintro (rfl | h)
      · exact zero_pow (by omega)
      · have e2 : q = (q - 1) + 1 := by omega
        rw [e2, pow_succ, h, one_mul]
  have h0 : (0 : E) ∉ Polynomial.nthRootsFinset (q - 1) (1 : E) := by
    rw [Polynomial.mem_nthRootsFinset hq1, zero_pow (by omega)]
    exact zero_ne_one
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, e, Finset.card_insert_of_notMem h0,
    hprim.card_nthRootsFinset]
  omega

omit [Fintype E] [DecidableEq E] in
theorem exists_pow_eq_of_fixed (hσ : ∀ x, σ x = x ^ q) (hq : 1 ≤ q) {μ : E}
    (hμ : orderOf μ ≠ 0) (hdvd : q - 1 ∣ orderOf μ) {l : E} (hl : σ l = l) (hl0 : l ≠ 0) :
    ∃ i : ℕ, μ ^ i = l := by
  have : NeZero (orderOf μ) := ⟨hμ⟩
  obtain ⟨r, hr⟩ := hdvd
  have hl1 : l ^ orderOf μ = 1 := by
    rw [hr, pow_mul, pow_pred_eq_one hσ hq hl hl0, one_pow]
  obtain ⟨i, -, hi⟩ := (IsPrimitiveRoot.orderOf μ).eq_pow_of_pow_eq_one hl1
  exact ⟨i, hi⟩

omit [Fintype E] [DecidableEq E] in
theorem exists_card_eq_two_pow [CharP E 2] [Finite E] {n : ℕ} (hE : Nat.card E = 2 ^ n)
    {S : Finset E} (h0 : 0 ∈ S) (hadd : ∀ z ∈ S, ∀ w ∈ S, z + w ∈ S) :
    ∃ j, S.card = 2 ^ j := by
  let H : AddSubgroup E :=
    { carrier := (S : Set E)
      add_mem' := fun {a b} ha hb => hadd a ha b hb
      zero_mem' := h0
      neg_mem' := fun {a} ha => by
        show -a ∈ S
        rw [CharTwo.neg_eq]
        exact ha }
  have h1 : Nat.card H ∣ 2 ^ n := hE ▸ AddSubgroup.card_addSubgroup_dvd_card H
  have h2 : Nat.card H = S.card := by
    change Nat.card (S : Set E) = S.card
    rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  exact ⟨j, h2 ▸ hj⟩

end Count

end LineCount

end CFSG.SeitzReduction.RankOne
