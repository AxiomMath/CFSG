module

public import CFSG.RankThree.PartOne.KC.EvenSymplecticFourRootAxisStructure
public import CFSG.LocalAnalysis.SteinbergSFFullCenterWeylOvergroupsBase
public import CFSG.LocalAnalysis.SteinbergSFFullCenterTorusComplementBase
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bSylow

public section

namespace CFSG.LocalAnalysis.EvenBN.Sp4

namespace ProductModel

open Subgroup
open scoped commutatorElement
open CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.RankThree.PartOne.KCRootAxis
open CFSG.LocalAnalysis.SymplecticFourStandard.FullCenterWeyl
  (weylElt weylMat glMat_weylElt weylElt_inv)
open CFSG.LocalAnalysis.SymplecticFourStandard.FullCenterTorus (axisTorus)
open CFSG.LocalAnalysis.SymplecticFourStandard.GomiFusion (diagTorus_conj exists_diagTorus)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_map_conj_iff_inv_mul_mul_mem {G : Type*} [Group G] {H : Subgroup G} {g y : G} :
    y ∈ H.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ H := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem eq_one_of_sq_eq_one_in_charTwo {r : K} (h : r ^ 2 = 1) : r = 1 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have h1 : (r - 1) ^ 2 = 0 := by linear_combination h - (r - 1) * h2
  have h3 : r - 1 = 0 := (pow_eq_zero_iff two_ne_zero).mp h1
  linear_combination h3

theorem eq_zero_of_mul_eq_self_of_ne_one {s x : K} (hs : s ≠ 1) (h : s * x = x) : x = 0 := by
  have h1 : (s - 1) * x = 0 := by linear_combination h
  exact (mul_eq_zero.mp h1).resolve_left (sub_ne_zero.mpr hs)

theorem glMat_coe_mul (x y : antiSp K) :
    glMat ((x * y : antiSp K) : GL (Fin 4) K) =
      glMat (x : GL (Fin 4) K) * glMat (y : GL (Fin 4) K) :=
  rfl

theorem uElt_congr {a b c d a' b' c' d' : K} (h₁ : a = a') (h₂ : b = b') (h₃ : c = c')
    (h₄ : d = d') : uElt a b c d = uElt a' b' c' d' := by
  rw [h₁, h₂, h₃, h₄]

theorem weylMat_one_mul_two :
    weylMat K Axis.one * weylMat K Axis.two =
      !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem weylMat_two_mul_one :
    weylMat K Axis.two * weylMat K Axis.one =
      !![0, 1, 0, 0; 0, 0, 0, 1; 1, 0, 0, 0; 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem weylMat_one_mul_two_mul_one :
    weylMat K Axis.one * weylMat K Axis.two * weylMat K Axis.one =
      !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0] := by
  rw [weylMat_one_mul_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [weylMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem commutator_uElt_uElt (a b c d A B C D : K) :
    ⁅uElt a b c d, uElt A B C D⁆ = uElt 0 (a * D + A * d) (a ^ 2 * D + A ^ 2 * d) 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [commutatorElement_def, uElt_inv, uElt_inv, uElt_mul, uElt_mul, uElt_mul]
  refine uElt_congr ?_ ?_ ?_ ?_
  · linear_combination (A + a) * h2
  · linear_combination (B + A * D + b + a * D + a * d) * h2
  · linear_combination (C + A * B + A ^ 2 * D + c + 2 * b * A + 2 * a * B + 3 * a * A * D +
      2 * a * d * A + a * b + a ^ 2 * d) * h2
  · linear_combination (D + d) * h2

theorem uElt_coords_of_commute {a b c d A B C D : K}
    (h : uElt a b c d * uElt A B C D = uElt A B C D * uElt a b c d) :
    a * D = A * d ∧ a * A * D = a * A * d := by
  rw [uElt_mul, uElt_mul] at h
  obtain ⟨-, h₁, h₃, -⟩ := uElt_inj h
  exact ⟨by linear_combination h₁, by linear_combination h₃⟩

theorem coords_eq_of_orth {a d A D : K} (ha : a ≠ 0) (hd : d ≠ 0) (h₁ : a * D = A * d)
    (h₂ : a * A * D = a * A * d) : (A = 0 ∧ D = 0) ∨ (A = a ∧ D = d) := by
  have h₃ : (a * A) * (D - d) = 0 := by linear_combination h₂
  rcases mul_eq_zero.mp h₃ with h₄ | h₄
  · have hA : A = 0 := (mul_eq_zero.mp h₄).resolve_left ha
    refine Or.inl ⟨hA, ?_⟩
    have h₅ : a * D = 0 := by rw [h₁, hA, zero_mul]
    exact (mul_eq_zero.mp h₅).resolve_left ha
  · have hD : D = d := sub_eq_zero.mp h₄
    refine Or.inr ⟨?_, hD⟩
    have h₅ : (a - A) * d = 0 := by linear_combination h₁ - a * h₄
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h₅).resolve_right hd)).symm

theorem exists_uElt_add_mem {H : Subgroup (antiSp K)} {a d a' d' : K}
    (h : ∃ b c : K, uElt a b c d ∈ H) (h' : ∃ b c : K, uElt a' b c d' ∈ H) :
    ∃ b c : K, uElt (a + a') b c (d + d') ∈ H := by
  obtain ⟨b, c, hbc⟩ := h
  obtain ⟨b', c', hbc'⟩ := h'
  have hmul := mul_mem hbc hbc'
  rw [uElt_mul] at hmul
  exact ⟨_, _, hmul⟩

theorem eq_antiUnipotent_of_pairs (hK : 2 < Nat.card K) {H : Subgroup (antiSp K)}
    (hH : H ≤ antiUnipotent K) (hp : ∀ a d : K, ∃ b c : K, uElt a b c d ∈ H) :
    H = antiUnipotent K := by
  have hZ : antiUnipotentCenter K ≤ H := by
    rw [← commutator_antiUnipotent_eq hK]
    refine Subgroup.commutator_le.2 ?_
    rintro _ ⟨a, b, c, d, rfl⟩ _ ⟨A, B, C, D, rfl⟩
    obtain ⟨b₁, c₁, h₁⟩ := hp a d
    obtain ⟨b₂, c₂, h₂⟩ := hp A D
    have hc : ⁅uElt a b₁ c₁ d, uElt A b₂ c₂ D⁆ ∈ H := by
      rw [commutatorElement_def]
      exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)
    rw [commutator_uElt_uElt] at hc ⊢
    exact hc
  refine le_antisymm hH fun x hx => ?_
  obtain ⟨a, b, c, d, rfl⟩ := hx
  obtain ⟨b₁, c₁, h₁⟩ := hp a d
  have hz : (uElt a b₁ c₁ d)⁻¹ * uElt a b c d ∈ antiUnipotentCenter K :=
    ⟨b₁ + a * d + b + a * d, c₁ + c + a * b + a * a * d + (b₁ + a * d) * a, by
      rw [uElt_inv, uElt_mul, CharTwo.add_self_eq_zero a, CharTwo.add_self_eq_zero d]⟩
  have hmul := mul_mem h₁ (hZ hz)
  rwa [mul_inv_cancel_left] at hmul

theorem exists_mul_mul_of_mem_sup_sup {G : Type*} [Group G] {H₁ H₂ Z : Subgroup G}
    (h₁₂ : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x)
    (hZ : ∀ z ∈ Z, ∀ x ∈ H₁ ⊔ H₂, x * z = z * x) {x : G} (hx : x ∈ H₁ ⊔ H₂ ⊔ Z) :
    ∃ h₁ ∈ H₁, ∃ h₂ ∈ H₂, ∃ z ∈ Z, x = h₁ * h₂ * z := by
  have hn₁ : H₂ ≤ Subgroup.normalizer (H₁ : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro y hy k hk
    rw [← h₁₂ k hk y hy, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  have hn₂ : Z ≤ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro z hz k hk
    rw [← hZ z hz k hk, mul_assoc, mul_inv_cancel, mul_one]
    exact hk
  have e₁ := Subgroup.coe_mul_of_right_le_normalizer_left H₁ H₂ hn₁
  have e₂ := Subgroup.coe_mul_of_right_le_normalizer_left (H₁ ⊔ H₂) Z hn₂
  have hx' : x ∈ ((H₁ ⊔ H₂ ⊔ Z : Subgroup G) : Set G) := hx
  rw [e₂] at hx'
  obtain ⟨y, hy, z, hz, rfl⟩ := hx'
  have hy' : y ∈ ((H₁ ⊔ H₂ : Subgroup G) : Set G) := hy
  rw [e₁] at hy'
  obtain ⟨h₁, hh₁, h₂, hh₂, rfl⟩ := hy'
  exact ⟨h₁, hh₁, h₂, hh₂, z, hz, rfl⟩

theorem exists_pairs_of_le_sup {H₁ H₂ : Subgroup (antiSp K)} (hH₁ : H₁ ≤ antiUnipotent K)
    (hH₂ : H₂ ≤ antiUnipotent K) (hc : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x)
    (hU : antiUnipotent K ≤ H₁ ⊔ H₂ ⊔ antiUnipotentCenter K) (x y : K) :
    ∃ a₁ d₁ a₂ d₂ : K, (∃ b c : K, uElt a₁ b c d₁ ∈ H₁) ∧ (∃ b c : K, uElt a₂ b c d₂ ∈ H₂) ∧
      x = a₁ + a₂ ∧ y = d₁ + d₂ := by
  have hsup : H₁ ⊔ H₂ ≤ antiUnipotent K := sup_le hH₁ hH₂
  obtain ⟨h₁, hh₁, h₂, hh₂, z, hz, hxe⟩ := exists_mul_mul_of_mem_sup_sup hc
    (fun z hz g hg => (antiUnipotentCenter_comm hz (hsup hg)).symm)
    (hU (uElt_mem_antiUnipotent x 0 0 y))
  obtain ⟨a₁, b₁, c₁, d₁, rfl⟩ := hH₁ hh₁
  obtain ⟨a₂, b₂, c₂, d₂, rfl⟩ := hH₂ hh₂
  obtain ⟨b₃, c₃, rfl⟩ := hz
  rw [uElt_mul, uElt_mul] at hxe
  obtain ⟨hx₁, -, -, hx₄⟩ := uElt_inj hxe
  exact ⟨a₁, d₁, a₂, d₂, ⟨b₁, c₁, hh₁⟩, ⟨b₂, c₂, hh₂⟩, by linear_combination hx₁,
    by linear_combination hx₄⟩

theorem eq_antiUnipotent_of_commute_of_pair (hK : 2 < Nat.card K) {H H' : Subgroup (antiSp K)}
    (hH : H ≤ antiUnipotent K) (hc : ∀ x ∈ H, ∀ y ∈ H', x * y = y * x)
    (hspan : ∀ x y : K, ∃ a₁ d₁ a₂ d₂ : K, (∃ b c : K, uElt a₁ b c d₁ ∈ H) ∧
      (∃ b c : K, uElt a₂ b c d₂ ∈ H') ∧ x = a₁ + a₂ ∧ y = d₁ + d₂)
    {a₀ d₀ : K} (ha₀ : a₀ ≠ 0) (hd₀ : d₀ ≠ 0) (h₀ : ∃ b c : K, uElt a₀ b c d₀ ∈ H) :
    H = antiUnipotent K := by
  refine eq_antiUnipotent_of_pairs hK hH fun x y => ?_
  obtain ⟨a₁, d₁, a₂, d₂, h₁, ⟨b₂, c₂, h₂⟩, rfl, rfl⟩ := hspan x y
  obtain ⟨b₀, c₀, h₀'⟩ := h₀
  obtain ⟨e₁, e₂⟩ := uElt_coords_of_commute (hc _ h₀' _ h₂)
  rcases coords_eq_of_orth ha₀ hd₀ e₁ e₂ with ⟨hA, hD⟩ | ⟨hA, hD⟩
  · rw [hA, hD, add_zero, add_zero]
    exact h₁
  · rw [hA, hD]
    exact exists_uElt_add_mem h₁ ⟨b₀, c₀, h₀'⟩

theorem antiUnipotent_eq_of_commute (hK : 4 ≤ Nat.card K) {H₁ H₂ : Subgroup (antiSp K)}
    (hH₁ : H₁ ≤ antiUnipotent K) (hH₂ : H₂ ≤ antiUnipotent K)
    (hn₁ : ∀ u ∈ antiUnipotent K, ∀ x ∈ H₁, u * x * u⁻¹ ∈ H₁)
    (hn₂ : ∀ u ∈ antiUnipotent K, ∀ x ∈ H₂, u * x * u⁻¹ ∈ H₂)
    (hc : ∀ x ∈ H₁, ∀ y ∈ H₂, x * y = y * x)
    (hU : antiUnipotent K ≤ H₁ ⊔ H₂ ⊔ antiUnipotentCenter K) :
    H₁ = antiUnipotent K ∨ H₂ = antiUnipotent K := by
  have hK2 : 2 < Nat.card K := by omega
  clear hn₁ hn₂
  have hspan := exists_pairs_of_le_sup hH₁ hH₂ hc hU
  have hspan' : ∀ x y : K, ∃ a₁ d₁ a₂ d₂ : K, (∃ b c : K, uElt a₁ b c d₁ ∈ H₂) ∧
      (∃ b c : K, uElt a₂ b c d₂ ∈ H₁) ∧ x = a₁ + a₂ ∧ y = d₁ + d₂ := by
    intro x y
    obtain ⟨a₁, d₁, a₂, d₂, h₁, h₂, hx, hy⟩ := hspan x y
    exact ⟨a₂, d₂, a₁, d₁, h₂, h₁, by rw [hx, add_comm], by rw [hy, add_comm]⟩
  by_cases h₁ : ∃ a d : K, a ≠ 0 ∧ d ≠ 0 ∧ ∃ b c : K, uElt a b c d ∈ H₁
  · obtain ⟨a₀, d₀, ha₀, hd₀, h₀⟩ := h₁
    exact Or.inl (eq_antiUnipotent_of_commute_of_pair hK2 hH₁ hc hspan ha₀ hd₀ h₀)
  by_cases h₂ : ∃ a d : K, a ≠ 0 ∧ d ≠ 0 ∧ ∃ b c : K, uElt a b c d ∈ H₂
  · obtain ⟨a₀, d₀, ha₀, hd₀, h₀⟩ := h₂
    exact Or.inr (eq_antiUnipotent_of_commute_of_pair hK2 hH₂
      (fun x hx y hy => (hc y hy x hx).symm) hspan' ha₀ hd₀ h₀)
  exfalso
  obtain ⟨a₁, d₁, a₂, d₂, ⟨b₁, c₁, hb₁⟩, ⟨b₂, c₂, hb₂⟩, hx, hy⟩ := hspan 1 1
  obtain ⟨e₁, -⟩ := uElt_coords_of_commute (hc _ hb₁ _ hb₂)
  have hdd : d₁ = a₁ := by linear_combination (-1 : K) * e₁ - a₁ * hy + d₁ * hx
  by_cases ha₁ : a₁ = 0
  · have hd₁ : d₁ = 0 := by rw [hdd, ha₁]
    have ha₂ : a₂ = 1 := by linear_combination -hx - ha₁
    have hd₂ : d₂ = 1 := by linear_combination -hy - hd₁
    exact h₂ ⟨a₂, d₂, by rw [ha₂]; exact one_ne_zero, by rw [hd₂]; exact one_ne_zero, b₂, c₂, hb₂⟩
  · exact h₁ ⟨a₁, d₁, ha₁, by rw [hdd]; exact ha₁, b₁, c₁, hb₁⟩

theorem antiUnipotent_inf_centralizer_axisTorus_le (hK : 4 ≤ Nat.card K) (i : Axis) :
    antiUnipotent K ⊓ centralizer (axisTorus K i : Set (antiSp K)) ≤ antiUnipotentCenter K := by
  intro g hg
  obtain ⟨⟨a, b, c, d, rfl⟩, hg⟩ := Subgroup.mem_inf.mp hg
  obtain ⟨r, hr0, hr1⟩ := exists_ne_zero_ne (K := K) (by omega) 1
  have hr1' : r ≠ 1 := fun h => hr1 h.symm
  rw [mem_centralizer_iff] at hg
  cases i
  · obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) hr0 (inv_ne_zero hr0)
    have h1 : δ * uElt a b c d = uElt a b c d * δ := hg δ ⟨r, hr0, hδ⟩
    have h2 : δ⁻¹ * uElt a b c d * δ = uElt a b c d := by
      rw [mul_assoc, ← h1, inv_mul_cancel_left]
    rw [diagTorus_conj hr0 (inv_ne_zero hr0) hδ] at h2
    obtain ⟨ha, -, -, hd⟩ := uElt_inj h2
    have ha0 : a = 0 := by
      refine eq_zero_of_mul_eq_self_of_ne_one (s := r * r⁻¹⁻¹) ?_ ha
      rw [inv_inv, ← sq]
      exact fun h => hr1' (eq_one_of_sq_eq_one_in_charTwo h)
    have hd0 : d = 0 :=
      eq_zero_of_mul_eq_self_of_ne_one (s := r⁻¹ ^ 2)
        (fun h => hr1' (inv_eq_one.mp (eq_one_of_sq_eq_one_in_charTwo h))) hd
    exact ⟨b, c, by rw [ha0, hd0]⟩
  · obtain ⟨δ, -, hδ⟩ := exists_diagTorus (K := K) one_ne_zero hr0
    have h1 : δ * uElt a b c d = uElt a b c d * δ := hg δ ⟨r, hr0, hδ⟩
    have h2 : δ⁻¹ * uElt a b c d * δ = uElt a b c d := by
      rw [mul_assoc, ← h1, inv_mul_cancel_left]
    rw [diagTorus_conj one_ne_zero hr0 hδ] at h2
    obtain ⟨ha, -, -, hd⟩ := uElt_inj h2
    have ha0 : a = 0 := by
      refine eq_zero_of_mul_eq_self_of_ne_one (s := 1 * r⁻¹) ?_ ha
      rw [one_mul]
      exact fun h => hr1' (inv_eq_one.mp h)
    have hd0 : d = 0 :=
      eq_zero_of_mul_eq_self_of_ne_one (s := r ^ 2)
        (fun h => hr1' (eq_one_of_sq_eq_one_in_charTwo h)) hd
    exact ⟨b, c, by rw [ha0, hd0]⟩

theorem weylElt_mul_weylElt_pow_four :
    (weylElt K Axis.one * weylElt K Axis.two) ^ 4 = 1 := by
  set w₁ := weylElt K Axis.one
  set w₂ := weylElt K Axis.two
  have hP : glMat ((w₁ * w₂ : antiSp K) : GL (Fin 4) K) =
      !![0, 0, 1, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 1, 0, 0] := by
    rw [glMat_coe_mul]
    exact weylMat_one_mul_two
  have hQ : glMat ((w₁ * w₂ * (w₁ * w₂) : antiSp K) : GL (Fin 4) K) =
      !![0, 0, 0, 1; 0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0] := by
    rw [glMat_coe_mul, hP]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]
  have e : (w₁ * w₂) ^ 4 = (w₁ * w₂ * (w₁ * w₂)) * (w₁ * w₂ * (w₁ * w₂)) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [e]
  refine antiSp_ext ?_
  rw [glMat_coe_mul, hQ]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_four]

theorem exists_root_trick_axis :
    ∃ i : Axis,
      antiUnipotent K = rootA K i.swap ⊔
        (rootA K i ⊓ (rootA K i.swap).map (MulAut.conj (weylElt K i)).toMonoidHom) ∧
      ∃ a ∈ rootA K i.swap ⊓ (rootA K i.swap).map
          (MulAut.conj (weylElt K i.swap * weylElt K i)).toMonoidHom,
        a * weylElt K i * a⁻¹ ∈ (rootA K i.swap).map (MulAut.conj (weylElt K i)).toMonoidHom ⊓
          (rootA K i.swap).map
            (MulAut.conj (weylElt K i * weylElt K i.swap * weylElt K i)).toMonoidHom := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine ⟨Axis.one, ?_, ?_⟩
  ·
    change antiUnipotent K = radA2 K ⊔ (radA1 K ⊓ (radA2 K).map
      (MulAut.conj (weylElt K Axis.one)).toMonoidHom)
    refine le_antisymm ?_
      (sup_le radA2_le_antiUnipotent (inf_le_left.trans radA1_le_antiUnipotent))
    rintro _ ⟨a, b, c, d, rfl⟩
    have e : uElt a b c d = uElt a (b + a * d) c 0 * uElt 0 0 0 d := by
      rw [uElt_mul]
      refine uElt_congr ?_ ?_ ?_ ?_
      · ring
      · linear_combination (-(a * d)) * h2
      · ring
      · ring
    have hconj : (weylElt K Axis.one)⁻¹ * uElt 0 0 0 d * weylElt K Axis.one = uElt 0 0 d 0 := by
      refine antiSp_ext ?_
      rw [weylElt_inv]
      simp only [glMat_coe_mul, glMat_weylElt, glMat_uElt]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [weylMat, uMat, Matrix.mul_apply, Fin.sum_univ_four]
    rw [e]
    refine mul_mem (Subgroup.mem_sup_left ⟨a, b + a * d, c, rfl⟩)
      (Subgroup.mem_sup_right ⟨⟨0, 0, d, rfl⟩, ?_⟩)
    refine mem_map_conj_iff_inv_mul_mul_mem.mpr ?_
    rw [hconj]
    exact ⟨0, 0, d, rfl⟩
  ·
    change ∃ a ∈ radA2 K ⊓ (radA2 K).map
        (MulAut.conj (weylElt K Axis.two * weylElt K Axis.one)).toMonoidHom,
      a * weylElt K Axis.one * a⁻¹ ∈ (radA2 K).map
          (MulAut.conj (weylElt K Axis.one)).toMonoidHom ⊓
        (radA2 K).map (MulAut.conj
          (weylElt K Axis.one * weylElt K Axis.two * weylElt K Axis.one)).toMonoidHom
    have ha_inv : (uElt 1 0 0 0 : antiSp K)⁻¹ = uElt 1 0 0 0 := by
      rw [uElt_inv]
      exact uElt_congr rfl (by ring) rfl rfl
    refine ⟨uElt 1 0 0 0, ⟨⟨1, 0, 0, rfl⟩, ?_⟩, ?_, ?_⟩
    ·
      refine mem_map_conj_iff_inv_mul_mul_mem.mpr ?_
      rw [mul_inv_rev, weylElt_inv, weylElt_inv]
      have h : weylElt K Axis.one * weylElt K Axis.two * uElt 1 0 0 0 *
          (weylElt K Axis.two * weylElt K Axis.one) = uElt 0 1 0 0 := by
        refine antiSp_ext ?_
        simp only [glMat_coe_mul, glMat_weylElt, glMat_uElt]
        rw [weylMat_one_mul_two, weylMat_two_mul_one]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]
      rw [h]
      exact ⟨0, 1, 0, rfl⟩
    ·
      refine mem_map_conj_iff_inv_mul_mul_mem.mpr ?_
      rw [ha_inv]
      have h : (weylElt K Axis.one)⁻¹ * (uElt 1 0 0 0 * weylElt K Axis.one * uElt 1 0 0 0) *
          weylElt K Axis.one = uElt 1 0 0 0 := by
        refine antiSp_ext ?_
        rw [weylElt_inv]
        simp only [glMat_coe_mul, glMat_weylElt, glMat_uElt]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [weylMat, uMat, Matrix.mul_apply, Fin.sum_univ_four, one_add_one_eq_two, h2]
      rw [h]
      exact ⟨1, 0, 0, rfl⟩
    ·
      refine mem_map_conj_iff_inv_mul_mul_mem.mpr ?_
      rw [ha_inv]
      have hinv : (weylElt K Axis.one * weylElt K Axis.two * weylElt K Axis.one)⁻¹ =
          weylElt K Axis.one * weylElt K Axis.two * weylElt K Axis.one := by
        rw [mul_inv_rev, mul_inv_rev, weylElt_inv, weylElt_inv, mul_assoc]
      have hL : uMat (1 : K) 0 0 0 * weylMat K Axis.one * uMat 1 0 0 0 =
          !![1, 0, 0, 0; 1, 1, 0, 0; 0, 0, 1, 0; 0, 0, 1, 1] := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [weylMat, uMat, Matrix.mul_apply, Fin.sum_univ_four, one_add_one_eq_two, h2]
      have h : (weylElt K Axis.one * weylElt K Axis.two * weylElt K Axis.one) *
          (uElt 1 0 0 0 * weylElt K Axis.one * uElt 1 0 0 0) *
          (weylElt K Axis.one * weylElt K Axis.two * weylElt K Axis.one) = uElt 0 1 0 0 := by
        refine antiSp_ext ?_
        simp only [glMat_coe_mul, glMat_weylElt, glMat_uElt]
        rw [weylMat_one_mul_two_mul_one, hL]
        ext i j
        fin_cases i <;> fin_cases j <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]
      rw [hinv, h]
      exact ⟨0, 1, 0, rfl⟩

end ProductModel

end CFSG.LocalAnalysis.EvenBN.Sp4
