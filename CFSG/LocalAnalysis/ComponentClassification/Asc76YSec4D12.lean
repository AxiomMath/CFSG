module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D11
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D9

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem exists_conj_eq_mul_of_isDihedral {T V : Subgroup G} (hV : IsDihedralRot V T) {z : G}
    (hzT : z ∉ T) (hzz : z * z = 1) (hD : IsDihedralTwoGroup (zpowers z ⊔ T))
    (hinv : ∀ v ∈ V, z * v * z⁻¹ = v⁻¹) {u : G} (hu : u ∈ V) :
    ∃ c : G, c⁻¹ * z * c = z * u := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D : Subgroup G := zpowers z ⊔ T with hDdef
  have hTD : T ≤ D := le_sup_right
  have hDnc : ¬ IsMulCommutative D := by
    intro hcomm
    apply hV.not_isMulCommutative
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    have := hcomm.is_comm.comm ⟨a, hTD a.2⟩ ⟨b, hTD b.2⟩
    simpa using congrArg Subtype.val this
  obtain ⟨C, hC⟩ := exists_isDihedralRot hD hDnc
  obtain ⟨ρ, hρ, hρo⟩ := hV.exists_gen
  have hρV : ρ ∈ V := hρ ▸ mem_zpowers ρ
  have hρC : ρ ∈ C :=
    hC.mem_of_mul_self_ne_one (hTD (hV.le hρV)) (hV.gen_mul_self_ne_one hρo)
  have hVC : V ≤ C := by
    rw [← hρ]
    exact (zpowers_le).mpr hρC
  have hzD : z ∈ D := mem_sup_left (mem_zpowers z)
  have hz1 : z ≠ 1 := fun h => hzT (h ▸ T.one_mem)
  have hzC : z ∉ C := by
    intro hzC
    obtain ⟨zC, -, -, -, hzCuniq, -⟩ := hC.exists_involution
    obtain ⟨t, htV, ht1, htt, -, -⟩ := hV.exists_involution
    have e1 := (hzCuniq z hzC hzz).resolve_left hz1
    have e2 := (hzCuniq t (hVC htV) htt).resolve_left ht1
    exact hzT (by rw [e1, ← e2]; exact hV.le htV)
  have hCV : C ≠ V := by
    intro hCV
    have h1 := hC.card_eq
    have h2 := hV.card_eq
    rw [hCV] at h1
    have hTeq : T = D := eq_of_le_of_card_ge hTD (by rw [h1, h2])
    exact hzT (hTeq ▸ hzD)
  obtain ⟨a, ha⟩ := (hV.isPGroup.to_le hV.le).exists_card_eq
  obtain ⟨b, hb⟩ := (hC.isPGroup.to_le hC.le).exists_card_eq
  have hab : a < b := by
    have hdvd : Nat.card V ∣ Nat.card C := card_dvd_of_le hVC
    rw [ha, hb] at hdvd
    have hle : a ≤ b := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
    rcases hle.lt_or_eq with h | h
    · exact h
    · exfalso
      apply hCV
      exact (eq_of_le_of_card_ge hVC (by rw [ha, hb, h])).symm
  have huV : u ^ Nat.card V = 1 := by
    have h1 : (⟨u, hu⟩ : V) ^ Nat.card V = 1 := pow_card_eq_one'
    have h2 := congrArg Subtype.val h1
    rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
  have hpow : u ^ (Nat.card C / 2) = 1 := by
    obtain ⟨k, rfl⟩ : ∃ k, b = a + 1 + k := ⟨b - (a + 1), by omega⟩
    have e : Nat.card C / 2 = Nat.card V * 2 ^ k := by
      rw [hb, ha, pow_add, pow_add, pow_one]
      have : 2 ^ a * 2 * 2 ^ k = 2 * (2 ^ a * 2 ^ k) := by ring
      rw [this, Nat.mul_div_cancel_left _ (by norm_num)]
    rw [e, pow_mul, huV, one_pow]
  obtain ⟨c, hcC, hcu⟩ := hC.exists_sq_of_pow_half_eq_one (hVC hu) hpow
  refine ⟨c, ?_⟩
  have h1 : z * c * z⁻¹ = c⁻¹ := hC.conj_eq z hzD hzC c hcC
  have h2 : z * u * z⁻¹ = u⁻¹ := hinv u hu
  calc c⁻¹ * z * c = c⁻¹ * (z * c * z⁻¹) * z := by group
    _ = (c * c)⁻¹ * z := by rw [h1]; group
    _ = u⁻¹ * z := by rw [hcu]
    _ = (z * u * z⁻¹) * z := by rw [h2]
    _ = z * u := by group

theorem conj_inv_mem_of_forall_conj_mem {A : Set G} {g : G}
    (h : ∀ p ∈ A, g * p * g⁻¹ ∈ A) : ∀ p ∈ A, g⁻¹ * p * g ∈ A := by
  have hk : ∀ k : ℕ, ∀ p ∈ A, g ^ k * p * (g ^ k)⁻¹ ∈ A := by
    intro k
    induction k with
    | zero => intro p hp; simpa using hp
    | succ k ih =>
      intro p hp
      have := h _ (ih p hp)
      have e : g * (g ^ k * p * (g ^ k)⁻¹) * g⁻¹ = g ^ (k + 1) * p * (g ^ (k + 1))⁻¹ := by
        rw [pow_succ']
        group
      rwa [e] at this
  intro p hp
  have hm := pow_orderOf_eq_one g
  obtain ⟨m, hm'⟩ : ∃ m, orderOf g = m + 1 := ⟨orderOf g - 1, by have := orderOf_pos g; omega⟩
  rw [hm', pow_succ] at hm
  have e : g ^ m = g⁻¹ := eq_inv_of_mul_eq_one_left hm
  have := hk m p hp
  rwa [e, inv_inv] at this

theorem mul_mem_sec4W_of_inv (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {g : G} (hinv : ∀ x ∈ sec4W Ω S, IsZInv Ω x →
      ∀ w ∈ AschbacherTightEmbedding.rightConjugate (sec4W Ω S) g, x * w * x⁻¹ = w⁻¹)
    {t t' : G} (ht : t ∈ AschbacherTightEmbedding.rightConjugate (sec4W Ω S) g)
    (htZ : IsZInv Ω t) (ht' : t' ∈ AschbacherTightEmbedding.rightConjugate (sec4W Ω S) g)
    (ht'Z : IsZInv Ω t') : t * t' ∈ sec4W Ω S := by
  set W := sec4W Ω S with hWdef
  set W' := AschbacherTightEmbedding.rightConjugate W g with hW'def
  set A : Set G := {p | ∃ x y : G, x ∈ W ∧ IsZInv Ω x ∧ y ∈ W ∧ IsZInv Ω y ∧ p = x * y}
    with hAdef
  have hAW : ∀ p ∈ A, p ∈ W := by
    rintro p ⟨x, y, hx, -, hy, -, rfl⟩
    exact mul_mem hx hy
  have hA : ∀ p ∈ A, ∀ w ∈ W, p * w = w * p := fun p hp w hw =>
    sec4W_mul_comm hΩ hS (hAW p hp) hw
  have hAW' : ∀ p ∈ A, ∀ w ∈ W', p * w = w * p := by
    rintro p ⟨x, y, hx, hxZ, hy, hyZ, rfl⟩ w hw
    have h1 : y * w * y⁻¹ = w⁻¹ := hinv y hy hyZ w hw
    have h2 : x * w⁻¹ * x⁻¹ = w := by
      have := hinv x hx hxZ w hw
      calc x * w⁻¹ * x⁻¹ = (x * w * x⁻¹)⁻¹ := by group
        _ = w := by rw [this, inv_inv]
    calc x * y * w = x * (y * w * y⁻¹) * x⁻¹ * (x * y) := by group
      _ = x * w⁻¹ * x⁻¹ * (x * y) := by rw [h1]
      _ = w * (x * y) := by rw [h2]
  have hAh : ∀ p ∈ A, ∀ w ∈ W, (g⁻¹⁻¹ * p * g⁻¹) * w = w * (g⁻¹⁻¹ * p * g⁻¹) := by
    intro p hp w hw
    have hw' : g⁻¹ * w * g ∈ W' := conj_mem_rightConjugate hw g
    have h1 := hAW' p hp _ hw'
    rw [inv_inv]
    calc g * p * g⁻¹ * w = g * (p * (g⁻¹ * w * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * w * g) * p) * g⁻¹ := by rw [h1]
      _ = w * (g * p * g⁻¹) := by group
  obtain ⟨n, hnW, hn⟩ := exists_mem_normalizer_conj_eq hΩ hS hA hAh
  have hAn : ∀ p ∈ A, n⁻¹ * p * n ∈ A := by
    rintro p ⟨x, y, hx, hxZ, hy, hyZ, rfl⟩
    have hconjW : ∀ x ∈ W, n⁻¹ * x * n ∈ W := fun x hx => by
      have := (mem_normalizer_iff.mp (inv_mem hnW) x).mp hx
      simpa using this
    refine ⟨n⁻¹ * x * n, n⁻¹ * y * n, hconjW x hx, hxZ.conj hΩ n, hconjW y hy, hyZ.conj hΩ n, ?_⟩
    group
  have hgA : ∀ p ∈ A, g * p * g⁻¹ ∈ A := by
    intro p hp
    have := hn p hp
    rw [inv_inv] at this
    rw [this]
    exact hAn p hp
  have hginv := conj_inv_mem_of_forall_conj_mem hgA
  have hx : g * t * g⁻¹ ∈ W := by
    rw [hW'def, mem_rightConjugate_iff] at ht
    exact ht
  have hx' : g * t' * g⁻¹ ∈ W := by
    rw [hW'def, mem_rightConjugate_iff] at ht'
    exact ht'
  have hxZ : IsZInv Ω (g * t * g⁻¹) := by
    have := htZ.conj hΩ g⁻¹
    rwa [inv_inv] at this
  have hx'Z : IsZInv Ω (g * t' * g⁻¹) := by
    have := ht'Z.conj hΩ g⁻¹
    rwa [inv_inv] at this
  have hp : (g * t * g⁻¹) * (g * t' * g⁻¹) ∈ A := ⟨_, _, hx, hxZ, hx', hx'Z, rfl⟩
  have := hAW _ (hginv _ hp)
  have e : g⁻¹ * ((g * t * g⁻¹) * (g * t' * g⁻¹)) * g = t * t' := by group
  rwa [e] at this

end CFSG.ComponentClassification.Asc76.Sec4
