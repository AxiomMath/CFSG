module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpOuter

public section

namespace CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain

variable {K : Type} [Field K] [CharP K 2]

private theorem gm1pB_frobHom_uElt (a b c d : K) :
    frobHom K (uElt a b c d) = uElt (a ^ 2) (b ^ 2) (c ^ 2) (d ^ 2) := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  refine antiSp_ext ?_
  rw [glMat_frobHom, glMat_uElt, glMat_uElt]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [uMat] <;> linear_combination (a * b * d) * h2

private theorem gm1pB_uElt_inj {a b c d a' b' c' d' : K}
    (h : uElt a b c d = uElt a' b' c' d') : a = a' ∧ b = b' ∧ c = c' ∧ d = d' :=
  uMat_inj (congrArg (fun x : antiSp K => glMat (x : GL (Fin 4) K)) h)

private theorem gm1pB_uElt_congr {a b c d a' b' c' d' : K} (h1 : a = a') (h2 : b = b')
    (h3 : c = c') (h4 : d = d') : uElt a b c d = uElt a' b' c' d' := by
  subst h1 h2 h3 h4
  rfl

private theorem gm1pB_one_eq : (1 : antiSp K) = uElt 0 0 0 0 :=
  antiSp_ext uMat_zero.symm

private theorem gm1pB_sq_eq_zero_or_one {s : K} (hs : s ^ 2 = s) : s = 0 ∨ s = 1 := by
  have hm : s * (s - 1) = 0 := by linear_combination hs
  rcases mul_eq_zero.mp hm with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private theorem gm1pB_pow_four [Finite K] (hK : Nat.card K = 4) (x : K) : x ^ 4 = x := by
  haveI : Fintype K := Fintype.ofFinite K
  have hc : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, hK]
  have h := FiniteField.pow_card x
  rwa [hc] at h

private theorem gm1pB_exists_ne_zero_one [Finite K] (hK : Nat.card K = 4) :
    ∃ y : K, y ≠ 0 ∧ y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hsurj : Function.Surjective (fun x : Fin 2 => if x = 0 then (0 : K) else 1) := by
    intro y
    by_cases hy : y = 0
    · exact ⟨0, by simp [hy]⟩
    · exact ⟨1, by simp [hcon y hy]⟩
  have hle := Nat.card_le_card_of_surjective _ hsurj
  have h2' : Nat.card (Fin 2) = 2 := by simp
  omega

private theorem gm1pB_exists_sq_add_self [Finite K] (hK : Nat.card K = 4) {s : K}
    (hs : s ^ 2 = s) : ∃ y : K, y ^ 2 + y = s := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rcases gm1pB_sq_eq_zero_or_one hs with rfl | rfl
  · exact ⟨0, by ring⟩
  · obtain ⟨y, hy0, hy1⟩ := gm1pB_exists_ne_zero_one hK
    have h3 : y ^ 3 = 1 := by
      have hm : y * (y ^ 3 - 1) = 0 := by linear_combination gm1pB_pow_four hK y
      rcases mul_eq_zero.mp hm with h | h
      · exact absurd h hy0
      · exact sub_eq_zero.mp h
    have hq : y ^ 2 + y + 1 = 0 := by
      have hm : (y - 1) * (y ^ 2 + y + 1) = 0 := by linear_combination h3
      rcases mul_eq_zero.mp hm with h | h
      · exact absurd (sub_eq_zero.mp h) hy1
      · exact h
    exact ⟨y, by linear_combination hq - h2⟩

private theorem gm1pB_card_fixed : Nat.card {x : K // x ^ 2 = x} = 2 := by
  refine Nat.card_eq_two_iff.mpr ⟨⟨0, by simp⟩, ⟨1, by simp⟩, ?_, ?_⟩
  · intro h
    exact zero_ne_one (congrArg Subtype.val h : (0 : K) = 1)
  · ext ⟨z, hz⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases gm1pB_sq_eq_zero_or_one hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl

private noncomputable def gm1pB_fixElt
    (p : {x : K // x ^ 2 = x} × {x : K // x ^ 2 = x} × {x : K // x ^ 2 = x} ×
      {x : K // x ^ 2 = x}) :
    ↥(antiUnipotent K ⊓ (frobHom K).eqLocus (MonoidHom.id (antiSp K))) :=
  ⟨uElt p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2.1, Subgroup.mem_inf.mpr ⟨uElt_mem_antiUnipotent _ _ _ _, by
    have ha : p.1.1 ^ 2 = p.1.1 := p.1.2
    have hb : p.2.1.1 ^ 2 = p.2.1.1 := p.2.1.2
    have hc : p.2.2.1.1 ^ 2 = p.2.2.1.1 := p.2.2.1.2
    have hd : p.2.2.2.1 ^ 2 = p.2.2.2.1 := p.2.2.2.2
    show frobHom K (uElt p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2.1) =
      uElt p.1.1 p.2.1.1 p.2.2.1.1 p.2.2.2.1
    rw [gm1pB_frobHom_uElt, ha, hb, hc, hd]⟩⟩

private theorem gm1pB_fixElt_bijective :
    Function.Bijective (gm1pB_fixElt (K := K)) := by
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩, ⟨d, hd⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩, ⟨c', hc'⟩, ⟨d', hd'⟩⟩ h
    have h' : uElt a b c d = uElt a' b' c' d' := congrArg Subtype.val h
    obtain ⟨rfl, rfl, rfl, rfl⟩ := gm1pB_uElt_inj h'
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨hxU, hxF⟩ := Subgroup.mem_inf.mp hx
    obtain ⟨a, b, c, d, rfl⟩ := hxU
    have hF : frobHom K (uElt a b c d) = uElt a b c d := hxF
    rw [gm1pB_frobHom_uElt] at hF
    obtain ⟨A, B, C, D⟩ := gm1pB_uElt_inj hF
    exact ⟨(⟨a, A⟩, ⟨b, B⟩, ⟨c, C⟩, ⟨d, D⟩), rfl⟩

theorem antiUnipotent_cocycle_four [Finite K] (hK : Nat.card K = 4) {u : antiSp K}
    (hu : u ∈ antiUnipotent K) (h : u * frobHom K u = 1) :
    ∃ v ∈ antiUnipotent K, u = v * (frobHom K v)⁻¹ := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  rw [gm1pB_frobHom_uElt, uElt_mul] at h
  obtain ⟨E1, E2, E3, E4⟩ := gm1pB_uElt_inj (h.trans gm1pB_one_eq)
  have A2 : a ^ 2 = a := by linear_combination E1 - a * h2
  have D2 : d ^ 2 = d := by linear_combination E4 - d * h2
  have B2 : b ^ 2 + b = a * d := by linear_combination E2 - a * E4
  have C2 : c ^ 2 + c = 0 := by
    linear_combination E3 - a * B2 - (b + a * d) * A2 - a ^ 3 * D2 - a ^ 2 * d * h2
  obtain ⟨δ, Hδ⟩ := gm1pB_exists_sq_add_self hK D2
  obtain ⟨α, Hα⟩ := gm1pB_exists_sq_add_self hK A2
  have F4 : δ ^ 4 = δ := gm1pB_pow_four hK δ
  have hs2 : (b + a * δ ^ 2) ^ 2 = b + a * δ ^ 2 := by
    linear_combination B2 + δ ^ 4 * A2 + a * F4 + a * Hδ
      + (a * b * δ ^ 2 - b - a * δ ^ 2 + a * d) * h2
  obtain ⟨β, Hβ⟩ := gm1pB_exists_sq_add_self hK hs2
  have hM : (α * (b + a * δ ^ 2) + a * β) ^ 2 = α * (b + a * δ ^ 2) + a * β := by
    linear_combination α ^ 2 * hs2 + β ^ 2 * A2 + (b + a * δ ^ 2) * Hα + a * Hβ
      + (-(α * (b + a * δ ^ 2)) + a * (b + a * δ ^ 2) - a * β
        + α * a * (b + a * δ ^ 2) * β) * h2
  have hγ : (c + (α * (b + a * δ ^ 2) + a * β)) ^ 2 = c + (α * (b + a * δ ^ 2) + a * β) := by
    linear_combination C2 + hM + (c * (α * (b + a * δ ^ 2) + a * β) - c) * h2
  obtain ⟨γ, Hγ⟩ := gm1pB_exists_sq_add_self hK hγ
  have hm : α * β ^ 2 + α ^ 2 * β = α * (b + a * δ ^ 2) + a * β := by
    linear_combination α * Hβ + β * Hα - α * β * h2
  refine ⟨uElt α β γ δ, uElt_mem_antiUnipotent _ _ _ _, ?_⟩
  rw [gm1pB_frobHom_uElt, uElt_inv, uElt_mul]
  refine gm1pB_uElt_congr ?_ ?_ ?_ ?_
  · linear_combination (-1 : K) * Hα
  · linear_combination (-1 : K) * Hβ - δ ^ 2 * Hα - a * δ ^ 2 * h2
  · linear_combination (-1 : K) * Hγ - hm - (α * (b + a * δ ^ 2) + a * β + α ^ 3 * δ ^ 2) * h2
  · linear_combination (-1 : K) * Hδ

theorem card_antiUnipotent_inf_fixed [Finite K] (hK : Nat.card K = 4) :
    Nat.card ↥(antiUnipotent K ⊓ (frobHom K).eqLocus (MonoidHom.id (antiSp K))) = 2 ^ 4 := by
  refine (Nat.card_congr (Equiv.ofBijective _ (gm1pB_fixElt_bijective (K := K)))).symm.trans ?_
  norm_num [Nat.card_prod, gm1pB_card_fixed]

end CFSG.LocalAnalysis.EvenBN.UnitaryFiveTwo.Gomi1P
