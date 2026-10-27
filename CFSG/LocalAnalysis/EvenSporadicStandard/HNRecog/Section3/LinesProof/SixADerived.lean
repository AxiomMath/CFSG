module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixABasic
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.LinesProof.SixAShape

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

variable {G : Type} [Group G] {a z : G}

private def lines_four_u (b t : G) : Fin 4 → G := ![1, b, t, t * b]

private lemma lines_four_u_inv_mul_mem {b t : G} (hb2 : b ^ 2 = 1) (ht2 : t ^ 2 = 1)
    (hbt : b * t = t * b) {i j : Fin 4} (hij : i ≠ j) :
    (lines_four_u b t j)⁻¹ * lines_four_u b t i ∈ ({b, t, t * b} : Set G) := by
  have hbi : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact hb2
  have hti : t⁻¹ = t := by rw [inv_eq_iff_mul_eq_one, ← pow_two]; exact ht2
  have htbi : (t * b)⁻¹ = t * b := by rw [mul_inv_rev, hbi, hti]; exact hbt
  have ht1 : t * (t * b) = b := by rw [← mul_assoc, ← pow_two, ht2, one_mul]
  have hb1 : b * (t * b) = t := by rw [← mul_assoc, hbt, mul_assoc, ← pow_two, hb2, mul_one]
  have htbb : t * b * b = t := by rw [mul_assoc, ← pow_two, hb2, mul_one]
  have htbt : t * b * t = b := by rw [mul_assoc, hbt, ← mul_assoc, ← pow_two, ht2, one_mul]
  fin_cases i <;> fin_cases j <;>
    simp_all [lines_four_u, hbi, hti, htbi, hbt, ht1, hb1, htbb, htbt, pow_two]

theorem lines_four_mul_card_le [Finite G] {K N : Subgroup G} {b t : G} (hb : b ∈ K) (ht : t ∈ K)
    (hb2 : b ^ 2 = 1) (ht2 : t ^ 2 = 1) (hbt : b * t = t * b) (hbN : b ∉ N) (htN : t ∉ N)
    (htbN : t * b ∉ N) : 4 * Nat.card ↥(K ⊓ N) ≤ Nat.card ↥K := by
  have hu : ∀ i : Fin 4, lines_four_u b t i ∈ K := by
    intro i
    fin_cases i
    · simpa [lines_four_u] using K.one_mem
    · simpa [lines_four_u] using hb
    · simpa [lines_four_u] using ht
    · simpa [lines_four_u] using K.mul_mem ht hb
  have hinj : Function.Injective (fun p : ↥(K ⊓ N) × Fin 4 =>
      (⟨lines_four_u b t p.2 * (p.1 : G),
        K.mul_mem (hu p.2) (Subgroup.mem_inf.mp p.1.2).1⟩ : ↥K)) := by
    rintro ⟨l, i⟩ ⟨l', j⟩ h
    have h1 : lines_four_u b t i * (l : G) = lines_four_u b t j * (l' : G) :=
      congrArg (fun x : ↥K => (x : G)) h
    have hmem : (lines_four_u b t j)⁻¹ * lines_four_u b t i ∈ N := by
      have h2 : (lines_four_u b t j)⁻¹ * lines_four_u b t i = (l' : G) * (l : G)⁻¹ := by
        calc (lines_four_u b t j)⁻¹ * lines_four_u b t i
            = (lines_four_u b t j)⁻¹ * (lines_four_u b t i * (l : G)) * (l : G)⁻¹ := by
              group
          _ = (lines_four_u b t j)⁻¹ * (lines_four_u b t j * (l' : G)) * (l : G)⁻¹ := by
              rw [h1]
          _ = (l' : G) * (l : G)⁻¹ := by group
      rw [h2]
      exact N.mul_mem (Subgroup.mem_inf.mp l'.2).2 (N.inv_mem (Subgroup.mem_inf.mp l.2).2)
    have hij : i = j := by
      by_contra hij
      have hset := lines_four_u_inv_mul_mem hb2 ht2 hbt hij
      rcases hset with h' | h' | h'
      · exact hbN (h' ▸ hmem)
      · exact htN (h' ▸ hmem)
      · exact htbN (h' ▸ hmem)
    subst hij
    exact Prod.ext (Subtype.ext (mul_left_cancel h1)) rfl
  have hcard := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, Nat.card_fin] at hcard
  rw [mul_comm]
  exact hcard

theorem lines_sixA_derived [Finite G] (h : IsF5Type a z) (hnc : ¬ IsConj a z)
    (hF3 : Fusion3Facts a z) (hPic : A8Pictures a z) (hT5 : TableVFacts a z)
    (h6A : SixAFacts a z) {x : G} (hx : x ∈ orb6A a a) :
    derivedOf (Gxy a x) = Gxy a x ⊓ derivedOf (Gxy a ((a * x) ^ 3)) := by
  obtain ⟨hb, hle, hX, hK⟩ := lines_sixA_setup h hF3 hT5 hx
  obtain ⟨t, htK, s, hs, ht2, hs2, ht_eq, _⟩ := lines_sixA_t h hnc hF3 hPic hT5 h6A hx
  have hbK : (a * x) ^ 3 ∈ Gxy a x := sixA_b_mem_Gxy_x h hx
  have hb2 : ((a * x) ^ 3) ^ 2 = 1 := sixA_b_sq h hx
  have hbt : (a * x) ^ 3 * t = t * (a * x) ^ 3 := (sixA_comm_b_of_mem htK).symm
  obtain ⟨haN, hbN, habN⟩ := lines_not_mem_derived h hnc (IsConj.refl a) hb hX hPic
  have hsH : s ∈ Gxy a ((a * x) ^ 3) := derivedOf_le _ hs
  have hsb : s * (a * x) ^ 3 = (a * x) ^ 3 * s :=
    (mem_Gx.mp (mem_Gxy.mp hsH).2).symm
  have hsinv : s⁻¹ ∈ derivedOf (Gxy a ((a * x) ^ 3)) :=
    (derivedOf (Gxy a ((a * x) ^ 3))).inv_mem hs
  have htN : t ∉ derivedOf (Gxy a ((a * x) ^ 3)) := by
    intro htmem
    have hts : t * s⁻¹ = a * (a * x) ^ 3 := by rw [ht_eq]; group
    have hm : t * s⁻¹ ∈ derivedOf (Gxy a ((a * x) ^ 3)) :=
      Subgroup.mul_mem _ htmem hsinv
    rw [hts] at hm
    exact habN hm
  have htbeq : t * (a * x) ^ 3 = a * s := by
    calc t * (a * x) ^ 3
        = a * ((a * x) ^ 3 * (s * (a * x) ^ 3)) := by rw [ht_eq]; group
      _ = a * ((a * x) ^ 3 * ((a * x) ^ 3 * s)) := by rw [hsb]
      _ = a * (((a * x) ^ 3 * (a * x) ^ 3) * s) := by group
      _ = a * s := by rw [← pow_two, hb2, one_mul]
  have htbN : t * (a * x) ^ 3 ∉ derivedOf (Gxy a ((a * x) ^ 3)) := by
    intro htbmem
    have htbs : t * (a * x) ^ 3 * s⁻¹ = a := by rw [htbeq]; group
    have hm : t * (a * x) ^ 3 * s⁻¹ ∈ derivedOf (Gxy a ((a * x) ^ 3)) :=
      Subgroup.mul_mem _ htbmem hsinv
    rw [htbs] at hm
    exact haN hm
  have h4 := lines_four_mul_card_le hbK htK hb2 ht2 hbt hbN htN htbN
  have hcardK : Nat.card ↥(Gxy a x) = 240 := lines_card_z2_sym5 hK
  rw [hcardK] at h4
  have hL60 : Nat.card ↥(Gxy a x ⊓ derivedOf (Gxy a ((a * x) ^ 3))) ≤ 60 := by omega
  have hcardD : Nat.card ↥(derivedOf (Gxy a x)) = 60 :=
    lines_card_a5 (lines_isShapeA5_derivedOf hK)
  refine Subgroup.eq_of_le_of_card_ge (le_inf (derivedOf_le _) (derivedOf_mono hle)) ?_
  rw [hcardD]
  exact hL60

end CFSG.EvenSporadicStandard.HNRecog.Section3
