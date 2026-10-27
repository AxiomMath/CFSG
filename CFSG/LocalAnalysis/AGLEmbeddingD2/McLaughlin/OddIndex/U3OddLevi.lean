module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddEmb
public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OddIndex.U3OddNormalizer

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OddIndex

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime] [CharP F p]

section Z

variable (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)

include hp2 in
theorem odd_prime_pow : Odd (p ^ f) :=
  ((Fact.out : p.Prime).eq_two_or_odd'.resolve_left hp2).pow

omit [Finite F] in
include hp2 in
theorem two_ne_zero_of_char_ne_two : (2 : F) ≠ 0 := by
  intro h2
  have : p ∣ 2 := (CharP.cast_eq_zero_iff F p 2).1 (by exact_mod_cast h2)
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).1 this)

include hp2 in
theorem mat3_zSU : mat3 (zSU hF) = Matrix.diagonal ![(-1 : F), 1, -1] := by
  have hodd := odd_prime_pow (p := p) (f := f) hp2
  have heven : Even (p ^ f - 1) := by
    obtain ⟨m, hm⟩ := hodd
    exact ⟨m, by omega⟩
  show tMat (p ^ f) (-1 : Fˣ) = _
  unfold tMat
  rw [heven.neg_one_pow, hodd.neg_one_pow]
  simp

include hp2 in
theorem offblock_of_commute_zSU {x : SU (unitaryInvolution F p f) 3} (hx : x * zSU hF = zSU hF * x) :
    mat3 x 0 1 = 0 ∧ mat3 x 1 0 = 0 ∧ mat3 x 1 2 = 0 ∧ mat3 x 2 1 = 0 := by
  have hm : mat3 x * mat3 (zSU hF) = mat3 (zSU hF) * mat3 x := by
    rw [← mat3_mul, ← mat3_mul, hx]
  rw [mat3_zSU hF hp2] at hm
  have h2 := two_ne_zero_of_char_ne_two (F := F) hp2
  have key : ∀ i j : Fin 3, (![(-1 : F), 1, -1] j - ![(-1 : F), 1, -1] i) * mat3 x i j = 0 := by
    intro i j
    have := congrFun (congrFun hm i) j
    simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at this
    linear_combination this
  have k01 := key 0 1
  have k10 := key 1 0
  have k12 := key 1 2
  have k21 := key 2 1
  simp at k01 k10 k12 k21
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases k01 with h | h
    · exact absurd (by linear_combination h) h2
    · exact h
  · rcases k10 with h | h
    · exact absurd (by linear_combination -h) h2
    · exact h
  · rcases k12 with h | h
    · exact absurd (by linear_combination -h) h2
    · exact h
  · rcases k21 with h | h
    · exact absurd (by linear_combination h) h2
    · exact h

omit [CharP F p] in
include hF in
theorem exists_pow_sub_one_eq {u : Fˣ} (hu : u ^ (p ^ f + 1) = 1) :
    ∃ μ : Fˣ, μ ^ (p ^ f - 1) = u := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgo : orderOf g = (p ^ f) ^ 2 - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hF]
  obtain ⟨m, hm0⟩ := mem_powers_iff_mem_zpowers.2 (hg u)
  have hm : g ^ m = u := hm0
  have hq : 1 ≤ p ^ f := Nat.one_le_pow _ _ (Fact.out : p.Prime).pos
  obtain ⟨k, hk⟩ : ∃ k, p ^ f = k + 1 := ⟨p ^ f - 1, by omega⟩
  have hsq : (p ^ f) ^ 2 - 1 = (p ^ f - 1) * (p ^ f + 1) := by
    rw [hk, Nat.add_sub_cancel]
    have h : (k + 1) ^ 2 = k * (k + 1 + 1) + 1 := by ring
    omega
  have h1 : g ^ (m * (p ^ f + 1)) = 1 := by rw [pow_mul, hm, hu]
  have h2 : (p ^ f - 1) * (p ^ f + 1) ∣ m * (p ^ f + 1) := by
    rw [← hsq, ← hgo]
    exact orderOf_dvd_of_pow_eq_one h1
  have h3 : (p ^ f - 1) ∣ m := Nat.dvd_of_mul_dvd_mul_right (by omega) h2
  obtain ⟨j, rfl⟩ := h3
  exact ⟨g ^ j, by rw [← pow_mul, mul_comm, hm]⟩

theorem norm_mid_of_blockForm {x : SU (unitaryInvolution F p f) 3} (h01 : mat3 x 0 1 = 0)
    (h21 : mat3 x 2 1 = 0) : (mat3 x 1 1) ^ (p ^ f) * mat3 x 1 1 = 1 := by
  have h := x.2.2
  have e11 := congrFun (congrFun h 1) 1
  have h01' : (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) 0 1 = 0 := h01
  have h21' : (((x : GL (Fin 3) F)) : Matrix (Fin 3) (Fin 3) F) 2 1 = 0 := h21
  simp [conjTr, antidiag, Matrix.mul_apply, Fin.sum_univ_three, h01', h21'] at e11
  simp only [iterateFrobenius_def] at e11
  exact e11

theorem mat3_tSU (ν : Fˣ) :
    mat3 (tSU hF ν) = Matrix.diagonal ![(ν : F), ((ν ^ (p ^ f - 1) : Fˣ) : F),
      (((ν ^ (p ^ f))⁻¹ : Fˣ) : F)] := rfl

include hp2 in
theorem embSU_mul_zSU (M : SU (unitaryInvolution F p f) 2) :
    embSU (unitaryInvolution F p f) M * zSU hF = zSU hF * embSU (unitaryInvolution F p f) M := by
  apply mat3_injective
  rw [mat3_mul, mat3_mul, mat3_zSU hF hp2]
  show embMat _ * _ = _ * embMat _
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [embMat, Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tSU_mem_range_embSU_iff (μ : Fˣ) :
    tSU hF μ ∈ (embSU (unitaryInvolution F p f)).range ↔ μ ^ (p ^ f - 1) = 1 := by
  constructor
  · rintro ⟨M, hM⟩
    have := congrFun (congrFun (congrArg mat3 hM) 1) 1
    rw [mat3_tSU hF] at this
    simp only [mat3, coe_embSU, embMat] at this
    exact Units.ext (by rw [Units.val_pow_eq_pow_val]; simpa using this.symm)
  · intro h
    refine mem_range_embSU_of_blockForm ?_ ?_ ?_ ?_ ?_ <;> rw [mat3_tSU hF]
    · simp
    · simp
    · simp
    · simp
    · simp [h]

include hp2 in
theorem exists_levi_mul_torus_of_commute_zSU {x : SU (unitaryInvolution F p f) 3}
    (hx : x * zSU hF = zSU hF * x) :
    ∃ l ∈ (embSU (unitaryInvolution F p f)).range, ∃ t ∈ (tSU hF).range, x = l * t := by
  obtain ⟨h01, h10, h12, h21⟩ := offblock_of_commute_zSU hF hp2 hx
  have hnorm := norm_mid_of_blockForm h01 h21
  have he0 : mat3 x 1 1 ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hnorm
    exact zero_ne_one hnorm
  set u : Fˣ := Units.mk0 (mat3 x 1 1) he0 with hu
  have hu1 : u ^ (p ^ f + 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one, pow_succ, hnorm]
  obtain ⟨μ, hμ⟩ := exists_pow_sub_one_eq hF hu1
  refine ⟨x * (tSU hF μ)⁻¹, ?_, tSU hF μ, ⟨μ, rfl⟩, by rw [inv_mul_cancel_right]⟩
  have hinv : (tSU hF μ)⁻¹ = tSU hF μ⁻¹ := (map_inv (tSU hF) μ).symm
  apply mem_range_embSU_of_blockForm
  all_goals rw [mat3_mul, hinv, mat3_tSU hF]
  · simp [Matrix.mul_diagonal, h01]
  · simp [Matrix.mul_diagonal, h10]
  · simp [Matrix.mul_diagonal, h12]
  · simp [Matrix.mul_diagonal, h21]
  · have hm : (μ : F) ^ (p ^ f - 1) = mat3 x 1 1 := by
      have := congrArg (fun v : Fˣ => (v : F)) hμ
      simpa [hu] using this
    simp only [Matrix.mul_diagonal]
    simp [hm, he0]

include hp2 in
theorem mem_centralizer_zSU_iff (x : SU (unitaryInvolution F p f) 3) :
    x * zSU hF = zSU hF * x ↔
      ∃ l ∈ (embSU (unitaryInvolution F p f)).range, ∃ t ∈ (tSU hF).range, x = l * t := by
  constructor
  · exact exists_levi_mul_torus_of_commute_zSU hF hp2
  · rintro ⟨_, ⟨M, rfl⟩, _, ⟨μ, rfl⟩, rfl⟩
    have hT : tSU hF μ * zSU hF = zSU hF * tSU hF μ := by
      rw [zSU, ← map_mul, ← map_mul, mul_comm]
    rw [mul_assoc, hT, ← mul_assoc, embSU_mul_zSU hF hp2, mul_assoc]

include hp2 in
theorem centralizer_zSU :
    Subgroup.centralizer ({zSU hF} : Set (SU (unitaryInvolution F p f) 3)) =
      (embSU (unitaryInvolution F p f)).range ⊔ (tSU hF).range := by
  apply le_antisymm
  · intro x hx
    have hx' : x * zSU hF = zSU hF * x := (hx (zSU hF) rfl).symm
    obtain ⟨l, hl, t, ht, rfl⟩ := (mem_centralizer_zSU_iff hF hp2 x).1 hx'
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hl) (Subgroup.mem_sup_right ht)
  · refine sup_le ?_ ?_
    · rintro _ ⟨M, rfl⟩ g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact (embSU_mul_zSU hF hp2 M).symm
    · rintro _ ⟨μ, rfl⟩ g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      rw [zSU, ← map_mul, ← map_mul, mul_comm]

end Z

end CFSG.AGLEmbeddingD2.McLaughlin.OddIndex
