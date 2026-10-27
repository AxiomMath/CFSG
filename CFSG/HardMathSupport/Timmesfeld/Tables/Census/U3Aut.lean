module

public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.T9
public import CFSG.RankThree.PartTwo.Sec4.Item413AutU3

public section

namespace CFSG.HardMathSupport.Timmesfeld.Tables.Census

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec4

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K}

theorem card_le_nine_of_mulAut_unitaryPSU [Finite K] (h3 : (3 : K) ≠ 0) (hq : 2 < p ^ f)
    (hf : ¬ 3 ∣ f) (B : Subgroup (MulAut (unitaryPSU h 3))) (hB : CFSG.Assembly.IsElemAbelian 3 B) :
    Nat.card B ≤ 9 := by
  have := h.finite
  set N := (psuConj h).range
  set C := (psuField h).range
  have hAut : Nat.card (RingAut K) = 2 * f := (card_ringAut_and_isCyclic h.prime K h.card).1
  have hCN : C ≤ Subgroup.normalizer (N : Set (MulAut (unitaryPSU h 3))) := by
    rintro _ ⟨σ, rfl⟩
    refine mem_normalizer_of_conj_mem fun x hx => ?_
    obtain ⟨A, rfl⟩ := hx
    exact ⟨_, (psuField_mul_psuConj_mul_inv σ A).symm⟩
  have hBNC : ∀ b ∈ B, ∃ n ∈ N, ∃ c ∈ C, b = n * c := by
    intro b _
    obtain ⟨A, σ, hAσ⟩ := exists_psuConj_mul_psuField hq b
    exact ⟨psuConj h A, ⟨A, rfl⟩, psuField h σ, ⟨σ, rfl⟩, hAσ⟩
  have hcop : Nat.Coprime 3 (2 * f) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 fun hd =>
      (Nat.Prime.dvd_mul Nat.prime_three).1 hd |>.elim (by omega) hf
  have hBN : ∀ b ∈ B, b ∈ N := by
    intro b hb
    obtain ⟨n, hn, c, hc, rfl⟩ := hBNC b hb
    have hb3 : (n * c) ^ 3 = 1 := hB.2 _ hb
    have hconj : ∀ m ∈ N, c * m * c⁻¹ ∈ N := fun m hm =>
      (Subgroup.mem_normalizer_iff.1 (hCN hc) m).1 hm
    have hc3 : c ^ 3 ∈ N := by
      have h0 : n * (c * n * c⁻¹) * (c * (c * n * c⁻¹) * c⁻¹) * c ^ 3 = (n * c) ^ 3 := by
        simp only [pow_succ, pow_zero, one_mul]
        group
      have h1 : c ^ 3 = (n * (c * n * c⁻¹) * (c * (c * n * c⁻¹) * c⁻¹))⁻¹ :=
        eq_inv_of_mul_eq_one_right (h0.trans hb3)
      rw [h1]
      exact N.inv_mem (N.mul_mem (N.mul_mem hn (hconj n hn)) (hconj _ (hconj n hn)))
    have hc2f : c ^ (2 * f) = 1 := by
      obtain ⟨σ, rfl⟩ := hc
      have hσ : σ ^ (2 * f) = 1 := by
        have := pow_card_eq_one' (G := RingAut K) (x := σ)
        rwa [hAut] at this
      rw [← map_pow, hσ, map_one]
    obtain ⟨k, -, hk⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by have := h.one_le; omega)
    have hck : c = (c ^ 3) ^ k := by
      have h3k : c ^ (3 * k) = c :=
        calc c ^ (3 * k) = c ^ (2 * f * (3 * k / (2 * f)) + 3 * k % (2 * f)) := by
              rw [Nat.div_add_mod]
          _ = c := by rw [pow_add, pow_mul, hc2f, one_pow, one_mul, hk, pow_one]
      rw [← pow_mul]
      exact h3k.symm
    exact N.mul_mem hn (hck ▸ N.pow_mem hc3 k)
  set ψ : unitaryIsom3 h →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.mk' _).comp (unitaryIsom3 h).subtype
  have hk : (psuConj h).ker = ψ.ker := by
    ext A
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, psuConj_eq_one_iff]
    change _ ↔ QuotientGroup.mk' _ (A : GL (Fin 3) K) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  set χ : N →* GL (Fin 3) K ⧸ CFSG.Assembly.LowTwoRank.StatedScalars (Fin 3) K :=
    (QuotientGroup.kerLift ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).toMonoidHom.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.toMonoidHom)
  have hχ : Function.Injective χ :=
    (QuotientGroup.kerLift_injective ψ).comp ((QuotientGroup.quotientMulEquivOfEq hk).injective.comp
      (QuotientGroup.quotientKerEquivRange (psuConj h)).symm.injective)
  set E := ((B ⊓ N).subgroupOf N).map χ
  have hcardE : Nat.card E = Nat.card (B ⊓ N : Subgroup _) := by
    rw [Subgroup.card_map_of_injective hχ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hB.1.1.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h9 : Nat.card (B ⊓ N : Subgroup _) ≤ 9 := by
    rw [← hcardE]
    refine card_le_nine_of_pgl3 h3 E ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact hBc _ (Subgroup.mem_subgroupOf.mp hx).1 _ (Subgroup.mem_subgroupOf.mp hy).1
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have : x ^ 3 = 1 := Subtype.ext (by
        rw [Subgroup.coe_pow, Subgroup.coe_one]
        exact hB.2 _ (Subgroup.mem_subgroupOf.mp hx).1)
      rw [this, map_one]
  rwa [inf_eq_left.2 fun b hb => hBN b hb] at h9

theorem u3AutRankLeTwo_holds : U3AutRankLeTwo := by
  intro G _ _ hG
  obtain ⟨n, hn, h3n, hn1, -, K, _, _, hcard, ⟨e⟩⟩ := hG
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hcard, ← pow_mul, mul_comm]⟩
  have h3 : (3 : K) ≠ 0 := three_ne_zero_of_card Nat.prime_two (by norm_num) hU.card
  have hq : 2 < 2 ^ n := lt_of_lt_of_le (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) (show 2 ≤ n by omega))
  let e' : G ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm
  refine csSup_le' ?_
  rintro r ⟨E, -, hE, hcardE⟩
  have hB := card_le_nine_of_mulAut_unitaryPSU h3 hq h3n
    (E.map (MulAut.congr e').toMonoidHom) (isElemAbelian_map _ hE)
  rw [Subgroup.card_map_of_injective (MulAut.congr e').injective, hcardE,
    show (9 : ℕ) = 3 ^ 2 by norm_num] at hB
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp hB

end CFSG.HardMathSupport.Timmesfeld.Tables.Census
