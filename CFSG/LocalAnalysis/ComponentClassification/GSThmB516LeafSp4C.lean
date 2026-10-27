module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81X10SpTwo
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB516LeafOrd
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.ComponentClassification.GSThmB.Pump516

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open SymplecticHigher SymplecticFlag CatFactsSp4 X10Sp4

variable {K : Type} [Field K]

theorem psp4_fixed_cases [Finite K] {p f' : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hf' : 1 ≤ f')
    (hK : Nat.card K = p ^ f') (h5 : 5 ≤ p ^ f') {α : MulAut (StatedProj (StatedSp 2 K))}
    (hα2 : α * α = 1) (hα1 : α ≠ 1) {M : Subgroup (StatedProj (StatedSp 2 K))}
    (hMX : M ≤ fixOf α) (hM : IsPComponent 2 (M.subgroupOf (fixOf α))) :
    (pPrimeCore 2 ↥M = ⊥ ∧ Nat.card M = p ^ f' * ((p ^ f') ^ 2 - 1)) ∨
      (IsSimpleGroup M ∧ Nat.card M * 2 = p ^ f' * ((p ^ f') ^ 2 - 1)) ∨
      (IsSimpleGroup M ∧ Nat.card M * 2 = (p ^ f') ^ 2 * (((p ^ f') ^ 2) ^ 2 - 1)) ∨
      (IsSimpleGroup M ∧ ∃ k : ℕ, k ^ 2 = p ^ f' ∧
        Nat.card M * 2 = k ^ 4 * ((k ^ 2 - 1) * (k ^ 4 - 1))) := by
  have hodd : Odd (Nat.card K) := odd_card_of_card_eq hp hp2 hK
  have h2 := two_ne_zero_of_odd_card hodd
  obtain ⟨A, σ, hα, hσ2, ⟨d, hd⟩, -, hfield⟩ :=
    (CatalogueBSymplecticRepresentation.odd_symplectic_automorphism_semilinear_representation
      (GH74.Generic.ringChar_ne_two_of_card_eq hp hp2 hK) le_rfl).2.2 α hα2 hα1
  rw [hα] at hMX hM hα1
  by_cases hσ : σ = 1
  · subst hσ
    rw [map_one, mul_one] at hMX hM hα1
    rcases inner_cases hp hp2 hf' hK h5 A d (mul_self_of_rep A d hd) hα1 hMX hM with
      he | h1 | h1
    · obtain ⟨e⟩ := he
      refine Or.inl ⟨?_, ?_⟩
      · rw [← pPrimeCore_map_iso 2 e.symm, pPrimeCore_SL2 h2 (by omega), Subgroup.map_bot]
      · rw [Nat.card_congr e.toEquiv, card_SL2, hK]
    · exact Or.inr (Or.inl ⟨h1.2.1, by rw [h1.2.2, card_SL2, hK]⟩)
    · exact Or.inr (Or.inr (Or.inl h1))
  · obtain ⟨hs, hc⟩ := field_card hodd A σ hσ2 hσ d hd hMX hM
    obtain ⟨hKk, -⟩ := hfield hσ
    have hk : Nat.card {c : K // σ c = c} =
        Nat.card (CatalogueBLinearTwoDescent.fixedSubfield K σ) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun c =>
        (CatalogueBLinearTwoDescent.mem_fixedSubfield K σ c).symm)
    rw [hk, hK] at hKk
    exact Or.inr (Or.inr (Or.inr ⟨hs, _, hKk.symm, hc⟩))

theorem card_psl2_mul_two {X : Type} [Group X] {p e : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : Blueprint.LieModel X .PSL 2 p e) : Nat.card X * 2 = p ^ e * ((p ^ e) ^ 2 - 1) :=
  CFSG.Open.StatedAPI.card_mul_two_of_statedClassicalModel_psl_two_odd hp hp2 (h.statedClassicalModel (by decide))

theorem pPrimeCore_eq_bot_of_simple {M : Type} [Group M] [IsSimpleGroup M]
    (h : Nontrivial (M ⧸ pPrimeCore 2 M)) : pPrimeCore 2 M = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (IsSimpleGroup.eq_bot_or_eq_top_of_normal (pPrimeCore 2 M)).resolve_right fun ht => ?_
  obtain ⟨x, y, hxy⟩ := h
  apply hxy
  induction x using QuotientGroup.induction_on with | H x => ?_
  induction y using QuotientGroup.induction_on with | H y => ?_
  rw [QuotientGroup.eq]
  rw [ht]
  exact mem_top _

theorem not_dvd_mul_sub_one {p Q c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hQ : p ∣ Q)
    (hQ1 : 1 ≤ Q) (hc : c = 1 ∨ c = 2) : ¬ p ∣ c * (Q - 1) := by
  intro hd
  rcases (Nat.Prime.dvd_mul hp).mp hd with hd | hd
  · rcases hc with rfl | rfl
    · exact hp.one_lt.ne' (Nat.dvd_one.mp hd)
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hd)
  · exact not_dvd_sub_one hp hQ hQ1 hd

theorem eq_of_sl_card {p a b c : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hc : c = 1 ∨ c = 2) (h : c * (p ^ a * ((p ^ a) ^ 2 - 1)) = p ^ b * ((p ^ b) ^ 2 - 1)) :
    a = b ∧ c = 1 := by
  have hpa : p ∣ (p ^ a) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
  have hpb : p ∣ (p ^ b) ^ 2 := dvd_pow (dvd_pow_self p (by omega)) two_ne_zero
  have h1a : 1 ≤ (p ^ a) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos a)
  have h1b : 1 ≤ (p ^ b) ^ 2 := Nat.one_le_pow _ _ (pow_pos hp.pos b)
  have h' : p ^ a * (c * ((p ^ a) ^ 2 - 1)) = p ^ b * (1 * ((p ^ b) ^ 2 - 1)) := by
    rw [one_mul, ← h]
    ring
  obtain ⟨rfl, hAB⟩ := eq_of_pow_mul_eq hp (not_dvd_mul_sub_one hp hp2 hpa h1a hc)
    (not_dvd_mul_sub_one hp hp2 hpb h1b (Or.inl rfl)) h'
  refine ⟨rfl, ?_⟩
  have h9 : 4 ≤ (p ^ a) ^ 2 := by
    have : 2 ≤ p ^ a := hp.two_le.trans (Nat.le_self_pow (by omega) p)
    nlinarith
  rcases hc with rfl | rfl
  · rfl
  · omega

theorem two_mul_pow_four_add_one_lt {q : ℕ} (hq : 3 ≤ q) :
    2 * (q ^ 4 + 1) < q ^ 2 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := by
  have h2 : 9 ≤ q ^ 2 := by nlinarith
  have h3 : 27 ≤ q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h4 : q ^ 4 = q ^ 2 * q ^ 2 := by ring
  have hA : 2 * q ^ 2 + 2 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) := by
    have : (q ^ 2 - 1) * 4 ≤ (q ^ 2 - 1) * (q ^ 3 - 1) :=
      Nat.mul_le_mul_left _ (by omega)
    omega
  calc 2 * (q ^ 4 + 1) < q ^ 2 * (2 * q ^ 2 + 2) := by rw [h4]; nlinarith
    _ ≤ q ^ 2 * ((q ^ 2 - 1) * (q ^ 3 - 1)) := Nat.mul_le_mul_left _ hA

theorem two_mul_psp4_sq_lt {q : ℕ} (hq : 3 ≤ q) :
    2 * ((q ^ 2) ^ 2 * (((q ^ 2) ^ 2) ^ 2 - 1)) <
      q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ (by omega)
  have e1 : ((q ^ 2) ^ 2) ^ 2 - 1 = (q ^ 4 - 1) * (q ^ 4 + 1) := by
    have h := Nat.sq_sub_sq (q ^ 4) 1
    rw [one_pow] at h
    rw [show ((q ^ 2) ^ 2) ^ 2 = (q ^ 4) ^ 2 by ring, h, mul_comm]
  have hB : 0 < q ^ 4 * (q ^ 4 - 1) := Nat.mul_pos (by positivity) (by
    have : 81 ≤ q ^ 4 := by
      calc 81 = 3 ^ 4 := by norm_num
        _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
    omega)
  have key := two_mul_pow_four_add_one_lt hq
  calc 2 * ((q ^ 2) ^ 2 * (((q ^ 2) ^ 2) ^ 2 - 1))
      = q ^ 4 * (q ^ 4 - 1) * (2 * (q ^ 4 + 1)) := by rw [e1]; ring
    _ < q ^ 4 * (q ^ 4 - 1) * (q ^ 2 * ((q ^ 2 - 1) * (q ^ 3 - 1))) :=
        Nat.mul_lt_mul_of_pos_left key hB
    _ = q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by ring

theorem two_mul_psp4_lt {q : ℕ} (hq : 3 ≤ q) :
    2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1))) <
      q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by
  have h2 : 9 ≤ q ^ 2 := by nlinarith
  have h3 : 27 ≤ q ^ 3 := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hq 3
  have h81 : 81 ≤ q ^ 4 := by
    calc 81 = 3 ^ 4 := by norm_num
      _ ≤ q ^ 4 := Nat.pow_le_pow_left hq 4
  have hB : 0 < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) :=
    Nat.mul_pos (by positivity) (Nat.mul_pos (by omega) (by omega))
  have hk : 2 < q ^ 2 * (q ^ 3 - 1) :=
    lt_of_lt_of_le (by norm_num : 2 < 9 * 26) (Nat.mul_le_mul h2 (by omega))
  calc 2 * (q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)))
      = q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) * 2 := by ring
    _ < q ^ 4 * ((q ^ 2 - 1) * (q ^ 4 - 1)) * (q ^ 2 * (q ^ 3 - 1)) :=
        Nat.mul_lt_mul_of_pos_left hk hB
    _ = q ^ 6 * (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by ring

theorem l4u4_card_lower {X : Type} [Group X] {p f : ℕ} (hp2 : p ≠ 2)
    (hX : (p ^ f % 4 = 3 ∧ Blueprint.LieModel X .PSL 4 p f) ∨
      (p ^ f % 4 = 1 ∧ Blueprint.LieModel X .PSU 4 p f)) :
    (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1) ≤
      Nat.card X * 4 := by
  rcases hX with ⟨-, hX⟩ | ⟨-, hX⟩
  · rw [← card_psl4 hp2 hX]
    exact Nat.mul_le_mul_left _ (Nat.gcd_le_left _ (by norm_num))
  · have h := card_psu4 hp2 hX
    calc (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 - 1) * ((p ^ f) ^ 4 - 1)
        ≤ (p ^ f) ^ 6 * ((p ^ f) ^ 2 - 1) * ((p ^ f) ^ 3 + 1) * ((p ^ f) ^ 4 - 1) := by
          gcongr
          omega
      _ = Nat.card X * Nat.gcd 4 (p ^ f + 1) := h.symm
      _ ≤ Nat.card X * 4 := Nat.mul_le_mul_left _ (Nat.gcd_le_left _ (by norm_num))

end CFSG.ComponentClassification.GSThmB.Pump516
