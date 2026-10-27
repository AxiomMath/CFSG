module

public import CFSG.Blueprint.Catalog
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ElementaryAbelian
public import CFSG.Open.BenderStronglyEmbeddedMilestoneDefs
import CFSG.ClassicalGroups.Unitary.Simple
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.StronglyEmbedded.BenderBorelTransport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Adapters.LieModelSimple
import CFSG.CGT.Timmesfeld75.L2Pair
import CFSG.CGT.Timmesfeld75.ListWCBasic
import CFSG.ClassicalGroups
import CFSG.LieType.BorelTits.CompleteFlag
import CFSG.StronglyEmbedded.ParityCriterion
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK

open CFSG.Blueprint CFSG.Assembly.LowTwoRank

section Generic

variable {Y : Type*} [Group Y]

theorem exists_four_of_fusionBenderBorel [Finite Y] {q k : ℕ}
    (hB : CFSG.Open.fusionBenderBorel Y q k) (hq : 4 ∣ q) :
    ∃ E : Subgroup Y, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 Y))
  obtain ⟨-, -, hsq, hZ, -⟩ := hB Q
  set Z := Subgroup.center (Q : Subgroup Y)
  obtain ⟨E, hE⟩ := Sylow.exists_subgroup_card_pow_prime (G := Z) 2 (n := 2)
    (by rw [hZ]; simpa using hq)
  set f : Z →* Y := (Q : Subgroup Y).subtype.comp Z.subtype
  have hf : Function.Injective f :=
    (Q : Subgroup Y).subtype_injective.comp Z.subtype_injective
  have : CFSG.IsElementaryAbelian 2 E :=
    { is_comm := ⟨fun x y => Subtype.ext (Subtype.ext
        (Subgroup.mem_center_iff.mp (y : Z).2 ((x : Z) : Q)))⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (Subtype.ext (hsq (x : Z) (x : Z).2)) }
  exact ⟨E.map f, CFSG.IsElementaryAbelian.map f, by
    rw [Subgroup.card_map_of_injective hf, hE]; norm_num⟩

theorem factorization_two_card_of_fusionBenderBorel [Finite Y] {n k : ℕ}
    (hB : CFSG.Open.fusionBenderBorel Y (2 ^ n) k) : (Nat.card Y).factorization 2 = n * k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow 2 Y))
  have h := (hB Q).2.2.2.2
  rw [Sylow.card_eq_multiplicity, ← pow_mul] at h
  exact Nat.pow_right_injective le_rfl h

theorem exists_mul_ne_of_four_dvd_card [IsSimpleGroup Y] (h4 : 4 ∣ Nat.card Y) :
    ∃ a b : Y, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  let _ : CommGroup Y := { (inferInstance : Group Y) with mul_comm := hc }
  have hp : (Nat.card Y).Prime := IsSimpleGroup.prime_card
  have h2 := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 (dvd_trans (by norm_num) h4)
  rw [← h2] at h4
  norm_num at h4

end Generic

section Arithmetic

theorem unitaryThree_oddPart_eq (m : ℕ) :
    ((m + 1) ^ 3 + 1) * ((m + 1) ^ 2 - 1) = (m + 2) ^ 2 * (m * (m ^ 2 + m + 1)) := by
  have h : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    omega
  rw [h]
  ring

theorem three_dvd_of_unitaryThree_order {N m : ℕ} (hm3 : ¬ 3 ∣ m + 1)
    (hN : N * Nat.gcd 3 (m + 2) = (m + 1) ^ 3 * ((m + 2) ^ 2 * (m * (m ^ 2 + m + 1)))) :
    3 ∣ N := by
  by_cases h3 : 3 ∣ m + 2
  · obtain ⟨k, hk⟩ := h3
    rw [Nat.gcd_eq_left ⟨k, hk⟩, hk] at hN
    have e : N * 3 = 3 * (3 * (k ^ 2 * ((m + 1) ^ 3 * (m * (m ^ 2 + m + 1))))) := by
      rw [hN]
      ring
    generalize k ^ 2 * ((m + 1) ^ 3 * (m * (m ^ 2 + m + 1))) = t at e
    exact ⟨t, by omega⟩
  · rw [((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3).gcd_eq_one, mul_one] at hN
    have hm : 3 ∣ m := by omega
    rw [hN]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (dvd_mul_of_dvd_left hm _) _) _

end Arithmetic

section Unitary

variable {X : Type} [Group X] {n : ℕ}

theorem statedClassicalModel_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    StatedClassicalModel X .PSU 3 2 n :=
  CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)

theorem two_le_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) : 2 ≤ n := by
  obtain ⟨⟨-, hf, -, hne⟩, -⟩ := statedClassicalModel_of_lieModel_PSU3 h
  by_contra hlt
  obtain rfl : n = 1 := by omega
  exact hne rfl

theorem finite_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) : Finite X := by
  obtain ⟨-, K, _, _, -, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_PSU3 h
  exact Finite.of_equiv _ e.symm.toEquiv

theorem exists_mulEquiv_psu3_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    Nonempty (X ≃* CFSG.Open.PSU3 2 n) := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_PSU3 h
  have hcard : Nat.card K = 2 ^ (2 * n) := by rw [hK, ← pow_mul, mul_comm]
  let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) K (2 ^ n)) := e
  exact ⟨e'.trans
    (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n (two_le_of_lieModel_PSU3 h) hcard)⟩

theorem isSimpleGroup_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) : IsSimpleGroup X :=
  CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h

theorem fusionBenderBorel_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    CFSG.Open.fusionBenderBorel X (2 ^ n) 3 := by
  have := finite_of_lieModel_PSU3 h
  obtain ⟨e⟩ := exists_mulEquiv_psu3_of_lieModel_PSU3 h
  have : Finite (CFSG.Open.PSU3 2 n) := Finite.of_equiv X e.toEquiv
  exact (CFSG.Open.bender_psu3_borel_full n (two_le_of_lieModel_PSU3 h)).map_mulEquiv e.symm

theorem exists_four_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    ∃ E : Subgroup X, CFSG.IsElementaryAbelian 2 E ∧ Nat.card E = 4 := by
  have := finite_of_lieModel_PSU3 h
  exact exists_four_of_fusionBenderBorel (fusionBenderBorel_of_lieModel_PSU3 h)
    (pow_dvd_pow 2 (two_le_of_lieModel_PSU3 h) : 2 ^ 2 ∣ 2 ^ n)

theorem exists_mul_ne_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    ∃ a b : X, a * b ≠ b * a := by
  have := isSimpleGroup_of_lieModel_PSU3 h
  obtain ⟨E, -, hE4⟩ := exists_four_of_lieModel_PSU3 h
  exact exists_mul_ne_of_four_dvd_card (hE4 ▸ Subgroup.card_subgroup_dvd_card E)

theorem card_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    Nat.card X =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 - 1) / Nat.gcd 3 (2 ^ n + 1) := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_PSU3 h
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
    Nat.prime_two hf hK (by norm_num), show Finset.Icc 2 3 = {2, 3} by decide,
    Finset.prod_pair (by norm_num)]
  have h2 : (((2 ^ n : ℕ) : ℤ) ^ 2 - (-1) ^ 2).toNat = (2 ^ n) ^ 2 - 1 := by
    have : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    rw [show ((2 ^ n : ℕ) : ℤ) ^ 2 - (-1) ^ 2 = (((2 ^ n) ^ 2 - 1 : ℕ) : ℤ) by
      push_cast [Nat.cast_sub this]
      ring]
    exact Int.toNat_natCast _
  have h3 : (((2 ^ n : ℕ) : ℤ) ^ 3 - (-1) ^ 3).toNat = (2 ^ n) ^ 3 + 1 := by
    rw [show ((2 ^ n : ℕ) : ℤ) ^ 3 - (-1) ^ 3 = (((2 ^ n) ^ 3 + 1 : ℕ) : ℤ) by
      push_cast
      ring]
    exact Int.toNat_natCast _
  rw [h2, h3, mul_comm ((2 ^ n) ^ 2 - 1), ← mul_assoc]

theorem card_eq_ordTwistedA_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    Nat.card X = CFSG.Open.ordTwistedA 2 (2 ^ n) := by
  obtain ⟨⟨-, hf, -⟩, K, _, _, hK, ⟨e⟩⟩ := statedClassicalModel_of_lieModel_PSU3 h
  rw [Nat.card_congr e.toEquiv, CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU
    Nat.prime_two hf hK (by norm_num)]
  rfl

theorem card_mul_gcd_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    Nat.card X * Nat.gcd 3 (2 ^ n + 1) =
      (2 ^ n) ^ 3 * ((2 ^ n) ^ 3 + 1) * ((2 ^ n) ^ 2 - 1) := by
  rw [card_of_lieModel_PSU3 h]
  refine Nat.div_mul_cancel ?_
  have h1 : 2 ^ n + 1 ∣ (2 ^ n) ^ 3 + 1 := by
    simpa using Odd.nat_add_dvd_pow_add_pow (2 ^ n) 1 (by decide : Odd 3)
  exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right ((Nat.gcd_dvd_right _ _).trans h1) _) _

theorem exists_card_mul_gcd_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    ∃ m : ℕ, 2 ^ n = m + 1 ∧ Odd m ∧
      Nat.card X * Nat.gcd 3 (m + 2) = (m + 1) ^ 3 * ((m + 2) ^ 2 * (m * (m ^ 2 + m + 1))) := by
  have hn := two_le_of_lieModel_PSU3 h
  obtain ⟨m, hm⟩ : ∃ m, 2 ^ n = m + 1 := ⟨2 ^ n - 1, by have := Nat.one_le_two_pow (n := n); omega⟩
  have h2 : 2 ∣ m + 1 := hm ▸ dvd_pow_self 2 (by omega)
  have hN := card_mul_gcd_of_lieModel_PSU3 h
  rw [hm, mul_assoc, unitaryThree_oddPart_eq, show m + 1 + 1 = m + 2 by omega] at hN
  exact ⟨m, hm, Nat.odd_iff.2 (by omega), hN⟩

theorem factorization_two_card_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) :
    (Nat.card X).factorization 2 = 3 * n := by
  have := finite_of_lieModel_PSU3 h
  rw [factorization_two_card_of_fusionBenderBorel (fusionBenderBorel_of_lieModel_PSU3 h),
    mul_comm]

theorem three_dvd_card_of_lieModel_PSU3 (h : LieModel X .PSU 3 2 n) : 3 ∣ Nat.card X := by
  obtain ⟨m, hm, -, hN⟩ := exists_card_mul_gcd_of_lieModel_PSU3 h
  refine three_dvd_of_unitaryThree_order (fun h3 => ?_) hN
  rw [← hm] at h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

end Unitary

end CFSG.LocalAnalysis.EvenBN.GMSK
