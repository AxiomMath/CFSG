module

public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
import CFSG.FeitThompson.Definitions.AlphaPrimesOfAFiniteGroup
import CFSG.FeitThompson.Local.PrimeTorsionExponentRankTwo
import CFSG.FeitThompson.Local.PrimeCubeTorsionCentralizerCyclic
import CFSG.FeitThompson.Local.SmallTorsionMetacyclic
import CFSG.FeitThompson.Local.PrimeCubeOddScalarObstruction
import CFSG.FeitThompson.Local.NondefiningOddPrimesBelowDefining
import CFSG.FeitThompson.Local.InvariantCyclicComplementCommutatorPlane
import CFSG.FeitThompson.Local.MetacyclicCoprimeActionAbelian
import CFSG.FeitThompson.Local.PCubeCentralTrivialActionInner
import CFSG.FeitThompson.Local.ExponentPrimeRankTwoOrderCube
import CFSG.FeitThompson.Local.NoncentralTorsionCubeCommutatorPlane

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

open Subgroup
open scoped commutatorElement Pointwise

variable {p : ℕ} {R : Type*} [Group R] {A : Type*} [Group A]

theorem elementaryAbelianPRank_le_two_iff [Finite R] (hp : 1 < p) :
    elementaryAbelianPRank p R ≤ 2 ↔ 3 ∉ elementaryAbelianRanks p R := by
  rw [← le_elementaryAbelianPRank_iff hp]
  omega

omit [Group A] in
private theorem not_dvd_card_of_coprime (hp : p.Prime) (hAcop : (Nat.card A).Coprime p) :
    ¬ p ∣ Nat.card A := fun h => hp.one_lt.ne' <| Nat.dvd_one.mp <| by
  rw [← show Nat.gcd (Nat.card A) p = 1 from hAcop]
  exact Nat.dvd_gcd h dvd_rfl

omit [Group A] in
private theorem coprime_card_of_coprime_prime [Finite R] (hp : p.Prime) (hR : IsPGroup p R)
    (hAcop : (Nat.card A).Coprime p) : (Nat.card A).Coprime (Nat.card R) := by
  have := Fact.mk hp
  obtain ⟨n, hn⟩ := hR.exists_card_eq
  rw [hn]
  exact hAcop.pow_right n

private theorem displacement_set_comm (ρ : A →* MulAut R) :
    {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y}
      = {g : R | ∃ (a : A) (r : R), r⁻¹ * ρ a r = g} :=
  Set.ext fun _ => ⟨fun ⟨x, a, h⟩ => ⟨a, x, h⟩, fun ⟨a, x, h⟩ => ⟨x, a, h⟩⟩

theorem three_lt_of_closure_displacement_eq_top [Finite R] [Finite A] [Nontrivial R]
    (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R)
    (hrank : elementaryAbelianPRank p R ≤ 2)
    (hAodd : Odd (Nat.card A)) (hAcop : (Nat.card A).Coprime p) (ρ : A →* MulAut R)
    (hgen : closure {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = ⊤) : 3 < p := by
  have hrange : ρ.range ≠ ⊥ := by
    intro h
    have h1 : ∀ a : A, ρ a = 1 := fun a => Subgroup.mem_bot.mp (h ▸ (⟨a, rfl⟩ : ρ a ∈ ρ.range))
    have hset : {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = {1} := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      exact ⟨fun ⟨x, a, hx⟩ => by rw [← hx, h1 a]; simp, fun h => ⟨1, 1, by simp [h]⟩⟩
    rw [hset, Subgroup.closure_singleton_one] at hgen
    exact absurd hgen bot_ne_top
  have hcarddvd : Nat.card ρ.range ∣ Nat.card A := Subgroup.card_range_dvd ρ
  have hrangeodd : Odd (Nat.card ρ.range) := hAodd.of_dvd_nat hcarddvd
  obtain ⟨q, hq, hqdvd⟩ :=
    Nat.exists_prime_and_dvd (fun h => hrange (Subgroup.card_eq_one.mp h))
  have hqodd : Odd q := hrangeodd.of_dvd_nat hqdvd
  have hqp : q ≠ p := by
    rintro rfl
    exact not_dvd_card_of_coprime hq hAcop (hqdvd.trans hcarddvd)
  have hqlt : q < p :=
    prime_lt_of_dvd_card_of_odd_of_elementaryAbelianPRank_le_two hp hodd hR hrank hrangeodd hq
      hqp hqdvd
  have hq2 : q ≠ 2 := by
    rintro rfl
    simp [Nat.odd_iff] at hqodd
  have := hq.two_le
  omega

theorem card_omega1_eq_prime_cube [Finite R] [Finite A] (hp : p.Prime) (hp3 : 3 < p)
    (hR : IsPGroup p R) (hrank : elementaryAbelianPRank p R ≤ 2)
    (hnab : ¬ IsMulCommutative R) (hcop : (Nat.card A).Coprime (Nat.card R))
    (ρ : A →* MulAut R)
    (hgen : closure {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = ⊤) :
    Nat.card ↥(omega1 p R) = p ^ 3 := by
  have := Fact.mk hp
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  have hexp : ∀ b ∈ omega1 p R, b ^ p = 1 := fun b hb =>
    pow_eq_one_of_mem_omega1_of_elementaryAbelianPRank_le_two hp hp3 hR hrank hb
  have hrankB : elementaryAbelianPRank p ↥(omega1 p R) ≤ 2 :=
    le_trans (elementaryAbelianPRank_subgroup_le hp.one_lt _) hrank
  have hub : Nat.card ↥(omega1 p R) ≤ p ^ 3 :=
    card_le_pow_three_of_elementaryAbelianPRank_le_two hp hrankB
      (fun b => Subtype.ext (by push_cast; exact hexp _ b.2))
  obtain ⟨k, hk⟩ := (hR.to_subgroup (omega1 p R)).exists_card_eq
  have hk3 : k ≤ 3 := by
    rw [hk] at hub
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 hub
  have hkne : ¬ k ≤ 2 := by
    intro hk2
    have hle : Nat.card ↥(omega1 p R) ≤ p ^ 2 := by
      rw [hk]; exact Nat.pow_le_pow_right hp.pos hk2
    exact hnab (isMulCommutative_of_isMetacyclic_of_coprime hp hodd hR
      (isMetacyclic_of_natCard_omega1_le_sq hp hp3 hR hle) hcop ρ hgen)
  rw [hk, show k = 3 by omega]

theorem not_isMulCommutative_omega1 [Finite R] (hp : p.Prime)
    (h3 : 3 ∉ elementaryAbelianRanks p R) (hexp : ∀ b ∈ omega1 p R, b ^ p = 1)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) : ¬ IsMulCommutative ↥(omega1 p R) := by
  intro hab
  have := hab
  let _ : CommGroup ↥(omega1 p R) := IsMulCommutative.instCommGroup
  exact h3 (mem_elementaryAbelianRanks.2 ⟨omega1 p R, nonempty_mulEquiv_pi_of_exponent hp
    (fun b => Subtype.ext (by push_cast; exact hexp _ b.2)) hB⟩)

theorem commutator_top_omega1_le_map_center [Finite R] [Finite A] (hp : p.Prime) (hodd : Odd p)
    (hR : IsPGroup p R) (hB : Nat.card ↥(omega1 p R) = p ^ 3)
    (hnab : ¬ IsMulCommutative ↥(omega1 p R)) (hexp : ∀ b ∈ omega1 p R, b ^ p = 1)
    (hAodd : Odd (Nat.card A)) (hAp : ¬ p ∣ Nat.card A) (ρ : A →* MulAut R)
    (hgen : closure {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = ⊤) :
    ⁅(⊤ : Subgroup R), omega1 p R⁆ ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype := by
  by_contra hZ
  obtain ⟨X, hXinv, hXcyc, hXD, -, -, -, hBX, hBinfX⟩ :=
    exists_invariant_isCyclic_complement_commutator_plane hp hodd hR hB hnab hexp hZ ρ hAp
  exact not_isInvariantSubgroup_of_closure_displacement_eq_top hp hodd
    (B := omega1 p R) (Z := (center ↥(omega1 p R)).map (omega1 p R).subtype)
    (T := ⁅(⊤ : Subgroup R), omega1 p R⁆) (X := X)
    hB hnab hexp (inf_centralizer_omega1_eq_map_center p R).symm rfl
    (card_commutator_top_omega1 hp hR hB hnab hZ)
    (map_center_le_commutator_top_omega1 hp hB hnab)
    (commutator_top_commutator_top_omega1_le hp hR hB hnab hZ)
    hXD hXcyc hBX hBinfX hAodd ρ hXinv (by rw [← displacement_set_comm ρ]; exact hgen)

theorem centralizer_omega1_le_center (hp : p.Prime)
    (hB : Nat.card ↥(omega1 p R) = p ^ 3) (hnab : ¬ IsMulCommutative ↥(omega1 p R))
    (hcyc : IsCyclic ↥(centralizer (omega1 p R : Set R)))
    (hBR : ⁅omega1 p R, (⊤ : Subgroup R)⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype) :
    centralizer (omega1 p R : Set R) ≤ center R := by
  have := hcyc
  have hCab : IsMulCommutative ↥(centralizer (omega1 p R : Set R)) :=
    IsCyclic.isMulCommutative
  intro c hc
  rw [mem_center_iff]
  intro r
  obtain ⟨b, hb, c', hc', rfl⟩ := exists_mem_mul_mem_centralizer hp hB hnab hBR r
  have h1 : b * c = c * b := mem_centralizer_iff.mp hc b hb
  have h2 : c * c' = c' * c := setLike_mul_comm hc hc'
  calc b * c' * c = b * (c' * c) := by rw [mul_assoc]
    _ = b * (c * c') := by rw [h2]
    _ = b * c * c' := by rw [mul_assoc]
    _ = c * b * c' := by rw [h1]
    _ = c * (b * c') := by rw [mul_assoc]

theorem three_lt_and_exists_central_product [Finite R] [Finite A]
    (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R) (hnab : ¬ IsMulCommutative R)
    (h3 : 3 ∉ elementaryAbelianRanks p R)
    (hAodd : Odd (Nat.card A)) (hAcop : (Nat.card A).Coprime p) (ρ : A →* MulAut R)
    (hgen : closure {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = ⊤) :
    3 < p ∧ ∃ B C : Subgroup R,
      B ⊔ C = ⊤ ∧
      ¬ IsMulCommutative ↥B ∧ Nat.card ↥B = p ^ 3 ∧ (∀ b ∈ B, b ^ p = 1) ∧
      Nontrivial ↥C ∧ IsCyclic ↥C ∧ C ≤ center R ∧
      B ⊓ C = (center ↥B).map B.subtype ∧
      ((center ↥B).map B.subtype : Set R) = {c ∈ (C : Set R) | c ^ p = 1} ∧
      Nat.card ↥((center ↥B).map B.subtype) = p := by
  have hntR : Nontrivial R := by
    rcases subsingleton_or_nontrivial R with h | h
    · exact absurd (IsMulCommutative.of_comm fun a b => Subsingleton.elim _ _) hnab
    · exact h
  have hrank : elementaryAbelianPRank p R ≤ 2 := (elementaryAbelianPRank_le_two_iff hp.one_lt).2 h3
  have hAp : ¬ p ∣ Nat.card A := not_dvd_card_of_coprime hp hAcop
  have hp3 : 3 < p := three_lt_of_closure_displacement_eq_top hp hodd hR hrank hAodd hAcop ρ hgen
  have hexp : ∀ b ∈ omega1 p R, b ^ p = 1 := fun b hb =>
    pow_eq_one_of_mem_omega1_of_elementaryAbelianPRank_le_two hp hp3 hR hrank hb
  have hB : Nat.card ↥(omega1 p R) = p ^ 3 := card_omega1_eq_prime_cube hp hp3 hR hrank hnab
    (coprime_card_of_coprime_prime hp hR hAcop) ρ hgen
  have hBnab : ¬ IsMulCommutative ↥(omega1 p R) := not_isMulCommutative_omega1 hp h3 hexp hB
  have hBR : ⁅omega1 p R, (⊤ : Subgroup R)⁆
      ≤ (center ↥(omega1 p R)).map (omega1 p R).subtype := by
    rw [Subgroup.commutator_comm]
    exact commutator_top_omega1_le_map_center hp hodd hR hB hBnab hexp hAodd hAp ρ hgen
  have hcyc : IsCyclic ↥(centralizer (omega1 p R : Set R)) :=
    isCyclic_centralizer_omega1 hp hodd hR hB hBnab
  exact ⟨hp3, omega1 p R, centralizer (omega1 p R : Set R),
    sup_centralizer_eq_top hp hB hBnab hBR, hBnab, hB, hexp,
    nontrivial_centralizer_omega1 hp hB hBnab, hcyc,
    centralizer_omega1_le_center hp hB hBnab hcyc hBR,
    inf_centralizer_omega1_eq_map_center p R,
    (coe_pTorsion_centralizer_omega1 hexp).symm, card_map_center_omega1 hp hB hBnab⟩

theorem three_lt_and_exists_central_product_mul [Finite R] [Finite A]
    (hp : p.Prime) (hodd : Odd p) (hR : IsPGroup p R) (hnab : ¬ IsMulCommutative R)
    (h3 : 3 ∉ elementaryAbelianRanks p R)
    (hAodd : Odd (Nat.card A)) (hAcop : (Nat.card A).Coprime p) (ρ : A →* MulAut R)
    (hgen : closure {y : R | ∃ (x : R) (a : A), x⁻¹ * ρ a x = y} = ⊤) :
    3 < p ∧ ∃ B C : Subgroup R,
      (B : Set R) * (C : Set R) = Set.univ ∧
      ¬ IsMulCommutative ↥B ∧ Nat.card ↥B = p ^ 3 ∧ (∀ b ∈ B, b ^ p = 1) ∧
      Nontrivial ↥C ∧ IsCyclic ↥C ∧ C ≤ center R ∧
      B ⊓ C = (center ↥B).map B.subtype ∧
      ((center ↥B).map B.subtype : Set R) = {c ∈ (C : Set R) | c ^ p = 1} ∧
      Nat.card ↥((center ↥B).map B.subtype) = p := by
  obtain ⟨hp3, B, C, hBC, hBnab, hBcard, hBexp, hCnt, hCcyc, hCZ, hBinfC, hZtors, hZcard⟩ :=
    three_lt_and_exists_central_product hp hodd hR hnab h3 hAodd hAcop ρ hgen
  have : C.Normal :=
    ⟨fun x hx g => by rw [Subgroup.mem_center_iff.mp (hCZ hx) g]; simpa using hx⟩
  exact ⟨hp3, B, C, by rw [← Subgroup.mul_normal, hBC, Subgroup.coe_top], hBnab, hBcard, hBexp,
    hCnt, hCcyc, hCZ, hBinfC, hZtors, hZcard⟩

end

end CFSG.FeitThompson
