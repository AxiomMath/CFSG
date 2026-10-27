module

public import CFSG.RankThree.Chevalley.SteinbergBID4A2CharCentralizer
public import CFSG.CGT.PushingUpLit.BHS.Prelim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K148Inner

open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley
open scoped Pointwise

theorem exists_units_pow_two_pow_eq {L : Type} [Field L] [IsAlgClosed L] (c : Lˣ) (k : ℕ) :
    ∃ c' : Lˣ, c' ^ (2 ^ k) = c := by
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (c : L) (pow_pos (by norm_num : (0 : ℕ) < 2) k)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (pow_ne_zero k (by norm_num : (2 : ℕ) ≠ 0))] at hz
    exact c.ne_zero hz.symm
  exact ⟨Units.mk0 z hz0, Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_mk0, hz])⟩

theorem torusGroup_eq_one_of_pow_two_pow {τ : Tag} {L : Type} [Field L] [CharP L 2]
    {h : ModGL τ L}
    (hh : h ∈ torusGroup τ L) {k : ℕ} (hk : h ^ (2 ^ k) = 1) : h = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨l, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have h1 : l ^ (2 ^ k) = 1 := by
    refine rootDiagUnit_injective (K := L) ?_
    rw [← rootDiagUnit_pow, hk, rootDiagUnit_one]
  have h2 : ∀ i, l i = 1 := by
    intro i
    have hi : ((l i : L)) ^ (2 ^ k) = 1 := by
      have h3 := congrFun h1 i
      simp only [Pi.pow_apply, Pi.one_apply] at h3
      simpa using congrArg Units.val h3
    have h4 : ((l i : L) - 1) ^ (2 ^ k) = 0 := by
      rw [sub_pow_char_pow, hi, one_pow, sub_self]
    have h5 : (l i : L) - 1 = 0 := by
      by_contra h0
      exact absurd h4 (pow_ne_zero _ h0)
    exact Units.ext (sub_eq_zero.1 h5)
  have hl : l = 1 := funext h2
  rw [hl, rootDiagUnit_one]

theorem d4A2TorusElt_pow {L : Type} [Field L]
    (t u : Lˣ) (n : ℕ) :
    CFSG.RankThree.Chevalley.d4A2TorusElt (K := L) t u ^ n =
      CFSG.RankThree.Chevalley.d4A2TorusElt (t ^ n) (u ^ n) := by
  induction n with
  | zero =>
    rw [pow_zero, pow_zero, pow_zero, CFSG.RankThree.Chevalley.d4A2TorusElt_one]
  | succ n ih =>
    rw [pow_succ, ih, CFSG.RankThree.Chevalley.d4A2TorusElt_mul, pow_succ, pow_succ]

theorem exists_two_pow_root_subsystemTorus_d4A2 {L : Type} [Field L] [IsAlgClosed L]
    {t : ModGL Tag.D4 L} (ht : t ∈ subsystemTorus Tag.D4 L CFSG.RankThree.Chevalley.d4SuppA2)
    (k : ℕ) :
    ∃ s ∈ subsystemTorus Tag.D4 L CFSG.RankThree.Chevalley.d4SuppA2, s ^ (2 ^ k) = t := by
  obtain ⟨t₁, t₂, rfl⟩ := (CFSG.RankThree.Chevalley.mem_subsystemTorus_d4A2).1 ht
  obtain ⟨t₁', ht₁⟩ := exists_units_pow_two_pow_eq t₁ k
  obtain ⟨t₂', ht₂⟩ := exists_units_pow_two_pow_eq t₂ k
  refine ⟨CFSG.RankThree.Chevalley.d4A2TorusElt t₁' t₂', ?_, ?_⟩
  · exact (CFSG.RankThree.Chevalley.mem_subsystemTorus_d4A2).2 ⟨t₁', t₂', rfl⟩
  · rw [d4A2TorusElt_pow, ht₁, ht₂]

theorem exists_two_pow_root_d4A2Tv {L : Type} [Field L] [IsAlgClosed L]
    (v : WeylGroup Tag.D4)
    {t : ModGL Tag.D4 L} (ht : t ∈ CFSG.RankThree.Chevalley.d4A2Tv L v) (k : ℕ) :
    ∃ s ∈ CFSG.RankThree.Chevalley.d4A2Tv L v, s ^ (2 ^ k) = t := by
  rw [CFSG.RankThree.Chevalley.d4A2Tv, Subgroup.mem_map] at ht
  obtain ⟨s, hs, rfl⟩ := ht
  obtain ⟨r, hr, hsr⟩ := exists_two_pow_root_subsystemTorus_d4A2 hs k
  refine ⟨canonicalRep (coxeterSystem Tag.D4) L v * r *
    (canonicalRep (coxeterSystem Tag.D4) L v)⁻¹, ?_, ?_⟩
  · rw [CFSG.RankThree.Chevalley.d4A2Tv, Subgroup.mem_map]
    exact ⟨r, hr, rfl⟩
  · rw [conj_pow, hsr]
    rfl

theorem mem_d4A2Qv_of_pow_two_pow {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {a : Fin Tag.D4.rank → Lˣ}
    (hord : orderOf (rootDiagUnit Tag.D4 a) = 3) {v : WeylGroup Tag.D4}
    (hSig : rootCharKernel a = (fun α => v • α) '' CFSG.RankThree.Chevalley.d4A2Sigma)
    {u : ModGL Tag.D4 L} (hu : u ∈ toralCentralizer Tag.D4 L a) {k : ℕ} (hpow : u ^ (2 ^ k) = 1) :
    u ∈ CFSG.RankThree.Chevalley.d4A2Qv L v := by
  have hpK : ringChar L ≠ 3 := by
    rw [ringChar.eq L 2]
    norm_num
  obtain ⟨-, hset, -, -, -, -, -, hinf, -⟩ :=
    CFSG.RankThree.Chevalley.D4_odd_prime_A2_root_character_centralizer L 3 Nat.prime_three
      (by norm_num) hpK a hord v hSig
  have hle := CFSG.RankThree.Chevalley.torusGroup_le_normalizer_d4A2Qv (K := L) v
  have hmem : u ∈ (torusGroup Tag.D4 L : Set (ModGL Tag.D4 L)) *
      (CFSG.RankThree.Chevalley.d4A2Qv L v : Set (ModGL Tag.D4 L)) := by
    rw [← hset]
    exact hu
  rw [Set.mem_mul] at hmem
  obtain ⟨h, hh, w, hw, rfl⟩ := hmem
  obtain ⟨w', hw', hpow'⟩ :=
    CFSG.CGT.PushingUpLit.BHS.pow_mul_mem_of_mem_normalizer (hle hh) hw (2 ^ k)
  have hQ : h ^ (2 ^ k) ∈ CFSG.RankThree.Chevalley.d4A2Qv L v := by
    have h1 : h ^ (2 ^ k) = w'⁻¹ := by
      rw [hpow'] at hpow
      rw [eq_inv_of_mul_eq_one_right hpow, inv_inv]
    rw [h1]
    exact inv_mem hw'
  have hT : h ^ (2 ^ k) ∈ CFSG.RankThree.Chevalley.d4A2Tv L v := by
    have hQT : h ^ (2 ^ k) ∈ (CFSG.RankThree.Chevalley.d4A2Qv L v ⊓ torusGroup Tag.D4 L :
        Subgroup (ModGL Tag.D4 L)) := ⟨hQ, pow_mem hh _⟩
    rwa [hinf] at hQT
  obtain ⟨s, hs, hsp⟩ := exists_two_pow_root_d4A2Tv v hT k
  have hs' : s ∈ (CFSG.RankThree.Chevalley.d4A2Qv L v ⊓ torusGroup Tag.D4 L :
      Subgroup (ModGL Tag.D4 L)) := hinf.symm ▸ hs
  have hcomm : Commute h s⁻¹ := torusGroup_mul_comm hh (inv_mem hs'.2)
  have h2 : (h * s⁻¹) ^ (2 ^ k) = 1 := by
    rw [hcomm.mul_pow, inv_pow, hsp, mul_inv_cancel]
  have h1 : h = s := by
    have h3 := torusGroup_eq_one_of_pow_two_pow (mul_mem hh (inv_mem hs'.2)) h2
    exact mul_inv_eq_one.1 h3
  rw [h1]
  exact mul_mem hs'.1 hw

end CFSG.LocalAnalysis.GLTheoremA.K148Inner

end
