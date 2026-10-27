module

public import CFSG.RankThree.PartOne.KGD.D4QFrame

public section

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley.TrialityFold

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4Minus_h90_root {L : Type} [Field L] [IsAlgClosed L] (q : ℕ) {c : Lˣ}
    (hc : c * (c ^ q)⁻¹ * c ^ (q * q) = 1) :
    ∃ c₁ : Lˣ, c₁ ^ (q + 1) = c⁻¹ ∧ c₁ ^ (q ^ 3 + 1) = 1 := by
  obtain ⟨r, hr⟩ : ∃ r, q * q = q + r := ⟨q * q - q, by have := Nat.le_mul_self q; omega⟩
  have hcr : c ^ (r + 1) = 1 := by
    rw [hr, pow_add, mul_assoc, inv_mul_cancel_left] at hc
    rw [pow_succ']
    exact hc
  have hqr : q ^ 3 + 1 = (q + 1) * (r + 1) := by
    have h3 : q ^ 3 = q * (q * q) := by ring
    rw [h3, hr]
    nlinarith [hr]
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq ((c⁻¹ : Lˣ) : L) (Nat.succ_pos q)
  have hz0 : z ≠ 0 := by
    rintro rfl
    rw [zero_pow (Nat.succ_ne_zero q)] at hz
    exact (c⁻¹).ne_zero hz.symm
  have hc₁ : (Units.mk0 z hz0) ^ (q + 1) = c⁻¹ := Units.ext (by simpa using hz)
  refine ⟨Units.mk0 z hz0, hc₁, ?_⟩
  rw [hqr, pow_mul, hc₁, inv_pow, hcr, inv_one]

theorem d4Minus_h90_coord_one {L : Type} [Field L] (q : ℕ) {c₁ : Lˣ} :
    (c₁ ^ q)⁻¹ * (((c₁ ^ (q + 1))⁻¹ ^ q)⁻¹) * (c₁ ^ (q * q))⁻¹ = 1 := by
  group

theorem d4Minus_h90_coord_three {L : Type} [Field L] (q : ℕ) {c₁ : Lˣ} :
    c₁ ^ (q * q) * ((c₁ ^ (q + 1))⁻¹ ^ (q * q)) * c₁⁻¹ = (c₁ ^ (q ^ 3 + 1))⁻¹ := by
  rw [show q ^ 3 = q * q * q by ring]
  group

theorem d4Minus_h90_tuple_pow {L : Type} [Field L] {b : Lˣ} {n : ℕ} (hb : b ^ n = 1) :
    d4Tuple 1 1 b 1 ^ n = (1 : Fin TwistTag.D4.tag.rank → Lˣ) := by
  funext i
  rcases fin_cases i with rfl | rfl | rfl | rfl
  · exact one_pow n
  · exact one_pow n
  · exact hb
  · exact one_pow n

theorem d4Minus_s0_pow3 {L : Type} [Field L] {b : Lˣ} (hb : b ^ 3 = 1) :
    rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] ^ 3 = 1 := by
  have h : (rootDiagUnitHom TwistTag.D4.tag L) (d4Tuple 1 1 b 1) ^ 3 = 1 := by
    rw [← map_pow, d4Minus_h90_tuple_pow hb, map_one]
  exact h

end CFSG.GH74.GLS.Stage2.Bender.Thm1

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4Minus_h90_conj {L : Type} [Field L] (a : Fin TwistTag.D4.tag.rank → Lˣ) :
    (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag a * diagramMap TwistTag.D4 L =
      rootDiagUnit TwistTag.D4.tag (fun i => a (TwistTag.D4.perm i)) := by
  have h := diagramMap_mul_rootDiagUnit (K := L) (t := TwistTag.D4)
    (fun i => a (TwistTag.D4.perm i))
  simp only [Equiv.apply_symm_apply] at h
  rw [mul_assoc, ← h, inv_mul_cancel_left]

theorem d4Minus_s0_comm {L : Type} [Field L] (b : Lˣ) :
    (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] *
      diagramMap TwistTag.D4 L = rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] := by
  have h : (diagramMap TwistTag.D4 L)⁻¹ * rootDiagUnit TwistTag.D4.tag (d4Tuple 1 1 b 1) *
      diagramMap TwistTag.D4 L = rootDiagUnit TwistTag.D4.tag (d4Tuple 1 1 b 1) := by
    rw [d4Minus_h90_conj]
    congr 1
    funext i
    rcases fin_cases i with rfl | rfl | rfl | rfl
    · rw [perm_i0]; rfl
    · rw [perm_i1]; rfl
    · rw [perm_i2]
    · rw [perm_i3]; rfl
  exact h

end CFSG.GH74.GLS.Stage2.Bender.Thm1


namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

theorem d4Minus_s0_mem {L : Type} [Field L] [IsAlgClosed L] {q : ℕ}
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ q) {b : Lˣ} (hb : b ^ (q + 1) = 1) :
    rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] ∈
      twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr) := by
  rw [d4Q_twistedTorus Fr]
  refine ⟨d4QTuple q b 1, d4QTuple_mem hFr hb (one_pow _), ?_⟩
  have h : d4QTuple q b 1 = d4Tuple 1 1 b 1 := by simp [d4QTuple]
  rw [h]
  rfl

theorem d4Minus_torus_h1 {L : Type} [Field L] [IsAlgClosed L] {ℓ q : ℕ} [CharP L ℓ] (hℓq : ℓ ∣ q)
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ q) {t : ModGL TwistTag.D4.tag L}
    (ht : t ∈ twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr))
    (hcoc : t * ((diagramMap TwistTag.D4 L)⁻¹ * t * diagramMap TwistTag.D4 L) *
      ((diagramMap TwistTag.D4 L)⁻¹ * ((diagramMap TwistTag.D4 L)⁻¹ * t *
        diagramMap TwistTag.D4 L) * diagramMap TwistTag.D4 L) = 1) :
    ∃ e ∈ twistedTorusOf (trialityOpposition L) (twistHom TwistTag.D4 L Fr), ∃ b : Lˣ,
      b ^ 3 = 1 ∧ b ^ (q + 1) = 1 ∧
      e * t * ((diagramMap TwistTag.D4 L)⁻¹ * e * diagramMap TwistTag.D4 L)⁻¹ =
        rootDiagUnit TwistTag.D4.tag ![1, 1, b, 1] := by
  have _ := hℓq
  rw [d4Q_twistedTorus Fr] at ht ⊢
  obtain ⟨a, ha, rfl⟩ : ∃ a ∈ fixedCharTuples d4QM Fr, rootDiagUnit TwistTag.D4.tag a = t := by
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 ht
    exact ⟨a, ha, rfl⟩
  rw [d4Minus_h90_conj, d4Minus_h90_conj, ← rootDiagUnit_mul, ← rootDiagUnit_mul] at hcoc
  have hpt : ∀ i, a i * a (TwistTag.D4.perm i) * a (TwistTag.D4.perm (TwistTag.D4.perm i)) = 1 :=
    fun i => congrFun (rootDiagUnit_injective (hcoc.trans rootDiagUnit_one.symm)) i
  have h2 : a i2 ^ 3 = 1 := by
    have h := hpt i2
    rw [perm_i2, perm_i2] at h
    rw [pow_three']
    exact h
  have h3 : a i3 = a i0 ^ (q * q) := by
    rw [d4Q_a3 hFr ha, d4Q_a1 hFr ha, inv_pow, ← pow_mul, inv_inv]
  have h0 : a i0 * (a i0 ^ q)⁻¹ * a i0 ^ (q * q) = 1 := by
    have h := hpt i0
    rw [perm_i0, perm_i1, d4Q_a1 hFr ha, h3] at h
    exact h
  obtain ⟨c₁, hc₁, hc₁N⟩ := d4Minus_h90_root q h0
  have hc0 : a i0 = (c₁ ^ (q + 1))⁻¹ := by rw [hc₁, inv_inv]
  refine ⟨rootDiagUnit TwistTag.D4.tag (d4QTuple q 1 c₁),
    ⟨d4QTuple q 1 c₁, d4QTuple_mem hFr (one_pow _) hc₁N, rfl⟩, a i2, h2, d4Q_pow2 hFr ha, ?_⟩
  rw [d4Minus_h90_conj, rootDiagUnit_inv, ← rootDiagUnit_mul, ← rootDiagUnit_mul]
  change rootDiagUnit TwistTag.D4.tag _ = rootDiagUnit TwistTag.D4.tag (d4Tuple 1 1 (a i2) 1)
  congr 1
  funext i
  rcases fin_cases i with rfl | rfl | rfl | rfl
  · show d4QTuple q 1 c₁ i0 * a i0 * (d4QTuple q 1 c₁ (TwistTag.D4.perm i0))⁻¹ =
      d4Tuple 1 1 (a i2) 1 i0
    rw [perm_i0]
    change c₁ * a i0 * ((c₁ ^ q)⁻¹)⁻¹ = 1
    rw [inv_inv, hc0]
    group
  · show d4QTuple q 1 c₁ i1 * a i1 * (d4QTuple q 1 c₁ (TwistTag.D4.perm i1))⁻¹ =
      d4Tuple 1 1 (a i2) 1 i1
    rw [perm_i1]
    change (c₁ ^ q)⁻¹ * a i1 * (c₁ ^ (q * q))⁻¹ = 1
    rw [d4Q_a1 hFr ha, hc0]
    exact d4Minus_h90_coord_one q
  · show d4QTuple q 1 c₁ i2 * a i2 * (d4QTuple q 1 c₁ (TwistTag.D4.perm i2))⁻¹ =
      d4Tuple 1 1 (a i2) 1 i2
    rw [perm_i2]
    change 1 * a i2 * (1 : Lˣ)⁻¹ = a i2
    rw [inv_one, one_mul, mul_one]
  · show d4QTuple q 1 c₁ i3 * a i3 * (d4QTuple q 1 c₁ (TwistTag.D4.perm i3))⁻¹ =
      d4Tuple 1 1 (a i2) 1 i3
    rw [perm_i3]
    change c₁ ^ (q * q) * a i3 * c₁⁻¹ = 1
    rw [h3, hc0, d4Minus_h90_coord_three, hc₁N, inv_one]

end CFSG.GH74.GLS.Stage2.Bender.Thm1
