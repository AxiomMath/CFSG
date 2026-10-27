module

public import CFSG.LieType.SeitzGeneration.ExcTorusUntw

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

section Matrix

theorem negOne_sub_smul_one (r : ℕ) (q : ℤ) :
    (-1 : Matrix (Fin r) (Fin r) ℤ) - q • (1 : Matrix (Fin r) (Fin r) ℤ) =
      (-(q + 1)) • (1 : Matrix (Fin r) (Fin r) ℤ) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, ite_true,
      smul_eq_mul]
    ring
  · simp only [Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply, Matrix.one_apply, h,
      ite_false, smul_eq_mul]
    ring

theorem natAbs_det_negOne_sub (r q : ℕ) :
    ((-1 : Matrix (Fin r) (Fin r) ℤ) - (q : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)).det.natAbs =
      (q + 1) ^ r := by
  rw [negOne_sub_smul_one, Matrix.det_smul, Matrix.det_one, mul_one, Fintype.card_fin,
    Int.natAbs_pow]
  congr 1

theorem charpoly_negOne (r : ℕ) :
    (-1 : Matrix (Fin r) (Fin r) ℤ).charpoly = cyclotomic 2 ℤ ^ r * 1 := by
  have : (-1 : Matrix (Fin r) (Fin r) ℤ) = Matrix.diagonal (fun _ => -1) := by
    ext i j
    by_cases h : i = j <;> simp [h]
  rw [this, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    mul_one, cyclotomic_two]
  simp

theorem negOne_sq (r : ℕ) : (-1 : Matrix (Fin r) (Fin r) ℤ) ^ 2 = 1 := by
  rw [sq, neg_mul_neg, one_mul]

end Matrix

private theorem exists_char_dvd (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] :
    ∃ ℓ : ℕ, ℓ.Prime ∧ CharP L ℓ ∧ ℓ ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  refine ⟨ringChar K, hℓ, charP_of_injective_algebraMap (algebraMap K L).injective _, ?_⟩
  rw [hq]
  exact dvd_pow_self _ f.ne_zero

section V3

variable {τ : Tag} {L : Type}
  [Field L] (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)

open Classical in
@[expose] noncomputable def V3 : Subgroup (ModGL τ L) :=
  if h : IsMulCommutative (twistedTorusOf n Φ) then torsionSubgroup (twistedTorusOf n Φ) h 3
  else ⊥

variable {n Φ}

theorem mem_V3 (hT : IsMulCommutative (twistedTorusOf n Φ)) {x : ModGL τ L} :
    x ∈ V3 n Φ ↔ x ∈ twistedTorusOf n Φ ∧ x ^ 3 = 1 := by
  unfold V3
  simp only [hT, ↓reduceDIte]
  exact Iff.rfl

theorem V3_le : V3 n Φ ≤ twistedTorusOf n Φ := by
  unfold V3
  split_ifs with h
  · exact fun x hx => hx.1
  · exact bot_le

theorem pow_three_eq_one_of_mem_V3 {x : ModGL τ L} (hx : x ∈ V3 n Φ) : x ^ 3 = 1 := by
  unfold V3 at hx
  split_ifs at hx with h
  · exact hx.2
  · rw [Subgroup.mem_bot] at hx
    rw [hx, one_pow]

theorem mul_comm_of_mem_V3 (hT : IsMulCommutative (twistedTorusOf n Φ)) {a b : ModGL τ L}
    (ha : a ∈ V3 n Φ) (hb : b ∈ V3 n Φ) : a * b = b * a := by
  have := hT
  exact setLike_mul_comm (V3_le ha) (V3_le hb)

end V3

section Torus

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
  (Fr : L →+* L) (w0 : WeylGroup τ) (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u)

include hw0 in
theorem twistedTorusOf_negOne_eq :
    twistedTorusOf (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) Fr).map
        (rootDiagUnitHom τ L) := by
  have hw : ∀ u, w0 • u = (-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) *ᵥ u := fun u => by
    rw [hw0, Matrix.neg_mulVec, Matrix.one_mulVec]
  show twistedTorus (canonicalRep (coxeterSystem τ) L w0) Fr = _
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
    refine ⟨a, ?_, rfl⟩
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
    exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
  · rintro ⟨a, ha, rfl⟩
    rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
    exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a, mem_twistedFixedTuples_iff_conj.1 ha⟩

include hw0 in
theorem isMulCommutative_twistedTorusOf :
    IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
      (Units.map (entrywiseHom Fr))) := by
  rw [twistedTorusOf_negOne_eq Fr w0 hw0]
  exact isMulCommutative_map _ inferInstance

end Torus

section Order

variable
  {τ : Tag} {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
  (Fr : L →+* L) (w0 : WeylGroup τ) (hw0 : ∀ u : Fin τ.rank → ℤ, w0 • u = -u)

include hw0 in
theorem card_twistedTorusOf_negOne (hFr : ∀ c, Fr c = c ^ Nat.card K) :
    Nat.card (twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
      (Units.map (entrywiseHom Fr))) = (Nat.card K + 1) ^ τ.rank := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨ℓ, hℓ, hcharL, hℓq⟩ := exists_char_dvd K L
  have hdet := natAbs_det_negOne_sub τ.rank (Nat.card K)
  have hBne : ((-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) -
      (Nat.card K : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)).det ≠ 0 := fun h => by
    rw [h] at hdet
    exact absurd hdet.symm (pow_ne_zero _ (Nat.succ_ne_zero _))
  have hcop : ¬ ℓ ∣ ((-1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) -
      (Nat.card K : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)).det.natAbs := by
    rw [hdet]
    intro h
    have h1 := hℓ.dvd_of_dvd_pow h
    have h2 : ℓ ∣ 1 := (Nat.dvd_add_right hℓq).1 h1
    exact hℓ.one_lt.ne' (Nat.dvd_one.1 h2)
  rw [twistedTorusOf_negOne_eq Fr w0 hw0,
    Subgroup.card_map_of_injective rootDiagUnit_injective,
    natCard_fixedCharTuples _ Fr hFr hBne hcop, hdet]

include hw0 in
theorem card_V3_negOne (hFr : ∀ c, Fr c = c ^ Nat.card K) (h3 : 3 ∣ Nat.card K + 1) :
    Nat.card (V3 (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr))) =
      3 ^ τ.rank := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hcomm := isMulCommutative_twistedTorusOf Fr w0 hw0
  have hV : V3 (canonicalRep (coxeterSystem τ) L w0) (Units.map (entrywiseHom Fr)) =
      torsionSubgroup (twistedTorusOf (canonicalRep (coxeterSystem τ) L w0)
        (Units.map (entrywiseHom Fr))) hcomm 3 := by
    unfold V3
    simp only [hcomm, ↓reduceDIte]
  obtain ⟨ℓ, hℓ, hcharL, hℓq⟩ := exists_char_dvd K L
  have hpq : ¬ 3 ∣ Nat.card K := fun h => by
    have : 3 ∣ 1 := (Nat.dvd_add_right h).1 h3
    omega
  have hpℓ : 3 ≠ ℓ := fun h => hpq (h ▸ hℓq)
  have hq1 : ((Nat.card K : ℕ) : ZMod 3) = -1 := by
    have := (ZMod.natCast_eq_zero_iff (Nat.card K + 1) 3).2 h3
    rw [Nat.cast_add, Nat.cast_one] at this
    exact eq_neg_of_add_eq_zero_left this
  have he : orderOf ((Nat.card K : ℕ) : ZMod 3) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [hq1]
    exact orderOf_eq_prime_iff.2 ⟨by decide, by decide⟩
  rw [hV, natCard_torsion_eq (fixedCharTuples _ Fr) _
      (twistedTorusOf_negOne_eq Fr w0 hw0) hcomm 3,
    natCard_fixedTorsion _ Fr hℓ hFr Nat.prime_three hpℓ,
    natCard_solutions_modMat Nat.prime_three (-1) (1 : ℤ[X]) (negOne_sq _) (by norm_num)
      (charpoly_negOne _) hpq he (by norm_num)]

end Order

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
