module

public import CFSG.LieType.SeitzGeneration.ExcTorusUntw

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.LieType.SeitzGeneration Polynomial
open scoped Matrix

private theorem exists_char_dvd_gen (K : Type) [Field K] [Finite K] (L : Type) [Field L]
    [Algebra K L] : ∃ ℓ : ℕ, ℓ.Prime ∧ CharP L ℓ ∧ ℓ ∣ Nat.card K := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  refine ⟨ringChar K, hℓ, charP_of_injective_algebraMap (algebraMap K L).injective _, ?_⟩
  rw [hq]
  exact dvd_pow_self _ f.ne_zero

section Torus

variable
  {τ : Tag} {L : Type} [Field L] [IsAlgClosed L]
  (Fr : L →+* L) (w : WeylGroup τ) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
  (hM : ∀ u : Fin τ.rank → ℤ, w • u = M *ᵥ u)

include hM in
theorem twistedTorusOf_eq_map_fixedCharTuples :
    twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr)) =
      (fixedCharTuples M Fr).map (rootDiagUnitHom τ L) := by
  show twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr = _
  ext x
  constructor
  · intro hx
    obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
    refine ⟨a, ?_, rfl⟩
    rw [← twistedFixedTuples_eq_fixedCharTuples hM Fr]
    exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
  · rintro ⟨a, ha, rfl⟩
    rw [← twistedFixedTuples_eq_fixedCharTuples hM Fr] at ha
    exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a, mem_twistedFixedTuples_iff_conj.1 ha⟩

include hM in
theorem isMulCommutative_twistedTorusOf_gen :
    IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) := by
  rw [twistedTorusOf_eq_map_fixedCharTuples Fr w hM]
  exact isMulCommutative_map _ inferInstance

end Torus

section Order

variable
  {τ : Tag} {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]
  (Fr : L →+* L) (w : WeylGroup τ) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
  (hM : ∀ u : Fin τ.rank → ℤ, w • u = M *ᵥ u)

include hM in
theorem card_twistedTorusOf_gen (hFr : ∀ c, Fr c = c ^ Nat.card K) {e : ℕ} (he0 : e ≠ 0)
    (hpow : M ^ e = 1) :
    Nat.card (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) = (M.charpoly.eval (Nat.card K : ℤ)).natAbs := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨ℓ, hℓ, hcharL, hℓq⟩ := exists_char_dvd_gen K L
  have hcop := CFSG.LieType.SeitzGeneration.not_dvd_natAbs_det_sub hℓ hℓq M he0 hpow
  have hBne : (M - (Nat.card K : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)).det ≠ 0 :=
    fun h => hcop (by rw [h]; exact dvd_zero _)
  rw [twistedTorusOf_eq_map_fixedCharTuples Fr w hM,
    Subgroup.card_map_of_injective rootDiagUnit_injective,
    natCard_fixedCharTuples M Fr hFr hBne hcop,
    CFSG.LieType.SeitzGeneration.natAbs_eval_charpoly]

include hM in
theorem finite_twistedTorusOf_gen (hFr : ∀ c, Fr c = c ^ Nat.card K) {e : ℕ} (he0 : e ≠ 0)
    (hpow : M ^ e = 1) :
    Finite (twistedTorusOf (canonicalRep (coxeterSystem τ) L w) (Units.map (entrywiseHom Fr))) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  obtain ⟨ℓ, hℓ, hcharL, hℓq⟩ := exists_char_dvd_gen K L
  have hcop := CFSG.LieType.SeitzGeneration.not_dvd_natAbs_det_sub hℓ hℓq M he0 hpow
  refine Nat.finite_of_card_ne_zero (fun h0 => ?_)
  rw [card_twistedTorusOf_gen Fr w hM hFr he0 hpow,
    CFSG.LieType.SeitzGeneration.natAbs_eval_charpoly] at h0
  exact hcop (by rw [h0]; exact dvd_zero _)

end Order

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross
