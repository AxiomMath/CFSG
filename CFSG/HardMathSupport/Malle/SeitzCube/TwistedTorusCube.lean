module

public import CFSG.LieType.SeitzGeneration.ExcTorusUntw

public section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE Polynomial
open scoped Matrix


theorem exists_twistedTorus_elemAbelian {τ : Tag} (K : Type) [Field K] [Finite K] (L : Type)
    [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {p : ℕ} (hp : p.Prime) (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (w : WeylGroup τ) (hw : ∀ u, w • u = M *ᵥ u) {n e m : ℕ} (R : ℤ[X]) (hn0 : n ≠ 0)
    (hpow : M ^ n = 1) (hn : ¬ p ∣ n) (hchar : M.charpoly = cyclotomic e ℤ ^ m * R)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (hR : ¬ (p : ℤ) ∣ R.eval (Nat.card K : ℤ)) :
    ∃ E : Subgroup (ModGL τ L),
      E ≤ twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr ∧ IsElemAbelian p E ∧
        Nat.card E = p ^ m := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  have hT0 : twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr =
      (fixedCharTuples M Fr).map (rootDiagUnitHom τ L) := by
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
  have hcomm : IsMulCommutative (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) := by
    rw [hT0]
    exact isMulCommutative_map _ inferInstance
  set B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    M - (Nat.card K : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval (Nat.card K : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hpos : 0 < (cyclotomic e ℤ).eval (Nat.card K : ℤ) :=
    cyclotomic_pos' e (by exact_mod_cast hq2)
  have hRne : R.eval (Nat.card K : ℤ) ≠ 0 := fun h => hR (by rw [h]; exact dvd_zero _)
  have hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0 := by
    rw [hchar, eval_mul, eval_pow]
    exact mul_ne_zero (pow_ne_zero m hpos.ne') hRne
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ hℓq M hn0 hpow
  have hpℓ : p ≠ ringChar K := fun h => hpq (h ▸ hℓq)
  have htors : Nat.card (torsionSubgroup (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr)
      hcomm p) = p ^ m := by
    rw [natCard_torsion_eq (fixedCharTuples M Fr) _ hT0 hcomm p,
      natCard_fixedTorsion M Fr hℓ hFr hp hpℓ,
      natCard_solutions_modMat hp M R hpow hn hchar hpq he hR]
  refine ⟨torsionSubgroup _ hcomm p, fun x hx => hx.1, ⟨?_, fun x hx => hx.2⟩, htors⟩
  exact IsMulCommutative.of_comm fun a b => Subtype.ext
    (setLike_mul_comm (a.2.1 : _ ∈ twistedTorus _ Fr) (b.2.1 : _ ∈ twistedTorus _ Fr))

end CFSG.HardMathSupport.Malle.SeitzCube
