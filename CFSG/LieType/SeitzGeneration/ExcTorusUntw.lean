module

public import CFSG.LieType.SeitzGeneration.ExcTorusCard
public import CFSG.LieType.SeitzGeneration.ExcTorusEigen
public import CFSG.LieType.SeitzGeneration.ExcTorusArith
public import CFSG.LieType.SeitzGeneration.ExcTorusLang
public import CFSG.RankThree.PartOne.KE.CTLangData
public import CFSG.RankThree.PartOne.KE.CTStatement
public import CFSG.RankThree.PartOne.KE.CTTorus

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.PartOne.KE
  Polynomial
open scoped Matrix

section Charpoly

variable {r : ℕ}

theorem natAbs_eval_charpoly (M : Matrix (Fin r) (Fin r) ℤ) (q : ℤ) :
    (M.charpoly.eval q).natAbs = (M - q • (1 : Matrix (Fin r) (Fin r) ℤ)).det.natAbs := by
  rw [Matrix.eval_charpoly]
  have : Matrix.scalar (Fin r) q - M = -(M - q • (1 : Matrix (Fin r) (Fin r) ℤ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp
  rw [this, Matrix.det_neg, Int.natAbs_mul, Int.natAbs_pow, Int.natAbs_neg, Int.natAbs_one,
    one_pow, one_mul]

theorem charpoly_coeff_zero_of_pow_eq_one (M : Matrix (Fin r) (Fin r) ℤ) {n : ℕ} (hn : n ≠ 0)
    (hpow : M ^ n = 1) : M.charpoly.coeff 0 = 1 ∨ M.charpoly.coeff 0 = -1 := by
  have h1 : M.det ^ n = 1 := by rw [← Matrix.det_pow, hpow, Matrix.det_one]
  have h2 : IsUnit M.det := IsUnit.of_pow_eq_one h1 hn
  have h3 : IsUnit (M.charpoly.coeff 0) := by
    have := Matrix.det_eq_sign_charpoly_coeff M ▸ h2
    exact isUnit_of_mul_isUnit_right this
  exact Int.isUnit_iff.1 h3

theorem not_dvd_natAbs_det_sub {ℓ q : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ∣ q)
    (M : Matrix (Fin r) (Fin r) ℤ) {n : ℕ} (hn : n ≠ 0) (hpow : M ^ n = 1) :
    ¬ ℓ ∣ (M - (q : ℤ) • (1 : Matrix (Fin r) (Fin r) ℤ)).det.natAbs := by
  rw [← natAbs_eval_charpoly]
  intro h
  have h1 : (ℓ : ℤ) ∣ M.charpoly.eval (q : ℤ) := Int.natCast_dvd.2 h
  have h2 : (ℓ : ℤ) ∣ (q : ℤ) := Int.natCast_dvd_natCast.2 hℓq
  have h3 := sub_dvd_eval_sub (q : ℤ) 0 M.charpoly
  rw [sub_zero] at h3
  have h4 : (ℓ : ℤ) ∣ M.charpoly.eval 0 := by
    have := dvd_sub h1 (h2.trans h3)
    simpa using this
  rw [← coeff_zero_eq_eval_zero] at h4
  have h5 : (ℓ : ℤ) ∣ 1 := by
    rcases charpoly_coeff_zero_of_pow_eq_one M hn hpow with h | h <;> rw [h] at h4
    · exact h4
    · simpa using h4
  have := Int.natCast_dvd_natCast.1 (by simpa using h5 : (ℓ : ℤ) ∣ ((1 : ℕ) : ℤ))
  exact hℓ.one_lt.ne' (Nat.dvd_one.1 this)

end Charpoly

section Torsion

variable {τ : Tag} {L : Type} [Field L]

theorem natCard_torsion_eq (T : Subgroup (Fin τ.rank → Lˣ)) (S : Subgroup (ModGL τ L))
    (hS : S = T.map (rootDiagUnitHom τ L)) (hT : IsMulCommutative S) (p : ℕ) :
    Nat.card (torsionSubgroup S hT p) =
      Nat.card {a : T // ∀ i, (a : Fin τ.rank → Lˣ) i ^ p = 1} := by
  subst hS
  have hinj : Function.Injective (rootDiagUnitHom τ L) := rootDiagUnit_injective
  have hpow : ∀ a : Fin τ.rank → Lˣ, (rootDiagUnitHom τ L a) ^ p = 1 ↔ ∀ i, a i ^ p = 1 :=
    fun a => by
      rw [← map_pow, ← map_one (rootDiagUnitHom τ L), hinj.eq_iff]
      exact ⟨fun h i => congrFun h i, fun h => funext h⟩
  symm
  refine Nat.card_congr (Equiv.ofBijective
    (fun a => ⟨rootDiagUnitHom τ L a.1.1, ⟨a.1.1, a.1.2, rfl⟩, (hpow _).2 a.2⟩) ⟨?_, ?_⟩)
  · intro a b h
    have h1 : rootDiagUnitHom τ L a.1.1 = rootDiagUnitHom τ L b.1.1 := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext (hinj h1))
  · rintro ⟨x, ⟨a, ha, rfl⟩, hx⟩
    exact ⟨⟨⟨a, ha⟩, (hpow a).1 hx⟩, rfl⟩

end Torsion

section Main


theorem sylowTorus_untwisted {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : ¬ p ∣ Nat.card K) {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hM : CFSG.RankThree.PartOne.KE.IsWeylMatrix τ M) {n e m : ℕ} (R : ℤ[X]) (hn0 : n ≠ 0)
    (hpow : M ^ n = 1) (hn : ¬ p ∣ n) (hchar : M.charpoly = cyclotomic e ℤ ^ m * R)
    (he : orderOf ((Nat.card K : ℕ) : ZMod p) = e) (hR : ¬ (p : ℤ) ∣ R.eval (Nat.card K : ℤ))
    (hord : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      (p ^ (Nat.card K ^ e - 1).factorization p) ^ m) :
    SylowTorus (adjointGroup τ K) p m := by
  classical
  obtain ⟨w, hw⟩ := hM
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  have hq2 : 2 ≤ Nat.card K := Finite.one_lt_card
  have he0 : e ≠ 0 := he ▸ orderOf_natCast_ne_zero hp hpq
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  let ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
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
  have hcomm : IsMulCommutative (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) := by
    show IsMulCommutative (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr)
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
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) = (M.charpoly.eval (Nat.card K : ℤ)).natAbs := by
    show Nat.card (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) = _
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have hpℓ : p ≠ ringChar K := fun h => hpq (h ▸ hℓq)
  have htors : Nat.card (torsionSubgroup (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) hcomm p) = p ^ m := by
    rw [natCard_torsion_eq (fixedCharTuples M Fr) _ hT0 hcomm p,
      natCard_fixedTorsion M Fr hℓ hFr hp hpℓ,
      natCard_solutions_modMat hp M R hpow hn hchar hpq he hR]
  have hordN : p ^ (Nat.card (adjointGroup τ K)).factorization p =
      p ^ ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p := by
    rw [hord, hchar, ordProj_cyclotomic_pow_mul_eval hp hq2 he he0 hR]
  have hrat' : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X →
        IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hPp
    rw [hrange]
    exact (finite_fixed_subgroup_rational d hτ Fr hFr X hXC hXF).2 p hp hp3 P hPX hPp
  exact sylowTorus_of_twisted_torus ι hι (Units.map (entrywiseHom Fr))
    (canonicalRep (coxeterSystem τ) L w) g0 hg0C hg0 hp (Int.natAbs_ne_zero.2 hev) hrat' hcomm
    hcard htors hordN

end Main

end CFSG.LieType.SeitzGeneration
