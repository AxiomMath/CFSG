module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3UniBlock
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H81A3LinTorus
import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H81.UniA3

open Matrix CFSG.Open CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.LocalAnalysis.GLTheoremA.H81.LinA3

variable {ℓ f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData ℓ f K}

theorem ker_projU : (projU h).ker = normOneScalars h (SG h) 4 :=
  QuotientGroup.ker_mk' _

theorem ker_projU_le_center : (projU h).ker ≤ Subgroup.center ↥(SG h) := by
  rw [ker_projU]
  exact normOneScalars_le_center h _ 4

theorem projU_noTorsion {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∀ z ∈ (projU h).ker, z ^ p = 1 → z = 1 := by
  intro z hz hzp
  rw [ker_projU] at hz
  obtain ⟨c, -, hc4, hzc⟩ := mem_normOneScalars.1 hz
  have hcp : c ^ p = 1 := by
    have h1 : ((z ^ p : ↥(SG h)) : GL (Fin 4) K) = 1 := by rw [hzp]; rfl
    rw [Subgroup.coe_pow, hzc, ← map_pow] at h1
    have h2 := congrArg (fun g : GL (Fin 4) K => (g : Matrix (Fin 4) (Fin 4) K) 0 0) h1
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Units.val_one, Matrix.scalar_apply,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h2)
  have hgcd : Nat.gcd 4 p = 1 := by
    have h2 : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2)
    have : Nat.Coprime (2 ^ 2) p := Nat.Coprime.pow_left 2 h2
    simpa using this
  have hc1 : c = 1 := by
    have := pow_gcd_eq_one.2 ⟨hc4, hcp⟩
    rwa [hgcd, pow_one] at this
  apply Subtype.ext
  rw [hzc, hc1, map_one]
  rfl

theorem bar_mul_self_of_pow_eq_one {p : ℕ} (hpq : p ∣ ℓ ^ f + 1) {c : K} (hc : c ^ p = 1) :
    h.bar c * c = 1 := by
  rw [UnitaryFieldData.bar_apply, ← pow_succ]
  obtain ⟨k, hk⟩ := hpq
  rw [hk, pow_mul, hc, one_pow]

theorem exists_conj_diagU_mem [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ ℓ ^ f + 1) {P : Subgroup (PS h)} (hP : IsElemAbelian p P)
    (hcard : Nat.card P = p ^ 3) :
    ∃ A : primeFormUnitary h (idGram K 4), ∀ (d : Fin 4 → K) (hn : ∀ i, h.bar (d i) * d i = 1)
      (hd : ∏ i, d i = 1), (∀ i, d i ^ p = 1) →
        projU h (diagU h d hn hd) ∈ P.map (primeFormConjHom h (idGram K 4) A).toMonoidHom := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨B, hBP, -, hBel, hBcard⟩ :=
    CFSG.StandardType.TableBUE.exists_lift_of_noTorsion (projU h) (QuotientGroup.mk'_surjective _)
      hp (projU_noTorsion hp hp2) hP
  let ι : ↥(SG h) →* ↥(primeFormUnitary h (idGram K 4)) :=
    Subgroup.inclusion (fun g hg => ((mem_gramSU_iff_unitary h).1 hg).1)
  have hBcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hBel.1.is_comm.comm (⟨a, ha⟩ : B) ⟨b, hb⟩)
  obtain ⟨Pm, hPm⟩ := CFSG.RankThree.PartOne.KFU.exists_unitary_conj_diag h hp hpq (B.map ι)
    (by
      rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBcomm a ha b hb])
    (by
      rintro _ ⟨a, ha, rfl⟩
      rw [← map_pow, hBel.2 a ha, map_one])
  refine ⟨Pm⁻¹, ?_⟩
  let c := primeFormConjSU h (idGram K 4) Pm⁻¹
  let B' : Subgroup ↥(SG h) := B.map c.toMonoidHom
  have hB'P : B'.map (projU h) = P.map (primeFormConjHom h (idGram K 4) Pm⁻¹).toMonoidHom := by
    rw [← hBP, Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hdiag : ∀ x ∈ B', ∀ i j, i ≠ j → ((x : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j = 0 := by
    rintro _ ⟨a, ha, rfl⟩ i j hij
    have h1 := hPm (ι a) ⟨a, ha, rfl⟩ hij
    have h2 : ((c a : ↥(SG h)) : GL (Fin 4) K) =
        ((Pm⁻¹ * ι a * Pm : primeFormUnitary h (idGram K 4)) : GL (Fin 4) K) := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      change ((Pm : GL (Fin 4) K))⁻¹ * a * ((Pm : GL (Fin 4) K))⁻¹⁻¹ =
        ((Pm : GL (Fin 4) K))⁻¹ * a * Pm
      rw [inv_inv]
    change ((c a : ↥(SG h)) : GL (Fin 4) K).val i j = 0
    rw [h2]
    exact h1
  have hpow : ∀ x ∈ B', x ^ p = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_pow, hBel.2 a ha, map_one]
  have hB'card : Nat.card B' = p ^ 3 := by
    rw [Subgroup.card_map_of_injective c.injective, hBcard, hcard]
  have hxd : ∀ x : B', ((x : ↥(SG h)) : GL (Fin 4) K).val =
      diagonal fun i => ((x : ↥(SG h)) : GL (Fin 4) K).val i i := by
    intro x
    ext i j
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij, hdiag x x.2 i j hij]
  have hmemT : ∀ x : B', (fun i => ((x : ↥(SG h)) : GL (Fin 4) K).val i i) ∈ torusSet p K := by
    intro x
    refine ⟨fun i => ?_, ?_⟩
    · have h1 := congrArg (fun y : ↥(SG h) => ((y : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i i)
        (hpow x x.2)
      simp only [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, OneMemClass.coe_one,
        Units.val_one, one_apply_eq] at h1
      rw [hxd, diagonal_pow, diagonal_apply_eq] at h1
      exact h1
    · have h1 := (mem_gramSU.1 (x : ↥(SG h)).2).2
      rw [hxd, det_diagonal] at h1
      exact h1
  let δ : B' → torusSet p K := fun x => ⟨_, hmemT x⟩
  have hδ : Function.Injective δ := by
    intro x y hxy
    have h1 := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    ext i j
    by_cases hij : i = j
    · subst hij
      exact congrFun h1 i
    · rw [hdiag x x.2 i j hij, hdiag y y.2 i j hij]
  have hT : Nat.card (torusSet p K) ≤ Nat.card B' := by
    rw [hB'card]
    exact natCard_torusSet_le hp.pos
  have : Finite (torusSet p K) := Set.toFinite _
  have hbij := hδ.bijective_of_nat_card_le hT
  intro d hn hd hdp
  obtain ⟨x, hx⟩ := hbij.2 ⟨d, hdp, hd⟩
  have hxd' : (x : ↥(SG h)) = diagU h d hn hd := by
    apply Subtype.ext
    apply Units.ext
    rw [coe_diagU]
    ext i j
    have h1 := congrArg Subtype.val hx
    by_cases hij : i = j
    · subst hij
      rw [diagonal_apply_eq]
      exact congrFun h1 i
    · rw [diagonal_apply_ne _ hij, hdiag x x.2 i j hij]
  rw [← hB'P, ← hxd']
  exact Subgroup.mem_map_of_mem _ x.2

end CFSG.LocalAnalysis.GLTheoremA.H81.UniA3
