module

public import CFSG.LocalAnalysis.SeitzReduction.E6PilotNonsplit
public import CFSG.RankThree.SteinbergR3ELinearTwoPrimeCentralizer
public import CFSG.LocalAnalysis.SectionRank.Ccomm.LinearTwo
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQChoice
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.LangStronglyOrthogonalCommute
public import CFSG.LieType.Universal.Spin.Roots
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotLeviPerp
public import CFSG.RankThree.SteinbergR3ELinearTwoOddFieldFixed
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Lemma83
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.Cardinalities
public import CFSG.Walter.Defs

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two

open Subgroup Polynomial
open CFSG.SeitzReduction.E6Pilot
open CFSG.LieType.Chevalley
open CFSG.Blueprint.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction

section Diagonalization

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

local notation "K₂" => FiniteField.Extension K 2 2

theorem exists_diagonalization_of_orderOf {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {A : SL2 K} (hA : orderOf A = p) :
    ∃ l : K₂ˣ, ∃ P : SL2 K₂,
      (l : K₂) ^ 2 -
          algebraMap K K₂ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) * (l : K₂) + 1 = 0 ∧
        l ≠ 1 ∧ l ^ p = 1 ∧ (l : K₂) ∉ Set.range (algebraMap K K₂) ∧
        (l : K₂) ^ Nat.card K = ((l⁻¹ : K₂ˣ) : K₂) ∧
        P⁻¹ * Matrix.SpecialLinearGroup.map (algebraMap K K₂) A * P = HSL l := by
  classical
  have hpp : p.Prime := Fact.out
  set t : K := Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) with ht
  have hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 :=
    CFSG.ABGLocalTools.apply_one_zero_ne_zero_of_orderOf (F := K) hp hpq hA
  obtain ⟨x, hx⟩ := F4Pilot.exists_sq_sub_mul_add_one_eq_zero t
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  have hx1 : x ≠ 1 := by
    rintro rfl
    have ht0 : t = 0 := by
      apply (algebraMap K K₂).injective
      rw [map_zero]
      have htwo : (1 : K₂) + 1 = 0 := CharTwo.add_self_eq_zero 1
      linear_combination htwo - hx
    have hA2 : A ^ 2 = 1 := by
      refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
      rw [F4Pilot.sq_eq_trace_smul_sub_one, ← ht, ht0, zero_smul, zero_sub, Matrix.neg_apply,
        CharTwo.neg_eq, Matrix.SpecialLinearGroup.coe_one]
    have h2 : orderOf A ≤ 2 := orderOf_le_of_pow_eq_one (by norm_num) hA2
    rw [hA] at h2
    have h3 : 2 ≤ p := hpp.two_le
    omega
  have hll : x ≠ x⁻¹ := by
    intro h
    have h2 : x * x = 1 := by
      nth_rewrite 2 [h]
      exact mul_inv_cancel₀ hx0
    exact hx1 (F4Pilot.eq_one_of_sq_eq_one_of_charTwo (by rwa [sq]))
  set l : K₂ˣ := Units.mk0 x hx0 with hldef
  have hlx : (l : K₂) = x := rfl
  set A₂ : SL2 K₂ := Matrix.SpecialLinearGroup.map (algebraMap K K₂) A with hA₂
  have hA₂co : (A₂ : Matrix (Fin 2) (Fin 2) K₂) =
      (A : Matrix (Fin 2) (Fin 2) K).map (algebraMap K K₂) := by
    rw [hA₂, Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
  have htrA : Matrix.trace (A₂ : Matrix (Fin 2) (Fin 2) K₂) = algebraMap K K₂ t := by
    rw [hA₂co]
    exact (AddMonoidHom.map_trace (algebraMap K K₂) (A : Matrix (Fin 2) (Fin 2) K)).symm
  have hc' : (A₂ : Matrix (Fin 2) (Fin 2) K₂) 1 0 ≠ 0 := by
    rw [hA₂co, Matrix.map_apply]
    intro h0
    exact hc ((algebraMap K K₂).injective (by simpa using h0))
  have hlr : (l : K₂) ^ 2 - algebraMap K K₂ t * (l : K₂) + 1 = 0 := by
    rw [hlx]
    exact hx
  have hlr' : (l : K₂) ^ 2 - Matrix.trace (A₂ : Matrix (Fin 2) (Fin 2) K₂) * (l : K₂) + 1 = 0 := by
    rw [htrA]
    exact hlr
  have hll' : (l : K₂) ≠ ((l⁻¹ : K₂ˣ) : K₂) := by
    simpa [hlx, Units.val_inv_eq_inv_val] using hll
  obtain ⟨P, hP⟩ := F4Pilot.exists_inv_mul_mul_eq_HSL A₂ hc' l hlr' hll'
  have hA₂p : A₂ ^ p = 1 := by
    rw [hA₂, ← map_pow, show A ^ p = 1 from by rw [← hA]; exact pow_orderOf_eq_one A, map_one]
  have hlpow : l ^ p = 1 := by
    have hHSL : (HSL l : SL2 K₂) ^ p = 1 := by
      rw [← hP, show P⁻¹ * A₂ * P = P⁻¹ * A₂ * P⁻¹⁻¹ by rw [inv_inv], conj_pow, hA₂p]
      simp
    rw [F4Pilot.HSL_pow] at hHSL
    refine Units.ext ?_
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    have h := congrArg (fun g : SL2 K₂ => (g : Matrix (Fin 2) (Fin 2) K₂) 0 0) hHSL
    simpa [coe_HSL, Matrix.SpecialLinearGroup.coe_one] using h
  have hl1 : l ≠ 1 := by
    intro h
    apply hx1
    rw [← hlx]
    simpa using congrArg Units.val h
  have hlrange : (l : K₂) ∉ Set.range (algebraMap K K₂) := by
    rintro ⟨a, ha⟩
    have hap : a ^ p = 1 := by
      have h : algebraMap K K₂ (a ^ p) = 1 := by
        rw [map_pow, ha]
        simpa using (congrArg Units.val hlpow :
          ((l ^ p : K₂ˣ) : K₂) = ((1 : K₂ˣ) : K₂))
      exact (algebraMap K K₂).injective (by simpa using h)
    have ha1 : a ≠ 1 := by
      intro h
      exact hl1 (Units.ext (by rw [← ha, h]; simp))
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_pow hpp.pos.ne'] at hap
      exact zero_ne_one hap
    have haord : orderOf a = p := by
      have hd : orderOf a ∣ p := orderOf_dvd_of_pow_eq_one hap
      rcases (Nat.dvd_prime hpp).mp hd with h | h
      · exact absurd h (fun h => ha1 (orderOf_eq_one_iff.mp h))
      · exact h
    have hunit : orderOf a ∣ Nat.card K - 1 := by
      have h := orderOf_dvd_natCard (Units.mk0 a ha0)
      rw [Nat.card_units] at h
      rwa [show orderOf (Units.mk0 a ha0 : Kˣ) = orderOf a by
        simpa using (orderOf_units (y := Units.mk0 a ha0)).symm] at h
    have hp1 : p ∣ Nat.card K - 1 := haord ▸ hunit
    have h2 : p ∣ 2 := by
      have := Nat.dvd_sub hpq hp1
      rwa [show Nat.card K + 1 - (Nat.card K - 1) = 2 by
        have := Nat.card_pos (α := K); omega] at this
    have hp2 : p ≤ 2 := Nat.le_of_dvd (by norm_num) h2
    have h3 : 2 ≤ p := hpp.two_le
    omega
  have hlq : (l : K₂) ^ Nat.card K = ((l⁻¹ : K₂ˣ) : K₂) := by
    have hqroot : ((l : K₂) ^ Nat.card K) ^ 2 -
        algebraMap K K₂ t * ((l : K₂) ^ Nat.card K) + 1 = 0 := by
      have h := congrArg (FiniteField.Extension.frob K 2 2) hlr
      rw [map_add, map_sub, map_mul, map_pow, map_one, map_zero,
        (FiniteField.Extension.frob K 2 2).commutes t,
        FiniteField.Extension.frob_apply] at h
      simpa using h
    have hne : (l : K₂) ^ Nat.card K ≠ (l : K₂) := by
      intro h
      apply hlrange
      rw [← FiniteField.Extension.frob_apply] at h
      exact (F4Pilot.frob_eq_self_iff (l : K₂)).1 h
    have hsub : ((l : K₂) ^ Nat.card K - (l : K₂)) *
        ((l : K₂) ^ Nat.card K + (l : K₂) - algebraMap K K₂ t) = 0 := by
      linear_combination hqroot - hlr
    have hsum : (l : K₂) ^ Nat.card K + (l : K₂) = algebraMap K K₂ t := by
      rcases mul_eq_zero.mp hsub with h | h
      · exact absurd (sub_eq_zero.mp h) hne
      · linear_combination h
    have hmul : (l : K₂) ^ Nat.card K * (l : K₂) = 1 := by
      rw [← hsum] at hlr
      have h1 : 1 - (l : K₂) ^ Nat.card K * (l : K₂) = 0 := by
        linear_combination hlr
      exact (sub_eq_zero.mp h1).symm
    rw [Units.val_inv_eq_inv_val]
    exact eq_inv_of_mul_eq_one_left hmul
  exact ⟨l, P, hlr, hl1, hlpow, hlrange, hlq, hP⟩

end Diagonalization

section SL2Centralizer

variable {K : Type*} [Field K] [Finite K] [CharP K 2]

local notation "K₂" => FiniteField.Extension K 2 2

private theorem mu_pow_card_add_one {A : SL2 K} {C : Subgroup (SL2 K)}
    {coords : C → K × K} {l : K₂ˣ}
    (hcoords : ∀ B : C, (B : Matrix (Fin 2) (Fin 2) K) =
      (coords B).1 • (1 : Matrix (Fin 2) (Fin 2) K) +
        (coords B).2 • (A : Matrix (Fin 2) (Fin 2) K))
    (hlr : (l : K₂) ^ 2 -
      algebraMap K K₂ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) * (l : K₂) + 1 = 0)
    (hlq : (l : K₂) ^ Nat.card K = ((l⁻¹ : K₂ˣ) : K₂)) :
    ∀ B : C, (algebraMap K K₂ (coords B).1 + algebraMap K K₂ (coords B).2 * (l : K₂)) ^
      (Nat.card K + 1) = 1 := by
  have hfrob : ∀ (z : K₂) (α β : K),
      (algebraMap K K₂ α + algebraMap K K₂ β * z) ^ Nat.card K =
        algebraMap K K₂ α + algebraMap K K₂ β * z ^ Nat.card K := by
    intro z α β
    rw [← FiniteField.Extension.frob_apply, ← FiniteField.Extension.frob_apply, map_add, map_mul,
      AlgEquiv.commutes, AlgEquiv.commutes]
  have hμq : ∀ B : C,
      (algebraMap K K₂ (coords B).1 + algebraMap K K₂ (coords B).2 * (l : K₂)) ^ Nat.card K =
        algebraMap K K₂ (coords B).1 +
          algebraMap K K₂ (coords B).2 * ((l⁻¹ : K₂ˣ) : K₂) := by
    intro B
    rw [hfrob, hlq]
  intro B
  set x := (coords B).1 with hxdef
  set y := (coords B).2 with hydef
  have hxy := hcoords B
  have hdetK : x ^ 2 + x * y * Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) + y ^ 2 = 1 := by
    have h := (B : SL2 K).2
    rw [hxy] at h
    rw [CFSG.RankThree.LinearTwo.det_smul_one_add_smul, A.2, mul_one] at h
    exact h
  have hdetK₂ : (algebraMap K K₂ x) ^ 2 + algebraMap K K₂ x * algebraMap K K₂ y *
      algebraMap K K₂ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) +
        (algebraMap K K₂ y) ^ 2 = 1 := by
    have := congrArg (algebraMap K K₂) hdetK
    simpa only [map_add, map_mul, map_pow, map_one] using this
  have hsum : (l : K₂) + ((l⁻¹ : K₂ˣ) : K₂) =
      algebraMap K K₂ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K)) := by
    have hmul : (l : K₂) * ((l⁻¹ : K₂ˣ) : K₂) = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hzero : (l : K₂) * ((l : K₂) + ((l⁻¹ : K₂ˣ) : K₂) -
        algebraMap K K₂ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K))) = 0 := by
      rw [mul_sub, mul_add, hmul, ← sq]
      linear_combination hlr
    exact sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_left l.ne_zero)
  have hmul : (l : K₂) * ((l⁻¹ : K₂ˣ) : K₂) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  calc (algebraMap K K₂ x + algebraMap K K₂ y * (l : K₂)) ^ (Nat.card K + 1)
      = (algebraMap K K₂ x + algebraMap K K₂ y * (l : K₂)) ^ Nat.card K *
          (algebraMap K K₂ x + algebraMap K K₂ y * (l : K₂)) := by rw [pow_succ]
    _ = (algebraMap K K₂ x + algebraMap K K₂ y * ((l⁻¹ : K₂ˣ) : K₂)) *
          (algebraMap K K₂ x + algebraMap K K₂ y * (l : K₂)) := by rw [hμq]
    _ = (algebraMap K K₂ x) ^ 2 + algebraMap K K₂ x * algebraMap K K₂ y *
          (algebraMap K K₂ (Matrix.trace (A : Matrix (Fin 2) (Fin 2) K))) +
          (algebraMap K K₂ y) ^ 2 := by
        rw [show (algebraMap K K₂ x + algebraMap K K₂ y * ((l⁻¹ : K₂ˣ) : K₂)) *
            (algebraMap K K₂ x + algebraMap K K₂ y * (l : K₂)) =
            (algebraMap K K₂ x) ^ 2 + algebraMap K K₂ x * algebraMap K K₂ y *
              ((l : K₂) + ((l⁻¹ : K₂ˣ) : K₂)) +
              (algebraMap K K₂ y) ^ 2 * ((l : K₂) * ((l⁻¹ : K₂ˣ) : K₂)) by ring]
        rw [hmul, mul_one, hsum]
    _ = 1 := hdetK₂

private theorem mu_injective {A : SL2 K} {C : Subgroup (SL2 K)}
    {coords : C → K × K} {l : K₂ˣ}
    (hcoords : ∀ B : C, (B : Matrix (Fin 2) (Fin 2) K) =
      (coords B).1 • (1 : Matrix (Fin 2) (Fin 2) K) +
        (coords B).2 • (A : Matrix (Fin 2) (Fin 2) K))
    (hcommutant : ∀ B ∈ C, ∃ x y : K, (B : Matrix (Fin 2) (Fin 2) K) =
      x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (A : Matrix (Fin 2) (Fin 2) K))
    (hAnscalar : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • 1)
    (hlrange : (l : K₂) ∉ Set.range (algebraMap K K₂)) :
    ∀ B B' : C,
      algebraMap K K₂ (coords B).1 + algebraMap K K₂ (coords B).2 * (l : K₂) =
      algebraMap K K₂ (coords B').1 +
        algebraMap K K₂ (coords B').2 * (l : K₂) → B = B' := by
  intro B B' hBB
  obtain ⟨x, y, hxy⟩ := hcommutant B B.2
  obtain ⟨x', y', hxy'⟩ := hcommutant B' B'.2
  have hcu := CFSG.RankThree.LinearTwo.eq_of_smul_one_add_smul_eq hAnscalar
    (hxy.symm.trans (hcoords B))
  have hcu' := CFSG.RankThree.LinearTwo.eq_of_smul_one_add_smul_eq hAnscalar
    (hxy'.symm.trans (hcoords B'))
  rw [← hcu.1, ← hcu.2, ← hcu'.1, ← hcu'.2] at hBB
  have hy : y = y' := by
    by_contra hy
    apply hlrange
    refine ⟨(x - x') / (y' - y), ?_⟩
    have hhy : ¬y' = y := fun h => hy h.symm
    have hne : algebraMap K K₂ (y' - y) ≠ 0 :=
      (map_ne_zero (algebraMap K K₂)).2 (sub_ne_zero.mpr hhy)
    have hkey : algebraMap K K₂ (x - x') = algebraMap K K₂ (y' - y) * (l : K₂) := by
      rw [map_sub, map_sub, sub_mul]
      linear_combination hBB
    rw [map_div₀, hkey, mul_div_cancel_left₀ _ hne]
  have hx : x = x' := by
    rw [hy] at hBB
    exact (algebraMap K K₂).injective (add_right_cancel hBB)
  refine Subtype.ext (Subtype.ext ?_)
  rw [hxy, hxy', hx, hy]

theorem centralizer_sl2_eq_of_isCyclic_of_mem {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1) {X : Subgroup (SL2 K)} (hXcyc : IsCyclic X)
    (hXcard : Nat.card X = Nat.card K + 1) {A : SL2 K} (hAX : A ∈ X) (hA : orderOf A = p) :
    Subgroup.centralizer ({A} : Set (SL2 K)) = X := by
  classical
  set t : K := Matrix.trace (A : Matrix (Fin 2) (Fin 2) K) with ht
  obtain ⟨l, P, hlr, hl1, hlpow, hlrange, hlq, -⟩ :=
    exists_diagonalization_of_orderOf (K := K) (A := A) hp hpq hA
  let C : Subgroup (SL2 K) := Subgroup.centralizer ({A} : Set (SL2 K))
  have hAnscalar : ∀ c : K, (A : Matrix (Fin 2) (Fin 2) K) ≠ c • 1 := by
    intro c hc
    have hdet : c * c = 1 := by
      have h := A.2
      rw [hc] at h
      have hcc : (c • (1 : Matrix (Fin 2) (Fin 2) K)).det = c * c := by
        simp [Matrix.det_fin_two, sq]
      rwa [hcc] at h
    have hc1 : c = 1 := F4Pilot.eq_one_of_sq_eq_one_of_charTwo (by rwa [sq])
    have hA1 : A = 1 := by
      refine Subtype.ext ?_
      rw [hc, hc1, one_smul, Matrix.SpecialLinearGroup.coe_one]
    rw [hA1, orderOf_one] at hA
    exact (Fact.out (p := p.Prime)).one_lt.ne' hA.symm
  have hcommutant : ∀ B ∈ C,
      ∃ x y : K, (B : Matrix (Fin 2) (Fin 2) K) =
        x • (1 : Matrix (Fin 2) (Fin 2) K) + y • (A : Matrix (Fin 2) (Fin 2) K) := by
    intro B hB
    have hBA : (B : Matrix (Fin 2) (Fin 2) K) * (A : Matrix (Fin 2) (Fin 2) K) =
        (A : Matrix (Fin 2) (Fin 2) K) * (B : Matrix (Fin 2) (Fin 2) K) := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp hB
      exact congrArg Subtype.val h
    exact CFSG.SectionRank.Ccomm.exists_eq_smul_one_add_smul (by
      rintro ⟨c, hc⟩
      exact hAnscalar c hc) hBA.symm
  let coords : C → K × K := fun B =>
    (Classical.choose (hcommutant B B.2),
      Classical.choose (Classical.choose_spec (hcommutant B B.2)))
  have coords_spec : ∀ B : C, (B : Matrix (Fin 2) (Fin 2) K) =
      (coords B).1 • (1 : Matrix (Fin 2) (Fin 2) K) +
        (coords B).2 • (A : Matrix (Fin 2) (Fin 2) K) :=
    fun B => Classical.choose_spec (Classical.choose_spec (hcommutant B B.2))
  have hlr' : (l : K₂) ^ 2 - algebraMap K K₂ t * (l : K₂) + 1 = 0 := hlr
  set μ : C → K₂ := fun B =>
    algebraMap K K₂ (coords B).1 + algebraMap K K₂ (coords B).2 * (l : K₂) with hμdef
  have hμpow : ∀ B : C, (μ B) ^ (Nat.card K + 1) = 1 := by
    simpa only [hμdef] using mu_pow_card_add_one coords_spec hlr' hlq
  have hμinj : ∀ B B' : C, μ B = μ B' → B = B' := by
    simpa only [hμdef] using mu_injective coords_spec hcommutant hAnscalar hlrange
  have hcard : Nat.card C ≤ Nat.card K + 1 := by
    let F : C → nthRootsFinset (Nat.card K + 1) (1 : K₂) := fun B =>
      ⟨μ B, (mem_nthRootsFinset (by omega) 1).2 (hμpow B)⟩
    have hF : Function.Injective F := fun B B' h =>
      hμinj B B' (congrArg Subtype.val h)
    calc Nat.card C ≤ Nat.card (nthRootsFinset (Nat.card K + 1) (1 : K₂)) :=
          Nat.card_le_card_of_injective F hF
      _ = (nthRootsFinset (Nat.card K + 1) (1 : K₂)).card := Nat.card_eq_finsetCard _
      _ ≤ Nat.card K + 1 := by
          rw [nthRootsFinset_def]
          exact (Multiset.toFinset_card_le _).trans (card_nthRoots _ _)
  have hle : X ≤ C := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    letI : IsCyclic X := hXcyc
    exact setLike_mul_comm hx hAX
  exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hXcard]; exact hcard)).symm

end SL2Centralizer


section Descent


variable {τ : Tag} {K : Type} [Field K]

local notation "K₂" => FiniteField.Extension K 2 2

open CFSG.Blueprint.Chevalley

theorem exists_mem_mul_of_commute_nonsplit_of_descent_of_orderOf
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [Finite K] [CharP K 2]
    (hdesc : PerpLeviFrobDescent τ K) {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p)
    (hpq : p ∣ Nat.card K + 1) {X : Subgroup (SL2 K)} (hXcyc : IsCyclic X)
    (hXcard : Nat.card X = Nat.card K + 1) {A : SL2 K} (hAX : A ∈ X)
    (hA : orderOf A = p) {g : ModGL τ K} (hg : g ∈ adjointGroup τ K)
    (hgx : g * rootSL2 τ K (highRoot τ) A = rootSL2 τ K (highRoot τ) A * g) :
    ∃ y ∈ X, ∃ d ∈ rootSpan τ K (EPilot.perpRoots τ),
      g = rootSL2 τ K (highRoot τ) y * d := by
  have hp : p ≠ 2 := by omega
  obtain ⟨l, P, -, hl1, hlp, -, hlq, hP⟩ :=
    exists_diagonalization_of_orderOf (K := K) (A := A) hp hpq hA
  have hl3 : 3 ≤ orderOf l := by
    have hdvd : orderOf l ∣ p := orderOf_dvd_of_pow_eq_one hlp
    have hpos : 0 < orderOf l := orderOf_pos l
    have hne1 : orderOf l ≠ 1 := fun h => hl1 (orderOf_eq_one_iff.1 h)
    have hne2 : orderOf l ≠ 2 := fun h => by
      have h2 : l ^ 2 = 1 := by
        have := pow_orderOf_eq_one l
        rwa [h] at this
      apply hl1
      have hv : (l : K₂) = (1 : K₂) := by
        have h2' : (l : K₂) * (l : K₂) = 1 := by
          have := congrArg Units.val h2
          simpa [Units.val_pow_eq_pow_val, sq] using this
        exact F4Pilot.eq_one_of_sq_eq_one_of_charTwo (by simpa [sq] using h2')
      exact Units.ext hv
    have hle : orderOf l ≤ p := Nat.le_of_dvd (Fact.out (p := p.Prime)).pos hdvd
    omega
  have hxJ : rootSL2 τ K (highRoot τ) A ∈ EPilot.highRootSL2 τ K :=
    rootSL2_highRoot_mem_highRootSL2 A
  have hx : orderOf (rootSL2 τ K (highRoot τ) A) = p := by
    rw [orderOf_injective _ rootSL2_highRoot_injective, hA]
  set σ : FiniteField.Extension K 2 2 →+* FiniteField.Extension K 2 2 :=
    (FiniteField.Extension.frob K 2 2).toRingEquiv.toRingHom with hσ
  have hfix : ∀ z : FiniteField.Extension K 2 2, σ z = z ↔
      z ∈ Set.range (algebraMap K (FiniteField.Extension K 2 2)) :=
    fun z => F4Pilot.frob_eq_self_iff z
  have hσι : σ.comp (algebraMap K (FiniteField.Extension K 2 2)) =
      algebraMap K (FiniteField.Extension K 2 2) :=
    RingHom.ext fun a => (FiniteField.Extension.frob K 2 2).commutes a
  have hK₂ : ringChar (FiniteField.Extension K 2 2) = 2 := ringChar.eq _ 2
  set n := rootSL2 τ (FiniteField.Extension K 2 2) (highRoot τ) P with hn
  have hnJ : n ∈ EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) :=
    rootSL2_highRoot_mem_highRootSL2 P
  have hconj : n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
      (rootSL2 τ K (highRoot τ) A) * n = rootDiagUnit τ (EPilot.highDiag τ l) := by
    rw [baseChangeGL_rootSL2_highRoot, hn, ← map_inv, ← map_mul, ← map_mul, hP,
      rootSL2_highRoot_HSL hτ]
  have hm : n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g * n ∈
      toralCentralizer τ (FiniteField.Extension K 2 2) (EPilot.highDiag τ l) := by
    refine mem_toralCentralizer.2 ⟨?_, ?_⟩
    · exact mul_mem (mul_mem (inv_mem (rootSL2_highRoot_mem_adjointGroup P))
        (baseChangeGL_mem_adjointGroup _ hg)) (rootSL2_highRoot_mem_adjointGroup P)
    · have hgx₂ : baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g *
          baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
            (rootSL2 τ K (highRoot τ) A) =
          baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
            (rootSL2 τ K (highRoot τ) A) *
            baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g := by
        rw [← map_mul, hgx, map_mul]
      rw [← hconj]
      calc n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
              (rootSL2 τ K (highRoot τ) A) * n *
              (n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g * n) *
            (n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
              (rootSL2 τ K (highRoot τ) A) * n)⁻¹ =
          n⁻¹ * (baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
              (rootSL2 τ K (highRoot τ) A) *
            baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g) *
            (baseChangeGL (algebraMap K (FiniteField.Extension K 2 2))
              (rootSL2 τ K (highRoot τ) A))⁻¹ * n := by group
        _ = n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g * n := by
            rw [← hgx₂]; group
  rw [(EPilot.toralCentralizer_highDiag_eq_sup hτ hK₂ hl3).1, ← SetLike.mem_coe,
    Subgroup.coe_mul_of_left_le_normalizer_right _ _
      EPilot.highTorusLine_le_normalizer_perpLevi] at hm
  obtain ⟨t, ht, d, hd, htd⟩ := Set.mem_mul.1 hm
  set j := n * t * n⁻¹ with hjdef
  have hjJ : j ∈ EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) :=
    mul_mem (mul_mem hnJ (EPilot.highTorusLine_le_highRootSL2 hτ ht)) (inv_mem hnJ)
  have hg₂ : baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g = j * d := by
    have hnd : n * d * n⁻¹ = d := by
      rw [commute_of_mem_highRootSL2_of_mem_perpLevi hτ hnJ hd, mul_inv_cancel_right]
    calc baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g =
        n * (n⁻¹ * baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g * n) * n⁻¹ :=
          by group
      _ = n * (t * d) * n⁻¹ := by rw [htd]
      _ = (n * t * n⁻¹) * (n * d * n⁻¹) := by group
      _ = j * d := by rw [hnd]
  have hσg : baseChangeGL σ (baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g) =
      baseChangeGL (algebraMap K (FiniteField.Extension K 2 2)) g := by
    rw [F4Pilot.baseChangeGL_baseChangeGL, hσι]
  have hσj : baseChangeGL σ j ∈ EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) := by
    rw [← range_rootSL2_highRoot] at hjJ
    obtain ⟨B, hB⟩ := hjJ
    rw [← hB, baseChangeGL_rootSL2_highRoot]
    exact rootSL2_highRoot_mem_highRootSL2 _
  have hσd : baseChangeGL σ d ∈ rootSpan τ (FiniteField.Extension K 2 2)
      (EPilot.perpRoots τ) :=
    F4Pilot.map_rootSpan_baseChangeGL_le σ _ ⟨d, hd, rfl⟩
  have hjd : baseChangeGL σ j = j ∧ baseChangeGL σ d = d := by
    have h1 : (baseChangeGL σ j)⁻¹ * j = baseChangeGL σ d * d⁻¹ := by
      have h2 : baseChangeGL σ j * baseChangeGL σ d = j * d := by
        rw [← map_mul, ← hg₂, hσg]
      calc (baseChangeGL σ j)⁻¹ * j = (baseChangeGL σ j)⁻¹ * (j * d) * d⁻¹ := by group
        _ = (baseChangeGL σ j)⁻¹ * (baseChangeGL σ j * baseChangeGL σ d) * d⁻¹ := by rw [h2]
        _ = baseChangeGL σ d * d⁻¹ := by group
    have hJ : (baseChangeGL σ j)⁻¹ * j ∈
        EPilot.highRootSL2 τ (FiniteField.Extension K 2 2) :=
      mul_mem (inv_mem hσj) hjJ
    have hD : (baseChangeGL σ j)⁻¹ * j ∈
        rootSpan τ (FiniteField.Extension K 2 2) (EPilot.perpRoots τ) := by
      rw [h1]
      exact mul_mem hσd (inv_mem hd)
    have h0 := (Subgroup.disjoint_def.1 (disjoint_highRootSL2_perpLevi hτ)) hJ hD
    rw [h0] at h1
    exact ⟨inv_mul_eq_one.1 h0, mul_inv_eq_one.1 h1.symm⟩
  obtain ⟨d₀, hd₀D, hd₀⟩ := hdesc d hd hjd.2
  obtain ⟨y, hyJ, hy⟩ :=
    exists_baseChangeGL_eq_of_mem_highRootSL2 (algebraMap K (FiniteField.Extension K 2 2)) σ hfix
      hjJ hjd.1
  have hgyd : g = y * d₀ :=
    baseChangeGL_injective (algebraMap K (FiniteField.Extension K 2 2))
      (by rw [map_mul, hy, hd₀, hg₂])
  rw [← range_rootSL2_highRoot] at hyJ
  obtain ⟨B, rfl⟩ := hyJ
  have hyx : Commute (rootSL2 τ K (highRoot τ) B) (rootSL2 τ K (highRoot τ) A) := by
    have hd₀x : Commute (rootSL2 τ K (highRoot τ) A) d₀ :=
      commute_of_mem_highRootSL2_of_mem_perpLevi hτ (rootSL2_highRoot_mem_highRootSL2 A) hd₀D
    rw [show rootSL2 τ K (highRoot τ) B = g * d₀⁻¹ by rw [hgyd, mul_inv_cancel_right]]
    exact Commute.mul_left hgx hd₀x.symm.inv_left
  have hBA : B ∈ X := by
    have hB : B ∈ Subgroup.centralizer ({A} : Set (SL2 K)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply rootSL2_highRoot_injective
      rw [map_mul, map_mul]
      exact hyx.eq
    rwa [centralizer_sl2_eq_of_isCyclic_of_mem (K := K) (p := p) hp hpq hXcyc hXcard hAX hA]
      at hB
  exact ⟨B, hBA, d₀, hd₀D, hgyd⟩

end Descent

section E6Descent


variable {K : Type} [Field K]

open CFSG.Blueprint.Chevalley

theorem exists_mem_mul_of_commute_nonsplit_E6_of_orderOf [Finite K] [CharP K 2]
    {p : ℕ} [Fact p.Prime] (hp3 : 3 ≤ p) (hpq : p ∣ Nat.card K + 1)
    {X : Subgroup (SL2 K)} (hXcyc : IsCyclic X) (hXcard : Nat.card X = Nat.card K + 1)
    {A : SL2 K} (hAX : A ∈ X) (hA : orderOf A = p) {g : ModGL .E6 K}
    (hg : g ∈ adjointGroup .E6 K)
    (hgx : g * rootSL2 .E6 K (highRoot .E6) A = rootSL2 .E6 K (highRoot .E6) A * g) :
    ∃ y ∈ X, ∃ d ∈ rootSpan .E6 K a5LeviRoots, g = rootSL2 .E6 K (highRoot .E6) y * d := by
  obtain ⟨y, hy, d, hd, hg'⟩ :=
    exists_mem_mul_of_commute_nonsplit_of_descent_of_orderOf (Or.inl rfl)
      perpLeviFrobDescent_E6 hp3 hpq hXcyc hXcard hAX hA hg hgx
  exact ⟨y, hy, d, hd, hg'⟩

end E6Descent

end CFSG.LocalAnalysis.GLTheoremA.Y10F.ExcE6Two
