module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S20
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Models.Blueprint
public import CFSG.RankThree.GF2n.Stroth80.GriessLinear
public import CFSG.ClassicalGroups.Orthogonal.Simple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRootData
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

open Matrix CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)
open CFSG.Quasithin (perfectCore)
open CFSG.QuasithinUnique.Vol2Native.A312L

abbrev TailModel (K A : Type) [Field K] [AddCommGroup A] [Module K A] (r : ℕ) :=
  ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  {qA : QuadraticForm K A} {a₀ : A}

@[expose] def tailRankOneParabolic (qA : QuadraticForm K A) (a₀ : A) (i : Fin r) :
    Subgroup (TailModel K A r) :=
  Subgroup.closure ((tailBorel r qA : Set (TailModel K A r)) ∪ {tailWeylElt r qA a₀ i})

@[expose] def TailRankOneSL2Surjection [Finite (TailModel K A r)]
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) (i : Fin r) : Prop :=
  ∃ f : ↥(Hinf (tailRankOneParabolic qA a₀ i)) →* SpecialLinearGroup (Fin 2) K,
    Function.Surjective f ∧ IsPGroup 2 f.ker

theorem isL2_rankOneParabolic_tail_of_sl2Surjection [FiniteDimensional K A]
    [Finite (TailModel K A r)]
    (hani : qA.Anisotropic) {a₀ : A} (ha₀ : a₀ ≠ 0) {i : Fin r} (hi : i.val + 1 < r)
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (hsurj : TailRankOneSL2Surjection (qA := qA) hani ha₀ i) :
    IsL2 (Bar2 (Hinf (tailRankOneParabolic qA a₀ i))) n := by
  haveI : Finite K :=
    (Nat.card_ne_zero.mp (by rw [hK]; exact pow_ne_zero n (by norm_num))).2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : ringChar K = 2 :=
    CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq Nat.prime_two (by omega) hK
  haveI : CharP K 2 := hchar ▸ ringChar.charP K
  have hK4 : ∃ s : Finset K, s.card = 4 := by
    refine exists_finset_card_four ?_
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hnab : ∃ a b : SpecialLinearGroup (Fin 2) K, a * b ≠ b * a :=
    sl2_nonabelian (K := K) hK4
  haveI : IsSimpleGroup (SpecialLinearGroup (Fin 2) K) := sl2_isSimple (K := K) hK4
  have hmodel : LieModel (StatedProj (StatedSL 2 K)) .PSL 2 2 n :=
    CFSG.Models.LieModel.toBlueprint (by decide)
      (CFSG.RankThree.GF2n.Stroth80.lieModel_statedProj_sl (K := K) (m := 2) (f := n)
        (by norm_num) hn hK)
  obtain ⟨f, hf, hker⟩ := hsurj
  let e : Bar2 (Hinf (tailRankOneParabolic qA a₀ i)) ≃* StatedProj (StatedSL 2 K) :=
    (modO2EquivOfHom hnab f hf hker).trans sl2EquivStatedProj
  exact LieModel.of_mulEquiv (t := .PSL) (n := 2) (p := 2) (f := n) e.symm hmodel

theorem hinf_rankOneParabolic_tail_eq_bot_of_solvable [Finite K] [Finite A]
    [Finite (TailModel K A r)] (i : Fin r)
    (hsolv : Group.IsSolvable ↥(tailRankOneParabolic qA a₀ i)) :
    Hinf (tailRankOneParabolic qA a₀ i) = ⊥ := by
  rw [Hinf, CFSG.inSubgroup, ← CFSG.Quasithin.perfectCore_eq_map_perfectResidual]
  exact (CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot _).mp hsolv

section Restrict

variable {V : Type} [AddCommGroup V] [Module K V]

noncomputable def flagStabilizer (F : Submodule K V) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | F.map (g : V →ₗ[K] V) = F}
  one_mem' := by simp
  mul_mem' := by
    intro g h hg hh
    rw [Set.mem_setOf_eq] at hg hh ⊢
    change F.map ((g : V →ₗ[K] V).comp (h : V →ₗ[K] V)) = F
    rw [Submodule.map_comp, hh, hg]
  inv_mem' := by
    intro g hg
    rw [Set.mem_setOf_eq] at hg ⊢
    have hcomp : ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V).comp ((g : V ≃ₗ[K] V) : V →ₗ[K] V) =
        LinearMap.id := LinearMap.ext (g.left_inv)
    have h : (F.map ((g : V ≃ₗ[K] V) : V →ₗ[K] V)).map ((g⁻¹ : V ≃ₗ[K] V) : V →ₗ[K] V) = F := by
      rw [← Submodule.map_comp, hcomp, Submodule.map_id]
    rwa [hg] at h

end Restrict

end CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
