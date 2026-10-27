module

public import CFSG.ClassicalInvolution.ModelFacts.FundPerfectNodes
public import CFSG.LieType.Steinberg.G2.RankOne
public import CFSG.LieType.Steinberg.TwistedD4.RankOne
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.CharacterTheory.Semidihedral.ElementStructure
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.SpinMinus
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.CurtisTits
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.Blueprint.Chevalley CFSG.LieType
open scoped MatrixGroups

theorem fundPerfect_of_all_nodes (t : StatedLieTag) (n p e : ℕ) [hp : Fact p.Prime]
    (hfund : IsFundTag t) (hadm : StatedLieAdmissible t n p e)
    (hdiv : (modelUniv t n p e hp.out).D.divisible = ∅)
    (hperf : ∀ i : Fin (modelUniv t n p e hp.out).D.rank,
      rankOne (modelUniv t n p e hp.out).D.rootGroup i ≤
        ⁅rankOne (modelUniv t n p e hp.out).D.rootGroup i,
          rankOne (modelUniv t n p e hp.out).D.rootGroup i⁆) :
    ∀ R ∈ fundamentalSubgroups t (modelUniv t n p e hp.out).D, R ≤ ⁅R, R⁆ := by
  obtain ⟨_, _, hct, -⟩ := hasBruhatDatum t n p e hp.out hfund hadm
  intro R hR
  obtain ⟨g, γ, hγ, rfl⟩ := mem_roots_of_mem_fundamentalSubgroups hR
  obtain ⟨w, i, rfl⟩ : ∃ (w : (coxeterMatrix (modelUniv t n p e hp.out).D.isFiniteType).Group)
      (i : Fin (modelUniv t n p e hp.out).D.rank),
      γ = weylAction (modelUniv t n p e hp.out).D.isFiniteType w (Pi.single i 1) := by
    rcases hγ with ⟨w, i, rfl⟩ | ⟨w, i, hi, rfl⟩
    · exact ⟨w, i, rfl⟩
    · rw [hdiv] at hi
      exact absurd hi (Set.notMem_empty i)
  obtain ⟨g', hg'⟩ := exists_map_conj_rankOne hct w
  have h1 := hg' (Pi.single i 1) (Or.inl ⟨1, i, by simp⟩)
  rw [← h1, map_conj_map_conj]
  exact fundPerfect_map_conj_le_commutator (hperf i) _

theorem rankOne_eq_range_of_sl2 {K : Type*} [Group K] {D : UniversalRootDatum K}
    {i : Fin D.rank} {F : Type} [Field F] (φ : SL(2, F) →* K)
    (hu : ∀ c, φ (sl2Upper c) ∈ D.rootGroup (Pi.single i 1))
    (hl : ∀ c, φ (sl2Lower c) ∈ D.rootGroup (-Pi.single i 1))
    (hle : rankOne D.rootGroup i ≤ φ.range) : rankOne D.rootGroup i = φ.range := by
  refine le_antisymm hle ?_
  rintro _ ⟨A, rfl⟩
  obtain ⟨e', a, b, c, rfl⟩ := Adjoint.sl2_eq_prod A
  simp only [map_mul]
  exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_right (hl e')) (Subgroup.mem_sup_left (hu a)))
    (Subgroup.mem_sup_right (hl b))) (Subgroup.mem_sup_left (hu c))

section G2

theorem g2_rankOne_perfect {K : Type} [Field K] [Finite K] (h4 : 4 ≤ Nat.card K)
    (l : Fin (Tag.rank .G2)) :
    rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l ≤
      ⁅rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l,
        rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l⁆ := by
  obtain ⟨φ, -, hup, hlow⟩ := Adjoint.g2_exists_sl2_hom (K := K) l
  have hup' : ∀ c, φ (sl2Upper c) =
      Adjoint.xPar (Chevalley.rootOperatorFamily .G2) (Pi.single l 1) c := fun c => by
    rw [hup, Adjoint.xPar_simple]
  have hlow' : ∀ c, φ (sl2Lower c) =
      Adjoint.xPar (Chevalley.rootOperatorFamily .G2) (-Pi.single l 1) c := fun c => by
    rw [hlow, Adjoint.xPar_neg_simple]
  have hle : rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l ≤ φ.range := by
    refine sup_le ?_ ?_
    · intro g hg
      obtain ⟨c, rfl⟩ := Adjoint.exists_of_mem_rootGroup_simple (Chevalley.rootOperatorFamily .G2) hg
      exact ⟨sl2Upper c, hup c⟩
    · intro g hg
      obtain ⟨c, rfl⟩ :=
        Adjoint.exists_of_mem_rootGroup_neg_simple (Chevalley.rootOperatorFamily .G2) hg
      exact ⟨sl2Lower c, hlow c⟩
  have heq : rankOne (Adjoint.rootGroup (Chevalley.rootOperatorFamily .G2) K) l = φ.range :=
    rankOne_eq_range_of_sl2 (D := Adjoint.g2Datum K) (i := l) φ
      (fun c => by rw [hup']; exact Adjoint.xPar_mem (isRoot_single .G2 l) c)
      (fun c => by rw [hlow']; exact Adjoint.xPar_mem (isRoot_neg_single .G2 l) c) hle
  rw [heq]
  exact fundPerfect_range_le_commutator (CFSG.ClassicalInvolution.sl2_isPerfect h4) φ

variable (n p e : ℕ) [hp : Fact p.Prime]

theorem fundPerfect_G2 (hadm : StatedLieAdmissible .G2 n p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .G2 (modelUniv .G2 n p e hp.out).D, R ≤ ⁅R, R⁆ := by
  have h4' : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e (by have := hadm.2.1; omega)]
    exact h4
  exact fundPerfect_of_all_nodes .G2 n p e trivial hadm rfl fun l =>
    g2_rankOne_perfect (K := GaloisField p e) h4' l

end G2

section D4

open CFSG.LieType.Steinberg.TwistedD4

theorem le_card_fixedField_iterateFrobenius {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) :
    p ^ e ≤ Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) := by
  obtain ⟨ι⟩ : Nonempty (GaloisField p e →ₐ[ZMod p] GaloisField p (3 * e)) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (by
      rw [GaloisField.finrank p (by omega), GaloisField.finrank p (by omega)]
      exact dvd_mul_left e 3)
  have hpow : ∀ x : GaloisField p e, x ^ (p ^ e) = x := fun x => by
    have := Fintype.ofFinite (GaloisField p e)
    have := FiniteField.pow_card x
    rwa [← Nat.card_eq_fintype_card, GaloisField.card p e (by omega)] at this
  have hfix : ∀ x : GaloisField p e,
      ι x ∈ fixedField (iterateFrobenius (GaloisField p (3 * e)) p e) := fun x => by
    show iterateFrobenius (GaloisField p (3 * e)) p e (ι x) = ι x
    rw [iterateFrobenius_def, ← map_pow, hpow]
  have hinj : Function.Injective fun x : GaloisField p e =>
      (⟨ι x, hfix x⟩ : fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) :=
    fun x y h => ι.injective (congrArg Subtype.val h)
  have := Nat.card_le_card_of_injective _ hinj
  rwa [GaloisField.card p e (by omega)] at this

variable {K : Type} [Field K] {σ : K →+* K} (hσ : ∀ c, σ (σ (σ c)) = c)
include hσ

theorem rankOne_long_eq_range :
    rankOne (twistedRootGroup σ) (ng 0) = (slLong σ hσ).range := by
  refine rankOne_eq_range_of_sl2 (D := twistedDatum σ) (i := ng 0) (slLong σ hσ) ?_ ?_ ?_
  · intro c
    exact (mem_twistedRootGroup (σ := σ)).2 (by
      rw [slLong_val, slLongE_upper]
      exact xPar_single_two_mem_twisted hσ c.2)
  · intro c
    exact (mem_twistedRootGroup (σ := σ)).2 (by
      rw [slLong_val, slLongE_lower]
      exact xPar_neg_single_two_mem_twisted hσ c.2)
  · refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ (isRoot_single d4 (nd 2))
        proj_single_two rho_single_two _).1 ((mem_twistedRootGroup (σ := σ)).1 hx)
      exact ⟨sl2Upper ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_upper]; exact hxc.symm)⟩
    · obtain ⟨c, hc, hxc⟩ := (mem_twistedRootSubgroupD4_iff_of_fixed hσ
        (isRoot_neg_single d4 (nd 2)) proj_neg_single_two rho_neg_single_two _).1
        ((mem_twistedRootGroup (σ := σ)).1 hx)
      exact ⟨sl2Lower ⟨c, hc⟩, Subtype.ext (by rw [slLong_val, slLongE_lower]; exact hxc.symm)⟩

theorem rankOne_short_eq_range :
    rankOne (twistedRootGroup σ) (ng 1) = (slShort σ hσ).range := by
  have hr : (slShort σ hσ).range = (phiShortTw σ hσ).range := by
    rw [slShort, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr (MulEquiv.surjective _),
      Subgroup.map_top]
  refine rankOne_eq_range_of_sl2 (D := twistedDatum σ) (i := ng 1) (slShort σ hσ) ?_ ?_ ?_
  · intro c
    refine (mem_twistedRootGroup (σ := σ)).2 ?_
    rw [slShort_upper]
    have := xOuter_mem σ (s := 1) (Or.inl rfl) (hσ c)
    rwa [one_smul] at this
  · intro c
    refine (mem_twistedRootGroup (σ := σ)).2 ?_
    rw [slShort_lower]
    have := xOuter_mem σ (s := -1) (Or.inr rfl) (hσ c)
    rwa [neg_one_smul] at this
  · rw [hr]
    exact rankOne_short_le_range hσ

omit hσ in
theorem fundPerfect_trialityD4 (n p e : ℕ) [hp : Fact p.Prime]
    (hadm : StatedLieAdmissible .trialityD4 n p e) (h4 : 4 ≤ p ^ e) :
    ∀ R ∈ fundamentalSubgroups .trialityD4 (modelUniv .trialityD4 n p e hp.out).D,
      R ≤ ⁅R, R⁆ := by
  have he : 1 ≤ e := hadm.2.1
  have hK : Nat.card (GaloisField p (3 * e)) = (p ^ e) ^ 3 := by
    rw [GaloisField.card p (3 * e) (by omega), pow_mul']
  have hσ := sigma_three_of_card (σ := iterateFrobenius (GaloisField p (3 * e)) p e) (q := p ^ e)
    hK (fun c => iterateFrobenius_def p e c)
  have h4L : 4 ≤ Nat.card (fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) :=
    h4.trans (le_card_fixedField_iterateFrobenius he)
  have h4S : 4 ≤ Nat.card (GaloisField p (3 * e)) := by
    rw [hK]
    exact four_le_pow_three (by omega)
  refine fundPerfect_of_all_nodes .trialityD4 n p e trivial hadm rfl ?_
  intro k
  match k with
  | ⟨0, _⟩ =>
    have hr := fundPerfect_range_le_commutator
      (CFSG.ClassicalInvolution.sl2_isPerfect h4L)
      (slLong (iterateFrobenius (GaloisField p (3 * e)) p e) hσ)
    rw [← rankOne_long_eq_range hσ] at hr
    exact hr
  | ⟨1, _⟩ =>
    have hr := fundPerfect_range_le_commutator
      (CFSG.ClassicalInvolution.sl2_isPerfect h4S)
      (slShort (iterateFrobenius (GaloisField p (3 * e)) p e) hσ)
    rw [← rankOne_short_eq_range hσ] at hr
    exact hr

end D4

end CFSG.ClassicalInvolution.ModelFacts
