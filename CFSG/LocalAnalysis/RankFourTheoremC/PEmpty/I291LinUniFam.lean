module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUniCore
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291P65Defs
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODLinear
public import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294ODUnitary

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni

open CFSG.Open Subgroup Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification.CatalogueBHigherLinearAction (slConjugation)
open CFSG.LocalAnalysis.RankFourTheoremC (odFamily_linear odFamily_unitary_of_inputs
  l212in_projectiveSLEquivStated card_scalars_eq_gcd exists_cover_linear exists_cover_unitary
  exists_char_pow_card card_scalars_statedSU)
open CFSG.LocalAnalysis.RankFourTheoremC.I294OD (torus_commuting torus_normalized
  exists_monomial_matrices)

section Linear

variable {n : ℕ} {K : Type} [Field K]

theorem coe_pow_eq_one {p : ℕ} {B : GL (Fin n) K} (hB : B ^ p = 1) :
    (B : Matrix (Fin n) (Fin n) K) ^ p = 1 := by
  have := congrArg Units.val hB
  rwa [Units.val_pow_eq_pow_val, Units.val_one] at this

theorem exists_nonpower_scalar {p : ℕ} (hp : p.Prime) (B : GL (Fin n) K)
    (hBZ : B ^ p ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range)
    (hnp : ∀ w ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range, w ^ p ≠ B ^ p) :
    ∃ ζ : K, (∀ b : K, b ^ p ≠ ζ) ∧ (B : Matrix (Fin n) (Fin n) K) ^ p = scalar (Fin n) ζ := by
  obtain ⟨c, hc⟩ := hBZ
  refine ⟨(c : K), fun b hb => ?_, ?_⟩
  · have hb0 : b ≠ 0 := by
      rintro rfl
      have : (c : K) = 0 := by rw [← hb]; exact zero_pow hp.ne_zero
      exact c.ne_zero this
    refine hnp (GeneralLinearGroup.scalar (Fin n) (Units.mk0 b hb0)) ⟨_, rfl⟩ ?_
    rw [← hc, ← map_pow]
    congr 1
    exact Units.ext (by simpa using hb)
  · have h1 := congrArg Units.val hc
    rw [GeneralLinearGroup.coe_scalar] at h1
    rw [h1, Units.val_pow_eq_pow_val]

variable [Finite K]

theorem linear_torus {p : ℕ} (hp : p.Prime) (hn5 : 5 ≤ n) (hpK : p ∣ Nat.card K - 1)
    (B : GL (Fin n) K) (hB : B ^ p = 1) :
    ∃ f : (Fin 3 → Multiplicative (ZMod p)) →* SpecialLinearGroup (Fin n) K,
      Function.Injective ((proj n K).comp f) ∧ ∀ a, slConjugation n K B (f a) = f a := by
  obtain ⟨f, hfi, hfc, hfs⟩ := torus_commuting hp hn5 hpK (coe_pow_eq_one hB)
  refine ⟨f, ?_, fun a => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro x hx
    exact (injective_iff_map_eq_one f).1 hfi x (hfs x (proj_eq_one_iff.1 hx))
  · refine Subtype.ext ((coe_slConjugation B (f a)).trans ?_)
    calc (B : Matrix (Fin n) (Fin n) K) * (f a : Matrix (Fin n) (Fin n) K) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = ((f a : Matrix (Fin n) (Fin n) K) * B) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hfc a]
      _ = (f a : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

theorem linear_mono {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hn : p + 3 ≤ n)
    (B : GL (Fin n) K)
    (hBZ : B ^ p ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range)
    (hnp : ∀ w ∈ (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range, w ^ p ≠ B ^ p) :
    ∃ T : Subgroup (SpecialLinearGroup (Fin n) K), IsElemAbelian p T ∧
      p ^ (p + 1) ≤ Nat.card (T.map (proj n K)) ∧ ∀ t ∈ T, slConjugation n K B t ∈ T := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, hM⟩ := exists_nonpower_scalar hp B hBZ hnp
  obtain ⟨P, Q, N, π, hPQ, hQP, hMP, hN⟩ := exists_monomial_matrices hp hζ hM
  obtain ⟨T, hT, hcard, hnorm⟩ := torus_normalized hp hpK hn hPQ hQP hMP hN
  refine ⟨T, hT, hcard, fun g hg => ?_⟩
  obtain ⟨g', hg', hgg'⟩ := hnorm g hg
  have h : slConjugation n K B g = g' := by
    refine Subtype.ext ((coe_slConjugation B g).trans ?_)
    calc (B : Matrix (Fin n) (Fin n) K) * (g : Matrix (Fin n) (Fin n) K) *
          ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
        = ((g' : Matrix (Fin n) (Fin n) K) * B) *
            ((B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
          rw [hgg']
      _ = (g' : Matrix (Fin n) (Fin n) K) := by
          rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]
  rw [h]
  exact hg'

theorem linear_case (hGA : CFSG.Open.GriessAllModelsStatement) {Y : Type} [Group Y] [Finite Y]
    (L : Subgroup Y) [L.Normal] (hq : CFSG.Open.IsQuasisimple ↥L)
    (hZp : IsPGroup 5 (center ↥L))
    (hperf : ∀ (N : Subgroup Y) [N.Normal], IsPGroup 5 (Y ⧸ N) → N = ⊤)
    {x : Y} (hx : orderOf x = 5) (hx2 : CFSG.Open.pRank 5 (centralizer ({x} : Set Y)) ≤ 2)
    (hpn : 5 ∣ n) (hpK : 5 ∣ Nat.card K - 1)
    (e : ↥L ⧸ center ↥L ≃* StatedProj (StatedSL n K)) : I291P65.Is29a ↥L := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hp : Nat.Prime 5 := by norm_num
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · haveI := hq.2
      haveI : Subsingleton (StatedProj (StatedSL 0 K)) := inferInstance
      exact absurd e.injective.subsingleton (not_subsingleton _)
    · exact h
  have hn5 : 5 ≤ n := Nat.le_of_dvd hn0 hpn
  let e' : ↥L ⧸ center ↥L ≃* projectiveSL n K :=
    e.trans (l212in_projectiveSLEquivStated n K).symm
  obtain ⟨φ, hφ, hφπ⟩ := exists_cover_linear hp le_rfl hGA hq hZp (by omega) e'
  have hF := odFamily_linear hp le_rfl hpn hn0 hpK
  have hperfSL : Group.IsPerfect (SpecialLinearGroup (Fin n) K) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hnp : n = 5 := by
    refine n_eq_p_of_cover (p := 5) le_rfl hpn hn0 L hperf hx hx2 hperfSL (proj n K)
      (fun B => (slConjugation n K B).toMonoidHom) (conjAut n K)
      (GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K).range hF.central hF.comm_mem
      (fun B h => (hF.ker_eq B).1 h) e' φ hφπ (fun B s => (conjAut_proj B s).symm)
      (fun w hw B => ?_) (fun B hB => linear_torus hp hn5 hpK B hB)
      (fun hn B hBZ hnp => linear_mono hp hpK hn B hBZ hnp)
    obtain ⟨u, rfl⟩ := hw
    refine MonoidHom.ext fun g => ?_
    show slConjugation n K (GeneralLinearGroup.scalar (Fin n) u * B) g = slConjugation n K B g
    rw [map_mul, CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation_scalar,
      one_mul]
  subst hnp
  have hcard : Nat.card (proj 5 K).ker = 5 := by
    rw [ker_proj, card_scalars_eq_gcd (by norm_num), Nat.gcd_eq_left hpK]
  rcases final_of_cover (proj 5 K) e' φ hφ hφπ hcard with ⟨⟨h⟩⟩ | ⟨⟨h⟩⟩
  · exact Or.inl ⟨K, inferInstance, inferInstance, hpK,
      Or.inl ⟨h.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 5 K)⟩⟩
  · exact Or.inl ⟨K, inferInstance, inferInstance, hpK,
      Or.inr ⟨h.trans (l212in_projectiveSLEquivStated 5 K)⟩⟩

end Linear

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I291LinUni
