module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.R9
public import CFSG.RankThree.PartTwo.KFacts.L34Aut
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound

open CFSG.RankThree.PartTwo.KFacts.L34
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
open CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourOuter (diagGL)
open scoped commutatorElement

theorem exists_equiv_projectiveSL_of_l34Index {d : TauCeti.ValidLieTypeIndex}
    (hd : IsL34Index d) {K : Type} [Group K]
    (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    ∃ (F : Type) (_ : Field F), Nat.card F = 4 ∧ Nonempty (K ≃* projectiveSL 3 F) := by
  obtain ⟨q, hq2, hqe, hd'⟩ := hd
  obtain ⟨⟨d, hv⟩, rfl⟩ : ∃ d' : {d : TauCeti.LieTypeIndex // d.Valid}, d' = d := ⟨d, rfl⟩
  simp only at hd'
  subst hd'
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  refine ⟨GaloisField q.p q.exponent, inferInstance, ?_, ⟨?_⟩⟩
  · rw [GaloisField.card q.p q.exponent q.exponent_pos.ne', hq2, hqe]
    norm_num
  · exact ((e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 2 q hv)).trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 3 (GaloisField q.p q.exponent))).trans
      (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3
        (GaloisField q.p q.exponent)).symm

theorem pow_three_of_isPGroup_mulAut {k : Type*} [Field k] (hk : Nat.card k = 4)
    (γ : MulAut (projectiveSL 3 k)) (hγ : IsPGroup 3 (Subgroup.zpowers γ)) : γ ^ 3 = 1 := by
  have : Finite (MulAut (projectiveSL 3 k)) :=
    Nat.finite_of_card_ne_zero (by rw [card_mulAut hk]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set x := conjAut 3 k (diagGL u)
  set y := (MulAut.conj (bP : projectiveSL 3 k) : MulAut (projectiveSL 3 k))
  have h3 := LinearThreeFourOuter.units_pow_three hk u
  have hx3 : x ^ 3 = 1 := by
    rw [← map_pow, pow_three, LinearThreeFourOuter.diagGL_mul, LinearThreeFourOuter.diagGL_mul,
      ← pow_three, h3, LinearThreeFourOuter.diagGL_one, map_one]
  have hy3 : y ^ 3 = 1 := by
    rw [← map_pow, pow_three_of_mem_eZero hk bP_mem_eZero, map_one]
  have hab : aP u * bP = bP * aP u := commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero
  have hxa : x (aP u)⁻¹ = (aP u)⁻¹ := by rw [map_inv, conjAut_diagGL_aP]
  have hz : ⁅x, y⁆ = MulAut.conj (aP u)⁻¹ := by
    rw [commutatorElement_def, CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv,
      conjAut_diagGL_bP hk hu, ← map_inv, ← map_mul]
    congr 1
    calc bP * (aP u)⁻¹ * bP⁻¹ = bP * ((aP u)⁻¹ * bP⁻¹) := by group
      _ = bP * (bP⁻¹ * (aP u)⁻¹) := by
          rw [show (aP u)⁻¹ * bP⁻¹ = (bP * aP u)⁻¹ by group, ← hab]
          group
      _ = (aP u)⁻¹ := by group
  have hzx : Commute ⁅x, y⁆ x := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹
    have := CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv x (aP u)⁻¹
    rw [hxa] at this
    calc MulAut.conj (aP u)⁻¹ * x = x * MulAut.conj (aP u)⁻¹ * x⁻¹ * x := by rw [this]
      _ = x * MulAut.conj (aP u)⁻¹ := by group
  have hzy : Commute ⁅x, y⁆ y := by
    rw [hz]
    show MulAut.conj (aP u)⁻¹ * MulAut.conj bP = MulAut.conj bP * MulAut.conj (aP u)⁻¹
    rw [← map_mul, ← map_mul]
    congr 1
    calc (aP u)⁻¹ * bP = (aP u)⁻¹ * (bP * aP u) * (aP u)⁻¹ := by group
      _ = (aP u)⁻¹ * (aP u * bP) * (aP u)⁻¹ := by rw [hab]
      _ = bP * (aP u)⁻¹ := by group
  have hz1 : ⁅x, y⁆ ≠ 1 := by
    rw [hz]
    intro h
    exact aP_ne_one hk hu (inv_eq_one.mp (conj_injective hk (h.trans (map_one _).symm)))
  have hL : (Nat.card (MulAut (projectiveSL 3 k))).factorization 3 = 3 := by
    rw [card_mulAut hk]
    exact CFSG.RankThree.Asc83Table.factorization_eq_of_eq Nat.prime_three
      (show 241920 = 3 ^ 3 * 8960 by norm_num) (by norm_num)
  have hP := CFSG.RankThree.Asc83Table.ex27_card_sylow hx3 hy3 hzx hzy hz1 hL
  obtain ⟨g, hg⟩ := CFSG.RankThree.Asc83Table.exists_map_conj_le hP hγ
  have hmem : g * γ * g⁻¹ ∈ Subgroup.closure ({x, y} : Set (MulAut (projectiveSL 3 k))) :=
    hg ⟨γ, Subgroup.mem_zpowers γ, rfl⟩
  have hcube := CFSG.RankThree.Asc83Table.pow_three_eq_one_of_mem hx3 hzx hzy hy3 hmem
  have h1 : MulAut.conj g (γ ^ 3) = 1 := by
    rw [map_pow]
    exact hcube
  exact (map_eq_one_iff _ (MulAut.conj g).injective).mp h1

theorem kFactL34Exp3 : KFactL34Exp3 := by
  intro d hd X _ _ K hKn hKC ⟨e⟩ x hx
  have : K.Normal := hKn
  obtain ⟨F, _, hF, ⟨ψ⟩⟩ := exists_equiv_projectiveSL_of_l34Index hd e
  let θ : X →* MulAut K := MulAut.conjNormal
  have hθ : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hmem : g ∈ Subgroup.centralizer (K : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have := congrArg (fun φ : MulAut K => ((φ ⟨k, hk⟩ : K) : X)) hg
      have h2 : g * k * g⁻¹ = k := by
        have h3 : ((MulAut.conjNormal g : MulAut K) ⟨k, hk⟩ : X) = g * k * g⁻¹ :=
          MulAut.conjNormal_apply g ⟨k, hk⟩
        rw [← h3]
        exact this
      calc k * g = g * k * g⁻¹ * g := by rw [h2]
        _ = g * k := by group
    rw [hKC] at hmem
    exact hmem
  let ι : X →* MulAut (projectiveSL 3 F) := (MulAut.congr ψ).toMonoidHom.comp θ
  have hι : Function.Injective ι := (MulAut.congr ψ).injective.comp hθ
  have hxι : IsPGroup 3 (Subgroup.zpowers (ι x)) := by
    rw [← MonoidHom.map_zpowers]
    exact hx.map ι
  have hcube := pow_three_of_isPGroup_mulAut hF (ι x) hxι
  apply hι
  rw [map_pow, hcube, map_one]

end CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
