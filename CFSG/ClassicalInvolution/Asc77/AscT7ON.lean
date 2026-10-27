module

public import CFSG.ClassicalInvolution.Asc77.AscT7OM
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Outer
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift

public section

namespace CFSG.ClassicalInvolution.G2D4Models.Twin

open CFSG.ClassicalInvolution.ModelFacts.Orth15.T7O
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.ClassicalInvolution.ModelFacts.Orth15 CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalInvolution.Models.Transfer CFSG.ClassicalInvolution.RouteD

section SqGlue

variable {H : Type} [Group H]

@[expose] def SqOn (L : Subgroup H) (S : Set H) (k₀ z : H) : Prop :=
  k₀ * k₀ = z → ∀ v : ↥(inducedAutOn L),
    (∀ c ∈ S, ∀ hc : c ∈ Subgroup.normalizer (L : Set H),
      v * toInducedAutOn L ⟨c, hc⟩ = toInducedAutOn L ⟨c, hc⟩ * v) →
    ∀ (hz : z ∈ Subgroup.normalizer (L : Set H)) (hk : k₀ ∈ Subgroup.normalizer (L : Set H)),
      v * v = toInducedAutOn L ⟨z, hz⟩ →
      alphaOf (Subgroup.closure ({toInducedAutOn L ⟨k₀, hk⟩ * v, toInducedAutOn L ⟨z, hz⟩} :
        Set ↥(inducedAutOn L))) = ⊥

theorem sqOn_congr {L L' : Subgroup H} (hL : L = L') {S S' : Set H} (hS : S = S') {k₀ k₀' z z' : H}
    (hk : k₀ = k₀') (hz : z = z') (h : SqOn L S k₀ z) : SqOn L' S' k₀' z' := by
  subst hL hS hk hz
  exact h

theorem sq_of_sqOn {K : Type} [Group K] (ψ : K →* H) (R R' : Subgroup K) (x k : K)
    (h : SqOn ψ.range ((R.map ψ : Set H) ∪ (R'.map ψ : Set H)) (ψ k) (ψ x))
    (hkk : ψ k * ψ k = ψ x) (v : ↥(inducedAutOn ψ.range))
    (hvR : ∀ r ∈ R, v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvR' : ∀ r ∈ R', v * FrameVertex.innerHom ψ r = FrameVertex.innerHom ψ r * v)
    (hvv : v * v = FrameVertex.innerHom ψ x) :
    alphaOf (Subgroup.closure ({FrameVertex.innerHom ψ k * v, FrameVertex.innerHom ψ x} :
      Set ↥(inducedAutOn ψ.range))) = ⊥ := by
  refine h hkk v ?_ (mem_normalizer_range ψ x) (mem_normalizer_range ψ k) hvv
  rintro c (⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩) hc
  · exact hvR r hr
  · exact hvR' r hr

end SqGlue

section D4Sq

variable {p f : ℕ} [Fact p.Prime]

theorem sqOn_of_pair_ord_d4 (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) {H : Type} [Group H] [Finite H]
    {ψ : spinGroup (quadPlus 4 (GaloisField p f)) →* H}
    {R R' : Subgroup (spinGroup (quadPlus 4 (GaloisField p f)))}
    {x x' : spinGroup (quadPlus 4 (GaloisField p f))}
    (hpair : TwinPairOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩
      ψ R R' x x')
    (hord : spinAction (quadPlus 4 (GaloisField p f)) x =
      spinAction (quadPlus 4 (GaloisField p f)) x')
    {k : spinGroup (quadPlus 4 (GaloisField p f))} (hk : k ∈ R) :
    SqOn ψ.range ((R.map ψ : Set H) ∪ (R'.map ψ : Set H)) (ψ k) (ψ x) := by
  have hn3 : 3 ≤ 4 := by norm_num
  obtain ⟨hodd, -⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  have hdim : Module.finrank (GaloisField p f) (Fin 4 ⊕ Fin 4 → GaloisField p f) = 8 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
  have : Group.IsPerfect (spinGroup (quadPlus 4 (GaloisField p f))) :=
    isPerfect_spinGroup_quadPlus hn3
  obtain ⟨hRp, hR'p, hRc, hR'c, hinj, hinj'⟩ := d4PairData hp2 hq hadm hpair
  have hlift := liftSimFr_of_d4FixLift hfl hp2 hq ψ hpair.ker
  intro hkk v hvS hz hk' hvv
  have hvR : ∀ r ∈ R, v * spinInd ψ r = spinInd ψ r * v := fun r hr =>
    hvS (ψ r) (Or.inl ⟨r, hr, rfl⟩) (mem_normalizer_range ψ r)
  have hvR' : ∀ r ∈ R', v * spinInd ψ r = spinInd ψ r * v := fun r hr =>
    hvS (ψ r) (Or.inr ⟨r, hr, rfl⟩) (mem_normalizer_range ψ r)
  exact alphaOf_spin_twin_pair_sq hodd (five_le_card_galoisField hq)
    (nondegenerate_polarBilin_quadPlus 4 _) (range_spinAction_quadPlus hn3) (by omega) hRp hR'p
    hRc hR'c hinj hinj' hpair.ne hpair.hx hpair.hx2 hpair.hx1 hpair.hx' hpair.hx'2 hpair.hx'1
    hord hpair.ker hlift hk hkk v hvR hvR' hvv

theorem twinSqAlphaOn_d4 (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) :
    TwinSqAlphaOn .POmegaPlus
      ⟨spinGroup (quadPlus 4 (GaloisField p f)), plusDatum 4 (GaloisField p f) (by norm_num)⟩ := by
  obtain ⟨-, h4⟩ := CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq
  obtain ⟨-, hF⟩ := CFSG.ClassicalInvolution.RouteD.card_galoisField_of_four_le
    (p := p) (f := f) (by omega)
  obtain ⟨ρ, hρ⟩ := exists_triality hadm h4 hF
  intro H _ _ ψ R R' x x' hpair k hk hkk v hvR hvR' hvv
  obtain ⟨hc, hc2⟩ := twinPairOn_central_div hpair
  obtain ⟨σ, hσ, hθ⟩ := exists_aut_ordinary hp2 hadm ρ hρ hc hc2
  have hpair' := twinPairOn_transport hpair σ hσ
  have hord : spinAction (quadPlus 4 (GaloisField p f)) (σ x) =
      spinAction (quadPlus 4 (GaloisField p f)) (σ x') := by
    rw [map_mul, map_inv, map_mul, map_inv] at hθ
    exact mul_inv_eq_one.mp hθ
  have hO' := sqOn_of_pair_ord_d4 hfl hp2 hq hadm hpair' hord (k := σ k) ⟨k, hk, rfl⟩
  have hr := range_comp_symm ψ σ
  have hO : SqOn ψ.range ((R.map ψ : Set H) ∪ (R'.map ψ : Set H)) (ψ k) (ψ x) := by
    refine sqOn_congr hr ?_ ?_ ?_ hO'
    · rw [map_map_comp_symm, map_map_comp_symm]
    · simp
    · simp
  exact sq_of_sqOn ψ R R' x k hO hkk v hvR hvR' hvv

theorem twinSqAlpha_d4 (hfl : D4FixLift p f) (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hadm : StatedLieAdmissible .POmegaPlus 4 p f) : TwinSqAlpha p f .POmegaPlus 4 := by
  have key : ∀ M : LieUniversal, M = ⟨spinGroup (quadPlus 4 (GaloisField p f)),
      plusDatum 4 (GaloisField p f) (by norm_num)⟩ → TwinSqAlphaOn .POmegaPlus M := by
    intro M hM
    subst hM
    exact twinSqAlphaOn_d4 hfl hp2 hq hadm
  exact key _ (CFSG.ClassicalInvolution.ModelFacts.modelUniv_POmegaPlus (by norm_num))

end D4Sq

end CFSG.ClassicalInvolution.G2D4Models.Twin
