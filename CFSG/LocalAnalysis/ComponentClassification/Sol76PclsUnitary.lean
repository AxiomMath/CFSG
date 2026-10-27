module

public import CFSG.LocalAnalysis.ComponentClassification.Sol76PclsLinear
public import CFSG.LieType.Steinberg.CentralExt.UnitaryHigher
public import CFSG.LieType.Universal.Unitary.Comparison
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoProjectiveFormulas
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.StrongEmbedding
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.SLB4A.Basic
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
public import CFSG.Walter.J1
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.ComponentClassification.Sol76T13.R12.Pcls

open CFSG Subgroup Matrix CFSG.Assembly.LowTwoRank

section Signs

variable {n : ℕ} {F : Type} [Field F]

theorem toGL_slSign_mem_statedSU {q : ℕ} (hq : Odd q) {ε : Fin n → F} (hε : ∏ i, ε i = 1)
    (h2 : ∀ i, ε i * ε i = 1) :
    Matrix.SpecialLinearGroup.toGL (slSign ε hε) ∈ StatedSU n q F := by
  apply Subgroup.subset_closure
  obtain ⟨k, rfl⟩ := hq
  refine ⟨?_, ?_⟩
  · change (diagonal ε).det = 1
    rw [det_diagonal, hε]
  · change ((diagonal ε).map (· ^ (2 * k + 1)))ᵀ * diagonal ε = 1
    rw [diagonal_map (by simp), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hpow : ε i ^ (2 * k + 1) = ε i := by rw [pow_succ, pow_mul, sq, h2, one_pow, one_mul]
    rw [hpow, h2]

theorem toGL_slSign_not_mem_scalars {ε : Fin n → F} (hε : ∏ i, ε i = 1) {i j : Fin n}
    (hij : ε i ≠ ε j) :
    Matrix.SpecialLinearGroup.toGL (slSign ε hε) ∉ StatedScalars (Fin n) F := by
  rintro ⟨c, hc⟩
  have hm := congrArg (fun g : GL (Fin n) F => (g : Matrix (Fin n) (Fin n) F)) hc
  have hi := congrFun (congrFun hm i) i
  have hj := congrFun (congrFun hm j) j
  simp only [Matrix.GeneralLinearGroup.scalar, Units.coe_map] at hi hj
  change Matrix.scalar (Fin n) (c : F) i i = diagonal ε i i at hi
  change Matrix.scalar (Fin n) (c : F) j j = diagonal ε j j at hj
  simp only [scalar_apply, diagonal_apply_eq] at hi hj
  exact hij (hi.symm.trans hj)

end Signs

section Covers

variable {Q : Type} [Group Q] [Finite Q]

theorem three_le_pRank_of_PSU (hO : pPrimeCore 2 Q = ⊥) {z : Q} (hzZ : z ∈ center Q)
    (hz2 : orderOf z = 2) {n : ℕ} (hn : 3 ≤ n) {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) (hp2 : p ≠ 2)
    (e : Q ⧸ center Q ≃* StatedProj (StatedSU n (p ^ f) F)) : 3 ≤ CFSG.pRank 2 Q := by
  set πQ := e.toMonoidHom.comp (QuotientGroup.mk' (center Q)) with hπQ
  have hπQs : Function.Surjective πQ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerQ := ker_quotientMap e
  have h2Q : IsPGroup 2 πQ.ker := hkerQ ▸ isPGroup_center_of_pPrimeCore_eq_bot hO
  set πG : StatedSU n (p ^ f) F →* StatedProj (StatedSU n (p ^ f) F) := QuotientGroup.mk' _
    with hπG
  have hπG1 : ∀ x, πG x = 1 ↔ (x : GL (Fin n) F) ∈ StatedScalars (Fin n) F := fun x => by
    rw [hπG, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  obtain ⟨s, hs⟩ : ∃ s : StatedSU n (p ^ f) F →* ↥(pullbackSub πG πQ),
      ∀ x, pullbackFst πG πQ (s x) = x := by
    set ψ := CFSG.LieType.Universal.Unitary.equivStatedSU hF n
    set π := pullbackFst πG πQ
    have hker : (ψ.symm.toMonoidHom.comp π).ker = π.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        map_eq_one_iff _ ψ.symm.injective]
    obtain ⟨s, hs, -⟩ := CFSG.LieType.Steinberg.su_central_two_extension_splitting hF hp2
      (by omega) (π := ψ.symm.toMonoidHom.comp π)
      (ψ.symm.surjective.comp (pullbackFst_surjective hπQs))
      (hker ▸ pullbackFst_ker_le_center hkerQ.le) (hker ▸ isPGroup_pullbackFst_ker h2Q)
    exact ⟨s.comp ψ.symm.toMonoidHom, fun g => ψ.symm.injective (hs (ψ.symm g))⟩
  obtain ⟨τ, hτ⟩ := exists_lift_of_section hs
  have hq : Odd (p ^ f) := (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hn1 : (-1 : F) ≠ 1 := by
    intro h
    have h2F : (2 : F) = 0 := by linear_combination -h
    have := (CharP.cast_eq_zero_iff F p 2).mp (by exact_mod_cast h2F)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp this)
  obtain ⟨ε, δ, hε, hδ, hε2, hδ2, ⟨i, j, hij⟩, ⟨i', j', hij'⟩, ⟨i'', j'', hij''⟩⟩ :=
    exists_sign_pair hn hn1
  have hεδ2 : ∀ l, (ε * δ) l * (ε * δ) l = 1 := fun l => by
    simp only [Pi.mul_apply]
    calc ε l * δ l * (ε l * δ l) = (ε l * ε l) * (δ l * δ l) := by ring
      _ = 1 := by rw [hε2, hδ2, one_mul]
  have hεδ : ∏ l, (ε * δ) l = 1 := by
    simp only [Pi.mul_apply]
    rw [Finset.prod_mul_distrib, hε, hδ, one_mul]
  set a : StatedSU n (p ^ f) F := ⟨_, toGL_slSign_mem_statedSU hq hε hε2⟩ with ha
  set b : StatedSU n (p ^ f) F := ⟨_, toGL_slSign_mem_statedSU hq hδ hδ2⟩ with hb
  have hab : a * b = ⟨_, toGL_slSign_mem_statedSU hq hεδ hεδ2⟩ :=
    Subtype.ext (by simp only [ha, hb, Subgroup.coe_mul, ← map_mul, slSign_mul])
  have hz1 : z ≠ 1 := by rintro rfl; rw [orderOf_one] at hz2; omega
  have hzz : z * z = 1 := by rw [← pow_two, ← hz2, pow_orderOf_eq_one]
  refine three_le_pRank_of_four_group hτ (a := a) (b := b) ?_ ?_ ?_ ?_ ?_ ?_ hzZ hzz hz1
    (by rw [← MonoidHom.mem_ker, hkerQ]; exact hzZ)
  · exact Subtype.ext (by simp only [ha, Subgroup.coe_mul, ← map_mul, slSign_mul_self hε hε2,
      map_one, Subgroup.coe_one])
  · exact Subtype.ext (by simp only [hb, Subgroup.coe_mul, ← map_mul, slSign_mul_self hδ hδ2,
      map_one, Subgroup.coe_one])
  · exact Subtype.ext (by simp only [ha, hb, Subgroup.coe_mul, ← map_mul, slSign_comm])
  · rw [Ne, hπG1]; exact toGL_slSign_not_mem_scalars hε hij
  · rw [Ne, hπG1]; exact toGL_slSign_not_mem_scalars hδ hij'
  · rw [hab, Ne, hπG1]; exact toGL_slSign_not_mem_scalars _ hij''

end Covers

end CFSG.ComponentClassification.Sol76T13.R12.Pcls
