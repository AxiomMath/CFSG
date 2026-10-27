module

public import CFSG.ClassicalInvolution.Phan.PhanQ49ThmS
public import CFSG.ClassicalInvolution.Phan.PhanQ47Smul
public import CFSG.ClassicalInvolution.Phan.PhanQ46StdInst
import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalSpin

public section

namespace CFSG.ClassicalInvolution.PhanQ

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.PhanP
  CFSG.ClassicalInvolution.PhanD4 CFSG.ClassicalInvolution.PhanG CFSG.ClassicalInvolution.Phan
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.Monster.B.Geometry
  CFSG.Monster.B.Geometry.ChamberSystem CFSG.ClassicalInvolution.Phan.TitsChamber
  CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.Steinberg

section SolidInput

variable {p e : ℕ} [Fact p.Prime] (M : StdModel p e)
  [Algebra (GaloisField p e) (GaloisField p (2 * e))]
  (D : KData (GaloisField p e) (GaloisField p (2 * e)) M.ε)

theorem unitaryInvolution_eq_tau (hq : 5 ≤ p ^ e) (x : GaloisField p (2 * e)) :
    unitaryInvolution (GaloisField p (2 * e)) p e x = D.τ x := by
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hF : Nat.card (GaloisField p e) = p ^ e := GaloisField.card p e he
  rw [unitaryInvolution_apply, D.tau_pow, hF]


set_option linter.unusedSectionVars false

theorem solidNull_of_phanSolid (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e) (h0 : PtStep0 M.S)
    (he : PtEdge M.S) {W : Submodule (GaloisField p (2 * e)) (V8 (GaloisField p (2 * e)))}
    (hW : PhanSolid D W)
    {x : spinGroup (quadPlus 4 (GaloisField p e)) ⧸ parab M.S {1, 2, 3}}
    (w : (ptGraph M.S).Walk x x) (hw : ∀ v ∈ w.support, lineOfPt M D hp2 hq v ≤ W) :
    SolidNull M.S h0 w := by
  have hodd := (CFSG.ClassicalInvolution.ModelFacts.card_galoisField_facts hp2 hq).1
  have h2K := two_ne_zero_gf hp2 (2 * e)
  obtain ⟨g, hg⟩ := hW.exists_conj_std_iff D hodd h2K M.hε (unitaryInvolution_eq_tau M D hq)
  rcases hg with hg | hg
  · obtain ⟨ψ, hS⟩ := exists_stdSolid_G M hp2 hq D
    obtain ⟨hR, hip, hedge, hsurj⟩ := hS.conditions hp2 hq h0 he
    refine solidNull_of_points_smul h0 hS.hrange (Set.range hS.chain.Phi) hR hip hedge g w ?_
    intro v hv
    refine hsurj _ ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective v
    have h1 := hw _ hv
    rw [lineOfPt_mk, Submodule.span_singleton_le_iff_mem] at h1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, lineOfPt_mk, Submodule.span_singleton_le_iff_mem]
    have h3 := (hg (h • z0 M.ε)).1 h1
    unfold ptVec
    rwa [NPair.mul_smul']
  · obtain ⟨ψ, hS⟩ := exists_stdSolid_H M hp2 hq D
    obtain ⟨hR, hip, hedge, hsurj⟩ := hS.conditions hp2 hq h0 he
    refine solidNull_of_points_smul h0 hS.hrange (Set.range hS.chain.Phi) hR hip hedge g w ?_
    intro v hv
    refine hsurj _ ?_
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective v
    have h1 := hw _ hv
    rw [lineOfPt_mk, Submodule.span_singleton_le_iff_mem] at h1
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, lineOfPt_mk, Submodule.span_singleton_le_iff_mem]
    have h3 := (hg (h • z0 M.ε)).1 h1
    unfold ptVec
    rwa [NPair.mul_smul']

end SolidInput

end CFSG.ClassicalInvolution.PhanQ
