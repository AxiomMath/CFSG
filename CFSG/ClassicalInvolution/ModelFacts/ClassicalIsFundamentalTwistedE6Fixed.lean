module

public import CFSG.LieType.AlgebraicGroups.ToralTwistPinningSemilinear

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Chevalley.ToralSign CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Abstract

variable {G : Type*} [Group G]

theorem map_conj_fixedPointsIn_eq (M : Subgroup G) (F Fh : G →* G) {u h : G} (hu : u ∈ M)
    (hFh : ∀ y, Fh y = h * F y * h⁻¹) (hFu : F u = h⁻¹ * u) :
    (fixedPointsIn M F).map (MulAut.conj u).toMonoidHom = fixedPointsIn M Fh := by
  ext z
  rw [Subgroup.mem_map, mem_fixedPointsIn]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyM, hyF⟩ := mem_fixedPointsIn.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨mul_mem (mul_mem hu hyM) (inv_mem hu), ?_⟩
    rw [hFh, map_mul, map_mul, map_inv, hyF, hFu]
    group
  · rintro ⟨hzM, hzF⟩
    refine ⟨u⁻¹ * z * u, mem_fixedPointsIn.2 ⟨mul_mem (mul_mem (inv_mem hu) hzM) hu, ?_⟩, ?_⟩
    · have hFz : F z = h⁻¹ * z * h := by
        have := hFh z
        rw [hzF] at this
        calc F z = h⁻¹ * (h * F z * h⁻¹) * h := by group
          _ = h⁻¹ * z * h := by rw [← this]
      rw [map_mul, map_mul, map_inv, hFz, hFu]
      group
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end Abstract

section Frobenius

variable (p : ℕ) [Fact p.Prime] {k : Type} [Field k] [CharP k p]

theorem frobTwistGL_mul_left_apply {τ : Tag} (e : ℕ) (h Q y : ModGL τ k) :
    frobTwistGL τ k p e (h * Q) y = h * frobTwistGL τ k p e Q y * h⁻¹ := by
  simp only [frobTwistGL_apply]
  group

theorem wordWeylMatrix_nil (τ : Tag) : wordWeylMatrix τ k [] = 1 := by
  simp [wordWeylMatrix]

theorem thetaMap_one {τ : Tag} (ρ : Equiv.Perm (Fin τ.rank)) (v : Fin τ.rank → ℤ) :
    thetaMap (1 : WeylGroup τ) ρ v = permLattice ρ v := by
  rw [thetaMap, one_smul]

theorem exists_frobTwistGL_diagramMap_pinnedX_of_fixed (t : TwistTag) (e : ℕ)
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) (hfix : permLattice t.perm β = β) :
    ∃ μ : kˣ, ∀ c : k, frobTwistGL t.tag k p e (diagramMap t k) (pinnedX t.tag k β c) =
      pinnedX t.tag k β ((μ : k) * c ^ (p ^ e)) := by
  obtain ⟨μ, hμ⟩ := wordWeylMatrix_mul_diagramMap_conj_pinnedX (k := k) t [] hβ
  rw [wordWeylMatrix_nil, ToralSign.wordElt_nil, thetaMap_one, hfix, one_mul] at hμ
  refine ⟨μ, fun c => ?_⟩
  rw [frobTwistGL_apply, entrywiseFrobGL_pinnedX, hμ, iterateFrobenius_def]

theorem card_fixedPointsIn_rootSubgroup_le [IsAlgClosed k] (t : TwistTag) {e : ℕ} (he : 1 ≤ e)
    {β : Fin t.tag.rank → ℤ} (hβ : IsRoot t.tag β) (hfix : permLattice t.perm β = β) :
    Nat.card (fixedPointsIn (rootSubgroup t.tag k β)
      (frobTwistGL t.tag k p e (diagramMap t k))) ≤ p ^ e := by
  classical
  obtain ⟨μ, hμ⟩ := exists_frobTwistGL_diagramMap_pinnedX_of_fixed (k := k) p t e hβ hfix
  set q := p ^ e with hq
  have hq2 : 2 ≤ q := by
    have := (Fact.out : p.Prime).two_le
    calc 2 ≤ p := this
      _ = p ^ 1 := (pow_one p).symm
      _ ≤ p ^ e := Nat.pow_le_pow_right (by omega) he
  have hμ0 : (μ : k) ≠ 0 := μ.ne_zero
  let P : Polynomial k := Polynomial.C (μ : k) * Polynomial.X ^ q - Polynomial.X
  have hdeg1 : (Polynomial.C (μ : k) * Polynomial.X ^ q).natDegree = q :=
    Polynomial.natDegree_C_mul_X_pow q (μ : k) hμ0
  have hlt : (Polynomial.X : Polynomial k).natDegree <
      (Polynomial.C (μ : k) * Polynomial.X ^ q).natDegree := by
    rw [hdeg1, Polynomial.natDegree_X]
    omega
  have hPdeg : P.natDegree = q := by
    rw [Polynomial.natDegree_sub_eq_left_of_natDegree_lt hlt, hdeg1]
  have hP0 : P ≠ 0 := by
    intro h
    rw [h, Polynomial.natDegree_zero] at hPdeg
    omega
  have hmem : ∀ g : fixedPointsIn (rootSubgroup t.tag k β)
      (frobTwistGL t.tag k p e (diagramMap t k)), g.1 ∈ rootSubgroup t.tag k β :=
    fun g => (mem_fixedPointsIn.1 g.2).1
  choose c hc using fun g : fixedPointsIn (rootSubgroup t.tag k β)
      (frobTwistGL t.tag k p e (diagramMap t k)) => mem_rootSubgroup.1 (hmem g)
  have hroot : ∀ g, c g ∈ P.roots.toFinset := by
    intro g
    have hF := (mem_fixedPointsIn.1 g.2).2
    rw [← hc g, hμ] at hF
    have h1 := pinnedX_injective t.tag k β hF
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    simp only [P, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    rw [h1, sub_self]
  have hinj : Function.Injective fun g => (⟨c g, hroot g⟩ : P.roots.toFinset) := by
    intro g g' h
    have h1 : c g = c g' := congrArg Subtype.val h
    exact Subtype.ext (by rw [← hc g, ← hc g', h1])
  calc Nat.card (fixedPointsIn (rootSubgroup t.tag k β)
        (frobTwistGL t.tag k p e (diagramMap t k))) ≤ Nat.card P.roots.toFinset :=
        Nat.card_le_card_of_injective _ hinj
    _ = P.roots.toFinset.card := Nat.card_eq_fintype_card.trans (Fintype.card_coe _)
    _ ≤ Multiset.card P.roots := Multiset.toFinset_card_le _
    _ ≤ P.natDegree := Polynomial.card_roots' P
    _ = q := hPdeg

end Frobenius

end CFSG.ClassicalInvolution.ModelFacts
