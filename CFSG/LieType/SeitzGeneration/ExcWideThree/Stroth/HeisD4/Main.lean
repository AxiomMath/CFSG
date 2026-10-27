module

public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Decomp
public import CFSG.LieType.SeitzGeneration.ExcWideThree.Stroth.HeisD4.Lift

public noncomputable section

namespace CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis


section Conj

variable {L : Type} [Field L] [IsAlgClosed L]

theorem map_conj_heisM {a : Fin Tag.E6.rank → Lˣ} {s : WeylGroup Tag.E6}
    (hs : ∀ α, IsRoot Tag.E6 α → (rootChar a α = 1 ↔ s • α ∈ parabolicRoots Tag.E6 d4Support)) :
    (heisM a).map (MulAut.conj (canonicalRep (coxeterSystem Tag.E6) L s)).toMonoidHom =
      torusGroup Tag.E6 L ⊔ subsystemGroup Tag.E6 L d4Support := by
  have hT := map_conj_eq_of_mem_normalizer (canonicalRep_mem_normalizer (R := L) s)
  have hS := (canonical_weyl_root_transport Tag.E6 L).1 s (rootCharKernel a) fun α hα => hα.1
  have himg : (fun α => s • α) '' rootCharKernel a = parabolicRoots Tag.E6 d4Support := by
    ext β
    constructor
    · rintro ⟨α, ⟨hα, hχ⟩, rfl⟩
      exact (hs α hα).1 hχ
    · intro hβ
      have hr : IsRoot Tag.E6 (s⁻¹ • β) := IsRoot.smul hβ.1 s⁻¹
      refine ⟨s⁻¹ • β, ⟨hr, (hs _ hr).2 (by rwa [smul_inv_smul])⟩, smul_inv_smul s β⟩
  rw [← toralRootGroup_eq_heisM]
  show (torusGroup Tag.E6 L ⊔ rootSpan Tag.E6 L (rootCharKernel a)).map _ = _
  rw [Subgroup.map_sup, hT, hS, himg, subsystemGroup_eq_rootSpan]

end Conj

end CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

namespace CFSG.LieType.SeitzGeneration.ExcWideThree

open CFSG.LieType.SeitzGeneration.ExcWideThree.HeisD4

open CFSG.LieType.SeitzGeneration.ExcHighThree CFSG.HardMathSupport.Timmesfeld.Torality
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.Steinberg
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.W2
  CFSG.RankThree.Chevalley
  CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.E6Heis



theorem e6HeisFrameFixedEltD_holds : E6HeisFrameFixedEltD := by
  intro K _ _ hK3 hK4 E hE hcard hd F hD
  classical
  obtain ⟨y', hyN, ⟨m0, hm0, hy'm0⟩, hy'3, hy'F, hx⟩ := frame_straighten hK4 hE F
  obtain ⟨s, hs, hw₀, hsh₀⟩ := stdPosition hD
  set ns := canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) s with hns
  have hnsF : Units.map (entrywiseHom F.Fr) ns = ns :=
    E8Lift.units_map_entrywiseHom_canonicalRep F.Fr s
  have hconj := map_conj_heisM (L := AlgebraicClosure K) hs
  set y'' := ns * y' * ns⁻¹ with hy''
  have hy''F : Units.map (entrywiseHom F.Fr) y'' = y'' := by
    rw [hy'', map_mul, map_mul, map_inv, hnsF, hy'F]
  have hy''3 : y'' ^ 3 = 1 := by
    have := conj_pow (a := ns) (b := y') (i := 3)
    rw [hy'', this, hy'3]
    group
  set g := ns * canonicalRep (coxeterSystem Tag.E6) (AlgebraicClosure K) F.w * ns⁻¹ with hg
  have hm''mem : ns * m0 * ns⁻¹ ∈
      torusGroup Tag.E6 (AlgebraicClosure K) ⊔
        subsystemGroup Tag.E6 (AlgebraicClosure K) d4Support := by
    rw [← hconj]
    exact ⟨m0, hm0, rfl⟩
  have hy''eq : y'' = (ns * m0 * ns⁻¹) * g := by
    rw [hy'', hy'm0, hg]
    group
  have hgmono : g ∈ monomialSubgroup Tag.E6 (AlgebraicClosure K) :=
    mul_mem (mul_mem (canonicalRep_mem_monomialSubgroup' s)
      (canonicalRep_mem_monomialSubgroup' F.w)) (inv_mem (canonicalRep_mem_monomialSubgroup' s))
  have hgmaps : MapsRootLines g (s * F.w * s⁻¹) :=
    ((mapsRootLines_canonicalRep s).mul (mapsRootLines_canonicalRep F.w)).mul
      (mapsRootLines_canonicalRep s).inv
  obtain ⟨ε, hε, m, hm, hgeq⟩ := mono_decomp hgmono hgmaps hw₀ hsh₀
  have hmm : (ns * m0 * ns⁻¹) * m ∈
      torusGroup Tag.E6 (AlgebraicClosure K) ⊔
        subsystemGroup Tag.E6 (AlgebraicClosure K) d4Support :=
    mul_mem hm''mem hm
  have hy''β : y'' = ((ns * m0 * ns⁻¹) * m) * d4TrialityRep (AlgebraicClosure K) ^ ε := by
    rw [hy''eq, hgeq]
    group
  obtain ⟨x'', hxQ, hx1, hxℓ, hxF, hcomm⟩ := exists_fixed_ell_std hK3 F.Fr F.hFr hε hmm hy''β
    hy''F hy''3
  have hxM : ns⁻¹ * x'' * ns ∈ heisM F.a := by
    have hxT : x'' ∈ (heisM F.a).map (MulAut.conj ns).toMonoidHom := by
      rw [hconj]
      exact Subgroup.mem_sup_right hxQ
    obtain ⟨g', hg', hg'x⟩ := hxT
    have : g' = ns⁻¹ * x'' * ns := by
      rw [← hg'x]
      simp [MulAut.conj_apply]
      group
    rw [← this]
    exact hg'
  refine hx (ns⁻¹ * x'' * ns) hxM ?_ ?_ ?_ ?_
  · intro h
    apply hx1
    have : x'' = ns * (ns⁻¹ * x'' * ns) * ns⁻¹ := by group
    rw [this, h]
    group
  · have := conj_pow (a := ns⁻¹) (b := x'') (i := ringChar K)
    rw [inv_inv] at this
    rw [this, hxℓ]
    group
  · rw [map_mul, map_mul, map_inv, hnsF, hxF]
  · have h2 : y'' * x'' = x'' * y'' := hcomm
    rw [hy''] at h2
    show (ns⁻¹ * x'' * ns) * y' = y' * (ns⁻¹ * x'' * ns)
    calc (ns⁻¹ * x'' * ns) * y' = ns⁻¹ * (x'' * (ns * y' * ns⁻¹)) * ns := by group
      _ = ns⁻¹ * ((ns * y' * ns⁻¹) * x'') * ns := by rw [← h2]
      _ = y' * (ns⁻¹ * x'' * ns) := by group

end CFSG.LieType.SeitzGeneration.ExcWideThree
