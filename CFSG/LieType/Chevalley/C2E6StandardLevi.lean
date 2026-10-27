module

public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.C2E6StandardFixedTorus
public import CFSG.LieType.Chevalley.GraphFixedParabolicRootFactors

public noncomputable section

namespace CFSG.LieType.Chevalley.C2E6Std

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

@[expose] def barEquiv : K ≃+* K :=
  { barHom with
    invFun := barHom
    left_inv := bar_bar
    right_inv := bar_bar }

theorem barEquiv_toRingHom : barEquiv.toRingHom = barHom := rfl

@[expose] def nativeUnion (J : Set (Fin 4)) : Set (Fin Tag.E6.rank) :=
  ⋃ i ∈ J, ((nativeOrbit i : Finset (Fin 6)) : Set (Fin 6))

theorem nativeUnion_eq (J : Set (Fin 4)) :
    nativeUnion J = TwistTag.E6.orbitUnion (foldedIndex '' J) := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨foldedIndex i, ⟨i, hi, rfl⟩, ?_⟩
    rw [← nativeOrbit_eq_orbit]
    exact hxi
  · intro hx
    obtain ⟨_, ⟨i, hi, rfl⟩, hxi⟩ := Set.mem_iUnion₂.mp hx
    refine Set.mem_iUnion₂.mpr ⟨i, hi, ?_⟩
    rw [nativeOrbit_eq_orbit]
    exact hxi

theorem mem_nativeUnion_of_two_mem {J : Set (Fin 4)} (hJ : (2 : Fin 4) ∈ J) :
    i6 2 ∈ nativeUnion J ∧ i6 4 ∈ nativeUnion J :=
  ⟨Set.mem_biUnion hJ (show (2 : Fin 6) ∈ ((nativeOrbit 2 : Finset (Fin 6)) : Set (Fin 6)) from
      Finset.mem_coe.mpr (by decide)),
    Set.mem_biUnion hJ (show (4 : Fin 6) ∈ ((nativeOrbit 2 : Finset (Fin 6)) : Set (Fin 6)) from
      Finset.mem_coe.mpr (by decide))⟩

abbrev stdRadical
    (J : Set (Fin 4)) : Subgroup (ModGL Tag.E6 K) :=
  parabolicRadical Tag.E6 K (nativeUnion J) ⊓ stdFixedGroup

abbrev stdLevi
    (J : Set (Fin 4)) : Subgroup (ModGL Tag.E6 K) :=
  subsystemGroup Tag.E6 K (nativeUnion J) ⊓ stdFixedGroup

abbrev stdLeviUnipotent
    (J : Set (Fin 4)) : Subgroup (ModGL Tag.E6 K) :=
  parabolicLeviUnipotent Tag.E6 K (nativeUnion J) ⊓ stdFixedGroup

@[expose] def stdLeviBorel
    (J : Set (Fin 4)) : Subgroup (ModGL Tag.E6 K) :=
  stdTorus ⊔ stdLeviUnipotent J

theorem stdRadical_eq
    (J : Set (Fin 4)) :
    stdRadical J = graphFixedParabolicRadical TwistTag.E6 K barHom (foldedIndex '' J) := by
  rw [stdRadical, nativeUnion_eq]
  rfl

theorem stdLeviUnipotent_eq
    (J : Set (Fin 4)) :
    stdLeviUnipotent J =
      graphFixedParabolicLeviUnipotent TwistTag.E6 K barHom (foldedIndex '' J) := by
  rw [stdLeviUnipotent, nativeUnion_eq]
  rfl

theorem rootDiagUnit_inv' (a : Fin Tag.E6.rank → Kˣ) :
    (rootDiagUnit Tag.E6 a)⁻¹ = rootDiagUnit Tag.E6 a⁻¹ :=
  inv_eq_of_mul_eq_one_right (by rw [← rootDiagUnit_mul, mul_inv_cancel, rootDiagUnit_one])

theorem conj_rootDiagUnit_mem_subsystemGroup
    (X : Set (Fin Tag.E6.rank))
    (a : Fin Tag.E6.rank → Kˣ) {g : ModGL Tag.E6 K} (hg : g ∈ subsystemGroup Tag.E6 K X) :
    rootDiagUnit Tag.E6 a * g * (rootDiagUnit Tag.E6 a)⁻¹ ∈ subsystemGroup Tag.E6 K X := by
  have hle : subsystemGroup Tag.E6 K X ≤ (subsystemGroup Tag.E6 K X).comap
      (MulAut.conj (rootDiagUnit Tag.E6 a)).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation Tag.E6 K a).1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inl rfl⟩
    · rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        (root_diagonal_conjugation Tag.E6 K a).2.1 i c]
      exact Subgroup.subset_closure ⟨i, hi, _, Or.inr rfl⟩
  exact hle hg

theorem torusGroup_le_normalizer_subsystemGroup
    (X : Set (Fin Tag.E6.rank)) :
    torusGroup Tag.E6 K ≤
      Subgroup.normalizer (subsystemGroup Tag.E6 K X : Set (ModGL Tag.E6 K)) := by
  intro h hh
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨conj_rootDiagUnit_mem_subsystemGroup X a, fun hg => ?_⟩
  have h1 := conj_rootDiagUnit_mem_subsystemGroup X a⁻¹ hg
  rwa [← rootDiagUnit_inv', inv_inv, show (rootDiagUnit Tag.E6 a)⁻¹ *
    (rootDiagUnit Tag.E6 a * g * (rootDiagUnit Tag.E6 a)⁻¹) * rootDiagUnit Tag.E6 a = g by
      group] at h1

theorem coe_parabolicLevi
    (X : Set (Fin Tag.E6.rank)) :
    (parabolicLevi Tag.E6 K X : Set (ModGL Tag.E6 K)) =
      (torusGroup Tag.E6 K : Set (ModGL Tag.E6 K)) *
        (subsystemGroup Tag.E6 K X : Set (ModGL Tag.E6 K)) :=
  Subgroup.coe_mul_of_left_le_normalizer_right _ _ (torusGroup_le_normalizer_subsystemGroup X)

theorem subsystemGroup_le_parabolicLevi
    (X : Set (Fin Tag.E6.rank)) :
    subsystemGroup Tag.E6 K X ≤ parabolicLevi Tag.E6 K X :=
  le_sup_right

theorem fixedTorusGen_mem_subsystemTorus
    {X : Set (Fin Tag.E6.rank)} (h2 : i6 2 ∈ X)
    (h4 : i6 4 ∈ X) : fixedTorusGen ∈ subsystemTorus Tag.E6 K X :=
  mul_mem (Subgroup.subset_closure ⟨i6 2, h2, _, rfl⟩) (Subgroup.subset_closure ⟨i6 4, h4, _, rfl⟩)

theorem stdTorus0_le_subsystemGroup
    {X : Set (Fin Tag.E6.rank)} (h2 : i6 2 ∈ X)
    (h4 : i6 4 ∈ X) : stdTorus0 ≤ subsystemGroup Tag.E6 K X := by
  rw [stdTorus0_eq_zpowers]
  exact Subgroup.zpowers_le.mpr (subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K)
    (A := X) (fixedTorusGen_mem_subsystemTorus h2 h4))

theorem parabolicLevi_inf_stdFixedGroup
    {X : Set (Fin Tag.E6.rank)} (h2 : i6 2 ∈ X)
    (h4 : i6 4 ∈ X) :
    parabolicLevi Tag.E6 K X ⊓ stdFixedGroup = subsystemGroup Tag.E6 K X ⊓ stdFixedGroup := by
  refine le_antisymm (fun g hg => ⟨?_, hg.2⟩)
    (inf_le_inf_right _ (subsystemGroup_le_parabolicLevi X))
  have hgΓ : g ∈ twistedFixedGroup TwistTag.E6 K barHom := hg.2
  have hgM : g ∈ (parabolicLevi Tag.E6 K X : Set (ModGL Tag.E6 K)) := hg.1
  rw [coe_parabolicLevi] at hgM
  obtain ⟨h, hh, s, hs, rfl⟩ := hgM
  have hs' : s ∈ (subsystemGroup Tag.E6 K X : Set (ModGL Tag.E6 K)) := hs
  rw [(subsystem_root_group_bruhat Tag.E6 K X).2.2.1] at hs'
  simp only [Set.mem_iUnion] at hs'
  obtain ⟨w, -, hsw⟩ := hs'
  obtain ⟨_, ⟨b, hb, _, rfl, rfl⟩, v, hv, rfl⟩ := hsw
  beta_reduce at hs hgΓ ⊢
  have hhB : h * b ∈ borelGroup Tag.E6 K :=
    mul_mem (Subgroup.mem_sup_left hh) (subsystemBorel_le_borelGroup hb)
  have hvU : v ∈ rootSpan Tag.E6 K (inversionSet w) := hv
  have hgw : h * (b * canonicalRep (coxeterSystem Tag.E6) K w * v) ∈ bruhatCell Tag.E6 K w := by
    rw [show h * (b * canonicalRep (coxeterSystem Tag.E6) K w * v) =
      h * b * canonicalRep (coxeterSystem Tag.E6) K w * v by group]
    exact (bijOn_bruhatCell (K := K) w).1 (Set.mk_mem_prod hhB hvU)
  obtain ⟨-, b', hb', u', hu', heq⟩ := exists_fixed_bruhat_factor barHom_surjective hgΓ hgw
  have hinj := (bijOn_bruhatCell (K := K) w).2.1 (Set.mk_mem_prod hb'.1 hu'.1)
    (Set.mk_mem_prod hhB hvU) (heq.trans (by rw [← mul_assoc, ← mul_assoc]; try rfl))
  have e : b' = h * b := congrArg Prod.fst hinj
  have hb'' : h * b ∈ graphFixedBorel TwistTag.E6 K barHom := e ▸ hb'
  have hb3 : h * b ∈ (graphFixedTorus TwistTag.E6 K barHom : Set (ModGL TwistTag.E6.tag K)) *
      (graphFixedPosUnipotent TwistTag.E6 K barHom : Set (ModGL TwistTag.E6.tag K)) := by
    rw [← graphFixedBorel_eq_mul barHom_surjective]
    exact hb''
  obtain ⟨h₀, hh₀, u₀, hu₀, hhb⟩ := hb3
  have hb4 : b ∈ (subsystemTorus Tag.E6 K X : Set (ModGL Tag.E6 K)) *
      (parabolicLeviUnipotent Tag.E6 K X : Set (ModGL Tag.E6 K)) := by
    rw [← coe_subsystemBorel]
    exact hb
  obtain ⟨t, ht, vX, hvX, rfl⟩ := hb4
  beta_reduce at hhb hs ⊢
  obtain ⟨-, -, -, -, -, -, huniq, -⟩ := triangular_borel_structure.{0, 0} Tag.E6 K
  have hu := huniq (h * t) (mul_mem hh (subsystemTorus_le_torusGroup ht)) h₀ hh₀.1 vX
    (parabolicLeviUnipotent_le_posUnipotent X hvX) u₀ hu₀.1 (by rw [mul_assoc]; exact hhb.symm)
  have hht : h * t ∈ subsystemGroup Tag.E6 K X :=
    hu.1 ▸ stdTorus0_le_subsystemGroup h2 h4 hh₀
  have hhS : h ∈ subsystemGroup Tag.E6 K X := by
    rw [show h = h * t * t⁻¹ by group]
    exact mul_mem hht
      (inv_mem (subsystemTorus_le_subsystemGroup (τ := Tag.E6) (K := K) (A := X) ht))
  exact mul_mem hhS hs

theorem stdLevi_eq
    {J : Set (Fin 4)} (hJ : (2 : Fin 4) ∈ J) :
    stdLevi J = graphFixedParabolicLevi TwistTag.E6 K barHom (foldedIndex '' J) := by
  obtain ⟨h2, h4⟩ := mem_nativeUnion_of_two_mem hJ
  rw [graphFixedParabolicLevi, ← nativeUnion_eq]
  change subsystemGroup Tag.E6 K (nativeUnion J) ⊓ stdFixedGroup =
    parabolicLevi Tag.E6 K (nativeUnion J) ⊓ stdGroup
  rw [← stdFixedGroup_eq_stdGroup, parabolicLevi_inf_stdFixedGroup h2 h4]

end CFSG.LieType.Chevalley.C2E6Std
