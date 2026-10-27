module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiChevOrbitSwapDefs
public import CFSG.Open.StatedDefs
public import CFSG.Quasithin.Recognition.CertU33DcPG
import CFSG.Mathlib.GroupTheory.Automorphism.FixOvergroupsIndexTwo
import CFSG.LocalAnalysis.StandardType.ChevTwoMarking
import CFSG.Quasithin.EmptyFaithful.SBc17Ent3
import CFSG.Quasithin.Recognition.CertR2aBridges
import CFSG.Quasithin.Recognition.CertU33AutBound
import CFSG.Quasithin.Recognition.CertU33Phi
import CFSG.Quasithin.Recognition.CertU33Psu
import CFSG.GroupTheory.SylowIntersectionControl.GomiChevAtomTransport
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Foundations
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Reduction
public import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Quasithin.Background.F2Equiv
import CFSG.Quasithin.Recognition.CertU33Wreath

public section

namespace CFSG.GroupTheory

open CFSG.Quasithin CFSG.ABGLocalTools Subgroup
open scoped Pointwise

private noncomputable abbrev u33T :
    Subgroup U33G := u33Data.T

private noncomputable abbrev u33Stab :
    Subgroup (MulAut U33G) := MulAction.stabilizer (MulAut U33G) u33SylowT

private theorem mem_u33Stab_iff
    (φ : MulAut U33G) :
    φ ∈ u33Stab ↔ u33T.map φ.toMonoidHom = u33T := by
  constructor
  · intro h
    exact map_T_of_mem_stabilizer h
  · intro h
    rw [MulAction.mem_stabilizer_iff]
    apply Sylow.ext
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    exact h

private theorem map_conj_eq_self_of_mem_normalizer {C : Subgroup U33G} {g : U33G}
    (hC : g ∈ Subgroup.normalizer (C : Set U33G)) :
    C.map (MulAut.conj g).toMonoidHom = C := by
  ext x
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hC y).mp hy
  · intro hx
    refine ⟨g⁻¹ * x * g, ?_, by group⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hC) x).mp hx
    simpa using this

private theorem conj_mem_u33Stab
    (g : U33G)
    (hg : g ∈ Subgroup.normalizer (u33T : Set U33G)) : MulAut.conj g ∈ u33Stab :=
  (mem_u33Stab_iff (MulAut.conj g)).mpr (map_conj_eq_self_of_mem_normalizer hg)

private theorem map_eq_self_of_mapsTo [Finite U33G] {C : Subgroup U33G} {φ : MulAut U33G}
    (h : ∀ x ∈ C, φ x ∈ C) : C.map φ.toMonoidHom = C := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := hx
    simpa using h y hy
  · rw [Subgroup.card_map_of_injective φ.injective]

private theorem u33_atom_eq_A_or_B
    {A : Subgroup U33G}
    (hA : IsGomiAtom ⊤ u33T A) : A = u33Data.A ∨ A = u33Data.B := by
  have hnorm : Subgroup.normalizer (u33T : Set U33G) = u33T := u33Extra.normalizer_T
  have hcov : Subgroup.normalizer (u33T : Set U33G) ⋖ A :=
    (isGomiAtom_top_iff_covBy u33T A).mp hA
  rw [hnorm] at hcov
  rcases u33Data.lattice A hcov.1.le with h | h | h | h
  · exact absurd h.symm hcov.1.ne
  · exact Or.inl h
  · exact Or.inr h
  · exfalso
    exact hcov.2 (lt_of_le_of_ne u33Data.T_le_A u33Data.T_ne_A)
      (by rw [h]; exact lt_of_le_of_ne le_top u33A_ne_top)

private theorem u33_normalizer_le_A_or_B
    (X : Subgroup U33G)
    (hX : X ∈ ({u33Data.A, u33Data.B} : Set (Subgroup U33G))) :
    Subgroup.normalizer (u33T : Set U33G) ≤ X := by
  have hnorm : Subgroup.normalizer (u33T : Set U33G) = u33T := u33Extra.normalizer_T
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rw [hnorm]
  rcases hX with rfl | rfl
  · exact u33Data.T_le_A
  · exact u33Data.T_le_B

private theorem card_u33Stab_le :
    Nat.card u33Stab ≤ 2 * Nat.card (Subgroup.normalizer (u33T : Set U33G)) := by
  have hnorm : Subgroup.normalizer (u33T : Set U33G) = u33T := u33Extra.normalizer_T
  have hcard : Nat.card (Subgroup.normalizer (u33T : Set U33G)) = 32 := by
    rw [hnorm, u33_card_T]
  rw [hcard]
  exact card_stabilizer_u33SylowT_le

private theorem u33_phi'_mem_stab [Finite U33G] :
    u33Phi' ∈ u33Stab :=
  (mem_u33Stab_iff u33Phi').mpr (map_eq_self_of_mapsTo (fun x hx => u33Phi'_T x hx))

private theorem u33_phi'_fixes [Finite U33G] :
    ∀ X ∈ ({u33Data.A, u33Data.B} : Set (Subgroup U33G)),
      X.map u33Phi'.toMonoidHom = X := by
  intro X hX
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hX
  rcases hX with rfl | rfl
  · exact map_eq_self_of_mapsTo (fun x hx => u33Phi'_A x hx)
  · exact map_eq_self_of_mapsTo (fun x hx => u33Phi'_B x hx)

private theorem u33_phi'_not_inner_range :
    u33Phi' ∉ (MulAut.conj : U33G →* MulAut U33G).range := by
  rintro ⟨w, hw⟩
  exact u33Phi'_not_inner ⟨w, fun x => by
    have h := congrArg (fun f : MulAut U33G => f x) hw
    simpa [MulAut.conj_apply] using h.symm⟩

theorem gomiAtomsFixed_u33G :
    GomiAtomsFixed CFSG.Quasithin.U33G := by
  have : Finite U33G := u33Pres_finite_card_le.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowOf 2 u33T ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff, Subgroup.relIndex_top_right]
    exact ⟨le_top, u33_syl⟩
  refine gomiAtomsFixed_of_isSylowOf hT ?_
  intro A α hαT hA
  have hα : α ∈ u33Stab := (mem_u33Stab_iff α).mpr hαT
  rcases u33_atom_eq_A_or_B hA with hAB | hAB
  · rw [hAB]
    exact CFSG.GroupTheory.AutomorphismAction.map_eq_of_card_le_two_mul_card_normalizer
      center_u33G conj_mem_u33Stab card_u33Stab_le u33_normalizer_le_A_or_B u33_phi'_mem_stab
      u33_phi'_not_inner_range u33_phi'_fixes hα (by simp)
  · rw [hAB]
    exact CFSG.GroupTheory.AutomorphismAction.map_eq_of_card_le_two_mul_card_normalizer
      center_u33G conj_mem_u33Stab card_u33Stab_le u33_normalizer_le_A_or_B u33_phi'_mem_stab
      u33_phi'_not_inner_range u33_phi'_fixes hα (by simp)

theorem gomiAtomsFixed_of_psu_three_three
    {K : Type} [Group K]
    [Finite K] (hK : CFSG.Open.StatedClassicalModel K .PSU 3 3 1) : GomiAtomsFixed K := by
  obtain ⟨e⟩ := CFSG.Quasithin.SBc17.nonempty_mulEquiv_PSU3_of_isPSU hK
  obtain ⟨e'⟩ := u33Pres_mulEquiv_PSU3
  have : Finite U33G := u33Pres_finite_card_le.1
  exact GomiAtomsFixed.of_mulEquiv (e.trans e'.symm) gomiAtomsFixed_u33G

theorem gomiAtomsFixed_of_lie_twistedA_three
    {K : Type} [Group K]
    [Finite K] {d : TauCeti.ValidLieTypeIndex} {q : TauCeti.PrimePower} (hq : q.card = 3)
    (hd : d.1 = .twistedA 2 q) (e : K ≃* (TauCeti.CFSGIndex.lie d).Group) :
    GomiAtomsFixed K := by
  obtain ⟨d, hv⟩ := d
  have hd' : d = .twistedA 2 q := hd
  subst hd'
  exact gomiAtomsFixed_of_psu_three_three
    (CFSG.StandardType.ChevTwo.statedClassicalModel_psu_three_three_of_twistedA_two q hv hq e)

end CFSG.GroupTheory
