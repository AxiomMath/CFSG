module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixTools
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem5DeltaLocalSixConj

public section

open CFSG.Open
open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools

namespace CFSG.ComponentClassification.AschbacherTheorem5

namespace DeltaLocal

open SectionSix SectionSix.BarTools RankOne SixConj SixTools

namespace Six

variable {G : Type} [Group G] [Finite G] {D : Subgroup G} {r : ℕ}
  {Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D)}

@[expose] def centralizerJoinH (D U : Subgroup G) : Subgroup G :=
  (AschbacherToolkit.centralizerJoin (U.subgroupOf (Subgroup.normalizer (D : Set G)))).map
    (Subgroup.normalizer (D : Set G)).subtype

omit [Finite G] in
theorem centralizerJoinH_le (D U : Subgroup G) :
    centralizerJoinH D U ≤ Subgroup.normalizer (D : Set G) :=
  Subgroup.map_subtype_le _

omit [Finite G] in
theorem centralizerJoinH_le_conj {U : Subgroup G} {g : G}
    (hU : U ∈ fourGroupsInto (Subgroup.normalizer (D : Set G))
      (rightConjugate (Subgroup.normalizer (D : Set G)) g)) :
    centralizerJoinH D U ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g := by
  rw [centralizerJoinH, Subgroup.map_le_iff_le_comap]
  apply iSup₂_le
  intro w hw1 y hy
  have hwU : (((w : Subgroup.normalizer (D : Set G)) : G)) ∈ U := w.2
  have hw1' : ((w : Subgroup.normalizer (D : Set G)) : G) ≠ 1 := fun h => hw1 (Subtype.ext h)
  refine hU.2.2.2 _ hwU hw1' ?_
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hy)

theorem bar_centralizerJoinH {U : Subgroup G} (hU2 : IsPGroup 2 U) :
    bar D (centralizerJoinH D U) = AschbacherToolkit.centralizerJoin (bar D U) := by
  have hcj := AschbacherToolkit.centralizerJoin_quotient_of_isPGroup (coreIn D) (coreIn_odd D)
    (U := U.subgroupOf (Subgroup.normalizer (D : Set G))) hU2.comap_subtype
  have hsub : (centralizerJoinH D U).subgroupOf (Subgroup.normalizer (D : Set G)) =
      AschbacherToolkit.centralizerJoin (U.subgroupOf (Subgroup.normalizer (D : Set G))) :=
    Subgroup.comap_map_eq_self_of_injective (Subgroup.normalizer (D : Set G)).subtype_injective _
  change ((centralizerJoinH D U).subgroupOf (Subgroup.normalizer (D : Set G))).map (toBar D) =
    AschbacherToolkit.centralizerJoin ((U.subgroupOf (Subgroup.normalizer (D : Set G))).map
      (toBar D))
  rw [hsub]
  exact hcj.symm

@[expose] def PairAt (D U : Subgroup G) (Abar : Fin r → Subgroup (D ⧸ aschbacherThm5OddCore D))
    (j : Fin r) (p q : Bar D) : Prop :=
  IsQ8Pair p q ∧ p ∈ bar D (aschbacherThm5Preimage D (Abar j)) ∧
    q ∈ bar D (aschbacherThm5Preimage D (Abar j)) ∧
    p ∈ AschbacherToolkit.centralizerJoin (bar D U) ∧
    q ∈ AschbacherToolkit.centralizerJoin (bar D U) ∧
    p ^ 2 ∈ Subgroup.centralizer (bar D (aschbacherThm5Preimage D (Abar j)) : Set (Bar D)) ∧
    ∀ t ∈ bar D (aschbacherThm5Preimage D (Abar j)), t ^ 2 = 1 → t = 1 ∨ t = p ^ 2

theorem cross_commute (hyp : Hyp61 G D r Abar) {j k : Fin r} (hjk : j ≠ k) {x y : Bar D}
    (hx : x ∈ bar D (aschbacherThm5Preimage D (Abar j)))
    (hy : y ∈ bar D (aschbacherThm5Preimage D (Abar k))) : x * y = y * x :=
  ((Subgroup.mem_centralizer_iff.mp (Strong.bar_factor_le_centralizer hyp hjk hy)) x hx)

omit [Finite G] in
theorem conj_normalizer_inv (g : G) :
    rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹ =
      Subgroup.normalizer (D : Set G) := by
  rw [normalizer_rightConjugate, rightConjugate_mul, mul_inv_cancel, rightConjugate_one]

theorem pRank_conjFactor (g : G) (m : Fin r) :
    CFSG.Open.pRank 2 (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)) =
      CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) := by
  rw [preimage_conjFactors]
  exact Conj.pRank_map (MulAut.conj g⁻¹) (by norm_num) _

theorem false_of_elemAbelian_eight (hC : Counterexample G D r Abar) (hin : SectionSixInputs)
    {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    (hrank : ∀ m, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) ≤ 1) (m : Fin r)
    {E : Subgroup G} (hEel : IsElemAbelian 2 E) (hE8 : Nat.card E = 8)
    (hEH : E ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hEC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer (D : Set G)) : False := by
  have hC' := hC.conj g
  have hH' := normalizer_rightConjugate D g
  have hinv := conj_normalizer_inv (D := D) g
  have hg' : rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      g⁻¹ ≠ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    rw [hinv, hH']
    exact Ne.symm hg
  have hEH' : E ≤ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := hH' ▸ hEH
  obtain ⟨W, hWE, hW4, -⟩ :=
    AschbacherKnownGroup.Lemma35.exists_fourGroup_of_mem hEel (by rw [hE8]; norm_num) E.one_mem
  have hW : W ∈ fourGroupsInto (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      (rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹) :=
    ⟨hWE.trans hEH', hW4.1, hW4.2, fun w hw hw1 => hinv ▸ hEC w (hWE hw) hw1⟩
  exact no_elemAbelian_eight hC' hin hg' hW m (by rw [pRank_conjFactor]; exact hrank m) hEel hE8
    hEH' (fun e he he1 => hinv ▸ hEC e he he1)

theorem false_of_faithful_quaternion (hC : Counterexample G D r Abar) (hin : SectionSixInputs)
    {g : G}
    (hg : rightConjugate (Subgroup.normalizer (D : Set G)) g ≠ Subgroup.normalizer (D : Set G))
    (hrank : ∀ m, CFSG.Open.pRank 2 (aschbacherThm5Preimage D (Abar m)) ≤ 1) (m : Fin r)
    {X E : Subgroup G} (hX : AschbacherTheorem3.IsQuaternionTwoGroup X)
    (hXH : X ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hXN : X ≤ Subgroup.normalizer
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Set G))
    (hXf : ∀ x ∈ X, x ≠ 1 → ¬ aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)) x)
    (hEel : IsElemAbelian 2 E) (hE4 : Nat.card E = 4)
    (hEH : E ≤ rightConjugate (Subgroup.normalizer (D : Set G)) g)
    (hEN : E ≤ Subgroup.normalizer
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m) : Set G))
    (hEf : ∀ e ∈ E, e ≠ 1 → ¬ aschbacherThm5Centralizes (aschbacherThm5Core (rightConjugate D g))
      (aschbacherThm5Preimage (rightConjugate D g) (conjFactors D Abar g m)) e)
    (hEC : ∀ e ∈ E, e ≠ 1 → Subgroup.centralizer ({e} : Set G) ≤
      Subgroup.normalizer (D : Set G))
    (hEX : E ≤ Subgroup.centralizer (X : Set G)) : False := by
  have hC' := hC.conj g
  have hH' := normalizer_rightConjugate D g
  have hinv := conj_normalizer_inv (D := D) g
  have hg' : rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      g⁻¹ ≠ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := by
    rw [hinv, hH']
    exact Ne.symm hg
  have hEH' : E ≤ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := hH' ▸ hEH
  have hXH' : X ≤ Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G) := hH' ▸ hXH
  have hE : E ∈ fourGroupsInto (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G))
      (rightConjugate (Subgroup.normalizer ((rightConjugate D g : Subgroup G) : Set G)) g⁻¹) :=
    ⟨hEH', hEel, hE4, fun e he he1 => hinv ▸ hEC e he he1⟩
  exact no_faithful_quaternion hC' hin hg' hE m (by rw [pRank_conjFactor]; exact hrank m) hX
    hXH' hXN hXf hEel hE4 hEH' hEN hEf hEX

end Six

end DeltaLocal

end CFSG.ComponentClassification.AschbacherTheorem5
