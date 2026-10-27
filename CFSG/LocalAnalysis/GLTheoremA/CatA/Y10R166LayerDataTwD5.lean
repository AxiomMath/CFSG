module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerDataTwD4
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166LayerData
public import CFSG.Certificates.WordSubgroupRel
public import CFSG.LieType.Multipliers.ProductKernel
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U43Action
public import CFSG.LieType.Multipliers.U43BridgeInputs
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim
public import CFSG.Milestones.CL_LIT_Griess_Schur_multipliers_Lie_type
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10012
public import Certificates.Certificate10013
public import Certificates.Certificate10014
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate9130

public section

namespace CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD

open CFSG.SeitzReduction.OmegaPilot
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.Open
open QuadraticMap Subgroup ClassicalGroups.Orthogonal
open scoped Classical

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n q : ℕ} {b c : F}

@[expose] noncomputable def ldE (k : Fin 4) : Fin (2 * 5) :=
  minusIndexEquiv 5 (by norm_num) (Sum.inl k)

@[expose] noncomputable def ldF (k : Fin 4) : Fin (2 * 5) :=
  minusIndexEquiv 5 (by norm_num) (Sum.inr (Sum.inl k))

@[expose] noncomputable def ldAL : Fin (2 * 5) := anisoCoordLeft (n := 5) (by norm_num)

private noncomputable def ldAR : Fin (2 * 5) := anisoCoordRight (n := 5) (by norm_num)

private def IsU0 (i : Fin (2 * 5)) : Prop :=
  i = ldE 0 ∨ i = ldF 0 ∨ i = ldE 1 ∨ i = ldF 1

private def IsU1 (i : Fin (2 * 5)) : Prop :=
  i = ldE 2 ∨ i = ldF 2 ∨ i = ldE 3 ∨ i = ldF 3

private def IsA (i : Fin (2 * 5)) : Prop := i = ldAL ∨ i = ldAR

private theorem ldE_injective : Function.Injective ldE := fun _ _ h =>
  Sum.inl_injective ((minusIndexEquiv 5 (by norm_num)).injective h)

private theorem ldF_injective : Function.Injective ldF := fun _ _ h =>
  Sum.inl_injective (Sum.inr_injective ((minusIndexEquiv 5 (by norm_num)).injective h))

private theorem ldE_ne_ldF (k l : Fin 4) : ldE k ≠ ldF l := fun h =>
  Sum.inl_ne_inr ((minusIndexEquiv 5 (by norm_num)).injective h)

private theorem ldE_ne_ldAL (k : Fin 4) : ldE k ≠ ldAL := fun h =>
  Sum.inl_ne_inr ((minusIndexEquiv 5 (by norm_num)).injective h)

private theorem ldE_ne_ldAR (k : Fin 4) : ldE k ≠ ldAR := fun h =>
  Sum.inl_ne_inr ((minusIndexEquiv 5 (by norm_num)).injective h)

private theorem ldF_ne_ldAL (k : Fin 4) : ldF k ≠ ldAL := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective ((minusIndexEquiv 5 (by norm_num)).injective h))

private theorem ldF_ne_ldAR (k : Fin 4) : ldF k ≠ ldAR := fun h =>
  Sum.inl_ne_inr (Sum.inr_injective ((minusIndexEquiv 5 (by norm_num)).injective h))

private theorem fin4_cases (k : Fin 4) : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
  fin_cases k <;> simp

private theorem isU0_or_isU1_or_isA (i : Fin (2 * 5)) : IsU0 i ∨ IsU1 i ∨ IsA i := by
  obtain ⟨s, rfl⟩ := (minusIndexEquiv 5 (by norm_num)).surjective i
  rcases s with k | k | t
  · rcases fin4_cases k with rfl | rfl | rfl | rfl <;> simp [IsU0, IsU1, ldE]
  · rcases fin4_cases k with rfl | rfl | rfl | rfl <;> simp [IsU0, IsU1, ldF]
  · fin_cases t <;> simp [IsA, ldAL, ldAR, anisoCoordLeft, anisoCoordRight]

theorem polar_cPair_e (k : Fin 4) (v : Fin (2 * 5) → F) :
    polar (Qc F b c) (cPair F b c k).e v = v (ldF k) := by
  simp only [cPair]
  exact (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) b c k).polar_left v

theorem polar_cPair_f (k : Fin 4) (v : Fin (2 * 5) → F) :
    polar (Qc F b c) (cPair F b c k).f v = v (ldE k) := by
  simp only [cPair]
  exact (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) b c k).polar_right v

theorem single_apply_eq_zero_iff {d : ℕ} {K : Type} [Field K] {i j : Fin d} :
    (Pi.single (M := fun _ => K) i (1 : K) : Fin d → K) j = 0 ↔ i ≠ j := by
  constructor
  · intro h hij
    subst hij
    rw [Pi.single_eq_same] at h
    exact one_ne_zero h
  · intro h
    exact Pi.single_eq_of_ne (M := fun _ => K) (Ne.symm h) 1

theorem inW_cPair_single_iff (a₁ a₂ : Fin 4) (i : Fin (2 * 5)) :
    InW (cPair F b c a₁) (cPair F b c a₂) (Pi.single i (1 : F)) ↔
      (i ≠ ldF a₁ ∧ i ≠ ldE a₁ ∧ i ≠ ldF a₂ ∧ i ≠ ldE a₂) := by
  unfold InW
  simp only [polar_cPair_e, polar_cPair_f, single_apply_eq_zero_iff]

@[expose] def basisSet (P : Fin (2 * 5) → Prop) : Set (Fin (2 * 5) → F) :=
  {v | ∃ i, P i ∧ v = Pi.single i (1 : F)}

private theorem mem_basisSet {P : Fin (2 * 5) → Prop} {i : Fin (2 * 5)} :
    Pi.single i (1 : F) ∈ basisSet (F := F) P ↔ P i := by
  constructor
  · rintro ⟨j, hj, hji⟩
    have hji' : j = i := by
      by_contra hne
      have h : (Pi.single j (1 : F) : Fin (2 * 5) → F) i = 0 := Pi.single_eq_of_ne (Ne.symm hne) 1
      rw [← hji] at h
      rw [Pi.single_eq_same] at h
      exact one_ne_zero h
    rwa [hji'] at hj
  · intro h
    exact ⟨i, h, rfl⟩

private theorem basisSet_mono {P Q : Fin (2 * 5) → Prop} (h : ∀ i, P i → Q i) :
    basisSet (F := F) P ⊆ basisSet (F := F) Q := by
  rintro v ⟨i, hi, rfl⟩
  exact ⟨i, h i hi, rfl⟩

private theorem coordFix_anti {T₁ T₂ : Set (Fin (2 * 5) → F)} (h : T₂ ⊆ T₁) :
    fixPtSub (K := F) T₁ ≤ fixPtSub (K := F) T₂ :=
  fun _ hx v hv => hx v (h hv)

private theorem fix_sup {hQ' : ∃ v, Qc F b c v ≠ 0} {T : Set (Fin (2 * 5) → F)}
    {A B : Subgroup (matrixProjectiveDerived (Qc F b c))}
    (hA : ∀ x ∈ A, projLiftHom hQ' x ∈ fixPtSub (K := F) T)
    (hB : ∀ y ∈ B, projLiftHom hQ' y ∈ fixPtSub (K := F) T) :
    ∀ x ∈ A ⊔ B, projLiftHom hQ' x ∈ fixPtSub (K := F) T := by
  intro x hx
  rw [Subgroup.sup_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with hy | hy
    · exact hA y hy
    · exact hB y hy
  | one =>
    rw [map_one]
    exact one_mem (fixPtSub (K := F) T)
  | mul y z hy hz ihy ihz =>
    rw [map_mul]
    exact mul_mem ihy ihz
  | inv y hy ihy =>
    rw [map_inv]
    exact inv_mem ihy

theorem linearEquiv_eq_one_of_fix_single {d : ℕ} {K : Type} [Field K]
    {Y : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (h : ∀ i : Fin d, Y (Pi.single i (1 : K)) = Pi.single i (1 : K)) : Y = 1 := by
  refine LinearEquiv.ext fun x => ?_
  have hx : x = ∑ i, x i • (Pi.single (M := fun _ => K) i (1 : K) : Fin d → K) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  rw [map_sum]
  have h2 : ∀ i : Fin d, Y (x i • (Pi.single (M := fun _ => K) i (1 : K) : Fin d → K)) =
      x i • (Pi.single (M := fun _ => K) i (1 : K) : Fin d → K) := fun i => by
    rw [map_smul, h]
  rw [Finset.sum_congr rfl (fun i _ => h2 i)]
  exact hx.symm

private theorem eq_one_of_fix_all {hQ' : ∃ v, Qc F b c v ≠ 0}
    {x : matrixProjectiveDerived (Qc F b c)}
    (h : ∀ i, projLiftHom hQ' x (Pi.single i (1 : F)) = Pi.single i (1 : F)) : x = 1 := by
  have hY : projLiftHom hQ' x = 1 := linearEquiv_eq_one_of_fix_single h
  exact projLiftHom_injective hQ' (hY.trans (map_one _).symm)

private theorem fix_zpow {hQ' : ∃ v, Qc F b c v ≠ 0}
    {g : matrixProjectiveDerived (Qc F b c)} {v : Fin (2 * 5) → F}
    (hg : projLiftHom hQ' g v = v) (k : ℤ) : projLiftHom hQ' (g ^ k) v = v := by
  have hmem : projLiftHom hQ' g ∈ fixPtSub (K := F) ({v} : Set (Fin (2 * 5) → F)) := by
    rw [mem_fixPtSub]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact hg
  have hle : Subgroup.zpowers g ≤
      (fixPtSub (K := F) ({v} : Set (Fin (2 * 5) → F))).comap (projLiftHom hQ') :=
    Subgroup.zpowers_le.2 ((Subgroup.mem_comap).2 hmem)
  exact (mem_fixPtSub.1 ((Subgroup.mem_comap).1 (hle (Subgroup.zpow_mem_zpowers g k)))) _
    (Set.mem_singleton v)

private theorem fix_of_mem_zpowers {hQ' : ∃ v, Qc F b c v ≠ 0}
    {g x : matrixProjectiveDerived (Qc F b c)} {v : Fin (2 * 5) → F}
    (hg : projLiftHom hQ' g v = v) (hx : x ∈ Subgroup.zpowers g) :
    projLiftHom hQ' x v = v := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  exact fix_zpow hg k

private theorem fix_zpowers_set {hQ' : ∃ v, Qc F b c v ≠ 0}
    {g : matrixProjectiveDerived (Qc F b c)} {P : Fin (2 * 5) → Prop}
    (hg : ∀ i, P i → projLiftHom hQ' g (Pi.single i (1 : F)) = Pi.single i (1 : F)) :
    ∀ x ∈ Subgroup.zpowers g, projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet P) := by
  intro x hx
  rw [mem_fixPtSub]
  rintro v ⟨i, hi, rfl⟩
  exact fix_of_mem_zpowers (hg i hi) hx

private theorem fix_g0_of (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    {i : Fin (2 * 5)} (hi : IsU1 i ∨ IsA i) :
    projLiftHom hQ' X.g0 (Pi.single i (1 : F)) = Pi.single i (1 : F) := by
  have key : InW (cPair F b c 0) (cPair F b c 1) (Pi.single i (1 : F)) := by
    rw [inW_cPair_single_iff]
    rcases hi with (h | h | h | h) | (h | h)
    · subst h
      exact ⟨ldE_ne_ldF 2 0, ldE_injective.ne (by decide), ldE_ne_ldF 2 1,
        ldE_injective.ne (by decide)⟩
    · subst h
      exact ⟨ldF_injective.ne (by decide), Ne.symm (ldE_ne_ldF 0 2), ldF_injective.ne (by decide),
        Ne.symm (ldE_ne_ldF 1 2)⟩
    · subst h
      exact ⟨ldE_ne_ldF 3 0, ldE_injective.ne (by decide), ldE_ne_ldF 3 1,
        ldE_injective.ne (by decide)⟩
    · subst h
      exact ⟨ldF_injective.ne (by decide), Ne.symm (ldE_ne_ldF 0 3), ldF_injective.ne (by decide),
        Ne.symm (ldE_ne_ldF 1 3)⟩
    · subst h
      exact ⟨Ne.symm (ldF_ne_ldAL 0), Ne.symm (ldE_ne_ldAL 0), Ne.symm (ldF_ne_ldAL 1),
        Ne.symm (ldE_ne_ldAL 1)⟩
    · subst h
      exact ⟨Ne.symm (ldF_ne_ldAR 0), Ne.symm (ldE_ne_ldAR 0), Ne.symm (ldF_ne_ldAR 1),
        Ne.symm (ldE_ne_ldAR 1)⟩
  exact leviFixBar_lift_fixes (F := F) (b := b) (c := c) (hQ' := hQ') X.mem_g0 key

private theorem fix_g2_of (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    {i : Fin (2 * 5)} (hi : IsU0 i ∨ IsA i) :
    projLiftHom hQ' X.g2 (Pi.single i (1 : F)) = Pi.single i (1 : F) := by
  have key : InW (cPair F b c 2) (cPair F b c 3) (Pi.single i (1 : F)) := by
    rw [inW_cPair_single_iff]
    rcases hi with (h | h | h | h) | (h | h)
    · subst h
      exact ⟨ldE_ne_ldF 0 2, ldE_injective.ne (by decide), ldE_ne_ldF 0 3,
        ldE_injective.ne (by decide)⟩
    · subst h
      exact ⟨ldF_injective.ne (by decide), Ne.symm (ldE_ne_ldF 2 0), ldF_injective.ne (by decide),
        Ne.symm (ldE_ne_ldF 3 0)⟩
    · subst h
      exact ⟨ldE_ne_ldF 1 2, ldE_injective.ne (by decide), ldE_ne_ldF 1 3,
        ldE_injective.ne (by decide)⟩
    · subst h
      exact ⟨ldF_injective.ne (by decide), Ne.symm (ldE_ne_ldF 2 1), ldF_injective.ne (by decide),
        Ne.symm (ldE_ne_ldF 3 1)⟩
    · subst h
      exact ⟨Ne.symm (ldF_ne_ldAL 2), Ne.symm (ldE_ne_ldAL 2), Ne.symm (ldF_ne_ldAL 3),
        Ne.symm (ldE_ne_ldAL 3)⟩
    · subst h
      exact ⟨Ne.symm (ldF_ne_ldAR 2), Ne.symm (ldE_ne_ldAR 2), Ne.symm (ldF_ne_ldAR 3),
        Ne.symm (ldE_ne_ldAR 3)⟩
  exact leviFixBar_lift_fixes (F := F) (b := b) (c := c) (hQ' := hQ') X.mem_g2 key

private theorem inW_flip_right {P₁ P₂ : HypPair (Qc F b c)} {v : Fin (2 * 5) → F}
    (h : InW P₁ P₂ v) : InW P₁ (flipPair P₂) v :=
  ⟨h.1, h.2.1, h.2.2.2, h.2.2.1⟩

private theorem fix_g3_of (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    {i : Fin (2 * 5)} (hi : IsU0 i ∨ IsA i) :
    projLiftHom hQ' X.g3 (Pi.single i (1 : F)) = Pi.single i (1 : F) := by
  have key : InW (cPair F b c 2) (cPair F b c 3) (Pi.single i (1 : F)) := by
    rw [inW_cPair_single_iff]
    rcases hi with (h | h | h | h) | (h | h)
    · subst h
      exact ⟨ldE_ne_ldF 0 2, ldE_injective.ne (by decide), ldE_ne_ldF 0 3,
        ldE_injective.ne (by decide)⟩
    · subst h
      exact ⟨ldF_injective.ne (by decide), Ne.symm (ldE_ne_ldF 2 0), ldF_injective.ne (by decide),
        Ne.symm (ldE_ne_ldF 3 0)⟩
    · subst h
      exact ⟨ldE_ne_ldF 1 2, ldE_injective.ne (by decide), ldE_ne_ldF 1 3,
        ldE_injective.ne (by decide)⟩
    · subst h
      exact ⟨ldF_injective.ne (by decide), Ne.symm (ldE_ne_ldF 2 1), ldF_injective.ne (by decide),
        Ne.symm (ldE_ne_ldF 3 1)⟩
    · subst h
      exact ⟨Ne.symm (ldF_ne_ldAL 2), Ne.symm (ldE_ne_ldAL 2), Ne.symm (ldF_ne_ldAL 3),
        Ne.symm (ldE_ne_ldAL 3)⟩
    · subst h
      exact ⟨Ne.symm (ldF_ne_ldAR 2), Ne.symm (ldE_ne_ldAR 2), Ne.symm (ldF_ne_ldAR 3),
        Ne.symm (ldE_ne_ldAR 3)⟩
  exact leviFixBar_lift_fixes (F := F) (b := b) (c := c) (hQ' := hQ') X.mem_g3
    (inW_flip_right key)

private theorem fix_u_of (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q))
    {i : Fin (2 * 5)} (hi : IsU0 i ∨ IsU1 i) :
    projLiftHom hQ' X.u (Pi.single i (1 : F)) = Pi.single i (1 : F) := by
  have key : ∀ k : Fin 4, projLiftHom hQ' X.u (Pi.single (ldE k) (1 : F)) =
        Pi.single (ldE k) (1 : F) ∧
      projLiftHom hQ' X.u (Pi.single (ldF k) (1 : F)) = Pi.single (ldF k) (1 : F) := by
    intro k
    have h := anisoTorus_lift_fixes_split (F := F) (b := b) (c := c) hirr (hQ' := hQ') X.mem_u k
    exact ⟨by rw [projLiftHom_apply]; exact h.1, by rw [projLiftHom_apply]; exact h.2⟩
  rcases hi with (h | h | h | h) | (h | h | h | h)
  · subst h; exact (key 0).1
  · subst h; exact (key 0).2
  · subst h; exact (key 1).1
  · subst h; exact (key 1).2
  · subst h; exact (key 2).1
  · subst h; exact (key 2).2
  · subst h; exact (key 3).1
  · subst h; exact (key 3).2

private theorem disjoint_zp0_sup23 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    Subgroup.zpowers X.g0 ⊓ (Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3) = ⊥ := by
  have h0 : ∀ x ∈ Subgroup.zpowers X.g0,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU1 i ∨ IsA i)) :=
    fix_zpowers_set (fun i hi => fix_g0_of hirr hQ' X hi)
  have h2 : ∀ x ∈ Subgroup.zpowers X.g2,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU0 i ∨ IsA i)) :=
    fix_zpowers_set (fun i hi => fix_g2_of hirr hQ' X hi)
  have h3 : ∀ x ∈ Subgroup.zpowers X.g3,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU0 i ∨ IsA i)) :=
    fix_zpowers_set (fun i hi => fix_g3_of hirr hQ' X hi)
  have h23 : ∀ x ∈ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU0 i ∨ IsA i)) :=
    fix_sup h2 h3
  refine le_antisymm ?_ bot_le
  rintro x ⟨hx0, hx23⟩
  rw [Subgroup.mem_bot]
  refine eq_one_of_fix_all (hQ' := hQ') fun i => ?_
  rcases isU0_or_isU1_or_isA i with h | h | h
  · exact (mem_fixPtSub.1 (h23 x hx23)) _ ((mem_basisSet).2 (Or.inl h))
  · exact (mem_fixPtSub.1 (h0 x hx0)) _ ((mem_basisSet).2 (Or.inl h))
  · exact (mem_fixPtSub.1 (h0 x hx0)) _ ((mem_basisSet).2 (Or.inr h))

private theorem disjoint_zp2_zp3 (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    Subgroup.zpowers X.g2 ⊓ Subgroup.zpowers X.g3 = ⊥ := by
  obtain ⟨hQ, hT⟩ := regular_coordinateQuadMinus 5 F b c (by norm_num) hirr
  have hbot := leviFixBar_inf_flip_eq_bot (cPair_orth F b c 2 3 (by decide)) hQ hT hQ'
  refine le_antisymm ?_ bot_le
  rintro x ⟨hx2, hx3⟩
  have h1 : x ∈ leviFixBar (cPair F b c 2) (cPair F b c 3) := Subgroup.zpowers_le.2 X.mem_g2 hx2
  have h2 : x ∈ leviFixBar (cPair F b c 2) (flipPair (cPair F b c 3)) :=
    Subgroup.zpowers_le.2 X.mem_g3 hx3
  have hmem : x ∈ leviFixBar (cPair F b c 2) (cPair F b c 3) ⊓
      leviFixBar (cPair F b c 2) (flipPair (cPair F b c 3)) := ⟨h1, h2⟩
  rw [hbot] at hmem
  exact hmem

private theorem disjoint_sup023_zpu (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (hQ' : ∃ v, Qc F b c v ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    (Subgroup.zpowers X.g0 ⊔ (Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3)) ⊓
      Subgroup.zpowers X.u = ⊥ := by
  have h0 : ∀ x ∈ Subgroup.zpowers X.g0,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU1 i ∨ IsA i)) :=
    fix_zpowers_set (fun i hi => fix_g0_of hirr hQ' X hi)
  have h2 : ∀ x ∈ Subgroup.zpowers X.g2,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU0 i ∨ IsA i)) :=
    fix_zpowers_set (fun i hi => fix_g2_of hirr hQ' X hi)
  have h3 : ∀ x ∈ Subgroup.zpowers X.g3,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU0 i ∨ IsA i)) :=
    fix_zpowers_set (fun i hi => fix_g3_of hirr hQ' X hi)
  have h23 : ∀ x ∈ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU0 i ∨ IsA i)) :=
    fix_sup h2 h3
  have hA : ∀ x ∈ Subgroup.zpowers X.g0,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsA i)) :=
    fun x hx => coordFix_anti (basisSet_mono (fun _ h => Or.inr h)) (h0 x hx)
  have hB : ∀ x ∈ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsA i)) :=
    fun x hx => coordFix_anti (basisSet_mono (fun _ h => Or.inr h)) (h23 x hx)
  have hsup : ∀ x ∈ Subgroup.zpowers X.g0 ⊔ (Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3),
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsA i)) :=
    fix_sup hA hB
  have hu : ∀ x ∈ Subgroup.zpowers X.u,
      projLiftHom hQ' x ∈ fixPtSub (K := F) (basisSet (fun i => IsU0 i ∨ IsU1 i)) :=
    fix_zpowers_set (fun i hi => fix_u_of hirr hQ' X hi)
  refine le_antisymm ?_ bot_le
  rintro x ⟨hxS, hxu⟩
  rw [Subgroup.mem_bot]
  refine eq_one_of_fix_all (hQ' := hQ') fun i => ?_
  rcases isU0_or_isU1_or_isA i with h | h | h
  · exact (mem_fixPtSub.1 (hu x hxu)) _ ((mem_basisSet).2 (Or.inl h))
  · exact (mem_fixPtSub.1 (hu x hxu)) _ ((mem_basisSet).2 (Or.inr h))
  · exact (mem_fixPtSub.1 (hsup x hxS)) _ ((mem_basisSet).2 h)

private theorem card_sup_eq_mul_of_disjoint {A B : Subgroup (matrixProjectiveDerived (Qc F b c))}
    (hAB : A ⊓ B = ⊥) (hc : ∀ a ∈ A, ∀ bb ∈ B, a * bb = bb * a) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hc).1
  rw [hAB, Subgroup.card_bot, mul_one] at h
  exact h

private theorem commute_sup_right {G₀ : Type} [Group G₀] {a : G₀} {K L : Subgroup G₀}
    (hK : ∀ y ∈ K, a * y = y * a) (hL : ∀ y ∈ L, a * y = y * a) :
    ∀ y ∈ K ⊔ L, a * y = y * a := by
  intro y hy
  rw [Subgroup.sup_eq_closure] at hy
  induction hy using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact hK x hx
    · exact hL x hx
  | one => simp
  | mul x z hx hz ihx ihz =>
    calc a * (x * z) = (a * x) * z := by rw [mul_assoc]
      _ = (x * a) * z := by rw [ihx]
      _ = x * (a * z) := by rw [mul_assoc]
      _ = x * (z * a) := by rw [ihz]
      _ = x * z * a := by rw [mul_assoc]
  | inv x hx ihx =>
    calc a * x⁻¹ = x⁻¹ * (x * a) * x⁻¹ := by group
      _ = x⁻¹ * (a * x) * x⁻¹ := by rw [ihx]
      _ = x⁻¹ * a := by group

private theorem card_sup_zpowers (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    Nat.card ↥(Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3 ⊔
      Subgroup.zpowers X.u) = q ^ 4 := by
  classical
  have hQ' : ∃ v, Qc F b c v ≠ 0 :=
    (isHypCoord_coordinateQuadMinus (K := F) (n := 5) (by norm_num) (b := b) (c := c)
      (0 : Fin 4)).exists_ne_zero
  have hz0 : Nat.card (Subgroup.zpowers X.g0) = q := by rw [Nat.card_zpowers, X.ord_g0]
  have hz2 : Nat.card (Subgroup.zpowers X.g2) = q := by rw [Nat.card_zpowers, X.ord_g2]
  have hz3 : Nat.card (Subgroup.zpowers X.g3) = q := by rw [Nat.card_zpowers, X.ord_g3]
  have hzu : Nat.card (Subgroup.zpowers X.u) = q := by rw [Nat.card_zpowers, X.ord_u]
  have hc23 : ∀ y ∈ Subgroup.zpowers X.g2, ∀ z ∈ Subgroup.zpowers X.g3, y * z = z * y :=
    zpowers_commute (commute_g2_g3 hirr X)
  have h23 : Nat.card ↥(Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3) = q ^ 2 := by
    rw [card_sup_eq_mul_of_disjoint (disjoint_zp2_zp3 hirr hQ' X) hc23, hz2, hz3, _root_.sq]
  have hc02 : ∀ y ∈ Subgroup.zpowers X.g0, ∀ z ∈ Subgroup.zpowers X.g2, y * z = z * y :=
    zpowers_commute (commute_g0_g2 X hQ')
  have hc03 : ∀ y ∈ Subgroup.zpowers X.g0, ∀ z ∈ Subgroup.zpowers X.g3, y * z = z * y :=
    zpowers_commute (commute_g0_g3 X hQ')
  have hc0 : ∀ y ∈ Subgroup.zpowers X.g0,
      ∀ z ∈ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3, y * z = z * y := by
    intro y hy
    exact commute_sup_right (fun u hu => hc02 y hy u hu) (fun u hu => hc03 y hy u hu)
  have h023 : Nat.card ↥(Subgroup.zpowers X.g0 ⊔
      (Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3)) = q ^ 3 := by
    rw [card_sup_eq_mul_of_disjoint (disjoint_zp0_sup23 hirr hQ' X) hc0, hz0, h23]
    ring
  have hc0u : ∀ y ∈ Subgroup.zpowers X.g0, ∀ z ∈ Subgroup.zpowers X.u, y * z = z * y :=
    zpowers_commute (commute_g0_u hirr X hQ')
  have hc2u : ∀ y ∈ Subgroup.zpowers X.g2, ∀ z ∈ Subgroup.zpowers X.u, y * z = z * y :=
    zpowers_commute (commute_g2_u hirr X hQ')
  have hc3u : ∀ y ∈ Subgroup.zpowers X.g3, ∀ z ∈ Subgroup.zpowers X.u, y * z = z * y :=
    zpowers_commute (commute_g3_u hirr X hQ')
  have hcu : ∀ z ∈ Subgroup.zpowers X.u,
      ∀ y ∈ Subgroup.zpowers X.g0 ⊔ (Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3),
        z * y = y * z := by
    intro z hz y hy
    refine commute_sup_right (fun u hu => ?_) (fun u hu => ?_) y hy
    · exact (hc0u u hu z hz).symm
    · exact commute_sup_right (fun v hv => (hc2u v hv z hz).symm)
        (fun v hv => (hc3u v hv z hz).symm) u hu
  have h4 : Nat.card ↥((Subgroup.zpowers X.g0 ⊔ (Subgroup.zpowers X.g2 ⊔
      Subgroup.zpowers X.g3)) ⊔ Subgroup.zpowers X.u) = q ^ 4 := by
    rw [card_sup_eq_mul_of_disjoint (disjoint_sup023_zpu hirr hQ' X)
      (fun a ha bb hb => (hcu bb hb a ha).symm), h023, hzu]
    ring
  rwa [show Subgroup.zpowers X.g0 ⊔ Subgroup.zpowers X.g2 ⊔ Subgroup.zpowers X.g3 ⊔
      Subgroup.zpowers X.u = (Subgroup.zpowers X.g0 ⊔ (Subgroup.zpowers X.g2 ⊔
      Subgroup.zpowers X.g3)) ⊔ Subgroup.zpowers X.u from by simp only [sup_assoc]]

theorem card_bJ (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    (X : LayerQGenerators (F := F) (b := b) (c := c) (q := q)) :
    Nat.card (bJ X) = q ^ 4 :=
  card_sup_zpowers hirr X

end CFSG.LocalAnalysis.GLTheoremA.Y10F.OmegaMinusLD
