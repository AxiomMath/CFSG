module

public import CFSG.ClassicalInvolution.Q3.Q3AM289Glue
public import CFSG.ClassicalInvolution.Q3.Q3AM289Lay
public import CFSG.ClassicalInvolution.Q3.Q3AM289Stmt
public import CFSG.ClassicalInvolution.Q3.Q3AMXNOrb

public section

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3T8.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Disconnected CFSG.ClassicalInvolution.Asc77
  CFSG.ClassicalInvolution.Uniform CFSG.ClassicalInvolution.Balance.Bootstrap
  CFSG.ClassicalInvolution.Q3.Q3NL
open CFSG.ClassicalInvolution.Q3.Q3AM (nbrLayer exactCore3_le_nbrLayer nbrLayer_le_centralizer
  conj_mem_nbrLayer s3Shape_layerFam)
open scoped commutatorElement

section Layer

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {K J : Subgroup G}
  {S : Sylow 2 G} {R T W : Subgroup G} {z t : G}


theorem BadStd8.centralizer_conjSub_eq [IsSimpleGroup G] (h : BadStd8 Ω K J S R T W z t)
    {M : Subgroup G} {a : G} (hM : M ∈ Ω) (ha : IsUniqueInvolution M a) :
    ∀ g ∈ Subgroup.centralizer ({a} : Set G), conjSub g M = M := by
  have hstd := h.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hnt : ∀ M ∈ Ω, ∀ M' ∈ twinSet Ω M, M' = M := fun M hM =>
    T8.noTwins_of_mem hΩ.conjInvariant hstd.stand.trans hstd.noTwins hM
  exact fun g hg => mem_normalizer_iff_conjSub_eq.mp
    (T8.centralizer_le_normalizer_of_noTwins hΩ.conjInvariant hM (hnt M hM) ha hg)

theorem BadStd8.centralizer_le_normalizer_nbrLayer [IsSimpleGroup G]
    (h : BadStd8 Ω K J S R T W z t) {M : Subgroup G} {a : G} (hM : M ∈ Ω)
    (ha : IsUniqueInvolution M a) :
    Subgroup.centralizer ({a} : Set G) ≤
      Subgroup.normalizer ((nbrLayer Ω M a : Subgroup G) : Set G) := by
  have hΩ : HypOmegaMod Ω := h.std.stand.hyp
  have hCM := h.centralizer_conjSub_eq hM ha
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => conj_mem_nbrLayer hΩ hCM hg hy, fun hy => ?_⟩
  have := conj_mem_nbrLayer hΩ hCM (Subgroup.inv_mem _ hg) hy
  simpa [mul_assoc] using this

theorem commutator_self_mem_oddCoreOf_nbrLayer (Ω : Set (Subgroup G)) (M : Subgroup G) (a : G) :
    ∀ x ∈ nbrLayer Ω M a, ⁅x, a⁆ ∈ oddCoreOf (nbrLayer Ω M a) := by
  intro x hx
  have hxa : x * a = a * x :=
    Subgroup.mem_centralizer_singleton_iff.mp (nbrLayer_le_centralizer Ω M a hx)
  rw [commutatorElement_eq_one_iff_mul_comm.mpr hxa]
  exact (oddCoreOf _).one_mem

theorem mem_nbrLayer_of_mem {M N : Subgroup G} {a x : G} (hN : N ∈ omegaNbr Ω M) (hx : x ∈ N)
    (hxa : x * a = a * x) : x ∈ nbrLayer Ω M a :=
  exactCore3_le_nbrLayer hN ⟨hx, Subgroup.mem_centralizer_singleton_iff.mpr hxa⟩

theorem s3_mem_omegaStarNbr_nbr2 [IsSimpleGroup G] (hbad : BadStd8 Ω K J S R T W z t) {s : G}
    (hs : Q3AM.S3AxisL Ω K J z t s) {J₂ : Subgroup G} (hJ₂ : J₂ ∈ omegaNbr Ω K)
    (hu₂ : IsUniqueInvolution J₂ (t * s)) :
    ∃ L ∈ omegaNbr Ω K, IsUniqueInvolution L s ∧ L ∈ omegaStarNbr Ω J₂ := by
  have hstd := hbad.std
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hΩM : Q3T7M.HM Ω := hstd.stand.modU
  obtain ⟨L, hL, hu_s, hstar, -⟩ := hs.nbr
  obtain ⟨-, -, A, hA, hAL, hAJ⟩ := hstar
  have hA2 : IsPGroup 2 A := hΩM.isPGroup_of_mem_USet hA
  obtain ⟨-, -, -, -, -, -, -, -, h4⟩ := hΩM.exists_data_of_mem_USet hA
  have hAt : ∀ a ∈ A, a * t = t * a := by
    intro a ha
    have h1 : a * t * a⁻¹ ∈ J := by
      have := (Subgroup.mem_normalizer_iff.mp (hAJ ha) t).mp hstd.ht.mem
      exact this
    have h2 : (a * t * a⁻¹) * (a * t * a⁻¹) = 1 := by
      calc (a * t * a⁻¹) * (a * t * a⁻¹) = a * (t * t) * a⁻¹ := by group
        _ = 1 := by rw [hstd.ht.sq]; group
    rcases hstd.ht.unique _ h1 h2 with h3 | h3
    · exact absurd (by simpa using h3) hstd.ht.ne_one
    · calc a * t = (a * t * a⁻¹) * a := by group
        _ = t * a := by rw [h3]
  have hAs : ∀ a ∈ A, a * s = s * a := by
    intro a ha
    have h1 : a * s * a⁻¹ ∈ L := L.mul_mem (L.mul_mem (hAL ha) hu_s.mem) (L.inv_mem (hAL ha))
    have h2 : (a * s * a⁻¹) * (a * s * a⁻¹) = 1 := by
      calc (a * s * a⁻¹) * (a * s * a⁻¹) = a * (s * s) * a⁻¹ := by group
        _ = 1 := by rw [hu_s.sq]; group
    rcases hu_s.unique _ h1 h2 with h3 | h3
    · exact absurd (by simpa using h3) hu_s.ne_one
    · calc a * s = (a * s * a⁻¹) * a := by group
        _ = s * a := by rw [h3]
  have hAc : A ≤ Subgroup.centralizer ({t * s} : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * (t * s) = (a * t) * s := by group
      _ = (t * a) * s := by rw [hAt a ha]
      _ = t * (a * s) := by group
      _ = t * (s * a) := by rw [hAs a ha]
      _ = (t * s) * a := by group
  have hne : J₂ ≠ L := by
    intro e
    have h1 : IsUniqueInvolution L (t * s) := e ▸ hu₂
    have h2 : t * s = s := (h1.unique s hu_s.mem hu_s.sq).resolve_left hu_s.ne_one |>.symm
    exact hstd.ht.ne_one (mul_eq_right.mp h2)
  exact ⟨L, hL, hu_s, hL.1, hne.symm, A, hA, hAL,
    hΩ.le_normalizer_of_le_centralizer hJ₂.1 hL.1 hne hu₂ hAL hA2 (by omega) hAc⟩

theorem s3Nbr2 [IsSimpleGroup G] (h : Q3AM.S3Setting Ω K J S R T W z t) {s : G}
    (hs : Q3AM.S3AxisL Ω K J z t s) : ∃ J₂ ∈ omegaNbr Ω K, IsUniqueInvolution J₂ (t * s) := by
  have hbad := h.bad
  have hstd := hbad.std
  have hz2 := hstd.hz.sq
  have ht2 := hstd.ht.sq
  have hΩ : HypOmegaMod Ω := hstd.stand.hyp
  have hzt : z * t = t * z := Q3CL.T8.mul_comm_of_mem_omegaNbr hΩ hstd.hz hstd.hJ hstd.ht
  have hS : S3Shape (Q3AM.layerFam Ω K z) := s3Shape_layerFam h.layer
  obtain ⟨L, hL, hu_s, -, -⟩ := hs.nbr
  have htY : t ∈ nbrLayer Ω K z := mem_nbrLayer_of_mem hstd.hJ hstd.ht.mem hzt.symm
  have hsY : s ∈ nbrLayer Ω K z := mem_nbrLayer_of_mem hL hu_s.mem hs.comm_z.symm
  have hts2 : (t * s) * (t * s) = 1 := by
    calc t * s * (t * s) = t * (s * t) * s := by group
      _ = t * (t * s) * s := by rw [← hs.comm_t]
      _ = (t * t) * (s * s) := by group
      _ = 1 := by rw [ht2, hs.sq, one_mul]
  have hts : t ≠ s := fun e => hs.indep (e ▸ Subgroup.subset_closure (by simp))
  have hts1 : t * s ≠ 1 := fun e => hts (by
    have h1 : s = t⁻¹ := eq_inv_of_mul_eq_one_right e
    rw [h1, inv_eq_of_mul_eq_one_right ht2])
  have hzts : z * (t * s) = (t * s) * z := by
    calc z * (t * s) = (z * t) * s := by group
      _ = (t * z) * s := by rw [hzt]
      _ = t * (z * s) := by group
      _ = t * (s * z) := by rw [hs.comm_z]
      _ = (t * s) * z := by group
  have hzX := commutator_self_mem_oddCoreOf_nbrLayer Ω K z
  obtain ⟨y, hyY, -, hyt⟩ := exists_conj_lift_involutions
    (hbad.centralizer_le_normalizer_nbrLayer hstd.stand.mem hstd.hz)
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl) hz2 hzX htY
    ((nbrLayer Ω K z).mul_mem htY hsY) ht2 hts2 hstd.ht.ne_one hts1 hzt hzts hS.involutionsConj
  have hyC : y ∈ Subgroup.centralizer ({z} : Set G) := nbrLayer_le_centralizer Ω K z hyY
  refine ⟨conjSub y J, hbad.conjSub_mem_omegaNbr hyC hstd.hJ, ?_⟩
  have := hstd.ht.conj y
  rwa [hyt] at this

end Layer

end CFSG.ClassicalInvolution.Q3.Q3T8.Asc77
