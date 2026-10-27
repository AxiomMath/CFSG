module

public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddSU
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherMaximalParabolics
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ.OddGenForm

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ

open CFSG.Open CFSG.LieType.BorelTits CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.LinearGroups CFSG.Assembly.LowTwoRank
open scoped Matrix Pointwise

section SUGen

variable {q f : ℕ} [Fact q.Prime] {K : Type} [Field K] [Finite K] [CharP K q]

theorem unitaryForm_β_eq_stdHermForm (h : UnitaryFieldData q f K) (hK : Nat.card K = (q ^ f) ^ 2)
    {n : ℕ} (u v : Fin n → K) : (unitaryForm q f hK n).β u v = stdHermForm h n u v := by
  rw [unitaryForm_β]
  simp [stdHermForm, UnitaryFieldData.bar_apply, unitaryInvolution_apply, iterateFrobenius_def]

end SUGen

section SUTransport

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {r ε : ℕ}

theorem natRep_hypTransport_mem {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) (g : hypSU h r ε) (W : Submodule K (HypIndex r ε → K))
    (hg : g • W = W) :
    ∀ v ∈ transportSubspace h hR W,
      natRep (StatedSU (2 * r + ε) (p ^ f) K) (hypTransport h hR g) v ∈ transportSubspace h hR W := by
  intro v hv
  have h1 := transportSubspace_smul hR g W
  rw [hg] at h1
  have h2 : (hypTransport h hR g) • v ∈ (hypTransport h hR g) • transportSubspace h hR W :=
    Submodule.smul_mem_pointwise_smul _ _ _ hv
  rw [← h1] at h2
  convert h2 using 1
  rw [natRep_apply]
  rfl

end SUTransport


section SUMain

variable {q f : ℕ} [Fact q.Prime] {K : Type} [Field K] [Finite K] [CharP K q]
  {h : UnitaryFieldData q f K} {r ε : ℕ}

theorem map_projIsoStabilizer_le {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) (hn : 1 ≤ 2 * r + ε) (W : Submodule K (HypIndex r ε → K)) :
    (projIsoStabilizer h r ε W).map (hypPSUEquivStatedProj h hR hn).toMonoidHom ≤
      (subspStab (natRep (StatedSU (2 * r + ε) (q ^ f) K)) (transportSubspace h hR W)).map
        (QuotientGroup.mk' ((StatedScalars (Fin (2 * r + ε)) K).subgroupOf
          (StatedSU (2 * r + ε) (q ^ f) K))) := by
  rintro _ ⟨y, ⟨g, hg, rfl⟩, rfl⟩
  refine ⟨hypTransport h hR g, mem_subspStab_of_forward
    (natRep_hypTransport_mem hR g W (mem_isoStabilizer.1 hg)), ?_⟩
  exact (hypPSUEquivStatedProj_hypProj hR hn g).symm

@[expose] def hypVec (r ε : ℕ) (K : Type) [Field K] (a : Fin r) : HypIndex r ε → K :=
  Pi.single (Sum.inl a) 1

theorem isoFlag_one (hr : 0 < r) :
    CFSG.ClassicalGroups.UnitaryFlag.isoFlag r ε K 1 = Submodule.span K {hypVec r ε K ⟨0, hr⟩} := by
  unfold CFSG.ClassicalGroups.UnitaryFlag.isoFlag
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have : j = ⟨0, hr⟩ := Fin.ext (show (j : ℕ) = 0 by omega)
    rw [this]
    rfl
  · rintro rfl
    exact ⟨⟨0, hr⟩, by simp, rfl⟩

theorem isoFlag_two (hr : 1 < r) :
    CFSG.ClassicalGroups.UnitaryFlag.isoFlag r ε K 2 = Submodule.span K {hypVec r ε K ⟨0, by omega⟩} ⊔
      Submodule.span K {hypVec r ε K ⟨1, hr⟩} := by
  unfold CFSG.ClassicalGroups.UnitaryFlag.isoFlag
  rw [← Submodule.span_union]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_union, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    by_cases hj0 : (j : ℕ) = 0
    · left
      have : j = ⟨0, by omega⟩ := Fin.ext hj0
      rw [this]
      rfl
    · right
      have : j = ⟨1, hr⟩ := Fin.ext (show (j : ℕ) = 1 by omega)
      rw [this]
      rfl
  · rintro (rfl | rfl)
    · exact ⟨⟨0, by omega⟩, by simp, rfl⟩
    · exact ⟨⟨1, hr⟩, by simp, rfl⟩

theorem hypForm_hypVec (i j : Fin r) : hypForm h r ε (hypVec r ε K i) (hypVec r ε K j) = 0 := by
  unfold hypVec
  rw [hypForm_single_inl]
  simp [Pi.single_apply]

theorem transportSubspace_span_singleton {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) (v : HypIndex r ε → K) :
    transportSubspace h hR (Submodule.span K {v}) = Submodule.span K {R *ᵥ v} := by
  rw [transportSubspace_apply, Submodule.map_span, Set.image_singleton]
  rfl

theorem transport_injective {R : Matrix (Fin (2 * r + ε)) (HypIndex r ε) K}
    (hR : IsHypTransport h R) {a b : HypIndex r ε → K} (hab : R *ᵥ a = R *ᵥ b) : a = b := by
  have := congrArg (fun w => transportInv h R *ᵥ w) hab
  simpa only [Matrix.mulVec_mulVec, transportInv_mul hR, Matrix.one_mulVec] using this

end SUMain


section SUFinal

variable {q f : ℕ} [Fact q.Prime] {K : Type} [Field K] [Finite K] [CharP K q]

theorem hypVec_ne_zero {r ε : ℕ} (a : Fin r) : (hypVec r ε K a) ≠ 0 := fun hz => by
  have := congrFun hz (Sum.inl a)
  simp [hypVec] at this

theorem twoParabolics_PSU_hyp (h : UnitaryFieldData q f K) (hK : Nat.card K = (q ^ f) ^ 2)
    {r ε : ℕ} (hr : 2 ≤ r) (hε : ε ≤ 1) :
    TwoParabolics q (StatedProj (StatedSU (2 * r + ε) (q ^ f) K)) := by
  have hr1 : 1 ≤ r := by omega
  have hr0 : 0 < r := by omega
  have hr2 : 1 < r := by omega
  have hn1 : 1 ≤ 2 * r + ε := by omega
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  set ehyp := hypPSUEquivStatedProj h hR hn1 with hehyp
  have hB : hypProjBorel h r ε ∈ sylowNormalizers h r ε := by
    rw [mem_sylowNormalizers_iff h hr1 hε]
    refine ⟨1, ?_⟩
    have h1 : (MulAut.conj (hypProj h r ε (1 : hypSU h r ε))).toMonoidHom =
        MonoidHom.id (hypPSU h r ε) := by
      rw [map_one]
      ext x
      simp [MulAut.conj_apply]
    rw [h1, Subgroup.map_id]
  obtain ⟨T, hT⟩ := hB
  have hTB : (T : Subgroup (hypPSU h r ε)) ≤ hypProjBorel h r ε := hT ▸ Subgroup.le_normalizer
  set U : Sylow q (StatedProj (StatedSU (2 * r + ε) (q ^ f) K)) :=
    Sylow.mapSurjective (f := ehyp.toMonoidHom) ehyp.surjective T with hU
  have hUc : (U : Subgroup (StatedProj (StatedSU (2 * r + ε) (q ^ f) K))) =
      (T : Subgroup (hypPSU h r ε)).map ehyp.toMonoidHom := Sylow.coe_mapSurjective _ T
  have hcoat : IsCoatom (projIsoStabilizer h r ε (hypFlag h r ε 1)) :=
    isCoatom_projIsoStabilizer_hypFlag h hr1 hε le_rfl hr1
  have hP₁c : IsCoatom ((projIsoStabilizer h r ε (hypFlag h r ε 1)).map ehyp.toMonoidHom) :=
    (OrderIso.isCoatom_iff (MulEquiv.mapSubgroup ehyp) _).2 hcoat
  have hB₁ : hypProjBorel h r ε ≤ projIsoStabilizer h r ε (hypFlag h r ε 1) :=
    hypProjBorel_le_projIsoStabilizer h (le_refl 1) hr1
  have hB₂ : hypProjBorel h r ε ≤ projIsoStabilizer h r ε (hypFlag h r ε 2) :=
    hypProjBorel_le_projIsoStabilizer h (by norm_num : 1 ≤ 2) hr
  set x₁ : Fin (2 * r + ε) → K := R *ᵥ hypVec r ε K ⟨0, hr0⟩ with hx₁
  set x₂ : Fin (2 * r + ε) → K := R *ᵥ hypVec r ε K ⟨1, hr2⟩ with hx₂
  have hF₁ : transportSubspace h hR (hypFlag h r ε 1) = Submodule.span K {x₁} := by
    rw [hypFlag, if_pos hr1, isoFlag_one hr0, transportSubspace_span_singleton]
  have hF₂ : transportSubspace h hR (hypFlag h r ε 2) =
      Submodule.span K {x₁} ⊔ Submodule.span K {x₂} := by
    rw [hypFlag, if_pos hr, isoFlag_two hr2, OrderIso.map_sup, transportSubspace_span_singleton,
      transportSubspace_span_singleton]
  have hP₁le := map_projIsoStabilizer_le (f := f) hR hn1 (hypFlag h r ε 1)
  rw [hF₁] at hP₁le
  have hU₁ : (U : Subgroup (StatedProj (StatedSU (2 * r + ε) (q ^ f) K))) ≤
      (projIsoStabilizer h r ε (hypFlag h r ε 1)).map ehyp.toMonoidHom := by
    rw [hUc]
    exact Subgroup.map_mono (hTB.trans hB₁)
  have hU₂ := (Subgroup.map_mono (hTB.trans hB₂)).trans
    (map_projIsoStabilizer_le (f := f) hR hn1 (hypFlag h r ε 2))
  rw [hF₂] at hU₂
  rw [← hUc] at hU₂
  have hform : ∀ a b : Fin r, (unitaryForm q f hK (2 * r + ε)).β (R *ᵥ hypVec r ε K a)
      (R *ᵥ hypVec r ε K b) = 0 := fun a b => by
    rw [unitaryForm_β_eq_stdHermForm h hK, stdHermForm_transport hR, hypForm_hypVec]
  have hx₁0 : x₁ ≠ 0 := fun hz => hypVec_ne_zero (K := K) (ε := ε) ⟨0, hr0⟩ (transport_injective hR (by
    rw [Matrix.mulVec_zero]
    exact hz))
  have hind : x₂ ∉ Submodule.span K {x₁} := by
    intro hmem
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have h1 : R *ᵥ (a • hypVec r ε K ⟨0, hr0⟩) = R *ᵥ hypVec r ε K ⟨1, hr2⟩ := by
      rw [Matrix.mulVec_smul]
      exact ha
    have h2 := congrFun (transport_injective hR h1) (Sum.inl ⟨1, hr2⟩)
    simp [hypVec, Pi.single_apply] at h2
  exact twoParabolics_of_form (unitaryForm q f hK (2 * r + ε))
    (natRep (StatedSU (2 * r + ε) (q ^ f) K)) (natRep_injective _)
    (isIsometric_natRep_statedSU hK _)
    ((StatedScalars (Fin (2 * r + ε)) K).subgroupOf (StatedSU (2 * r + ε) (q ^ f) K))
    (fun z hz => exists_smul_of_mem_scalars (g := z) hz) (-1) (neg_ne_zero.2 one_ne_zero)
    (fun v => (unitaryForm q f hK (2 * r + ε)).β v v = 0) (ea1_SU hK _) hx₁0
    (hform ⟨0, hr0⟩ ⟨0, hr0⟩) (hform ⟨1, hr2⟩ ⟨1, hr2⟩) (hform ⟨0, hr0⟩ ⟨0, hr0⟩)
    (hform ⟨1, hr2⟩ ⟨1, hr2⟩) (hform ⟨0, hr0⟩ ⟨1, hr2⟩) hind U hP₁c hP₁le hU₁ hU₂

end SUFinal


section SUModel

variable {q : ℕ} [Fact q.Prime]

theorem twoParabolics_PSU {n f : ℕ} {S : Type} [Group S] [Finite S] (hn : 4 ≤ n)
    (hm : StatedClassicalModel S .PSU n q f) : TwoParabolics q S := by
  obtain ⟨r, ε, hε, rfl⟩ : ∃ r ε : ℕ, ε ≤ 1 ∧ n = 2 * r + ε := ⟨n / 2, n % 2, by omega, by omega⟩
  obtain ⟨⟨hq, hf, -⟩, K, _, hfin, hcard, ⟨e⟩⟩ := hm
  have hh : UnitaryFieldData q f K := ⟨hq, hf, by rw [hcard, ← pow_mul, mul_comm]⟩
  haveI : CharP K q := hh.charP
  have key := twoParabolics_PSU_hyp hh hcard (r := r) (ε := ε) (by omega) hε
  exact key.of_mulEquiv e.symm

end SUModel


end CFSG.HardMathSupport.Solomon.Coordinator.YS08.LieQ
