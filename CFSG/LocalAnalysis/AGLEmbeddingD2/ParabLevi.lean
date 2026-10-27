module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanLieOutRadical
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTits
public import CFSG.LocalAnalysis.AGLEmbeddingD2.LeviSection
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.Open.Defs

public section

namespace CFSG.AGLEmbeddingD2.ParabLevi

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbedding.LieOut
open scoped commutatorElement

variable {K : Type*} [Group K]

section Defs

variable (D : UniversalRootDatum K)

@[expose] def leviRad (I : Set (Fin D.rank)) : Subgroup K := ⨆ j ∈ Iᶜ, radical D j

@[expose] def leviM (I : Set (Fin D.rank)) : Subgroup K := ⨆ i ∈ I, rankOne D.rootGroup i

end Defs

variable {D : UniversalRootDatum K} {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K}
  {I : Set (Fin D.rank)}

theorem radical_le_leviRad {j : Fin D.rank} (hj : j ∉ I) : radical D j ≤ leviRad D I :=
  le_iSup₂_of_le (f := fun j (_ : j ∈ Iᶜ) => radical D j) j hj le_rfl

theorem rankOne_le_leviM {i : Fin D.rank} (hi : i ∈ I) : rankOne D.rootGroup i ≤ leviM D I :=
  le_iSup₂_of_le (f := fun i (_ : i ∈ I) => rankOne D.rootGroup i) i hi le_rfl

theorem leviRad_le_posUnipotent : leviRad D I ≤ posUnipotent D :=
  iSup₂_le fun j _ => radical_le_posUnipotent j

theorem isPGroup_leviRad (hext : SteinbergExtras D n H)
    (hp : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ)) : IsPGroup 2 (leviRad D I) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (isPGroup_iSup_pos hext hp).to_le leviRad_le_posUnipotent

section Weyl

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H)

include hct in
theorem nrep_mem_leviM {z : (coxeterMatrix D.isFiniteType).Group}
    (hz : z ∈ (coxeterMatrix D.isFiniteType).toCoxeterSystem.parabolic I) :
    nrep hct z ∈ leviM D I := by
  obtain ⟨ω, hω, hωI, rfl⟩ :=
    (coxeterMatrix D.isFiniteType).toCoxeterSystem.exists_isReduced_wordProd_eq_of_mem_parabolic hz
  rw [nrep_wordProd hct hω]
  apply list_prod_mem
  intro y hy
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hy
  exact rankOne_le_leviM (hωI b hb) (hct.n_mem b)

include hct in
theorem rootGroup_le_leviM {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (hsupp : ∀ k ∉ I, γ k = 0) : D.rootGroup γ ≤ leviM D I := by
  have hΦ := CFSG.LieType.RootSystem.isCTRootSystem D.isFiniteType D.divisible
  intro x hx
  obtain ⟨w, i, c, hc, rfl⟩ := hΦ.exists_eq γ hγ
  have hsupp' : ∀ k ∉ I, weylAction D.isFiniteType w (Pi.single i 1) k = 0 := by
    intro k hk
    have := hsupp k hk
    simp only [Pi.smul_apply, smul_eq_mul, mul_eq_zero] at this
    exact this.resolve_left hc
  obtain ⟨z, hz, m, hm, hzm⟩ := hΦ.exists_parabolic I w i hsupp'
  have hzγ : weylAction D.isFiniteType z (c • weylAction D.isFiniteType w (Pi.single i 1)) =
      c • Pi.single m 1 := by
    rw [map_zsmul, hzm]
  have hcm : c • (Pi.single m 1 : Fin D.rank → ℤ) ∈ D.roots := hzγ ▸ hΦ.smul_mem z _ hγ
  have hconj : nrep hct z * x * (nrep hct z)⁻¹ ∈ D.rootGroup (c • Pi.single m 1) := by
    rw [← hzγ, ← actsAs_nrep hct z _ hγ]
    exact ⟨x, hx, rfl⟩
  have hrank : D.rootGroup (c • Pi.single m 1) ≤ rankOne D.rootGroup m :=
    hct.le_rankOne m _ hcm fun k hk => by simp [Pi.single_eq_of_ne hk]
  have hmem := rankOne_le_leviM hm (hrank hconj)
  have hnz := nrep_mem_leviM hct hz
  have e : x = (nrep hct z)⁻¹ * (nrep hct z * x * (nrep hct z)⁻¹) * nrep hct z := by group
  rw [e]
  exact mul_mem (mul_mem (inv_mem hnz) hmem) hnz

include hct in
theorem posUnipotent_le_leviRad_sup_leviM : posUnipotent D ≤ leviRad D I ⊔ leviM D I := by
  refine iSup₂_le fun γ hγ => ?_
  by_cases h : ∃ j ∉ I, 0 < γ j
  · obtain ⟨j, hj, hγj⟩ := h
    exact (rootGroup_le_radical hγ.1 hγj).trans ((radical_le_leviRad hj).trans le_sup_left)
  · push Not at h
    refine (rootGroup_le_leviM hct hγ.1 fun k hk => ?_).trans le_sup_right
    exact le_antisymm (h k hk) (coord_nonneg_of_ht_pos hγ.1 hγ.2 k)

end Weyl

section Normal

variable (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
  (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

theorem le_normalizer_leviRad {A : Subgroup K}
    (h : ∀ j ∉ I, A ≤ Subgroup.normalizer (radical D j : Set K)) :
    A ≤ Subgroup.normalizer (leviRad D I : Set K) :=
  le_normalizer_iSup fun j => le_normalizer_iSup fun hj => h j hj

theorem le_normalizer_leviM {A : Subgroup K}
    (h : ∀ i ∈ I, A ≤ Subgroup.normalizer (rankOne D.rootGroup i : Set K)) :
    A ≤ Subgroup.normalizer (leviM D I : Set K) :=
  le_normalizer_iSup fun i => le_normalizer_iSup fun hi => h i hi

include hct hext in
theorem borel_le_normalizer_leviRad : borel D H ≤ Subgroup.normalizer (leviRad D I : Set K) :=
  le_normalizer_leviRad fun j _ => borel_le_normalizer_radical hct hext j

include hext in
theorem rankOne_le_normalizer_leviRad {i : Fin D.rank} (hi : i ∈ I) :
    rankOne D.rootGroup i ≤ Subgroup.normalizer (leviRad D I : Set K) :=
  le_normalizer_leviRad fun _ hj =>
    rankOne_le_normalizer_radical hext fun hij => hj (hij ▸ hi)

include hct in
theorem torus_le_normalizer_leviM :
    (⨆ k, H k) ≤ Subgroup.normalizer (leviM D I : Set K) := by
  refine le_normalizer_leviM fun i _ => le_normalizer_sup ?_ ?_
  · exact iSup_le_normalizer_rootGroup hct
      ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i)
  · exact iSup_le_normalizer_rootGroup hct ((RootSystem.ofCartan D.isFiniteType
      D.divisible).neg_mem _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem i))

include hct hext in
theorem le_normalizer_leviRad_sup_leviM {A : Subgroup K} (hBA : borel D H ≤ A) :
    A ≤ Subgroup.normalizer
      ((leviRad D (negIndices D A) ⊔ leviM D (negIndices D A) : Subgroup K) : Set K) := by
  have hself : (leviRad D (negIndices D A) ⊔ leviM D (negIndices D A) : Subgroup K) ≤
      Subgroup.normalizer
        ((leviRad D (negIndices D A) ⊔ leviM D (negIndices D A) : Subgroup K) : Set K) :=
    Subgroup.le_normalizer
  refine (eq_borel_sup_rankOne hct hext hBA).le.trans ?_
  refine sup_le (sup_le ?_ ?_) (iSup₂_le fun i hi => ?_)
  · exact le_normalizer_sup ((le_sup_left.trans (borel_le_normalizer_leviRad hct hext)))
      (torus_le_normalizer_leviM hct)
  · exact (posUnipotent_le_leviRad_sup_leviM hct).trans hself
  · exact ((rankOne_le_leviM hi).trans le_sup_right).trans hself

include hct hext in
theorem le_torus_sup_leviRad_sup_leviM {A : Subgroup K} (hBA : borel D H ≤ A) :
    A ≤ (⨆ k, H k) ⊔ (leviRad D (negIndices D A) ⊔ leviM D (negIndices D A)) := by
  refine (eq_borel_sup_rankOne hct hext hBA).le.trans ?_
  refine sup_le (sup_le le_sup_left ((posUnipotent_le_leviRad_sup_leviM hct).trans le_sup_right))
    (iSup₂_le fun i hi => ((rankOne_le_leviM hi).trans le_sup_right).trans le_sup_right)

include hext in
theorem isMulCommutative_torus : IsMulCommutative ↥(⨆ k, H k) := by
  rw [Subgroup.iSup_eq_closure]
  apply Subgroup.isMulCommutative_closure
  intro x hx y hy _
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  obtain ⟨j, hj⟩ := Set.mem_iUnion.mp hy
  exact hext.torus_commute i j x hi y hj

theorem leviRad_sup_leviM_le {A : Subgroup K} (hBA : borel D H ≤ A) :
    leviRad D (negIndices D A) ⊔ leviM D (negIndices D A) ≤ A :=
  sup_le (leviRad_le_posUnipotent.trans (le_sup_right.trans hBA))
    (iSup₂_le fun _ hi => rankOne_le_of_mem_negIndices hBA hi)

include hct hext in
theorem commutator_le_leviRad_sup_leviM {A : Subgroup K} (hBA : borel D H ≤ A) :
    ⁅A, A⁆ ≤ leviRad D (negIndices D A) ⊔ leviM D (negIndices D A) := by
  set N := leviRad D (negIndices D A) ⊔ leviM D (negIndices D A) with hN
  have hNA : N ≤ A := leviRad_sup_leviM_le hBA
  have hTA : (⨆ k, H k) ≤ A := le_sup_left.trans hBA
  have hnorm : (N.subgroupOf A).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mpr
      (le_normalizer_leviRad_sup_leviM hct hext hBA)
  have htop : N.subgroupOf A ⊔ (⨆ k, H k).subgroupOf A = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hNA hTA, Subgroup.subgroupOf_eq_top, sup_comm]
    exact le_torus_sup_leviRad_sup_leviM hct hext hBA
  have hcomm : IsMulCommutative ↥((⨆ k, H k).subgroupOf A) := by
    have hT := isMulCommutative_torus hext
    refine ⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩
    have := congrArg Subtype.val (hT.is_comm.comm ⟨(a : K), a.2⟩ ⟨(b : K), b.2⟩)
    exact this
  have hle := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top htop hcomm
  rw [← Subgroup.map_subtype_commutator]
  refine (Subgroup.map_mono hle).trans ?_
  rintro _ ⟨x, hx, rfl⟩
  exact hx

include hct hext in
theorem hasSubquotient_leviM {A : Subgroup K} (hBA : borel D H ≤ A)
    (hp : ∀ γ ∈ D.roots, IsPGroup 2 (D.rootGroup γ)) {Q : Type*} [Group Q]
    (hQ : commutator Q = ⊤) (hQ2 : ∀ R : Subgroup Q, R.Normal → IsPGroup 2 R → R = ⊥)
    (h : LeviSection.HasSubquotient A Q) :
    LeviSection.HasSubquotient (leviM D (negIndices D A)) Q := by
  have h1 := (h.commutator hQ).mono (commutator_le_leviRad_sup_leviM hct hext hBA)
  have hnorm : leviRad D (negIndices D A) ⊔ leviM D (negIndices D A) ≤
      Subgroup.normalizer (leviRad D (negIndices D A) : Set K) :=
    sup_le Subgroup.le_normalizer
      (iSup₂_le fun _ hi => rankOne_le_normalizer_leviRad hext hi)
  exact h1.of_sup_normal_pGroup le_sup_left le_sup_right hnorm le_rfl
    (isPGroup_leviRad hext hp) hQ2

end Normal

end CFSG.AGLEmbeddingD2.ParabLevi
