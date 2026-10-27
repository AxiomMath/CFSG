module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.PerfectCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census228Spor.J3
public import CFSG.RankThree.PartTwo.Sec21.Item228CensusProofSpor
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup CFSG.RankThree.PartTwo.KFacts.K426 CFSG.RankThree.PartTwo.Sec21 CFSG.Blueprint
open CFSG.Sporadic.Schreier (j3P)
open scoped commutatorElement

theorem centralizer_conj_map' {S : Type*} [Group S] (g a : S) :
    centralizer ({g * a * g⁻¹} : Set S) =
      (centralizer ({a} : Set S)).map (MulAut.conj g).toMonoidHom := by
  ext y
  simp only [mem_centralizer_singleton_iff, mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have : y * (g * a * g⁻¹) = g * a * g⁻¹ * y := hy
    calc g⁻¹ * y * g * a = g⁻¹ * (y * (g * a * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * a * g⁻¹ * y) * g := by rw [this]
      _ = a * (g⁻¹ * y * g) := by group
  · rintro ⟨z, hz, rfl⟩
    have : z * a = a * z := hz
    calc g * z * g⁻¹ * (g * a * g⁻¹) = g * (z * a) * g⁻¹ := by group
      _ = g * (a * z) * g⁻¹ := by rw [this]
      _ = g * a * g⁻¹ * (g * z * g⁻¹) := by group

theorem map_conj_eq_of_mem {S : Type*} [Group S] {P : Subgroup S} {k : S} (hk : k ∈ P) :
    P.map (MulAut.conj k).toMonoidHom = P := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact P.mul_mem (P.mul_mem hk hz) (P.inv_mem hk)
  · intro hx
    exact ⟨k⁻¹ * x * k, P.mul_mem (P.mul_mem (P.inv_mem hk) hx) hk, by group⟩

theorem commutator_alt6_eq_top : commutator (alternatingGroup (Fin 6)) = ⊤ := by
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hn : (commutator (alternatingGroup (Fin 6))).Normal := inferInstance
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6))) with h | h
  · exfalso
    let g1 : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 0 1 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    let g2 : alternatingGroup (Fin 6) :=
      ⟨Equiv.swap 1 2 * Equiv.swap 3 4, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩
    have hmem : ⁅g1, g2⁆ ∈ commutator (alternatingGroup (Fin 6)) :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    have hne : g1 * g2 ≠ g2 * g1 := by decide +kernel
    exact hne hmem
  · exact h

theorem perfect_of_equiv_alt6 {S : Type*} [Group S] (D : Subgroup S)
    (e : ↥D ≃* alternatingGroup (Fin 6)) : ⁅D, D⁆ = D := by
  rw [← isPerfect_iff_commutator_eq]
  refine ⟨?_⟩
  apply Subgroup.map_injective (f := e.toMonoidHom) e.injective
  rw [show commutator ↥D = ⁅(⊤ : Subgroup ↥D), ⊤⁆ from rfl,
    Subgroup.map_commutator, Subgroup.map_top, MonoidHom.range_eq_top.2 e.surjective]
  exact commutator_alt6_eq_top

section Main


set_option linter.unusedSectionVars false

theorem exists_A6_in_centralizer_j3P {y : Equiv.Perm (Fin 6156)} (hy : y ∈ j3P)
    (hy3 : orderOf y = 3)
    (h5 : 5 ∣ Nat.card (centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156)))) :
    ∃ Dy : Subgroup (Equiv.Perm (Fin 6156)),
      Dy ≤ centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P ∧
      ⁅centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P,
        centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P⁆ ≤ Dy ∧ ⁅Dy, Dy⁆ = Dy ∧
      Nonempty (↥Dy ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨k0, hk0, c, hc, e', he', hyeq⟩ := j3t_fusion hy hy3
  rcases hc with rfl | rfl
  · have hA3 : j3tXA ^ 3 = 1 := (j3tReps_spec (c := 0) (by norm_num)).2
    obtain ⟨eD⟩ := CFSG.AGLEmbeddingD2.Wilson.Census228Spor.nonempty_mulEquiv_D_alt6
    set D : Subgroup (Equiv.Perm (Fin 6156)) := closure (Set.range j3tD) with hD
    have hDj : D ≤ j3P := (closure_le _).2 (by rintro _ ⟨i, rfl⟩; exact j3tD_mem i)
    have hDC : D ≤ centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :=
      le_inf CFSG.AGLEmbeddingD2.Wilson.Census228Spor.closure_j3tD_le_centralizer hDj
    set σ : Equiv.Perm (Fin 6156) →* Equiv.Perm (Fin 6156) := (MulAut.conj k0).toMonoidHom
      with hσ
    have hσinj : Function.Injective σ := (MulAut.conj k0).injective
    have hCy : centralizer ({y} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P =
        (centralizer ({j3tXA} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P).map σ := by
      rw [Subgroup.map_inf_eq _ _ σ hσinj, hσ, map_conj_eq_of_mem hk0, hyeq,
        centralizer_conj_map', CFSG.Quasithin.Kleidman.centralizer_pow_eq hA3 he']
    refine ⟨D.map σ, ?_, ?_, ?_, ?_⟩
    · rw [hCy]; exact Subgroup.map_mono hDC
    · rw [hCy, ← Subgroup.map_commutator]
      exact Subgroup.map_mono j3t_derived.1
    · rw [← Subgroup.map_commutator, perfect_of_equiv_alt6 D eD]
    · exact ⟨(MulEquiv.subgroupMap (MulAut.conj k0) D).symm.trans eD⟩
  · exfalso
    have hB3 : j3tXB ^ 3 = 1 := (j3tReps_spec (c := 1) (by norm_num)).2
    rw [hyeq, CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_conj hk0 hB3 he',
      ← j3t_caseB.1, j3t_caseB.2] at h5
    omega

set_option maxRecDepth 20000 in
theorem perfect_core_centralizer_J3Cover {X : Type} [Group X] [Finite X]
    (hX : CFSG.IsQuasisimple X) (hZ3 : Nat.card (center X) = 3)
    (e : X ⧸ center X ≃* NativeSporadic.J3) {a : X} (ha : a ∉ center X)
    (ha3 : a ^ 3 ∈ center X)
    (h5 : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} : Set NativeSporadic.J3))) :
    ∃ P : Subgroup X, P ≤ centralizer ({a} : Set X) ∧ ⁅P, P⁆ = P ∧
      Nonempty (↥P ≃* alternatingGroup (Fin 6)) ∧
      ∀ P' : Subgroup X, P' ≤ centralizer ({a} : Set X) → ⁅P', P'⁆ = P' → P' ≤ P := by
  set ψ : X ⧸ center X ≃* ↥j3P := e.trans Item228CensusProof.j3CarrierEquiv with hψ
  set ρ : X →* Equiv.Perm (Fin 6156) :=
    j3P.subtype.comp (ψ.toMonoidHom.comp (QuotientGroup.mk' (center X))) with hρ
  have hρapp : ∀ w : X, ρ w = (ψ (w : X ⧸ center X) : Equiv.Perm (Fin 6156)) := fun w => rfl
  have hρker : ρ.ker = center X := by
    ext w
    rw [MonoidHom.mem_ker, hρapp]
    constructor
    · intro h
      have h1 : ψ (w : X ⧸ center X) = 1 := Subtype.ext h
      rwa [map_eq_one_iff ψ ψ.injective, QuotientGroup.eq_one_iff] at h1
    · intro h
      rw [(QuotientGroup.eq_one_iff w).2 h, map_one]
      rfl
  have hρR : ρ.range = j3P := by
    ext r
    constructor
    · rintro ⟨w, rfl⟩
      rw [hρapp]
      exact (ψ _).2
    · intro hr
      obtain ⟨w, hw⟩ := QuotientGroup.mk_surjective (ψ.symm ⟨r, hr⟩)
      refine ⟨w, ?_⟩
      rw [hρapp, hw, MulEquiv.apply_symm_apply]
  have hK : ∀ P : Subgroup X, P ≤ centralizer ({a} : Set X) → ⁅P, P⁆ = P → P ⊓ ρ.ker = ⊥ := by
    intro P hP hperf
    rw [hρker]
    exact j3CoverCentralizer X hX hZ3 ⟨e⟩ a ha ha3 P hP ((isPerfect_iff_commutator_eq P).2 hperf)
  have hyR : ρ a ∈ j3P := by rw [← hρR]; exact ⟨a, rfl⟩
  have hy3 : orderOf (ρ a) = 3 := by
    have h3 : ρ a ^ 3 = 1 := by
      rw [← map_pow]
      exact (MonoidHom.mem_ker.1 (hρker ▸ ha3))
    have h1 : ρ a ≠ 1 := by
      intro h
      exact ha (hρker ▸ MonoidHom.mem_ker.2 h)
    exact orderOf_eq_prime h3 h1
  have h5' : 5 ∣ Nat.card (centralizer ({ρ a} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P :
      Subgroup (Equiv.Perm (Fin 6156))) := by
    have hya : ρ a = ((Item228CensusProof.j3CarrierEquiv (e (a : X ⧸ center X)) : ↥j3P) :
        Equiv.Perm (Fin 6156)) := hρapp a
    rw [hya]
    have h5c : 5 ∣ Nat.card (centralizer ({e (a : X ⧸ center X)} :
        Set (NativeSporadic.Carrier .J3))) := h5
    generalize e (a : X ⧸ center X) = x at h5c ⊢
    have := CFSG.RankThree.PartTwo.KFacts.K426Rest.card_centralizer_of_mulEquiv
      Item228CensusProof.j3CarrierEquiv x
    exact Dvd.dvd.trans h5c (dvd_of_eq this)
  obtain ⟨Dy, hDy1, hDy2, hDy3, ⟨eD⟩⟩ := exists_A6_in_centralizer_j3P hyR hy3 h5'
  have hpre : ((centralizer ({ρ a} : Set (Equiv.Perm (Fin 6156)))).comap ρ).map ρ =
      centralizer ({ρ a} : Set (Equiv.Perm (Fin 6156))) ⊓ j3P := by
    rw [Subgroup.map_comap_eq, hρR, inf_comm]
  obtain ⟨P, hP1, hP2, -, ⟨eP⟩, hP5⟩ := perfect_core_of_cover ρ hρker.le a Dy
    (by rw [hpre]; exact hDy1) (by rw [hpre]; exact hDy2) hDy3 hK
  exact ⟨P, hP1, hP2, ⟨eP.trans eD⟩, hP5⟩

end Main

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
