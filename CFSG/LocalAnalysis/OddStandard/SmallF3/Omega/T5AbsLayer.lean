module

import CFSG.RankThree.PartTwo.Sec21.Item21Res7ProofCensusTools
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeF
import CFSG.Quasithin.Background.RonanD34
import CFSG.GH74.GLS.Stage2.Bender.Thm2.Naturality
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.GroupTheory.LocalCores.Components

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

open scoped commutatorElement

variable {A B : Type} [Group A] [Group B]

theorem inSubgroup_layer_eq_of_two_index [Finite A] {K K' : Subgroup A} (hKK : K ≤ K')
    (hN : (K.subgroupOf K').Normal) (hidx : ∃ n : ℕ, (K.subgroupOf K').index = 2 ^ n) :
    CFSG.inSubgroup CFSG.layer K' = CFSG.inSubgroup CFSG.layer K := by
  let W : Subgroup ↥K' := K.subgroupOf K'
  have hWn : W.Normal := hN
  have hidxW : ∃ n : ℕ, W.index = 2 ^ n := hidx
  have hle : CFSG.layer ↥K' ≤ W :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.s15_Three_layer_le_of_two_index hWn hidxW
  have hlayer : (CFSG.layer ↥W).map W.subtype = CFSG.layer ↥K' := by
    refine le_antisymm (CFSG.Quasithin.RonanD34.map_layer_le_layer_of_normal hWn) ?_
    rw [CFSG.layer.eq_sSup (G := ↥K')]
    refine sSup_le fun C hC => ?_
    have hCW : C ≤ W := (CFSG.LocalCores.component_le_layer hC).trans hle
    have hcompC : CFSG.IsComponent (C.subgroupOf W) :=
      CFSG.LocalCores.component_overgroup hC hCW
    have hmap : C ≤ (CFSG.layer ↥W).map W.subtype := by
      have h := Subgroup.map_mono (f := W.subtype)
        (CFSG.LocalCores.component_le_layer hcompC)
      rwa [Subgroup.map_subgroupOf_eq_of_le hCW] at h
    exact hmap
  let e : ↥W ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKK
  have he : (CFSG.layer ↥W).map e.toMonoidHom = CFSG.layer ↥K :=
    CFSG.GH74.GLS.Stage2.Bender.Thm2.layer_map_mulEquiv e
  have hhom : K.subtype.comp e.toMonoidHom = K'.subtype.comp W.subtype := by
    ext x
    rfl
  change (CFSG.layer ↥K').map K'.subtype = (CFSG.layer ↥K).map K.subtype
  have hfin : (CFSG.layer ↥K).map K.subtype = (CFSG.layer ↥K').map K'.subtype := by
    rw [← he, Subgroup.map_map, hhom, ← Subgroup.map_map]
    exact congrArg (fun S : Subgroup ↥K' => S.map K'.subtype) hlayer
  exact hfin.symm

theorem cent_normal_two_index [Finite A] (f : A →* B) (hz : f.ker ≤ Subgroup.center A)
    (h2 : ∀ k ∈ f.ker, k * k = 1) (H : Subgroup A) (s : A) :
    H ⊓ Subgroup.centralizer ({s} : Set A) ≤
        H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f ∧
      ((H ⊓ Subgroup.centralizer ({s} : Set A)).subgroupOf
        (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f)).Normal ∧
      ∃ n : ℕ, ((H ⊓ Subgroup.centralizer ({s} : Set A)).subgroupOf
        (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f)).index = 2 ^ n := by
  have hKle : H ⊓ Subgroup.centralizer ({s} : Set A) ≤
      H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f := by
    intro h hh
    rw [Subgroup.mem_inf] at hh ⊢
    refine ⟨hh.1, ?_⟩
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    subst hg
    have hsh : s * h = h * s :=
      Subgroup.mem_centralizer_iff.mp hh.2 s (Set.mem_singleton s)
    rw [← map_mul, ← map_mul, hsh]
  let c : A → A := fun h => ⁅s, h⁆
  have hcmem : ∀ h : ↥(H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f), c h ∈ f.ker := by
    intro h
    have hfh : f (h : A) ∈ Subgroup.centralizer ({f s} : Set B) := h.2.2
    have hcomm : f s * f (h : A) = f (h : A) * f s :=
      Subgroup.mem_centralizer_iff.mp hfh (f s) (Set.mem_singleton (f s))
    rw [MonoidHom.mem_ker]
    have hmap : f (c h) = ⁅f s, f (h : A)⁆ := by
      simp only [c]
      exact map_commutatorElement f (g₁ := s) (g₂ := (h : A))
    rw [hmap, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm
  have hc1 : c 1 = 1 := by
    simp only [c]
    exact commutatorElement_one_right s
  have hcmul : ∀ h h' : ↥(H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f),
      c ((h : A) * (h' : A)) = c (h : A) * c (h' : A) := by
    intro h h'
    have hch' : c (h' : A) ∈ Subgroup.center A := hz (hcmem h')
    have hcomm : (h : A) * c (h' : A) = c (h' : A) * (h : A) :=
      Subgroup.mem_center_iff.mp hch' (h : A)
    have hstep : c ((h : A) * (h' : A)) =
        c (h : A) * (h : A) * c (h' : A) * (h : A)⁻¹ := by
      simp only [c]
      exact commutatorElement_mul_right_eq_mul_conj s (h : A) (h' : A)
    rw [hstep]
    calc c (h : A) * (h : A) * c (h' : A) * (h : A)⁻¹
        = c (h : A) * ((h : A) * c (h' : A)) * (h : A)⁻¹ := by group
      _ = c (h : A) * (c (h' : A) * (h : A)) * (h : A)⁻¹ := by rw [hcomm]
      _ = c (h : A) * c (h' : A) := by group
  let ψ : ↥(H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f) →* ↥f.ker :=
    { toFun := fun h => ⟨c h, hcmem h⟩
      map_one' := Subtype.ext hc1
      map_mul' := fun h h' => Subtype.ext (hcmul h h') }
  have hker : ψ.ker = (H ⊓ Subgroup.centralizer ({s} : Set A)).subgroupOf
      (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f) := by
    ext h
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro hh
      have hc : c (h : A) = 1 := by
        have h := congrArg (Subtype.val : ↥f.ker → A) hh
        simpa [ψ] using h
      refine ⟨h.2.1, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [Set.mem_singleton_iff] at hg
      subst hg
      exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [c] using hc)
    · intro hh
      have hcent : (h : A) ∈ Subgroup.centralizer ({s} : Set A) := hh.2
      have hch : c (h : A) = 1 := by
        change ⁅s, (h : A)⁆ = 1
        rw [commutatorElement_eq_one_iff_mul_comm]
        exact Subgroup.mem_centralizer_iff.mp hcent s (Set.mem_singleton s)
      show ψ h = 1
      exact Subtype.ext hch
  have hsq : ∀ y : ↥ψ.range, y * y = 1 := by
    rintro ⟨y, hy⟩
    rw [MonoidHom.mem_range] at hy
    obtain ⟨h, rfl⟩ := hy
    apply Subtype.ext
    exact Subtype.ext (h2 (c h) (hcmem h))
  have hP : IsPGroup 2 ↥ψ.range := fun g => ⟨1, by
    simpa [pow_two] using hsq g⟩
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  refine ⟨hKle, ?_, ⟨n, ?_⟩⟩
  · rw [← hker]
    exact MonoidHom.normal_ker ψ
  · rw [← hker, Subgroup.index_ker]
    exact hn

theorem map_inSubgroup_layer [Finite A] (f : A →* B) (hz : f.ker ≤ Subgroup.center A)
    (K : Subgroup A) :
    (CFSG.inSubgroup CFSG.layer K).map f = CFSG.inSubgroup CFSG.layer (K.map f) := by
  let fK : ↥K →* ↥(K.map f) := f.subgroupMap K
  have hfK : Function.Surjective fK := f.subgroupMap_surjective K
  have hker : fK.ker ≤ Subgroup.center ↥K := by
    intro k hk
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hkA : (k : A) ∈ f.ker := by
      rw [MonoidHom.mem_ker] at hk
      have h := congrArg (Subtype.val : ↥(K.map f) → B) hk
      simpa [fK, MonoidHom.subgroupMap_apply_coe] using h
    have hcen : (k : A) ∈ Subgroup.center A := hz hkA
    exact Subgroup.mem_center_iff.mp hcen (y : A)
  have hmap := CFSG.RankThree.PartTwo.Sec21.Item21Res7Proof.map_layer_of_surjective fK hfK hker
  have hhom : f.comp K.subtype = (K.map f).subtype.comp fK := by
    ext x
    rfl
  change ((CFSG.layer ↥K).map K.subtype).map f =
    (CFSG.layer ↥(K.map f)).map (K.map f).subtype
  calc ((CFSG.layer ↥K).map K.subtype).map f
      = (CFSG.layer ↥K).map (f.comp K.subtype) := by rw [Subgroup.map_map]
    _ = (CFSG.layer ↥K).map ((K.map f).subtype.comp fK) := by rw [hhom]
    _ = ((CFSG.layer ↥K).map fK).map (K.map f).subtype := by rw [Subgroup.map_map]
    _ = (CFSG.layer ↥(K.map f)).map (K.map f).subtype := by rw [hmap]

theorem map_comap_centralizer (f : A →* B) (H : Subgroup A) (s : A) :
    (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f).map f =
      H.map f ⊓ Subgroup.centralizer ({f s} : Set B) := by
  ext b
  constructor
  · intro hb
    rw [Subgroup.mem_map] at hb
    obtain ⟨h, hh, rfl⟩ := hb
    rw [Subgroup.mem_inf]
    exact ⟨Subgroup.mem_map_of_mem f hh.1, hh.2⟩
  · intro hb
    rw [Subgroup.mem_inf] at hb
    obtain ⟨hbH, hbC⟩ := hb
    rw [Subgroup.mem_map] at hbH ⊢
    obtain ⟨h, hh, rfl⟩ := hbH
    exact ⟨h, ⟨hh, hbC⟩, rfl⟩

theorem map_layer_cent [Finite A] (f : A →* B) (hz : f.ker ≤ Subgroup.center A)
    (h2 : ∀ k ∈ f.ker, k * k = 1) (H : Subgroup A) (s : A) :
    CFSG.inSubgroup CFSG.layer (H.map f ⊓ Subgroup.centralizer ({f s} : Set B)) =
      (CFSG.inSubgroup CFSG.layer (H ⊓ Subgroup.centralizer ({s} : Set A))).map f := by
  obtain ⟨hKle, hN, hidx⟩ := cent_normal_two_index f hz h2 H s
  have heq : CFSG.inSubgroup CFSG.layer
      (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f) =
      CFSG.inSubgroup CFSG.layer (H ⊓ Subgroup.centralizer ({s} : Set A)) :=
    inSubgroup_layer_eq_of_two_index hKle hN hidx
  have h1 : CFSG.inSubgroup CFSG.layer (H.map f ⊓ Subgroup.centralizer ({f s} : Set B)) =
      CFSG.inSubgroup CFSG.layer
        ((H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f).map f) :=
    congrArg (CFSG.inSubgroup CFSG.layer) (map_comap_centralizer f H s).symm
  have h2' : CFSG.inSubgroup CFSG.layer
        ((H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f).map f) =
      (CFSG.inSubgroup CFSG.layer
        (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f)).map f :=
    (map_inSubgroup_layer f hz (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f)).symm
  have h3 : (CFSG.inSubgroup CFSG.layer
        (H ⊓ (Subgroup.centralizer ({f s} : Set B)).comap f)).map f =
      (CFSG.inSubgroup CFSG.layer (H ⊓ Subgroup.centralizer ({s} : Set A))).map f :=
    congrArg (fun S => S.map f) heq
  exact h1.trans (h2'.trans h3)

end CFSG.OddStandard.SmallF3.Omega
