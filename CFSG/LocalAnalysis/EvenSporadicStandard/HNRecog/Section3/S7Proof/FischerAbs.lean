module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Shapes
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.Fischer
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Section3.S7Proof.Subtype

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section3

open CFSG.EvenSporadicStandard.HNRecog

theorem s7_fischer_abstract {G : Type} [Group G] [Finite G] (H : Subgroup G) (D : Set G)
    (hDH : D ⊆ (H : Set G)) (hinv : ∀ d ∈ D, d ^ 2 = 1 ∧ d ≠ 1)
    (hnorm : ∀ d ∈ D, ∀ k ∈ H, k * d * k⁻¹ ∈ D)
    (h3 : ∀ d ∈ D, ∀ e ∈ D, (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1) (hne : D.Nonempty)
    (hC : ∀ d ∈ D, H ⊓ Gx d ≤ Subgroup.closure (D ∩ (Gx d : Set G)))
    (hshape : ∀ d ∈ D, IsShapeZ2TimesSym 5 ↥(H ⊓ Gx d)) : IsShapeSym 7 ↥H := by
  let K : Subgroup G := Subgroup.closure D
  have hKH : K ≤ H := (Subgroup.closure_le H).mpr hDH
  let DK : Set ↥K := K.subtype ⁻¹' D
  have hinvK : ∀ d ∈ DK, d ^ 2 = 1 ∧ d ≠ 1 := by
    intro d hd
    obtain ⟨h1, h2⟩ := hinv (d : G) hd
    exact ⟨Subtype.ext (by simpa using h1),
      fun hd1 => h2 (by simpa using congrArg (fun x : ↥K => (x : G)) hd1)⟩
  have hnormK : ∀ d ∈ DK, ∀ k : ↥K, k * d * k⁻¹ ∈ DK := by
    intro d hd k
    exact hnorm (d : G) hd (k : G) (hKH k.2)
  have h3K : ∀ d ∈ DK, ∀ e ∈ DK, (d * e) ^ 3 = 1 ∨ (d * e) ^ 2 = 1 := by
    intro d hd e he
    rcases h3 (d : G) hd (e : G) he with h | h
    · exact Or.inl (Subtype.ext (by simpa using h))
    · exact Or.inr (Subtype.ext (by simpa using h))
  have hgen : Subgroup.closure DK = ⊤ := by
    refine eq_top_iff.mpr (fun m _ => ?_)
    exact (s7_mem_closure_subtype_iff K D Subgroup.subset_closure m).mp
      (show (m : G) ∈ Subgroup.closure D from m.2)
  have hneK : DK.Nonempty := by
    obtain ⟨d, hd⟩ := hne
    exact ⟨⟨d, Subgroup.subset_closure hd⟩, hd⟩
  have hKeq : ∀ d ∈ DK, K ⊓ Gx (d : G) = H ⊓ Gx (d : G) := by
    intro d hd
    refine le_antisymm ?_ ?_
    · exact le_inf (le_trans inf_le_left hKH) inf_le_right
    · refine le_inf ?_ inf_le_right
      exact le_trans (hC (d : G) hd)
        ((Subgroup.closure_le K).mpr (fun x hx => Subgroup.subset_closure hx.1))
  have hle : ∀ d ∈ DK, H ⊓ Gx (d : G) ≤ K := by
    intro d hd
    rw [← hKeq d hd]
    exact inf_le_left
  have hCK : ∀ d ∈ DK, Subgroup.centralizer ({d} : Set ↥K) =
      Subgroup.closure (DK ∩ (Subgroup.centralizer ({d} : Set ↥K) : Set ↥K)) := by
    intro d hd
    refine le_antisymm ?_ ?_
    · intro m hm
      have hmcomm : m * d = d * m := Subgroup.mem_centralizer_singleton_iff.mp hm
      have hmM : (m : G) ∈ K ⊓ Gx (d : G) := by
        refine ⟨m.2, ?_⟩
        have hcomm' : (m : G) * (d : G) = (d : G) * (m : G) := by
          simpa using congrArg (fun x : ↥K => (x : G)) hmcomm
        exact mem_Gx.mpr hcomm'.symm
      have hmH : (m : G) ∈ H ⊓ Gx (d : G) := by
        rwa [hKeq d hd] at hmM
      have hmClosure : (m : G) ∈ Subgroup.closure (D ∩ (Gx (d : G) : Set G)) :=
        hC (d : G) hd hmH
      have hsub : K.subtype ⁻¹' (D ∩ (Gx (d : G) : Set G)) ⊆
          DK ∩ (Subgroup.centralizer ({d} : Set ↥K) : Set ↥K) := by
        intro x hx
        refine ⟨hx.1, ?_⟩
        have hxcomm : (d : G) * (x : G) = (x : G) * (d : G) := mem_Gx.mp hx.2
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subtype.ext (by simpa using hxcomm.symm))
      have hmCl : m ∈ Subgroup.closure
          (K.subtype ⁻¹' (D ∩ (Gx (d : G) : Set G))) :=
        (s7_mem_closure_subtype_iff K (D ∩ (Gx (d : G) : Set G))
          (fun x hx => Subgroup.subset_closure hx.1) m).mp hmClosure
      exact Subgroup.closure_mono hsub hmCl
    · exact (Subgroup.closure_le _).mpr Set.inter_subset_right
  have hshapeK : ∀ d ∈ DK, Nonempty (↥(Subgroup.centralizer ({d} : Set ↥K)) ≃*
      Z 2 × Sym 5) := by
    intro d hd
    have hL : ∀ g : G, g ∈ K ⊓ Gx (d : G) ↔ g ∈ K ∧ g * (d : G) = (d : G) * g := by
      intro g
      rw [Subgroup.mem_inf, mem_Gx]
      exact and_congr Iff.rfl eq_comm
    obtain ⟨e1⟩ := s7_centralizer_subtype_equiv K d (K ⊓ Gx (d : G)) hL
    have h2 := hshape (d : G) hd
    rw [IsShapeZ2TimesSym] at h2
    obtain ⟨e2⟩ := h2
    exact ⟨e1.trans ((MulEquiv.subgroupCongr (hKeq d hd)).trans e2)⟩
  obtain ⟨⟨isoK⟩, hconjK⟩ := fischer_S7 DK hinvK hnormK h3K hgen hneK hCK hshapeK
  have hHK : H ≤ K := by
    intro h hh
    obtain ⟨d0, hd0⟩ := hne
    have hconj_mem : h * d0 * h⁻¹ ∈ D := hnorm d0 hd0 h hh
    have hd0K : (⟨d0, Subgroup.subset_closure hd0⟩ : ↥K) ∈ DK := hd0
    have heK : (⟨h * d0 * h⁻¹, Subgroup.subset_closure hconj_mem⟩ : ↥K) ∈ DK := hconj_mem
    obtain ⟨k, hk⟩ := isConj_iff.1
      (hconjK ⟨d0, Subgroup.subset_closure hd0⟩ hd0K
        ⟨h * d0 * h⁻¹, Subgroup.subset_closure hconj_mem⟩ heK)
    have hkG : (k : G) * d0 * (k : G)⁻¹ = h * d0 * h⁻¹ := by
      simpa using congrArg (fun x : ↥K => (x : G)) hk
    have hucomm : d0 * ((k : G)⁻¹ * h) = ((k : G)⁻¹ * h) * d0 := by
      calc d0 * ((k : G)⁻¹ * h)
          = (k : G)⁻¹ * ((k : G) * d0 * (k : G)⁻¹) * h := by group
        _ = (k : G)⁻¹ * (h * d0 * h⁻¹) * h := by rw [hkG]
        _ = ((k : G)⁻¹ * h) * d0 := by group
    have huH : (k : G)⁻¹ * h ∈ H := H.mul_mem (H.inv_mem (hKH k.2)) hh
    have huGx : (k : G)⁻¹ * h ∈ Gx d0 := by
      rw [mem_Gx]
      exact hucomm
    have huK : (k : G)⁻¹ * h ∈ K :=
      hle ⟨d0, Subgroup.subset_closure hd0⟩ hd0K ⟨huH, huGx⟩
    have hh_eq : h = (k : G) * ((k : G)⁻¹ * h) := by group
    rw [hh_eq]
    exact K.mul_mem k.2 huK
  have hHK_eq : H = K := le_antisymm hHK hKH
  rw [IsShapeSym]
  exact ⟨(MulEquiv.subgroupCongr hHK_eq).trans isoK⟩

end CFSG.EvenSporadicStandard.HNRecog.Section3
