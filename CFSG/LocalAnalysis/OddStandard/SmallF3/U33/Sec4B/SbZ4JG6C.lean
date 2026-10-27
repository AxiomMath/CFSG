module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4JG2A

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type} [Group G] [Finite G] {NQ : Subgroup G} {N : Subgroup ↥NQ} [N.Normal]

theorem z4j_d17_transport {Vc Vsub : Subgroup ↥NQ} {Vh : Subgroup (↥NQ ⧸ N)}
    (hVc : Z4JLift N Vc Vh) (hVsub : Vsub ≤ Vc) {b : ↥NQ} (hb : b ∈ Vc)
    (h17G : 17 ≤ {x : G | x ∈ Vc.map NQ.subtype ⊓ centralizer ({(b : G)} : Set G) ⊓
      centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) ∧ x * x = 1}.ncard) :
    17 ≤ {u : ↥NQ ⧸ N | u ∈ Vh ⊓ centralizer ({z4iπ N b} : Set (↥NQ ⧸ N)) ⊓
      centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) ∧
      u * u = 1}.ncard := by
  let Ax : Set ↥NQ := {x₀ | x₀ ∈ Vc ∧ b * x₀ = x₀ * b ∧
    (∀ v ∈ Vsub, v * x₀ = x₀ * v) ∧ x₀ * x₀ = 1}
  let A : Set G := {x : G | x ∈ Vc.map NQ.subtype ⊓ centralizer ({(b : G)} : Set G) ⊓
    centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) ∧ x * x = 1}
  let B : Set (↥NQ ⧸ N) := {u : ↥NQ ⧸ N | u ∈ Vh ⊓ centralizer ({z4iπ N b} : Set (↥NQ ⧸ N)) ⊓
    centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) ∧
    u * u = 1}
  change 17 ≤ B.ncard
  have hAxmem : ∀ x₀ : ↥NQ, x₀ ∈ Ax ↔ x₀ ∈ Vc ∧ b * x₀ = x₀ * b ∧
      (∀ v ∈ Vsub, v * x₀ = x₀ * v) ∧ x₀ * x₀ = 1 := fun _ => Iff.rfl
  have hAmem : ∀ x : G, x ∈ A ↔ x ∈ Vc.map NQ.subtype ⊓ centralizer ({(b : G)} : Set G) ⊓
      centralizer ((Vsub.map NQ.subtype : Subgroup G) : Set G) ∧ x * x = 1 := fun _ => Iff.rfl
  have hBmem : ∀ u : ↥NQ ⧸ N, u ∈ B ↔ u ∈ Vh ⊓ centralizer ({z4iπ N b} : Set (↥NQ ⧸ N)) ⊓
      centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) ∧
      u * u = 1 := fun _ => Iff.rfl
  have hsub : A ⊆ (fun x₀ : ↥NQ => (x₀ : G)) '' Ax := by
    intro x hx
    rw [hAmem] at hx
    obtain ⟨hxmem, hxsq⟩ := hx
    rw [Subgroup.mem_inf] at hxmem
    obtain ⟨hxmem, hxcv⟩ := hxmem
    rw [Subgroup.mem_inf] at hxmem
    obtain ⟨hxV, hxcb⟩ := hxmem
    obtain ⟨x₀, hx₀V, hx₀eq⟩ := Subgroup.mem_map.1 hxV
    have hx₀eq' : (x₀ : G) = x := hx₀eq
    refine ⟨x₀, ?_, hx₀eq'⟩
    rw [hAxmem]
    have hb : b * x₀ = x₀ * b := by
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_iff.1 hxcb (b : G) (Set.mem_singleton (b : G))
      rw [← hx₀eq'] at h
      simpa using h
    have hv : ∀ v ∈ Vsub, v * x₀ = x₀ * v := by
      intro v hv
      apply Subtype.ext
      have h := Subgroup.mem_centralizer_iff.1 hxcv (v : G)
        (Subgroup.mem_map_of_mem NQ.subtype hv)
      rw [← hx₀eq'] at h
      simpa using h
    have hsq : x₀ * x₀ = 1 := by
      apply Subtype.ext
      show (x₀ : G) * (x₀ : G) = (1 : G)
      rw [hx₀eq']
      exact hxsq
    exact ⟨hx₀V, hb, hv, hsq⟩
  have hBsup : (z4iπ N) '' Ax ⊆ B := by
    rintro u ⟨x₀, hx₀, rfl⟩
    rw [hBmem]
    rw [hAxmem] at hx₀
    obtain ⟨hx₀V, hx₀b, hx₀v, hx₀sq⟩ := hx₀
    have hVh : z4iπ N x₀ ∈ Vh := by
      rw [← hVc.map_eq]
      exact Subgroup.mem_map_of_mem (z4iπ N) hx₀V
    have hcentb : z4iπ N x₀ ∈ centralizer ({z4iπ N b} : Set (↥NQ ⧸ N)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      rw [← map_mul, ← map_mul, hx₀b]
    have hcentv : z4iπ N x₀ ∈
        centralizer ((Vsub.map (z4iπ N) : Subgroup (↥NQ ⧸ N)) : Set (↥NQ ⧸ N)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hw
      rw [← map_mul, ← map_mul, hx₀v v hv]
    refine ⟨?_, ?_⟩
    · rw [Subgroup.mem_inf, Subgroup.mem_inf]
      exact ⟨⟨hVh, hcentb⟩, hcentv⟩
    · simp only [← map_mul, hx₀sq, map_one]
  have hA_le : A.ncard ≤ ((fun x₀ : ↥NQ => (x₀ : G)) '' Ax).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have himg_le : ((fun x₀ : ↥NQ => (x₀ : G)) '' Ax).ncard ≤ Ax.ncard :=
    Set.ncard_image_le (Set.toFinite _)
  have hInj : Set.InjOn (z4iπ N) Ax := by
    intro a ha a' ha' hab
    rw [hAxmem] at ha ha'
    exact hVc.inj ha.1 ha'.1 hab
  have hcard : (z4iπ N '' Ax).ncard = Ax.ncard := hInj.ncard_image
  have hB_le : (z4iπ N '' Ax).ncard ≤ B.ncard :=
    Set.ncard_le_ncard hBsup (Set.toFinite _)
  calc 17 ≤ A.ncard := h17G
    _ ≤ ((fun x₀ : ↥NQ => (x₀ : G)) '' Ax).ncard := hA_le
    _ ≤ Ax.ncard := himg_le
    _ = (z4iπ N '' Ax).ncard := hcard.symm
    _ ≤ B.ncard := hB_le

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
