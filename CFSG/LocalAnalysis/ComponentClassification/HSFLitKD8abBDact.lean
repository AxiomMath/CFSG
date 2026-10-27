module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abBAct
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitKD8abT2d

public noncomputable section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup

namespace Sec8

namespace MB

@[expose] def Z4 : List MB := [1, z, k, z * k]

@[expose] def dImgs (py pu c0 c1 : MB) : List MB :=
  [pu, w₁ * y * c0 * py⁻¹, v * (w₁ * y) * c1, z, py, t, z * k]

@[expose] def dValid1 : List (MB × MB × MB × MB) :=
  [(u, y, 1, k), (u, y, 1, z * k), (u, y, z, 1), (u, y, z, z),
    (u * z, z * y, 1, k), (u * z, z * y, 1, z * k), (u * z, z * y, z, 1), (u * z, z * y, z, z)]

@[expose] def dValidT : List (MB × MB × MB × MB) :=
  [(u, y, k, k), (u, y, k, z * k), (u, y, z * k, 1), (u, y, z * k, z),
    (u * z, z * y, k, k), (u * z, z * y, k, z * k), (u * z, z * y, z * k, 1),
    (u * z, z * y, z * k, z)]

theorem dImgs_mem : ∀ py ∈ [u, z * u], ∀ pu ∈ [z * y, y], ∀ c0 ∈ Z4, ∀ c1 ∈ Z4,
    ∀ g ∈ dImgs py pu c0 c1, inR1 g = true := by decide +kernel

@[expose] def dSq (py pu c0 c1 s : MB) : Bool :=
  gensR1.all fun g =>
    applyR1 (compR1 (dImgs py pu c0 c1) (dImgs py pu c0 c1)) g == applyR1 (conjR1 s) g

theorem dSq_one : ∀ py ∈ [u, z * u], ∀ pu ∈ [z * y, y], ∀ c0 ∈ Z4, ∀ c1 ∈ Z4,
    dSq py pu c0 c1 1 = true → (py, pu, c0, c1) ∈ dValid1 := by decide +kernel

theorem dSq_t : ∀ py ∈ [u, z * u], ∀ pu ∈ [z * y, y], ∀ c0 ∈ Z4, ∀ c1 ∈ Z4,
    dSq py pu c0 c1 t = true → (py, pu, c0, c1) ∈ dValidT := by decide +kernel

theorem dSq_of {py pu c0 c1 s : MB}
    (h : ∀ g ∈ gensR1, applyR1 (compR1 (dImgs py pu c0 c1) (dImgs py pu c0 c1)) g =
      applyR1 (conjR1 s) g) : dSq py pu c0 c1 s = true := by
  rw [dSq, List.all_eq_true]
  intro g hg
  exact beq_iff_eq.mpr (h g hg)

end MB

end Sec8

namespace KD8abB

open KD7 KD8ab Sec8

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : L2Data t L}
  {C : A.CaseKD} {S : KDBase A C} {T₁ : Subgroup X}

namespace BData

variable (B : BData S T₁)

theorem ι_mem_Z4 {c : X} (hc : c ∈ (zpowers S.z ⊔ zpowers S.k : Subgroup X)) :
    ∃ c' ∈ MB.Z4, B.ι c' = c := by
  rcases B.G.V₁.eq_of_mem_zk hc with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp [MB.Z4], map_one _⟩
  · exact ⟨MB.z, by simp [MB.Z4], B.ι_z⟩
  · exact ⟨MB.k, by simp [MB.Z4], B.ι_k⟩
  · exact ⟨MB.z * MB.k, by simp [MB.Z4], by rw [map_mul, B.ι_z, B.ι_k]; rfl⟩

theorem d_actsR1 : ∃ py ∈ [MB.u, MB.z * MB.u], ∃ pu ∈ [MB.z * MB.y, MB.y], ∃ c0 ∈ MB.Z4,
    ∃ c1 ∈ MB.Z4, B.ActsR1 C.d (MB.dImgs py pu c0 c1) := by
  obtain ⟨c, hc, hw⟩ := B.G.d_conj_w₁c
  obtain ⟨c', hc', hv⟩ := B.G.d_conj_vN
  obtain ⟨c0, hc0, rfl⟩ := B.ι_mem_Z4 hc
  obtain ⟨c1, hc1, rfl⟩ := B.ι_mem_Z4 hc'
  have hu := B.ι_u
  have hz := B.ι_z
  have hyy := B.ι_y
  have hk := B.ι_k
  have ht := B.ι_t
  have hdz := d_conj_z S (C := C)
  have hdt := d_conj_t (C := C)
  have hdk := B.G.d_conj_k
  have hw₁ : B.ι MB.w₁ = B.ι (MB.w₁ * MB.y) * (B.ι MB.y)⁻¹ := by
    rw [map_mul]; group
  obtain ⟨py, hpy, hdy⟩ : ∃ py ∈ [MB.u, MB.z * MB.u], C.d * S.y * C.d⁻¹ = B.ι py := by
    rcases d_conj_y S (C := C) with h | h
    · exact ⟨MB.u, by simp, by rw [h, hu]⟩
    · exact ⟨MB.z * MB.u, by simp, by rw [h, map_mul, hz, hu]⟩
  obtain ⟨pu, hpu, hdu⟩ : ∃ pu ∈ [MB.z * MB.y, MB.y], C.d * (S.x * S.y) * C.d⁻¹ = B.ι pu := by
    rcases d_conj_xy S (C := C) with h | h
    · exact ⟨MB.z * MB.y, by simp, by rw [h, map_mul, hz, hyy]⟩
    · exact ⟨MB.y, by simp, by rw [h, hyy]⟩
  refine ⟨py, hpy, pu, hpu, c0, hc0, c1, hc1, actsR1_of_map ?_⟩
  simp only [MB.gensR1, MB.dImgs, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨by rw [hu, hdu], ?_, ?_, by rw [hz, hdz], by rw [hyy, hdy], by rw [ht, hdt], ?_⟩
  · rw [hw₁, show C.d * (B.ι (MB.w₁ * MB.y) * (B.ι MB.y)⁻¹) * C.d⁻¹ =
      (C.d * B.ι (MB.w₁ * MB.y) * C.d⁻¹) * (C.d * B.ι MB.y * C.d⁻¹)⁻¹ by group, B.ι_w₁c, hw,
      hyy, hdy, ← B.ι_w₁c]
    simp only [map_mul, map_inv]
  · rw [B.ι_v, hv, ← B.ι_w₁c, ← B.ι_v]
    simp only [map_mul]
  · rw [hk, hdk, map_mul, hz, hk]

variable {B} in
theorem ActsR1.sq_eq {f : List MB} (hd : B.ActsR1 C.d f) (hf : ∀ g ∈ f, MB.inR1 g = true)
    {s : MB} (hs : C.d * C.d = B.ι s) :
    ∀ g ∈ MB.gensR1, MB.applyR1 (MB.compR1 f f) g = MB.applyR1 (MB.conjR1 s) g := by
  intro g hg
  refine (hd.mul hd hf).eq_of_actsAs (B.actsR1_ι s) (by rw [hs]; exact ActsAs.refl _ _) g
    (MB.gensR1_mem g hg)

theorem exists_dValid1 (hd : C.d * C.d = 1) :
    ∃ o ∈ MB.dValid1, B.ActsR1 C.d (MB.dImgs o.1 o.2.1 o.2.2.1 o.2.2.2) := by
  obtain ⟨py, hpy, pu, hpu, c0, hc0, c1, hc1, h⟩ := B.d_actsR1
  refine ⟨(py, pu, c0, c1), MB.dSq_one py hpy pu hpu c0 hc0 c1 hc1 (MB.dSq_of ?_), h⟩
  exact h.sq_eq (MB.dImgs_mem py hpy pu hpu c0 hc0 c1 hc1) (s := 1) (by rw [hd, map_one])

theorem exists_dValidT (hd : C.d * C.d = t) :
    ∃ o ∈ MB.dValidT, B.ActsR1 C.d (MB.dImgs o.1 o.2.1 o.2.2.1 o.2.2.2) := by
  obtain ⟨py, hpy, pu, hpu, c0, hc0, c1, hc1, h⟩ := B.d_actsR1
  refine ⟨(py, pu, c0, c1), MB.dSq_t py hpy pu hpu c0 hc0 c1 hc1 (MB.dSq_of ?_), h⟩
  exact h.sq_eq (MB.dImgs_mem py hpy pu hpu c0 hc0 c1 hc1) (s := MB.t) (by rw [hd, B.ι_t])

end BData

end KD8abB

end CFSG.ComponentClassification.HSFLit
