module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH0

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H}

private lemma s888_comm_iff_commutator {a b : X} :
    a * b = b * a ↔ a * b * a⁻¹ * b⁻¹ = 1 := by
  constructor
  · intro h
    rw [h]
    group
  · intro h
    calc
      a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h, one_mul]

private lemma s888_iso_z_eq_neg_one (hq : Sec5B517Quad K z) {i : Fin 4}
    (e : ↥(K i) ≃* SL23) : e ⟨z, hq.z_mem i⟩ = -1 := by
  have hsq : e ⟨z, hq.z_mem i⟩ * e ⟨z, hq.z_mem i⟩ = 1 := by
    rw [← map_mul]
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) * ⟨z, hq.z_mem i⟩ = 1 :=
      Subtype.ext (by simpa using hq.z_sq)
    rw [hsub, map_one]
  rcases sl23_unique_involution _ hsq with h1 | hneg
  · exfalso
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) = 1 := e.injective (by rw [h1, map_one])
    exact hq.z_ne (congrArg Subtype.val hsub)
  · exact hneg

private lemma s888_comm_mem_zpowers (hq : Sec5B517Quad K z) {i : Fin 4} {u v : H}
    (hu : u ∈ K i) (hu4 : u ^ 4 = 1) (hv : v ∈ K i) (hv4 : v ^ 4 = 1) :
    u * v * u⁻¹ * v⁻¹ ∈ zpowers z := by
  obtain ⟨e⟩ := hq.iso i
  have hzu : e ⟨z, hq.z_mem i⟩ = -1 := s888_iso_z_eq_neg_one hq e
  have hu4' : (e ⟨u, hu⟩) ^ 4 = 1 := by
    have hsub : (⟨u, hu⟩ : ↥(K i)) ^ 4 = 1 := Subtype.ext (by simpa using hu4)
    rw [← map_pow, hsub, map_one]
  have hv4' : (e ⟨v, hv⟩) ^ 4 = 1 := by
    have hsub : (⟨v, hv⟩ : ↥(K i)) ^ 4 = 1 := Subtype.ext (by simpa using hv4)
    rw [← map_pow, hsub, map_one]
  have hmap : e (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹) =
      e ⟨u, hu⟩ * e ⟨v, hv⟩ * (e ⟨u, hu⟩)⁻¹ * (e ⟨v, hv⟩)⁻¹ := by
    simp only [map_mul, map_inv]
  rcases (sl23_q8_comm_sq (e ⟨u, hu⟩) (e ⟨v, hv⟩) hu4' hv4').1 with hc | hc
  · have hsub : (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ : ↥(K i)) = 1 := by
      apply e.injective
      rw [hmap, hc]
      exact (map_one e).symm
    have hG : u * v * u⁻¹ * v⁻¹ = 1 := by simpa using congrArg Subtype.val hsub
    rw [hG]
    exact (zpowers z).one_mem
  · have hsub : (⟨u, hu⟩ * ⟨v, hv⟩ * ⟨u, hu⟩⁻¹ * ⟨v, hv⟩⁻¹ : ↥(K i)) = ⟨z, hq.z_mem i⟩ := by
      apply e.injective
      rw [hmap, hc]
      exact hzu.symm
    have hG : u * v * u⁻¹ * v⁻¹ = z := by simpa using congrArg Subtype.val hsub
    rw [hG]
    exact Subgroup.mem_zpowers z

private lemma s888_sq_mem_zpowers (hq : Sec5B517Quad K z) {i : Fin 4} {u : H}
    (hu : u ∈ K i) (h4 : u ^ 4 = 1) : u * u ∈ zpowers z := by
  rcases hq.sq_of_pow4 hu h4 with h | h
  · rw [h]
    exact (zpowers z).one_mem
  · rw [h]
    exact Subgroup.mem_zpowers z

private lemma s888_prod_commutator (hq : Sec5B517Quad K z) {k l : Fin 4 → H}
    (hk : ∀ i, k i ∈ K i) (hl : ∀ i, l i ∈ K i) :
    Sec5B517Prod k * Sec5B517Prod l * (Sec5B517Prod k)⁻¹ * (Sec5B517Prod l)⁻¹ =
      Sec5B517Prod (fun i => k i * l i * (k i)⁻¹ * (l i)⁻¹) := by
  simp only [sec5b517_prod_inv hq hk, sec5b517_prod_inv hq hl,
    sec5b517_prod_mul hq hk hl,
    sec5b517_prod_mul hq (fun i => (K i).mul_mem (hk i) (hl i))
      (fun i => (K i).inv_mem (hk i)),
    sec5b517_prod_mul hq
      (fun i => (K i).mul_mem ((K i).mul_mem (hk i) (hl i)) ((K i).inv_mem (hk i)))
      (fun i => (K i).inv_mem (hl i))]

theorem planeV_comm (hq : Sec5B517Quad K z) (α : H →* X) (hker : α.ker = zpowers z) :
    ∀ a ∈ planeV hq α, ∀ b ∈ planeV hq α, a * b = b * a := by
  intro a ha b hb
  rw [planeV, Subgroup.mem_map] at ha hb
  obtain ⟨q, hqmem, hqa⟩ := ha
  obtain ⟨r, hrmem, hrb⟩ := hb
  rw [← hqa, ← hrb]
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hqmem
  obtain ⟨l, hl, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hrmem
  have hki : ∀ i, k i ∈ K i := fun i => (hk i).1
  have hli : ∀ i, l i ∈ K i := fun i => (hl i).1
  have hker_mem : Sec5B517Prod k * Sec5B517Prod l * (Sec5B517Prod k)⁻¹ *
      (Sec5B517Prod l)⁻¹ ∈ α.ker := by
    rw [hker, s888_prod_commutator hq hki hli]
    simp only [Sec5B517Prod]
    exact (zpowers z).mul_mem ((zpowers z).mul_mem ((zpowers z).mul_mem
      (s888_comm_mem_zpowers hq (hki 0) (hk 0).2 (hli 0) (hl 0).2)
      (s888_comm_mem_zpowers hq (hki 1) (hk 1).2 (hli 1) (hl 1).2))
      (s888_comm_mem_zpowers hq (hki 2) (hk 2).2 (hli 2) (hl 2).2))
      (s888_comm_mem_zpowers hq (hki 3) (hk 3).2 (hli 3) (hl 3).2)
  rw [s888_comm_iff_commutator]
  have hα : α (Sec5B517Prod k * Sec5B517Prod l * (Sec5B517Prod k)⁻¹ *
      (Sec5B517Prod l)⁻¹) = 1 := (MonoidHom.mem_ker).mpr hker_mem
  simpa only [map_mul, map_inv] using hα

theorem planeV_sq (hq : Sec5B517Quad K z) (α : H →* X) (hker : α.ker = zpowers z) :
    ∀ a ∈ planeV hq α, a * a = 1 := by
  intro a ha
  rw [planeV, Subgroup.mem_map] at ha
  obtain ⟨q, hqmem, hqa⟩ := ha
  rw [← hqa]
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hqmem
  have hki : ∀ i, k i ∈ K i := fun i => (hk i).1
  have hker_mem : Sec5B517Prod k * Sec5B517Prod k ∈ α.ker := by
    rw [hker, sec5b517_prod_mul hq hki hki]
    simp only [Sec5B517Prod]
    exact (zpowers z).mul_mem ((zpowers z).mul_mem ((zpowers z).mul_mem
      (s888_sq_mem_zpowers hq (hki 0) (hk 0).2)
      (s888_sq_mem_zpowers hq (hki 1) (hk 1).2))
      (s888_sq_mem_zpowers hq (hki 2) (hk 2).2))
      (s888_sq_mem_zpowers hq (hki 3) (hk 3).2)
  have hα : α (Sec5B517Prod k * Sec5B517Prod k) = 1 := (MonoidHom.mem_ker).mpr hker_mem
  simpa only [map_mul] using hα

theorem planeV_decomp (hq : Sec5B517Quad K z) (α : H →* X) :
    ∀ v ∈ planeV hq α, ∃ w : Fin 4 → X, (∀ i, w i ∈ planeW hq α i) ∧
      v = w 0 * w 1 * w 2 * w 3 := by
  intro v hv
  rw [planeV, Subgroup.mem_map] at hv
  obtain ⟨q, hqmem, hqv⟩ := hv
  obtain ⟨k, hk, rfl⟩ := (Sec5B517Q8.mem_iff hq).mp hqmem
  refine ⟨fun i => α (k i), ?_, ?_⟩
  · intro i
    rw [planeW, Subgroup.mem_map]
    exact ⟨k i, ⟨Sec5B517Q8.mem_of_mem hq (hk i).1 (hk i).2, (hk i).1⟩, rfl⟩
  · rw [← hqv, Sec5B517Prod]
    simp only [map_mul]

end CFSG.OddStandard.SmallF3.Omega
