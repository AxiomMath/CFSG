module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5S888PH4
public import CFSG.Assembly.Subnormal

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {H X : Type} [Group H] [Group X] {z : H} {K : Fin 4 → Subgroup H} {α : H →* X}

private lemma s888_K_le_all (i : Fin 4) : K i ≤ Sec5B517All K := by
  fin_cases i
  · exact le_sup_left.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans (le_sup_left.trans le_sup_left)
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

private lemma s888_K_le_normalizer (hq : Sec5B517Quad K z) (j : Fin 4) :
    K j ≤ normalizer (Sec5B517Q8 hq : Set H) := by
  intro y hy
  rw [Subgroup.mem_set_normalizer_iff]
  intro u
  constructor
  · intro hu
    exact Sec5B517Q8.conj_mem hq (s888_K_le_all j hy) hu
  · intro hu
    have h := Sec5B517Q8.conj_mem hq (s888_K_le_all j ((K j).inv_mem hy)) hu
    rwa [show y⁻¹ * (y * u * y⁻¹) * (y⁻¹)⁻¹ = u by group] at h

private lemma s888_all_le_normalizer (hq : Sec5B517Quad K z) :
    Sec5B517All K ≤ normalizer (Sec5B517Q8 hq : Set H) :=
  sup_le (sup_le (sup_le (s888_K_le_normalizer hq 0) (s888_K_le_normalizer hq 1))
    (s888_K_le_normalizer hq 2)) (s888_K_le_normalizer hq 3)

private lemma s888_K_normalizes_K (hq : Sec5B517Quad K z) {i j : Fin 4} (hji : j ≠ i) :
    K j ≤ normalizer (K i : Set H) := by
  rw [Subgroup.le_normalizer_iff]
  intro y hy u hu
  have hcomm : y * u = u * y := hq.comm j i hji y hy u hu
  rwa [show y * u * y⁻¹ = u by rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]]

private lemma s888_all_le_normalizer_K (hq : Sec5B517Quad K z) (i : Fin 4) :
    Sec5B517All K ≤ normalizer (K i : Set H) := by
  have h : ∀ j, K j ≤ normalizer (K i : Set H) := by
    intro j
    by_cases hji : j = i
    · subst hji; exact Subgroup.le_normalizer
    · exact s888_K_normalizes_K hq hji
  exact sup_le (sup_le (sup_le (h 0) (h 1)) (h 2)) (h 3)

private lemma s888_Q8_proof_irrel {hq hq' : Sec5B517Quad K z} :
    Sec5B517Q8 hq = Sec5B517Q8 hq' :=
  Subgroup.ext fun _ => Iff.rfl

private lemma s888_map_conj_le_all [Finite H] {T : Subgroup H} (hP : PocketHyp z K T)
    {x : H} (hxN : x ∈ normalizer (Sec5B517Q8 hP.quad : Set H)) (j : Fin 4) :
    (K j).map (MulAut.conj x).toMonoidHom ≤ Sec5B517All K := by
  obtain ⟨j', hj'⟩ := hP.perm x⁻¹ (inv_mem hxN) j
  have hEq : (K j).map (MulAut.conj x).toMonoidHom = CFSG.conjugate (K j) x⁻¹ := by
    simp [CFSG.conjugate]
  rw [hEq, hj']
  exact s888_K_le_all j'

private lemma s888_conj_mem_all [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) {x : H} (hxN : x ∈ normalizer (Sec5B517Q8 hS.quad : Set H))
    {y : H} (hy : y ∈ Sec5B517All K) : x * y * x⁻¹ ∈ Sec5B517All K := by
  have hxN' : x ∈ normalizer (Sec5B517Q8 hP.quad : Set H) := by
    rwa [s888_Q8_proof_irrel (hq := hP.quad) (hq' := hS.quad)] at hxN
  have hle : Sec5B517All K ≤ (Sec5B517All K).comap (MulAut.conj x).toMonoidHom := by
    apply sup_le
    · apply sup_le
      · apply sup_le
        · exact (Subgroup.map_le_iff_le_comap).mp (s888_map_conj_le_all hP hxN' 0)
        · exact (Subgroup.map_le_iff_le_comap).mp (s888_map_conj_le_all hP hxN' 1)
      · exact (Subgroup.map_le_iff_le_comap).mp (s888_map_conj_le_all hP hxN' 2)
    · exact (Subgroup.map_le_iff_le_comap).mp (s888_map_conj_le_all hP hxN' 3)
  simpa [MulAut.conj_apply] using hle hy

theorem map_K_le_normalizer (hS : PlaneSetup z K α) (i : Fin 4) :
    (K i).map α ≤ normalizer (planeV hS.quad α : Set X) := by
  rintro y ⟨u, hu, rfl⟩
  exact (mem_normalizer_planeV_iff hS).2 (s888_K_le_normalizer hS.quad i hu)

theorem map_K_subnormal [Finite H] {T : Subgroup H} (hS : PlaneSetup z K α)
    (hP : PocketHyp z K T) (i : Fin 4) :
    (((K i).map α).subgroupOf (normalizer (planeV hS.quad α : Set X))).IsSubnormal := by
  let N : Subgroup H := normalizer (Sec5B517Q8 hS.quad : Set H)
  let All : Subgroup H := Sec5B517All K
  have hKleAll : K i ≤ All := s888_K_le_all i
  have hAllLeN : All ≤ N := s888_all_le_normalizer hS.quad
  have hnormK : ((K i).subgroupOf All).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKleAll).mpr
      (s888_all_le_normalizer_K hS.quad i)
  have hnormAll : (All.subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAllLeN).mpr
      (Subgroup.le_normalizer_iff.mpr (fun x hx y hy => s888_conj_mem_all hS hP hx hy))
  have hsubn_H : CFSG.Open.IsSubnormal (K i) N :=
    CFSG.Open.IsSubnormal.step hKleAll hnormK
      (CFSG.Open.IsSubnormal.step hAllLeN hnormAll (CFSG.Open.IsSubnormal.refl N))
  have hNmap : N.map α = normalizer (planeV hS.quad α : Set X) := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_planeV_iff hS).2 hx
    · intro g hg
      obtain ⟨x, rfl⟩ := hS.surj g
      exact ⟨x, (mem_normalizer_planeV_iff hS).1 hg, rfl⟩
  have hsubn_X : CFSG.Open.IsSubnormal ((K i).map α)
      (normalizer (planeV hS.quad α : Set X)) := by
    have h := CFSG.Open.IsSubnormal.map α hsubn_H
    rwa [hNmap] at h
  exact (CFSG.Open.IsSubnormal.iff_subgroupOf (map_K_le_normalizer hS i)).1 hsubn_X

private lemma s888_sl23_comm_pair :
    ∃ a b : SL23, a ^ 4 = 1 ∧ b ^ 4 = 1 ∧ a * b * a⁻¹ * b⁻¹ = -1 := by
  decide +kernel

private lemma s888_pow4_of_map {i : Fin 4} (e : ↥(K i) ≃* SL23) {u : H} (hu : u ∈ K i)
    {u' : SL23} (h : e ⟨u, hu⟩ = u') (h4 : u' ^ 4 = 1) : u ^ 4 = 1 := by
  have hsub : (⟨u, hu⟩ : ↥(K i)) ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, h, h4, map_one]
  simpa using congrArg (fun x : ↥(K i) => (x : H)) hsub

theorem exists_comm_pair (hq : Sec5B517Quad K z) (i : Fin 4) :
    ∃ a ∈ Sec5B517Q8 hq ⊓ K i, ∃ b ∈ Sec5B517Q8 hq ⊓ K i, a * b * a⁻¹ * b⁻¹ = z := by
  obtain ⟨e⟩ := hq.iso i
  obtain ⟨a', b', ha'4, hb'4, hcomm'⟩ := s888_sl23_comm_pair
  let A : ↥(K i) := e.symm a'
  let B : ↥(K i) := e.symm b'
  have heA : e A = a' := e.apply_symm_apply a'
  have heB : e B = b' := e.apply_symm_apply b'
  have hA4 : A ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, heA, ha'4, map_one]
  have hB4 : B ^ 4 = 1 := by
    apply e.injective
    rw [map_pow, heB, hb'4, map_one]
  have hzsq : e ⟨z, hq.z_mem i⟩ * e ⟨z, hq.z_mem i⟩ = 1 := by
    rw [← map_mul, ← map_one e]
    congr 1
    apply Subtype.ext
    simpa using hq.z_sq
  have hzne : e ⟨z, hq.z_mem i⟩ ≠ 1 := by
    intro h
    have hsub : (⟨z, hq.z_mem i⟩ : ↥(K i)) = 1 := e.injective (by rw [h, map_one])
    exact hq.z_ne (by simpa using congrArg (fun x : ↥(K i) => (x : H)) hsub)
  have hzeta : e ⟨z, hq.z_mem i⟩ = -1 :=
    (sl23_unique_involution _ hzsq).resolve_left hzne
  have hAmem : (A : H) ∈ Sec5B517Q8 hq ⊓ K i :=
    (mem_inf_K_iff hq i).mpr
      ⟨A.2, s888_pow4_of_map e A.2 heA ha'4⟩
  have hBmem : (B : H) ∈ Sec5B517Q8 hq ⊓ K i :=
    (mem_inf_K_iff hq i).mpr
      ⟨B.2, s888_pow4_of_map e B.2 heB hb'4⟩
  have hcz : (⟨z, hq.z_mem i⟩ : ↥(K i)) = A * B * A⁻¹ * B⁻¹ := by
    apply e.injective
    rw [hzeta]
    show -1 = e (A * B * A⁻¹ * B⁻¹)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, heA, heB]
    exact hcomm'.symm
  refine ⟨(A : H), hAmem, (B : H), hBmem, ?_⟩
  have hval := congrArg (fun x : ↥(K i) => (x : H)) hcz
  simpa using hval.symm

end CFSG.OddStandard.SmallF3.Omega
