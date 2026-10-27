module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3A6eVec

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e

open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3.AE.Wr
open Finset
open scoped commutatorElement

structure E8Pkg {Y : Type} [Group Y] (I D : Subgroup Y) where
  φ : ↥I →* AEQ 8
  inj : Function.Injective φ
  range_eq : φ.range = aeBar8
  le : D ≤ I
  mem_D : ∀ x : ↥I, (x : Y) ∈ D ↔ permQ 8 (φ x) = 1

namespace E8Pkg

variable {Y : Type} [Group Y] {I D : Subgroup Y} (P : E8Pkg I D)

open Classical in
@[expose] noncomputable def ph (x : Y) : AEQ 8 := if h : x ∈ I then P.φ ⟨x, h⟩ else 1

theorem ph_of_mem {x : Y} (h : x ∈ I) : P.ph x = P.φ ⟨x, h⟩ := dif_pos h

theorem ph_mul {x y : Y} (hx : x ∈ I) (hy : y ∈ I) : P.ph (x * y) = P.ph x * P.ph y := by
  rw [P.ph_of_mem (I.mul_mem hx hy), P.ph_of_mem hx, P.ph_of_mem hy, ← map_mul]
  rfl

theorem ph_one : P.ph 1 = 1 := by
  rw [P.ph_of_mem I.one_mem]
  exact map_one P.φ

theorem ph_inv {x : Y} (hx : x ∈ I) : P.ph x⁻¹ = (P.ph x)⁻¹ := by
  rw [P.ph_of_mem (I.inv_mem hx), P.ph_of_mem hx, ← map_inv]
  rfl

theorem ph_inj {x y : Y} (hx : x ∈ I) (hy : y ∈ I) (h : P.ph x = P.ph y) : x = y := by
  rw [P.ph_of_mem hx, P.ph_of_mem hy] at h
  exact congrArg Subtype.val (P.inj h)

theorem ph_mem {x : Y} (hx : x ∈ I) : P.ph x ∈ aeBar8 := by
  rw [P.ph_of_mem hx, ← P.range_eq]
  exact ⟨_, rfl⟩

@[expose] noncomputable def rho (x : Y) : Equiv.Perm (Fin 8) := permQ 8 (P.ph x)

theorem rho_mul {x y : Y} (hx : x ∈ I) (hy : y ∈ I) : P.rho (x * y) = P.rho x * P.rho y := by
  unfold rho
  rw [P.ph_mul hx hy, map_mul]

theorem rho_one : P.rho 1 = 1 := by
  unfold rho
  rw [P.ph_one, map_one]

theorem rho_inv {x : Y} (hx : x ∈ I) : P.rho x⁻¹ = (P.rho x)⁻¹ := by
  unfold rho
  rw [P.ph_inv hx, map_inv]

theorem sign_rho {x : Y} (hx : x ∈ I) : Equiv.Perm.sign (P.rho x) = 1 := by
  have h := P.ph_mem hx
  obtain ⟨a, ha, he⟩ := h
  unfold rho
  rw [← he, permQ_mkQ]
  exact ha.2

theorem mem_D_iff {x : Y} (hx : x ∈ I) : x ∈ D ↔ P.rho x = 1 := by
  have := P.mem_D ⟨x, hx⟩
  unfold rho
  rw [P.ph_of_mem hx]
  exact this

theorem rho_eq_one_of_mem_D {d : Y} (hd : d ∈ D) : P.rho d = 1 :=
  (P.mem_D_iff (P.le hd)).1 hd

include P in
theorem conj_mem_D {i d : Y} (hi : i ∈ I) (hd : d ∈ D) : i * d * i⁻¹ ∈ D := by
  have hdI := P.le hd
  have hc : i * d * i⁻¹ ∈ I := I.mul_mem (I.mul_mem hi hdI) (I.inv_mem hi)
  rw [P.mem_D_iff hc, P.rho_mul (I.mul_mem hi hdI) (I.inv_mem hi), P.rho_mul hi hdI, P.rho_inv hi,
    P.rho_eq_one_of_mem_D hd]
  group

theorem exists_lift {σ : Equiv.Perm (Fin 8)} (hσ : Equiv.Perm.sign σ = 1) :
    ∃ i ∈ I, P.rho i = σ := by
  have hm : mkQ 8 (ofPerm σ) ∈ P.φ.range := by
    rw [P.range_eq]
    refine ⟨ofPerm σ, ⟨?_, ?_⟩, rfl⟩
    · show wsum (ofPerm σ) = 0
      unfold wsum ofPerm
      simp
    · exact hσ
  obtain ⟨i, hi⟩ := hm
  refine ⟨i, i.2, ?_⟩
  unfold rho
  rw [P.ph_of_mem i.2]
  simp only [hi]
  rfl

theorem exists_vec {S : Finset (Fin 8)} (hS : Even S.card) : ∃ d ∈ D, P.ph d = vq S := by
  have hm : vq S ∈ P.φ.range := by
    rw [P.range_eq]
    exact vq_mem_aeBar8 hS
  obtain ⟨d, hd⟩ := hm
  refine ⟨d, ?_, ?_⟩
  · rw [P.mem_D d, hd, permQ_vq]
  · rw [P.ph_of_mem d.2]
    exact hd

theorem vec_of_mem_D {d : Y} (hd : d ∈ D) : ∃ S : Finset (Fin 8), Even S.card ∧ P.ph d = vq S := by
  have hdI := P.le hd
  exact exists_vq_of_ker (P.ph_mem hdI) (P.rho_eq_one_of_mem_D hd)

theorem ph_conj {i d : Y} (hi : i ∈ I) (hd : d ∈ I) :
    P.ph (i * d * i⁻¹) = P.ph i * P.ph d * (P.ph i)⁻¹ := by
  rw [P.ph_mul (I.mul_mem hi hd) (I.inv_mem hi), P.ph_mul hi hd, P.ph_inv hi]

theorem conj_vec {i d : Y} (hi : i ∈ I) (hd : d ∈ I) {S : Finset (Fin 8)} (h : P.ph d = vq S) :
    P.ph (i * d * i⁻¹) = vq (S.map (P.rho i).toEmbedding) := by
  rw [P.ph_conj hi hd, h, conj_vq]
  rfl

end E8Pkg

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6e
