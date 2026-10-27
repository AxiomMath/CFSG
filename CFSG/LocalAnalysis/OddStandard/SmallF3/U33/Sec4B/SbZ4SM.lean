module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SE0
public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.Sec4B.SbZ4SB

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {x₁ x₂ lam rho tau : G}

namespace Z4Good

private theorem conj_inv_mul {b v : G} (hb : t * b * t⁻¹ = b)
    (hv : t * v * t⁻¹ = v * b ^ 2) (hcomm : Commute b v) (hb4 : b ^ 4 = 1)
    (hv2 : v * v = 1) : t * (b * v) * t⁻¹ = (b * v)⁻¹ := by
  have hb3 : b ^ 3 = b⁻¹ :=
    mul_eq_one_iff_eq_inv.mp (by rw [← pow_succ]; simpa using hb4)
  have hv_inv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hconj : t * (b * v) * t⁻¹ = b * (v * b ^ 2) := by
    rw [show t * (b * v) * t⁻¹ = (t * b * t⁻¹) * (t * v * t⁻¹) by group, hb, hv]
  rw [hconj, mul_inv_rev, hv_inv, ← hb3]
  rw [show b * (v * b ^ 2) = (b * v) * b ^ 2 by group, hcomm.eq,
    show (v * b) * b ^ 2 = v * b ^ 3 by group]

variable (hg : Z4Good t L S x₁ x₂ lam rho tau)
include hg

theorem mem_cent_ttau_iff (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹) {a : G}
    (ha : a ∈ ctxQ t tau x₁ x₂ rho) :
    a ∈ centralizer ({t * tau} : Set G) ↔ t * a * t⁻¹ = a⁻¹ := by
  have hconj : (t * tau) * a * (t * tau)⁻¹ = (t * a * t⁻¹)⁻¹ := by
    calc (t * tau) * a * (t * tau)⁻¹ = t * (tau * a * tau⁻¹) * t⁻¹ := by group
      _ = t * a⁻¹ * t⁻¹ := by rw [htau a ha]
      _ = (t * a * t⁻¹)⁻¹ := by group
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : (t * tau) * a * (t * tau)⁻¹ = a := by
      rw [← h]
      group
    rw [hconj] at h'
    have := congrArg Inv.inv h'
    simpa using this
  · intro h
    have h' : (t * tau) * a * (t * tau)⁻¹ = a := by
      rw [hconj, h]
      simp
    exact (mul_inv_eq_iff_eq_mul.mp h').symm

theorem C_Q_ttau (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹)
    {V' : Subgroup G} {v₁ v₂ : G} (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) :
    ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) = closure {x₁ * v₁, x₂ * v₂} := by
  have hED : closure ({x₁ * v₁, x₂ * v₂} : Set G) ≤
      ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
    rw [Subgroup.closure_le]
    intro g hgen
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hgen
    rcases hgen with rfl | rfl
    · have hQ : x₁ * v₁ ∈ ctxQ t tau x₁ x₂ rho :=
        mul_mem hg.x₁_mem_Q (hV.V'_le_Q hg.toZ4Pre hV.v₁_mem)
      refine ⟨hQ, (hg.mem_cent_ttau_iff htau hQ).mpr ?_⟩
      exact conj_inv_mul (hg.t_conj_B (subset_closure (by simp))) hV.t_v₁
        (hg.Q_comm x₁ hg.x₁_mem_Q v₁ (hV.V'_le_Q hg.toZ4Pre hV.v₁_mem))
        hg.x₁_pow_four (hV.sq_eq_one hV.v₁_mem)
    · have hQ : x₂ * v₂ ∈ ctxQ t tau x₁ x₂ rho :=
        mul_mem hg.x₂_mem_Q (hV.V'_le_Q hg.toZ4Pre hV.v₂_mem)
      refine ⟨hQ, (hg.mem_cent_ttau_iff htau hQ).mpr ?_⟩
      exact conj_inv_mul (hg.t_conj_B (subset_closure (by simp))) hV.t_v₂
        (hg.Q_comm x₂ hg.x₂_mem_Q v₂ (hV.V'_le_Q hg.toZ4Pre hV.v₂_mem))
        hg.x₂_pow_four (hV.sq_eq_one hV.v₂_mem)
  have claimA : ∀ b ∈ baseGrp x₁ x₂,
      ∃ v ∈ V', b * v ∈ closure ({x₁ * v₁, x₂ * v₂} : Set G) := by
    intro b hb
    rw [baseGrp] at hb
    induction hb using Subgroup.closure_induction with
    | mem g hgen =>
        rcases hgen with rfl | rfl
        · exact ⟨v₁, hV.v₁_mem, subset_closure (by simp)⟩
        · exact ⟨v₂, hV.v₂_mem, subset_closure (by simp)⟩
    | one => exact ⟨1, one_mem _, by simp⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨v, hv, hxv⟩ := ihx
        obtain ⟨v', hv', hyv'⟩ := ihy
        refine ⟨v * v', mul_mem hv hv', ?_⟩
        have hcomm : v * y = y * v :=
          hg.Q_comm v (hV.V'_le_Q hg.toZ4Pre hv) y (hg.base_le_Q hy)
        have hcalc : (x * v) * (y * v') = (x * y) * (v * v') := by
          calc (x * v) * (y * v') = x * (v * y) * v' := by group
            _ = x * (y * v) * v' := by rw [hcomm]
            _ = (x * y) * (v * v') := by group
        rw [← hcalc]
        exact mul_mem hxv hyv'
    | inv x hx ihx =>
        obtain ⟨v, hv, hxv⟩ := ihx
        refine ⟨v⁻¹, inv_mem hv, ?_⟩
        have hcx : Commute x v :=
          hg.Q_comm x (hg.base_le_Q hx) v (hV.V'_le_Q hg.toZ4Pre hv)
        have hxvinv : x⁻¹ * v⁻¹ = (x * v)⁻¹ := by
          rw [mul_inv_rev]
          exact hcx.inv_inv.eq
        rw [hxvinv]
        exact inv_mem hxv
  apply le_antisymm
  · intro a ha
    obtain ⟨haQ, haC⟩ := ha
    obtain ⟨b, hbB, v, hvV, rfl⟩ := hV.mem_Q_decomp hg.toZ4Pre haQ
    obtain ⟨v', hv'V, hbv'E⟩ := claimA b hbB
    have huV : v * v'⁻¹ ∈ V' := mul_mem hvV (inv_mem hv'V)
    have huQ : v * v'⁻¹ ∈ ctxQ t tau x₁ x₂ rho := hV.V'_le_Q hg.toZ4Pre huV
    have hbv_comm : Commute b v :=
      hg.Q_comm b (hg.base_le_Q hbB) v (hV.V'_le_Q hg.toZ4Pre hvV)
    have hbv'_comm : Commute b v' :=
      hg.Q_comm b (hg.base_le_Q hbB) v' (hV.V'_le_Q hg.toZ4Pre hv'V)
    have hident : b * v * (b * v')⁻¹ = v * v'⁻¹ := by
      rw [mul_inv_rev, hbv_comm.eq, ← hbv'_comm.inv_inv.eq]
      group
    have huD : v * v'⁻¹ ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) := by
      have hbv'D : b * v' ∈ ctxQ t tau x₁ x₂ rho ⊓ centralizer ({t * tau} : Set G) :=
        hED hbv'E
      rw [← hident]
      exact mul_mem ⟨haQ, haC⟩ (inv_mem hbv'D)
    have hu_inv : t * (v * v'⁻¹) * t⁻¹ = (v * v'⁻¹)⁻¹ :=
      (hg.mem_cent_ttau_iff htau huQ).mp huD.2
    have hz : z4Comm t (v * v'⁻¹) = 1 := by
      unfold z4Comm
      rw [hu_inv, ← mul_inv_rev, hV.sq_eq_one huV, inv_one]
    have hu1 : v * v'⁻¹ = 1 := hV.eq_one_of_comm hg.toZ4Pre huV hz
    have hveq : v = v' := by
      calc v = v * v'⁻¹ * v' := by group
        _ = 1 * v' := by rw [hu1]
        _ = v' := by rw [one_mul]
    rw [hveq]
    exact hbv'E
  · exact hED

theorem ctx4ZV (htau : ∀ a ∈ ctxQ t tau x₁ x₂ rho, tau * a * tau⁻¹ = a⁻¹)
    {V' : Subgroup G} {v₁ v₂ : G} (hV : Z4VBase t tau x₁ x₂ lam rho V' v₁ v₂) :
    Ctx4ZV t tau x₁ x₂ lam rho V' v₁ v₂ :=
  hV.toCtx4ZV (hg.C_Q_ttau htau hV)

end Z4Good

end CFSG.OddStandard.SmallF3.HarrisU33
