module

public import CFSG.LocalAnalysis.OddStandard.ONanIdK

public section

namespace CFSG.OddStandard.ONanRec

open Subgroup F2 F2.AlpE Model CFSG.ABGLocalTools CFSG.ComponentClassification.GHarris

theorem y0E_ne_xE : y0E ≠ xE ∧ y0E ≠ xE⁻¹ := by decide

theorem xE_inv_y0E : InWE (xE⁻¹ * y0E) := by decide

theorem xE_four : xE ^ 4 = 1 ∧ xE * xE ≠ 1 := by decide

theorem y0E_four : y0E ^ 4 = 1 ∧ y0E * y0E ≠ 1 := by decide

namespace FusCtx

variable {G : Type} [Group G] [Finite G] {v1 v2 v3 s t : G} (D : FusCtx G v1 v2 v3 s t)

include D

theorem isSylowOf_P_centralizer_z : IsSylowOf 2 (alpP v1 v2 v3 s t)
    (centralizer ({invRep v1 v2 v3 s t 0} : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine D.isSylowOf_P.of_le (fun p hp => ?_) le_top
  rw [mem_centralizer_singleton_iff]
  exact (AlpEmb.centre_alpP D.E D.hF D.z_mem_P).2 (Or.inr rfl) p hp

theorem conj_phi_four {e : AlpE} (he : e ^ 4 = 1 ∧ e * e ≠ 1) (h : G) :
    (h * D.E.φ e * h⁻¹) ^ 4 = 1 ∧ h * D.E.φ e * h⁻¹ * (h * D.E.φ e * h⁻¹) ≠ 1 := by
  refine ⟨by rw [conj_pow, ← map_pow, he.1, map_one, mul_one, mul_inv_cancel], fun h1 => he.2 ?_⟩
  have e1 : h * D.E.φ e * h⁻¹ * (h * D.E.φ e * h⁻¹) = h * D.E.φ (e * e) * h⁻¹ := by
    rw [map_mul]
    group
  rw [e1, conj_eq_one_iff] at h1
  exact (map_eq_one_iff D.E.φ D.E.inj).1 h1

theorem exists_conj_y0_out (hone : OneClass G) :
    ∃ g : G, g * (v1 * v3) * g⁻¹ ∈ alpP v1 v2 v3 s t ∧
      g * (v1 * v3) * g⁻¹ ∉ alpV v1 v2 v3 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hjy : invRep v1 v2 v3 s t 3 * (v1 * v3) = v1 * v3 * invRep v1 v2 v3 s t 3 := by
    rw [D.j_eq, D.y0_eq, ← map_mul, ← map_mul, y0E_comm_jE]
  obtain ⟨g0, hg0⟩ := isConj_iff.1 (hone _ _ (D.orderOf_rep 3) (D.orderOf_rep 0))
  have hRC : closure ({invRep v1 v2 v3 s t 3, v1 * v3} : Set G) ≤
      centralizer ({invRep v1 v2 v3 s t 3} : Set G) := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact mem_centralizer_singleton_iff.2 rfl
    · exact mem_centralizer_singleton_iff.2 hjy.symm
  have hRP : closure ({invRep v1 v2 v3 s t 3, v1 * v3} : Set G) ≤ alpP v1 v2 v3 s t := by
    rw [closure_le]
    rintro _ (rfl | rfl)
    · exact AlpEmb.invRep_mem D.E 3
    · exact D.y0_mem_P
  have hRp := (D.isPGroup_P.to_le hRP).map (MulAut.conj g0).toMonoidHom
  have hR'z : (closure ({invRep v1 v2 v3 s t 3, v1 * v3} : Set G)).map
      (MulAut.conj g0).toMonoidHom ≤ centralizer ({invRep v1 v2 v3 s t 0} : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hg0]
    have h := mem_centralizer_singleton_iff.1 (hRC ha)
    calc g0 * a * g0⁻¹ * (g0 * invRep v1 v2 v3 s t 3 * g0⁻¹)
        = g0 * (a * invRep v1 v2 v3 s t 3) * g0⁻¹ := by group
      _ = g0 * (invRep v1 v2 v3 s t 3 * a) * g0⁻¹ := by rw [h]
      _ = g0 * invRep v1 v2 v3 s t 3 * g0⁻¹ * (g0 * a * g0⁻¹) := by group
  obtain ⟨c, hc, hcR⟩ := exists_conj_le_of_isSylowOf D.isSylowOf_P_centralizer_z hR'z hRp
  have hcz : c * invRep v1 v2 v3 s t 0 * c⁻¹ = invRep v1 v2 v3 s t 0 := by
    rw [mem_centralizer_singleton_iff.1 hc, mul_inv_cancel_right]
  have hgj : c * g0 * invRep v1 v2 v3 s t 3 * (c * g0)⁻¹ = invRep v1 v2 v3 s t 0 := by
    rw [← hcz, ← hg0]
    group
  have hgy : c * g0 * (v1 * v3) * (c * g0)⁻¹ ∈ alpP v1 v2 v3 s t := by
    have := hcR (g0 * (v1 * v3) * g0⁻¹) ⟨v1 * v3, subset_closure (by simp), rfl⟩
    rwa [show c * (g0 * (v1 * v3) * g0⁻¹) * c⁻¹ = c * g0 * (v1 * v3) * (c * g0)⁻¹ by group]
      at this
  refine ⟨c * g0, hgy, fun hV => ?_⟩
  obtain ⟨n, hn, hny⟩ := D.fuse_V (D.V_le_centralizer_V hV) (D.V_le_centralizer_V D.y0_mem_V)
    ⟨(c * g0)⁻¹, by group⟩
  have hkY : n⁻¹ * (c * g0) ∈ centralizer ({v1 * v3} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    calc n⁻¹ * (c * g0) * (v1 * v3)
        = n⁻¹ * (c * g0 * (v1 * v3) * (c * g0)⁻¹) * n * (n⁻¹ * (c * g0)) := by group
      _ = v1 * v3 * (n⁻¹ * (c * g0)) := by rw [hny]
  apply D.not_conj_j_mem_V (inv_mem hkY)
  rw [inv_inv, show n⁻¹ * (c * g0) * invRep v1 v2 v3 s t 3 * (n⁻¹ * (c * g0))⁻¹ =
    n⁻¹ * (c * g0 * invRep v1 v2 v3 s t 3 * (c * g0)⁻¹) * n by group, hgj]
  exact conj_inv_mem_V hn D.z_mem_V'

theorem conj_x_mem_V (hone : OneClass G) {h : G}
    (hP : h * xel v1 v2 v3 * h⁻¹ ∈ alpP v1 v2 v3 s t) :
    h * xel v1 v2 v3 * h⁻¹ ∈ alpV v1 v2 v3 := by
  by_contra hV
  obtain ⟨g, hgP, hgV⟩ := D.exists_conj_y0_out hone
  have hx := D.conj_phi_four xE_four h
  rw [← D.x_eq] at hx
  have hy := D.conj_phi_four y0E_four g
  rw [← D.y0_eq] at hy
  obtain ⟨g', hg'⟩ := D.isConj_order_four hP hV hx.1 hx.2 hgP hgV hy.1 hy.2
  obtain ⟨m, hmx⟩ : ∃ m : G, m * xel v1 v2 v3 * m⁻¹ = v1 * v3 := by
    refine ⟨g⁻¹ * g' * h, ?_⟩
    calc g⁻¹ * g' * h * xel v1 v2 v3 * (g⁻¹ * g' * h)⁻¹
        = g⁻¹ * (g' * (h * xel v1 v2 v3 * h⁻¹) * g'⁻¹) * g := by group
      _ = g⁻¹ * (g * (v1 * v3) * g⁻¹) * g := by rw [hg']
      _ = v1 * v3 := by group
  have hW : (xel v1 v2 v3)⁻¹ * (m * xel v1 v2 v3 * m⁻¹) ∈ alpW v1 v2 v3 := by
    rw [hmx, D.x_eq, D.y0_eq, ← map_inv, ← map_mul, D.mem_W_phi]
    exact xE_inv_y0E
  rcases D.conj_x_of_mem hW with h1 | h1
  · rw [hmx, D.x_eq, D.y0_eq] at h1
    exact y0E_ne_xE.1 (D.E.inj h1)
  · rw [hmx, D.x_eq, D.y0_eq, ← map_inv] at h1
    exact y0E_ne_xE.2 (D.E.inj h1)

end FusCtx

end CFSG.OddStandard.ONanRec
