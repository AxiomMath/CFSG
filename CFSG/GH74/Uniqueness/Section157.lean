module

public import CFSG.GH74.Uniqueness.Section157Big
public import CFSG.GH74.Uniqueness.Section15Last

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

variable {X : Type} [Group X] [Finite X]

namespace Conf156

variable {M : Subgroup X} {n : ℕ} {L D K J Mo V R₁ : Subgroup X} {u : X}

theorem false_of_eq (C : Conf156 M n L D K J Mo V R₁ u) {R₀ : Subgroup X}
    (hR : R0Data M K Mo R₁ R₀ n u) (hRV : R₁ = V) (hH : Hering32Stmt) : False := by
  have F := C.F
  have hKcomm : ∀ a ∈ K, ∀ b ∈ K, a * b = b * a := by
    obtain ⟨g, hg⟩ := F.K_cyclic.exists_generator
    intro a ha b hb
    obtain ⟨i, hi⟩ := mem_zpowers_iff.mp (hg ⟨a, ha⟩)
    obtain ⟨j, hj⟩ := mem_zpowers_iff.mp (hg ⟨b, hb⟩)
    have h1 : (⟨a, ha⟩ : ↥K) * ⟨b, hb⟩ = ⟨b, hb⟩ * ⟨a, ha⟩ := by
      rw [← hi, ← hj]
      exact (Commute.zpow_zpow_self g i j).eq
    exact congrArg Subtype.val h1
  have hxR₁ : ∀ x, x ∈ V → x ∈ R₁ := fun x hx => by rw [hRV]; exact hx
  obtain ⟨hn3, x, hxM, hxV, hxR₀⟩ := heringFinal M V R₀ Mo D K u n F.two_le hR.Mo_le
    (hR.le_R₁.trans C.R₁_le) F.V_le F.D_le F.K_le_D F.V_normal hR.normal F.Mo_normal
    (fun d hd k hk => F.D_conj_K hd hk) F.card_Mo hR.card_R₀ (by rw [← hRV]; exact C.card_R₁)
    F.card_K F.card_M F.Mo_sq hR.abelian (fun x hx => C.sq_R₁ x (hR.le_R₁ hx)) hR.sq_ne
    (C.R₁_le C.u_mem_R₁) hR.u_not_mem C.u_sq hR.inv
    (fun x hx hxR₀ => C.inv_R₁ x (hxR₁ x hx) (fun h => hxR₀ (hR.Mo_le h))
      (hR.invol x (hxR₁ x hx) hxR₀))
    hKcomm F.K_trans F.K_fpf (fun d hd => mul_inv_eq_iff_eq_mul.mp (C.D_comm_u hd)) C.VD C.C0_le
    F.V_max F.oddGen hH
  have hx₁ : x * x ∈ R₁ := hxR₁ _ hxV
  obtain ⟨g, hg, hgu⟩ := C.inv_R₁ (x * x) hx₁ (fun h => hxR₀ (hR.Mo_le h))
    (hR.invol _ hx₁ hxR₀)
  have hww : g⁻¹ * x * g * (g⁻¹ * x * g) = u := by
    calc g⁻¹ * x * g * (g⁻¹ * x * g) = g⁻¹ * (x * x) * g := by group
      _ = u := by rw [← hgu]; group
  have hc : (g⁻¹ * x * g) * u = u * (g⁻¹ * x * g) := by
    rw [← hww]
    group
  have hwN : g⁻¹ * x * g ∈ normalizer (L : Set X) := C.cent_le_N hc
  have hwLJ : g⁻¹ * x * g ∈ L ⊔ J :=
    F.out_three hn3 _ hwN (by rw [hww]; exact mem_sup_right C.u_mem_J)
  have hJN : J ≤ normalizer (L : Set X) := F.J_le_D.trans F.D_le_N
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right J L hJN] at hwLJ
  obtain ⟨j, hj, l, hl, hjl⟩ := hwLJ
  have hjl0 : j * l = g⁻¹ * x * g := hjl
  have hjj : j * j = 1 := by
    rcases C.J_eq j hj with rfl | rfl
    · exact one_mul 1
    · exact C.u_sq
  have hul : u = l * l := by
    have hjl' : j * l = l * j := F.J_comm hj hl
    calc u = (g⁻¹ * x * g) * (g⁻¹ * x * g) := hww.symm
      _ = (j * l) * (j * l) := by rw [hjl0]
      _ = (j * j) * (l * l) := by
        calc (j * l) * (j * l) = j * (l * j) * l := by group
          _ = j * (j * l) * l := by rw [hjl']
          _ = (j * j) * (l * l) := by group
      _ = l * l := by rw [hjj, one_mul]
  exact C.u_ne (F.eq_one_of_mem_L_J (hul ▸ L.mul_mem hl hl) C.u_mem_J)

end Conf156

theorem Conf156.false {M : Subgroup X} {n : ℕ} {L D K J Mo V R₁ : Subgroup X} {u : X}
    (C : Conf156 M n L D K J Mo V R₁ u) (hH : Hering32Stmt) : False := by
  obtain ⟨R₀, hR⟩ := C.exists_R0Data
  by_cases hRV : R₁ = V
  · exact C.false_of_eq hR hRV hH
  · exact C.false_of_ne hR hRV

end CFSG.GH74.Uniqueness
