module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec4FDelta

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z : G} {A B : Subgroup G}
  {φ : (Fin 7 → ZMod 2) → G}

theorem Sec4FSetup.mem_B_sup_cent (h : Sec4FSetup t L S z A B φ) {c : G}
    (hcN : c ∈ normalizer (L : Set G)) (hcB : ∀ b ∈ B, c * b = b * c) :
    c ∈ B ⊔ centralizer (L : Set G) := by
  have hLt : L ≤ centralizer ({t} : Set G) := h.ctx.component.le
  have hP : IsSylow2Of (S ⊓ L) L :=
    sec4_isSylow2Of_inf hLt (fun c hc => h.cent_le_normalizer hc) h.ctx.sylow
  exact h.inputs.hcB G L h.omega7 (S ⊓ L) B hP h.data.bdata.isMax h.data.bdata.card c hcN hcB

theorem Sec4FSetup.no_sqrt_t (h : Sec4FSetup t L S z A B φ) {c : G}
    (hc : c ∈ centralizer (L : Set G)) (hsq : c * c = t) : False := by
  have hct : c * t = t * c := by
    calc c * t = c * (c * c) := by rw [← hsq]
      _ = (c * c) * c := by group
      _ = t * c := by rw [hsq]
  have hcA : ∀ a ∈ A, c * a = a * c := by
    intro a ha
    obtain ⟨b, hb, hba⟩ := h.mem_A_cases ha
    have hcb : c * b = b * c :=
      (Subgroup.mem_centralizer_iff.mp hc b (h.B_le_L hb)).symm
    rcases hba with rfl | rfl
    · exact hcb
    · calc c * (b * t) = (c * b) * t := by group
        _ = (b * c) * t := by rw [hcb]
        _ = b * (c * t) := by group
        _ = b * (t * c) := by rw [hct]
        _ = (b * t) * c := by group
  obtain ⟨n, hnN, hnpt⟩ := h.exists_conj_pt (some 0)
  set c₁ : G := n * c * n⁻¹ with hc₁
  have hc₁sq : c₁ * c₁ = sec4MPt t φ (some 0) := by
    rw [hnpt]
    calc c₁ * c₁ = n * (c * c) * n⁻¹ := by rw [hc₁]; group
      _ = n * t * n⁻¹ := by rw [hsq]
  have hc₁A : ∀ a ∈ A, c₁ * a = a * c₁ := by
    intro a ha
    have ha' : n⁻¹ * a * n ∈ A := by
      simpa using (Subgroup.mem_set_normalizer_iff.mp
        ((normalizer (A : Set G)).inv_mem hnN) a).mp ha
    calc c₁ * a = n * c * (n⁻¹ * a) := by rw [hc₁]; group
      _ = n * c * ((n⁻¹ * a * n) * n⁻¹) := by group
      _ = n * (c * (n⁻¹ * a * n)) * n⁻¹ := by group
      _ = n * ((n⁻¹ * a * n) * c) * n⁻¹ := by rw [hcA (n⁻¹ * a * n) ha']
      _ = (n * (n⁻¹ * a * n) * n⁻¹) * (n * c * n⁻¹) := by group
      _ = a * c₁ := by rw [hc₁]; group
  have hc₁cent : c₁ ∈ centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact hc₁A t h.t_mem_A
  have hc₁N : c₁ ∈ normalizer (L : Set G) := h.cent_le_normalizer hc₁cent
  have hc₁B : ∀ b ∈ B, c₁ * b = b * c₁ := fun b hb => hc₁A b (h.B_le_A hb)
  have hc₁sup : c₁ ∈ B ⊔ centralizer (L : Set G) := h.mem_B_sup_cent hc₁N hc₁B
  have hcomm : ∀ x ∈ B, ∀ y ∈ centralizer (L : Set G), x * y = y * x :=
    fun x hx y hy => Subgroup.mem_centralizer_iff.mp hy x (h.B_le_L hx)
  obtain ⟨b, hb, d, hd, hc₁bd⟩ := sec4F_mem_sup_comm hcomm hc₁sup
  have hbd : b * d = d * b :=
    Subgroup.mem_centralizer_iff.mp hd b (h.B_le_L hb)
  have hbd_sq : (b * d) * (b * d) = d * d := by
    calc (b * d) * (b * d) = b * (d * (b * d)) := by group
      _ = b * ((d * b) * d) := by group
      _ = b * ((b * d) * d) := by rw [hbd.symm]
      _ = b * b * (d * d) := by group
      _ = d * d := by rw [h.A_sq (h.B_le_A hb), one_mul]
  have hd_sq : d * d = sec4MPt t φ (some 0) := by
    rw [← hc₁sq, hc₁bd]
    exact hbd_sq.symm
  set x : G := φ (sec4MW 0) with hx
  have hpt_eq : sec4MPt t φ (some 0) = t * x := by
    rw [hx]
    rfl
  have htx : t * x = d * d := hpt_eq.symm.trans hd_sq.symm
  have hx_eq : x = t * (d * d) := by
    have h1 : t * (t * x) = t * (d * d) := by rw [htx]
    rwa [← mul_assoc, h.t_sq, one_mul] at h1
  have hxcent : x ∈ centralizer (L : Set G) := by
    rw [hx_eq]
    exact Subgroup.mul_mem _ h.t_mem_cent (Subgroup.mul_mem _ hd hd)
  have hxB : x ∈ B := by
    rw [hx]
    exact h.data.bdata.perm.mem (sec4MW_even 0)
  have hxL : x ∈ L := h.B_le_L hxB
  have hv0 : sec4MW 0 ≠ 0 := by
    intro h0
    have hw := sec4MW_weight 0
    rw [h0] at hw
    have h0' : vecWeight (0 : Fin 7 → ZMod 2) = 0 := by simp [vecWeight]
    rw [h0'] at hw
    exact absurd hw (by decide)
  have hx2 : orderOf x = 2 := by
    rw [hx]
    exact h.data.bdata.perm.orderOf_eq_two (sec4MW_even 0) hv0
  exact sec4_not_mem_of_mem_centralizer h.omega7 hx2 hxcent hxL

end CFSG.OddStandard.SmallF3.Omega
