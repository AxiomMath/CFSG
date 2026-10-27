module

public import CFSG.CGT.Stroth76.NoInvFrame
public import CFSG.CGT.Stroth77.Stroth34Local

public section

namespace CFSG.CGT.Stroth77

variable {G : Type} [Group G] [Finite G]

theorem StrothFrame.mem_A_of_involution (F : StrothFrame G) {z : G}
    (hzS : z ∈ (F.S : Subgroup G)) (hz2 : z * z = 1)
    (hzA : z ∈ Subgroup.centralizer (F.A : Set G))
    (huv : z⁻¹ * (F.dA.uv⁻¹ * z * F.dA.uv) ∈ F.A) (ht : z⁻¹ * (F.dA.t⁻¹ * z * F.dA.t) ∈ F.A) :
    z ∈ F.A := by
  have hz : ∀ y ∈ Subgroup.zpowers z, y = 1 ∨ y = z := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two]; exact hz2
    rcases Int.even_or_odd' k with ⟨j, rfl | rfl⟩
    · left; rw [zpow_mul, h2, one_zpow]
    · right; rw [zpow_add_one, zpow_mul, h2, one_zpow, one_mul]
  refine Stroth76.frame_noInvolutionsCentralizing_of_conj F (B := F.A)
    (C := Subgroup.zpowers z) le_rfl (fun b hb _ => hb) ((Subgroup.zpowers_le).mpr hzS)
    ((Subgroup.zpowers_le).mpr hzA) ?_ ?_ z (Subgroup.mem_zpowers z) hz2 hzA
  · intro y hy
    rcases hz y hy with rfl | rfl
    · simp
    · exact huv
  · intro y hy
    rcases hz y hy with rfl | rfl
    · simp
    · exact ht

namespace Local.Setting

variable {S D : Subgroup G} (h : Setting S D)

theorem proj_mem_centralizer_mhoOne {g r : G} (hg : g ∈ Subgroup.normalizer (D : Set G))
    (hr : r ∈ h.R) (hrC : r ∈ Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G)) :
    h.proj g r ∈ Subgroup.centralizer ((mhoOne D : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyD : y ∈ D := CFSG.GroupTheory.HuppertProduct.mho_le D 2 hy
  have hgy : g * y * g⁻¹ ∈ mhoOne D := CFSG.GroupTheory.HuppertProduct.conj_mem_mho
    (fun s hs => by simpa using (Subgroup.mem_normalizer_iff''.mp (inv_mem hg) s).mp hs) hy
  have hc := Subgroup.mem_centralizer_iff.mp hrC _ hgy
  have e := h.proj_conj_D hg hr hyD
  have e' : (g⁻¹ * r * g)⁻¹ * y * (g⁻¹ * r * g) = y := by
    calc (g⁻¹ * r * g)⁻¹ * y * (g⁻¹ * r * g) = g⁻¹ * r⁻¹ * ((g * y * g⁻¹) * r) * g := by group
      _ = g⁻¹ * r⁻¹ * (r * (g * y * g⁻¹)) * g := by rw [hc]
      _ = y := by group
  rw [e'] at e
  calc y * h.proj g r = h.proj g r * ((h.proj g r)⁻¹ * y * h.proj g r) := by group
    _ = h.proj g r * y := by rw [e]

end Local.Setting

end CFSG.CGT.Stroth77
