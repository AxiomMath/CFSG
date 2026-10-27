module

public import CFSG.LocalAnalysis.EvenBN.GMS.GMS43Local

public section

namespace CFSG.LocalAnalysis.EvenBN.GMS

open Subgroup CFSG.LocalAnalysis CFSG.ABGLocalTools

@[expose] def LocalFieldBound {H : Type*} [Group H] (A : Subgroup H) (t : H) (n : ℕ) : Prop :=
  (∀ x ∈ centralizer ({t} : Set H), x ^ 2 ∈ A ⊔ centralizer (A : Set H)) ∧
  (n = 2 → centralizer ({t} : Set H) ≤ A ⊔ centralizer (A : Set H))

namespace LocalSetting

section Bound

variable {H : Type*} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}
  (h : LocalSetting A t U V D n) (hF : LocalFieldBound A t n) {T : Subgroup H}
  (hT : IsSylowOf 2 T (centralizer ({t} : Set H))) (hUT : U ≤ T)
include h hF hT hUT

theorem mul_self_mem_of_localFieldBound {x : H} (hx : x ∈ T) : x * x ∈ U ⊔ zpowers t := by
  rw [← h.T_inf_sup hT hUT]
  exact mem_inf.mpr ⟨mul_mem hx hx, by rw [← sq]; exact hF.1 x (hT.le hx)⟩

theorem relIndex_le_two_of_localFieldBound : (U ⊔ zpowers t).relIndex T ≤ 2 := by
  refine relIndex_le_two_of_forall_mul_mem fun a ha b hb haB hbB => ?_
  have hab := h.inv_mul_mem_of_mul_self_mem hT hUT ha hb haB hbB
    (h.mul_self_mem_of_localFieldBound hF hT hUT ha)
    (h.mul_self_mem_of_localFieldBound hF hT hUT hb)
  rw [show a * b = (a * a) * (a⁻¹ * b) by group]
  exact mul_mem (h.mul_self_mem_of_localFieldBound hF hT hUT ha) hab

theorem le_B_of_localFieldBound (hn : n = 2) : T ≤ U ⊔ zpowers t := by
  intro x hx
  rw [← h.T_inf_sup hT hUT]
  exact mem_inf.mpr ⟨hx, hF.2 hn (hT.le hx)⟩

end Bound

section Main

variable {H : Type} [Group H] [Finite H] {A : Subgroup H} {t : H} {U V D : Subgroup H} {n : ℕ}

theorem exists_sylow_stronglyClosed (h : LocalSetting A t U V D n)
    (hF : LocalFieldBound A t n) :
    ∃ S : Sylow 2 H, V ≤ S ∧
      ∀ v ∈ V, ∀ g : H, g⁻¹ * v * g ∈ (S : Subgroup H) → g⁻¹ * v * g ∈ V := by
  obtain ⟨T, h43⟩ := h.exists_hyp43
  rcases Nat.lt_or_ge n 3 with hn | hn
  · have hn2 : n = 2 := by have := h.two_le; omega
    have hTB := h.le_B_of_localFieldBound hF h43.sylow h43.U_le hn2
    have hle : V ⊔ T ≤ V ⊔ zpowers t := sup_le le_sup_left (hTB.trans h43.B_le_Vt)
    obtain ⟨P, hP, hcl⟩ := h43.exists_sylow_of_no_involution fun y hy _ => hle hy
    exact ⟨P, hP ▸ le_sup_left, fun v hv g hg => hcl v hv g (hP ▸ hg)⟩
  · exact h43.exists_sylow_of_relIndex_le_two hn
      (h.relIndex_le_two_of_localFieldBound hF h43.sylow h43.U_le)

end Main

end LocalSetting

end CFSG.LocalAnalysis.EvenBN.GMS
