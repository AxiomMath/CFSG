module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Tr
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84A3Act

public section

namespace CFSG.OddStandard.SmallF3.Omega

namespace A3

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z g : G}
  {B K L1 : Subgroup G}

theorem elem_of_sq (h : Sec8T84L1 G t L S z g B K L1) (h1 : ∀ l ∈ L1, l * l = 1) :
    IsElemAb2 L1 8 := by
  have hc : ∀ a ∈ L1, ∀ b ∈ L1, a * b = b * a := by
    intro a ha b hb
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h1 a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h1 b hb)
    have hab : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right (h1 _ (L1.mul_mem ha hb))).symm
    rw [hab, mul_inv_rev, ha', hb']
  haveI : IsMulCommutative ↥L1 := ⟨⟨fun a b => Subtype.ext (hc a a.2 b b.2)⟩⟩
  exact ⟨⟨inferInstance, fun x hx => by rw [pow_two]; exact h1 x hx⟩, h.card⟩

theorem decomp_N (h8B : Asc82Lemma8B) (hctx : Sec8Ctx G t L S z g B)
    (h : Sec8T84L1 G t L S z g B K L1) :
    Nsub8 t B = L1 ⊔ (Nsub8 t B ⊓ centralizer ({t} : Set G)) := by
  apply le_antisymm
  · intro n hn
    have hb : n * t * n⁻¹ * t⁻¹ ∈ B := sec8t84a1_comm_mem h8B hctx hn
    obtain ⟨e, he, hek⟩ := tau_exists hctx h hb
    have h1 : e * t * e⁻¹ = n * t * n⁻¹ := by
      have h2 : e * t * e⁻¹ * t⁻¹ = n * t * n⁻¹ * t⁻¹ := hek
      exact mul_right_cancel h2
    have hcomm : (e⁻¹ * n) * t = t * (e⁻¹ * n) :=
      calc (e⁻¹ * n) * t = e⁻¹ * (n * t * n⁻¹) * n := by group
        _ = e⁻¹ * (e * t * e⁻¹) * n := by rw [h1]
        _ = t * (e⁻¹ * n) := by group
    have hc : e⁻¹ * n ∈ Nsub8 t B ⊓ centralizer ({t} : Set G) :=
      ⟨(Nsub8 t B).mul_mem ((Nsub8 t B).inv_mem ((setup hctx h).V_le he)) hn,
        Subgroup.mem_centralizer_singleton_iff.mpr hcomm⟩
    have hn' : n = e * (e⁻¹ * n) := by group
    rw [hn']
    exact Subgroup.mul_mem_sup he hc
  · exact sup_le (setup hctx h).V_le inf_le_left

theorem normal_N (hctx : Sec8Ctx G t L S z g B) (h : Sec8T84L1 G t L S z g B K L1) :
    ((L1 ⊔ oddCoreIn (Nsub8 t B)).subgroupOf (Nsub8 t B)).Normal := by
  refine ⟨fun y hy n => ?_⟩
  have hy' : (y : G) ∈ L1 ⊔ oddCoreIn (Nsub8 t B) := Subgroup.mem_subgroupOf.mp hy
  obtain ⟨x, hx, o, ho, hxo⟩ := (RedAct.mem_sup_iff (setup hctx h)).mp hy'
  rw [Subgroup.mem_subgroupOf]
  have e : (n : G) * (y : G) * (n : G)⁻¹ =
      ((n : G) * x * (n : G)⁻¹) * ((n : G) * o * (n : G)⁻¹) := by
    rw [hxo]
    group
  have hn1 : (n : G) * x * (n : G)⁻¹ ∈ L1 ⊔ oddCoreIn (Nsub8 t B) := h.inv n n.2 x hx
  have hn2 : (n : G) * o * (n : G)⁻¹ ∈ oddCoreIn (Nsub8 t B) :=
    sec8t84a1_O_norm (n : G) n.2 o ho
  show (n : G) * (y : G) * (n : G)⁻¹ ∈ L1 ⊔ oddCoreIn (Nsub8 t B)
  rw [e]
  exact Subgroup.mul_mem _ hn1 (Subgroup.mem_sup_right hn2)

theorem sec8E_of_sq (F : Sec8T84Base) (hctx : Sec8Ctx G t L S z g B)
    (h : Sec8T84L1 G t L S z g B K L1) (h1 : ∀ l ∈ L1, l * l = 1) :
    Sec8E G t L S z g B L1 where
  ctx := hctx
  le_N := (setup hctx h).V_le
  elem := elem_of_sq h h1
  t_norm := fun e he => L1_normal h t (t_mem_K h.K_data) e he
  cent_t := inf_cent_t hctx h
  comm_le := fun e he => (cl2_of h.K_data).tau_mem (t_mem_K h.K_data) (h.le he)
  comm_onto := fun b hb => tau_exists hctx h hb
  decomp := decomp_N F.h8B hctx h
  normal := normal_N hctx h

end A3

end CFSG.OddStandard.SmallF3.Omega
