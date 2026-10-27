module

public import CFSG.GH74.Generic.S1.Exo.NbShape

public section

namespace CFSG.GH74.Generic.S1.Exo

open CFSG Subgroup CFSG.GH74 CFSG.GH74.GLS

namespace NbhdHyp

variable {H : Type} [Group H] [Finite H] {q : ℕ} {w y : H} {J₂ J₄ : Subgroup H}
  (h : NbhdHyp H q w y J₂ J₄)

include h

theorem conj_inv_eq {g : H} (hg : g * y * g⁻¹ = w * y) : g⁻¹ * y * g = w * y := by
  have e1 : g⁻¹ * (g * y * g⁻¹) * g = y := by group
  rw [hg] at e1
  have e2 : g⁻¹ * (w * y) * g = w * (g⁻¹ * y * g) := by
    have hw : g⁻¹ * w = w * g⁻¹ := by rw [h.w_central g⁻¹]
    calc g⁻¹ * (w * y) * g = (g⁻¹ * w) * y * g := by group
      _ = (w * g⁻¹) * y * g := by rw [hw]
      _ = w * (g⁻¹ * y * g) := by group
  rw [e2] at e1
  have e3 : w * (w * (g⁻¹ * y * g)) = w * y := by rw [e1]
  rw [← mul_assoc, h.w_sq, one_mul] at e3
  exact e3

theorem conj_mem_cent {g : H} (hg : g * y * g⁻¹ = w * y) (c : H) :
    g * c * g⁻¹ ∈ centralizer ({w * y} : Set H) ↔ c ∈ centralizer ({w * y} : Set H) := by
  rw [h.mem_cent_iff, h.mem_cent_iff]
  have hgi := h.conj_inv_eq hg
  have hw : ∀ x : H, w * x = x * w := fun x => (h.w_central x).symm
  constructor
  · intro hc
    have e : c * (g⁻¹ * y * g) = (g⁻¹ * y * g) * c := by
      calc c * (g⁻¹ * y * g) = g⁻¹ * ((g * c * g⁻¹) * y) * g := by group
        _ = g⁻¹ * (y * (g * c * g⁻¹)) * g := by rw [hc]
        _ = (g⁻¹ * y * g) * c := by group
    rw [hgi] at e
    have e' : w * (c * y) = w * (y * c) := by
      calc w * (c * y) = c * (w * y) := by rw [← mul_assoc, hw c, mul_assoc]
        _ = (w * y) * c := e
        _ = w * (y * c) := by rw [mul_assoc]
    exact mul_left_cancel e'
  · intro hc
    have e : (g * c * g⁻¹) * y = y * (g * c * g⁻¹) := by
      have h1 : c * (w * y) = (w * y) * c := by
        calc c * (w * y) = w * (c * y) := by rw [← mul_assoc, ← hw c, mul_assoc]
          _ = w * (y * c) := by rw [hc]
          _ = (w * y) * c := by rw [mul_assoc]
      rw [← hgi] at h1
      calc (g * c * g⁻¹) * y = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by rw [h1]
        _ = y * (g * c * g⁻¹) := by group
    exact e

@[expose] def centConj {g : H} (hg : g * y * g⁻¹ = w * y) :
    ↥(centralizer ({w * y} : Set H)) ≃* ↥(centralizer ({w * y} : Set H)) where
  toFun c := ⟨g * c * g⁻¹, (h.conj_mem_cent hg c).2 c.2⟩
  invFun c := ⟨g⁻¹ * c * g, (h.conj_mem_cent hg (g⁻¹ * c * g)).1 (by
    have : g * (g⁻¹ * (c : H) * g) * g⁻¹ = c := by group
    rw [this]
    exact c.2)⟩
  left_inv c := by
    apply Subtype.ext
    show g⁻¹ * (g * (c : H) * g⁻¹) * g = c
    group
  right_inv c := by
    apply Subtype.ext
    show g * (g⁻¹ * (c : H) * g) * g⁻¹ = c
    group
  map_mul' a b := by
    apply Subtype.ext
    show g * ((a : H) * b) * g⁻¹ = g * a * g⁻¹ * (g * b * g⁻¹)
    group

theorem not_conj_wy (g : H) : g * y * g⁻¹ ≠ w * y := by
  intro hg
  set C : Subgroup H := centralizer ({w * y} : Set H) with hCdef
  have hyC : y ∈ C := (h.mem_cent_iff y).2 rfl
  have hJ₂C : J₂ ≤ C := h.J₂_le_cent
  have hJ₄C : J₄ ≤ C := h.J₄_le_cent
  let φ := h.centConj hg
  let L : Subgroup ↥C := (J₄.subgroupOf C).map φ.toMonoidHom
  have hLc : IsComponent L := CFSG.LocalCores.isComponent_map_mulEquiv φ h.comp₄
  have hLsup : L.map C.subtype ≤ J₂ ⊔ J₄ := h.bal L hLc
  have hwy_mem : (w * y) ∈ L.map C.subtype := by
    refine ⟨φ ⟨y, hyC⟩, ⟨⟨y, hyC⟩, ?_, rfl⟩, ?_⟩
    · exact h.y_mem
    · exact hg
  have hd2 := CFSG.LocalCores.distinct_components_commute hLc h.comp₂
  have hd4 := CFSG.LocalCores.distinct_components_commute hLc h.comp₄
  rcases hd2 with hL2 | hc2
  · have hwyJ₂ : (w * y) ∈ J₂ := by
      have hm := hwy_mem
      rw [hL2] at hm
      obtain ⟨c, hc, hcy⟩ := hm
      have hc' : (c : H) ∈ J₂ := hc
      rwa [show (c : H) = w * y from hcy] at hc'
    have hyJ₂ : y ∈ J₂ := by
      have := J₂.mul_mem h.w_mem hwyJ₂
      rwa [← mul_assoc, h.w_sq, one_mul] at this
    rcases h.cent₂ y hyJ₂ (fun b hb => (h.comm b hb y h.y_mem).symm) with h1 | h1
    · exact h.y_ne_one h1
    · exact h.w_ne_y h1.symm
  · rcases hd4 with hL4 | hc4
    · have hwyJ₄ : (w * y) ∈ J₄ := by
        have hm := hwy_mem
        rw [hL4] at hm
        obtain ⟨c, hc, hcy⟩ := hm
        have hc' : (c : H) ∈ J₄ := hc
        rwa [show (c : H) = w * y from hcy] at hc'
      have hwJ₄ : w ∈ J₄ := by
        have := J₄.mul_mem hwyJ₄ (J₄.inv_mem h.y_mem)
        rwa [mul_assoc, mul_inv_cancel, mul_one] at this
      rcases h.cent₄ w hwJ₄ (fun b _ => (h.w_central b).symm) with h1 | h1
      · exact h.w_ne_one h1
      · exact h.w_ne_y h1
    ·
      have hcomm2 := nb_comm_of_commutator_eq_bot hc2
      have hcomm4 := nb_comm_of_commutator_eq_bot hc4
      have hq : IsQuasisimple ↥(L.map C.subtype) :=
        CFSG.LocalCores.isQuasisimple_of_mulEquiv (L.equivMapOfInjective C.subtype C.subtype_injective)
          hLc.1
      have hcent : ∀ b ∈ L.map C.subtype, ∀ a ∈ J₂ ⊔ J₄, a * b = b * a := by
        rintro _ ⟨ℓ, hℓ, rfl⟩ a ha
        have hle : J₂ ⊔ J₄ ≤ centralizer ({(ℓ : H)} : Set H) := by
          refine sup_le (fun a' ha' => ?_) (fun a' ha' => ?_)
          · rw [Subgroup.mem_centralizer_singleton_iff]
            have := hcomm2 ℓ hℓ ⟨a', hJ₂C ha'⟩ ha'
            exact (congrArg Subtype.val this).symm
          · rw [Subgroup.mem_centralizer_singleton_iff]
            have := hcomm4 ℓ hℓ ⟨a', hJ₄C ha'⟩ ha'
            exact (congrArg Subtype.val this).symm
        have := hle ha
        rw [Subgroup.mem_centralizer_singleton_iff] at this
        exact this
      exact nb_false_of_comm_self hq (fun a ha b hb => hcent b hb a (hLsup ha))

end NbhdHyp

end CFSG.GH74.Generic.S1.Exo
