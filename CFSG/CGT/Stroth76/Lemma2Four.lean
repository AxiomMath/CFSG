module

public import Mathlib.GroupTheory.Sylow
public import CFSG.CGT.Stroth76.TModel

public section

namespace CFSG.CGT.Stroth76

open CFSG.CGT.Stroth77.Arch76

section Elements

variable {X : Type*} [Group X] (K : Config X)

theorem dElt_mem_centralizer_eq_zero {d : Dc}
    (h : dElt K d ∈ Subgroup.centralizer (K.A : Set X)) : d = 0 := by
  have hfix : ∀ v, dact d v = v := fun v => K.ev_injective (by
    rw [← conj_dElt_ev, mul_assoc, Subgroup.mem_centralizer_iff.mp h _ (K.ev_mem v),
      ← mul_assoc, inv_mul_cancel, one_mul])
  exact (dact_eq_id_iff d).1 ⟨hfix _, hfix _, hfix _⟩

theorem card_sup_dElt_ge [Finite X] {B : Subgroup X} (hB : ∀ d : Dc, dElt K d ∈ B → d = 0) :
    8 * Nat.card B ≤ Nat.card (B ⊔ Subgroup.closure {K.uv, K.t, K.u} : Subgroup X) := by
  let f : B × Dc → (B ⊔ Subgroup.closure {K.uv, K.t, K.u} : Subgroup X) := fun p =>
    ⟨p.1 * dElt K p.2, mul_mem (Subgroup.mem_sup_left p.1.2)
      (Subgroup.mem_sup_right (dElt_mem_D K p.2))⟩
  have hf : Function.Injective f := by
    rintro ⟨b, d⟩ ⟨b', d'⟩ h
    have h' : (b : X) * dElt K d = b' * dElt K d' := congrArg Subtype.val h
    have hmem : dElt K (dmul d (dinv d')) ∈ B := by
      rw [dElt_mul, ← dElt_inv]
      have : dElt K d * (dElt K d')⁻¹ = (b : X)⁻¹ * b' := by
        rw [eq_inv_mul_iff_mul_eq, ← mul_assoc, h', mul_inv_cancel_right]
      rw [this]
      exact B.mul_mem (B.inv_mem b.2) b'.2
    have hd : d = d' := (dmul_dinv_eq_zero_iff d d').1 (hB _ hmem)
    subst hd
    have hb : (b : X) = b' := mul_right_cancel h'
    rw [Subtype.ext hb]
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Dc)] at this
  simpa [mul_comm] using this

end Elements

variable {X : Type*} [Group X] [Finite X] (K : Config X)

theorem arch76Lemma2_index_four [K.A.Normal] {C : Subgroup X}
    (hCA : Subgroup.centralizer (K.A : Set X) = C) (hC : Nat.card C = 2 ^ 7) (P : Sylow 2 X)
    (hTP : K.A ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P) (hP : Nat.card P ∣ 2 ^ 10) :
    (P : Subgroup X) = C ⊔ Subgroup.closure {K.uv, K.t, K.u} := by
  subst hCA
  have hCP : Subgroup.centralizer (K.A : Set X) ≤ P := (IsPGroup.of_card hC).le_sylow_of_normal P
  have hle : Subgroup.centralizer (K.A : Set X) ⊔ Subgroup.closure {K.uv, K.t, K.u} ≤ P :=
    sup_le hCP (le_sup_right.trans hTP)
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h8 := card_sup_dElt_ge K (B := Subgroup.centralizer (K.A : Set X))
    (fun d hd => dElt_mem_centralizer_eq_zero K hd)
  have hPle : Nat.card P ≤ 2 ^ 10 := Nat.le_of_dvd (by norm_num) hP
  rw [hC] at h8
  omega

end CFSG.CGT.Stroth76
