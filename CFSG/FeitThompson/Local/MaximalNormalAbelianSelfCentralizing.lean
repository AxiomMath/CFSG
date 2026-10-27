module

public import Mathlib.GroupTheory.PGroup
import CFSG.FeitThompson.Local.NormalSubgroupCentralPrimeTorsion

open Subgroup

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p a : ℕ} {P : Type*} [Group P] {A : Subgroup P}

theorem centralizer_eq_of_maximal_normal_isMulCommutative
    (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (hA : Maximal (fun B : Subgroup P => B.Normal ∧ IsMulCommutative B) A) :
    centralizer (A : Set P) = A := by
  obtain ⟨⟨hAn, hAc⟩, hAmax⟩ := hA
  have := hAn
  have := hAc
  have hAle : A ≤ centralizer (A : Set P) := Subgroup.le_centralizer A
  refine le_antisymm ?_ hAle
  by_contra hlt
  have : Fact p.Prime := ⟨hp⟩
  have hfin : Finite P := Nat.finite_of_card_ne_zero (by rw [hP]; exact pow_ne_zero _ hp.pos.ne')
  have hkerA : (QuotientGroup.mk' A).ker = A := QuotientGroup.ker_mk' A
  have hLne : (centralizer (A : Set P)).map (QuotientGroup.mk' A) ≠ ⊥ := by
    intro h
    rw [Subgroup.map_eq_bot_iff, hkerA] at h
    exact hlt h
  have : ((centralizer (A : Set P)).map (QuotientGroup.mk' A)).Normal :=
    (Subgroup.normal_centralizer (H := A)).map _ (QuotientGroup.mk'_surjective A)
  obtain ⟨b, hb⟩ := ((IsPGroup.of_card hP).to_quotient A).exists_card_eq
  obtain ⟨Q, hQle, hQcard⟩ :=
    exists_le_inf_center_natCard_eq ((centralizer (A : Set P)).map (QuotientGroup.mk' A)) hp hb hLne
  have hAT : A ≤ Q.comap (QuotientGroup.mk' A) := fun x hx => Subgroup.mem_comap.mpr <| by
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem Q
  have hTC : Q.comap (QuotientGroup.mk' A) ≤ centralizer (A : Set P) :=
    calc Q.comap (QuotientGroup.mk' A)
        ≤ ((centralizer (A : Set P)).map (QuotientGroup.mk' A)).comap (QuotientGroup.mk' A) :=
          Subgroup.comap_mono (hQle.trans inf_le_left)
      _ = centralizer (A : Set P) := Subgroup.comap_map_eq_self (hkerA.le.trans hAle)
  have hQn : Q.Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_center_iff.mp (hQle.trans inf_le_right hn) g, mul_inv_cancel_right]
      exact hn⟩
  have hTn : (Q.comap (QuotientGroup.mk' A)).Normal := hQn.comap _
  have hTc : IsMulCommutative (Q.comap (QuotientGroup.mk' A)) := by
    have : IsCyclic Q := isCyclic_of_prime_card hQcard
    refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      (((QuotientGroup.mk' A).comp (Q.comap (QuotientGroup.mk' A)).subtype).codRestrict Q
        (fun x => Subgroup.mem_comap.mp x.2)) ?_
    intro x hx
    have hxA : (x : P) ∈ A := by
      have hx1 : (QuotientGroup.mk' A) (x : P) = 1 := by
        have := congrArg Subtype.val hx
        simpa [MonoidHom.codRestrict] using this
      exact (QuotientGroup.eq_one_iff (x : P)).mp (by simpa using hx1)
    rw [Subgroup.mem_center_iff]
    intro y
    have hy := Subgroup.mem_centralizer_iff.mp (hTC y.2) (x : P) hxA
    exact Subtype.ext (by simpa using hy.symm)
  have hTA : Q.comap (QuotientGroup.mk' A) = A := le_antisymm (hAmax ⟨hTn, hTc⟩ hAT) hAT
  have hQbot : Q = ⊥ := by
    have hmc := Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective A) Q
    rw [hTA] at hmc
    rw [← hmc, Subgroup.map_eq_bot_iff, hkerA]
  rw [hQbot, Nat.card_eq_one_iff_unique.mpr ⟨inferInstance, inferInstance⟩] at hQcard
  exact hp.one_lt.ne hQcard

theorem centralizer_eq_of_forall_eq_of_normal_isMulCommutative
    (hp : p.Prime) (hP : Nat.card P = p ^ a) [hAn : A.Normal] [hAc : IsMulCommutative A]
    (hAmax : ∀ B : Subgroup P, B.Normal → IsMulCommutative B → A ≤ B → B = A) :
    centralizer (A : Set P) = A :=
  centralizer_eq_of_maximal_normal_isMulCommutative hp hP
    ⟨⟨hAn, hAc⟩, fun B hB hAB => (hAmax B hB.1 hB.2 hAB).le⟩

theorem centralizer_eq_of_maximal_normal_isMulCommutative_of_isPGroup
    [Finite P] (hp : p.Prime) (hP : IsPGroup p P)
    (hA : Maximal (fun B : Subgroup P => B.Normal ∧ IsMulCommutative B) A) :
    centralizer (A : Set P) = A := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha⟩ := hP.exists_card_eq
  exact centralizer_eq_of_maximal_normal_isMulCommutative hp ha hA

theorem mem_centralizer_coe_iff {x : P} :
    x ∈ centralizer (A : Set P) ↔ ∀ a ∈ A, x * a = a * x :=
  ⟨fun hx a ha => (Subgroup.mem_centralizer_iff.mp hx a ha).symm,
    fun hx => Subgroup.mem_centralizer_iff.mpr fun a ha => (hx a ha).symm⟩

theorem mem_of_forall_mul_comm_of_maximal_normal_isMulCommutative
    (hp : p.Prime) (hP : Nat.card P = p ^ a)
    (hA : Maximal (fun B : Subgroup P => B.Normal ∧ IsMulCommutative B) A)
    {x : P} (hx : ∀ b ∈ A, x * b = b * x) : x ∈ A :=
  centralizer_eq_of_maximal_normal_isMulCommutative hp hP hA ▸ mem_centralizer_coe_iff.mpr hx

end

end CFSG.FeitThompson
