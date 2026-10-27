module

public import CFSG.GH74.GLS.C3.Prop121.Card7Abs2
public import CFSG.GH74.GLS.C3.Layer3.Basic

public section

namespace CFSG.GH74.GLS.C3.Prop121.Card7

open Subgroup Equiv Perm CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model

section Arith

variable {M : Type*} [Group M]

theorem ccard_inv_left (u v : M) : ccard M u⁻¹ v = ccard M u v := by
  unfold ccard
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun c => ?_))
  have h : (c * u⁻¹ = u⁻¹ * c) ↔ (c * u = u * c) := Commute.inv_right_iff (a := c) (b := u)
  rw [h]

theorem cc3_swap13 {G : Type*} [Group G] (a u v : G) : cc3 a u v = cc3 v u a := by
  unfold cc3
  refine Nat.card_congr (Equiv.subtypeEquivRight (fun c => ?_))
  tauto

end Arith

namespace Ctx

variable {G : Type} [Group G] {C : Ctx G}

@[expose] def Y1.B (Y : C.Y1) : Subgroup G := centralizer ({Y.y1} : Set G) ⊓ centralizer ({C.s} : Set G)

theorem Y1.card_B [Finite G] (hH : HFacts) (Y : C.Y1) : Nat.card ↥Y.B = 576 := by
  unfold Y1.B
  rw [card_inf_centralizer]
  exact (Y.tau_cases hH).2

theorem Y1.mem_self (Y : C.Y1) : Y.y1 ∈ centralizer ({Y.y1} : Set G) :=
  mem_centralizer_singleton_iff.2 rfl

theorem exists_sylow_B [Finite G] (hF : FFacts) (hH : HFacts) (Y : C.Y1) :
    ∃ Q : Sylow 2 ↥(centralizer ({C.s} : Set G)),
      ∀ q ∈ (Q : Subgroup ↥(centralizer ({C.s} : Set G))), (q : G) * Y.y1 = Y.y1 * (q : G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R⟩ : Nonempty (Sylow 2 ↥Y.B) := inferInstance
  have hRcard : Nat.card (R : Subgroup ↥Y.B) = 64 := by
    rw [Sylow.card_eq_multiplicity, Y.card_B hH]
    have h : (576 : ℕ).factorization 2 = 6 := by decide +kernel
    rw [h]
    norm_num
  set P : Subgroup G := (R : Subgroup ↥Y.B).map Y.B.subtype with hP
  have hPB : P ≤ Y.B := by
    rintro _ ⟨r, -, rfl⟩
    exact r.2
  have hPcard : Nat.card P = 64 := by
    rw [hP, Subgroup.card_map_of_injective Y.B.subtype_injective, hRcard]
  have hPp : IsPGroup 2 P := R.isPGroup'.map Y.B.subtype
  have hPs : P ≤ centralizer ({C.s} : Set G) := fun p hp => (hPB hp).2
  set P' : Subgroup ↥(centralizer ({C.s} : Set G)) :=
    P.subgroupOf (centralizer ({C.s} : Set G)) with hP'
  have hP'card : Nat.card P' = 64 := by
    rw [hP', ← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPs).toEquiv
  have hP'p : IsPGroup 2 P' := by
    have : IsPGroup 2 ↥P := hPp
    exact IsPGroup.of_card (n := 6) (by rw [hP'card]; norm_num)
  obtain ⟨Q, hQ⟩ := hP'p.exists_le_sylow
  have hQle : Nat.card (Q : Subgroup ↥(centralizer ({C.s} : Set G))) ≤ 64 := by
    have hmap := C.pgroup_le_64 hF hH ((Q : Subgroup ↥(centralizer ({C.s} : Set G))).map
      (centralizer ({C.s} : Set G)).subtype) (Q.isPGroup'.map _) (by
        rintro _ ⟨q, -, rfl⟩
        exact mem_centralizer_singleton_iff.1 q.2)
    rwa [Subgroup.card_map_of_injective (centralizer ({C.s} : Set G)).subtype_injective] at hmap
  have hEq : (Q : Subgroup ↥(centralizer ({C.s} : Set G))) = P' :=
    (Subgroup.eq_of_le_of_card_ge hQ (by rw [hP'card]; exact hQle)).symm
  refine ⟨Q, fun q hq => ?_⟩
  rw [hEq] at hq
  exact (mem_centralizer_singleton_iff.1 (hPB (Subgroup.mem_subgroupOf.1 hq)).1)

theorem exists_conj_mem_B [Finite G] (hF : FFacts) (hH : HFacts) (Y : C.Y1) (w : G)
    (hw : orderOf w = 2) (hws : w * C.s = C.s * w) :
    ∃ c : G, c * C.s = C.s * c ∧ (c * w * c⁻¹) * Y.y1 = Y.y1 * (c * w * c⁻¹) := by
  obtain ⟨Q, hQ⟩ := exists_sylow_B hF hH Y
  have hw' : orderOf (⟨w, mem_centralizer_singleton_iff.2 hws⟩ :
      ↥(centralizer ({C.s} : Set G))) = 2 := by
    rw [← Subgroup.orderOf_coe]; exact hw
  obtain ⟨g, hg⟩ := CFSG.GH74.GLS.Layer3.exists_conj_mem_sylow_two Q hw'
  refine ⟨(g : G), mem_centralizer_singleton_iff.1 g.2, ?_⟩
  have := hQ _ hg
  simpa using this

end Ctx

end CFSG.GH74.GLS.C3.Prop121.Card7
