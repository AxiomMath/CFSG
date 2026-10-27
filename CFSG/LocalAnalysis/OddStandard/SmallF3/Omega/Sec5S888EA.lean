module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5Defs

public section

open Subgroup

namespace CFSG.OddStandard.SmallF3.Omega

variable {G : Type} [Group G]

theorem relIndex_eq_two_pow_of_elemAb [Finite G] {C U : Subgroup G}
    (hab : IsElemAbelianModSub C U) : ∃ n : ℕ, C.relIndex U = 2 ^ n := by
  let W : Subgroup U := C.subgroupOf U
  have hWnormal : W.Normal := by
    refine ⟨fun w hw g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hw ⊢
    change (g : G) * (w : G) * (g : G)⁻¹ ∈ C
    have hcomm := (hab (g : G) g.2 (w : G) w.2).1
    have heq : (g : G) * (w : G) * (g : G)⁻¹ =
        ((g : G) * (w : G) * (g : G)⁻¹ * (w : G)⁻¹) * (w : G) := by group
    rw [heq]
    exact mul_mem hcomm hw
  haveI : W.Normal := hWnormal
  have hsq : ∀ x : U ⧸ W, x * x = 1 := by
    intro x
    refine QuotientGroup.induction_on x ?_
    intro a
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simpa only [Subgroup.coe_mul] using (hab (a : G) a.2 (a : G) a.2).2
  have hP : IsPGroup 2 (U ⧸ W) := fun x => ⟨1, by rw [pow_one, pow_two]; exact hsq x⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hP
  exact ⟨n, by rw [show C.relIndex U = Nat.card (U ⧸ W) from rfl, hn]⟩

theorem IsElemAbelianModSub.mono {C U V : Subgroup G} (hab : IsElemAbelianModSub C U)
    (hVU : V ≤ U) : IsElemAbelianModSub C V :=
  fun a ha b hb => hab a (hVU ha) b (hVU hb)

private lemma exists_mul_of_mem_sup {C U : Subgroup G}
    (hCU : ∀ u ∈ U, ∀ c ∈ C, u * c * u⁻¹ ∈ C) {x : G} (hx : x ∈ U ⊔ C) :
    ∃ u ∈ U, ∃ c ∈ C, x = u * c := by
  let S : Subgroup G :=
    { carrier := {x | ∃ u ∈ U, ∃ c ∈ C, x = u * c}
      one_mem' := ⟨1, one_mem U, 1, one_mem C, by rw [mul_one]⟩
      mul_mem' := by
        rintro x y ⟨u, hu, c, hc, rfl⟩ ⟨v, hv, d, hd, rfl⟩
        refine ⟨u * v, mul_mem hu hv, (v⁻¹ * c * v) * d, mul_mem ?_ hd, by group⟩
        simpa using hCU v⁻¹ (inv_mem hv) c hc
      inv_mem' := by
        rintro x ⟨u, hu, c, hc, rfl⟩
        refine ⟨u⁻¹, inv_mem hu, u * c⁻¹ * u⁻¹, ?_, by group⟩
        simpa using hCU u hu c⁻¹ (inv_mem hc) }
  have hS : U ⊔ C ≤ S :=
    sup_le (fun u hu => ⟨u, hu, 1, one_mem C, by rw [mul_one]⟩)
      (fun c hc => ⟨1, one_mem U, c, hc, by rw [one_mul]⟩)
  exact hS hx

theorem isElemAbelianModSub_sup {C U : Subgroup G}
    (hCU : ∀ u ∈ U, ∀ c ∈ C, u * c * u⁻¹ ∈ C)
    (hab : IsElemAbelianModSub C U) : IsElemAbelianModSub C (U ⊔ C) := by
  intro a ha b hb
  obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup hCU ha
  obtain ⟨v, hv, d, hd, rfl⟩ := exists_mul_of_mem_sup hCU hb
  refine ⟨?_, ?_⟩
  · have hα : u * c * u⁻¹ ∈ C := hCU u hu c hc
    have hβ : (u * v) * d * (u * v)⁻¹ ∈ C := hCU (u * v) (mul_mem hu hv) d hd
    have hγ : u * v * u⁻¹ * v⁻¹ ∈ C := (hab u hu v hv).1
    have hδ : (v * u) * c⁻¹ * (v * u)⁻¹ ∈ C :=
      hCU (v * u) (mul_mem hv hu) c⁻¹ (inv_mem hc)
    have hε : (v * d * v⁻¹)⁻¹ ∈ C := inv_mem (hCU v hv d hd)
    have heq : (u * c) * (v * d) * (u * c)⁻¹ * (v * d)⁻¹ =
        (u * c * u⁻¹) * ((u * v) * d * (u * v)⁻¹) * (u * v * u⁻¹ * v⁻¹) *
          ((v * u) * c⁻¹ * (v * u)⁻¹) * (v * d * v⁻¹)⁻¹ := by group
    rw [heq]
    exact mul_mem (mul_mem (mul_mem (mul_mem hα hβ) hγ) hδ) hε
  · have hα : u * c * u⁻¹ ∈ C := hCU u hu c hc
    have hγ : u * u ∈ C := (hab u hu u hu).2
    have heq : (u * c) * (u * c) = (u * c * u⁻¹) * (u * u) * c := by group
    rw [heq]
    exact mul_mem (mul_mem hα hγ) hc

theorem relIndex_le_of_forall_mul [Finite G] {A B C : Subgroup G}
    (h : ∀ a ∈ A, ∃ b ∈ B, ∃ c ∈ C, a = b * c) : C.relIndex A ≤ C.relIndex B := by
  classical
  have hchoose : ∀ a : A, ∃ b : B, ∃ c ∈ C, (a : G) = (b : G) * c := by
    intro a
    obtain ⟨b, hb, c, hc, hac⟩ := h a a.2
    exact ⟨⟨b, hb⟩, c, hc, hac⟩
  let pick : A → B := fun a => Classical.choose (hchoose a)
  have hpick : ∀ a : A, ∃ c ∈ C, (a : G) = (pick a : G) * c :=
    fun a => Classical.choose_spec (hchoose a)
  have hwd : ∀ a a' : A, QuotientGroup.leftRel (C.subgroupOf A) a a' →
      (QuotientGroup.mk (s := C.subgroupOf B) (pick a)) =
        (QuotientGroup.mk (s := C.subgroupOf B) (pick a')) := by
    intro a a' hr
    obtain ⟨c, hc, hac⟩ := hpick a
    obtain ⟨d, hd, hbd⟩ := hpick a'
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change ((pick a : B) : G)⁻¹ * ((pick a' : B) : G) ∈ C
    have hrC : (a : G)⁻¹ * (a' : G) ∈ C := by
      rw [QuotientGroup.leftRel_apply, Subgroup.mem_subgroupOf] at hr
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hr
    have hkey : ((pick a : B) : G)⁻¹ * ((pick a' : B) : G) =
        c * ((a : G)⁻¹ * (a' : G)) * d⁻¹ := by
      rw [hac, hbd]
      group
    rw [hkey]
    exact mul_mem (mul_mem hc hrC) (inv_mem hd)
  let F : A ⧸ (C.subgroupOf A) → B ⧸ (C.subgroupOf B) :=
    Quotient.lift (fun a : A => QuotientGroup.mk (s := C.subgroupOf B) (pick a)) hwd
  have hinj : Function.Injective F := by
    intro x
    refine Quotient.inductionOn x ?_
    intro a y
    refine Quotient.inductionOn y ?_
    intro b hxy
    change QuotientGroup.mk (s := C.subgroupOf B) (pick a) =
      QuotientGroup.mk (s := C.subgroupOf B) (pick b) at hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hxy
    change ((pick a : B) : G)⁻¹ * ((pick b : B) : G) ∈ C at hxy
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    change (a : G)⁻¹ * (b : G) ∈ C
    obtain ⟨c, hc, hac⟩ := hpick a
    obtain ⟨d, hd, hbd⟩ := hpick b
    have hkey : (a : G)⁻¹ * (b : G) =
        c⁻¹ * (((pick a : B) : G)⁻¹ * ((pick b : B) : G)) * d := by
      rw [hac, hbd]
      group
    rw [hkey]
    exact mul_mem (mul_mem (inv_mem hc) hxy) hd
  have hcard : Nat.card (A ⧸ (C.subgroupOf A)) ≤ Nat.card (B ⧸ (C.subgroupOf B)) :=
    Nat.card_le_card_of_injective F hinj
  change Nat.card (A ⧸ (C.subgroupOf A)) ≤ Nat.card (B ⧸ (C.subgroupOf B))
  exact hcard

end CFSG.OddStandard.SmallF3.Omega
