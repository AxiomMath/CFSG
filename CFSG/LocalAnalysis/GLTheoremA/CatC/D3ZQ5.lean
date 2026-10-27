module

public import Mathlib.Algebra.Module.ZMod
public import CFSG.LocalAnalysis.GLTheoremA.CatC.D3ZT1

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.LocalAnalysis.GLTheoremA

section AbstractLayer

variable {G : Type*} [Group G]

structure IsAbLayer (H N : Subgroup G) : Prop where
  le : N ≤ H
  conj_mem : ∀ x ∈ H, ∀ n ∈ N, x * n * x⁻¹ ∈ N
  comm_mem : ∀ x ∈ H, ∀ y ∈ H, x * y * x⁻¹ * y⁻¹ ∈ N

namespace IsAbLayer

variable {H N : Subgroup G}

theorem normal (h : IsAbLayer H N) : (N.subgroupOf H).Normal where
  conj_mem n hn x := by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using h.conj_mem x.1 x.2 n.1 hn

@[expose, instance_reducible] def commGroup (h : IsAbLayer H N) : CommGroup (H ⧸ N.subgroupOf H) :=
  letI := h.normal
  { (inferInstance : Group (H ⧸ N.subgroupOf H)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
        Subgroup.mem_subgroupOf]
      have := h.comm_mem y⁻¹.1 (H.inv_mem y.2) x⁻¹.1 (H.inv_mem x.2)
      simpa [mul_assoc] using this }

theorem mk_comm (h : IsAbLayer H N) (x y : H) :
    letI := h.normal
    (QuotientGroup.mk x * QuotientGroup.mk y : H ⧸ N.subgroupOf H) =
      QuotientGroup.mk y * QuotientGroup.mk x := by
  letI := h.normal
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have := h.comm_mem y⁻¹.1 (H.inv_mem y.2) x⁻¹.1 (H.inv_mem x.2)
  simpa [mul_assoc] using this

theorem cube_mem_of_gens (h : IsAbLayer H N) {S : Set G} (hS : H = Subgroup.closure S)
    (hgen : ∀ s ∈ S, s ^ 3 ∈ N) : ∀ x ∈ H, x ^ 3 ∈ N := by
  letI := h.normal
  intro x hxH0
  have hx' := hxH0
  rw [hS] at hx'
  induction hx' using Subgroup.closure_induction with
  | mem x hxS => exact hgen x hxS
  | one => simpa using N.one_mem
  | mul x y hxm hym ihx ihy =>
    have hxH : x ∈ H := hS ▸ hxm
    have hyH : y ∈ H := hS ▸ hym
    have hx3 := ihx hxH
    have hy3 := ihy hyH
    have key : ∀ z : H, ((z : G) ^ 3 ∈ N) ↔ ((QuotientGroup.mk z : H ⧸ N.subgroupOf H)) ^ 3 = 1 := by
      intro z
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      rfl
    have hX := (key ⟨x, hxH⟩).1 hx3
    have hY := (key ⟨y, hyH⟩).1 hy3
    have hcomm : Commute (QuotientGroup.mk (⟨x, hxH⟩ : H) : H ⧸ N.subgroupOf H)
        (QuotientGroup.mk (⟨y, hyH⟩ : H)) := h.mk_comm _ _
    have hXY : ((QuotientGroup.mk (⟨x, hxH⟩ * ⟨y, hyH⟩ : H) : H ⧸ N.subgroupOf H)) ^ 3 = 1 := by
      rw [QuotientGroup.mk_mul, hcomm.mul_pow, hX, hY, one_mul]
    exact (key (⟨x, hxH⟩ * ⟨y, hyH⟩)).2 hXY
  | inv x hxm ih =>
    have hxH : x ∈ H := hS ▸ hxm
    rw [inv_pow]
    exact N.inv_mem (ih hxH)

end IsAbLayer

structure IsLayer (H N : Subgroup G) : Prop extends IsAbLayer H N where
  cube_mem : ∀ x ∈ H, x ^ 3 ∈ N

namespace IsLayer

variable {H N : Subgroup G}

theorem normal (h : IsLayer H N) : (N.subgroupOf H).Normal := h.toIsAbLayer.normal

@[expose, instance_reducible] def commGroup (h : IsLayer H N) : CommGroup (H ⧸ N.subgroupOf H) :=
  h.toIsAbLayer.commGroup

end IsLayer

@[expose] def Lyr {H N : Subgroup G} (_ : IsLayer H N) : Type _ := Additive (H ⧸ N.subgroupOf H)

namespace Lyr

variable {H N : Subgroup G} (h : IsLayer H N)

instance : AddCommGroup (Lyr h) :=
  @Additive.addCommGroup (H ⧸ N.subgroupOf H) h.commGroup

@[expose] def mk (x : H) : Lyr h :=
  @Additive.ofMul (H ⧸ N.subgroupOf H) (QuotientGroup.mk x)

theorem mk_add (x y : H) : mk h (x * y) = mk h x + mk h y := rfl

theorem mk_zero : mk h (1 : H) = 0 := rfl

theorem mk_neg (x : H) : mk h x⁻¹ = -mk h x := by
  have := mk_add h x x⁻¹
  rw [mul_inv_cancel, mk_zero] at this
  exact (neg_eq_of_add_eq_zero_right this.symm).symm

theorem mk_nsmul (n : ℕ) (x : H) : n • mk h x = mk h (x ^ n) := by
  induction n with
  | zero => rw [zero_smul, pow_zero, mk_zero]
  | succ n ih => rw [succ_nsmul, ih, pow_succ, mk_add]

theorem mk_eq_zero {x : H} : mk h x = 0 ↔ (x : G) ∈ N := by
  letI := h.normal
  change (QuotientGroup.mk x : H ⧸ N.subgroupOf H) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem mk_eq_mk {x y : H} : mk h x = mk h y ↔ ((x⁻¹ * y : H) : G) ∈ N := by
  rw [← mk_eq_zero h, mk_add, mk_neg, neg_add_eq_zero]

theorem mk_surjective : Function.Surjective (mk h) := by
  intro z
  obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (s := N.subgroupOf H) (Additive.toMul z)
  exact ⟨x, hx⟩

theorem three_nsmul (z : Lyr h) : 3 • z = 0 := by
  obtain ⟨x, rfl⟩ := mk_surjective h z
  rw [mk_nsmul, mk_eq_zero]
  exact h.cube_mem x.1 x.2

instance : Module (ZMod 3) (Lyr h) := AddCommGroup.zmodModule (n := 3) (three_nsmul h)

instance [Finite G] : Finite (Lyr h) :=
  inferInstanceAs (Finite (H ⧸ N.subgroupOf H))

theorem card_mul [Finite G] : Nat.card (Lyr h) * Nat.card N = Nat.card H := by
  letI := h.normal
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (N.subgroupOf H)
  have h2 : Nat.card (N.subgroupOf H) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  rw [← h2, h1]
  rfl

section Map

variable {H N : Subgroup G} (h : IsLayer H N)

@[expose] def restr (ϕ : G →* G) (hH : ∀ x ∈ H, ϕ x ∈ H) : H →* H where
  toFun x := ⟨ϕ x.1, hH x.1 x.2⟩
  map_one' := Subtype.ext (map_one ϕ)
  map_mul' x y := Subtype.ext (map_mul ϕ x.1 y.1)

@[expose] def map (ϕ : G →* G) (hH : ∀ x ∈ H, ϕ x ∈ H) (hN : ∀ x ∈ N, ϕ x ∈ N) : Lyr h →+ Lyr h :=
  letI := h.normal
  MonoidHom.toAdditive (QuotientGroup.map (N.subgroupOf H) (N.subgroupOf H) (restr ϕ hH)
    (fun x hx => by
      rw [Subgroup.mem_subgroupOf] at hx
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      exact hN x.1 hx))

@[expose] def mapL (ϕ : G →* G) (hH : ∀ x ∈ H, ϕ x ∈ H) (hN : ∀ x ∈ N, ϕ x ∈ N) :
    Lyr h →ₗ[ZMod 3] Lyr h :=
  (map h ϕ hH hN).toZModLinearMap 3

theorem mapL_mk (ϕ : G →* G) (hH : ∀ x ∈ H, ϕ x ∈ H) (hN : ∀ x ∈ N, ϕ x ∈ N) (x : H) :
    mapL h ϕ hH hN (mk h x) = mk h ⟨ϕ x.1, hH x.1 x.2⟩ := rfl

end Map

section Count

variable {H N : Subgroup G} (h : IsLayer H N)

theorem relIndex_inf_le [Finite G] (A : Subgroup G) (S : Set (Lyr h))
    (hS : ∀ a (ha : a ∈ A) (haH : a ∈ H), mk h ⟨a, haH⟩ ∈ S) :
    (A ⊓ N).relIndex (A ⊓ H) ≤ Nat.card S := by
  letI := h.normal
  let f : ↥(A ⊓ H) →* H ⧸ N.subgroupOf H :=
    (QuotientGroup.mk' (N.subgroupOf H)).comp (Subgroup.inclusion inf_le_right)
  have hker : f.ker = (A ⊓ N).subgroupOf (A ⊓ H) := by
    ext ⟨a, ha⟩
    simp only [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    change (QuotientGroup.mk (⟨a, ha.2⟩ : H) : H ⧸ N.subgroupOf H) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    exact ⟨fun hn => ⟨ha.1, hn⟩, fun hn => hn.2⟩
  have hidx : (A ⊓ N).relIndex (A ⊓ H) = Nat.card f.range := by
    rw [← Subgroup.index_ker, hker]; rfl
  rw [hidx]
  refine Nat.card_le_card_of_injective (fun q : f.range => (⟨Additive.ofMul q.1, ?_⟩ : S)) ?_
  · obtain ⟨⟨a, ha⟩, hq⟩ := q.2
    rw [← hq]
    exact hS a ha.1 ha.2
  · intro q q' hqq
    have h1 : Additive.ofMul q.1 = Additive.ofMul q'.1 :=
      congrArg (fun z : S => (z : Lyr h)) hqq
    exact Subtype.ext (Additive.ofMul.injective h1)

end Count

end Lyr

end AbstractLayer

end CFSG.LocalAnalysis.GLTheoremA
