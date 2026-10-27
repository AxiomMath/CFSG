module

public import CFSG.HardMathSupport.Curtis.Proving.ActsTrivially

public section

namespace CFSG.HardMathSupport.Curtis.Proving

open CFSG.QuasithinUnique CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G]

theorem blockU_le_blockQ {L : Subgroup G} (hL : IsShort2 L) : blockU L ≤ blockQ L :=
  fun _ hx => (Subgroup.mem_inf.1 (hL.2.2.1.1 hx)).1

theorem blockU_mem_centralizer_blockQ {L : Subgroup G} (hL : IsShort2 L) {x : G}
    (hx : x ∈ blockU L) : x ∈ Subgroup.centralizer (blockQ L : Set G) :=
  (Subgroup.mem_inf.1 (hL.2.2.1.1 hx)).2

theorem blockU_comm {L : Subgroup G} (hL : IsShort2 L) {x y : G} (hx : x ∈ blockU L)
    (hy : y ∈ blockU L) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.1 (blockU_mem_centralizer_blockQ hL hx) y
    (blockU_le_blockQ hL hy)).symm

theorem blockU_sq {L : Subgroup G} (hL : IsShort2 L) {x : G} (hx : x ∈ blockU L) : x ^ 2 = 1 :=
  hL.2.2.1.2 x hx

theorem blockU_le_L (L : Subgroup G) : blockU L ≤ L := by
  have hQL : blockQ L ≤ L := by
    intro q hq
    unfold blockQ pCoreOf at hq
    obtain ⟨y, _, rfl⟩ := Subgroup.mem_map.mp hq
    exact y.2
  unfold blockU
  rw [Subgroup.commutator_le]
  intro q hq x hx
  rw [commutatorElement_def]
  exact L.mul_mem (L.mul_mem (L.mul_mem (hQL hq) hx) (L.inv_mem (hQL hq))) (L.inv_mem hx)

instance blockZ_subgroupOf_normal (L : Subgroup G) :
    ((blockZ L).subgroupOf (blockU L)).Normal :=
  ⟨fun n hn g => by
    have hg : (g : G) ∈ L := blockU_le_L L g.2
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hn ⊢
    exact blockZ_conj_mem_normalizer (Subgroup.le_normalizer hg) hn⟩

abbrev UZ (L : Subgroup G) : Type := ↥(blockU L) ⧸ (blockZ L).subgroupOf (blockU L)

instance UZ_commGroup (L : Subgroup G) [hL : Fact (IsShort2 L)] : CommGroup (UZ L) :=
  { (inferInstance : Group (UZ L)) with
    mul_comm := by
      intro x y
      induction x using QuotientGroup.induction_on with
      | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
          congr 1
          exact Subtype.ext (blockU_comm hL.out a.2 b.2) }

theorem UZ_sq_eq_one (L : Subgroup G) [hL : Fact (IsShort2 L)] (y : UZ L) : y ^ 2 = 1 := by
  induction y using QuotientGroup.induction_on with
  | H a =>
    rw [← QuotientGroup.mk_pow]
    have ha : a ^ 2 = 1 := Subtype.ext (by simpa using blockU_sq hL.out a.2)
    rw [ha, QuotientGroup.mk_one]

instance UZ_module (L : Subgroup G) [Fact (IsShort2 L)] : Module (ZMod 2) (Additive (UZ L)) :=
  AddCommGroup.zmodModule (n := 2) (fun x => by
    have h2 : Additive.ofMul ((Additive.toMul x) ^ 2) = Additive.ofMul 1 :=
      congrArg _ (UZ_sq_eq_one L (Additive.toMul x))
    rw [ofMul_pow, ofMul_one] at h2
    exact h2)

end CFSG.HardMathSupport.Curtis.Proving

end
