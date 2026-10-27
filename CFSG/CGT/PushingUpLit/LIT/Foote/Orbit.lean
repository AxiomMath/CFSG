module

public import CFSG.CGT.PushingUpLit.LIT.Foote.Setting

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem rightConjugate_inj' {A B : Subgroup G} {g : G} :
    rightConjugate A g = rightConjugate B g ↔ A = B := by
  constructor
  · intro h
    exact Subgroup.map_injective (MulAut.conj g⁻¹).injective h
  · intro h
    rw [h]

omit [Finite G] in
theorem rightConjugate_eq_iff {J : Subgroup G} {a b : G} :
    rightConjugate J a = rightConjugate J b ↔ b * a⁻¹ ∈ Subgroup.normalizer (J : Set G) := by
  constructor
  · intro h
    have := congrArg (fun A => rightConjugate A a⁻¹) h
    simp only [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this
    exact (rightConjugate_eq_self_iff J _).1 this.symm
  · intro h
    have h' := (rightConjugate_eq_self_iff J _).2 h
    calc rightConjugate J a = rightConjugate (rightConjugate J (b * a⁻¹)) a := by rw [h']
      _ = rightConjugate J b := by rw [rightConjugate_mul]; congr 1; group

omit [Finite G] in
theorem blockU_rightConjugate (K : Subgroup G) (g : G) :
    blockU (rightConjugate K g) = rightConjugate (blockU K) g := by
  have h1 : oTwoIn (rightConjugate K g) = rightConjugate (oTwoIn K) g :=
    oTwoIn_map_equiv (MulAut.conj g⁻¹) K
  unfold blockU
  rw [h1]
  exact (Subgroup.map_commutator (oTwoIn K) K (MulAut.conj g⁻¹).toMonoidHom).symm

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem conj {m : G} (hm : m ∈ M) : CE G M (rightConjugate J m) where
  simple := c.simple
  charTwo := c.charTwo
  maxLocal := c.maxLocal
  le := c.conj_le hm
  subnormal := c.subnormal_conj hm
  block := c.block.conj m
  unique := by
    ext M'
    simp only [maximalTwoLocalsContaining, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨hM', hsub⟩
      exact c.maxLocal_eq hM' hm fun x hx => hsub hx
    · rintro rfl
      exact ⟨c.maxLocal, fun x hx => c.conj_le hm hx⟩
  notNormal := by
    intro hn
    apply c.notNormal
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer c.le]
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (c.conj_le hm)] at hn
    intro k hk
    have hk' : m⁻¹ * k⁻¹ * m ∈ M := M.mul_mem (M.mul_mem (M.inv_mem hm) (M.inv_mem hk)) hm
    have h1 := (rightConjugate_eq_self_iff _ _).2 (hn hk')
    rw [rightConjugate_mul, rightConjugate_eq_iff] at h1
    have e : m * (m * (m⁻¹ * k⁻¹ * m))⁻¹ = k := by group
    rw [e] at h1
    exact h1

theorem commutator_conj_conj_eq_bot {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (hne : rightConjugate J a ≠ rightConjugate J b) :
    ⁅rightConjugate J a, rightConjugate J b⁆ = ⊥ := by
  have hm : a⁻¹ * b ∈ M := M.mul_mem (M.inv_mem ha) hb
  have e : rightConjugate (rightConjugate J a) (a⁻¹ * b) = rightConjugate J b := by
    rw [rightConjugate_mul]
    congr 1
    group
  have hne' : rightConjugate (rightConjugate J a) (a⁻¹ * b) ≠ rightConjugate J a := by
    rw [e]
    exact hne.symm
  have := (c.conj ha).commutator_conj_eq_bot hm hne'
  rwa [e] at this

theorem commute_conj_elems {a b : G} (ha : a ∈ M) (hb : b ∈ M)
    (hne : rightConjugate J a ≠ rightConjugate J b) {x y : G} (hx : x ∈ J) (hy : y ∈ J) :
    (b⁻¹ * y * b) * (a⁻¹ * x * a) = (a⁻¹ * x * a) * (b⁻¹ * y * b) := by
  have hcomm := c.commutator_conj_conj_eq_bot ha hb hne
  have hxa : a⁻¹ * x * a ∈ rightConjugate J a := by
    rw [mem_rightConjugate_iff]
    have e : a * (a⁻¹ * x * a) * a⁻¹ = x := by group
    rw [e]
    exact hx
  have hyb : b⁻¹ * y * b ∈ rightConjugate J b := by
    rw [mem_rightConjugate_iff]
    have e : b * (b⁻¹ * y * b) * b⁻¹ = y := by group
    rw [e]
    exact hy
  have := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm hxa
  exact Subgroup.mem_centralizer_iff.1 this _ hyb

theorem eq_of_blockU_eq {m : G} (hm : m ∈ M) (h : blockU (rightConjugate J m) = blockU J) :
    rightConjugate J m = J := by
  by_contra hne
  have hcomm := c.commutator_conj_eq_bot hm hne
  rw [Subgroup.commutator_comm] at hcomm
  have hK := c.block.conj m
  have h1 : ⁅blockU (rightConjugate J m), rightConjugate J m⁆ = ⊥ := by
    rw [h, Subgroup.commutator_comm]
    refine le_bot_iff.1 ?_
    calc ⁅rightConjugate J m, blockU J⁆ ≤ ⁅rightConjugate J m, J⁆ :=
          Subgroup.commutator_mono le_rfl (blockU_le J)
      _ = ⊥ := hcomm
  rw [hK.blockU_stable] at h1
  exact blockU_ne_bot_of_short hK.short h1

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
