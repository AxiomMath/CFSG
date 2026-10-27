module

public import CFSG.GH74.Uniqueness.SU.SU2Sem
public import CFSG.GH74.Uniqueness.SU.SU2Struct

public section

open Subgroup Pointwise

namespace CFSG.GH74.Uniqueness.SU.SU2

variable {X : Type} [Group X] {V : Type} [Group V] [MulDistribMulAction X V]

@[expose] def fixElt (t : X) : Subgroup V where
  carrier := {v | t • v = v}
  mul_mem' := fun {a b} ha hb => by
    have ha' : t • a = a := ha
    have hb' : t • b = b := hb
    show t • (a * b) = a * b
    rw [smul_mul', ha', hb']
  one_mem' := smul_one t
  inv_mem' := fun {a} ha => by
    have ha' : t • a = a := ha
    show t • a⁻¹ = a⁻¹
    rw [smul_inv', ha']

@[expose] def actV₁ {Y : Subgroup X} (hGO : GOPair V Y) :
    ↥(MulAction.stabilizer X (fixSub V Y)) →* MulAut ↥(commSub V Y) where
  toFun x :=
    { toFun := fun v => ⟨(x : X) • (v : V),
        hGO.smul_commSub_of_stab (MulAction.mem_stabilizer_iff.1 x.2) v.2⟩
      invFun := fun v => ⟨(x : X)⁻¹ • (v : V),
        hGO.smul_commSub_of_stab (by
          rw [inv_smul_eq_iff]; exact (MulAction.mem_stabilizer_iff.1 x.2).symm) v.2⟩
      left_inv := fun v => Subtype.ext (inv_smul_smul _ _)
      right_inv := fun v => Subtype.ext (smul_inv_smul _ _)
      map_mul' := fun a b => Subtype.ext (smul_mul' _ _ _) }
  map_one' := MulEquiv.ext fun v => Subtype.ext (one_smul _ _)
  map_mul' := fun a b => MulEquiv.ext fun v => Subtype.ext (mul_smul _ _ _)

theorem sem_consequences [Finite X] [Finite V] {Y : Subgroup X} (hGO : GOPair V Y) :
    (∀ t : X, t • fixSub V Y = fixSub V Y → orderOf t = 2 → (∃ u ∈ commSub V Y, t • u ≠ u) →
        Nat.card ↥(commSub V Y ⊓ fixElt t) ^ 2 = Nat.card ↥(commSub V Y)) ∧
    (∀ T : Subgroup X, T ≤ MulAction.stabilizer X (fixSub V Y) → IsPGroup 2 T →
        (∀ t ∈ T, (∀ u ∈ commSub V Y, t • u = u) → t = 1) → IsCyclic T) := by
  classical
  let _ : CommGroup V := hGO.commGroup
  set X₀ := MulAction.stabilizer X (fixSub V Y) with hX₀
  have hYX₀ : Y ≤ X₀ := fun y hy => MulAction.mem_stabilizer_iff.2 (smul_fixSub_of_mem hy)
  have hQ : ∀ q : ↥(commSub V Y), q * q = 1 := fun q => Subtype.ext (hGO.exp_two q)
  let ρ := actV₁ hGO
  have hEn : (Y.subgroupOf X₀).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hGO.normal_in_stab (g : X) (MulAction.mem_stabilizer_iff.1 g.2) (n : X) hn⟩
  have hEc : ∀ a ∈ Y.subgroupOf X₀, ∀ b ∈ Y.subgroupOf X₀, a * b = b * a :=
    fun a ha b hb => Subtype.ext (hGO.comm_Y ha hb)
  have hEtr : ∀ v w : ↥(commSub V Y), v ≠ 1 → w ≠ 1 →
      ∃ x ∈ Y.subgroupOf X₀, ρ x v = w := by
    intro v w hv hw
    obtain ⟨y, hy, hyv⟩ := hGO.transitive (v : V) v.2 (fun h => hv (Subtype.ext h)) (w : V) w.2
      (fun h => hw (Subtype.ext h))
    exact ⟨⟨y, hYX₀ hy⟩, hy, Subtype.ext hyv⟩
  have hEinj : ∀ x ∈ Y.subgroupOf X₀, (∀ v, ρ x v = v) → x = 1 := by
    intro x hx h
    apply Subtype.ext
    apply hGO.faithful
    intro u
    obtain ⟨c, hc, hp⟩ := hGO.exists_decomp u
    obtain ⟨p, hpdef⟩ : ∃ p : V, p = u * c⁻¹ := ⟨_, rfl⟩
    have hp' : p ∈ commSub V Y := hpdef ▸ hp
    have hu : u = p * c := by rw [hpdef]; simp
    have hxp : (x : X) • p = p := congrArg Subtype.val (h ⟨p, hp'⟩)
    rw [hu, smul_mul', hxp, hc (x : X) hx]
  have hEcard : Nat.card ↥(Y.subgroupOf X₀) + 1 = Nat.card ↥(commSub V Y) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX₀).toEquiv]
    exact hGO.card_Y_add_one
  have hQe : Nat.card ↥(commSub V Y) = 2 ^ (shapeN V - shapeK V Y) := hGO.card_commSub
  have he : 1 ≤ shapeN V - shapeK V Y := by
    have h1 : 1 < Nat.card ↥(commSub V Y) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hGO.commSub_ne_bot
    rw [hQe] at h1
    by_contra h0
    have : shapeN V - shapeK V Y = 0 := by omega
    rw [this] at h1
    simp at h1
  refine ⟨fun t ht0 ht hnt => ?_, fun T hT hT2 hfaith => ?_⟩
  · let t' : ↥X₀ := ⟨t, MulAction.mem_stabilizer_iff.2 ht0⟩
    have ht'2 : orderOf t' = 2 := by rw [← Subgroup.orderOf_coe t']; exact ht
    obtain ⟨u, hu, hu'⟩ := hnt
    have hnt' : ∃ v : ↥(commSub V Y), ρ t' v ≠ v :=
      ⟨⟨u, hu⟩, fun h => hu' (congrArg Subtype.val h)⟩
    have key := Sem.card_fixed_sq_of_involution hQ ρ hEc hEtr hEinj hEcard hQe he ht'2 hnt'
    have hcard : Nat.card ↥(commSub V Y ⊓ fixElt t) =
        Nat.card {v : ↥(commSub V Y) // ρ t' v = v} :=
      Nat.card_congr
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, Subtype.ext x.2.2⟩
          invFun := fun v => ⟨v.1.1, v.1.2, congrArg Subtype.val v.2⟩
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl }
    rw [hcard]
    exact key
  · have hT'2 : IsPGroup 2 (T.subgroupOf X₀) :=
      hT2.of_injective (Subgroup.subgroupOfEquivOfLe hT).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hT).injective
    have hfaith' : ∀ t ∈ T.subgroupOf X₀, (∀ v, ρ t v = v) → t = 1 := by
      intro t ht h
      apply Subtype.ext
      exact hfaith (t : X) ht (fun u hu => congrArg Subtype.val (h ⟨u, hu⟩))
    have hcyc : IsCyclic ↥(T.subgroupOf X₀) :=
      Sem.isCyclic_of_isPGroup_faithful hQ ρ hEc hEtr hEinj hEcard hQe he hT'2 hfaith'
    exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hT).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hT).surjective

theorem sem_card_le [Finite X] [Finite V] (hcomm : ∀ a b : V, a * b = b * a)
    (hV : ∀ v : V, v * v = 1) (hfaith : ∀ x : X, (∀ v : V, x • v = v) → x = 1)
    {E : Subgroup X} [E.Normal] (hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hEtr : ∀ v w : V, v ≠ 1 → w ≠ 1 → ∃ x ∈ E, x • v = w)
    (hEcard : Nat.card E + 1 = Nat.card V) {e : ℕ} (hVe : Nat.card V = 2 ^ e) (he : 1 ≤ e) :
    Nat.card X ≤ (2 ^ e - 1) * e := by
  let _ : CommGroup V := { ‹Group V› with mul_comm := hcomm }
  exact Sem.card_le_of_faithful hV (MulDistribMulAction.toMulAut X V) hEc hEtr
    (fun x _ h => hfaith x h) hEcard hVe he (fun x h => hfaith x h)

end CFSG.GH74.Uniqueness.SU.SU2
