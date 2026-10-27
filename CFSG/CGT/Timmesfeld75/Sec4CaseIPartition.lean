module

public import CFSG.CGT.Timmesfeld75.Sec4CaseIComm
public import CFSG.CGT.Timmesfeld75.Sec4TwoBasic

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open
open scoped commutatorElement

@[expose] def Sec4ActsTriv {G : Type} [Group G] (T T₁ T₂ : Subgroup G) (w : G) : Prop :=
  ∀ y ∈ sec4Y T T₁ T₂, ⁅w, y⁆ ∈ sec4N T T₁ T₂

section Triv

variable {G : Type} [Group G] {T T₁ T₂ : Subgroup G} {a : G} {w : G}

theorem Sec4ActsTriv.conj_mem (hw : Sec4ActsTriv T T₁ T₂ w) {m : G}
    (hm : m ∈ sec4N T T₁ T₂) : w * m * w⁻¹ ∈ sec4N T T₁ T₂ := by
  have h1 := hw m (sec4N_le_sec4Y hm)
  have e : w * m * w⁻¹ = ⁅w, m⁆ * m := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (sec4N T T₁ T₂).mul_mem h1 hm

theorem Sec4ActsTriv.conj_eq (hw : Sec4ActsTriv T T₁ T₂ w) {y : G} (hy : y ∈ sec4Y T T₁ T₂) :
    ∃ κ ∈ sec4N T T₁ T₂, w * y * w⁻¹ = κ * y :=
  ⟨⁅w, y⁆, hw y hy, by
    simp only [commutatorElement_def]
    group⟩

variable [Finite G]

omit [Finite G] in
theorem conjSubgroup_le_sec4Y {y : G} (hy : y ∈ sec4Y T T₁ T₂) :
    conjSubgroup y T ≤ sec4Y T T₁ T₂ := fun x hx => by
  have ht : y⁻¹ * x * y ∈ sec4Y T T₁ T₂ := left_le_sec4Y (mem_conjSubgroup.1 hx)
  have e : x = y * (y⁻¹ * x * y) * y⁻¹ := by group
  rw [e]
  exact (sec4Y T T₁ T₂).mul_mem ((sec4Y T T₁ T₂).mul_mem hy ht) ((sec4Y T T₁ T₂).inv_mem hy)

theorem Sec4Hyp.conjSubgroup_eq_of_actsTriv (h : Sec4Hyp T T₁ a T₂)
    (hw : Sec4ActsTriv T T₁ T₂ w) {y : G} (hy : y ∈ sec4Y T T₁ T₂) :
    conjSubgroup w (conjSubgroup y T) = conjSubgroup y T := by
  have hle := conjSubgroup_le_sec4Y (T₁ := T₁) (T₂ := T₂) hy
  have hV : IsPGroup 2 ↥(conjSubgroup y T ⊔ sec4N T T₁ T₂) :=
    (isPGroup_two_of_isElemAbelian
      (isElemAbelian_conjSubgroup h.pair.wc.1 y)).to_sup_of_normal_right'
      h.isPGroup_sec4N (hle.trans h.sec4Y_le_normalizer)
  refine eq_of_conj_le_pGroup (h.pair.wc.conj y) hV le_sup_left ?_
  refine conjSubgroup_le_of_forall_mem fun t ht => ?_
  have e : w * t * w⁻¹ = ⁅w, t⁆ * t := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (conjSubgroup y T ⊔ sec4N T T₁ T₂).mul_mem
    (Subgroup.mem_sup_right (hw t (hle ht))) (Subgroup.mem_sup_left ht)

theorem Sec4Hyp.comm_equivariant (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w) {y m : G}
    (hy : y ∈ sec4Y T T₁ T₂) (hm : m ∈ sec4N T T₁ T₂) :
    w * (y * m * y⁻¹) * w⁻¹ * (y * m * y⁻¹)⁻¹ = y * (w * m * w⁻¹ * m⁻¹) * y⁻¹ := by
  obtain ⟨κ, hκ, hwy⟩ := hw.conj_eq hy
  have hm' : w * m * w⁻¹ ∈ sec4N T T₁ T₂ := hw.conj_mem hm
  have hym : y * (w * m * w⁻¹) * y⁻¹ ∈ sec4N T T₁ T₂ :=
    (Subgroup.mem_normalizer_iff.1 (h.sec4Y_le_normalizer hy) _).1 hm'
  have hc := elemAbelian_mul_comm h.isElemAbelian_sec4N hκ hym
  have e1 : w * (y * m * y⁻¹) * w⁻¹ = (w * y * w⁻¹) * (w * m * w⁻¹) * (w * y * w⁻¹)⁻¹ := by group
  rw [e1, hwy]
  calc κ * y * (w * m * w⁻¹) * (κ * y)⁻¹ * (y * m * y⁻¹)⁻¹
      = κ * (y * (w * m * w⁻¹) * y⁻¹) * κ⁻¹ * (y * m * y⁻¹)⁻¹ := by group
    _ = (y * (w * m * w⁻¹) * y⁻¹) * κ * κ⁻¹ * (y * m * y⁻¹)⁻¹ := by rw [hc]
    _ = y * (w * m * w⁻¹ * m⁻¹) * y⁻¹ := by group

end Triv

section Nu

variable {G : Type} [Group G] [Finite G] {T T₁ T₂ : Subgroup G} {a w : G}

@[expose] def sec4Nu (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w) :
    ↥(sec4N T T₁ T₂) →* ↥(sec4N T T₁ T₂) :=
  normCommHom (sec4N T T₁ T₂) w
    (fun _ hm _ hm' => elemAbelian_mul_comm h.isElemAbelian_sec4N hm hm')
    (fun _ hm => hw.conj_mem hm)

theorem coe_sec4Nu (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w) (m : ↥(sec4N T T₁ T₂)) :
    ((sec4Nu h hw m : ↥(sec4N T T₁ T₂)) : G) = w * m * w⁻¹ * (m : G)⁻¹ :=
  rfl

@[expose] def sec4Psi (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w) (U : Subgroup G) :
    Subgroup ↥(sec4N T T₁ T₂) :=
  ((U ⊓ sec4N T T₁ T₂).subgroupOf (sec4N T T₁ T₂)).map (sec4Nu h hw)

theorem sec4Psi_le (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w) {U : Subgroup G}
    (hU : conjSubgroup w U = U) :
    sec4Psi h hw U ≤ (U ⊓ sec4N T T₁ T₂).subgroupOf (sec4N T T₁ T₂) := by
  rintro _ ⟨m, hm, rfl⟩
  have hmU : (m : G) ∈ U := (Subgroup.mem_subgroupOf.1 hm).1
  have h1 : w * (m : G) * w⁻¹ ∈ U := by
    have : w * (m : G) * w⁻¹ ∈ conjSubgroup w U := ⟨m, hmU, by simp [MulAut.conj_apply]⟩
    rwa [hU] at this
  refine Subgroup.mem_subgroupOf.2 ⟨?_, (sec4Nu h hw m).2⟩
  rw [coe_sec4Nu]
  exact U.mul_mem h1 (U.inv_mem hmU)

theorem sec4Psi_inf_eq_bot (h : Sec4Hyp T T₁ a T₂) (hw : Sec4ActsTriv T T₁ T₂ w)
    {U U' : Subgroup G} (hU : conjSubgroup w U = U) (hU' : conjSubgroup w U' = U')
    (hUU' : U ⊓ U' = ⊥) : sec4Psi h hw U ⊓ sec4Psi h hw U' = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 := sec4Psi_le h hw hU hx.1
  have h2 := sec4Psi_le h hw hU' hx.2
  have h3 : (x : G) ∈ U ⊓ U' := ⟨(Subgroup.mem_subgroupOf.1 h1).1,
    (Subgroup.mem_subgroupOf.1 h2).1⟩
  rw [hUU', Subgroup.mem_bot] at h3
  exact (Subgroup.mem_bot).2 (Subtype.ext h3)

end Nu

end CFSG.CGT.Timmesfeld75
