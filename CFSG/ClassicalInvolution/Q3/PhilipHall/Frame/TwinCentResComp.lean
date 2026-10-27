module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtxSecOddFree

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TL4
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinVtx
open scoped commutatorElement

section Basic

variable {H Q : Type} [Group H] [Finite H] [Group Q] [IsSimpleGroup Q]

theorem component_map_eq_top (f : H →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    {L : Subgroup H} (hL : CFSG.IsComponent L) : L.map f = ⊤ := by
  have hsub : (L.map f).IsSubnormal := hL.2.map hf
  rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup (inferInstance : IsSimpleGroup Q)
    hsub with h | h
  · exfalso
    have hle : L ≤ f.ker := by
      rw [Subgroup.map_eq_bot_iff] at h
      exact h
    have h2 : IsPGroup 2 ↥L := hk.to_le hle
    have : Nontrivial ↥L := CFSG.LocalCores.isQuasisimple_nontrivial hL.1
    have : Group.IsPerfect ↥L := hL.1.1
    have : Group.IsNilpotent ↥L := h2.isNilpotent
    exact Group.IsPerfect.not_isSolvable ↥L inferInstance
  · exact h

theorem nonabelian_of_component (f : H →* Q) (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    {L : Subgroup H} (hL : CFSG.IsComponent L) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra hcon
  push Not at hcon
  have hLtop := component_map_eq_top f hf hk hL
  have : Group.IsPerfect ↥L := hL.1.1
  have hψs : Function.Surjective (f.comp L.subtype) := by
    intro q
    have : q ∈ L.map f := by rw [hLtop]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hpQ : Group.IsPerfect Q := Q3NM.isPerfect_of_surjective _ hψs
  have hnt : (⊤ : Subgroup Q) ≠ ⊥ := by
    intro h
    have := IsSimpleGroup.toNontrivial (G := Q)
    obtain ⟨x, hx⟩ := exists_ne (1 : Q)
    exact hx (Subgroup.mem_bot.mp (h ▸ Subgroup.mem_top x))
  apply hnt
  have hcomm : ⁅(⊤ : Subgroup Q), ⊤⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x _ y _ => (hcon y x)
  rw [← hcomm]
  have h1 := Group.isPerfect_def.mp hpQ
  rw [_root_.commutator_def] at h1
  exact h1.symm

theorem component_eq_of_surj_simple (f : H →* Q)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) {L₁ L₂ : Subgroup H}
    (h₁ : CFSG.IsComponent L₁) (h₂ : CFSG.IsComponent L₂) : L₁ = L₂ := by
  rcases CFSG.LocalCores.distinct_components_commute h₁ h₂ with h | h
  · exact h
  · exfalso
    have e1 := component_map_eq_top f hf hk h₁
    have e2 := component_map_eq_top f hf hk h₂
    obtain ⟨a, b, hab⟩ := nonabelian_of_component f hf hk h₁
    apply hab
    have ha : a ∈ L₁.map f := by rw [e1]; trivial
    have hb : b ∈ L₂.map f := by rw [e2]; trivial
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := hb
    have hc : ⁅x, y⁆ ∈ ⁅L₁, L₂⁆ := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
    rw [← map_mul, ← map_mul, hc]

theorem center_eq_bot_of_nonabelian (hnab : ∃ a b : Q, a * b ≠ b * a) :
    Subgroup.center Q = ⊥ := by
  rcases (Subgroup.center Q).normal_of_characteristic.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    have ha : a ∈ Subgroup.center Q := h ▸ Subgroup.mem_top a
    exact hab ((Subgroup.mem_center_iff.mp ha b).symm)

theorem exists_centerQuot_equiv (f : H →* Q)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) {L : Subgroup H}
    (hL : CFSG.IsComponent L) : Nonempty (↥L ⧸ Subgroup.center ↥L ≃* Q ⧸ Subgroup.center Q) := by
  have hLtop := component_map_eq_top f hf hk hL
  set ψ : ↥L →* Q := f.comp L.subtype with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    have : q ∈ L.map f := by rw [hLtop]; trivial
    obtain ⟨x, hx, rfl⟩ := this
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ψ.ker ≤ Subgroup.center ↥L := by
    have hn : ψ.ker.Normal := inferInstance
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hL.1 hn with h | h
    · exfalso
      have hz : ∀ x : ↥L, ψ x = 1 := fun x => by
        have : x ∈ ψ.ker := h ▸ Subgroup.mem_top x
        exact this
      obtain ⟨a, b, hab⟩ := nonabelian_of_component f hf hk hL
      obtain ⟨x, rfl⟩ := hψs a
      obtain ⟨y, rfl⟩ := hψs b
      apply hab
      rw [hz x, hz y]
    · exact h
  have : Group.IsPerfect ↥L := hL.1.1
  exact ⟨Q3NM.centralQuotientIso ψ hψs hker⟩

theorem autOddFree_component_of_surj (f : H →* Q)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker) {L : Subgroup H}
    (hL : CFSG.IsComponent L) (hQ : (∃ a b : Q, a * b ≠ b * a) → Q3NM.AutOddFree Q) :
    Q3NM.AutOddFree ↥L := by
  obtain ⟨e⟩ := exists_centerQuot_equiv f hf hk hL
  have hfin : Finite Q := Finite.of_surjective f hf
  have : Group.IsPerfect ↥L := hL.1.1
  have hc : Subgroup.center Q = ⊥ :=
    center_eq_bot_of_nonabelian (nonabelian_of_component f hf hk hL)
  have e0 : Q ≃* Q ⧸ Subgroup.center Q :=
    (QuotientGroup.quotientBot (G := Q)).symm.trans
      (QuotientGroup.quotientMulEquivOfEq hc.symm)
  have hQ' : Q3NM.AutOddFree (Q ⧸ Subgroup.center Q) :=
    Q3NM.AutOddFree.of_mulEquiv e0 (hQ (nonabelian_of_component f hf hk hL))
  have hfin' : Finite (Q ⧸ Subgroup.center Q) := inferInstance
  have hLQ : Q3NM.AutOddFree (↥L ⧸ Subgroup.center ↥L) := Q3NM.AutOddFree.of_mulEquiv e.symm hQ'
  exact Q3NM.autOddFree_of_centralQuotient hLQ

theorem atMostOne_oddFree_of_surj_simple (f : H →* Q)
    (hf : Function.Surjective f) (hk : IsPGroup 2 f.ker)
    (hQ : (∃ a b : Q, a * b ≠ b * a) → Q3NM.AutOddFree Q) (x : H) :
    (∀ L₁ L₂ : Subgroup H, CFSG.IsComponent L₁ → CFSG.IsComponent L₂ →
      (∃ y ∈ L₁, x * y ≠ y * x) → (∃ y ∈ L₂, x * y ≠ y * x) → L₁ = L₂) ∧
    ∀ L : Subgroup H, CFSG.IsComponent L → x ∈ Subgroup.normalizer (L : Set H) →
      (∃ y ∈ L, x * y ≠ y * x) → Q3NM.AutOddFreeOn ↥L (IsInducedAut L x) :=
  ⟨fun _ _ h₁ h₂ _ _ => component_eq_of_surj_simple f hf hk h₁ h₂,
    fun _ hL _ _ => (autOddFree_component_of_surj f hf hk hL hQ).on _⟩

end Basic

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinCentRes
