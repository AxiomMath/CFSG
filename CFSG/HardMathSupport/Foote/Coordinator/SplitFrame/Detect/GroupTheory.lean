module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Components
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Defs

public section

namespace CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect

open Subgroup CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open scoped commutatorElement Pointwise

variable {G : Type*} [Group G]

theorem commutator_sup_le_of_normalizes (T X : Subgroup G)
    (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hN : T ≤ normalizer (X : Set G)) :
    ⁅T ⊔ X, T ⊔ X⁆ ≤ X := by
  have hXN : X ≤ normalizer (X : Set G) := le_normalizer
  have hmem : ∀ a ∈ T ⊔ X, ∃ x ∈ X, ∃ t ∈ T, a = x * t := by
    intro a ha
    have : a ∈ ((X ⊔ T : Subgroup G) : Set G) := by rw [sup_comm]; exact ha
    rw [coe_mul_of_right_le_normalizer_left X T hN] at this
    obtain ⟨x, hx, t, ht, rfl⟩ := this
    exact ⟨x, hx, t, ht, rfl⟩
  rw [commutator_le]
  intro a ha b hb
  obtain ⟨x, hx, t, ht, rfl⟩ := hmem a ha
  obtain ⟨x', hx', t', ht', rfl⟩ := hmem b hb
  have hc : Commute t t' := hT t ht t' ht'
  have hn : ∀ s ∈ T, ∀ y ∈ X, s * y * s⁻¹ ∈ X := fun s hs y hy =>
    (mem_normalizer_iff.1 (hN hs) y).1 hy
  have e : ⁅x * t, x' * t'⁆ = x * (t * x' * t⁻¹) * (t' * x⁻¹ * t'⁻¹) * x'⁻¹ := by
    have e1 : t' * t⁻¹ = t⁻¹ * t' := (hc.inv_left.eq).symm
    rw [commutatorElement_def]
    calc x * t * (x' * t') * (x * t)⁻¹ * (x' * t')⁻¹
        = x * t * x' * (t' * t⁻¹) * x⁻¹ * t'⁻¹ * x'⁻¹ := by group
      _ = x * t * x' * (t⁻¹ * t') * x⁻¹ * t'⁻¹ * x'⁻¹ := by rw [e1]
      _ = x * (t * x' * t⁻¹) * (t' * x⁻¹ * t'⁻¹) * x'⁻¹ := by group
  rw [e]
  exact X.mul_mem (X.mul_mem (X.mul_mem hx (hn t ht x' hx')) (hn t' ht' x⁻¹ (X.inv_mem hx)))
    (X.inv_mem hx')

theorem perfect_subgroup_commutator (X : Subgroup G) (hX : Group.IsPerfect X) : ⁅X, X⁆ = X := by
  have htop : (⊤ : Subgroup X).map X.subtype = X := by
    ext x
    simp
  have h1 : (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆).map X.subtype = ⁅X, X⁆ := by
    rw [Subgroup.map_commutator, htop]
  have h2 : (⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆) = ⊤ := by
    have := hX.commutator_eq_top
    rwa [_root_.commutator_def] at this
  rw [← h1, h2, htop]

theorem normalizes_of_forall_conj_le (H Γ X₁ X₂ T : Subgroup G)
    (hHΓ : H ≤ Γ) (hX₁ : X₁ ≤ H) (hX₂ : X₂ ≤ H)
    (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    (hperf : ⁅X₁, X₁⁆ = X₁) (hqs : CFSG.IsQuasisimple X₂)
    (hTcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (hTN : T ≤ normalizer (X₂ : Set G))
    (hcent : ∀ g ∈ Γ, (∀ x ∈ X₁, g * x = x * g) → g ∈ T ⊔ X₂)
    (hconj : ∀ h ∈ H, conjSub h X₁ ≤ X₁ ⊔ X₂) :
    H ≤ normalizer ((X₁ ⊔ X₂ : Subgroup G) : Set G) := by
  classical
  set X := X₁ ⊔ X₂ with hX
  have hXH : X ≤ H := sup_le hX₁ hX₂
  set N₀ : Subgroup G := ⨆ h : H, conjSub (h : G) X₁ with hN₀
  have hX₁N : X₁ ≤ N₀ := by
    refine le_iSup_of_le ⟨1, H.one_mem⟩ ?_
    simp only [conjSub_one]
    exact le_rfl
  have hN₀X : N₀ ≤ X := iSup_le fun h => hconj h h.2
  have hN₀le : ∀ h ∈ H, conjSub h N₀ ≤ N₀ := by
    intro h hh
    rw [hN₀]
    show (⨆ i : H, conjSub (i : G) X₁).map (MulAut.conj h).toMonoidHom ≤ _
    rw [Subgroup.map_iSup]
    refine iSup_le fun i => ?_
    have e : (conjSub (i : G) X₁).map (MulAut.conj h).toMonoidHom = conjSub (h * (i : G)) X₁ :=
      (conjSub_mul h i X₁).symm
    rw [e]
    exact le_iSup_of_le (⟨h * i, H.mul_mem hh i.2⟩ : H) le_rfl
  have hN₀eq : ∀ h ∈ H, conjSub h N₀ = N₀ := by
    intro h hh
    refine le_antisymm (hN₀le h hh) ?_
    calc N₀ = conjSub h (conjSub h⁻¹ N₀) := (conjSub_conjSub_inv h N₀).symm
      _ ≤ conjSub h N₀ := conjSub_mono h (hN₀le h⁻¹ (H.inv_mem hh))
  set U : Subgroup X₂ := (N₀ ⊓ X₂).subgroupOf X₂ with hU
  haveI hUn : U.Normal := ⟨fun z hz y => by
    rw [hU, Subgroup.mem_subgroupOf] at hz ⊢
    refine ⟨?_, (y * z * y⁻¹ : X₂).2⟩
    have hy : (y : G) ∈ H := hX₂ y.2
    have h1 : (y : G) * (z : G) * (y : G)⁻¹ ∈ conjSub (y : G) N₀ :=
      ⟨(z : G), hz.1, by simp [MulAut.conj_apply]⟩
    rw [hN₀eq _ hy] at h1
    simpa using h1⟩
  have hmulX : (X : Set G) = X₁ * X₂ := by
    have hN : X₂ ≤ normalizer (X₁ : Set G) := fun y hy =>
      mem_normalizer_of_forall_mul_eq fun x hx => (hcomm x hx y hy).symm
    exact coe_mul_of_right_le_normalizer_left X₁ X₂ hN
  rcases le_center_or_eq_top_of_isQuasisimple hqs U with hcen | htop
  ·
    have hZc : ∀ z ∈ N₀ ⊓ X₂, ∀ y ∈ X₂, z * y = y * z := by
      intro z hz y hy
      have hzU : (⟨z, hz.2⟩ : X₂) ∈ U := Subgroup.mem_subgroupOf.2 hz
      have h2 := Subgroup.mem_center_iff.1 (hcen hzU) ⟨y, hy⟩
      exact (congrArg Subtype.val h2).symm
    have hcomN : ⁅N₀, N₀⁆ = X₁ := by
      refine le_antisymm ?_ ?_
      · rw [commutator_le]
        intro n hn n' hn'
        have hnX : n ∈ (X : Set G) := hN₀X hn
        have hnX' : n' ∈ (X : Set G) := hN₀X hn'
        rw [hmulX] at hnX hnX'
        obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hnX
        obtain ⟨x₁', hx₁', x₂', hx₂', rfl⟩ := hnX'
        have hx₂N : x₂ ∈ N₀ := by
          have := N₀.mul_mem (N₀.inv_mem (hX₁N hx₁)) hn
          rwa [inv_mul_cancel_left] at this
        have hx₂N' : x₂' ∈ N₀ := by
          have := N₀.mul_mem (N₀.inv_mem (hX₁N hx₁')) hn'
          rwa [inv_mul_cancel_left] at this
        rw [commutatorElement_mul_eq (Commute.symm (hcomm x₁' hx₁' x₂ hx₂))
          (Commute.symm (hcomm x₁ hx₁ x₂' hx₂')) (hZc x₂ ⟨hx₂N, hx₂⟩ x₂' hx₂')]
        rw [← hperf]
        exact commutator_mem_commutator hx₁ hx₁'
      · rw [← hperf]
        exact commutator_mono hX₁N hX₁N
    have hX₁norm : ∀ h ∈ H, conjSub h X₁ = X₁ := by
      intro h hh
      calc conjSub h X₁ = conjSub h ⁅N₀, N₀⁆ := by rw [hcomN]
        _ = ⁅conjSub h N₀, conjSub h N₀⁆ := Subgroup.map_commutator _ _ _
        _ = ⁅N₀, N₀⁆ := by rw [hN₀eq h hh]
        _ = X₁ := hcomN
    have hX₂perf : ⁅X₂, X₂⁆ = X₂ := perfect_subgroup_commutator X₂ hqs.1
    have hX₂conj : ∀ h ∈ H, conjSub h X₂ ≤ X₂ := by
      intro h hh
      have hY : conjSub h X₂ ≤ T ⊔ X₂ := by
        intro y hy
        refine hcent y (hHΓ ?_) ?_
        · have hy' : h⁻¹ * y * h ∈ X₂ := mem_conjSub_iff.1 hy
          have : y = h * (h⁻¹ * y * h) * h⁻¹ := by group
          rw [this]
          exact H.mul_mem (H.mul_mem hh (hX₂ hy')) (H.inv_mem hh)
        · intro z hz
          have hz' : h⁻¹ * z * h ∈ X₁ := by
            have : z ∈ conjSub h X₁ := by rw [hX₁norm h hh]; exact hz
            exact mem_conjSub_iff.1 this
          have hy' : h⁻¹ * y * h ∈ X₂ := mem_conjSub_iff.1 hy
          have hc := hcomm _ hz' _ hy'
          calc y * z = h * ((h⁻¹ * y * h) * (h⁻¹ * z * h)) * h⁻¹ := by group
            _ = h * ((h⁻¹ * z * h) * (h⁻¹ * y * h)) * h⁻¹ := by rw [← hc]
            _ = z * y := by group
      have hperfY : ⁅conjSub h X₂, conjSub h X₂⁆ = conjSub h X₂ := by
        calc ⁅conjSub h X₂, conjSub h X₂⁆ = conjSub h ⁅X₂, X₂⁆ :=
              (Subgroup.map_commutator _ _ _).symm
          _ = conjSub h X₂ := by rw [hX₂perf]
      calc conjSub h X₂ = ⁅conjSub h X₂, conjSub h X₂⁆ := hperfY.symm
        _ ≤ ⁅T ⊔ X₂, T ⊔ X₂⁆ := commutator_mono hY hY
        _ ≤ X₂ := commutator_sup_le_of_normalizes T X₂ hTcomm hTN
    have hXconj : ∀ h ∈ H, conjSub h X ≤ X := by
      intro h hh
      show conjSub h (X₁ ⊔ X₂) ≤ X₁ ⊔ X₂
      unfold conjSub
      rw [Subgroup.map_sup]
      exact sup_le_sup (le_of_eq (hX₁norm h hh)) (hX₂conj h hh)
    intro h hh
    apply mem_normalizer_of_conjSub_eq
    refine le_antisymm (hXconj h hh) ?_
    calc X = conjSub h (conjSub h⁻¹ X) := (conjSub_conjSub_inv h X).symm
      _ ≤ conjSub h X := conjSub_mono h (hXconj h⁻¹ (H.inv_mem hh))
  ·
    have hX₂N : X₂ ≤ N₀ := by
      intro y hy
      have : (⟨y, hy⟩ : X₂) ∈ U := by rw [htop]; trivial
      exact ((Subgroup.mem_subgroupOf.1 this).1)
    have hNX : N₀ = X := le_antisymm hN₀X (sup_le hX₁N hX₂N)
    intro h hh
    exact mem_normalizer_of_conjSub_eq (by rw [← hNX]; exact hN₀eq h hh)

end CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect
