module

public import CFSG.ClassicalInvolution.Q3.TL4D1Pack
public import CFSG.ClassicalInvolution.Q3.TL4D1Sub

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isComponent_map_pCore {X : Subgroup G} (hX : X.IsSubnormal) (pX : D1Pack X) :
    IsComponent (X.map (QuotientGroup.mk' (pCore 2 G))) := by
  set Q := pCore 2 G with hQ
  set π := QuotientGroup.mk' Q with hπ
  set Xb := X.map π with hXb
  have hker : ∀ g : G, π g = 1 ↔ g ∈ Q := fun g => QuotientGroup.eq_one_iff g
  have hne : Nontrivial ↥Xb := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply pX.not_two
    have hle : X ≤ Q := fun x hx => by
      have : (⟨π x, ⟨x, hx, rfl⟩⟩ : ↥Xb) = 1 := Subsingleton.elim _ _
      exact (hker x).mp (congrArg Subtype.val this)
    exact pCore_isPGroup.to_le hle
  have hsimple : IsSimpleGroup ↥Xb := by
    refine { toNontrivial := hne, eq_bot_or_eq_top_of_normal := fun N' hN' => ?_ }
    set N : Subgroup G := X ⊓ (N'.map Xb.subtype).comap π with hN
    have hNX : N ≤ X := inf_le_left
    have hNn : ∀ x ∈ X, ∀ y ∈ N, x * y * x⁻¹ ∈ N := by
      rintro x hx y ⟨hyX, ⟨n, hn, hneq⟩⟩
      refine ⟨X.mul_mem (X.mul_mem hx hyX) (X.inv_mem hx), ?_⟩
      have hxb : π x ∈ Xb := ⟨x, hx, rfl⟩
      refine ⟨⟨π x, hxb⟩ * n * ⟨π x, hxb⟩⁻¹, hN'.conj_mem n hn _, ?_⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype] at hneq ⊢
      rw [hneq, map_mul, map_mul, map_inv]
    rcases pX.normal N hNX hNn with h2 | heq
    · left
      have hNs : N.IsSubnormal :=
        Subgroup.IsSubnormal.step N X hNX hX
          ((Subgroup.normal_subgroupOf_iff hNX).mpr fun y k hy hk => hNn k hk y hy)
      have hNQ : N ≤ Q := le_pCore_of_isSubnormal hNs le_rfl
        (fun w hw x hx => N.mul_mem (N.mul_mem hw hx) (N.inv_mem hw)) h2
      rw [eq_bot_iff]
      rintro ⟨_, ⟨x, hx, rfl⟩⟩ hxN'
      have hxN : x ∈ N := ⟨hx, ⟨_, hxN', rfl⟩⟩
      exact Subgroup.mem_bot.mpr (Subtype.ext ((hker x).mpr (hNQ hxN)))
    · right
      rw [eq_top_iff]
      rintro ⟨_, ⟨x, hx, rfl⟩⟩ -
      have hxN : x ∈ N := by rw [heq]; exact hx
      obtain ⟨-, n, hn, hneq⟩ := hxN
      have : n = ⟨π x, ⟨x, hx, rfl⟩⟩ := Subtype.ext hneq
      rw [← this]
      exact hn
  have hnab : ∃ a b : ↥Xb, a * b ≠ b * a := by
    by_contra hab
    push Not at hab
    have hcomm : ⁅Xb, Xb⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b hb
      have := hab ⟨a, ha⟩ ⟨b, hb⟩
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact congrArg Subtype.val this
    have hbot : Xb = ⊥ := by
      rw [← hcomm, hXb, ← Subgroup.map_commutator, pX.perfect]
    exact (Subgroup.nontrivial_iff_ne_bot Xb).mp hne hbot
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1,
    hX.map (QuotientGroup.mk'_surjective Q)⟩

theorem eq_or_comm_mem_pCore {X Y : Subgroup G} (hX : X.IsSubnormal) (hY : Y.IsSubnormal)
    (pX : D1Pack X) (pY : D1Pack Y) :
    X = Y ∨ ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ * y⁻¹ ∈ pCore 2 G := by
  set Q := pCore 2 G with hQ
  set π := QuotientGroup.mk' Q with hπ
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_map_pCore hX pX)
    (isComponent_map_pCore hY pY) with h | h
  · left
    have hXY : X ⊔ Q = Y ⊔ Q := by
      have h1 := congrArg (Subgroup.comap π) h
      rwa [Subgroup.comap_map_eq, Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h1
    have key : ∀ {A B : Subgroup G}, A.IsSubnormal → D1Pack B → B ≤ A ⊔ Q → B ≤ A := by
      intro A B hA pB hBA
      refine pB.odd.trans ((Subgroup.closure_le _).mpr ?_)
      rintro g ⟨hgB, hgo⟩
      exact mem_of_odd_of_mem_sup hA pCore_normal pCore_isPGroup (hBA hgB) hgo
    exact le_antisymm (key hY pX (le_sup_left.trans hXY.le))
      (key hX pY (le_sup_left.trans hXY.ge))
  · right
    intro x hx y hy
    have hc : π (x * y * x⁻¹ * y⁻¹) ∈ ⁅X.map π, Y.map π⁆ := by
      have := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π hx)
        (Subgroup.mem_map_of_mem π hy)
      rw [commutatorElement_def] at this
      simpa only [map_mul, map_inv] using this
    rw [h, Subgroup.mem_bot] at hc
    exact (QuotientGroup.eq_one_iff _).mp hc

end CFSG.ClassicalInvolution.Q3.TL4
