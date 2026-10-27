module

public import Mathlib.Data.Finset.Card

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

section Graph

variable {V : Type*}

@[expose] def closedNbhd (adj : V → V → Prop) (v : V) : Set V := {u | u = v ∨ adj u v}

@[expose] def outerNbhd (adj : V → V → Prop) (v : V) : Set V :=
  {u | u ∈ closedNbhd adj v ∧ closedNbhd adj u ≠ closedNbhd adj v}

variable {adj : V → V → Prop}

theorem mem_closedNbhd_comm (hsymm : ∀ u v, adj u v → adj v u) {u v : V} :
    u ∈ closedNbhd adj v ↔ v ∈ closedNbhd adj u := by
  constructor
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (hsymm _ _ h)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr (hsymm _ _ h)

theorem self_mem_closedNbhd (v : V) : v ∈ closedNbhd adj v := Or.inl rfl

theorem adj_of_twin {u v w : V} (hu : closedNbhd adj u = closedNbhd adj v)
    (hw : w ∈ closedNbhd adj v) (hne : w ≠ u) : adj w u := by
  have h : w ∈ closedNbhd adj u := hu ▸ hw
  rcases h with h | h
  · exact absurd h hne
  · exact h

theorem card_three_cases {s : Finset V} (hs : s.card = 3) {v : V} (hv : v ∈ s) :
    ∃ x y : V, x ≠ y ∧ x ≠ v ∧ y ≠ v ∧ ∀ u, u ∈ s ↔ (u = v ∨ u = x ∨ u = y) := by
  classical
  have h2 : (s.erase v).card = 2 := by rw [Finset.card_erase_of_mem hv, hs]
  obtain ⟨x, y, hxy, hxy'⟩ := Finset.card_eq_two.mp h2
  have hx : x ∈ s.erase v := by rw [hxy']; simp
  have hy : y ∈ s.erase v := by rw [hxy']; simp
  refine ⟨x, y, hxy, (Finset.mem_erase.mp hx).1, (Finset.mem_erase.mp hy).1, fun u => ?_⟩
  constructor
  · intro hu
    by_cases huv : u = v
    · exact Or.inl huv
    · have : u ∈ s.erase v := Finset.mem_erase.mpr ⟨huv, hu⟩
      rw [hxy'] at this
      simpa using Or.inr this
  · rintro (rfl | rfl | rfl)
    · exact hv
    · exact (Finset.mem_erase.mp hx).2
    · exact (Finset.mem_erase.mp hy).2

end Graph

section Four

variable {F : Type*}

@[expose] def CliqueFour (fadj : F → F → Prop) : Prop :=
  ∀ F₁ F₂ F₃ : F, F₁ ≠ F₂ → F₁ ≠ F₃ → F₂ ≠ F₃ → fadj F₁ F₂ → fadj F₁ F₃ → fadj F₂ F₃ →
    ∃ F₄ : F, F₄ ≠ F₁ ∧ F₄ ≠ F₂ ∧ F₄ ≠ F₃ ∧ fadj F₁ F₄ ∧ fadj F₂ F₄ ∧ fadj F₃ F₄ ∧
      ∀ F' : F, fadj F₁ F' → F' = F₂ ∨ F' = F₃ ∨ F' = F₄

end Four

section Main

variable {V : Type*} {adj : V → V → Prop}

theorem false_of_three_twins [Nonempty V] (hsymm : ∀ u v, adj u v → adj v u)
    (htw : ∀ v, ∃ s : Finset V, s.card = 3 ∧ ∀ u, u ∈ s ↔ closedNbhd adj u = closedNbhd adj v)
    (hloc : ∀ v, ∃ (F : Type) (fadj : F → F → Prop), CliqueFour fadj ∧ Nonempty F ∧
      ∃ e : ↥(outerNbhd adj v) ≃ F, ∀ u u' : ↥(outerNbhd adj v), u ≠ u' →
        (adj u.1 u'.1 ↔ fadj (e u) (e u'))) : False := by
  classical
  obtain ⟨K⟩ := ‹Nonempty V›
  obtain ⟨FK, fadjK, hBK, ⟨f₀⟩, eK, heK⟩ := hloc K
  set aM : ↥(outerNbhd adj K) := eK.symm f₀ with haM
  set M : V := aM.1 with hM
  have hMmem : M ∈ closedNbhd adj K := aM.2.1
  have hMne : closedNbhd adj M ≠ closedNbhd adj K := aM.2.2
  have hKM : K ∈ closedNbhd adj M := (mem_closedNbhd_comm hsymm).mp hMmem
  have hKY : K ∈ outerNbhd adj M := ⟨hKM, fun h => hMne h.symm⟩
  obtain ⟨FM, fadjM, hBM, -, eM, heM⟩ := hloc M
  obtain ⟨sK, hsK, hsKm⟩ := htw K
  have hKsK : K ∈ sK := (hsKm K).mpr rfl
  obtain ⟨T₂, T₃, h23, h2K, h3K, hsKc⟩ := card_three_cases hsK hKsK
  have hT : ∀ T, closedNbhd adj T = closedNbhd adj K → T ∈ outerNbhd adj M := by
    intro T hT
    refine ⟨(mem_closedNbhd_comm hsymm).mp (hT ▸ hMmem), ?_⟩
    rw [hT]
    exact fun h => hMne h.symm
  have hT2 : closedNbhd adj T₂ = closedNbhd adj K :=
    (hsKm T₂).mp ((hsKc T₂).mpr (Or.inr (Or.inl rfl)))
  have hT3 : closedNbhd adj T₃ = closedNbhd adj K :=
    (hsKm T₃).mp ((hsKc T₃).mpr (Or.inr (Or.inr rfl)))
  have adj_K2 : adj K T₂ := by
    have : K ∈ closedNbhd adj T₂ := by rw [hT2]; exact self_mem_closedNbhd K
    rcases this with h | h
    · exact absurd h.symm h2K
    · exact h
  have adj_K3 : adj K T₃ := by
    have : K ∈ closedNbhd adj T₃ := by rw [hT3]; exact self_mem_closedNbhd K
    rcases this with h | h
    · exact absurd h.symm h3K
    · exact h
  have adj_23 : adj T₂ T₃ := by
    have : T₃ ∈ closedNbhd adj T₂ := by
      rw [hT2, ← hT3]; exact self_mem_closedNbhd T₃
    rcases this with h | h
    · exact absurd h.symm h23
    · exact hsymm _ _ h
  set a₁ : ↥(outerNbhd adj M) := ⟨K, hKY⟩ with ha₁
  set a₂ : ↥(outerNbhd adj M) := ⟨T₂, hT T₂ hT2⟩ with ha₂
  set a₃ : ↥(outerNbhd adj M) := ⟨T₃, hT T₃ hT3⟩ with ha₃
  have n12 : a₁ ≠ a₂ := fun h => h2K (congrArg Subtype.val h).symm
  have n13 : a₁ ≠ a₃ := fun h => h3K (congrArg Subtype.val h).symm
  have n23 : a₂ ≠ a₃ := fun h => h23 (congrArg Subtype.val h)
  obtain ⟨F₄, h41, h42, h43, f14, f24, f34, hnb⟩ := hBM (eM a₁) (eM a₂) (eM a₃)
    (eM.injective.ne n12) (eM.injective.ne n13) (eM.injective.ne n23)
    ((heM a₁ a₂ n12).mp adj_K2) ((heM a₁ a₃ n13).mp adj_K3) ((heM a₂ a₃ n23).mp adj_23)
  set aν : ↥(outerNbhd adj M) := eM.symm F₄ with haν
  set ν : V := aν.1 with hν
  have hνeq : eM aν = F₄ := eM.apply_symm_apply F₄
  have hνM : closedNbhd adj ν ≠ closedNbhd adj M := aν.2.2
  have hνMmem : ν ∈ closedNbhd adj M := aν.2.1
  have nν1 : a₁ ≠ aν := fun h => h41 (by rw [← hνeq, ← h])
  have hνK : adj K ν := (heM a₁ aν nν1).mpr (by rw [hνeq]; exact f14)
  have hνK_ne : ν ≠ K := fun h => nν1 (Subtype.ext h.symm)
  have hνT2 : ν ≠ T₂ := fun h => h42 (by rw [← hνeq, ha₂]; exact congrArg eM (Subtype.ext h))
  have hνT3 : ν ≠ T₃ := fun h => h43 (by rw [← hνeq, ha₃]; exact congrArg eM (Subtype.ext h))
  have hνKY : ν ∈ outerNbhd adj K := by
    refine ⟨(mem_closedNbhd_comm hsymm).mpr (Or.inr hνK), fun h => ?_⟩
    have := (hsKm ν).mpr h
    rcases (hsKc ν).mp this with h' | h' | h'
    · exact hνK_ne h'
    · exact hνT2 h'
    · exact hνT3 h'
  obtain ⟨sM, hsM, hsMm⟩ := htw M
  have hMsM : M ∈ sM := (hsMm M).mpr rfl
  obtain ⟨M₂, M₃, h23', h2M, h3M, hsMc⟩ := card_three_cases hsM hMsM
  have hM2 : closedNbhd adj M₂ = closedNbhd adj M :=
    (hsMm M₂).mp ((hsMc M₂).mpr (Or.inr (Or.inl rfl)))
  have hM3 : closedNbhd adj M₃ = closedNbhd adj M :=
    (hsMm M₃).mp ((hsMc M₃).mpr (Or.inr (Or.inr rfl)))
  have hMY : ∀ w, closedNbhd adj w = closedNbhd adj M → w ∈ outerNbhd adj K := by
    intro w hw
    refine ⟨(mem_closedNbhd_comm hsymm).mpr (hw ▸ hKM), fun h => hMne ?_⟩
    rw [← hw, h]
  have hνw : ∀ w, closedNbhd adj w = closedNbhd adj M → adj ν w := by
    intro w hw
    have hne : ν ≠ w := fun h => hνM (by rw [h, hw])
    exact adj_of_twin hw hνMmem hne
  have hνM₂ := hνw M₂ hM2
  have hνM₃ := hνw M₃ hM3
  have hνM₁ : adj ν M := hνw M rfl
  have adj_M12 : adj M M₂ := by
    have : M ∈ closedNbhd adj M₂ := by rw [hM2]; exact self_mem_closedNbhd M
    rcases this with h | h
    · exact absurd h.symm h2M
    · exact h
  have adj_M13 : adj M M₃ := by
    have : M ∈ closedNbhd adj M₃ := by rw [hM3]; exact self_mem_closedNbhd M
    rcases this with h | h
    · exact absurd h.symm h3M
    · exact h
  set b₀ : ↥(outerNbhd adj K) := ⟨ν, hνKY⟩ with hb₀
  set b₁ : ↥(outerNbhd adj K) := ⟨M, hMY M rfl⟩ with hb₁
  set b₂ : ↥(outerNbhd adj K) := ⟨M₂, hMY M₂ hM2⟩ with hb₂
  set b₃ : ↥(outerNbhd adj K) := ⟨M₃, hMY M₃ hM3⟩ with hb₃
  have νM : ν ≠ M := fun h => hνM (by rw [h])
  have νM2 : ν ≠ M₂ := fun h => hνM (by rw [h, hM2])
  have νM3 : ν ≠ M₃ := fun h => hνM (by rw [h, hM3])
  have m01 : b₀ ≠ b₁ := fun h => νM (congrArg Subtype.val h)
  have m02 : b₀ ≠ b₂ := fun h => νM2 (congrArg Subtype.val h)
  have m03 : b₀ ≠ b₃ := fun h => νM3 (congrArg Subtype.val h)
  have m12 : b₁ ≠ b₂ := fun h => h2M (congrArg Subtype.val h).symm
  have m13 : b₁ ≠ b₃ := fun h => h3M (congrArg Subtype.val h).symm
  have m23 : b₂ ≠ b₃ := fun h => h23' (congrArg Subtype.val h)
  have adj_M23 : adj M₂ M₃ := by
    have : M₂ ∈ closedNbhd adj M₃ := by rw [hM3, ← hM2]; exact self_mem_closedNbhd M₂
    rcases this with h | h
    · exact absurd h h23'
    · exact h
  obtain ⟨G₄, -, -, -, -, -, -, hnb'⟩ := hBK (eK b₀) (eK b₁) (eK b₂)
    (eK.injective.ne m01) (eK.injective.ne m02) (eK.injective.ne m12)
    ((heK b₀ b₁ m01).mp hνM₁) ((heK b₀ b₂ m02).mp hνM₂) ((heK b₁ b₂ m12).mp adj_M12)
  have hb3 : eK b₃ = G₄ := by
    rcases hnb' (eK b₃) ((heK b₀ b₃ m03).mp hνM₃) with h | h | h
    · exact absurd (eK.injective h) m13.symm
    · exact absurd (eK.injective h) m23.symm
    · exact h
  obtain ⟨sν, hsν, hsνm⟩ := htw ν
  have hνsν : ν ∈ sν := (hsνm ν).mpr rfl
  obtain ⟨ν₂, ν₃, -, hν2ν, -, hsνc⟩ := card_three_cases hsν hνsν
  have hν2 : closedNbhd adj ν₂ = closedNbhd adj ν :=
    (hsνm ν₂).mp ((hsνc ν₂).mpr (Or.inr (Or.inl rfl)))
  have hν2Y : ν₂ ∈ outerNbhd adj K := by
    refine ⟨?_, fun h => hνKY.2 (hν2.symm.trans h)⟩
    have hKν : K ∈ closedNbhd adj ν := (mem_closedNbhd_comm hsymm).mp hνKY.1
    have hKν2 : K ∈ closedNbhd adj ν₂ := by rw [hν2]; exact hKν
    exact (mem_closedNbhd_comm hsymm).mpr hKν2
  have adj_νν2 : adj ν ν₂ := adj_of_twin hν2 (self_mem_closedNbhd ν) (Ne.symm hν2ν)
  set b₄ : ↥(outerNbhd adj K) := ⟨ν₂, hν2Y⟩ with hb₄
  have m04 : b₀ ≠ b₄ := fun h => hν2ν (congrArg Subtype.val h).symm
  rcases hnb' (eK b₄) ((heK b₀ b₄ m04).mp adj_νν2) with h | h | h
  ·
    have hv : ν₂ = M := congrArg Subtype.val (eK.injective h)
    exact hνM (by rw [← hν2, hv])
  · have hv : ν₂ = M₂ := congrArg Subtype.val (eK.injective h)
    exact hνM (by rw [← hν2, hv, hM2])
  · have hv : ν₂ = M₃ := congrArg Subtype.val (eK.injective (h.trans hb3.symm))
    exact hνM (by rw [← hν2, hv, hM3])

end Main

end CFSG.ClassicalInvolution.RouteD.Exotic
