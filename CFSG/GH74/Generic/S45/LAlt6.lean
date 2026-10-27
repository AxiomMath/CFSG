module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.GH74.Generic.S45.LAlt

section Coset

variable {G : Type*} [Group G] (L : Subgroup G)

theorem symm_apply_of_fix {α : MulAut G} (hfix : ∀ l ∈ L, α l = l) {l : G} (hl : l ∈ L) :
    α.symm l = l :=
  (MulEquiv.symm_apply_eq α).2 (hfix l hl).symm

@[expose] def cosetPerm (α : MulAut G) (hfix : ∀ l ∈ L, α l = l) : Equiv.Perm (G ⧸ L) where
  toFun := Quotient.map' α fun a b h => QuotientGroup.leftRel_apply.mpr <| by
    have h' : a⁻¹ * b ∈ L := QuotientGroup.leftRel_apply.mp h
    have e : (α a)⁻¹ * α b = a⁻¹ * b := by
      rw [← map_inv α a, ← map_mul α]
      exact hfix _ h'
    rw [e]
    exact h'
  invFun := Quotient.map' α.symm fun a b h => QuotientGroup.leftRel_apply.mpr <| by
    have h' : a⁻¹ * b ∈ L := QuotientGroup.leftRel_apply.mp h
    have e : (α.symm a)⁻¹ * α.symm b = a⁻¹ * b := by
      rw [← map_inv α.symm a, ← map_mul α.symm]
      exact symm_apply_of_fix L hfix h'
    rw [e]
    exact h'
  left_inv q := QuotientGroup.induction_on q fun g => by
    show (QuotientGroup.mk (α.symm (α g)) : G ⧸ L) = QuotientGroup.mk g
    rw [MulEquiv.symm_apply_apply]
  right_inv q := QuotientGroup.induction_on q fun g => by
    show (QuotientGroup.mk (α (α.symm g)) : G ⧸ L) = QuotientGroup.mk g
    rw [MulEquiv.apply_symm_apply]

theorem cosetPerm_mk (α : MulAut G) (hfix : ∀ l ∈ L, α l = l) (g : G) :
    cosetPerm L α hfix (QuotientGroup.mk g) = QuotientGroup.mk (α g) :=
  rfl

theorem cosetPerm_smul (α : MulAut G) (hfix : ∀ l ∈ L, α l = l) (g : G) (x : G ⧸ L) :
    cosetPerm L α hfix (g • x) = α g • cosetPerm L α hfix x := by
  refine QuotientGroup.induction_on x fun h => ?_
  show (QuotientGroup.mk (α (g * h)) : G ⧸ L) = QuotientGroup.mk (α g * α h)
  rw [map_mul α g h]

end Coset

theorem perm_eq_one_of_commute {X : Type*} [Fintype X] [DecidableEq X] (hX : Fintype.card X = 6)
    (b : X) (π : Equiv.Perm X) (hb : π b = b)
    (hc : ∀ x y z : X, x ≠ y → x ≠ z → y ≠ z → x ≠ b → y ≠ b → z ≠ b →
      π * (Equiv.swap x y * Equiv.swap x z) = (Equiv.swap x y * Equiv.swap x z) * π) :
    π = 1 := by
  refine Equiv.ext fun x => ?_
  show π x = x
  by_cases hxb : x = b
  · rw [hxb]
    exact hb
  by_contra hne
  have hcard : 1 < (Finset.univ \ ({b, x, π x} : Finset X)).card := by
    have h1 : (Finset.univ : Finset X).card = 6 := by rw [Finset.card_univ, hX]
    have h2 := Finset.le_card_sdiff ({b, x, π x} : Finset X) Finset.univ
    have h3 : ({b, x, π x} : Finset X).card ≤ 3 := Finset.card_le_three
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.1 hcard
  simp only [Finset.mem_sdiff, Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton,
    true_and, not_or] at hy hz
  obtain ⟨hyb, hyx, hyw⟩ := hy
  obtain ⟨hzb, hzx, hzw⟩ := hz
  have h := congrArg (fun p : Equiv.Perm X => p x)
    (hc x y z (Ne.symm hyx) (Ne.symm hzx) hyz hxb hyb hzb)
  simp only [Equiv.Perm.mul_apply] at h
  rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hzx (Ne.symm hyz),
    Equiv.swap_apply_of_ne_of_ne hne (Ne.symm hzw),
    Equiv.swap_apply_of_ne_of_ne hne (Ne.symm hyw)] at h
  exact hzx (π.injective h)

theorem aut_eq_one_of_fixes_index_six {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : Nat.card G = 360) (α : MulAut G) (L : Subgroup G) (hL : Nat.card L = 60)
    (hfix : ∀ l ∈ L, α l = l) : α = 1 := by
  classical
  have hidx : L.index = 6 := by
    have h := Subgroup.index_mul_card L
    rw [hL, hG] at h
    omega
  have hX : Nat.card (G ⧸ L) = 6 := hidx
  have hLtop : L ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top] at hL
    omega
  have hinj : Function.Injective (MulAction.toPermHom G (G ⧸ L)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.normalCore_eq_ker]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L.normalCore with h | h
    · exact h
    · exact absurd (eq_top_iff.2 (h.symm.le.trans L.normalCore_le)) hLtop
  have : Fintype (G ⧸ L) := Fintype.ofFinite _
  have hindex2 : (MulAction.toPermHom G (G ⧸ L)).range.index = 2 := by
    have h1 := Subgroup.index_mul_card (MulAction.toPermHom G (G ⧸ L)).range
    have h2 := (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
    have h3 : Nat.card (Equiv.Perm (G ⧸ L)) = 720 := by
      rw [Nat.card_perm, hX]
      decide
    rw [h2, hG, h3] at h1
    omega
  have hrange : (MulAction.toPermHom G (G ⧸ L)).range = alternatingGroup (G ⧸ L) :=
    Equiv.Perm.eq_alternatingGroup_of_index_eq_two hindex2
  obtain ⟨b, hbdef⟩ : ∃ b : G ⧸ L, b = QuotientGroup.mk 1 := ⟨_, rfl⟩
  have hstab : ∀ g : G, g • b = b → g ∈ L := by
    intro g hg
    rw [hbdef] at hg
    have h : (QuotientGroup.mk (g * 1) : G ⧸ L) = QuotientGroup.mk 1 := hg
    have h2 := QuotientGroup.eq.1 h
    simpa using h2
  obtain ⟨π, hπb, hπsmul⟩ : ∃ π : Equiv.Perm (G ⧸ L), π b = b ∧
      ∀ (g : G) (x : G ⧸ L), π (g • x) = α g • π x := by
    refine ⟨cosetPerm L α hfix, ?_, cosetPerm_smul L α hfix⟩
    rw [hbdef, cosetPerm_mk, map_one α]
  have hcomm : ∀ x y z : G ⧸ L, x ≠ y → x ≠ z → y ≠ z → x ≠ b → y ≠ b → z ≠ b →
      π * (Equiv.swap x y * Equiv.swap x z) = (Equiv.swap x y * Equiv.swap x z) * π := by
    intro x y z hxy hxz hyz hxb hyb hzb
    have hmem : Equiv.swap x y * Equiv.swap x z ∈ alternatingGroup (G ⧸ L) :=
      (Equiv.Perm.isThreeCycle_swap_mul_swap_same hxy hxz hyz).mem_alternatingGroup
    rw [← hrange] at hmem
    obtain ⟨g, hg⟩ := hmem
    have hcb : (Equiv.swap x y * Equiv.swap x z) b = b := by
      rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne (Ne.symm hxb) (Ne.symm hzb),
        Equiv.swap_apply_of_ne_of_ne (Ne.symm hxb) (Ne.symm hyb)]
    have hgb : g • b = b := by
      have h : (MulAction.toPermHom G (G ⧸ L)) g b = b := by
        rw [hg]
        exact hcb
      exact h
    have hgL : g ∈ L := hstab g hgb
    refine Equiv.ext fun t => ?_
    have h1 : π (g • t) = g • π t := by
      rw [hπsmul, hfix g hgL]
    rw [← hg, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    exact h1
  have hπ : π = 1 :=
    perm_eq_one_of_commute (by rw [Fintype.card_eq_nat_card]; exact hX) b π hπb hcomm
  have hπid : ∀ y, π y = y := fun y => by simp [hπ]
  refine MulEquiv.ext fun g => ?_
  show α g = g
  apply hinj
  refine Equiv.ext fun x => ?_
  have h := hπsmul g x
  rw [hπid, hπid] at h
  exact h.symm

theorem aut_alt6_eq_one_of_fixes_index_six
    (α : MulAut (alternatingGroup (Fin 6))) (Lb : Subgroup (alternatingGroup (Fin 6)))
    (hcard : Nat.card Lb = 60) (hfix : ∀ l ∈ Lb, α l = l) : α = 1 := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hG : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  exact aut_eq_one_of_fixes_index_six hG α Lb hcard hfix

end CFSG.GH74.Generic.S45.LAlt
