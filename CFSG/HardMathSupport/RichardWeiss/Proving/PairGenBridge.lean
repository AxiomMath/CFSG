module

public import CFSG.HardMathSupport.RichardWeiss.Proving.PairTypeDichotomy

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.CGT.PushingUpLit.CGT6

variable {S : Type} [Group S]

theorem mem_pairGen_of_map_conj_left {Y : Subgroup S} {g h x : S}
    (hx : x ∈ Y.map (MulAut.conj g).toMonoidHom) : x ∈ pairGen Y g h :=
  Subgroup.subset_closure (Or.inl hx)

theorem mem_pairGen_of_map_conj_right {Y : Subgroup S} {g h x : S}
    (hx : x ∈ Y.map (MulAut.conj h).toMonoidHom) : x ∈ pairGen Y g h :=
  Subgroup.subset_closure (Or.inr hx)

theorem pairGen_eq_closure {Y : Subgroup S} {g h a b : S}
    (hYa : Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers a)
    (hYb : Y.map (MulAut.conj h).toMonoidHom = Subgroup.zpowers b) :
    pairGen Y g h = Subgroup.closure ({a, b} : Set S) := by
  apply le_antisymm
  · apply (Subgroup.closure_le _).mpr
    rintro x (hx | hx)
    · have hx' : x ∈ Y.map (MulAut.conj g).toMonoidHom := hx
      rw [hYa] at hx'
      exact Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert a {b})) hx'
    · have hx' : x ∈ Y.map (MulAut.conj h).toMonoidHom := hx
      rw [hYb] at hx'
      exact Subgroup.zpowers_le.mpr
        (Subgroup.subset_closure (Set.mem_insert_of_mem a (Set.mem_singleton b))) hx'
  · apply (Subgroup.closure_le _).mpr
    rintro x (rfl | rfl)
    · exact mem_pairGen_of_map_conj_left (by rw [hYa]; exact Subgroup.mem_zpowers _)
    · exact mem_pairGen_of_map_conj_right (by rw [hYb]; exact Subgroup.mem_zpowers _)

theorem closure_top_pairGen {Y : Subgroup S} {g h a b : S}
    (ha : a ∈ pairGen Y g h) (hb : b ∈ pairGen Y g h)
    (hcl : pairGen Y g h = Subgroup.closure ({a, b} : Set S)) :
    Subgroup.closure ({⟨a, ha⟩, ⟨b, hb⟩} : Set ↥(pairGen Y g h)) = ⊤ := by
  apply Subgroup.map_injective (f := (pairGen Y g h).subtype) Subtype.val_injective
  rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  exact hcl.symm

theorem coe_pow_eq_one_iff {Y : Subgroup S} {g h : S} (x : ↥(pairGen Y g h)) (n : ℕ) :
    (x : S) ^ n = 1 ↔ x ^ n = 1 := by
  constructor
  · intro hx
    exact Subtype.ext (by simpa using hx)
  · intro hx
    have := congrArg Subtype.val hx
    simpa using this

theorem pairType_of_conjugates {Y : Subgroup S} {g h a b : S}
    (hK : IsZ3E9A4A5 ↥(pairGen Y g h)) (ha : orderOf a = 3) (hb : orderOf b = 3)
    (hab : Subgroup.zpowers a ≠ Subgroup.zpowers b)
    (hYa : Y.map (MulAut.conj g).toMonoidHom = Subgroup.zpowers a)
    (hYb : Y.map (MulAut.conj h).toMonoidHom = Subgroup.zpowers b) :
    (Nonempty (↥(pairGen Y g h) ≃* Multiplicative (ZMod 3 × ZMod 3)) ∧ a * b = b * a) ∨
    (Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 4)) ∧
      ((a * b) ^ 2 = 1 ↔ (a * b⁻¹) ^ 2 ≠ 1)) ∨
    (Nonempty (↥(pairGen Y g h) ≃* alternatingGroup (Fin 5)) ∧
      ((a * b) ^ 5 = 1 ∧ (b⁻¹ * a * b * a) ^ 2 = 1)) := by
  have hcl := pairGen_eq_closure hYa hYb
  have ha_mem : a ∈ pairGen Y g h :=
    mem_pairGen_of_map_conj_left (by rw [hYa]; exact Subgroup.mem_zpowers _)
  have hb_mem : b ∈ pairGen Y g h :=
    mem_pairGen_of_map_conj_right (by rw [hYb]; exact Subgroup.mem_zpowers _)
  have ha' : orderOf (⟨a, ha_mem⟩ : ↥(pairGen Y g h)) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact ha
  have hb' : orderOf (⟨b, hb_mem⟩ : ↥(pairGen Y g h)) = 3 := by
    rw [← Subgroup.orderOf_coe]
    exact hb
  have hab' : Subgroup.zpowers (⟨a, ha_mem⟩ : ↥(pairGen Y g h)) ≠
      Subgroup.zpowers (⟨b, hb_mem⟩ : ↥(pairGen Y g h)) := by
    intro heq
    apply hab
    have := congrArg (Subgroup.map (pairGen Y g h).subtype) heq
    rw [MonoidHom.map_zpowers, MonoidHom.map_zpowers] at this
    exact this
  have hgen := closure_top_pairGen ha_mem hb_mem hcl
  rcases pair_type hK ha' hb' hab' hgen with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨h1, congrArg Subtype.val h2⟩
  · refine Or.inr (Or.inl ⟨h1, ?_⟩)
    exact (coe_pow_eq_one_iff (⟨a, ha_mem⟩ * ⟨b, hb_mem⟩) 2).trans
      (h2.trans (not_congr (coe_pow_eq_one_iff
        (⟨a, ha_mem⟩ * (⟨b, hb_mem⟩ : ↥(pairGen Y g h))⁻¹) 2).symm))
  · refine Or.inr (Or.inr ⟨h1, ?_, ?_⟩)
    · exact (coe_pow_eq_one_iff (⟨a, ha_mem⟩ * ⟨b, hb_mem⟩) 5).mpr h2.1
    · exact (coe_pow_eq_one_iff
        ((⟨b, hb_mem⟩ : ↥(pairGen Y g h))⁻¹ * ⟨a, ha_mem⟩ * ⟨b, hb_mem⟩ * ⟨a, ha_mem⟩) 2).mpr h2.2

end CFSG.HardMathSupport.RichardWeiss.Proving

end
