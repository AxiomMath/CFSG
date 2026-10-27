module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.LayerSimple

public section

namespace CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3

open CFSG.HardMathSupport.Solomon.Coordinator

@[expose] def DefCharGoodPlus {S : Type*} [Group S] (β : MulAut S) : Prop :=
  (IsSimpleGroup (fixSubgroup β) ∧ ∃ a b : fixSubgroup β, a * b ≠ b * a) ∨
    CFSG.Open.GLAPPrimeCoreOf 3 (fixSubgroup β) = ⊥

private theorem transfer_exists_noncomm {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (hnc : ∃ a b : H, a * b ≠ b * a) : ∃ a b : G, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hnc
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  have h' := congrArg e h
  simp only [map_mul, MulEquiv.apply_symm_apply] at h'
  exact h'

private theorem transfer_glaPPrimeCoreOf_eq_bot {S T : Type*} [Group S] [Group T] (p : ℕ)
    (H : Subgroup S) (K : Subgroup T) (e : H ≃* K)
    (h : CFSG.Open.GLAPPrimeCoreOf p K = ⊥) : CFSG.Open.GLAPPrimeCoreOf p H = ⊥ := by
  have h' : (CFSG.pPrimeCore p K).map K.subtype = ⊥ := h
  have hK : CFSG.pPrimeCore p K = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ K.subtype_injective).1 h'
  have hH : CFSG.pPrimeCore p H = ⊥ := by
    rw [← CFSG.pPrimeCore_map_iso p e.symm, hK, Subgroup.map_bot]
  show (CFSG.pPrimeCore p H).map H.subtype = ⊥
  rw [hH, Subgroup.map_bot]

theorem DefCharGoodPlus.good {S : Type*} [Group S] [Finite S] {β : MulAut S}
    (h : DefCharGoodPlus β) :
    PerfectInLayer β ∨ CFSG.Open.GLAPPrimeCoreOf 3 (fixSubgroup β) = ⊥ := by
  rcases h with ⟨hs, hnc⟩ | h
  · exact Or.inl (LieSemisimple.perfectInLayer_of_isSimpleGroup β hs hnc)
  · exact Or.inr h

theorem defCharGoodPlus_of_equiv {S T : Type*} [Group S] [Group T] [Finite S] [Finite T]
    {β : MulAut S} {γ : MulAut T} (e : fixSubgroup β ≃* fixSubgroup γ) :
    DefCharGoodPlus γ → DefCharGoodPlus β := by
  rintro (⟨hs, hnc⟩ | h)
  · exact Or.inl ⟨e.isSimpleGroup, transfer_exists_noncomm e hnc⟩
  · exact Or.inr (transfer_glaPPrimeCoreOf_eq_bot 3 (fixSubgroup β) (fixSubgroup γ) e h)

theorem defCharGoodPlus_conj {S : Type*} [Group S] [Finite S] (ε β : MulAut S) :
    DefCharGoodPlus (ε * β * ε⁻¹) → DefCharGoodPlus β := by
  have hmap : (fixSubgroup β).map ε.toMonoidHom = fixSubgroup (ε * β * ε⁻¹) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy' : β y = y := hy
      show (ε * β * ε⁻¹) (ε y) = ε y
      simp only [MulAut.mul_apply, MulAut.inv_apply_self, hy']
    · intro hx
      have hx' : ε (β (ε⁻¹ x)) = x := hx
      refine Subgroup.mem_map.2 ⟨ε⁻¹ x, ?_, MulAut.apply_inv_self _ ε x⟩
      show β (ε⁻¹ x) = ε⁻¹ x
      apply ε.injective
      rw [hx', MulAut.apply_inv_self]
  exact defCharGoodPlus_of_equiv
    ((Subgroup.equivMapOfInjective (fixSubgroup β) ε.toMonoidHom ε.injective).trans
      (MulEquiv.subgroupCongr hmap))

theorem defCharGoodPlus_inv {S : Type*} [Group S] [Finite S] (β : MulAut S) :
    DefCharGoodPlus β⁻¹ → DefCharGoodPlus β := by
  have hfix : fixSubgroup β⁻¹ = fixSubgroup β := by
    ext x
    show β⁻¹ x = x ↔ β x = x
    constructor
    · intro h
      calc β x = β (β⁻¹ x) := by rw [h]
        _ = x := MulAut.apply_inv_self _ β x
    · intro h
      calc β⁻¹ x = β⁻¹ (β x) := by rw [h]
        _ = x := MulAut.inv_apply_self _ β x
  exact defCharGoodPlus_of_equiv (MulEquiv.subgroupCongr hfix.symm)

end CFSG.HardMathSupport.Dickson.DefCharOuter.TrialityChar3
