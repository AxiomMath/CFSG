module

public import CFSG.LargeExtraspecial.AS35KRbar
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LargeExtraspecial.AS35DStmt
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Fischer.Classification.Unitary CFSG.ClassicalGroups.Unitary
open CFSG.Blueprint.Fischer (K)

namespace AS35K

theorem eq_or_eq_conj_of_transport {X Y : Type*} [Group X] [Group Y] (ψ : X ≃* Y)
    (φ : MulAut X) {a : X}
    (h : ψ.symm.trans (φ.trans ψ) = 1 ∨ ψ.symm.trans (φ.trans ψ) = MulAut.conj (ψ a)) :
    (∀ x, φ x = x) ∨ ∀ x, φ x = a * x * a⁻¹ := by
  rcases h with h | h
  · refine Or.inl fun x => ψ.injective ?_
    have h1 := congrArg (fun β : MulAut Y => β (ψ x)) h
    simpa only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.one_apply] using h1
  · refine Or.inr fun x => ψ.injective ?_
    have h1 := congrArg (fun β : MulAut Y => β (ψ x)) h
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, MulAut.conj_apply] at h1
    rw [h1, map_mul, map_mul, map_inv]

theorem mulAut_mem_oTwoCent {X : Type} [Group X] (β : MulAut X) {a y : X} (ha : β a = a)
    (hy : y ∈ oTwoCent a) : β y ∈ oTwoCent a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsymm : β.symm a = a := by rw [MulEquiv.symm_apply_eq, ha]
  refine le_oTwoCent (P := (oTwoCent a).map β.toMonoidHom) ?_ ?_
    ((isPGroup_oTwoCent a).map _) ⟨y, hy, rfl⟩
  · rintro _ ⟨w, hw, rfl⟩
    have hw' := mem_centralizer_singleton_iff.mp (oTwoCent_le_centralizer a hw)
    rw [mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom, ← ha, ← map_mul, ← map_mul, hw']
  · rintro c hc _ ⟨w, hw, rfl⟩
    have hc' : β.symm c ∈ centralizer ({a} : Set X) := by
      rw [mem_centralizer_singleton_iff] at hc ⊢
      rw [← hsymm, ← map_mul, ← map_mul, hc]
    refine ⟨β.symm c * w * (β.symm c)⁻¹, conj_mem_oTwoCent hc' hw, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, map_mul, map_inv, MulEquiv.apply_symm_apply]

end AS35K

namespace Setting

variable {H : Type} [Group H] (T : Setting H)

theorem le_QG_of_normalizes {P : Subgroup H} (hPM : P ≤ T.M)
    (hn : ∀ c ∈ T.M, ∀ x ∈ P, c * x * c⁻¹ ∈ P) (h2 : IsPGroup 2 P) : P ≤ T.QG := by
  have hnor : (P.subgroupOf T.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hPM]
    exact fun x k hx hk => hn k hk x hx
  have hP := T.le_of_normal _ hnor (h2.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm)
  exact fun x hx => ⟨⟨x, hPM hx⟩, hP hx, rfl⟩

theorem map_zGen_le_of_fix {α : H ≃* H} (hα : α T.z = T.z) :
    T.zGen.map (α : H →* H) ≤ T.zGen := by
  rw [zGen, MonoidHom.map_closure]
  apply Subgroup.closure_mono
  rintro _ ⟨g, hg, rfl⟩
  obtain ⟨c, rfl⟩ := isConj_iff.mp hg
  refine isConj_iff.mpr ⟨α c, ?_⟩
  simp only [MonoidHom.coe_ofClass, map_mul, map_inv, hα]

theorem map_zGen_eq_of_fix {α : H ≃* H} (hα : α T.z = T.z) :
    T.zGen.map (α : H →* H) = T.zGen := by
  refine le_antisymm (T.map_zGen_le_of_fix hα) fun x hx => ?_
  have hsymm : α.symm T.z = T.z := by rw [MulEquiv.symm_apply_eq, hα]
  refine ⟨α.symm x, T.map_zGen_le_of_fix hsymm ⟨x, hx, rfl⟩, ?_⟩
  simp

@[expose] noncomputable def zGenAut (α : H ≃* H) (hα : α T.z = T.z) : MulAut T.zGen :=
  (α.subgroupMap T.zGen).trans (MulEquiv.subgroupCongr (T.map_zGen_eq_of_fix hα))

@[simp] theorem coe_zGenAut (α : H ≃* H) (hα : α T.z = T.z) (l : T.zGen) :
    ((T.zGenAut α hα l : T.zGen) : H) = α l := rfl

end Setting

namespace S14

@[expose] def UnitaryAutFacts (m : ℕ) : Prop :=
  (∀ β : MulAut (PG m), ∀ d ∈ DG m, β d ∈ DG m) ∧
    ∀ e : Fin m → K, e ≠ 0 → herm frob e e = 0 → ∀ β : MulAut (PG m),
      (∀ x ∈ AS35K.Rbar m e, β x = x) → β = 1 ∨ β = MulAut.conj (tq e)

@[expose] def AschTwoUnitaryModelStmt : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Setting H), 2 ≤ T.width → IsSimpleGroup T.zGen →
    centralizer (T.zGen : Set H) = ⊥ →
    (∀ l₁ ∈ T.zGen, ∀ l₂ ∈ T.zGen,
      orderOf (l₁ * T.z * l₁⁻¹ * (l₂ * T.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) →
    ∃ m : ℕ, 4 ≤ m ∧ ∃ ψ : T.zGen ≃* PG m,
      ∀ l : T.zGen, IsConj (⟨T.z, T.z_mem_zGen⟩ : T.zGen) l ↔ ψ l ∈ DG m

end S14

end CFSG.LargeExtraspecial
