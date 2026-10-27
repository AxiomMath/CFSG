module

public import CFSG.LargeExtraspecial.AS35KFisA
public import CFSG.LargeExtraspecial.AS35KBridgeMain

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Matrix CFSG.Open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary

namespace Setting

variable {H : Type} [Group H] [Finite H] (T : Setting H)

omit [Finite H] in
theorem exists_mul_ne_mul_zGen (hC : centralizer (T.zGen : Set H) = ⊥) :
    ∃ a b : T.zGen, a * b ≠ b * a := by
  by_contra h
  push Not at h
  have hz : T.z ∈ centralizer (T.zGen : Set H) := mem_centralizer_iff.mpr fun l hl =>
    congrArg Subtype.val (h ⟨l, hl⟩ T.zL)
  rw [hC, mem_bot] at hz
  exact T.z_ne_one hz

omit [Finite H] in
theorem orderOf_of_mem_DL {d : T.zGen} (hd : IsConj T.zL d) : orderOf d = 2 := by
  obtain ⟨c, rfl⟩ := isConj_iff.mp hd
  rw [← MulAut.conj_apply, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, coe_zL, T.orderOf_z]

omit [Finite H] in
theorem orderOf_mul_mem_DL (h3 : ∀ l₁ ∈ T.zGen, ∀ l₂ ∈ T.zGen,
      orderOf (l₁ * T.z * l₁⁻¹ * (l₂ * T.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ))
    {d e : T.zGen} (hd : IsConj T.zL d) (he : IsConj T.zL e) :
    orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ) := by
  obtain ⟨c₁, rfl⟩ := isConj_iff.mp hd
  obtain ⟨c₂, rfl⟩ := isConj_iff.mp he
  rw [← Subgroup.orderOf_coe]
  simpa using h3 c₁ c₁.2 c₂ c₂.2

theorem false_of_component_zGen {K : Subgroup T.zGen}
    (hK : IsComponentOf K (centralizer ({T.zL} : Set T.zGen))) : False := by
  have hLn := T.zGen_normal
  set C := (centralizer ({T.zL} : Set T.zGen)).map T.zGen.subtype with hCdef
  have hCM : C ≤ T.M := by
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ centralizer ({T.zL} : Set T.zGen) := hy
    rw [mem_centralizer_singleton_iff] at hy'
    rw [Subgroup.coe_subtype, T.mem_M_iff]
    exact congrArg Subtype.val hy'
  have hCn : (C.subgroupOf T.M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hCM]
    rintro _ k ⟨y, hy, rfl⟩ hk
    refine ⟨⟨k * y * k⁻¹, hLn.conj_mem _ y.2 k⟩, ?_, rfl⟩
    have hy0 : y ∈ centralizer ({T.zL} : Set T.zGen) := hy
    show (⟨k * y * k⁻¹, hLn.conj_mem _ y.2 k⟩ : T.zGen) ∈ centralizer ({T.zL} : Set T.zGen)
    rw [mem_centralizer_singleton_iff] at hy0 ⊢
    apply Subtype.ext
    have hy' : (y : H) * T.z = T.z * y := congrArg Subtype.val hy0
    have hk' : k * T.z = T.z * k := T.mem_M_iff.mp hk
    change k * (y : H) * k⁻¹ * T.z = T.z * (k * (y : H) * k⁻¹)
    calc k * (y : H) * k⁻¹ * T.z = k * (y : H) * (k⁻¹ * T.z) := by group
      _ = k * (y : H) * (T.z * k⁻¹) := by
        rw [show k⁻¹ * T.z = T.z * k⁻¹ by
          calc k⁻¹ * T.z = k⁻¹ * (T.z * k) * k⁻¹ := by group
            _ = k⁻¹ * (k * T.z) * k⁻¹ := by rw [hk']
            _ = T.z * k⁻¹ := by group]
      _ = k * ((y : H) * T.z) * k⁻¹ := by group
      _ = k * (T.z * y) * k⁻¹ := by rw [hy']
      _ = (k * T.z) * y * k⁻¹ := by group
      _ = T.z * (k * (y : H) * k⁻¹) := by rw [hk']; group
  have h1 := AS35K.isSubnormal_map T.zGen.subtype hK.2.1
  have h2 : IsSubnormal C T.M := IsSubnormal.step hCM hCn (IsSubnormal.refl _)
  exact T.not_isComponentOf _ ⟨(map_mono hK.1).trans hCM, AS35K.isSubnormal_trans h1 h2,
    AS35K.isQuasisimple_map _ T.zGen.subtype_injective hK.2.2⟩

omit [Finite H] in
theorem unitaryModel_of_case4 {m : ℕ}
    (hmodel : fischerCentralQuotientModel {g : T.zGen | IsConj T.zL g}
      (fischerMatrixGroup fun A => A.det = 1 ∧
        ∀ x y, fischerHermitianF4 m (A *ᵥ x) (A *ᵥ y) = fischerHermitianF4 m x y)
      (fischerTransvections (fischerHermitianF4 m)
        fun v => v ≠ 0 ∧ fischerHermitianF4 m v v = 0)) :
    ∃ ψ : T.zGen ≃* PG m, ∀ l : T.zGen, IsConj T.zL l ↔ ψ l ∈ DG m := by
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1 hmodel
  refine ⟨φ.trans (u2Equiv m), fun l => ?_⟩
  rw [← image_DU, ← hφ]
  constructor
  · intro hl
    exact ⟨φ l, ⟨l, hl, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨l', hl', rfl⟩, hll'⟩
    have h1 : l' = l := (φ.trans (u2Equiv m)).injective hll'
    rw [← h1]
    exact hl'

omit [Finite H] in
theorem fischer_hyps (hs : IsSimpleGroup T.zGen) (hC : centralizer (T.zGen : Set H) = ⊥)
    (h3 : ∀ l₁ ∈ T.zGen, ∀ l₂ ∈ T.zGen,
      orderOf (l₁ * T.z * l₁⁻¹ * (l₂ * T.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) :
    (∀ d ∈ {g : T.zGen | IsConj T.zL g}, orderOf d = 2) ∧
      (∀ d ∈ {g : T.zGen | IsConj T.zL g}, ∀ e ∈ {g : T.zGen | IsConj T.zL g},
        orderOf (d * e) ∈ ({1, 2, 3} : Set ℕ)) ∧
      closure {g : T.zGen | IsConj T.zL g} = ⊤ ∧ center T.zGen = ⊥ ∧
      IsSimpleGroup (_root_.commutator T.zGen) := by
  have hna := T.exists_mul_ne_mul_zGen hC
  refine ⟨fun _ hd => T.orderOf_of_mem_DL hd, fun _ hd _ he => T.orderOf_mul_mem_DL h3 hd he,
    AS35K.closure_isConj_eq_top fun h => T.z_ne_one (congrArg Subtype.val h),
    AS35K.center_eq_bot_of_simple hna, ?_⟩
  exact ((MulEquiv.subgroupCongr (AS35K.commutator_eq_top_of_simple hna)).trans
    Subgroup.topEquiv).isSimpleGroup

theorem false_of_sporadic_zGen
    (hs : IsSimpleGroup T.zGen) (hC : centralizer (T.zGen : Set H) = ⊥)
    (h3 : ∀ l₁ ∈ T.zGen, ∀ l₂ ∈ T.zGen,
      orderOf (l₁ * T.z * l₁⁻¹ * (l₂ * T.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ))
    (h : Nonempty (T.zGen ≃* CFSG.Blueprint.NativeSporadic.Fi22) ∨
      Nonempty (T.zGen ≃* CFSG.Blueprint.NativeSporadic.Fi23) ∨
      Nonempty (T.zGen ≃* MulAut CFSG.Blueprint.NativeSporadic.Fi24prime)) : False := by
  obtain ⟨hinv, hprod, hgen, hcen, hsim⟩ := T.fischer_hyps hs hC h3
  have hrec := CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_recognition T.zGen
    {g | IsConj T.zL g} ⟨T.zL, rfl⟩ hinv hprod hgen hcen hsim T.zL (IsConj.refl T.zL)
  rcases h with h | h | h
  · obtain ⟨K, hK, -⟩ := hrec.1.mp h
    exact T.false_of_component_zGen hK
  · obtain ⟨K, hK, -⟩ := hrec.2.1.mp h
    exact T.false_of_component_zGen hK
  · obtain ⟨K, hK, -⟩ := hrec.2.2.1.mp h
    exact T.false_of_component_zGen hK

end Setting

namespace S14

open Matrix in
@[expose] def FischerSpOrRefl {L : Type} [Group L] (D : Set L) : Prop :=
  (∃ m : ℕ, 2 ≤ m ∧ ∃ b : LinearMap.BilinForm (ZMod 2) (Fin (2 * m) → ZMod 2),
      (∀ x, b x x = 0) ∧ (∀ x, (∀ y, b x y = 0) → x = 0) ∧
      fischerLinearModel D
        (fischerMatrixGroup fun A => ∀ x y, b (A *ᵥ x) (A *ᵥ y) = b x y)
        (fischerTransvections (fun x y => b x y) fun v => v ≠ 0)) ∨
    (∃ m : ℕ, 5 ≤ m ∧ ∃ f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3),
      (∀ x y, f x y = f y x) ∧ (∀ x, (∀ y, f x y = 0) → x = 0) ∧
      fischerCentralQuotientModel D
        (Subgroup.closure (fischerTransvections (fun x y => f x y) fun v => f v v = 1))
        (fischerTransvections (fun x y => f x y) fun v => f v v = 1))

@[expose] def AschTwoSpReflStmt : Prop :=
  ∀ (H : Type) [Group H] [Finite H] (T : Setting H), 2 ≤ T.width → IsSimpleGroup T.zGen →
    centralizer (T.zGen : Set H) = ⊥ →
    (∀ l₁ ∈ T.zGen, ∀ l₂ ∈ T.zGen,
      orderOf (l₁ * T.z * l₁⁻¹ * (l₂ * T.z * l₂⁻¹)) ∈ ({1, 2, 3} : Set ℕ)) →
    FischerSpOrRefl {g : T.zGen | IsConj T.zL g} →
    ∃ m : ℕ, 4 ≤ m ∧ ∃ ψ : T.zGen ≃* PG m, ∀ l : T.zGen, IsConj T.zL l ↔ ψ l ∈ DG m

theorem aschTwoUnitaryModelStmt_of_spRefl
    (hres : AschTwoSpReflStmt) : AschTwoUnitaryModelStmt := by
  intro H _ _ T hw hs hC h3
  have hna := T.exists_mul_ne_mul_zGen hC
  obtain ⟨hinv, hprod, hgen, hcen, hsim⟩ := T.fischer_hyps hs hC h3
  rcases CFSG.Milestones.cl_lit_fischer_three_transposition_theorem_pinned T.zGen
      {g | IsConj T.zL g} ⟨T.zL, rfl⟩ hinv hprod hgen hcen hsim with
    ⟨m, -, φ, hφ⟩ | h2 | ⟨m, -, Q, hnd, -, h3'⟩ | ⟨m, hm, h4⟩ | h5 | ⟨φ, -⟩ | ⟨φ, -⟩ | ⟨φ, -⟩
  · exact (AS35K.false_of_perm hna φ ((hφ T.zL).mp (IsConj.refl _))).elim
  · exact hres H T hw hs hC h3 (Or.inl h2)
  · exact (AS35K.false_of_case3 hna (IsConj.refl T.zL) hnd h3').elim
  · obtain ⟨ψ, hψ⟩ := T.unitaryModel_of_case4 h4
    exact ⟨m, hm, ψ, hψ⟩
  · exact hres H T hw hs hC h3 (Or.inr h5)
  · exact (T.false_of_sporadic_zGen hs hC h3 (Or.inl ⟨φ⟩)).elim
  · exact (T.false_of_sporadic_zGen hs hC h3 (Or.inr (Or.inl ⟨φ⟩))).elim
  · exact (T.false_of_sporadic_zGen hs hC h3 (Or.inr (Or.inr ⟨φ⟩))).elim

end S14

end CFSG.LargeExtraspecial
