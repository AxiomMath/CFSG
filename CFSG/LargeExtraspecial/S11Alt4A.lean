module

public import CFSG.LargeExtraspecial.S7Alt4
public import CFSG.LargeExtraspecial.S11Seven

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.S11

open Subgroup Module CFSG.LargeExtraspecial.S4 CFSG.Open
open scoped MatrixGroups commutatorElement

universe u_G

theorem frattini_map_le_of_sq {X : Type*} [Group X] [Finite X] {P K : Subgroup X}
    (hP : IsPGroup 2 P) (hsq : ∀ x ∈ P, x ^ 2 ∈ K) (hcomm : ∀ x ∈ P, ∀ y ∈ P, ⁅x, y⁆ ∈ K) :
    (frattini P).map P.subtype ≤ K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (IsPGroup 2 P) := ⟨hP⟩
  have h : frattini P ≤ K.comap P.subtype := by
    rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
    rintro x (hx | ⟨y, rfl⟩)
    · have hx' : P.subtype x ∈ ⁅P, P⁆ := by
        have : P.subtype x ∈ (commutator P).map P.subtype := Subgroup.mem_map_of_mem _ hx
        rwa [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype] at this
      exact (Subgroup.commutator_le.mpr hcomm) hx'
    · exact hsq y y.2
  rintro _ ⟨y, hy, rfl⟩
  exact h hy

theorem center_specialLinearGroup_fin_three :
    center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  have h1 : r = 1 := by
    rcases CFSG.LargeExtraspecial.OrthoF2.zmod2_eq_zero_or_eq_one r with rfl | rfl
    · exact absurd hr (by decide)
    · rfl
  rw [mem_bot]
  ext i j
  rw [← hrA, h1]
  simp

section Basis

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] (b : Module.Basis (Fin 3) (ZMod 2) V)

theorem slAct_injective : Function.Injective (slAct b) := by
  intro A B h
  have h1 : Matrix.SpecialLinearGroup.toGL A = Matrix.SpecialLinearGroup.toGL B := by
    have := congrArg (CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
      b) h
    simpa [slAct] using this
  exact Matrix.SpecialLinearGroup.toGL_injective h1

@[expose] noncomputable def toPSL3 : (V ≃ₗ[ZMod 2] V) →* PSL(3, ZMod 2) :=
  (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))).comp
    (MulEquiv.ofBijective (slAct b) ⟨slAct_injective b, slAct_surjective b⟩).symm.toMonoidHom

theorem toPSL3_surjective : Function.Surjective (toPSL3 b) :=
  (QuotientGroup.mk'_surjective _).comp (MulEquiv.surjective _)

theorem toPSL3_injective : Function.Injective (toPSL3 b) := by
  have h1 : Function.Injective
      (QuotientGroup.mk' (center (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_specialLinearGroup_fin_three]
  exact h1.comp (MulEquiv.injective _)

end Basis

variable {G : Type u_G} [Group G] [Finite G] {S : Setting G} {g : G}

theorem isPGroup_Lbar (u : G) : IsPGroup 2 (S.Lbar u) := by
  have h1 : IsPGroup 2 (S.L0 u) := ((S.conjBy u).isPGroup_QG).to_le inf_le_left
  have h2 : IsPGroup 2 ((S.L0 u).subgroupOf S.M) :=
    h1.comap_of_injective S.M.subtype S.M.subtype_injective
  exact h2.map S.ρ

theorem pCore_le_ker_of_simple (H : Hyp4 S g) {t : S.O} (hs : IsSimpleGroup (RmodN S g t))
    (hnab : S5.NonabelianSylowTwo (RmodN S g t)) :
    CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar) ≤ (S7.resRM S g H.conj_mem t).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (Vt S g t ≃ₗ[ZMod 2] Vt S g t) := finite_linearEquiv_of_finite
  have hrange := S7.range_resRM H.conj_mem t
  have hperf := S7.commutator_eq_top_RmodN hs hnab
  have hP'R : (CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (S7.resRM S g H.conj_mem t) ≤ RmodN S g t := hrange ▸ map_le_range _ _
  have hP'p : IsPGroup 2 ((CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (S7.resRM S g H.conj_mem t)) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := (Rbar S g t).subgroupOf S.Mbar) 2).map _
  have hP'n : (((CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (S7.resRM S g H.conj_mem t)).subgroupOf (RmodN S g t)).Normal := by
    refine ⟨fun z hz y => ?_⟩
    rw [mem_subgroupOf] at hz ⊢
    obtain ⟨p, hp, hpz⟩ := hz
    have hy : (y : Vt S g t ≃ₗ[ZMod 2] Vt S g t) ∈ (S7.resRM S g H.conj_mem t).range := by
      rw [hrange]
      exact y.2
    obtain ⟨x, hx⟩ := hy
    refine ⟨x * p * x⁻¹, (CFSG.LieType.BorelTits.pCore_normal 2).conj_mem p hp x, ?_⟩
    simp only [map_mul, map_inv, hx, hpz, Subgroup.coe_mul, Subgroup.coe_inv]
  have hbot := S7.eq_bot_of_normal_of_isPGroup hperf hP'n
    (hP'p.of_equiv (subgroupOfEquivOfLe hP'R).symm)
  rw [subgroupOf_eq_bot] at hbot
  have hP'bot : (CFSG.Open.pCore 2 ((Rbar S g t).subgroupOf S.Mbar)).map
      (S7.resRM S g H.conj_mem t) = ⊥ :=
    eq_bot_iff.mpr fun z hz => (disjoint_iff_inf_le.mp hbot ⟨hz, hP'R hz⟩)
  rwa [Subgroup.map_eq_bot_iff] at hP'bot

end CFSG.LargeExtraspecial.S11
