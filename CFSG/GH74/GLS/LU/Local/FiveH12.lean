module

public import CFSG.GH74.GLS.IVK.Proofs2.Lemma41aL3

public section

open Subgroup CFSG.GH74.GLS.IVK CFSG.Assembly.LowTwoRank
open scoped MatrixGroups commutatorElement

namespace CFSG.GH74.GLS.LU.Local.Five

theorem zmod_five_cube_root_eq_one : ∀ r : ZMod 5, r ^ 3 = 1 → r = 1 := by decide

theorem center_specialLinear_three_zmod_five_eq_bot : Subgroup.center SL(3, ZMod 5) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  have h1 : r = 1 := zmod_five_cube_root_eq_one r (by simpa using hr)
  subst h1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← hrA, map_one]

theorem statedScalars_three_zmod_five_subgroupOf_eq_bot [Fact (Nat.Prime 5)] :
    (StatedScalars (Fin 3) (ZMod 5)).subgroupOf (StatedSL 3 (ZMod 5)) = ⊥ := by
  rw [← map_center_eq_statedScalars, center_specialLinear_three_zmod_five_eq_bot, Subgroup.map_bot]

theorem isLnEps_three_five {K : Type} [Group K] (e : SL(3, ZMod 5) ≃* K) : IsLnEps 3 K 1 5 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  refine Or.inl ⟨rfl, ZMod 5, inferInstance, inferInstance, Nat.card_zmod 5, ⟨?_⟩⟩
  have hinj : Function.Injective
      (QuotientGroup.mk' ((StatedScalars (Fin 3) (ZMod 5)).subgroupOf (StatedSL 3 (ZMod 5)))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact statedScalars_three_zmod_five_subgroupOf_eq_bot
  exact e.symm.trans ((specialLinearGroupEquivStatedSL 3 (ZMod 5)).trans
    (MulEquiv.ofBijective _ ⟨hinj, QuotientGroup.mk_surjective⟩))

theorem commutator_quotient_mem_range_toGL {F' : Type} [Field F'] (N : Subgroup (GL (Fin 2) F'))
    [N.Normal] (u v : GL (Fin 2) F' ⧸ N) :
    ⁅u, v⁆ ∈ ((QuotientGroup.mk' N).comp
      (Matrix.SpecialLinearGroup.toGL : SL(2, F') →* GL (Fin 2) F')).range := by
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  have hdet : Matrix.GeneralLinearGroup.det ⁅u', v'⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_def]
    simp
  have hdet' : ((⁅u', v'⁆ : GL (Fin 2) F') : Matrix (Fin 2) (Fin 2) F').det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hdet, Units.val_one]
  refine ⟨⟨(⁅u', v'⁆ : GL (Fin 2) F'), hdet'⟩, ?_⟩
  have h1 : (Matrix.SpecialLinearGroup.toGL ⟨(⁅u', v'⁆ : GL (Fin 2) F'), hdet'⟩ : GL (Fin 2) F') =
      ⁅u', v'⁆ := Units.ext rfl
  show QuotientGroup.mk' N (Matrix.SpecialLinearGroup.toGL ⟨(⁅u', v'⁆ : GL (Fin 2) F'), hdet'⟩) = _
  rw [h1]
  exact map_commutatorElement (QuotientGroup.mk' N) u' v'

theorem card_derived_centralizer_le {K : Type} [Group K] [Finite K] (hK : IsLnEps 3 K 1 5) (a : K)
    (ha : orderOf a = 2) (F : Type) [Field F] [Finite F] (hF : Nat.card F = 5) :
    Nat.card ↥⁅centralizer ({a} : Set K), centralizer ({a} : Set K)⁆ ≤ Nat.card (SL(2, F)) := by
  obtain ⟨F', _, _, N, _, hF', -, ⟨φ⟩⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.ivk_4_1a_L3 K 5 1 Nat.prime_five (by norm_num) (by simpa using hK) a ha
  set D := centralizer ({a} : Set K)
  let ψ : SL(2, F') →* GL (Fin 2) F' ⧸ N :=
    (QuotientGroup.mk' N).comp (Matrix.SpecialLinearGroup.toGL : SL(2, F') →* GL (Fin 2) F')
  let M : Subgroup ↥D := ψ.range.map φ.symm.toMonoidHom
  have hle : ⁅D, D⁆ ≤ M.map D.subtype := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    refine ⟨⁅(⟨x, hx⟩ : ↥D), (⟨y, hy⟩ : ↥D)⁆, ?_, rfl⟩
    refine ⟨φ ⁅(⟨x, hx⟩ : ↥D), (⟨y, hy⟩ : ↥D)⁆, ?_, by simp⟩
    rw [map_commutatorElement]
    exact commutator_quotient_mem_range_toGL N _ _
  have hcard1 : Nat.card ↥⁅D, D⁆ ≤ Nat.card ↥(M.map D.subtype) := Subgroup.card_le_of_le hle
  have hcard2 : Nat.card ↥(M.map D.subtype) = Nat.card ↥M :=
    Subgroup.card_map_of_injective D.subtype_injective
  have hcard3 : Nat.card ↥M = Nat.card ↥ψ.range :=
    Subgroup.card_map_of_injective φ.symm.injective
  have hcard4 : Nat.card ↥ψ.range ≤ Nat.card SL(2, F') :=
    Nat.card_le_card_of_surjective _ ψ.rangeRestrict_surjective
  have hcard5 : Nat.card SL(2, F') = Nat.card SL(2, F) := by
    have : Fintype F := Fintype.ofFinite F
    have : Fintype F' := Fintype.ofFinite F'
    have hcard : Fintype.card F' = Fintype.card F := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, hF']
      norm_num
    exact Nat.card_congr
      (CFSG.ClassicalModels.specialLinearFieldEquiv (FiniteField.ringEquivOfCardEq hcard)
        (Fin 2)).toEquiv
  omega

end CFSG.GH74.GLS.LU.Local.Five
