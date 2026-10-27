module

public import CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSixMaximalElementaryRadicals

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix

open Subgroup Module SymplecticFlag CFSG.Assembly.LowTwoRank
open LinearMap (BilinForm)

section Pull

variable {G X : Type*} [Group G] [Group X] {L : Subgroup G} (φ : L ≃* X)

@[expose] def pullSub (P : Subgroup X) : Subgroup G :=
  (P.comap φ.toMonoidHom).map L.subtype

variable {φ} in
theorem mem_pullSub {P : Subgroup X} {x : G} :
    x ∈ pullSub φ P ↔ ∃ h : x ∈ L, φ ⟨x, h⟩ ∈ P := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨h, hP⟩
    exact ⟨⟨x, h⟩, hP, rfl⟩

theorem pullSub_le (P : Subgroup X) : pullSub φ P ≤ L :=
  map_subtype_le _

theorem pullSub_eq_map (P : Subgroup X) :
    pullSub φ P = P.map (L.subtype.comp φ.symm.toMonoidHom) := by
  rw [pullSub, ← map_map]
  congr 1
  exact comap_equiv_eq_map_symm φ P

theorem card_pullSub (P : Subgroup X) : Nat.card (pullSub φ P) = Nat.card P := by
  rw [pullSub_eq_map, card_map_of_injective fun x y h => φ.symm.injective (subtype_injective L h)]

theorem isElementaryAbelian_pullSub {P : Subgroup X} (hP : IsElementaryAbelian 2 P) :
    IsElementaryAbelian 2 (pullSub φ P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [pullSub_eq_map]
  exact IsElementaryAbelian.map _

theorem pullSub_mono {P Q : Subgroup X} (h : P ≤ Q) : pullSub φ P ≤ pullSub φ Q :=
  map_mono (comap_mono h)

theorem centralizer_pullSub_inf (P : Subgroup X) :
    centralizer (pullSub φ P : Set G) ⊓ L = pullSub φ (centralizer (P : Set X)) := by
  ext x
  rw [mem_inf, mem_pullSub]
  constructor
  · rintro ⟨hx, hxL⟩
    refine ⟨hxL, mem_centralizer_iff.2 fun p hp => ?_⟩
    have hy : ((φ.symm p : L) : G) ∈ pullSub φ P :=
      mem_pullSub.2 ⟨(φ.symm p).2, by simpa using hp⟩
    have h := mem_centralizer_iff.1 hx _ hy
    have h' : φ.symm p * ⟨x, hxL⟩ = ⟨x, hxL⟩ * φ.symm p := Subtype.ext h
    have := congrArg φ h'
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this
  · rintro ⟨hxL, hx⟩
    refine ⟨mem_centralizer_iff.2 fun y hy => ?_, hxL⟩
    obtain ⟨hyL, hyP⟩ := mem_pullSub.1 hy
    have h := mem_centralizer_iff.1 hx _ hyP
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (φ.injective h)

theorem normalizer_pullSub_inf (P : Subgroup X) :
    normalizer (pullSub φ P : Set G) ⊓ L = pullSub φ (normalizer (P : Set X)) := by
  ext x
  rw [mem_inf, mem_pullSub]
  constructor
  · rintro ⟨hx, hxL⟩
    refine ⟨hxL, mem_normalizer_iff.2 fun p => ?_⟩
    have key := (mem_normalizer_iff.1 hx) ((φ.symm p : L) : G)
    have h1 : ((φ.symm p : L) : G) ∈ pullSub φ P ↔ p ∈ P := by
      rw [mem_pullSub]
      exact ⟨fun ⟨_, h⟩ => by simpa using h, fun h => ⟨(φ.symm p).2, by simpa using h⟩⟩
    have h2 : x * ((φ.symm p : L) : G) * x⁻¹ ∈ pullSub φ P ↔
        φ ⟨x, hxL⟩ * p * (φ ⟨x, hxL⟩)⁻¹ ∈ P := by
      rw [mem_pullSub]
      constructor
      · rintro ⟨_, h⟩
        have : (⟨x * ((φ.symm p : L) : G) * x⁻¹, by assumption⟩ : L) =
            ⟨x, hxL⟩ * φ.symm p * (⟨x, hxL⟩ : L)⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply] at h
        exact h
      · intro h
        refine ⟨mul_mem (mul_mem hxL (φ.symm p).2) (inv_mem hxL), ?_⟩
        have : (⟨x * ((φ.symm p : L) : G) * x⁻¹,
            mul_mem (mul_mem hxL (φ.symm p).2) (inv_mem hxL)⟩ : L) =
            ⟨x, hxL⟩ * φ.symm p * (⟨x, hxL⟩ : L)⁻¹ := rfl
        rw [this, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
        exact h
    rw [← h1, ← h2]
    exact key
  · rintro ⟨hxL, hx⟩
    refine ⟨mem_normalizer_iff.2 fun y => ?_, hxL⟩
    rw [mem_pullSub, mem_pullSub]
    constructor
    · rintro ⟨hyL, hyP⟩
      refine ⟨mul_mem (mul_mem hxL hyL) (inv_mem hxL), ?_⟩
      have : (⟨x * y * x⁻¹, mul_mem (mul_mem hxL hyL) (inv_mem hxL)⟩ : L) =
          ⟨x, hxL⟩ * ⟨y, hyL⟩ * (⟨x, hxL⟩ : L)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.1 hx _).1 hyP
    · rintro ⟨hyL', hyP⟩
      have hyL : y ∈ L := by
        have := mul_mem (mul_mem (inv_mem hxL) hyL') hxL
        simpa [mul_assoc] using this
      refine ⟨hyL, (mem_normalizer_iff.1 hx _).2 ?_⟩
      have : (⟨x * y * x⁻¹, hyL'⟩ : L) = ⟨x, hxL⟩ * ⟨y, hyL⟩ * (⟨x, hxL⟩ : L)⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv] at hyP
      exact hyP

theorem map_conj_pullSub (l : L) (P : Subgroup X) :
    (pullSub φ P).map (MulAut.conj (l : G)).toMonoidHom =
      pullSub φ (P.map (MulAut.conj (φ l)).toMonoidHom) := by
  ext x
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mem_pullSub]
  constructor
  · rintro ⟨y, ⟨hyL, hyP⟩, rfl⟩
    refine ⟨mul_mem (mul_mem l.2 hyL) (inv_mem l.2), φ ⟨y, hyL⟩, hyP, ?_⟩
    have : (⟨l * y * (l : G)⁻¹, mul_mem (mul_mem l.2 hyL) (inv_mem l.2)⟩ : L) =
        l * ⟨y, hyL⟩ * l⁻¹ := rfl
    rw [this, map_mul, map_mul, map_inv]
  · rintro ⟨hxL, p, hp, hpx⟩
    have hy : (l : G)⁻¹ * x * l ∈ L := mul_mem (mul_mem (inv_mem l.2) hxL) l.2
    refine ⟨(l : G)⁻¹ * x * l, ⟨hy, ?_⟩, by group⟩
    have : (⟨(l : G)⁻¹ * x * l, hy⟩ : L) = l⁻¹ * ⟨x, hxL⟩ * l := rfl
    rw [this, map_mul, map_mul, map_inv, ← hpx]
    simpa [mul_assoc] using hp

theorem eq_pullSub_of_le {E : Subgroup G} (hE : E ≤ L) :
    E = pullSub φ ((E.subgroupOf L).map φ.toMonoidHom) := by
  ext x
  rw [mem_pullSub]
  constructor
  · intro hx
    exact ⟨hE hx, ⟨x, hE hx⟩, mem_subgroupOf.2 hx, rfl⟩
  · rintro ⟨hxL, y, hy, hyx⟩
    have : y = ⟨x, hxL⟩ := φ.injective hyx
    subst this
    exact hy

end Pull

section Radicals

variable {G : Type*} [Group G] {L : Subgroup G}
variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {b : BilinForm (ZMod 2) V} (hb : b.IsAlt) (hnd : b.Nondegenerate)
  (hV : finrank (ZMod 2) V = 6) (φ : L ≃* bilinIsometryGroup b)

include hb hnd hV

theorem pullSub_radical {W : Submodule (ZMod 2) V} (hW : IsTotallyIsotropic b W)
    (hd : finrank (ZMod 2) W = 3) :
    IsElementaryAbelian 2 (pullSub φ (pointwiseStabilizer b W)) ∧
      Nat.card (pullSub φ (pointwiseStabilizer b W)) = 64 ∧
      centralizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L =
        pullSub φ (pointwiseStabilizer b W) ∧
      normalizer (pullSub φ (pointwiseStabilizer b W) : Set G) ⊓ L =
        pullSub φ (subspaceStabilizer b W) := by
  obtain ⟨h1, h2, h3, h4, -⟩ := pointwiseStabilizer_lagrangian hb hnd hV hW hd
  exact ⟨isElementaryAbelian_pullSub φ h1, by rw [card_pullSub, h2],
    by rw [centralizer_pullSub_inf, h3], by rw [normalizer_pullSub_inf, h4]⟩

theorem elementary_le_of_model {E : Subgroup G} (hEL : E ≤ L) (hE : IsElementaryAbelian 2 E) :
    Nat.card E ≤ 64 ∧ (Nat.card E = 64 → ∃ W : Submodule (ZMod 2) V, IsTotallyIsotropic b W ∧
      finrank (ZMod 2) W = 3 ∧ E = pullSub φ (pointwiseStabilizer b W)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E' := (E.subgroupOf L).map φ.toMonoidHom with hE'
  have hEq : E = pullSub φ E' := eq_pullSub_of_le φ hEL
  have hcard : Nat.card E' = Nat.card E := by
    rw [hEq, card_pullSub]
  have : IsElementaryAbelian 2 (E.subgroupOf L) := IsElementaryAbelian.subgroupOf hEL
  have hE'e : IsElementaryAbelian 2 E' := IsElementaryAbelian.map _
  obtain ⟨h64, heq⟩ := card_le_of_elementary hb hnd hV
    (fun x hx y hy => mul_comm_of_isElementaryAbelian hE'e hx hy)
    (fun x hx => mul_self_of_isElementaryAbelian hE'e hx)
  refine ⟨hcard ▸ h64, fun h => ?_⟩
  obtain ⟨W, hW, hd, hWE⟩ := heq (hcard.trans h)
  exact ⟨W, hW, hd, by rw [hEq, hWE]⟩

theorem exists_radical_mem_of_model {u : G} (huL : u ∈ L) (hu : u ^ 2 = 1) :
    ∃ W : Submodule (ZMod 2) V, IsTotallyIsotropic b W ∧ finrank (ZMod 2) W = 3 ∧
      u ∈ pullSub φ (pointwiseStabilizer b W) := by
  have hu' : φ ⟨u, huL⟩ ^ 2 = 1 := by
    rw [← map_pow]
    have : (⟨u, huL⟩ : L) ^ 2 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hu)
    rw [this, map_one]
  obtain ⟨W, hW, hd, hmem⟩ := exists_lagrangian_mem_pointwiseStabilizer hb hnd hV _ hu'
  exact ⟨W, hW, hd, mem_pullSub.2 ⟨huL, hmem⟩⟩

theorem exists_conj_radical_of_model {W W' : Submodule (ZMod 2) V}
    (hW : IsTotallyIsotropic b W) (hd : finrank (ZMod 2) W = 3) (hW' : IsTotallyIsotropic b W')
    (hd' : finrank (ZMod 2) W' = 3) :
    ∃ l : L, (pullSub φ (pointwiseStabilizer b W)).map (MulAut.conj (l : G)).toMonoidHom =
      pullSub φ (pointwiseStabilizer b W') := by
  obtain ⟨g, -, hg⟩ := exists_conj_pointwiseStabilizer hb hnd hV hW hd hW' hd'
  refine ⟨φ.symm g, ?_⟩
  rw [map_conj_pullSub, MulEquiv.apply_symm_apply, hg]

end Radicals

theorem exists_model_of_lieModel {Q : Type} [Group Q]
    (hQ : CFSG.Blueprint.LieModel Q .PSp 3 2 1) :
    ∃ (V : Type) (_ : AddCommGroup V) (_ : Module (ZMod 2) V) (_ : FiniteDimensional (ZMod 2) V)
      (b : BilinForm (ZMod 2) V), b.IsAlt ∧ b.Nondegenerate ∧ finrank (ZMod 2) V = 6 ∧
        Nonempty (Q ≃* bilinIsometryGroup b) := by
  obtain ⟨e⟩ := nonempty_mulEquiv_statedSp_of_lieModel hQ
  let inst : @Module (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2) _ AddCommGroup.toAddCommMonoid :=
    Pi.module _ _ _
  have hfd : FiniteDimensional (ZMod 2) (Fin 3 ⊕ Fin 3 → ZMod 2) := Module.Finite.pi
  have he : IsSymplecticBasis (pairedSympForm (ZMod 2) 3)
      (Pi.basisFun (ZMod 2) (Fin 3 ⊕ Fin 3)) :=
    toMatrix_pairedSympForm
  exact ⟨Fin 3 ⊕ Fin 3 → ZMod 2, inferInstance, inst, hfd, pairedSympForm (ZMod 2) 3,
    pairedSympForm_isAlt, pairedSympForm_nondegenerate, finrank_standard,
    ⟨e.trans (spCoord he).symm⟩⟩

end CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
