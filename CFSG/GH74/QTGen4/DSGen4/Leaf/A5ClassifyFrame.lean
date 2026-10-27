module

public import CFSG.GH74.QTGen4.DSGen4.Defs

public section

namespace CFSG.GH74.QTGen4.DSGen4

open scoped commutatorElement Matrix

variable {G : Type} [Group G]

abbrev glMat (g : GL (Fin 4) (ZMod 2)) : Matrix (Fin 4) (Fin 4) (ZMod 2) := (g : Matrix (Fin 4) (Fin 4) (ZMod 2))

structure ElemFrame (P E K : Subgroup G) where
  φ : ↥E →* Multiplicative (Fin 4 → ZMod 2)
  M : ↥P →* GL (Fin 4) (ZMod 2)
  surj : Function.Surjective φ
  ker : ∀ e : ↥E, φ e = 1 ↔ (e : G) ∈ K
  act : ∀ (p : ↥P) (e e' : ↥E), (e' : G) = (p : G) * (e : G) * (p : G)⁻¹ →
    glMat (M p) *ᵥ Multiplicative.toAdd (φ e) = Multiplicative.toAdd (φ e')

namespace ElemFrame

variable {P E K : Subgroup G}

theorem glMat_mul_inv (g : GL (Fin 4) (ZMod 2)) : glMat g * glMat g⁻¹ = 1 := Units.mul_inv g

theorem glMat_inv_mul (g : GL (Fin 4) (ZMod 2)) : glMat g⁻¹ * glMat g = 1 := Units.inv_mul g

@[expose] def conj (F : ElemFrame P E K) (g : GL (Fin 4) (ZMod 2)) : ElemFrame P E K where
  φ :=
    { toFun := fun e => Multiplicative.ofAdd (glMat g *ᵥ Multiplicative.toAdd (F.φ e))
      map_one' := by simp
      map_mul' := fun a b => by
        simp [Matrix.mulVec_add] }
  M :=
    { toFun := fun p => g * F.M p * g⁻¹
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_assoc] }
  surj := by
    intro y
    obtain ⟨e, he⟩ := F.surj (Multiplicative.ofAdd ((glMat g⁻¹) *ᵥ Multiplicative.toAdd y))
    refine ⟨e, ?_⟩
    simp only [MonoidHom.coe_mk, OneHom.coe_mk, he, toAdd_ofAdd]
    rw [Matrix.mulVec_mulVec, glMat_mul_inv, Matrix.one_mulVec]
    rfl
  ker := by
    intro e
    rw [← F.ker e]
    simp only [MonoidHom.coe_mk, OneHom.coe_mk]
    constructor
    · intro h
      have h' := congrArg (fun v => glMat g⁻¹ *ᵥ v) (congrArg Multiplicative.toAdd h)
      simp only [toAdd_ofAdd, toAdd_one, Matrix.mulVec_zero] at h'
      rw [Matrix.mulVec_mulVec, glMat_inv_mul, Matrix.one_mulVec] at h'
      exact congrArg Multiplicative.ofAdd h'
    · intro h
      rw [h]; simp
  act := by
    intro p e e' he'
    have h := F.act p e e' he'
    show glMat (g * F.M p * g⁻¹) *ᵥ (glMat g *ᵥ Multiplicative.toAdd (F.φ e)) =
      glMat g *ᵥ Multiplicative.toAdd (F.φ e')
    rw [← h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
    congr 1
    simp only [glMat, Units.val_mul, mul_assoc, Units.inv_mul, mul_one]

theorem conj_M (F : ElemFrame P E K) (g : GL (Fin 4) (ZMod 2)) (p : ↥P) :
    (F.conj g).M p = g * F.M p * g⁻¹ := rfl

end ElemFrame

section Existence

theorem IsElemSec.normal_subgroupOf {K E : Subgroup G} (h : IsElemSec K E) :
    (K.subgroupOf E).Normal := by
  refine ⟨fun k hk e => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hk ⊢
  have hc : ⁅(e : G), (k : G)⁆ ∈ K :=
    h.2.1 (Subgroup.commutator_mem_commutator e.2 k.2)
  have : ((e * k * e⁻¹ : ↥E) : G) = ⁅(e : G), (k : G)⁆ * (k : G) := by
    simp [commutatorElement_def]
  rw [this]
  exact K.mul_mem hc hk

@[expose] noncomputable def conjE {P E : Subgroup G} (hPE : P ≤ Subgroup.normalizer (E : Set G)) (p : ↥P) :
    ↥E ≃* ↥E :=
  ((MulAut.conj (p : G)).subgroupMap E).trans
    (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp (hPE p.2)))

theorem coe_conjE {P E : Subgroup G} (hPE : P ≤ Subgroup.normalizer (E : Set G)) (p : ↥P)
    (x : ↥E) : ((conjE hPE p x : ↥E) : G) = p * x * (p : G)⁻¹ := rfl

theorem map_conjE_subgroupOf {P E K : Subgroup G} (hPE : P ≤ Subgroup.normalizer (E : Set G))
    (hPK : P ≤ Subgroup.normalizer (K : Set G)) (p : ↥P) :
    (K.subgroupOf E).map (conjE hPE p).toMonoidHom = K.subgroupOf E := by
  ext x
  have hk := Subgroup.mem_normalizer_iff.mp (hPK p.2)
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    rw [Subgroup.mem_subgroupOf]
    exact (hk _).mp hy
  · intro hx
    refine ⟨(conjE hPE p).symm x, ?_, (conjE hPE p).apply_symm_apply x⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hx
    have h1 := coe_conjE hPE p ((conjE hPE p).symm x)
    rw [(conjE hPE p).apply_symm_apply] at h1
    rw [hk, ← h1]
    exact hx

@[expose] noncomputable def actV {P E K : Subgroup G} [(K.subgroupOf E).Normal]
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (p : ↥P) : (↥E ⧸ K.subgroupOf E) ≃* (↥E ⧸ K.subgroupOf E) :=
  QuotientGroup.congr (K.subgroupOf E) (K.subgroupOf E) (conjE hPE p)
    (map_conjE_subgroupOf hPE hPK p)

@[expose] noncomputable def actHom {P E K : Subgroup G} [(K.subgroupOf E).Normal]
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G)) :
    ↥P →* MulAut (↥E ⧸ K.subgroupOf E) where
  toFun := actV hPE hPK
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (Subtype.ext (by simp [coe_conjE]))
  map_mul' := by
    intro p q
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => exact congrArg QuotientGroup.mk (Subtype.ext (by simp [coe_conjE, mul_assoc]))

theorem actHom_mk {P E K : Subgroup G} [(K.subgroupOf E).Normal]
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (p : ↥P) (x : ↥E) : actHom hPE hPK p (QuotientGroup.mk x) = QuotientGroup.mk (conjE hPE p x) :=
  rfl

theorem exists_elemFrame [Finite G] {P E K : Subgroup G} (hs : IsElemSec K E) (hc : K.relIndex E = 16)
    (hPE : P ≤ Subgroup.normalizer (E : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G)) :
    Nonempty (ElemFrame P E K) := by
  haveI : (K.subgroupOf E).Normal := hs.normal_subgroupOf
  have hcomm : ∀ a b : ↥E ⧸ K.subgroupOf E, a * b = b * a := by
    intro a b
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have hc : ⁅((y : ↥E) : G)⁻¹, ((x : ↥E) : G)⁻¹⁆ ∈ K :=
          hs.2.1 (Subgroup.commutator_mem_commutator (E.inv_mem y.2) (E.inv_mem x.2))
        have : ((((x * y)⁻¹ * (y * x) : ↥E)) : G) = ⁅((y : ↥E) : G)⁻¹, ((x : ↥E) : G)⁻¹⁆ := by
          simp [commutatorElement_def, mul_assoc]
        rw [this]; exact hc
  have hpow : ∀ a : ↥E ⧸ K.subgroupOf E, a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H x =>
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hs.2.2 _ x.2
  have hcard : Nat.card (↥E ⧸ K.subgroupOf E) = 2 ^ 4 := by
    have : Nat.card (↥E ⧸ K.subgroupOf E) = K.relIndex E := rfl
    rw [this, hc]; norm_num
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) hcomm hpow hcard
  refine ⟨{
    φ := e.toMonoidHom.comp (QuotientGroup.mk' (K.subgroupOf E))
    M := (CFSG.SectionRank.Ccomm.elemAutEquivGL e).toMonoidHom.comp (actHom hPE hPK)
    surj := ?_
    ker := ?_
    act := ?_ }⟩
  · exact e.surjective.comp (QuotientGroup.mk'_surjective _)
  · intro x
    simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
      QuotientGroup.mk'_apply, EmbeddingLike.map_eq_one_iff, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
  · intro p x x' hx'
    have h := CFSG.SectionRank.Ccomm.elemAutEquivGL_mulVec e (actHom hPE hPK p)
      (QuotientGroup.mk x)
    have hxx : conjE hPE p x = x' := Subtype.ext (by rw [coe_conjE, hx'])
    simpa [actHom_mk, hxx] using h

end Existence

end CFSG.GH74.QTGen4.DSGen4
