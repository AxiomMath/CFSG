module

public import CFSG.LocalAnalysis.ComponentClassification.SmallLocalAlmostSimple

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup
open scoped commutatorElement

section Action

variable {A : Type*} [Group A]

@[expose] def centralPreimage {L : Type*} [Group L] (R : Subgroup L) [R.Normal] : Subgroup L :=
  (center (L ⧸ R)).comap (QuotientGroup.mk' R)

theorem mem_centralPreimage_iff {L : Type*} [Group L] {R : Subgroup L} [R.Normal] {l : L} :
    l ∈ centralPreimage R ↔ ∀ m : L, ⁅l, m⁆ ∈ R := by
  change QuotientGroup.mk' R l ∈ center (L ⧸ R) ↔ _
  rw [mem_center_iff]
  constructor
  · intro h m
    rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm]
    exact (h _).symm
  · intro h q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective R q
    have hm := (QuotientGroup.eq_one_iff _).mpr (h m)
    rw [← QuotientGroup.mk'_apply, map_commutatorElement,
      commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm.symm

theorem le_centralPreimage {L : Type*} [Group L] (R : Subgroup L) [R.Normal] :
    R ≤ centralPreimage R := fun r hr => by
  change QuotientGroup.mk' R r ∈ center (L ⧸ R)
  rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff r).mpr hr]
  exact one_mem _

theorem map_mulAut_eq_of_characteristic {L : Type*} [Group L] (Z : Subgroup L)
    [Z.Characteristic] (φ : MulAut L) : Z.map (φ : L →* L) = Z :=
  characteristic_iff_map_eq.mp inferInstance φ

instance centralPreimage_characteristic {L : Type*} [Group L] (R : Subgroup L)
    [R.Characteristic] : (centralPreimage R).Characteristic :=
  Characteristic.comap_quotient_mk inferInstance

@[expose] def conjQuotAction (L : Subgroup A) [L.Normal] (Z : Subgroup L) [Z.Characteristic] :
    A →* MulAut (L ⧸ Z) where
  toFun a := QuotientGroup.congr Z Z (MulAut.conjNormal a)
    (map_mulAut_eq_of_characteristic Z (MulAut.conjNormal a))
  map_one' := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [QuotientGroup.congr_mk, map_one]
      rfl
  map_mul' a b := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
        QuotientGroup.congr_mk, map_mul, MulAut.mul_apply]

variable {L : Subgroup A} [L.Normal] {Z : Subgroup L} [Z.Characteristic]

theorem conjQuotAction_mk (a : A) (l : L) :
    conjQuotAction L Z a (l : L ⧸ Z) = ((MulAut.conjNormal a l : L) : L ⧸ Z) :=
  rfl

theorem conjQuotAction_mk' (a : A) (l : L) (hl : a * l * a⁻¹ ∈ L) :
    conjQuotAction L Z a (l : L ⧸ Z) = ((⟨a * l * a⁻¹, hl⟩ : L) : L ⧸ Z) := by
  rw [conjQuotAction_mk]
  exact congrArg _ (Subtype.ext (MulAut.conjNormal_apply a l))

theorem conjQuotAction_coe (l : L) :
    conjQuotAction L Z (l : A) = MulAut.conj (l : L ⧸ Z) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H m =>
    rw [conjQuotAction_mk, MulAut.conjNormal_val, MulAut.conj_apply, MulAut.conj_apply,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]

theorem conjQuotAction_eq_one_iff {a : A} :
    conjQuotAction L Z a = 1 ↔ ∀ l ∈ L, ⁅l, a⁆ ∈ Z.map L.subtype := by
  have key : ∀ l : L, ((MulAut.conjNormal a l : L) : L ⧸ Z) = (l : L ⧸ Z) ↔
      ⁅(l : A), a⁆ ∈ Z.map L.subtype := by
    intro l
    rw [QuotientGroup.eq]
    have hval : ((l * (MulAut.conjNormal a l)⁻¹ : L) : A) = ⁅(l : A), a⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply, commutatorElement_def]
      group
    constructor
    · intro h
      exact ⟨_, (inferInstance : Z.Normal).mem_comm h, hval⟩
    · rintro ⟨z, hz, hzval⟩
      have hz' : z = l * (MulAut.conjNormal a l)⁻¹ := Subtype.ext (hzval.trans hval.symm)
      rw [hz'] at hz
      exact (inferInstance : Z.Normal).mem_comm hz
  constructor
  · intro h l hl
    have hq := congrArg (fun φ : MulAut (L ⧸ Z) => φ ((⟨l, hl⟩ : L) : L ⧸ Z)) h
    simp only [MulAut.one_apply, conjQuotAction_mk] at hq
    exact (key ⟨l, hl⟩).mp hq
  · intro h
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [conjQuotAction_mk, MulAut.one_apply]
      exact (key l).mpr (h l l.2)

theorem commutator_le_of_map_conjQuotAction_eq_bot {D : Subgroup A}
    (hD : D.map (conjQuotAction L Z) = ⊥) : ⁅L, D⁆ ≤ Z.map L.subtype := by
  rw [Subgroup.map_eq_bot_iff] at hD
  rw [commutator_le]
  intro l hl d hd
  exact conjQuotAction_eq_one_iff.mp (hD hd) l hl

end Action

variable {A : Type*} [Group A]

theorem normal_quasisimple_section_automorphism_image [Finite A] (L : Subgroup A) [L.Normal]
    (R : Subgroup L) [R.Characteristic] (hQ : IsQuasisimple (L ⧸ R)) :
    (IsSimpleGroup (L ⧸ centralPreimage R) ∧
        ∃ s t : L ⧸ centralPreimage R, s * t ≠ t * s) ∧
      (centralPreimage R).Characteristic ∧ ((centralPreimage R).map L.subtype).Normal ∧
      (∀ (a : A) (l : L) (hl : a * l * a⁻¹ ∈ L),
        conjQuotAction L (centralPreimage R) a (l : L ⧸ centralPreimage R) =
          ((⟨a * l * a⁻¹, hl⟩ : L) : L ⧸ centralPreimage R)) ∧
      (conjQuotAction L (centralPreimage R)).ker ⊓ L = (centralPreimage R).map L.subtype ∧
      L.map (conjQuotAction L (centralPreimage R)) =
        (MulAut.conj : L ⧸ centralPreimage R →* MulAut (L ⧸ centralPreimage R)).range ∧
      Nonempty (A ⧸ (conjQuotAction L (centralPreimage R)).ker ≃*
        (conjQuotAction L (centralPreimage R)).range) ∧
      (MulAut.conj : L ⧸ centralPreimage R →* MulAut (L ⧸ centralPreimage R)).range ≤
        (conjQuotAction L (centralPreimage R)).range ∧
      generalizedFitting (conjQuotAction L (centralPreimage R)).range =
        (MulAut.conj : L ⧸ centralPreimage R →* MulAut (L ⧸ centralPreimage R)).range.subgroupOf
          (conjQuotAction L (centralPreimage R)).range ∧
      Nonempty
        ((MulAut.conj : L ⧸ centralPreimage R →* MulAut (L ⧸ centralPreimage R)).range.subgroupOf
          (conjQuotAction L (centralPreimage R)).range ≃* L ⧸ centralPreimage R) ∧
      (∀ a : A, ⁅L, zpowers a⁆ = L → conjQuotAction L (centralPreimage R) a ≠ 1) ∧
      ∀ D : Subgroup A, ⁅L, D⁆ = L → D.map (conjQuotAction L (centralPreimage R)) ≠ ⊥ := by
  set Z := centralPreimage R with hZdef
  set α := conjQuotAction L Z with hαdef
  have hmapZ : Z.map (QuotientGroup.mk' R) = center (L ⧸ R) :=
    map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective R) _
  let e : (L ⧸ R) ⧸ center (L ⧸ R) ≃* L ⧸ Z :=
    (QuotientGroup.quotientMulEquivOfEq hmapZ.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient R Z (le_centralPreimage R))
  obtain ⟨-, hsimple, s, t, hst⟩ := hQ
  have : IsSimpleGroup (L ⧸ Z) := e.symm.isSimpleGroup
  have hnonab : ∃ s t : L ⧸ Z, s * t ≠ t * s :=
    ⟨e s, e t, fun h => hst (e.injective (by rw [map_mul, map_mul, h]))⟩
  have hZS : center (L ⧸ Z) = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hnonab).2
  have hinj := SmallLocal.mulAut_conj_injective hZS
  have hαL : L.map α = (MulAut.conj : L ⧸ Z →* MulAut (L ⧸ Z)).range := by
    ext φ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨((⟨a, ha⟩ : L) : L ⧸ Z), (conjQuotAction_coe (⟨a, ha⟩ : L)).symm⟩
    · rintro ⟨q, rfl⟩
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Z q
      exact ⟨(l : A), l.2, conjQuotAction_coe l⟩
  have hInn : (MulAut.conj : L ⧸ Z →* MulAut (L ⧸ Z)).range ≤ α.range := by
    rw [← hαL]
    exact map_le_range _ _
  obtain ⟨-, -, -, hF, he⟩ := SmallLocal.almost_simple_inner_generalized_fitting hnonab α.range hInn
  have hD : ∀ D : Subgroup A, ⁅L, D⁆ = L → D.map α ≠ ⊥ := by
    intro D hLD hDα
    have hle := commutator_le_of_map_conjQuotAction_eq_bot hDα
    rw [hLD] at hle
    apply hst
    have hZtop : ∀ q : L ⧸ Z, q = 1 := by
      intro q
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective Z q
      obtain ⟨z, hz, hzl⟩ := hle l.2
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ← Subtype.ext hzl]
      exact hz
    have hs : e s = 1 := hZtop _
    have ht : e t = 1 := hZtop _
    rw [← e.symm_apply_apply s, ← e.symm_apply_apply t, hs, ht]
  refine ⟨⟨inferInstance, hnonab⟩, inferInstance, inferInstance, fun a l hl => ?_, ?_, hαL,
    ⟨QuotientGroup.quotientKerEquivRange α⟩, hInn, hF, he, fun a hLa hαa => ?_, hD⟩
  · exact conjQuotAction_mk' a l hl
  · ext a
    constructor
    · rintro ⟨hk, ha⟩
      have h1 : MulAut.conj ((⟨a, ha⟩ : L) : L ⧸ Z) = MulAut.conj 1 := by
        rw [← conjQuotAction_coe, map_one]
        exact hk
      have h2 := (QuotientGroup.eq_one_iff _).mp (hinj h1)
      exact ⟨⟨a, ha⟩, h2, rfl⟩
    · rintro ⟨z, hz, rfl⟩
      refine ⟨?_, z.2⟩
      change α (z : A) = 1
      rw [hαdef, conjQuotAction_coe, (QuotientGroup.eq_one_iff z).mpr hz, map_one]
  · apply hD (zpowers a) hLa
    rw [MonoidHom.map_zpowers, hαa, zpowers_one_eq_bot]

end CFSG.ComponentClassification.UnbalancingLocal
