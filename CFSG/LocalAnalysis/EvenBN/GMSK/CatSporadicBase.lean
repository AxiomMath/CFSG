module

public import CFSG.LocalAnalysis.EvenBN.GMSK.FixedRoot
public import CFSG.LocalAnalysis.EvenBN.GMSK.SL2Facts
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporAut
public import CFSG.LocalAnalysis.ComponentClassification.RestrictedSporBasic
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoAutCard
public import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Walter.PSL2Facts.Even
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents

public section

namespace CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic

open Subgroup CFSG.Blueprint
open CFSG.ComponentClassification.RestrictedStd.Spor (CompsSatisfy IsoInvariant)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

@[expose] def IsRankOneFixedRoot {D : Type} [Group D] (n : ℕ) (α : MulAut D) (S : Subgroup D) :
    Prop :=
  2 ≤ n ∧ orderOf α = 2 ∧ S ≤ α.toMonoidHom.eqLocus (MonoidHom.id D) ∧
    (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))).Normal ∧
    (∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ^ n ∧
      Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K)) ∧ FixedRootRankOne α S

@[expose] def SporadicFixedRootFree (s : TauCeti.SporadicName) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → NativeSporadic.IsSporadic D s →
    ∀ (n : ℕ) (α : MulAut D) (S : Subgroup D), ¬ IsRankOneFixedRoot n α S

@[expose] def SporadicFixedRootFieldFour (s : TauCeti.SporadicName) : Prop :=
  ∀ (D : Type) [Group D] [Finite D], IsSimpleGroup D → NativeSporadic.IsSporadic D s →
    ∀ (n : ℕ) (α : MulAut D) (S : Subgroup D), IsRankOneFixedRoot n α S → n = 2

section SL2

variable {K : Type} [Field K] [Fintype K] {n : ℕ}

theorem charP_two_of_card (hn : 1 ≤ n) (hK : Fintype.card K = 2 ^ n) : CharP K 2 :=
  CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn
    (by rw [Nat.card_eq_fintype_card, hK])

theorem card_sl2 (hK : Fintype.card K = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, Nat.card_eq_fintype_card, hK]

theorem three_dvd_sl2Order (n : ℕ) : 3 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have h4 : (2 ^ n) ^ 2 % 3 = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, Nat.pow_mod]
    norm_num
  have h1 : 1 ≤ (2 ^ n) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  exact Dvd.dvd.mul_left (by omega) _

theorem sl2_center_eq_bot (hn : 1 ≤ n) (hK : Fintype.card K = 2 ^ n) :
    center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ := by
  have : CharP K 2 := charP_two_of_card hn hK
  exact CFSG.Walter.sl2_center_eq_bot_of_charTwo

theorem sl2_isSimple (hn : 2 ≤ n) (hK : Fintype.card K = 2 ^ n) :
    IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := by
  refine GMSK.sl2_isSimpleGroup (GMSK.two_eq_zero_of_card (by omega) hK) ?_
  rw [hK]
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem nonempty_sl2_mulEquiv_psl2GF (hn : 1 ≤ n) (hK : Fintype.card K = 2 ^ n) :
    Nonempty (Matrix.SpecialLinearGroup (Fin 2) K ≃* CFSG.AGLEmbedding.PSL2GF 2 n) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hG : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card 2 n (by omega)]
  let f : K ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by rw [hK, hG])
  let e : Matrix.SpecialLinearGroup (Fin 2) K ≃* Matrix.SpecialLinearGroup (Fin 2)
      (GaloisField 2 n) :=
    { toFun := Matrix.SpecialLinearGroup.map f.toRingHom
      invFun := Matrix.SpecialLinearGroup.map f.symm.toRingHom
      left_inv := fun A => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]
      right_inv := fun A => by
        ext i j
        simp [Matrix.SpecialLinearGroup.map_apply_coe]
      map_mul' := fun A B => map_mul _ A B }
  exact ⟨e.trans (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).symm⟩

theorem card_mulAut_sl2 (hn : 1 ≤ n) (hK : Fintype.card K = 2 ^ n) :
    Nat.card (MulAut (Matrix.SpecialLinearGroup (Fin 2) K)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := nonempty_sl2_mulEquiv_psl2GF hn hK
  rw [Nat.card_congr (MulAut.congr e).toEquiv, CFSG.AGLEmbedding.card_mulAut_psl2GF 2 n hn]

end SL2

theorem card_dvd_of_normal_sl2 {C : Type*} [Group C] [Finite C] (N : Subgroup C) [N.Normal]
    {K : Type} [Field K] [Fintype K] {n : ℕ} (hn : 1 ≤ n) (hK : Fintype.card K = 2 ^ n)
    (e : N ≃* Matrix.SpecialLinearGroup (Fin 2) K) (P : Subgroup C) (hP : IsPGroup 2 P) :
    Nat.card P ∣ Nat.card ↥(P ⊓ centralizer (N : Set C)) * (2 ^ n * n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set f : P →* MulAut N := (MulAut.conjNormal : C →* MulAut N).comp P.subtype with hf
  have hker : f.ker.map P.subtype = P ⊓ centralizer (N : Set C) := by
    ext x
    simp only [mem_map, MonoidHom.mem_ker, mem_inf, mem_centralizer_iff]
    constructor
    · rintro ⟨y, hy, rfl⟩
      refine ⟨y.2, fun m hm => ?_⟩
      have h1 := congrArg (fun φ : MulAut N => ((φ ⟨m, hm⟩ : N) : C)) hy
      simp only [hf, MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply] at h1
      calc m * (y : C) = (y : C) * m * (y : C)⁻¹ * y := by rw [h1]
        _ = y * m := by group
    · rintro ⟨hxP, hx⟩
      refine ⟨⟨x, hxP⟩, ?_, rfl⟩
      refine MulEquiv.ext fun m => Subtype.ext ?_
      simp only [hf, MonoidHom.comp_apply, coe_subtype, MulAut.conjNormal_apply,
        MulAut.one_apply]
      rw [← hx m m.2, mul_inv_cancel_right]
  have hkercard : Nat.card f.ker = Nat.card ↥(P ⊓ centralizer (N : Set C)) := by
    rw [← hker, card_map_of_injective P.subtype_injective]
  have hcard : Nat.card P = Nat.card f.ker * Nat.card f.range := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  have hp : IsPGroup 2 f.range := hP.of_surjective f.rangeRestrict f.rangeRestrict_surjective
  have : Finite (MulAut N) :=
    Finite.of_injective (fun φ : MulAut N => (φ : N → N)) DFunLike.coe_injective
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hdvd : Nat.card f.range ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) * n := by
    rw [← card_mulAut_sl2 hn hK, ← Nat.card_congr (MulAut.congr e).toEquiv]
    exact Subgroup.card_subgroup_dvd_card _
  have hcop : Nat.Coprime (2 ^ k) ((2 ^ n) ^ 2 - 1) := by
    have h : Nat.Coprime ((2 ^ n) ^ 2) ((2 ^ n) ^ 2 - 1) :=
      (Nat.coprime_self_sub_right (Nat.one_le_pow _ _ (by positivity))).mpr
        (Nat.coprime_one_right _)
    exact (h.coprime_dvd_left (dvd_pow (dvd_pow_self 2 (by omega)) two_ne_zero)).pow_left k
  have hrange : Nat.card f.range ∣ 2 ^ n * n := by
    rw [hk]
    rw [hk, show 2 ^ n * ((2 ^ n) ^ 2 - 1) * n = ((2 ^ n) ^ 2 - 1) * (2 ^ n * n) by ring] at hdvd
    exact hcop.dvd_of_dvd_mul_left hdvd
  rw [hcard, hkercard]
  exact Nat.mul_dvd_mul_left _ hrange

section FixedRoot

variable {D : Type} [Group D] {n : ℕ} {α : MulAut D} {S : Subgroup D}

theorem eqLocus_eq_fixSub (α : MulAut D) :
    α.toMonoidHom.eqLocus (MonoidHom.id D) = CFSG.Sporadic.Schreier.fixSub α := by
  ext x
  rfl

theorem eqLocus_conj (t : D) :
    (MulAut.conj t).toMonoidHom.eqLocus (MonoidHom.id D) = centralizer {t} := by
  ext y
  rw [mem_centralizer_singleton_iff]
  change t * y * t⁻¹ = y ↔ y * t = t * y
  constructor
  · intro h
    calc y * t = t * y * t⁻¹ * t := by rw [h]
      _ = t * y := by group
  · intro h
    calc t * y * t⁻¹ = y * t * t⁻¹ := by rw [h]
      _ = y := by group

theorem IsRankOneFixedRoot.exists_field (h : IsRankOneFixedRoot n α S) :
    ∃ (K : Type) (_ : Field K) (_ : Fintype K), Fintype.card K = 2 ^ n ∧
      Nonempty (S ≃* Matrix.SpecialLinearGroup (Fin 2) K) :=
  h.2.2.2.2.1

theorem IsRankOneFixedRoot.isSimpleGroup (h : IsRankOneFixedRoot n α S) : IsSimpleGroup S := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h.exists_field
  have := sl2_isSimple h.1 hK
  exact φ.isSimpleGroup

theorem IsRankOneFixedRoot.nonabelian (h : IsRankOneFixedRoot n α S) :
    ∃ a b : S, a * b ≠ b * a := by
  obtain ⟨K, _, _, -, ⟨φ⟩⟩ := h.exists_field
  obtain ⟨a, b, hab⟩ := GMSK.sl2_exists_mul_ne (K := K)
  refine ⟨φ.symm a, φ.symm b, fun h' => hab ?_⟩
  simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg φ h'

theorem IsRankOneFixedRoot.card (h : IsRankOneFixedRoot n α S) :
    Nat.card S = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h.exists_field
  rw [Nat.card_congr φ.toEquiv, card_sl2 hK]

theorem IsRankOneFixedRoot.center_eq_bot (h : IsRankOneFixedRoot n α S) : center S = ⊥ := by
  have := h.isSimpleGroup
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup h.nonabelian).2

theorem IsRankOneFixedRoot.card_quotient_center (h : IsRankOneFixedRoot n α S) :
    Nat.card (S ⧸ center S) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [← h.card]
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq h.center_eq_bot).trans
    QuotientGroup.quotientBot).toEquiv

theorem IsRankOneFixedRoot.isComponent (h : IsRankOneFixedRoot n α S) :
    CFSG.IsComponent (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) := by
  have hs := h.isSimpleGroup
  have e := Subgroup.subgroupOfEquivOfLe h.2.2.1
  have : IsSimpleGroup (S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D))) :=
    e.isSimpleGroup
  obtain ⟨a, b, hab⟩ := h.nonabelian
  have hnab : ∃ x y : S.subgroupOf (α.toMonoidHom.eqLocus (MonoidHom.id D)), x * y ≠ y * x := by
    refine ⟨e.symm a, e.symm b, fun h' => hab ?_⟩
    simpa only [map_mul, MulEquiv.apply_symm_apply] using congrArg e h'
  exact ⟨(CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).1, h.2.2.2.1.isSubnormal⟩

theorem IsRankOneFixedRoot.isComponentOf (h : IsRankOneFixedRoot n α S) :
    CFSG.Assembly.IsComponentOf S (α.toMonoidHom.eqLocus (MonoidHom.id D)) :=
  (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf h.2.2.1).2
    h.isComponent

theorem IsRankOneFixedRoot.false_of_comps (h : IsRankOneFixedRoot n α S)
    {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q)
    (hQSL : ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Q (Matrix.SpecialLinearGroup (Fin 2) K))
    (hC : CompsSatisfy (α.toMonoidHom.eqLocus (MonoidHom.id D)) Q) : False := by
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h.exists_field
  exact hQSL K hK (hQ _ _ (φ.symm.trans (Subgroup.subgroupOfEquivOfLe h.2.2.1).symm)
    (hC _ h.isComponent))

theorem exists_involution_of_mem_inner (hZ : center D = ⊥) (hα : orderOf α = 2)
    (hin : α ∈ inner D) : ∃ t : D, orderOf t = 2 ∧ MulAut.conj t = α := by
  obtain ⟨t, rfl⟩ := hin
  have ht2 : t ^ 2 = 1 := by
    have hc : t ^ 2 ∈ center D := by
      rw [mem_center_iff]
      intro y
      have hy := congrArg (fun β : MulAut D => β y) (pow_orderOf_eq_one (MulAut.conj t))
      rw [hα] at hy
      simp only [← map_pow, MulAut.conj_apply, MulAut.one_apply] at hy
      calc y * t ^ 2 = t ^ 2 * y * (t ^ 2)⁻¹ * t ^ 2 := by rw [hy]
        _ = t ^ 2 * y := by group
    rw [hZ, mem_bot] at hc
    exact hc
  have ht1 : t ≠ 1 := by
    rintro rfl
    rw [map_one, orderOf_one] at hα
    omega
  exact ⟨t, orderOf_eq_prime ht2 ht1, rfl⟩

theorem IsRankOneFixedRoot.card_dvd [Finite D] (h : IsRankOneFixedRoot n α S) {P : Subgroup D}
    (hPα : P ≤ α.toMonoidHom.eqLocus (MonoidHom.id D)) (hP : IsPGroup 2 P) :
    Nat.card P ∣ 2 * (2 ^ n * n) ∧ (α ∉ inner D → Nat.card P ∣ 2 ^ n * n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D) with hCdef
  obtain ⟨K, _, _, hK, ⟨φ⟩⟩ := h.exists_field
  set N := S.subgroupOf C
  have : N.Normal := h.2.2.2.1
  let e : N ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    (Subgroup.subgroupOfEquivOfLe h.2.2.1).trans φ
  set P' := P.subgroupOf C
  have eP : P' ≃* P := Subgroup.subgroupOfEquivOfLe hPα
  have hP' : IsPGroup 2 P' := hP.of_equiv eP.symm
  have hdvd := card_dvd_of_normal_sl2 N (by have := h.1; omega) hK e P' hP'
  rw [Nat.card_congr eP.toEquiv] at hdvd
  set Q := (P' ⊓ centralizer (N : Set C)).map C.subtype with hQdef
  have hQle : Q ≤ C ⊓ centralizer (S : Set D) := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.2 ⟨x.2, ?_⟩
    rw [mem_centralizer_iff]
    intro s hs
    have h1 := (mem_centralizer_iff.1 (mem_inf.1 hx).2) ⟨s, h.2.2.1 hs⟩
      (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hs)
    exact congrArg Subtype.val h1
  have hQp : IsPGroup 2 Q := (hP'.to_le inf_le_left).map C.subtype
  have hQcard : Nat.card Q = Nat.card ↥(P' ⊓ centralizer (N : Set C)) :=
    card_map_of_injective C.subtype_injective
  obtain ⟨hle, hout⟩ := h.2.2.2.2.2 Q hQle hQp
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQp
  have hQ2 : Nat.card Q ∣ 2 := by
    rw [hk] at hle ⊢
    rcases k with _ | _ | k
    · exact one_dvd _
    · exact dvd_rfl
    · exfalso
      have : 4 ≤ 2 ^ (k + 1 + 1) :=
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ (k + 1 + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
  rw [← hQcard] at hdvd
  refine ⟨hdvd.trans (Nat.mul_dvd_mul_right hQ2 _), fun hα => ?_⟩
  rw [hout hα, card_bot, one_mul] at hdvd
  exact hdvd

theorem IsRankOneFixedRoot.two_pow_dvd [Finite D] (h : IsRankOneFixedRoot n α S) {a : ℕ}
    (ha : 2 ^ a ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D))) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) ∧
      2 ^ a ∣ 2 * (2 ^ n * n) ∧ (α ∉ inner D → 2 ^ a ∣ 2 ^ n * n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := α.toMonoidHom.eqLocus (MonoidHom.id D)
  obtain ⟨P, hP⟩ := Sylow.exists_subgroup_card_pow_prime (G := C) 2 ha
  have hPp : IsPGroup 2 P := IsPGroup.of_card hP
  have hPD := h.card_dvd (P := P.map C.subtype) (map_subtype_le P) (hPp.map C.subtype)
  rw [card_map_of_injective C.subtype_injective, hP] at hPD
  refine ⟨?_, hPD⟩
  rw [← h.card, ← Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.2.2.1).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

theorem IsRankOneFixedRoot.center_eq_bot_of_isSimpleGroup (hD : IsSimpleGroup D)
    (h : IsRankOneFixedRoot n α S) : center D = ⊥ := by
  obtain ⟨a, b, hab⟩ := h.nonabelian
  have hnab : ∃ x y : D, x * y ≠ y * x :=
    ⟨a, b, fun h' => hab (Subtype.ext (by simpa only [coe_mul] using h'))⟩
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2

theorem mul_self_eq_one_of_orderOf_eq_two {G : Type*} [Group G] {β : G} (h : orderOf β = 2) :
    β * β = 1 := by
  rw [← sq, ← h, pow_orderOf_eq_one]

theorem IsRankOneFixedRoot.false_of_inner_comps (hD : IsSimpleGroup D)
    (h : IsRankOneFixedRoot n α S) (hin : α ∈ inner D) {Q : (Y : Type) → [Group Y] → Prop}
    (hQ : IsoInvariant Q)
    (hQSL : ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Q (Matrix.SpecialLinearGroup (Fin 2) K))
    (hC : ∀ t : D, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set D)) Q) : False := by
  obtain ⟨t, ht, rfl⟩ := exists_involution_of_mem_inner (h.center_eq_bot_of_isSimpleGroup hD)
    h.2.1 hin
  exact h.false_of_comps hQ hQSL
    (CompsSatisfy.of_mulEquiv hQ (MulEquiv.subgroupCongr (eqLocus_conj t)) (hC t ht))

theorem IsRankOneFixedRoot.false_of_outer_comps (h : IsRankOneFixedRoot n α S)
    (hout : α ∉ inner D) {Q : (Y : Type) → [Group Y] → Prop} (hQ : IsoInvariant Q)
    (hQSL : ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Q (Matrix.SpecialLinearGroup (Fin 2) K))
    (hC : ∀ β : MulAut D, orderOf β = 2 → β ∉ inner D →
      CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Q) : False :=
  h.false_of_comps hQ hQSL
    (CompsSatisfy.of_mulEquiv hQ (MulEquiv.subgroupCongr (eqLocus_eq_fixSub α)) (hC α h.2.1 hout))

theorem mem_inner_of_mulEquiv' {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (hH : ∀ β : MulAut H, β ∈ inner H) (β : MulAut G) : β ∈ inner G := by
  by_contra hβ
  exact CFSG.ComponentClassification.RestrictedStd.Spor.transportAut_not_mem_inner e hβ
    (hH _)

theorem card_eqLocus_congr {T : Type*} [Group T] (e : D ≃* T) (α : MulAut D) :
    Nat.card (α.toMonoidHom.eqLocus (MonoidHom.id D)) =
      Nat.card ((MulAut.congr e α).toMonoidHom.eqLocus (MonoidHom.id T)) := by
  refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun x => ?_)
  change α x = x ↔ e (α (e.symm (e x))) = e x
  rw [MulEquiv.symm_apply_apply, e.injective.eq_iff]

theorem congr_mem_inner_iff {T : Type*} [Group T] (e : D ≃* T) (α : MulAut D) :
    MulAut.congr e α ∈ inner T ↔ α ∈ inner D := by
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨e.symm y, ?_⟩
    apply (MulAut.congr e).injective
    rw [← hy, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj,
      MulEquiv.apply_symm_apply]
  · rintro ⟨x, rfl⟩
    exact ⟨e x, (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e x).symm⟩

theorem orderOf_congr {T : Type*} [Group T] (e : D ≃* T) (α : MulAut D) :
    orderOf (MulAut.congr e α) = orderOf α :=
  MulEquiv.orderOf_eq (MulAut.congr e) α

end FixedRoot

theorem sporadicFixedRootFree_of_comps {s : TauCeti.SporadicName}
    {Qi Qo : (Y : Type) → [Group Y] → Prop} (hQi : IsoInvariant Qi) (hQo : IsoInvariant Qo)
    (hSLi : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Qi (Matrix.SpecialLinearGroup (Fin 2) K))
    (hSLo : ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Qo (Matrix.SpecialLinearGroup (Fin 2) K))
    (hin : ∀ (G : Type) [Group G] [Finite G], Nonempty (G ≃* NativeSporadic.Carrier s) →
      ∀ t : G, orderOf t = 2 → CompsSatisfy (centralizer ({t} : Set G)) Qi)
    (hout : ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G →
      Nonempty (G ≃* NativeSporadic.Carrier s) → ∀ β : MulAut G, orderOf β = 2 → β ∉ inner G →
        CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Qo) :
    SporadicFixedRootFree s := by
  intro D _ _ hD hs n α S h
  by_cases hα : α ∈ inner D
  · exact h.false_of_inner_comps hD hα hQi (hSLi n h.1) (hin D hs)
  · exact h.false_of_outer_comps hα hQo (hSLo n h.1) (hout D hD hs)

theorem outer_comps_of_forall_inner {s : TauCeti.SporadicName}
    (hinner : ∀ β : MulAut (NativeSporadic.Carrier s), β ∈ inner (NativeSporadic.Carrier s))
    (Q : (Y : Type) → [Group Y] → Prop) (G : Type) [Group G] [Finite G] (_ : IsSimpleGroup G)
    (hG : Nonempty (G ≃* NativeSporadic.Carrier s)) (β : MulAut G) (_ : orderOf β = 2)
    (hβ : β ∉ inner G) : CompsSatisfy (CFSG.Sporadic.Schreier.fixSub β) Q :=
  absurd (mem_inner_of_mulEquiv' hG.some hinner β) hβ

theorem IsRankOneFixedRoot.sl2Order_dvd_card {D : Type} [Group D] {n : ℕ} {α : MulAut D}
    {S : Subgroup D} (h : IsRankOneFixedRoot n α S) :
    2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ Nat.card D := by
  rw [← h.card]
  exact Subgroup.card_subgroup_dvd_card S

theorem sporadicFixedRootFieldFour_of_card {s : TauCeti.SporadicName} {N : ℕ}
    (hN : Nat.card (NativeSporadic.Carrier s) = N)
    (hcheck : ∀ n : ℕ, 2 ≤ n → 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ N → n = 2) :
    SporadicFixedRootFieldFour s := by
  intro D _ _ _ hs n α S h
  obtain ⟨e⟩ := hs
  refine hcheck n h.1 ?_
  rw [← hN, ← Nat.card_congr e.toEquiv]
  exact h.sl2Order_dvd_card

theorem lt_of_sl2Order_dvd {n N B : ℕ} (hN : 0 < N) (hB : N < 2 ^ B)
    (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) ∣ N) : n < B := by
  have h1 : 2 ^ n ≤ N := Nat.le_of_dvd hN ((dvd_mul_right _ _).trans h)
  exact (Nat.pow_lt_pow_iff_right (by norm_num)).1 (h1.trans_lt hB)

theorem lt_of_sl2Order_eq {n N B : ℕ} (hn : 1 ≤ n) (hB : N < 2 ^ B)
    (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) = N) : n < B := by
  have h2 : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h4 : 1 < (2 ^ n) ^ 2 := by nlinarith
  have hN : 0 < N := by
    rw [← h]
    exact Nat.mul_pos (by positivity) (by omega)
  exact lt_of_sl2Order_dvd hN hB (dvd_of_eq h)

theorem sl2Order_ne_of_check {N B : ℕ} (hB : N < 2 ^ B)
    (hcheck : ∀ n < B, 2 ≤ n → 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ N) :
    ∀ n : ℕ, 2 ≤ n → 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ N :=
  fun n hn h => hcheck n (lt_of_sl2Order_eq (by omega) hB h) hn h

theorem sl2_not_not_three_dvd {K : Type} [Field K] [Fintype K] {n : ℕ}
    (hK : Fintype.card K = 2 ^ n) : ¬ ¬ 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K) := by
  rw [card_sl2 hK]
  exact not_not_intro (three_dvd_sl2Order n)

theorem card_sl2_quotient_center {K : Type} [Field K] [Fintype K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Fintype.card K = 2 ^ n) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸ center (Matrix.SpecialLinearGroup (Fin 2) K)) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  rw [← card_sl2 hK]
  exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq (sl2_center_eq_bot hn hK)).trans
    QuotientGroup.quotientBot).toEquiv

theorem sl2_fails_card_quotient_center_mem {N : Set ℕ}
    (hN : ∀ n : ℕ, 2 ≤ n → 2 ^ n * ((2 ^ n) ^ 2 - 1) ∉ N) :
    ∀ n : ℕ, 2 ≤ n → ∀ (K : Type) [Field K] [Fintype K], Fintype.card K = 2 ^ n →
      ¬ Nat.card (Matrix.SpecialLinearGroup (Fin 2) K ⧸
        center (Matrix.SpecialLinearGroup (Fin 2) K)) ∈ N := by
  intro n hn K _ _ hK h
  rw [card_sl2_quotient_center (by omega) hK] at h
  exact hN n hn h

theorem card_quotient_center_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card (X ⧸ center X) = Nat.card (Y ⧸ center Y) :=
  Nat.card_congr (QuotientGroup.congr (center X) (center Y) e (Subgroup.map_center_eq e)).toEquiv

end CFSG.LocalAnalysis.EvenBN.GMSK.Sporadic
