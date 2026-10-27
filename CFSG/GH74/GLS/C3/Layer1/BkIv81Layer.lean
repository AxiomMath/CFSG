module

public import CFSG.ClassicalInvolution.LocalComponent.Layer
public import CFSG.ClassicalInvolution.LBalance.Main
public import CFSG.LocalAnalysis.ComponentClassification.UGSChainKGroupTwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrSourceChange
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.GLS.C3.Layer1.Bk

open Subgroup CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
open CFSG.GH74.GLS
open scoped commutatorElement

section Copy

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem fixedSubgroup_conj_eq_centralizer' (z : X) :
    FixedCommutingProduct.fixedSubgroup (MulAut.conj z) = Subgroup.centralizer ({z} : Set X) := by
  ext m
  change z * m * z⁻¹ = m ↔ m ∈ Subgroup.centralizer ({z} : Set X)
  rw [Subgroup.mem_centralizer_singleton_iff, mul_inv_eq_iff_eq_mul]
  exact ⟨fun h => h.symm, fun h => h.symm⟩

theorem twoComponent_le_or_le_of_le_sup' {A B : Subgroup X} (hAsub : IsSubnormal A ⊤)
    (hBsub : IsSubnormal B ⊤) (hcomm : ⁅A, B⁆ = ⊥) {t : X}
    (hAinv : A.map (MulAut.conj t).toMonoidHom = A)
    (hBinv : B.map (MulAut.conj t).toMonoidHom = B) {C : Subgroup X}
    (hC : C = Subgroup.centralizer ({t} : Set X)) {Lc : Subgroup C}
    (hLc : TwoComponents.IsTwoComponent Lc) (hle : Lc.map C.subtype ≤ A ⊔ B) :
    Lc.map C.subtype ≤ A ∨ Lc.map C.subtype ≤ B := by
  classical
  have hfixed : FixedCommutingProduct.fixedSubgroup (MulAut.conj t) = C := by
    rw [hC]
    exact fixedSubgroup_conj_eq_centralizer' t
  have : Group.IsPerfect Lc := ⟨TwoComponents.perfect hLc⟩
  have : Group.IsPerfect (Lc.map C.subtype) := Group.IsPerfect.map C.subtype
  have hderived := FixedCommutingProduct.derived_fixed A B hcomm (MulAut.conj t) hAinv hBinv
  rw [hfixed] at hderived
  have hle'' : Lc.map C.subtype ≤ (A ⊔ B) ⊓ C := le_inf hle (Subgroup.map_subtype_le Lc)
  have hprod : Lc.map C.subtype ≤ (A ⊓ C) ⊔ (B ⊓ C) :=
    calc Lc.map C.subtype = ⁅Lc.map C.subtype, Lc.map C.subtype⁆ :=
          Subgroup.commutator_eq_self.symm
      _ ≤ ⁅(A ⊔ B) ⊓ C, (A ⊔ B) ⊓ C⁆ := Subgroup.commutator_mono hle'' hle''
      _ ≤ (A ⊓ C) ⊔ (B ⊓ C) := hderived
  have hlocal : Lc ≤ A.subgroupOf C ⊔ B.subgroupOf C := by
    have hmap : Lc.map C.subtype ≤ (A.subgroupOf C ⊔ B.subgroupOf C).map C.subtype := by
      rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype]
      exact hprod
    have hcomap := Subgroup.map_le_iff_le_comap.mp hmap
    rwa [Subgroup.comap_map_eq_self_of_injective C.subtype_injective] at hcomap
  have hAlocal : IsSubnormal (A.subgroupOf C) ⊤ := Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hAsub Subgroup.IsSubnormal.top).subgroupOf)
  have hBlocal : IsSubnormal (B.subgroupOf C) ⊤ := Components.chain_of_mathlib_subnormal
    ((Components.mathlib_subnormal_of_chain hBsub Subgroup.IsSubnormal.top).subgroupOf)
  have hpairJoin : sSup ({A.subgroupOf C, B.subgroupOf C} : Set (Subgroup C)) =
      A.subgroupOf C ⊔ B.subgroupOf C := by simp
  have hpairSub : ∀ s ∈ ({A.subgroupOf C, B.subgroupOf C} : Set (Subgroup C)),
      IsSubnormal s ⊤ := by
    intro s hs
    rcases Set.mem_insert_iff.mp hs with rfl | hs
    · exact hAlocal
    · rw [Set.mem_singleton_iff.mp hs]
      exact hBlocal
  obtain ⟨cont, hcont, hcontle⟩ := TwoComponentJoins.exists_le_of_le_sSup Lc hLc
    ({A.subgroupOf C, B.subgroupOf C} : Set (Subgroup C)) hpairSub (by rwa [hpairJoin])
  rcases Set.mem_insert_iff.mp hcont with rfl | hcont
  · left
    calc Lc.map C.subtype ≤ (A.subgroupOf C).map C.subtype := Subgroup.map_mono hcontle
      _ = A ⊓ C := Subgroup.subgroupOf_map_subtype A C
      _ ≤ A := inf_le_left
  · right
    rw [Set.mem_singleton_iff.mp hcont] at hcontle
    calc Lc.map C.subtype ≤ (B.subgroupOf C).map C.subtype := Subgroup.map_mono hcontle
      _ = B ⊓ C := Subgroup.subgroupOf_map_subtype B C
      _ ≤ B := inf_le_left

omit [Finite X] in
theorem isComponentOf_conj_map' {Q : Subgroup X} (hQ : IsComponentOf Q ⊤) (t : X) :
    IsComponentOf (Q.map (MulAut.conj t).toMonoidHom) ⊤ :=
  (LocalComponents.equiv_iff (MulAut.conj t) Q).mpr hQ

omit [Finite X] in
theorem conj_comp_conj_eq_id' {t : X} (ht2 : t * t = 1) :
    (MulAut.conj t).toMonoidHom.comp (MulAut.conj t).toMonoidHom = MonoidHom.id X := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  ext x
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hti,
    MonoidHom.id_apply]
  calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
    _ = x := by rw [ht2]; simp

omit [Finite X] in
theorem map_conj_map_conj_of_mul_self_eq_one' {t : X} (ht2 : t * t = 1) (K : Subgroup X) :
    (K.map (MulAut.conj t).toMonoidHom).map (MulAut.conj t).toMonoidHom = K := by
  rw [Subgroup.map_map, conj_comp_conj_eq_id' ht2, Subgroup.map_id]

omit [Finite X] in
theorem layer_eq_sup_sSup' {Q : Subgroup X} (hQ : IsComponentOf Q ⊤) :
    Layer.subgroup X = Q ⊔ sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} := by
  have hset : {R : Subgroup X | IsComponentOf R ⊤} =
      insert Q {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} := by
    ext R
    by_cases hRQ : R = Q
    · subst hRQ
      simp [hQ]
    · simp [hRQ]
  rw [Layer.subgroup, hset, sSup_insert]

theorem otherComponents_data' {Q : Subgroup X} (hQ : IsComponentOf Q ⊤) {t : X} (ht2 : t * t = 1)
    (hQinv : Q.map (MulAut.conj t).toMonoidHom = Q) :
    (sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q}).map (MulAut.conj t).toMonoidHom =
        sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} ∧
      ⁅Q, sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q}⁆ = ⊥ ∧
      IsSubnormal (sSup {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q}) ⊤ := by
  set S' : Set (Subgroup X) := {R : Subgroup X | IsComponentOf R ⊤ ∧ R ≠ Q} with hS'
  have hS'comp : ∀ b ∈ S', IsComponentOf b ⊤ := fun b hb => hb.1
  refine ⟨?_, ?_, ?_⟩
  · have hS'inv : ∀ R ∈ S', R.map (MulAut.conj t).toMonoidHom ∈ S' := by
      rintro R ⟨hR, hRQ⟩
      refine ⟨isComponentOf_conj_map' hR t, fun h => hRQ ?_⟩
      have := congrArg (fun K => K.map (MulAut.conj t).toMonoidHom) h
      simp only [map_conj_map_conj_of_mul_self_eq_one' ht2, hQinv] at this
      exact this
    have hle1 : (sSup S').map (MulAut.conj t).toMonoidHom ≤ sSup S' := by
      rw [Subgroup.map_le_iff_le_comap]
      refine sSup_le fun R hR => ?_
      rw [← Subgroup.map_le_iff_le_comap]
      exact le_sSup (hS'inv R hR)
    refine le_antisymm hle1 ?_
    have := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom) hle1
    rwa [map_conj_map_conj_of_mul_self_eq_one' ht2] at this
  · rw [Subgroup.commutator_comm]
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    refine sSup_le fun b hb => ?_
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (LocalComponents.commute_of_ne b Q (hS'comp b hb) hQ hb.2)
  · have hTE : sSup S' ≤ Layer.subgroup X :=
      sSup_le fun b hb => Layer.component_le (hS'comp b hb)
    have hTnormal : ((sSup S').subgroupOf (Layer.subgroup X)).Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTE]
      intro g hg
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        (map_conj_sSup_of_isComponentOf hS'comp hg)
    have : (Layer.subgroup X).Normal := Layer.normal X
    exact IsSubnormal.step hTE hTnormal
      (IsSubnormal.step le_top Subgroup.normal_subgroupOf (IsSubnormal.refl ⊤))

end Copy

theorem dichotomy_group {X : Type} [Group X] [Finite X] {B : Subgroup X} [B.Normal]
    (hB : IsPComponent 2 B) {u : X} (hu : orderOf u = 2) {K : Subgroup X}
    (hKC : K ≤ centralizer ({u} : Set X))
    (hK : IsPComponent 2 (K.subgroupOf (centralizer ({u} : Set X)))) :
    K ≤ B ⊔ pPrimeCore 2 X ∨ ⁅K, B⁆ ≤ pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOn : (pPrimeCore 2 X).Normal := pPrimeCore_normal
  have htt : u * u = 1 := by rw [← pow_two, ← hu, pow_orderOf_eq_one]
  let π := QuotientGroup.mk' (pPrimeCore 2 X)
  obtain ⟨hKπ, hKπP⟩ := UGSChain.map_twoComponent_centralizer_quotient hu hKC hK
  obtain ⟨Kc, hKc, -, hBmap, -⟩ := hB
  have hQ : IsComponentOf (B.map π) ⊤ := by
    rw [hBmap]
    exact (CFSG.isComponent_iff_open Kc).mp hKc
  have hπt : π u * π u = 1 := by rw [← map_mul, htt, map_one]
  have hQinv : (B.map π).map (MulAut.conj (π u)).toMonoidHom = B.map π := by
    rw [Subgroup.map_map]
    have : (MulAut.conj (π u)).toMonoidHom.comp π = π.comp (MulAut.conj u).toMonoidHom := by
      ext x
      simp [π, MulAut.conj_apply]
    rw [this, ← Subgroup.map_map]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.Normal.conj_mem inferInstance y hy u
    · intro hx
      exact ⟨u⁻¹ * x * u, by simpa using Subgroup.Normal.conj_mem inferInstance x hx u⁻¹,
        by simp [MulAut.conj_apply, mul_assoc]⟩
  obtain ⟨hBinv, hcomm, hBsub⟩ := otherComponents_data' hQ hπt hQinv
  have hLc : TwoComponents.IsTwoComponent
      ((K.map π).subgroupOf (centralizer ({π u} : Set (X ⧸ pPrimeCore 2 X)))) :=
    (CatalogueBAlternating.pComponent_two_iff _).1 hKπP
  have hO : componentClassificationOddCore (X ⧸ pPrimeCore 2 X) = ⊥ := by
    rw [← CatalogueBAlternating.primeCore_two_eq_oddCore]
    exact pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hlayer := twoComponent_le_layer_of_l2PrimeBalance l2PrimeBalance hO hπt rfl hLc
  rw [layer_eq_sup_sSup' hQ] at hlayer
  have hmap : ((K.map π).subgroupOf (centralizer ({π u} : Set (X ⧸ pPrimeCore 2 X)))).map
      (centralizer ({π u} : Set (X ⧸ pPrimeCore 2 X))).subtype = K.map π :=
    Subgroup.map_subgroupOf_eq_of_le hKπ
  rcases twoComponent_le_or_le_of_le_sup' hQ.2.1 hBsub hcomm hQinv hBinv rfl hLc hlayer with h | h
  · left
    rw [hmap] at h
    have := Subgroup.map_le_iff_le_comap.mp h
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at this
  · right
    rw [hmap] at h
    have h2 : ⁅K.map π, B.map π⁆ = ⊥ := by
      refine le_bot_iff.mp ((Subgroup.commutator_mono h le_rfl).trans ?_)
      rw [Subgroup.commutator_comm]
      exact hcomm.le
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h2
    exact h2

theorem dichotomy_sub {G : Type} [Group G] [Finite G] {X B K : Subgroup G} (hB : IsPCompIn 2 X B)
    (hBn : ∀ x ∈ X, ∀ b ∈ B, x * b * x⁻¹ ∈ B) {u : G} (hu : orderOf u = 2) (huX : u ∈ X)
    (hK : IsPCompIn 2 (X ⊓ centralizer ({u} : Set G)) K) :
    K ≤ B ⊔ pPrimeCoreOf 2 X ∨ ⁅K, B⁆ ≤ pPrimeCoreOf 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let u' : ↥X := ⟨u, huX⟩
  have hu' : orderOf u' = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hBX : B ≤ X := hB.1
  have hKX : K ≤ X ⊓ centralizer ({u} : Set G) := hK.1
  have hKX' : K ≤ X := hKX.trans inf_le_left
  have hBnormal : (B.subgroupOf X).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hBX]
    exact fun h k hh hk => hBn k hk h hh
  have hcen : centralizer ({u'} : Set ↥X) = (X ⊓ centralizer ({u} : Set G)).subgroupOf X := by
    ext x
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h1
      exact ⟨x.2, congrArg Subtype.val h1⟩
    · intro h1
      exact Subtype.ext h1.2
  have hKC : K.subgroupOf X ≤ centralizer ({u'} : Set ↥X) := by
    rw [hcen]
    exact fun x hx => hKX hx
  have hKP : IsPComponent 2 ((K.subgroupOf X).subgroupOf (centralizer ({u'} : Set ↥X))) := by
    rw [hcen]
    exact (CFSG.ComponentClassification.UnbalancedCorr.isPComponent_subgroupOf_subgroupOf_iff'
      (inf_le_left : X ⊓ centralizer ({u} : Set G) ≤ X) 2 Nat.prime_two).mpr hK.2
  have hOmap : (pPrimeCore 2 ↥X).map X.subtype = pPrimeCoreOf 2 X := rfl
  rcases dichotomy_group (B := B.subgroupOf X) hB.2 hu' hKC hKP with h | h
  · left
    have h1 := Subgroup.map_mono (f := X.subtype) h
    rwa [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hKX',
      Subgroup.map_subgroupOf_eq_of_le hBX, hOmap] at h1
  · right
    have h1 := Subgroup.map_mono (f := X.subtype) h
    rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKX',
      Subgroup.map_subgroupOf_eq_of_le hBX, hOmap] at h1

end CFSG.GH74.GLS.C3.Layer1.Bk
