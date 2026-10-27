module

public import CFSG.LocalAnalysis.ComponentClassification.CentralCoverLemmasBActionKernel
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115List
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals

public section

namespace CFSG.QuasithinUnique.Id2519.Tab

open CFSG.ComponentClassification CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1
open scoped commutatorElement

section Proj

variable {G : Type} [Group G] {X : Subgroup G} {Q : Type*} [Group Q]

@[expose] noncomputable def quotProj (e : (↥X ⧸ Subgroup.center ↥X) ≃* Q) : ↥X →* Q :=
  e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥X))

theorem quotProj_apply (e : (↥X ⧸ Subgroup.center ↥X) ≃* Q) (x : X) :
    quotProj e x = e (QuotientGroup.mk x) := rfl

theorem quotProj_surjective (e : (↥X ⧸ Subgroup.center ↥X) ≃* Q) :
    Function.Surjective (quotProj e) :=
  e.surjective.comp (QuotientGroup.mk'_surjective _)

theorem quotProj_ker (e : (↥X ⧸ Subgroup.center ↥X) ≃* Q) :
    (quotProj e).ker = Subgroup.center ↥X := by
  ext x
  simp only [quotProj, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end Proj

theorem mem_center_iff_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    e a ∈ Subgroup.center B ↔ a ∈ Subgroup.center A := by
  rw [← Subgroup.map_center_eq e]
  exact Subgroup.mem_map_iff_mem e.injective

theorem perfectResidualOf_le {G : Type} [Group G] (O : Subgroup G) :
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf O ≤ O :=
  Subgroup.map_subtype_le _

section Action

variable {G : Type} [Group G]

@[expose] noncomputable def conjAut (X : Subgroup G) (t : G)
    (ht : t ∈ Subgroup.normalizer (X : Set G)) : MulAut X :=
  X.normalizerMonoidHom ⟨t, ht⟩

theorem coe_conjAut (X : Subgroup G) {t : G} (ht : t ∈ Subgroup.normalizer (X : Set G)) (x : X) :
    ((conjAut X t ht x : X) : G) = t * x * t⁻¹ := by
  simp [conjAut]

variable {X : Subgroup G} {Q : Type*} [Group Q]

@[expose] noncomputable def quotActHom (π : X →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center X) : MulAut X →* MulAut Q :=
  (MulAut.congr (CentralCover.quotientEquivOfKerEqCenter π hπ hker)).toMonoidHom.comp
    (PerfectAutomorphisms.centerQuotientHom X)

variable (π : X →* Q) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center X)

theorem quotActHom_apply (σ : MulAut X) (x : X) : quotActHom π hπ hker σ (π x) = π (σ x) := by
  have hsymm : (CentralCover.quotientEquivOfKerEqCenter π hπ hker).symm (π x) =
      QuotientGroup.mk' (Subgroup.center X) x := by
    rw [MulEquiv.symm_apply_eq, CentralCover.quotientEquivOfKerEqCenter_mk]
  change CentralCover.quotientEquivOfKerEqCenter π hπ hker
    (PerfectAutomorphisms.onCenterQuotient σ
      ((CentralCover.quotientEquivOfKerEqCenter π hπ hker).symm (π x))) = _
  rw [hsymm, PerfectAutomorphisms.onCenterQuotient_apply_mk,
    CentralCover.quotientEquivOfKerEqCenter_mk]

theorem quotActHom_injective (hX : Group.IsPerfect X) :
    Function.Injective (quotActHom π hπ hker) := by
  have := hX
  have h1 : Function.Injective
      (MulAut.congr (CentralCover.quotientEquivOfKerEqCenter π hπ hker)) :=
    MulEquiv.injective _
  have h2 := PerfectAutomorphisms.centerQuotientHom_injective X
  exact h1.comp h2

theorem quotActHom_fix {σ : MulAut X} {x : X} (hx : σ x = x) :
    quotActHom π hπ hker σ (π x) = π x := by
  rw [quotActHom_apply, hx]

theorem quotActHom_conj (l : X) : quotActHom π hπ hker (MulAut.conj l) = MulAut.conj (π l) := by
  ext q
  obtain ⟨x, rfl⟩ := hπ q
  rw [quotActHom_apply]
  simp [MulAut.conj_apply, map_mul, map_inv]

theorem mem_inner_of_quotActHom (hX : Group.IsPerfect X) {σ : MulAut X}
    (h : quotActHom π hπ hker σ ∈ inner Q) : σ ∈ inner X := by
  obtain ⟨q, hq⟩ := h
  obtain ⟨l, rfl⟩ := hπ q
  refine ⟨l, quotActHom_injective π hπ hker hX ?_⟩
  rw [quotActHom_conj]
  exact hq

end Action

section Involution

variable {G : Type} [Group G] {X : Subgroup G} {Q : Type*} [Group Q] {t : G}

@[expose] noncomputable def quotAct (π : X →* Q) (hπ : Function.Surjective π)
    (hker : π.ker = Subgroup.center X) (ht : t ∈ Subgroup.normalizer (X : Set G)) : MulAut Q :=
  quotActHom π hπ hker (conjAut X t ht)

variable (π : X →* Q) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center X)
  (ht : t ∈ Subgroup.normalizer (X : Set G))

theorem quotAct_apply (x y : X) (hxy : (y : G) = t * x * t⁻¹) :
    quotAct π hπ hker ht (π x) = π y := by
  have : conjAut X t ht x = y := Subtype.ext (by rw [coe_conjAut, hxy])
  rw [quotAct, quotActHom_apply, this]

theorem quotAct_mul_self (ht2 : t * t = 1) :
    quotAct π hπ hker ht * quotAct π hπ hker ht = 1 := by
  ext q
  obtain ⟨x, rfl⟩ := hπ q
  have hy : ∃ y : X, (y : G) = t * x * t⁻¹ := ⟨conjAut X t ht x, coe_conjAut X ht x⟩
  obtain ⟨y, hy⟩ := hy
  have hz : ((x : X) : G) = t * y * t⁻¹ := by
    rw [hy]
    have : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
    rw [this]
    calc (x : G) = (t * t) * x * (t * t) := by rw [ht2]; group
      _ = t * (t * x * t) * t := by group
  simp only [MulAut.mul_apply, MulAut.one_apply]
  rw [quotAct_apply π hπ hker ht x y hy, quotAct_apply π hπ hker ht y x hz]

theorem quotAct_ne_one (hXq : CFSG.IsQuasisimple X) (hcomm : ⁅X, Subgroup.zpowers t⁆ = X) :
    quotAct π hπ hker ht ≠ 1 := by
  intro h1
  have hX : Group.IsPerfect X := hXq.1
  have hσ : conjAut X t ht = 1 := by
    apply quotActHom_injective π hπ hker hX
    rw [map_one]
    exact h1
  have hcent : ∀ x ∈ X, t * x = x * t := by
    intro x hx
    have h := congrArg (fun σ : MulAut X => ((σ ⟨x, hx⟩ : X) : G)) hσ
    simp only [coe_conjAut, MulAut.one_apply] at h
    calc t * x = t * x * t⁻¹ * t := by group
      _ = x * t := by rw [h]
  have hle : ⁅X, Subgroup.zpowers t⁆ ≤ ⊥ := by
    rw [Subgroup.commutator_le]
    intro x hx g hg
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hk : x * t ^ k = t ^ k * x :=
      ((Commute.zpow_left (show Commute t x from hcent x hx) k)).eq.symm
    rw [Subgroup.mem_bot, commutatorElement_def, hk]
    group
  rw [hcomm] at hle
  have hone : ∀ x : X, x = 1 := fun x => Subtype.ext (Subgroup.mem_bot.mp (hle x.2))
  have hq := hXq.2.1
  have : Nontrivial (↥X ⧸ Subgroup.center ↥X) := hq.toNontrivial
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥X ⧸ Subgroup.center ↥X)
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  exact hab (by rw [hone a', hone b'])

theorem inducesInner_of_quotAct_mem_inner (hX : Group.IsPerfect X) (ht2 : t * t = 1)
    (h : quotAct π hπ hker ht ∈ inner Q) : InducesInner t X := by
  obtain ⟨l, hl⟩ := mem_inner_of_quotActHom π hπ hker hX h
  refine ⟨((l : X) : G)⁻¹, X.inv_mem l.2, fun x hx => ?_⟩
  have h1 : ((l : X) : G) * x * ((l : X) : G)⁻¹ = t * x * t⁻¹ := by
    have := congrArg (fun σ : MulAut X => ((σ ⟨x, hx⟩ : X) : G)) hl
    simpa [coe_conjAut, MulAut.conj_apply] using this
  have hinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  calc t⁻¹ * x * t = t * x * t⁻¹ := by rw [hinv]
    _ = ((l : X) : G) * x * ((l : X) : G)⁻¹ := h1.symm
    _ = (((l : X) : G)⁻¹)⁻¹ * x * ((l : X) : G)⁻¹ := by rw [inv_inv]

end Involution

section ActHom

variable {G : Type} [Group G] {X : Subgroup G} {Q : Type*} [Group Q]
  (π : X →* Q) (hπ : Function.Surjective π) (hker : π.ker = Subgroup.center X)
  (Y : Subgroup G) (hYn : Y ≤ Subgroup.normalizer (X : Set G))

@[expose] noncomputable def actHom : ↥Y →* MulAut Q :=
  (quotActHom π hπ hker).comp ((X.normalizerMonoidHom).comp (Subgroup.inclusion hYn))

theorem actHom_apply (y : ↥Y) (x : ↥X) :
    actHom π hπ hker Y hYn y (π x) =
      π ((X.normalizerMonoidHom (Subgroup.inclusion hYn y)) x) :=
  quotActHom_apply π hπ hker _ x

theorem coe_actHom_conj (y : ↥Y) (x : ↥X) :
    (((X.normalizerMonoidHom (Subgroup.inclusion hYn y)) x : ↥X) : G) =
      (y : G) * (x : G) * (y : G)⁻¹ := by
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  rfl

theorem ker_actHom (hX : Group.IsPerfect X) :
    (actHom π hπ hker Y hYn).ker = (Y ⊓ Subgroup.centralizer (X : Set G)).subgroupOf Y := by
  ext y
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  constructor
  · intro h
    have h1 : X.normalizerMonoidHom (Subgroup.inclusion hYn y) = 1 := by
      apply quotActHom_injective π hπ hker hX
      rw [map_one]
      exact h
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have h2 := congrArg (fun σ : MulAut X => ((σ ⟨x, hx⟩ : X) : G)) h1
    simp only [coe_actHom_conj Y hYn, MulAut.one_apply] at h2
    calc x * (y : G) = ((y : G) * x * (y : G)⁻¹) * y := by rw [h2]
      _ = y * x := by group
  · rintro ⟨-, h⟩
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    rw [actHom_apply, MulAut.one_apply]
    congr 1
    apply Subtype.ext
    rw [coe_actHom_conj Y hYn]
    have hxy : (x : G) * (y : G) = (y : G) * (x : G) := Subgroup.mem_centralizer_iff.mp h x x.2
    calc (y : G) * (x : G) * (y : G)⁻¹ = ((x : G) * (y : G)) * (y : G)⁻¹ := by rw [hxy]
      _ = x := by group

theorem relIndex_eq_card_range (hX : Group.IsPerfect X) :
    (Y ⊓ Subgroup.centralizer (X : Set G)).relIndex Y =
      Nat.card (actHom π hπ hker Y hYn).range := by
  rw [Subgroup.relIndex, ← ker_actHom π hπ hker Y hYn hX, Subgroup.index_ker]

theorem actHom_fix {y : ↥Y} {k : ↥X} (hk : (k : G) * (y : G) = (y : G) * (k : G)) :
    actHom π hπ hker Y hYn y (π k) = π k := by
  rw [actHom_apply]
  congr 1
  apply Subtype.ext
  rw [coe_actHom_conj Y hYn]
  calc (y : G) * (k : G) * (y : G)⁻¹ = ((k : G) * (y : G)) * (y : G)⁻¹ := by rw [hk]
    _ = k := by group

end ActHom

theorem card_le_two_of_centralizer_trivial {Q : Type*} [Group Q] [Finite Q]
    (hout : Nat.card (Outer Q) ≤ 2) (Kb : Subgroup Q)
    (hC : Subgroup.centralizer (Kb : Set Q) = ⊥) (B : Subgroup (MulAut Q))
    (hB : ∀ β ∈ B, ∀ k ∈ Kb, β k = k) : Nat.card B ≤ 2 := by
  have hfin : Finite (MulAut Q) :=
    Finite.of_injective (fun α : MulAut Q => (α : Q → Q)) DFunLike.coe_injective
  let f : B →* Outer Q := (QuotientGroup.mk' (inner Q)).comp B.subtype
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro β hβ
    have hβ' : ((β : MulAut Q) : MulAut Q ⧸ inner Q) = 1 := hβ
    have hin : (β : MulAut Q) ∈ inner Q := (QuotientGroup.eq_one_iff _).mp hβ'

    obtain ⟨q, hq⟩ := hin
    have hq1 : q = 1 := by
      have : q ∈ Subgroup.centralizer (Kb : Set Q) := by
        rw [Subgroup.mem_centralizer_iff]
        intro k hk
        have h1 := hB β β.2 k hk
        rw [← hq] at h1
        simp only [MulAut.conj_apply] at h1
        calc k * q = (q * k * q⁻¹) * q := by rw [h1]
          _ = q * k := by group
      rw [hC] at this
      exact Subgroup.mem_bot.mp this
    apply Subtype.ext
    rw [← hq, hq1, map_one]
    rfl
  exact (Nat.card_le_card_of_injective f hinj).trans hout

end CFSG.QuasithinUnique.Id2519.Tab
