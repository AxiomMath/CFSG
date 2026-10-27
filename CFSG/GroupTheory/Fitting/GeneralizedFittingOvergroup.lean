module

public import CFSG.GroupTheory.Fitting.CharacteristicPOvergroup
public import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceQuotient

public section

namespace CFSG

open Subgroup CFSG.LocalCores

variable {X : Type*} [Group X] [Finite X]

private theorem pPrimeCore_eq_bot_of_normal {p : ℕ} [Fact p.Prime]
    {N : Subgroup X} [N.Normal] (hO : pPrimeCore p X = ⊥) :
    pPrimeCore p ↥N = ⊥ := by
  have hN : ((pPrimeCore p ↥N).map N.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hle : (pPrimeCore p ↥N).map N.subtype ≤ pPrimeCore p X := by
    refine le_sSup ⟨hN, ?_⟩
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact pPrimeCore_coprime_card
  rwa [hO, le_bot_iff, Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at hle

private theorem component_le_of_generalizedFitting_le {H : Subgroup X}
    (hF : generalizedFitting X ≤ H) {K : Subgroup X} (hK : IsComponent K) : K ≤ H :=
  (component_le_layer hK).trans
    ((le_sup_right : layer X ≤ fittingSubgroup X ⊔ layer X).trans
      (by simpa [generalizedFitting.eq_sup] using hF))

private theorem component_map_le_generalizedFitting {H : Subgroup X}
    (hF : generalizedFitting X ≤ H) {C : Subgroup ↥H} (hC : IsComponent C) :
    C.map H.subtype ≤ generalizedFitting X := by
  let F : Subgroup X := generalizedFitting X
  let FH : Subgroup ↥H := F.subgroupOf H
  have hFnormal : F.Normal :=
    (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).2
  have hFHnormal : FH.Normal := by
    dsimp [FH]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hFnormal]
      exact le_top)
  rcases LocalCores.component_normal_subgroup (G := ↥H) hC hFHnormal with hle | hcomm
  · have hmap : C.map H.subtype ≤ (F.subgroupOf H).map H.subtype := Subgroup.map_mono hle
    rw [Subgroup.map_subgroupOf_eq_of_le hF] at hmap
    exact hmap
  · have hcent_map : C.map H.subtype ≤ Subgroup.centralizer (F : Set X) := by
      have hcomm_map : ⁅C.map H.subtype, (F.subgroupOf H).map H.subtype⁆ = ⊥ := by
        rw [← Subgroup.map_commutator, hcomm, Subgroup.map_bot]
      rw [Subgroup.map_subgroupOf_eq_of_le hF] at hcomm_map
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm_map
    exact hcent_map.trans (CFSG.centralizer_generalizedFitting_le X)

theorem layer_map_eq_of_generalizedFitting_le {H : Subgroup X}
    (hF : generalizedFitting X ≤ H) :
    (layer ↥H).map H.subtype = layer X := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    rw [layer.eq_sSup]
    refine sSup_le ?_
    intro C hC
    let L : Subgroup X := C.map H.subtype
    let F : Subgroup X := generalizedFitting X
    let NH : Subgroup ↥H := F.subgroupOf H
    have hLleF : L ≤ F := by
      simpa [F] using component_map_le_generalizedFitting hF hC
    have hC_le_NH : C ≤ NH := by
      intro c hc
      have hcF : (c : X) ∈ F := hLleF (Subgroup.mem_map_of_mem H.subtype hc)
      simpa [NH, Subgroup.mem_subgroupOf] using hcF
    have hcompNH : IsComponent (C.subgroupOf NH) := LocalCores.component_overgroup hC hC_le_NH
    let e : ↥NH ≃* ↥F := Subgroup.subgroupOfEquivOfLe hF
    have hcompF : IsComponent ((C.subgroupOf NH).map e.toMonoidHom) :=
      LocalCores.isComponent_map_mulEquiv e hcompNH
    have hcompX : IsComponent (((C.subgroupOf NH).map e.toMonoidHom).map F.subtype) := by
      refine ⟨LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective _ _ F.subtype_injective) hcompF.1, ?_⟩
      exact hcompF.2.trans' ((LocalCores.generalized_fitting_characteristic (G := X)).2).isSubnormal
    have hmap_eq : (((C.subgroupOf NH).map e.toMonoidHom).map F.subtype) = L := by
      have hcomp : F.subtype.comp e.toMonoidHom = H.subtype.comp NH.subtype := by
        ext n
        rfl
      calc
        ((C.subgroupOf NH).map e.toMonoidHom).map F.subtype
            = (C.subgroupOf NH).map (F.subtype.comp e.toMonoidHom) := by
              rw [Subgroup.map_map]
        _ = (C.subgroupOf NH).map (H.subtype.comp NH.subtype) := by rw [hcomp]
        _ = ((C.subgroupOf NH).map NH.subtype).map H.subtype := by
              rw [← Subgroup.map_map]
        _ = C.map H.subtype := by
              rw [Subgroup.map_subgroupOf_eq_of_le hC_le_NH]
    exact (Subgroup.map_le_iff_le_comap).mp (by
      change L ≤ layer X
      rw [← hmap_eq]
      exact component_le_layer hcompX)
  · rw [layer.eq_sSup]
    refine sSup_le ?_
    intro K hK
    have hKH : K ≤ H := component_le_of_generalizedFitting_le hF hK
    have hKHcomp : IsComponent (K.subgroupOf H) := LocalCores.component_overgroup hK hKH
    have hmap : (K.subgroupOf H).map H.subtype = K :=
      Subgroup.map_subgroupOf_eq_of_le hKH
    rw [← hmap]
    exact Subgroup.map_mono (component_le_layer hKHcomp)

theorem pPrimeCore_eq_bot_of_generalizedFitting_le {p : ℕ} [Fact p.Prime]
    {H : Subgroup X} (hO : pPrimeCore p X = ⊥) (hF : generalizedFitting X ≤ H) :
    pPrimeCore p ↥H = ⊥ := by
  let F : Subgroup X := generalizedFitting X
  let N : Subgroup ↥H := F.subgroupOf H
  have hFnormal : F.Normal :=
    (LocalCores.generalized_fitting_characteristic (G := X)).2
  have hNnormal : N.Normal := by
    dsimp [N]
    exact Subgroup.normal_subgroupOf_of_le_normalizer (by
      rw [Subgroup.normalizer_eq_top_iff.mpr hFnormal]
      exact le_top)
  have hcoreF : pPrimeCore p ↥F = ⊥ := pPrimeCore_eq_bot_of_normal hO
  have hcoreN : pPrimeCore p ↥N = ⊥ := by
    let e : ↥N ≃* ↥F := Subgroup.subgroupOfEquivOfLe hF
    have hmap := pPrimeCore_map_iso (p := p) (G := ↥N) (G' := ↥F) e
    rw [hcoreF] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ e.injective).mp hmap
  have hC : Subgroup.centralizer (N : Set ↥H) ≤ N := by
    intro x hx
    have hxX : (x : X) ∈ Subgroup.centralizer (F : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have hfH : f ∈ H := hF hf
      have hn : (⟨f, hfH⟩ : ↥H) ∈ N := by
        simpa [N, Subgroup.mem_subgroupOf] using hf
      exact congrArg (fun y : ↥H => (y : X))
        (Subgroup.mem_centralizer_iff.mp hx _ hn)
    have hxF : (x : X) ∈ F := CFSG.centralizer_generalizedFitting_le X hxX
    simpa [N, Subgroup.mem_subgroupOf] using hxF
  exact pPrimeCore_eq_bot_of_normal_of_centralizer_le (B := ↥H) (N := N)
    hNnormal hcoreN hC

section quotientTransport

variable {p : ℕ} [Fact p.Prime]

private theorem quotient_restriction_kernel {O : Subgroup X} [O.Normal] {H : Subgroup X} :
    let q : X →* X ⧸ O := QuotientGroup.mk' O
    let Hbar : Subgroup (X ⧸ O) := H.map q
    let qH : ↥H →* ↥Hbar := (q.comp H.subtype).codRestrict Hbar (fun x =>
      Subgroup.mem_map_of_mem q x.2)
    Function.Surjective qH ∧ qH.ker = O.subgroupOf H := by
  dsimp only
  let q : X →* X ⧸ O := QuotientGroup.mk' O
  let Hbar : Subgroup (X ⧸ O) := H.map q
  let qH : ↥H →* ↥Hbar := (q.comp H.subtype).codRestrict Hbar (fun x =>
    Subgroup.mem_map_of_mem q x.2)
  constructor
  · intro y
    rcases y.2 with ⟨x, hx, hxy⟩
    refine ⟨⟨x, hx⟩, ?_⟩
    apply Subtype.ext
    exact hxy
  · ext x
    constructor
    · intro hx
      have hx' : q (x : X) = 1 := congrArg Subtype.val hx
      exact (QuotientGroup.eq_one_iff (x : X)).mp hx'
    · intro hx
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : X)).mpr hx

theorem map_pPrimeCore_eq_of_quotient {H : Subgroup X} (hOH : pPrimeCore p X ≤ H)
    (hF : generalizedFitting (X ⧸ pPrimeCore p X) ≤
      H.map (QuotientGroup.mk' (pPrimeCore p X))) :
    (pPrimeCore p ↥H).map H.subtype = pPrimeCore p X := by
  let O : Subgroup X := pPrimeCore p X
  let Xbar : Type _ := X ⧸ O
  let q : X →* Xbar := QuotientGroup.mk' O
  let Hbar : Subgroup Xbar := H.map q
  let Osub : Subgroup ↥H := O.subgroupOf H
  let qH : ↥H →* ↥Hbar := (q.comp H.subtype).codRestrict Hbar (fun x =>
    Subgroup.mem_map_of_mem q x.2)
  obtain ⟨hqH_surj, hker_qH⟩ := quotient_restriction_kernel (H := H) (O := O)
  have hcore_quot : pPrimeCore p Xbar = ⊥ := by
    dsimp [Xbar, O]
    exact pPrimeCore_quotient_eq_bot (Fact.out : p.Prime)
  have hcore_Hbar : pPrimeCore p ↥Hbar = ⊥ :=
    pPrimeCore_eq_bot_of_generalizedFitting_le (X := Xbar) (H := Hbar) hcore_quot hF
  have hOsub_normal : Osub.Normal :=
    (pPrimeCore_normal (p := p) (G := X)).subgroupOf H
  have hOsub_coprime : Nat.Coprime p (Nat.card Osub) := by
    have hcard : Nat.card Osub = Nat.card O :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOH).toEquiv
    rw [hcard]
    exact pPrimeCore_coprime_card (p := p) (G := X)
  have hOsub_le : Osub ≤ pPrimeCore p ↥H :=
    le_sSup ⟨hOsub_normal, hOsub_coprime⟩
  have hmap_core_le : (pPrimeCore p ↥H).map qH ≤ pPrimeCore p ↥Hbar :=
    map_pPrimeCore_le qH hqH_surj
  have hmap_core_bot : (pPrimeCore p ↥H).map qH = ⊥ := by
    exact le_bot_iff.mp (by simpa [hcore_Hbar] using hmap_core_le)
  have hcore_le : pPrimeCore p ↥H ≤ Osub := by
    change pPrimeCore p ↥H ≤ O.subgroupOf H
    rw [← hker_qH]
    exact (Subgroup.map_eq_bot_iff (pPrimeCore p ↥H) (f := qH)).mp hmap_core_bot
  have hcore_eq : pPrimeCore p ↥H = Osub := le_antisymm hcore_le hOsub_le
  rw [hcore_eq]
  exact Subgroup.map_subgroupOf_eq_of_le hOH

theorem map_pLayer_sup_pPrimeCore_eq_of_quotient {H : Subgroup X}
    (hOH : pPrimeCore p X ≤ H)
    (hF : generalizedFitting (X ⧸ pPrimeCore p X) ≤
      H.map (QuotientGroup.mk' (pPrimeCore p X))) :
    ((pLayer ↥H p) ⊔ pPrimeCore p ↥H).map H.subtype =
      pLayer X p ⊔ pPrimeCore p X := by
  let O : Subgroup X := pPrimeCore p X
  let Xbar : Type _ := X ⧸ O
  let q : X →* Xbar := QuotientGroup.mk' O
  let Hbar : Subgroup Xbar := H.map q
  let Osub : Subgroup ↥H := O.subgroupOf H
  let qH : ↥H →* ↥Hbar := (q.comp H.subtype).codRestrict Hbar (fun x =>
    Subgroup.mem_map_of_mem q x.2)
  obtain ⟨hqH_surj, hker_qH⟩ := quotient_restriction_kernel (H := H) (O := O)
  have hcore_eq : pPrimeCore p ↥H = Osub := by
    apply Subgroup.map_injective H.subtype_injective
    rw [map_pPrimeCore_eq_of_quotient (p := p) hOH hF,
      Subgroup.map_subgroupOf_eq_of_le hOH]
  have hlayer_map : (layer ↥Hbar).map Hbar.subtype = layer Xbar :=
    layer_map_eq_of_generalizedFitting_le (X := Xbar) (H := Hbar) hF
  have hlayer_le : layer Xbar ≤ Hbar := by
    have hF' : fittingSubgroup Xbar ⊔ layer Xbar ≤ Hbar := by
      simpa [generalizedFitting.eq_sup] using hF
    exact le_sup_right.trans hF'
  have hlayer_Hbar_eq : (layer ↥Hbar) = (layer Xbar).subgroupOf Hbar := by
    apply Subgroup.map_injective Hbar.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hlayer_le, hlayer_map]
  let e₀ : ↥H ⧸ qH.ker ≃* ↥Hbar :=
    QuotientGroup.quotientKerEquivOfSurjective qH hqH_surj
  let e : ↥H ⧸ Osub ≃* ↥Hbar :=
    (QuotientGroup.quotientMulEquivOfEq hker_qH.symm).trans e₀
  let eH : ↥H ⧸ pPrimeCore p ↥H ≃* ↥H ⧸ Osub :=
    QuotientGroup.quotientMulEquivOfEq hcore_eq
  let eT : ↥H ⧸ pPrimeCore p ↥H ≃* ↥Hbar := eH.trans e
  have heT_comp : eT.toMonoidHom.comp
      (QuotientGroup.mk' (pPrimeCore p ↥H)) = qH := by
    ext x
    simp [eT, eH, e, e₀, QuotientGroup.quotientMulEquivOfEq_mk,
      QuotientGroup.kerLift_mk]
    change QuotientGroup.kerLift qH (QuotientGroup.mk x) = qH x
    rw [QuotientGroup.kerLift_mk]
  have hmap_pLayer_H : (pLayer ↥H p).map qH = layer ↥Hbar := by
    calc
      (pLayer ↥H p).map qH
          = (pLayer ↥H p).map
              (eT.toMonoidHom.comp (QuotientGroup.mk' (pPrimeCore p ↥H))) := by
              rw [heT_comp]
      _ = ((pLayer ↥H p).map
            (QuotientGroup.mk' (pPrimeCore p ↥H))).map eT.toMonoidHom := by
              rw [Subgroup.map_map]
      _ = (layer (↥H ⧸ pPrimeCore p ↥H)).map eT.toMonoidHom := by
              rw [CFSG.ComponentClassification.LBalance.Quot.map_pLayer_eq_layer_quotient
                (H := ↥H) (p := p)]
      _ = layer ↥Hbar := CFSG.WholeGroup.layer_map_mulEquiv eT
  have hcomap_qH : (layer ↥Hbar).comap qH = pLayer ↥H p ⊔ Osub := by
    rw [← hmap_pLayer_H, Subgroup.comap_map_eq, hker_qH]
  have hcomap_qH_as_subgroupOf :
      (layer ↥Hbar).comap qH = ((layer Xbar).comap q).subgroupOf H := by
    ext x
    rw [hlayer_Hbar_eq]
    simp [Subgroup.mem_subgroupOf, Subgroup.mem_comap, qH]
  have hcomap_Hbar : Hbar.comap q = H := by
    dsimp [Hbar]
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hOH]
  have hpreimage_le : (layer Xbar).comap q ≤ H := by
    have h := Subgroup.comap_mono (f := q) hlayer_le
    rwa [hcomap_Hbar] at h
  calc
    ((pLayer ↥H p) ⊔ pPrimeCore p ↥H).map H.subtype
        = (pLayer ↥H p ⊔ Osub).map H.subtype := by rw [hcore_eq]
    _ = ((layer ↥Hbar).comap qH).map H.subtype := by rw [hcomap_qH]
    _ = (((layer Xbar).comap q).subgroupOf H).map H.subtype := by
          rw [hcomap_qH_as_subgroupOf]
    _ = (layer Xbar).comap q := Subgroup.map_subgroupOf_eq_of_le hpreimage_le
    _ = pLayer X p ⊔ O := by
          simpa [Xbar, O, q] using
            (CFSG.ComponentClassification.LBalance.Quot.comap_layer_quotient_eq
              (H := X) (p := p))
    _ = pLayer X p ⊔ pPrimeCore p X := by rfl

theorem map_pLayer_two_sup_pPrimeCore_two_eq_of_quotient {H : Subgroup X}
    (hOH : pPrimeCore 2 X ≤ H)
    (hF : generalizedFitting (X ⧸ pPrimeCore 2 X) ≤
      H.map (QuotientGroup.mk' (pPrimeCore 2 X))) :
    ((pLayer ↥H 2) ⊔ pPrimeCore 2 ↥H).map H.subtype =
      pLayer X 2 ⊔ pPrimeCore 2 X :=
  map_pLayer_sup_pPrimeCore_eq_of_quotient (p := 2) hOH hF

end quotientTransport

end CFSG

end
