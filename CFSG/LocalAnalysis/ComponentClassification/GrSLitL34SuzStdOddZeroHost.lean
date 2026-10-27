module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34SuzStdOddDichHost
public import CFSG.LocalAnalysis.ComponentClassification.GS82HConfigQuot

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open CFSG Subgroup

variable {G : Type} [Group G] [Finite G]

theorem exists_isPComponent_lift_of_isComponent {b : G}
    {L : Subgroup (↥(centralizer ({b} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({b} : Set G)))}
    (hL : IsComponent L) :
    ∃ M : Subgroup G, M ≤ centralizer ({b} : Set G) ∧
      IsPComponent 2 (M.subgroupOf (centralizer ({b} : Set G))) ∧
      Nonempty (↥M ⧸ Open.fusionZStar ↥M ≃* ↥L ⧸ center ↥L) ∧
      (∀ P : Subgroup G, P ≤ centralizer ({b} : Set G) → Group.IsPerfect ↥P →
        (P.subgroupOf (centralizer ({b} : Set G))).map
          (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))) ≤ L → P ≤ M) ∧
      ∀ (x : G) (hxb : x ∈ centralizer ({b} : Set G)),
        L.map (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))
          ⟨x, hxb⟩)).toMonoidHom = L → M.map (MulAut.conj x).toMonoidHom = M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer ({b} : Set G)
  let π : ↥C →* (↥C ⧸ pPrimeCore 2 ↥C) := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  let M₀ : Subgroup ↥C := CatalogueBPrimeJoin.canonicalPrimeLift 2 L
  have hlift := (CatalogueBPrimeJoin.canonical_prime_component_lift (X := ↥C) (p := 2)).1 L hL
  have hM₀ : IsPComponent 2 M₀ := hlift.1
  have hM₀π : M₀.map π = L := hlift.2.1
  have hMC : M₀.map C.subtype ≤ C := Subgroup.map_subtype_le M₀
  have hMsub : (M₀.map C.subtype).subgroupOf C = M₀ :=
    Subgroup.comap_map_eq_self_of_injective C.subtype_injective M₀
  have hMcomp : IsPComponent 2 ((M₀.map C.subtype).subgroupOf C) := by
    rw [hMsub]
    exact hM₀
  have hML : ((M₀.map C.subtype).subgroupOf C).map π = L := by
    rw [hMsub, hM₀π]
  obtain ⟨e⟩ := nonempty_image_center_quotient_equiv hMC hMcomp
  rw [hML] at e
  refine ⟨M₀.map C.subtype, hMC, hMcomp, ⟨e.symm⟩, ?_, ?_⟩
  · intro P hPb hPperf hPL'
    have hPC : P ≤ C := hPb
    have hq : Group.IsPerfect ↥(P.subgroupOf C) :=
      Group.IsPerfect.ofSurjective
        (f := (Subgroup.subgroupOfEquivOfLe hPC).symm.toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe hPC).symm.surjective
    have hPM : P.subgroupOf C ≤ L.comap π := Subgroup.map_le_iff_le_comap.mp hPL'
    have hle := GSThmB.HConfig.le_canonicalPrimeLift_of_isPerfect (H := ↥C) L hq hPM
    rw [← Subgroup.map_subgroupOf_eq_of_le hPC]
    exact Subgroup.map_mono hle
  · intro x hxb hLx
    have hd : π ⟨x, hxb⟩ ∈ Subgroup.normalizer ((M₀.map π : Subgroup _) : Set _) := by
      rw [hM₀π, Subgroup.mem_normalizer_iff_map_conj_eq]
      exact hLx
    have hxN : (⟨x, hxb⟩ : ↥C) ∈ Subgroup.normalizer (M₀ : Set ↥C) :=
      UnbalancedLayer.mem_normalizer_of_map hM₀ hd
    have hconj : M₀.map (MulAut.conj (⟨x, hxb⟩ : ↥C)).toMonoidHom = M₀ :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hxN
    have hcomp : C.subtype.comp (MulAut.conj (⟨x, hxb⟩ : ↥C)).toMonoidHom =
        (MulAut.conj x).toMonoidHom.comp C.subtype := by
      ext y
      simp [MulAut.conj_apply]
    calc (M₀.map C.subtype).map (MulAut.conj x).toMonoidHom
        = M₀.map ((MulAut.conj x).toMonoidHom.comp C.subtype) := by rw [Subgroup.map_map]
      _ = M₀.map (C.subtype.comp (MulAut.conj (⟨x, hxb⟩ : ↥C)).toMonoidHom) := by
          rw [← hcomp]
      _ = (M₀.map (MulAut.conj (⟨x, hxb⟩ : ↥C)).toMonoidHom).map C.subtype := by
          rw [Subgroup.map_map]
      _ = M₀.map C.subtype := by rw [hconj]

theorem false_of_host_onan_field_of_l34
    (hSch : LocalAnalysis.ComponentInitial.SchreierFor Blueprint.Catalog)
    (hC5 : L3TwoPowProperFixedCatalog) (hCI : GSLit.ClassicalInvolutionInput)
    (hGA : TBLit.GriessMultipliersAllModels) (h13 : Sol76T13.SolomonThm13Simple)
    (hCField : L34FieldCoreStepMirror) (hSField : L34FieldStandardExclusion)
    (hG : L34BaseSetting G) {b : G} (hb : orderOf b = 2) {P : Subgroup G}
    (hPb : P ≤ centralizer ({b} : Set G)) (hPq : IsQuasisimple ↥P)
    (hPodd : Odd (Nat.card (center ↥P))) (hPL : IsL34Type (↥P ⧸ center ↥P))
    {L : Subgroup (↥(centralizer ({b} : Set G)) ⧸ pPrimeCore 2 ↥(centralizer ({b} : Set G)))}
    (hL : IsComponent L)
    (hPL' : (P.subgroupOf (centralizer ({b} : Set G))).map
      (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer ({b} : Set G)))) ≤ L)
    (htype : Blueprint.NativeSporadic.IsSporadic (↥L ⧸ center ↥L) .ONan ∨
      Blueprint.LieModel (↥L ⧸ center ↥L) .PSL 3 2 4) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let C : Subgroup G := centralizer ({b} : Set G)
  let π : ↥C →* (↥C ⧸ pPrimeCore 2 ↥C) := QuotientGroup.mk' (pPrimeCore 2 ↥C)
  rcases htype with hON | hF
  ·
    have hPC : P ≤ C := hPb
    have hPqC : IsQuasisimple ↥(P.subgroupOf C) :=
      (IsQuasisimple.congr (Subgroup.subgroupOfEquivOfLe hPC)).mpr hPq
    have hPoddC : Odd (Nat.card (center ↥(P.subgroupOf C))) := by
      have hcard : Nat.card (center ↥(P.subgroupOf C)) = Nat.card (center ↥P) :=
        Nat.card_congr (Subgroup.centerCongr (Subgroup.subgroupOfEquivOfLe hPC)).toEquiv
      rw [hcard]
      exact hPodd
    have hZP : Open.fusionZStar ↥P = center ↥P :=
      GrS5.fusionZStar_eq_center_of_le hPq.1.commutator_eq_top
        (CFSG.GH74.Generic.BProg.B2.Prop31.normal_le_center_of_odd hPq inferInstance
          (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
    have hZPC : Open.fusionZStar ↥(P.subgroupOf C) = center ↥(P.subgroupOf C) :=
      GrS5.fusionZStar_eq_center_of_le hPqC.1.commutator_eq_top
        (CFSG.GH74.Generic.BProg.B2.Prop31.normal_le_center_of_odd hPqC inferInstance
          (Nat.coprime_two_left.mp pPrimeCore_coprime_card))
    have hPLzs : IsL34Type (↥P ⧸ Open.fusionZStar ↥P) :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hZP).symm hPL
    have hPLtypeC : IsL34Type (↥(P.subgroupOf C) ⧸ center ↥(P.subgroupOf C)) :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hZPC) (GrS4.isL34Type_subgroupOf hPC hPLzs)
    obtain ⟨hDq, hDodd, hDtype⟩ :=
      isQuasisimple_map_pPrimeCore_and_odd_card_center_and_isL34Type (C := ↥C)
        (K := P.subgroupOf C) hPqC hPoddC hPLtypeC
    exact false_of_le_onan_of_l34_odd (X := ↥C ⧸ pPrimeCore 2 ↥C)
      (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hL hON hPL'
      (D := (P.subgroupOf C).map π) hDq hDodd hDtype
  ·
    obtain ⟨M, hMb, hM, ⟨e⟩, hPle, -⟩ := exists_isPComponent_lift_of_isComponent hL
    have hML : Blueprint.LieModel (↥M ⧸ Open.fusionZStar ↥M) .PSL 3 2 4 :=
      CFSG.LieType.CurtisTits.lieModel_of_mulEquiv e.symm hF
    exact false_of_isPComponent_field_of_l34Base hSch hC5 hCI hGA h13 hCField hSField hG hb hMb hM
      (n := 4) le_rfl ⟨2, by norm_num⟩ hML

end CFSG.ComponentClassification.GrSLit.L34Sec5S
