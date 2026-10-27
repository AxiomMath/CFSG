module

public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.Residual
public import CFSG.LocalAnalysis.EvenSporadicStandard.McLStd.ComponentSwap

public section

namespace CFSG.EvenSporadicStandard.McLStd

open Subgroup CFSG CFSG.ComponentClassification CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem exists_hom_of_swappedPair {L : Subgroup G} {t u : G} (ht2 : orderOf t = 2)
    (htu : t ∈ centralizer ({u} : Set G)) (hLt : L ≤ centralizer ({t} : Set G))
    (hC : centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) ≤
      zpowers t ⊔ (centralizer ({u} : Set G) ⊓ L))
    (hsw : SwappedPair L t u) :
    ∃ φ : centralizer ({u} : Set G) →* Multiplicative (ZMod 2), φ ⟨t, htu⟩ ≠ 1 := by
  obtain ⟨J, hJ, hJt, hKJ, -⟩ := hsw
  set H : Subgroup G := centralizer ({u} : Set G) with hH
  have hJH : J ≤ H := CFSG.Quasithin.le_of_mem_cComp hJ.1
  have hts : t * t = 1 := by rw [← pow_two, ← ht2, pow_orderOf_eq_one]
  set O : Subgroup ↥H := Open.componentClassificationOddCore ↥H with hO
  let π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective O
  have hker : Odd (Nat.card π.ker) := by
    rw [QuotientGroup.ker_mk']
    exact OddCore.odd_card ↥H
  have hcore : Open.componentClassificationOddCore (↥H ⧸ O) = ⊥ := OddCore.quotient_corefree ↥H
  let t' : ↥H := ⟨t, htu⟩
  have ht't' : t' * t' = 1 := Subtype.ext (by simpa using hts)
  have ht'ord : orderOf t' = 2 := by
    rw [← Subgroup.orderOf_coe]
    exact ht2
  have hπt : π t' * π t' = 1 := by rw [← map_mul, ht't', map_one]
  let A : Subgroup ↥H := J.subgroupOf H
  have hAmap : A.map H.subtype = J := Subgroup.map_subgroupOf_eq_of_le hJH
  have hA : TwoComponents.IsTwoComponent A := (I32.isTwoComponentIn_iff hJH).1 hJ
  have hA' : TwoComponents.IsTwoComponent (CFSG.conjugate A t') := by
    rw [I32.conjugate_eq_map_conj ht't' A]
    exact (TwoComponentTransport.equiv_iff (MulAut.conj t') A).2 hA
  have hA'map : (CFSG.conjugate A t').map H.subtype = CFSG.conjugate J t := by
    have h1 := I32.map_conjugate H.subtype A t'
    rw [hAmap] at h1
    exact h1
  have hAπ : TwoComponents.IsTwoComponent (A.map π) :=
    OddKernelTwoComponents.image π hsurj hker A hA
  have hĀ : IsComponent (A.map π) :=
    (isComponent_iff_open _).2 (TwoComponents.ordinary_of_corefree hcore hAπ)
  have hAπ' : (CFSG.conjugate A t').map π = conjSub (π t') (A.map π) := by
    rw [I32.map_conjugate π A t']
    exact I32.conjugate_eq_map_conj hπt (A.map π)
  have hne : conjSub (π t') (A.map π) ≠ A.map π := by
    intro h
    rw [← hAπ'] at h
    have hAA' : CFSG.conjugate A t' = A :=
      OddKernelTwoComponents.lift_unique π hsurj hker _ _ hA' hA h
    apply hJt
    rw [← hA'map, hAA', hAmap]
  have hBH : centralizer ({u} : Set G) ⊓ L ≤ H := inf_le_left
  have hBle : (centralizer ({u} : Set G) ⊓ L).subgroupOf H ≤ A ⊔ CFSG.conjugate A t' := by
    intro b hb
    have hb' : (b : G) ∈ centralizer ({u} : Set G) ⊓ L := hb
    have hK : (b : G) ∈ (A ⊔ CFSG.conjugate A t').map H.subtype := by
      rw [Subgroup.map_sup, hAmap, hA'map, ← hKJ]
      exact le_layerClosure L u hb'
    obtain ⟨y, hy, hyb⟩ := hK
    have : y = b := Subtype.ext hyb
    rwa [← this]
  have hBπ : ((centralizer ({u} : Set G) ⊓ L).subgroupOf H).map π ≤
      A.map π ⊔ conjSub (π t') (A.map π) := by
    calc ((centralizer ({u} : Set G) ⊓ L).subgroupOf H).map π
        ≤ (A ⊔ CFSG.conjugate A t').map π := Subgroup.map_mono hBle
      _ = A.map π ⊔ (CFSG.conjugate A t').map π := Subgroup.map_sup _ _ _
      _ = A.map π ⊔ conjSub (π t') (A.map π) := by rw [hAπ']
  have hBs : ((centralizer ({u} : Set G) ⊓ L).subgroupOf H).map π ≤
      centralizer ({π t'} : Set (↥H ⧸ O)) := by
    rintro _ ⟨b, hb, rfl⟩
    rw [mem_centralizer_singleton_iff]
    have hbL : (b : G) ∈ L := (show (b : G) ∈ centralizer ({u} : Set G) ⊓ L from hb).2
    have h1 : (b : G) * t = t * (b : G) := mem_centralizer_singleton_iff.1 (hLt hbL)
    have h2 : b * t' = t' * b := Subtype.ext h1
    rw [← map_mul, ← map_mul, h2]
  have hC' : centralizer ({π t'} : Set (↥H ⧸ O)) ≤
      zpowers (π t') ⊔ ((centralizer ({u} : Set G) ⊓ L).subgroupOf H).map π := by
    rw [← OddKernelInvolutions.image_centralizer π hsurj hker t' ht'ord]
    rintro _ ⟨x, hx, rfl⟩
    have hxt : (x : G) * t = t * (x : G) :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 hx)
    have hxG : (x : G) ∈ centralizer ({t} : Set G) ⊓ centralizer ({u} : Set G) :=
      ⟨mem_centralizer_singleton_iff.2 hxt, x.2⟩
    have hmem := hC hxG
    have hxX : x ∈ zpowers t' ⊔ (centralizer ({u} : Set G) ⊓ L).subgroupOf H := by
      have h1 : (x : G) ∈
          (zpowers t' ⊔ (centralizer ({u} : Set G) ⊓ L).subgroupOf H).map H.subtype := by
        rw [Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hBH]
        exact hmem
      obtain ⟨y, hy, hyx⟩ := h1
      have : y = x := Subtype.ext hyx
      rwa [← this]
    have h2 := Subgroup.mem_map_of_mem π hxX
    rwa [Subgroup.map_sup, MonoidHom.map_zpowers] at h2
  obtain ⟨φ, hφ⟩ := exists_hom_of_swapped_component hπt hĀ hne hBπ hBs hC'
  exact ⟨φ.comp π, hφ⟩

end CFSG.EvenSporadicStandard.McLStd
