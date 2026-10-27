module

public import CFSG.GH74.GLS.C3.Layer1.BkB2G4Def
public import CFSG.GH74.SectionalRank
public import CFSG.LocalAnalysis.ComponentClassification.PrimeComplementQuotientComponents
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.GH74.Generic.BProg

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS
open scoped commutatorElement

theorem map_pPrimeCore_le_of_surjective {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (f : A →* B) (hf : Function.Surjective f) (p : ℕ) [Fact p.Prime] :
    (pPrimeCore p A).map f ≤ pPrimeCore p B := by
  have hN : ((pPrimeCore p A).map f).Normal := (pPrimeCore_normal (p := p) (G := A)).map f hf
  have hcop : Nat.Coprime p (Nat.card ((pPrimeCore p A).map f)) :=
    (pPrimeCore_coprime_card (p := p) (G := A)).coprime_dvd_right (Subgroup.card_map_dvd _ _)
  exact le_sSup ⟨hN, hcop⟩

theorem centralizer_map_quotient_of_sq {X : Type} [Group X] [Finite X] (O : Subgroup X) [O.Normal]
    (hO : Nat.Coprime 2 (Nat.card O)) {d : X} (hd : d * d = 1) :
    (centralizer ({d} : Set X)).map (QuotientGroup.mk' O) =
      centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfact : Fact (IsPGroup 2 ↥(zpowers d)) := by
    refine ⟨?_⟩
    have hord : orderOf d ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hd)
    rcases (Nat.dvd_prime Nat.prime_two).1 hord with hk | hk
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, hk]; rfl)
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hk]; rfl)
  have hcen : centralizer (((zpowers d).map (QuotientGroup.mk' O) : Subgroup (X ⧸ O)) :
        Set (X ⧸ O)) =
      (centralizer ((zpowers d : Subgroup X) : Set X)).map (QuotientGroup.mk' O) :=
    centralizer_map_quotient_eq_map_centralizer 2 (zpowers d) O inferInstance hO
  have hmapz : (zpowers d).map (QuotientGroup.mk' O) = zpowers (QuotientGroup.mk' O d) :=
    MonoidHom.map_zpowers _ d
  rw [hmapz] at hcen
  have h1 : centralizer ((zpowers (QuotientGroup.mk' O d) : Subgroup (X ⧸ O)) : Set (X ⧸ O)) =
      centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O)) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  have h2 : centralizer ((zpowers d : Subgroup X) : Set X) = centralizer ({d} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [h1, h2] at hcen
  exact hcen.symm

section CenQuot

variable {X : Type} [Group X]

@[expose] noncomputable def cenQuot (O : Subgroup X) [O.Normal] (d : X) :
    ↥(centralizer ({d} : Set X)) →* ↥(centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O))) :=
  ((QuotientGroup.mk' O).comp (centralizer ({d} : Set X)).subtype).codRestrict _ (fun c => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h := Subgroup.mem_centralizer_singleton_iff.1 c.2
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [← map_mul, ← map_mul, h])

theorem cenQuot_surjective [Finite X] (O : Subgroup X) [O.Normal]
    (hO : Nat.Coprime 2 (Nat.card O)) {d : X} (hd : d * d = 1) :
    Function.Surjective (cenQuot O d) := by
  rintro ⟨z, hz⟩
  have hz' : z ∈ (centralizer ({d} : Set X)).map (QuotientGroup.mk' O) := by
    rw [centralizer_map_quotient_of_sq O hO hd]; exact hz
  obtain ⟨c, hc, hcz⟩ := hz'
  exact ⟨⟨c, hc⟩, Subtype.ext hcz⟩

theorem mem_of_mem_cenQuot_ker (O : Subgroup X) [O.Normal] (d : X)
    {c : ↥(centralizer ({d} : Set X))} (hc : c ∈ (cenQuot O d).ker) : (c : X) ∈ O := by
  rw [MonoidHom.mem_ker] at hc
  have h2 := congrArg Subtype.val hc
  exact (QuotientGroup.eq_one_iff _).1 h2

theorem cenQuot_ker_odd (O : Subgroup X) [O.Normal] (hO : Nat.Coprime 2 (Nat.card O)) (d : X) :
    ¬ 2 ∣ Nat.card (cenQuot O d).ker := by
  let g : (cenQuot O d).ker →* O :=
    (((centralizer ({d} : Set X)).subtype).comp (cenQuot O d).ker.subtype).codRestrict O
      (fun c => mem_of_mem_cenQuot_ker O d c.2)
  have hg : Function.Injective g := by
    intro a b hab
    have h := congrArg (fun z : O => (z : X)) hab
    exact Subtype.ext (Subtype.ext h)
  have hdvd : Nat.card (cenQuot O d).ker ∣ Nat.card O := Subgroup.card_dvd_of_injective g hg
  have hnot : ¬ 2 ∣ Nat.card O := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hO
  exact fun h => hnot (h.trans hdvd)

theorem isPCompIn_map_cenQuot [Finite X] (O : Subgroup X) [O.Normal]
    (hO : Nat.Coprime 2 (Nat.card O)) {d : X} (hd : d * d = 1) {J : Subgroup X}
    (hJ : IsPCompIn 2 (centralizer ({d} : Set X)) J) :
    IsPCompIn 2 (centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O)))
      (J.map (QuotientGroup.mk' O)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hJC, hJc⟩ := hJ
  have hbij := (CFSG.ComponentClassification.CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection
    (cenQuot O d) (cenQuot_surjective O hO hd) (cenQuot_ker_odd O hO d)).1
  have hmap : IsPComponent 2 ((J.subgroupOf (centralizer ({d} : Set X))).map (cenQuot O d)) :=
    hbij.mapsTo hJc
  have hle : J.map (QuotientGroup.mk' O) ≤
      centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O)) := by
    rintro _ ⟨j, hj, rfl⟩
    exact (cenQuot O d ⟨j, hJC hj⟩).2
  refine ⟨hle, ?_⟩
  have heq : (J.map (QuotientGroup.mk' O)).subgroupOf
      (centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O))) =
      (J.subgroupOf (centralizer ({d} : Set X))).map (cenQuot O d) := by
    ext ⟨z, hz⟩
    constructor
    · rintro ⟨j, hj, hjz⟩
      exact ⟨⟨j, hJC hj⟩, hj, Subtype.ext hjz⟩
    · rintro ⟨⟨c, hc⟩, hcJ, hcz⟩
      exact ⟨c, hcJ, congrArg Subtype.val hcz⟩
  rw [heq]
  exact hmap

theorem map_pPrimeCoreOf_centralizer_le [Finite X] (O : Subgroup X) [O.Normal]
    (hO : Nat.Coprime 2 (Nat.card O)) {d : X} (hd : d * d = 1) :
    (pPrimeCoreOf 2 (centralizer ({d} : Set X))).map (QuotientGroup.mk' O) ≤
      pPrimeCoreOf 2 (centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomp : (QuotientGroup.mk' O).comp (centralizer ({d} : Set X)).subtype =
      (centralizer ({QuotientGroup.mk' O d} : Set (X ⧸ O))).subtype.comp (cenQuot O d) := rfl
  unfold pPrimeCoreOf
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map]
  exact Subgroup.map_mono
    (map_pPrimeCore_le_of_surjective (cenQuot O d) (cenQuot_surjective O hO hd) 2)

end CenQuot

theorem commutator_isCompIn_pPrimeCoreOf {Y : Type*} [Group Y] [Finite Y] {H K : Subgroup Y}
    (hK : IsCompIn H K) : ⁅K, pPrimeCoreOf 2 H⁆ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥H)) :=
    Nat.coprime_two_left.mp (pPrimeCore_coprime_card (p := 2) (G := ↥H))
  have hsolv : Group.IsSolvable (pPrimeCore 2 ↥H) := CFSG.Milestones.odd_order_solvable hodd
  have h := (CFSG.LocalCores.component_solvable_centralizer hsolv
    (pPrimeCore_normal (p := 2) (G := ↥H)).isSubnormal).1 _ hK.2
  have h2 := congrArg (Subgroup.map H.subtype) h
  rw [Subgroup.map_commutator, Subgroup.map_bot, Subgroup.map_subgroupOf_eq_of_le hK.1] at h2
  exact h2

theorem b2_general_core (hB : B_B2_g4) {X : Type} [Group X] [Finite X] (hg : Gen4 X)
    (hK : IsKGroupNative X) {d : X} (hd : orderOf d = 2) :
    ⁅pLayerOf 2 (centralizer ({d} : Set X)), pPrimeCoreOf 2 (centralizer ({d} : Set X))⁆ ≤
      pPrimeCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O : Subgroup X := pPrimeCore 2 X with hOdef
  have hOn : O.Normal := pPrimeCore_normal
  have hO : Nat.Coprime 2 (Nat.card O) := pPrimeCore_coprime_card
  set q : X →* X ⧸ O := QuotientGroup.mk' O with hq
  have hd2 : d * d = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one d
    rwa [hd] at this
  have hqd : orderOf (q d) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow, pow_two, hd2, map_one]
    · intro h
      have hdO : d ∈ O := (QuotientGroup.eq_one_iff d).1 h
      have h2 : 2 ∣ Nat.card O := hd ▸ Subgroup.orderOf_dvd_natCard O hdO
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 hO h2
  have hgb : Gen4 (X ⧸ O) := Gen4.quotient O hg
  have hKb : IsKGroupNative (X ⧸ O) := CFSG.SectionRank.IsKGroupCat.quotient hK O
  have hcore : pPrimeCore 2 (X ⧸ O) = ⊥ := pPrimeCore_quotient_pPrimeCore_eq_bot 2
  have hBb := hB (X ⧸ O) hgb hKb hcore (q d) hqd
  set C : Subgroup X := centralizer ({d} : Set X) with hC
  set Cb : Subgroup (X ⧸ O) := centralizer ({q d} : Set (X ⧸ O)) with hCb
  have hZ : pLayerOf 2 C ≤ (centralizer (pPrimeCoreOf 2 Cb : Set (X ⧸ O))).comap q := by
    refine sSup_le fun J hJ => ?_
    have hJb : IsPCompIn 2 Cb (J.map q) := isPCompIn_map_cenQuot O hO hd2 hJ
    have hcomm := commutator_isCompIn_pPrimeCoreOf (hBb _ hJb)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    exact Subgroup.map_le_iff_le_comap.1 hcomm
  rw [Subgroup.commutator_le]
  intro a ha n hn
  have haZ := hZ ha
  have hnb : q n ∈ pPrimeCoreOf 2 Cb := map_pPrimeCoreOf_centralizer_le O hO hd2 ⟨n, hn, rfl⟩
  have hcomm : q n * q a = q a * q n := Subgroup.mem_centralizer_iff.1 haZ (q n) hnb
  have h1 : q ⁅a, n⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hcomm.symm
  exact (QuotientGroup.eq_one_iff _).1 h1

section Ambient

variable {G : Type*} [Group G]

theorem isPCompIn_subgroupOf {p : ℕ} {M D J : Subgroup G} (hDM : D ≤ M) (hJ : IsPCompIn p D J) :
    IsPCompIn p (D.subgroupOf M) (J.subgroupOf M) := by
  obtain ⟨hJD, hJc⟩ := hJ
  refine ⟨fun x hx => hJD hx, ?_⟩
  let e : ↥(D.subgroupOf M) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDM
  have h := CFSG.LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent p e.symm hJc
  have heq : (J.subgroupOf D).map e.symm.toMonoidHom =
      (J.subgroupOf M).subgroupOf (D.subgroupOf M) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨e x, hx, e.symm_apply_apply x⟩
  rwa [heq] at h

theorem map_pPrimeCoreOf_subgroupOf (p : ℕ) {M D : Subgroup G} (hDM : D ≤ M) :
    (pPrimeCoreOf p (D.subgroupOf M)).map M.subtype = pPrimeCoreOf p D := by
  let e : ↥(D.subgroupOf M) ≃* ↥D := Subgroup.subgroupOfEquivOfLe hDM
  have h := pPrimeCore_map_iso p e
  unfold pPrimeCoreOf
  rw [Subgroup.map_map, ← h, Subgroup.map_map]
  rfl

theorem pLayerOf_le_map_subgroupOf (p : ℕ) {M D : Subgroup G} (hDM : D ≤ M) :
    pLayerOf p D ≤ (pLayerOf p (D.subgroupOf M)).map M.subtype := by
  refine sSup_le fun J hJ => ?_
  have hJM : J ≤ M := hJ.1.trans hDM
  rw [← Subgroup.map_subgroupOf_eq_of_le hJM]
  exact Subgroup.map_mono (le_sSup (isPCompIn_subgroupOf hDM hJ))

theorem centralizer_singleton_mk_eq_subgroupOf {M : Subgroup G} {d : G} (hdM : d ∈ M) :
    centralizer ({(⟨d, hdM⟩ : ↥M)} : Set ↥M) = (M ⊓ centralizer ({d} : Set G)).subgroupOf M := by
  ext a
  rw [mem_centralizer_singleton_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    mem_centralizer_singleton_iff]
  constructor
  · intro h
    exact ⟨a.2, congrArg Subtype.val h⟩
  · intro h
    exact Subtype.ext h.2

end Ambient

theorem b2_general_inf (hB : B_B2_g4) {G : Type} [Group G] [Finite G] {M : Subgroup G}
    (hg : Gen4 ↥M) (hK : IsKGroupNative ↥M) {d : G} (hdM : d ∈ M) (hd : orderOf d = 2) :
    ⁅pLayerOf 2 (M ⊓ centralizer ({d} : Set G)), pPrimeCoreOf 2 (M ⊓ centralizer ({d} : Set G))⁆ ≤
      pPrimeCoreOf 2 M := by
  have hDM : M ⊓ centralizer ({d} : Set G) ≤ M := inf_le_left
  have hd' : orderOf (⟨d, hdM⟩ : ↥M) = 2 := by rw [Subgroup.orderOf_mk]; exact hd
  have h := b2_general_core hB hg hK hd'
  rw [centralizer_singleton_mk_eq_subgroupOf hdM] at h
  have h2 := Subgroup.map_mono (f := M.subtype) h
  rw [Subgroup.map_commutator, map_pPrimeCoreOf_subgroupOf 2 hDM] at h2
  exact (Subgroup.commutator_mono (pLayerOf_le_map_subgroupOf 2 hDM) le_rfl).trans h2

end CFSG.GH74.Generic.BProg
