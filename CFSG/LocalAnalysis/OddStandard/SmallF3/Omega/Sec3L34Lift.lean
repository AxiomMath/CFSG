module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Trans
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

private theorem odd_card_oddCore' (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem centralizer_zpowers_eq {X : Type*} [Group X] (x : X) :
    Subgroup.centralizer ((Subgroup.zpowers x : Subgroup X) : Set X) =
      Subgroup.centralizer ({x} : Set X) := by
  rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]

private theorem isSubnormal_subgroupOf_of_eq {X : Type*} [Group X] {H A B : Subgroup X}
    (hAB : A = B) (h : (H.subgroupOf A).IsSubnormal) : (H.subgroupOf B).IsSubnormal := by
  subst hAB
  exact h

private theorem map_subgroupOf_equivMapOfInjective {X Y : Type*} [Group X] [Group Y]
    (f : X →* Y) (hf : Function.Injective f) {A K : Subgroup X} (hK : K ≤ A) :
    (K.subgroupOf A).map (A.equivMapOfInjective f hf).toMonoidHom =
      (K.map f).subgroupOf (A.map f) := by
  apply Subgroup.map_injective (Subgroup.subtype_injective (A.map f))
  rw [Subgroup.map_map]
  have hcomp : ((A.map f).subtype).comp (A.equivMapOfInjective f hf).toMonoidHom =
      f.comp A.subtype := by
    ext m
    rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le hK,
    Subgroup.map_subgroupOf_eq_of_le (Subgroup.map_mono hK)]

private theorem comap_oddCore_eq {P P' : Type*} [Group P] [Group P'] [Finite P] [Finite P']
    (φ : P →* P') (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) :
    (oddCore P').comap φ = oddCore P := by
  apply le_antisymm
  · have hn : ((oddCore P').comap φ).Normal := (oddCore_normal (G := P')).comap φ
    let g := φ.domRestrict ((oddCore P').comap φ)
    have hcard := Subgroup.card_ker_mul_card_range g
    have hrange : Nat.card g.range ∣ Nat.card (oddCore P') := by
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨v, rfl⟩
      exact v.2
    have hkerdvd : Nat.card g.ker ∣ Nat.card φ.ker := by
      have hsub : g.ker.map ((oddCore P').comap φ).subtype ≤ φ.ker := by
        rintro _ ⟨v, hv, rfl⟩
        exact MonoidHom.mem_ker.2 (MonoidHom.mem_ker.1 hv)
      rw [← Subgroup.card_map_of_injective (K := g.ker)
        ((oddCore P').comap φ).subtype_injective]
      exact Subgroup.card_dvd_of_le hsub
    have hodd : Odd (Nat.card ((oddCore P').comap φ)) := by
      rw [← hcard]
      exact (hker.of_dvd_nat hkerdvd).mul
        ((odd_card_oddCore' P').of_dvd_nat hrange)
    exact le_sSup ⟨hn, hodd⟩
  · rw [← Subgroup.map_le_iff_le_comap]
    have hn : ((oddCore P).map φ).Normal := (oddCore_normal (G := P)).map φ hφ
    have hodd : Odd (Nat.card ((oddCore P).map φ)) :=
      (odd_card_oddCore' P).of_dvd_nat (Subgroup.card_map_dvd _ φ)
    exact le_sSup ⟨hn, hodd⟩

private noncomputable def oddCoreQuotientEquiv {P P' : Type*} [Group P] [Group P']
    [Finite P] [Finite P']
    (φ : P →* P') (hφ : Function.Surjective φ) (hker : Odd (Nat.card φ.ker)) :
    P ⧸ oddCore P ≃* P' ⧸ oddCore P' :=
  (QuotientGroup.quotientMulEquivOfEq (by
      rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      exact (comap_oddCore_eq φ hφ hker).symm)).trans
    (QuotientGroup.quotientKerEquivOfSurjective
      ((QuotientGroup.mk' (oddCore P')).comp φ)
      ((QuotientGroup.mk'_surjective _).comp hφ))

private theorem map_top_inf_centralizer_subtype_eq {X : Type*} [Group X] (I : Subgroup X)
    (y : X) (hyI : y ∈ I) :
    (⊤ ⊓ Subgroup.centralizer ({⟨y, hyI⟩} : Set ↥I)).map I.subtype =
      I ⊓ Subgroup.centralizer ({y} : Set X) := by
  ext g
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.2, Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz.2))⟩
  · rintro ⟨hgI, hgC⟩
    exact ⟨⟨g, hgI⟩, ⟨Subgroup.mem_top _,
      Subgroup.mem_centralizer_singleton_iff.mpr
        (Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hgC))⟩, rfl⟩

theorem isI4PlusIn_top_of_quotient {A : Type} [Group A] [Finite A] {a : A} (ha : orderOf a = 2)
    (h : IsI4PlusIn (⊤ : Subgroup (A ⧸ oddCore A)) (QuotientGroup.mk a)) :
    IsI4PlusIn (⊤ : Subgroup A) a := by
  rw [IsI4PlusIn] at h ⊢
  refine ⟨ha, ?_⟩
  obtain ⟨Kbar, hKbar⟩ := h.2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let q : A →* A ⧸ oddCore A := QuotientGroup.mk' (oddCore A)
  let C : Subgroup A := Subgroup.centralizer ({a} : Set A)
  let Bbar : Subgroup (A ⧸ oddCore A) := Subgroup.centralizer ({q a} : Set (A ⧸ oddCore A))
  haveI : Fact (IsPGroup 2 (Subgroup.zpowers a)) :=
    ⟨IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ha]; norm_num)⟩
  have hNodd : Odd (Nat.card (oddCore A)) := odd_card_oddCore' A
  have hcop : Nat.Coprime 2 (Nat.card (oddCore A)) := Nat.coprime_two_left.mpr hNodd
  have haC : a ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  let ψ : ↥C →* ↥Bbar := (q.comp C.subtype).codRestrict Bbar (fun c => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    show q (c : A) * q a = q a * q (c : A)
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_singleton_iff.mp c.2])
  have hCmap : C.map q = Bbar := by
    have hmain := CFSG.centralizer_map_quotient_eq_map_centralizer 2 (Subgroup.zpowers a)
      (oddCore A) (oddCore_normal (G := A)) hcop
    dsimp only at hmain
    rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at hmain
    exact hmain.symm
  have hψsurj : Function.Surjective ψ := by
    intro y
    have hy : (y : A ⧸ oddCore A) ∈ C.map q := by
      rw [hCmap]
      exact y.2
    obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨c, hc⟩, Subtype.ext hcq⟩
  let K0 : Subgroup ↥C := (Kbar.subgroupOf Bbar).comap ψ
  have hKbarB : (Kbar.subgroupOf Bbar).IsSubnormal :=
    isSubnormal_subgroupOf_of_eq (top_inf_eq Bbar) hKbar.2.2.1
  have hK0sub : K0.IsSubnormal := Subgroup.IsSubnormal.comap ψ hKbarB
  let K : Subgroup A := K0.map C.subtype
  have haK : a ∈ K := by
    refine Subgroup.mem_map.mpr ⟨⟨a, haC⟩, ?_, rfl⟩
    dsimp only [K0]
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    exact hKbar.1
  have hKle : K ≤ ⊤ ⊓ Subgroup.centralizer ({a} : Set A) :=
    le_inf le_top (Subgroup.map_subtype_le K0)
  have hKsubC : (K.subgroupOf C).IsSubnormal := by
    have h : (K0.map C.subtype).subgroupOf C = K0 :=
      Subgroup.comap_map_eq_self_of_injective C.subtype_injective K0
    rw [show K = K0.map C.subtype from rfl, h]
    exact hK0sub
  have hKsub : (K.subgroupOf (⊤ ⊓ Subgroup.centralizer ({a} : Set A))).IsSubnormal :=
    isSubnormal_subgroupOf_of_eq (top_inf_eq C).symm hKsubC
  have hψker_le : ψ.ker.map C.subtype ≤ oddCore A := by
    rintro _ ⟨c, hc, rfl⟩
    have h1 : q (c : A) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hc)
    exact (QuotientGroup.eq_one_iff (c : A)).mp h1
  have hψodd : Odd (Nat.card ψ.ker) := by
    refine hNodd.of_dvd_nat ?_
    rw [← Subgroup.card_map_of_injective (K := ψ.ker) C.subtype_injective]
    exact Subgroup.card_dvd_of_le hψker_le
  have hKbar_le_Bbar : Kbar ≤ Bbar := hKbar.2.1.trans inf_le_right
  let ψK : ↥K0 →* ↥(Kbar.subgroupOf Bbar) :=
    (ψ.comp K0.subtype).codRestrict (Kbar.subgroupOf Bbar)
      (fun k => Subgroup.mem_comap.mp k.2)
  have hψKsurj : Function.Surjective ψK := by
    intro y
    obtain ⟨c, hc⟩ := hψsurj ⟨(y : A ⧸ oddCore A), hKbar_le_Bbar y.2⟩
    have hcy : (ψ c : A ⧸ oddCore A) = (y : A ⧸ oddCore A) := congrArg Subtype.val hc
    have hcK0 : c ∈ K0 := by
      dsimp only [K0]
      rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
      rw [hcy]
      exact y.2
    refine ⟨⟨c, hcK0⟩, Subtype.ext (Subtype.ext hcy)⟩
  have hψKker : ψK.ker = ψ.ker.comap K0.subtype := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap, MonoidHom.mem_ker]
    constructor
    · intro hx
      exact Subtype.ext
        (congrArg (fun z : ↥(Kbar.subgroupOf Bbar) => (z : A ⧸ oddCore A)) hx)
    · intro hx
      exact Subtype.ext hx
  have hψKodd : Odd (Nat.card ψK.ker) := by
    refine hψodd.of_dvd_nat ?_
    rw [hψKker]
    exact Subgroup.card_comap_dvd_of_injective ψ.ker K0.subtype K0.subtype_injective
  have hKbarSubMod : IsSL23Mod ↥(Kbar.subgroupOf Bbar) :=
    isSL23Mod_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKbar_le_Bbar).symm hKbar.2.2.2
  have hK0mod : IsSL23Mod ↥K0 := by
    obtain ⟨e⟩ := hKbarSubMod
    exact ⟨(oddCoreQuotientEquiv ψK hψKsurj hψKodd).trans e⟩
  have hKmod : IsSL23Mod ↥K := isSL23Mod_of_mulEquiv
    (Subgroup.equivMapOfInjective K0 C.subtype C.subtype_injective) hK0mod
  exact ⟨K, haK, hKle, hKsub, hKmod⟩

theorem isI4PlusIn_of_top {I : Subgroup G} {y : G} (hyI : y ∈ I)
    (h : IsI4PlusIn (⊤ : Subgroup ↥I) (⟨y, hyI⟩ : ↥I)) : IsI4PlusIn I y := by
  rw [IsI4PlusIn] at h ⊢
  refine ⟨(Subgroup.orderOf_mk y hyI).symm.trans h.1, ?_⟩
  obtain ⟨K', hK'⟩ := h.2
  let H : Subgroup G := I ⊓ Subgroup.centralizer ({y} : Set G)
  let H' : Subgroup ↥I := ⊤ ⊓ Subgroup.centralizer ({⟨y, hyI⟩} : Set ↥I)
  let K : Subgroup G := K'.map I.subtype
  have hK'le : K' ≤ H' := hK'.2.1
  have hgen := map_subgroupOf_equivMapOfInjective I.subtype I.subtype_injective hK'le
  have h1 : (K.subgroupOf (H'.map I.subtype)).IsSubnormal := by
    have hm : ((K'.subgroupOf H').map
        (H'.equivMapOfInjective I.subtype I.subtype_injective).toMonoidHom).IsSubnormal :=
      Subgroup.IsSubnormal.map
        (f := (H'.equivMapOfInjective I.subtype I.subtype_injective).toMonoidHom)
        (H'.equivMapOfInjective I.subtype I.subtype_injective).surjective hK'.2.2.1
    rw [hgen] at hm
    exact hm
  have hHmap : H'.map I.subtype = H := map_top_inf_centralizer_subtype_eq I y hyI
  have hKsub : (K.subgroupOf H).IsSubnormal := isSubnormal_subgroupOf_of_eq hHmap h1
  refine ⟨K, ?_, ?_, ?_, ?_⟩
  · exact Subgroup.mem_map.mpr ⟨⟨y, hyI⟩, hK'.1, rfl⟩
  · refine le_inf (Subgroup.map_subtype_le _) ?_
    rintro _ ⟨k', hk', rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp (hK'.2.1 hk').2))
  · simpa [H] using hKsub
  · exact isSL23Mod_of_mulEquiv
      (Subgroup.equivMapOfInjective K' I.subtype I.subtype_injective) hK'.2.2.2

end CFSG.OddStandard.SmallF3.Omega
