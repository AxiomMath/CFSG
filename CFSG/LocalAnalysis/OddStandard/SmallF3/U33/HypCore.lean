module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.U33.HypLayer
public import CFSG.LocalAnalysis.ComponentInitial.StandardBasics
public import CFSG.GroupTheory.CyclicSylowNormalOddComplement
public import CFSG.GroupTheory.Fitting.LayerTopBot

public section

namespace CFSG.OddStandard.SmallF3.HarrisU33

open Subgroup

open scoped Pointwise

private theorem isCyclic_comap_of_injective {A B : Type*} [Group A] [Group B]
    (f : A →* B) (hf : Function.Injective f) (Q : Subgroup B) (hQ : IsCyclic ↥Q) :
    IsCyclic ↥(Q.comap f) := by
  haveI : IsCyclic ↥Q := hQ
  refine isCyclic_of_injective
    ((f.domRestrict (Q.comap f)).codRestrict Q (fun x => x.2)) ?_
  intro x y h
  exact Subtype.ext (hf (congrArg (fun z : ↥Q => (z : B)) h))

private theorem isCyclic_sylow_of_le_centralizer {G : Type} [Group G] [Finite G]
    {L R : Subgroup G}
    (hcyc : ∀ S : Sylow 2 ↥(Subgroup.centralizer (L : Set G)),
      IsCyclic (S : Subgroup ↥(Subgroup.centralizer (L : Set G))))
    (hR : R ≤ Subgroup.centralizer (L : Set G)) (S : Sylow 2 ↥R) :
    IsCyclic (S : Subgroup ↥R) := by
  let C : Subgroup G := Subgroup.centralizer (L : Set G)
  let g : ↥R →* ↥C := R.subtype.codRestrict C (fun x => hR x.2)
  have hg : Function.Injective g := fun a b h =>
    R.subtype_injective (congrArg (fun z : ↥C => (z : G)) h)
  obtain ⟨Q, hQ⟩ := S.exists_comap_eq_of_injective (f := g) hg
  have hcomap : IsCyclic ↥((Q : Subgroup ↥C).comap g) :=
    isCyclic_comap_of_injective g hg (Q : Subgroup ↥C) (hcyc Q)
  rw [← hQ]
  exact hcomap

private theorem isCyclic_sylow_of_equiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (hcyc : ∀ S : Sylow 2 B, IsCyclic (S : Subgroup B)) (S : Sylow 2 A) :
    IsCyclic (S : Subgroup A) := by
  obtain ⟨Q, hQ⟩ := S.exists_comap_eq_of_injective (f := e.toMonoidHom) e.injective
  have hcomap : IsCyclic ↥((Q : Subgroup B).comap e.toMonoidHom) :=
    isCyclic_comap_of_injective e.toMonoidHom e.injective (Q : Subgroup B) (hcyc Q)
  rw [← hQ]
  exact hcomap

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

private theorem oddCore_eq_pPrimeCore_two_local (H : Type*) [Group H] :
    CFSG.oddCore H = CFSG.pPrimeCore 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact (CFSG.oddCore_eq_piCore H).trans (CFSG.pPrimeCore_eq_piCore H 2).symm

private theorem centralizer_inf_subgroupOf_aux (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    IsCyclic ↥((Subgroup.centralizer (L : Set G) ⊓ invCent t).subgroupOf (invCent t)) ∧
      IsPGroup 2 ((Subgroup.centralizer (L : Set G) ⊓ invCent t).subgroupOf (invCent t)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := invCent t
  set R : Subgroup G := Subgroup.centralizer (L : Set G) ⊓ H
  have hRH : R ≤ H := inf_le_right
  have hRC : R ≤ Subgroup.centralizer (L : Set G) := inf_le_left
  obtain ⟨-, -, -, -, hRn⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hC.standard htL ht
  have hR'n : (R.subgroupOf H).Normal := hRn
  haveI : (R.subgroupOf H).Normal := hR'n
  let S' : Sylow 2 ↥(R.subgroupOf H) := default
  have hS'cyc : IsCyclic (S' : Subgroup ↥(R.subgroupOf H)) :=
    isCyclic_sylow_of_equiv (Subgroup.subgroupOfEquivOfLe hRH)
      (fun S => isCyclic_sylow_of_le_centralizer (L := L) hC.cyclic hRC S) S'
  obtain ⟨-, hcover, -, ⟨-, hNodd, -, -⟩, hNchar⟩ :=
    CFSG.cyclic_sylow_normal_odd_complement (G := ↥(R.subgroupOf H)) S' hS'cyc
  have hNbot : CFSG.pPrimeCore 2 ↥(R.subgroupOf H) = ⊥ := by
    have hHO : CFSG.oddCore ↥H = ⊥ := hC.balanced t ht
    rw [oddCore_eq_pPrimeCore_two_local] at hHO
    haveI : (CFSG.pPrimeCore 2 ↥(R.subgroupOf H)).Characteristic := hNchar
    have hNmapn : ((CFSG.pPrimeCore 2 ↥(R.subgroupOf H)).map
        (R.subgroupOf H).subtype).Normal :=
      ConjAct.normal_of_characteristic_of_normal
    have hNmapodd : Odd (Nat.card ((CFSG.pPrimeCore 2 ↥(R.subgroupOf H)).map
        (R.subgroupOf H).subtype)) := by
      rw [Subgroup.card_map_of_injective (R.subgroupOf H).subtype_injective]
      exact hNodd
    have hle : (CFSG.pPrimeCore 2 ↥(R.subgroupOf H)).map (R.subgroupOf H).subtype ≤
        CFSG.pPrimeCore 2 ↥H :=
      CFSG.le_pPrimeCore_of_normal_coprime hNmapn (Nat.coprime_two_left.mpr hNmapodd)
    have hbot : (CFSG.pPrimeCore 2 ↥(R.subgroupOf H)).map (R.subgroupOf H).subtype = ⊥ :=
      le_bot_iff.mp (hle.trans_eq hHO)
    rwa [Subgroup.map_eq_bot_iff_of_injective _ (R.subgroupOf H).subtype_injective] at hbot
  have hS'top : (S' : Subgroup ↥(R.subgroupOf H)) = ⊤ := by
    rw [hNbot] at hcover
    have hScov : (S' : Set ↥(R.subgroupOf H)) = Set.univ := by
      refine Set.eq_univ_iff_forall.mpr fun x => ?_
      have hxmem : x ∈ ((⊥ : Subgroup ↥(R.subgroupOf H)) : Set ↥(R.subgroupOf H)) *
          (S' : Set ↥(R.subgroupOf H)) := by rw [hcover]; trivial
      rw [Set.mem_mul] at hxmem
      obtain ⟨a, ha, b, hb, hab⟩ := hxmem
      have ha1 : a = 1 := Subgroup.mem_bot.mp ha
      rw [← hab, ha1, one_mul]
      exact hb
    refine Subgroup.ext fun x => ?_
    have hx : x ∈ (S' : Set ↥(R.subgroupOf H)) := by rw [hScov]; trivial
    exact ⟨fun _ => trivial, fun _ => hx⟩
  refine ⟨?_, ?_⟩
  · have htop : IsCyclic (⊤ : Subgroup ↥(R.subgroupOf H)) := by
      rw [← hS'top]
      exact hS'cyc
    exact Subgroup.topEquiv.isCyclic.mp htop
  · have htop : IsPGroup 2 (⊤ : Subgroup ↥(R.subgroupOf H)) := by
      rw [← hS'top]
      exact S'.isPGroup'
    exact htop.of_equiv Subgroup.topEquiv

private theorem isCyclic_inf (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    IsCyclic ↥(Subgroup.centralizer (L : Set G) ⊓ invCent t) := by
  have h := (centralizer_inf_subgroupOf_aux hC ht htL).1
  exact (Subgroup.subgroupOfEquivOfLe
    (inf_le_right : Subgroup.centralizer (L : Set G) ⊓ invCent t ≤ invCent t)).isCyclic.mp h

private theorem le_twoCore (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    Subgroup.centralizer (L : Set G) ⊓ invCent t ≤ twoCore t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hR'p⟩ := centralizer_inf_subgroupOf_aux hC ht htL
  set H : Subgroup G := invCent t
  set R : Subgroup G := Subgroup.centralizer (L : Set G) ⊓ H
  obtain ⟨-, -, -, -, hRn⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.standard_involution_centralizer_normality
      hC.standard htL ht
  have hR'n : (R.subgroupOf H).Normal := hRn
  have hR'le : R.subgroupOf H ≤ CFSG.pCore 2 ↥H :=
    le_sSup (show (R.subgroupOf H).Normal ∧ IsPGroup 2 (R.subgroupOf H) from ⟨hR'n, hR'p⟩)
  calc R = (R.subgroupOf H).map H.subtype := (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
    _ ≤ (CFSG.pCore 2 ↥H).map H.subtype := Subgroup.map_mono hR'le
    _ = twoCore t := rfl

private theorem twoCore_le (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    twoCore t ≤ Subgroup.centralizer (L : Set G) ⊓ invCent t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change (CFSG.pCore 2 ↥(invCent t)).map (invCent t).subtype ≤
    Subgroup.centralizer (L : Set G) ⊓ invCent t
  refine le_inf ?_ (Subgroup.map_subtype_le _)
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  obtain ⟨y, hy, rfl⟩ := hx
  have hlayer : CFSG.inSubgroup CFSG.layer (invCent t) = L :=
    inSubgroup_layer_invCent_eq hC ht htL
  rw [← hlayer] at hl
  obtain ⟨z, hz, rfl⟩ := hl
  have hle : CFSG.pCore 2 ↥(invCent t) ≤
      Subgroup.centralizer (CFSG.layer ↥(invCent t) : Set ↥(invCent t)) :=
    CFSG.WholeGroup.pCore_le_centralizer_layer (G := ↥(invCent t)) 2
  have hcomm : z * y = y * z := Subgroup.mem_centralizer_iff.mp (hle hy) z hz
  exact congrArg (fun w : ↥(invCent t) => (w : G)) hcomm

theorem centralizer_inf_invCent_eq_twoCore (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    Subgroup.centralizer (L : Set G) ⊓ invCent t = twoCore t :=
  le_antisymm (le_twoCore hC ht htL) (twoCore_le hC ht htL)

theorem isCyclic_twoCore (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    IsCyclic (twoCore t) := by
  rw [← centralizer_inf_invCent_eq_twoCore hC ht htL]
  exact isCyclic_inf hC ht htL

theorem mem_twoCore (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G)) :
    t ∈ twoCore t := by
  rw [← centralizer_inf_invCent_eq_twoCore hC ht htL]
  exact ⟨htL, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩

theorem eq_one_or_eq_of_mem_twoCore_of_sq_eq_one (hC : SmallF3Cyclic G L) {t : G}
    (ht : orderOf t = 2) (htL : t ∈ Subgroup.centralizer (L : Set G))
    {x : G} (hx : x ∈ twoCore t) (hx2 : x ^ 2 = 1) : x = 1 ∨ x = t := by
  classical
  haveI : Fintype ↥(twoCore t) := Fintype.ofFinite _
  haveI : IsCyclic ↥(twoCore t) := isCyclic_twoCore hC ht htL
  have hcard : (Finset.univ.filter (fun a : ↥(twoCore t) => a ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (α := ↥(twoCore t)) (n := 2) (by norm_num)
  let x' : ↥(twoCore t) := ⟨x, hx⟩
  let t' : ↥(twoCore t) := ⟨t, mem_twoCore hC ht htL⟩
  have hx'2 : x' ^ 2 = 1 := Subtype.ext hx2
  have ht'2 : t' ^ 2 = 1 := by
    apply Subtype.ext
    show (t : G) ^ 2 = 1
    simpa [ht] using pow_orderOf_eq_one t
  have htne : t ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at ht
    omega
  have h1t' : (1 : ↥(twoCore t)) ≠ t' := by
    intro h
    exact htne (Subtype.ext_iff.mp h).symm
  have h2 : ({1, t'} : Finset ↥(twoCore t)) ⊆
      Finset.univ.filter (fun a : ↥(twoCore t) => a ^ 2 = 1) := by
    intro a ha
    simp only [Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl
    · simp
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ht'2⟩
  have hcard2 : ({1, t'} : Finset ↥(twoCore t)).card = 2 :=
    Finset.card_pair_eq_two_iff.mpr h1t'
  have hS : ({1, t'} : Finset ↥(twoCore t)) =
      Finset.univ.filter (fun a : ↥(twoCore t) => a ^ 2 = 1) :=
    Finset.eq_of_subset_of_card_le h2 (by rw [hcard2]; exact hcard)
  have hx'mem : x' ∈ ({1, t'} : Finset ↥(twoCore t)) := by
    rw [hS]
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'2⟩
  rcases (by simpa only [Finset.mem_insert, Finset.mem_singleton] using hx'mem) with h | h
  · exact Or.inl (Subtype.ext_iff.mp h)
  · exact Or.inr (Subtype.ext_iff.mp h)

end CFSG.OddStandard.SmallF3.HarrisU33
