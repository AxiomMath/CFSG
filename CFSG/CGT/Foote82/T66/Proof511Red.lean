module

public import CFSG.GroupTheory.QuasisimpleAutQuotient
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitQuotientHyp
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.GH74.E2.TermBasic
public import CFSG.CGT.Foote82.OddCover
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtKFOU3Perf
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.CGT.Foote82.Proof511

open Subgroup

theorem center_eq_bot_of_simple {S : Type*} [Group S] [IsSimpleGroup S]
    (hnab : ∃ a b : S, a * b ≠ b * a) : center S = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center S) with h | h
  · exact h
  · obtain ⟨a, b, hab⟩ := hnab
    exact absurd (mem_center_iff.mp (h ▸ mem_top b) a) hab

theorem injective_domRestrict_of_odd {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hodd : Odd (Nat.card f.ker)) {P : Subgroup A} (hP : IsPGroup 2 P) :
    Function.Injective (f.domRestrict P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [injective_iff_map_eq_one]
  intro a ha
  have hak : (a : A) ∈ f.ker := ha
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hP a
  have hd : orderOf (⟨(a : A), hak⟩ : ↥f.ker) ∣ Nat.card f.ker := orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hk] at hd
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · have h2 : 2 ∣ Nat.card f.ker := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) hd
    exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hodd)

noncomputable def mulEquivMapOfOdd {A B : Type*} [Group A] [Group B] [Finite A] (f : A →* B)
    (hodd : Odd (Nat.card f.ker)) {P : Subgroup A} (hP : IsPGroup 2 P) : ↥P ≃* ↥(P.map f) :=
  (MonoidHom.ofInjective (injective_domRestrict_of_odd f hodd hP)).trans
    (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range P f))

variable {G : Type} [Group G] [Finite G]

structure Hyp (X J L : Subgroup G) (z : G) : Prop where
  le : J ≤ X
  normal : (J.subgroupOf X).Normal
  relIndex_le : J.relIndex X ≤ 2
  cent_le : X ⊓ centralizer (J : Set G) ≤ (center ↥J).map J.subtype
  quasi : CFSG.IsQuasisimple ↥J
  odd : Odd (Nat.card ↥(center ↥J))
  mem : z ∈ X
  order : orderOf z = 2
  comp : CFSG.Open.IsComponentOf L (X ⊓ centralizer ({z} : Set G))
  simple : IsSimpleGroup ↥L
  nonab : ∃ a b : ↥L, a * b ≠ b * a

structure Red (J L : Subgroup G) (H : Type) [Group H] where
  ψ : ↥J →* H
  x : H
  Lb : Subgroup H
  eL : ↥Lb ≃* ↥L
  quasi : CFSG.IsQuasisimple ↥J
  odd : Odd (Nat.card ↥(center ↥J))
  simpleL : IsSimpleGroup ↥L
  nonabL : ∃ a b : ↥L, a * b ≠ b * a
  range_eq : ψ.range = generalizedFitting H
  ker_eq : ψ.ker = center ↥J
  cent_eq : centralizer (generalizedFitting H : Set H) = ⊥
  simple : IsSimpleGroup ↥(generalizedFitting H)
  nonab : ∃ a b : ↥(generalizedFitting H), a * b ≠ b * a
  order : orderOf x = 2
  le_F : Lb ≤ generalizedFitting H
  le_C : Lb ≤ centralizer ({x} : Set H)
  comp : CFSG.Open.IsComponentOf Lb (centralizer ({x} : Set H))
  le_J : L ≤ J
  mem_Lb : ∀ l : ↥J, (l : G) ∈ L → ψ l ∈ Lb
  orderOf_eq : ∀ l : ↥J, (l : G) ∈ L → orderOf (ψ l) = orderOf l

namespace Hyp

variable {X J L : Subgroup G} {z : G}

theorem le_normalizer (h : Hyp X J L z) : X ≤ normalizer (J : Set G) :=
  (normal_subgroupOf_iff_le_normalizer h.le).mp h.normal

theorem le_X (h : Hyp X J L z) : L ≤ X :=
  h.comp.1.trans inf_le_left

theorem le_J (h : Hyp X J L z) : L ≤ J := by
  have hP : Group.IsPerfect ↥L := Group.isPerfect_def.2 h.comp.2.2.1
  have hpos : J.relIndex X ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (by have := h.relIndex_le; omega : J.relIndex X = 1 ∨ J.relIndex X = 2) with h1 | h2
  · exact h.le_X.trans (relIndex_eq_one.mp h1)
  · exact CFSG.Quasithin.SBd19F.le_of_isPerfect_of_relindex_two h.le_X h2 hP

theorem exists_red (h : Hyp X J L z) :
    ∃ (H : Type) (_ : Group H) (_ : Finite H), Nonempty (Red J L H) := by
  classical
  have hN := h.le_normalizer
  have hLJ := h.le_J
  have hLX := h.le_X
  haveI := h.simple
  haveI hκn : (GroupTheory.quasisimpleActionKernel X J hN).Normal :=
    GroupTheory.quasisimpleActionKernel_normal X J hN
  set κ := GroupTheory.quasisimpleActionKernel X J hN with hκ
  have hκmem : ∀ y : ↥X, y ∈ κ ↔ (y : G) ∈ centralizer (J : Set G) := fun y => by
    rw [hκ, GroupTheory.quasisimpleActionKernel_eq_centralizer, mem_subgroupOf]
  have hκodd : Odd (Nat.card κ) := by
    have hle : κ.map X.subtype ≤ (center ↥J).map J.subtype := by
      intro g hg
      obtain ⟨y, hy, rfl⟩ := mem_map.mp hg
      exact h.cent_le ⟨y.2, (hκmem y).mp hy⟩
    have hd := card_dvd_of_le hle
    rw [card_map_of_injective X.subtype_injective,
      card_map_of_injective J.subtype_injective] at hd
    exact Odd.of_dvd_nat h.odd hd
  let π : ↥X →* ↥X ⧸ κ := QuotientGroup.mk' κ
  let Jb : Subgroup (↥X ⧸ κ) := (J.subgroupOf X).map π
  have hFJ : generalizedFitting (↥X ⧸ κ) = Jb := by
    rw [← CFSG.Adapters.genFittingFStar_eq_foundations]
    exact GroupTheory.quasisimple_genFittingFStar_image_eq X J h.le hN h.quasi
  let ψ : ↥J →* ↥X ⧸ κ := π.comp (inclusion h.le)
  have hψrange : ψ.range = Jb := by
    rw [MonoidHom.range_comp, inclusion_range]
  have hψker : ψ.ker = center ↥J := by
    ext j
    rw [MonoidHom.mem_ker, mem_center_iff]
    change (QuotientGroup.mk' κ (inclusion h.le j) = 1) ↔ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hκmem, mem_centralizer_iff]
    constructor
    · intro hj g
      exact Subtype.ext (hj g g.2)
    · intro hj g hg
      exact congrArg Subtype.val (hj ⟨g, hg⟩)
  have hz' : orderOf (⟨z, h.mem⟩ : ↥X) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact h.order
  have hz'κ : (⟨z, h.mem⟩ : ↥X) ∉ κ := by
    intro hm
    have h2 : orderOf (⟨⟨z, h.mem⟩, hm⟩ : ↥κ) = 2 := by
      rw [Subgroup.orderOf_mk]
      exact hz'
    have hd := orderOf_dvd_natCard (⟨⟨z, h.mem⟩, hm⟩ : ↥κ)
    rw [h2] at hd
    exact (Nat.not_even_iff_odd.mpr hκodd) (even_iff_two_dvd.mpr hd)
  have hx : orderOf (π ⟨z, h.mem⟩) = 2 := by
    apply orderOf_eq_prime
    · rw [← map_pow, ← hz', pow_orderOf_eq_one, map_one]
    · intro h1
      exact hz'κ ((QuotientGroup.eq_one_iff _).mp h1)
  have hCx : (centralizer ({(⟨z, h.mem⟩ : ↥X)} : Set ↥X)).map π =
      centralizer ({π ⟨z, h.mem⟩} : Set (↥X ⧸ κ)) :=
    CFSG.ComponentClassification.FooteLit.map_centralizer_mk'_of_odd hκodd hz'
  have hCsub : (X ⊓ centralizer ({z} : Set G)).subgroupOf X =
      centralizer ({(⟨z, h.mem⟩ : ↥X)} : Set ↥X) := by
    ext y
    rw [mem_subgroupOf, mem_inf, mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨-, hy⟩
      exact Subtype.ext hy
    · intro hy
      exact ⟨y.2, congrArg Subtype.val hy⟩
  let L' : Subgroup ↥X := L.subgroupOf X
  let Lb : Subgroup (↥X ⧸ κ) := L'.map π
  have hcL : center ↥L = ⊥ := center_eq_bot_of_simple h.nonab
  have hinj : Function.Injective (π.domRestrict L') := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have ha' : π (a : ↥X) = 1 := ha
    have haκ : (a : ↥X) ∈ κ := (QuotientGroup.eq_one_iff (a : ↥X)).mp ha'
    have haJ : ((a : ↥X) : G) ∈ centralizer (J : Set G) := (hκmem _).mp haκ
    have haL : ((a : ↥X) : G) ∈ L := mem_subgroupOf.mp a.2
    have hc : (⟨_, haL⟩ : ↥L) ∈ center ↥L := by
      rw [mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.mp haJ g (hLJ g.2))
    rw [hcL, mem_bot] at hc
    have hc' : ((a : ↥X) : G) = 1 := by simpa using congrArg Subtype.val hc
    exact Subtype.ext (Subtype.ext hc')
  have hLbr : (π.domRestrict L').range = Lb := MonoidHom.domRestrict_range L' π
  let eL : ↥Lb ≃* ↥L :=
    ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hLbr)).symm.trans
      (subgroupOfEquivOfLe hLX)
  have hLbJ : Lb ≤ Jb :=
    map_mono fun y hy => mem_subgroupOf.mpr (hLJ (mem_subgroupOf.mp hy))
  have hL'C : L' ≤ centralizer ({(⟨z, h.mem⟩ : ↥X)} : Set ↥X) := by
    rw [← hCsub]
    intro y hy
    exact mem_subgroupOf.mpr (h.comp.1 (mem_subgroupOf.mp hy))
  have hLbC : Lb ≤ centralizer ({π ⟨z, h.mem⟩} : Set (↥X ⧸ κ)) := hCx ▸ map_mono hL'C
  have hsub : CFSG.Open.IsSubnormal Lb (centralizer ({π ⟨z, h.mem⟩} : Set (↥X ⧸ κ))) := by
    rw [← hCx, ← hCsub]
    exact CFSG.Open.IsSubnormal.map π (CFSG.Open.IsSubnormal.comap X.subtype h.comp.2.1)
  have hq : CFSG.Open.IsQuasisimple ↥Lb := CFSG.Open.IsQuasisimple.of_mulEquiv eL h.comp.2.2
  have hord : ∀ l : ↥J, (l : G) ∈ L → orderOf (ψ l) = orderOf l := by
    intro l hl
    have h1 := orderOf_injective (π.domRestrict L') hinj ⟨inclusion h.le l, mem_subgroupOf.mpr hl⟩
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf (inclusion h.le l) = orderOf l :=
      orderOf_injective (inclusion h.le) (inclusion_injective h.le) l
    rw [← h2, ← h1]
    rfl
  refine ⟨↥X ⧸ κ, inferInstance, inferInstance, ⟨
    { ψ := ψ
      x := π ⟨z, h.mem⟩
      Lb := Lb
      eL := eL
      quasi := h.quasi
      odd := h.odd
      simpleL := h.simple
      nonabL := h.nonab
      range_eq := hψrange.trans hFJ.symm
      ker_eq := hψker
      cent_eq := ?_
      simple := ?_
      nonab := ?_
      order := hx
      le_F := hFJ ▸ hLbJ
      le_C := hLbC
      comp := ⟨hLbC, hsub, hq⟩
      le_J := hLJ
      mem_Lb := fun l hl => mem_map_of_mem π (mem_subgroupOf.mpr hl)
      orderOf_eq := hord }⟩⟩
  · rw [hFJ]
    exact GroupTheory.quasisimple_centralizer_image_eq_bot X J h.le hN h.quasi
  · rw [hFJ]
    exact GroupTheory.quasisimple_isSimpleGroup_image X J h.le hN h.quasi
  · rw [hFJ]
    exact GroupTheory.quasisimple_nonabelian_image X J h.le hN h.quasi

end Hyp

namespace Red

variable {J L : Subgroup G} {H : Type} [Group H] (r : Red J L H)

include r

@[expose] noncomputable def ψS : ↥J →* ↥(generalizedFitting H) :=
  r.ψ.codRestrict (generalizedFitting H) fun j => by
    rw [← r.range_eq]
    exact ⟨j, rfl⟩

@[simp] theorem coe_ψS (j : ↥J) : (r.ψS j : H) = r.ψ j :=
  rfl

theorem ψS_surjective : Function.Surjective r.ψS := by
  intro y
  have hy : (y : H) ∈ r.ψ.range := by
    rw [r.range_eq]
    exact y.2
  obtain ⟨j, hj⟩ := hy
  exact ⟨j, Subtype.ext hj⟩

theorem ker_ψS : r.ψS.ker = center ↥J := by
  rw [ψS, MonoidHom.ker_codRestrict, r.ker_eq]

noncomputable def quotEquiv : (↥J ⧸ center ↥J) ≃* ↥(generalizedFitting H) :=
  (QuotientGroup.quotientMulEquivOfEq r.ker_ψS.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective r.ψS r.ψS_surjective)

theorem pcomp [Finite H] : IsPComponent 2 (r.Lb.subgroupOf (centralizer ({r.x} : Set H))) := by
  haveI := r.simpleL
  have hq : CFSG.IsQuasisimple ↥(r.Lb.subgroupOf (centralizer ({r.x} : Set H))) :=
    (CFSG.IsQuasisimple.congr ((subgroupOfEquivOfLe r.le_C).trans r.eL)).mpr
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup r.nonabL).1
  exact CFSG.GH74.E2.isPComponent_two_of_component
    ⟨hq, CFSG.Open.IsSubnormal.subgroupOf r.comp.2.1⟩

theorem sylow_equiv (P' : Sylow 2 ↥(generalizedFitting H)) (P : Sylow 2 ↥J) :
    Nonempty (↥P' ≃* ↥P) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.mapSurjective_surjective r.ψS_surjective 2 P'
  have hodd : Odd (Nat.card r.ψS.ker) := r.ker_ψS ▸ r.odd
  have heq : (P' : Subgroup ↥(generalizedFitting H)) = (P₀ : Subgroup ↥J).map r.ψS := by
    rw [← hP₀, Sylow.coe_mapSurjective]
  exact ⟨((MulEquiv.subgroupCongr heq).trans (mulEquivMapOfOdd r.ψS hodd P₀.2).symm).trans
    (Sylow.equiv P₀ P)⟩

theorem lift_alt {n : ℕ} (hn : 8 ≤ n) (e : ↥(generalizedFitting H) ≃* alternatingGroup (Fin n)) :
    Nonempty (↥J ≃* alternatingGroup (Fin n)) := by
  let η : ↥J →* alternatingGroup (Fin n) :=
    (e : ↥(generalizedFitting H) →* alternatingGroup (Fin n)).comp r.ψS
  have hη : Function.Surjective η := e.surjective.comp r.ψS_surjective
  have hker : η.ker = center ↥J := by
    rw [MonoidHom.ker_mulEquiv_comp, r.ker_ψS]
  have hbot : η.ker = ⊥ :=
    CFSG.CGT.Foote82.ker_eq_bot_of_odd_alt (Group.isPerfect_def.1 r.quasi.1) hn η hη
      hker.le (hker ▸ r.odd)
  exact ⟨MulEquiv.ofBijective η ⟨(MonoidHom.ker_eq_bot_iff _).mp hbot, hη⟩⟩

end Red

end CFSG.CGT.Foote82.Proof511
