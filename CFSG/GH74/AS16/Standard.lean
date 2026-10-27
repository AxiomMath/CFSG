module

public import CFSG.GroupTheory.LocalCores.Components
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.NormalizerLeNormalizerCentralizer
public import CFSG.GH74.GLS.Basic

public section

namespace CFSG.GH74.AS16

open Subgroup CFSG
open scoped commutatorElement

variable {G : Type} [Group G]

theorem mem_conjugate_iff' (H : Subgroup G) (g x : G) :
    x ∈ conjugate H g ↔ g * x * g⁻¹ ∈ H := by
  simpa [conjugate, MulAut.conj_apply] using
    (Subgroup.mem_map_equiv (f := MulAut.conj g⁻¹) (K := H) (x := x))

theorem conjugate_centralizer_singleton (t g : G) :
    conjugate (centralizer ({t} : Set G)) g = centralizer ({g⁻¹ * t * g} : Set G) := by
  ext x
  rw [mem_conjugate_iff', mem_centralizer_singleton_iff, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' : t * (g * x * g⁻¹) = (g * x * g⁻¹) * t := h.symm
    calc x * (g⁻¹ * t * g) = g⁻¹ * (g * x * g⁻¹) * t * g := by group
      _ = g⁻¹ * (t * (g * x * g⁻¹)) * g := by rw [h']; group
      _ = (g⁻¹ * t * g) * x := by group
  · intro h
    have h' : x * (g⁻¹ * t * g) = (g⁻¹ * t * g) * x := h
    calc (g * x * g⁻¹) * t = g * (x * (g⁻¹ * t * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t * g) * x) * g⁻¹ := by rw [h']
      _ = t * (g * x * g⁻¹) := by group

theorem conjugate_centralizer (L : Subgroup G) (g : G) :
    conjugate (centralizer (L : Set G)) g = centralizer (conjugate L g : Set G) := by
  ext x
  rw [mem_conjugate_iff', mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h y hy
    rw [SetLike.mem_coe, mem_conjugate_iff'] at hy
    have h1 := h _ hy
    calc y * x = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by rw [h1]
      _ = x * y := by group
  · intro h y hy
    have hy' : g⁻¹ * y * g ∈ conjugate L g := by
      rw [mem_conjugate_iff']
      simpa [mul_assoc] using hy
    have h1 := h _ hy'
    calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
      _ = (g * x * g⁻¹) * y := by group

theorem isCompIn_conj {X L : Subgroup G} (h : GLS.IsCompIn X L) (g : G) :
    GLS.IsCompIn (conjugate X g) (conjugate L g) := by
  obtain ⟨hLX, hcomp⟩ := h
  refine ⟨Subgroup.map_mono hLX, ?_⟩
  let f : G ≃* G := MulAut.conj g⁻¹
  let e : ↥X ≃* ↥(conjugate X g) := MulEquiv.subgroupMap f X
  have hmap : (L.subgroupOf X).map e.toMonoidHom = (conjugate L g).subgroupOf (conjugate X g) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_subgroupOf]
      exact ⟨x, hx, rfl⟩
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      obtain ⟨l, hl, hly⟩ := hy
      refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
      change e.symm y ∈ L.subgroupOf X
      rw [Subgroup.mem_subgroupOf]
      have : ((e.symm y : X) : G) = l := by
        have h1 : ((e.symm y : X) : G) = f.symm (y : G) := rfl
        rw [h1, ← hly]
        exact f.symm_apply_apply l
      rw [this]
      exact hl
  have := LocalCores.isComponent_map_mulEquiv e hcomp
  rwa [hmap] at this

theorem isCompIn_commute [Finite G] {X A B : Subgroup G} (hA : GLS.IsCompIn X A)
    (hB : GLS.IsCompIn X B) : A = B ∨ ⁅A, B⁆ = ⊥ := by
  rcases LocalCores.distinct_components_commute hA.2 hB.2 with h | h
  · left
    have := (Subgroup.subgroupOf_inj).mp h
    rwa [inf_of_le_left hA.1, inf_of_le_left hB.1] at this
  · right
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro a ha b hb
    have hab : (⟨a, hA.1 ha⟩ : X) ∈ A.subgroupOf X := ha
    have hbb : (⟨b, hB.1 hb⟩ : X) ∈ B.subgroupOf X := hb
    have hc : ⁅(⟨a, hA.1 ha⟩ : X), ⟨b, hB.1 hb⟩⁆ ∈ ⁅A.subgroupOf X, B.subgroupOf X⁆ :=
      Subgroup.commutator_mem_commutator hab hbb
    rw [h, Subgroup.mem_bot] at hc
    have h3 : (a * b * a⁻¹ * b⁻¹ : G) = 1 := by
      have := congrArg Subtype.val hc
      simpa [commutatorElement_def] using this
    rw [Subgroup.mem_bot, commutatorElement_def]
    exact h3

theorem exists_involution_of_isQuasisimple [Finite G] {L : Subgroup G} (hq : IsQuasisimple ↥L) :
    ∃ i ∈ L, orderOf i = 2 := by
  obtain ⟨-, hsimple, ⟨a, b, hab⟩⟩ := hq
  have hnotodd : ¬ Odd (Nat.card (↥L ⧸ center ↥L)) := by
    intro hodd
    have hsolv := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsolv) a b)
  have heven : 2 ∣ Nat.card (↥L ⧸ center ↥L) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hnotodd)
  have hdvd : 2 ∣ Nat.card ↥L := heven.trans (Subgroup.card_quotient_dvd_card _)
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥L) 2 hdvd
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem exists_involution_of_even [Finite G] {A : Subgroup G} (h : Even (Nat.card A)) :
    ∃ t ∈ A, orderOf t = 2 := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := A) 2 (even_iff_two_dvd.mp h)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem conjugate_eq_self_iff (H : Subgroup G) (g : G) :
    conjugate H g = H ↔ g ∈ normalizer (H : Set G) := by
  change H.map (MulAut.conj g⁻¹) = H ↔ g ∈ normalizer (H : Set G)
  rw [← Subgroup.mem_normalizer_iff_map_conj_eq]
  exact (normalizer (H : Set G)).inv_mem_iff

theorem normalizer_le_normalizer_centralizer' (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer ((centralizer (L : Set G) : Subgroup G) : Set G) :=
  GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup L

theorem isStandardSubgroup_of_terminal [Finite G] {L : Subgroup G} (hq : IsQuasisimple ↥L)
    {z : G} (hz : orderOf z = 2) (hzL : z ∈ centralizer (L : Set G))
    (hterm : ∀ t ∈ centralizer (L : Set G), orderOf t = 2 →
      GLS.IsCompIn (centralizer ({t} : Set G)) L)
    (hnc : ∀ g : G, ¬ GLS.IsCompIn (centralizer (L : Set G)) (conjugate L g)) :
    IsStandardSubgroup L := by
  have hterm' : ∀ g : G, ∀ t ∈ centralizer ((conjugate L g : Subgroup G) : Set G), orderOf t = 2 →
      GLS.IsCompIn (centralizer ({t} : Set G)) (conjugate L g) := by
    intro g t ht ht2
    have ht' : g * t * g⁻¹ ∈ centralizer (L : Set G) := by
      rw [← mem_conjugate_iff' (centralizer (L : Set G)) g t, conjugate_centralizer]
      exact ht
    have ho : orderOf (g * t * g⁻¹) = 2 := by
      rw [← ht2]
      exact (MulAut.conj g).orderOf_eq t
    have h1 := isCompIn_conj (hterm _ ht' ho) g
    rwa [conjugate_centralizer_singleton, show g⁻¹ * (g * t * g⁻¹) * g = t by group] at h1
  have hcomm : ∀ g : G, ⁅L, conjugate L g⁆ ≠ ⊥ := by
    intro g hbot
    have hLg : L ≤ centralizer ((conjugate L g : Subgroup G) : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
    have hgL : conjugate L g ≤ centralizer (L : Set G) := by
      apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      rw [Subgroup.commutator_comm]
      exact hbot
    obtain ⟨i, hiL, hi2⟩ := exists_involution_of_isQuasisimple hq
    have hcomp := hterm' g i (hLg hiL) hi2
    have hCle : centralizer (L : Set G) ≤ centralizer ({i} : Set G) :=
      Subgroup.centralizer_le (by simpa using hiL)
    apply hnc g
    refine ⟨hgL, ?_, ?_⟩
    ·
      let e : ↥((conjugate L g).subgroupOf (centralizer ({i} : Set G))) ≃*
          ↥((conjugate L g).subgroupOf (centralizer (L : Set G))) :=
        (Subgroup.subgroupOfEquivOfLe hcomp.1).trans (Subgroup.subgroupOfEquivOfLe hgL).symm
      exact LocalCores.isQuasisimple_of_mulEquiv e hcomp.2.1
    ·
      have hsub := hcomp.2.2.comap (Subgroup.inclusion hCle)
      have heq : ((conjugate L g).subgroupOf (centralizer ({i} : Set G))).comap
          (Subgroup.inclusion hCle) = (conjugate L g).subgroupOf (centralizer (L : Set G)) := by
        ext y
        simp [Subgroup.mem_subgroupOf]
      rwa [heq] at hsub
  have hover : ∀ g : G,
      Even (Nat.card ↥(centralizer (L : Set G) ⊓ conjugate (centralizer (L : Set G)) g)) →
      g ∈ normalizer (L : Set G) := by
    intro g hev
    obtain ⟨t, ht, ht2⟩ := exists_involution_of_even hev
    have htC : t ∈ centralizer (L : Set G) := ht.1
    have htCg : t ∈ centralizer ((conjugate L g : Subgroup G) : Set G) := by
      rw [← conjugate_centralizer]
      exact ht.2
    have h1 := hterm t htC ht2
    have h2 := hterm' g t htCg ht2
    rcases isCompIn_commute h1 h2 with h | h
    · exact (conjugate_eq_self_iff L g).mp h.symm
    · exact absurd h (hcomm g)
  have hevC : Even (Nat.card (centralizer (L : Set G))) := by
    have := Subgroup.orderOf_dvd_natCard (centralizer (L : Set G)) hzL
    rw [hz] at this
    exact even_iff_two_dvd.mpr this
  refine ⟨hq, hevC, ?_, ?_, hcomm⟩
  · intro g hg
    by_contra hnot
    exact hg (normalizer_le_normalizer_centralizer' L (hover g (Nat.not_odd_iff_even.mp hnot)))
  · apply le_antisymm
    · intro g hg
      apply hover
      have hCg : conjugate (centralizer (L : Set G)) g = centralizer (L : Set G) :=
        (conjugate_eq_self_iff _ g).mpr hg
      rw [hCg, inf_idem]
      exact hevC
    · exact normalizer_le_normalizer_centralizer' L

end CFSG.GH74.AS16
