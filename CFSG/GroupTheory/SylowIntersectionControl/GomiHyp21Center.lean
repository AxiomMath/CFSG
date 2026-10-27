module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsChev
import CFSG.RankThree.PartOne.K159.InnLayerComb

public section

namespace CFSG.GroupTheory

open Subgroup

variable {G : Type} [Group G]

private theorem commute_of_mem_center_ghc {L : Subgroup G} {x : ↥L}
    (hx : x ∈ Subgroup.center ↥L) {w : G} (hw : w ∈ L) :
    w * (x : G) = (x : G) * w := by
  have h := Subgroup.mem_center_iff.mp hx (⟨w, hw⟩ : ↥L)
  simpa using congrArg Subtype.val h

private theorem mem_pCore_of_mem_center_ghc {K : Type*} [Group K] {p : ℕ} {x : K}
    (hx : x ∈ Subgroup.center K) (hp : IsPGroup p (Subgroup.zpowers x)) :
    x ∈ CFSG.pCore p K :=
  (le_sSup (show Subgroup.zpowers x ∈ {N : Subgroup K | N.Normal ∧ IsPGroup p N} from
    ⟨Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hx), hp⟩) :
    Subgroup.zpowers x ≤ CFSG.pCore p K) (Subgroup.mem_zpowers x)

private theorem not_two_dvd_orderOf_center_ghc [Finite G] {L : Subgroup G}
    (hL : CFSG.pCore 2 ↥L = ⊥) {l : ↥L} (hl : l ∈ Subgroup.center ↥L) :
    ¬ 2 ∣ orderOf l := by
  intro h2
  have hcard : 2 ∣ Nat.card ↥(Subgroup.zpowers l) := by rwa [Nat.card_zpowers]
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' 2 hcard
  have hwcenter : (w : ↥L) ∈ Subgroup.center ↥L := (Subgroup.zpowers_le.mpr hl) w.property
  have hword : orderOf (w : ↥L) = 2 := by
    show orderOf ((Subgroup.zpowers l).subtype w) = 2
    rw [orderOf_injective (Subgroup.zpowers l).subtype
      (Subgroup.zpowers l).subtype_injective w]
    exact hw
  have hp : IsPGroup 2 (Subgroup.zpowers (w : ↥L)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hword]; norm_num)
  have hmem : (w : ↥L) ∈ CFSG.pCore 2 ↥L := mem_pCore_of_mem_center_ghc hwcenter hp
  rw [hL] at hmem
  have hw1 : (w : ↥L) = 1 := by simpa using hmem
  rw [hw1, orderOf_one] at hword
  norm_num at hword

private theorem conj_le_centralizer_conj_ghc {L : Subgroup G} (h : GomiConjugatesCommute L)
    {a b : G} (hne : L.map (MulAut.conj a).toMonoidHom ≠ L.map (MulAut.conj b).toMonoidHom) :
    L.map (MulAut.conj a).toMonoidHom ≤
      Subgroup.centralizer ((L.map (MulAut.conj b).toMonoidHom : Subgroup G) : Set G) := by
  intro x hx
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hy
  set c : G := a⁻¹ * b with hcdef
  have hb : b = a * c := by simp [hcdef]
  have hcne : L.map (MulAut.conj c).toMonoidHom ≠ L := by
    intro hc
    apply hne
    have h1 : (L.map (MulAut.conj c).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        L.map (MulAut.conj a).toMonoidHom := by rw [hc]
    have h2 : (L.map (MulAut.conj c).toMonoidHom).map (MulAut.conj a).toMonoidHom =
        L.map (MulAut.conj b).toMonoidHom := by
      rw [Subgroup.map_map]
      have hh : (MulAut.conj a).toMonoidHom.comp (MulAut.conj c).toMonoidHom =
          (MulAut.conj b).toMonoidHom := by
        ext t
        rw [hb]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.coe_comp,
          Function.comp_apply]
        group
      rw [hh]
    exact h1.symm.trans h2
  have hcom : MulAut.conj c m * l = l * MulAut.conj c m :=
    Subgroup.mem_centralizer_iff.mp
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h.commute c hcne) hl)
      (MulAut.conj c m) (Subgroup.mem_map.mpr ⟨m, hm, rfl⟩)
  rw [hb]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcom ⊢
  have e1 : (a * c * m * (a * c)⁻¹) * (a * l * a⁻¹) =
      a * ((c * m * c⁻¹) * l) * a⁻¹ := by group
  have e2 : (a * l * a⁻¹) * (a * c * m * (a * c)⁻¹) =
      a * (l * (c * m * c⁻¹)) * a⁻¹ := by group
  rw [e1, e2, hcom]

private theorem not_two_dvd_orderOf_center_map_conj_ghc [Finite G] {L : Subgroup G}
    (hL : CFSG.pCore 2 ↥L = ⊥) (g : G) {z : G}
    (hz : z ∈ (L.map (MulAut.conj g).toMonoidHom : Subgroup G) ⊓
      Subgroup.centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) :
    ¬ 2 ∣ orderOf z := by
  obtain ⟨hzK, hzC⟩ := hz
  obtain ⟨l, hlL, hlz⟩ := Subgroup.mem_map.mp hzK
  have hcenter : (⟨l, hlL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro u
    apply Subtype.ext
    have h := Subgroup.mem_centralizer_iff.mp hzC (MulAut.conj g (u : G))
      (Subgroup.mem_map.mpr ⟨(u : G), u.property, rfl⟩)
    rw [← hlz] at h
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    have h2 := congrArg (fun t => g⁻¹ * t * g) h
    have e1 : g⁻¹ * ((g * (u : G) * g⁻¹) * (g * l * g⁻¹)) * g = (u : G) * l := by group
    have e2 : g⁻¹ * ((g * l * g⁻¹) * (g * (u : G) * g⁻¹)) * g = l * (u : G) := by group
    rw [e1, e2] at h2
    exact h2
  have hzorder : orderOf z = orderOf (⟨l, hlL⟩ : ↥L) := by
    rw [← hlz, orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective l]
    exact orderOf_injective (Subgroup.subtype L) (Subgroup.subtype_injective L)
      (⟨l, hlL⟩ : ↥L)
  intro h2
  exact not_two_dvd_orderOf_center_ghc hL hcenter (hzorder ▸ h2)

private theorem odd_card_of_no_two_dvd_order_ghc [Finite G] (H : Subgroup G)
    (h : ∀ z ∈ H ⊓ Subgroup.centralizer (H : Set G), ¬ 2 ∣ orderOf z) :
    Odd (Nat.card ↥(H ⊓ Subgroup.centralizer (H : Set G))) := by
  rw [← Nat.not_even_iff_odd]
  intro heven
  have h2 : 2 ∣ Nat.card ↥(H ⊓ Subgroup.centralizer (H : Set G)) := even_iff_two_dvd.mp heven
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hzord' : orderOf (z : G) = 2 := by
    show orderOf ((Subgroup.subtype _) z) = 2
    rw [orderOf_injective (Subgroup.subtype _) Subtype.coe_injective z]
    exact hzord
  exact h (z : G) z.property (by rw [hzord'])

theorem GomiConjugatesCommute.subgroupOf_center_eq {L : Subgroup G} (h : GomiConjugatesCommute L) :
    (normalClosure (L : Set G) ⊓ centralizer (normalClosure (L : Set G) : Set G)).subgroupOf L =
      center ↥L := by
  apply le_antisymm
  · intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    exact Subgroup.mem_center_iff.mpr fun g => Subtype.ext
      (Subgroup.mem_centralizer_iff.mp hx.2 (g : G)
        (Subgroup.le_normalClosure (H := L) g.property))
  · intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine ⟨Subgroup.le_normalClosure (H := L) x.property, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro y hy
    have hle : normalClosure (L : Set G) ≤ Subgroup.centralizer ({x.1} : Set G) := by
      change closure (Group.conjugatesOfSet (L : Set G)) ≤ Subgroup.centralizer ({x.1} : Set G)
      rw [Subgroup.closure_le]
      intro y hy
      refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
      obtain ⟨l, hl, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hy
      rw [isConj_iff] at hconj
      obtain ⟨c, rfl⟩ := hconj
      by_cases hceq : L.map (MulAut.conj c).toMonoidHom = L
      · have hwl : MulAut.conj c l ∈ L := by
          rw [← hceq]
          exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
        simpa only [MulAut.conj_apply] using commute_of_mem_center_ghc hx hwl
      · have hxcent : (x : G) ∈ Subgroup.centralizer
            ((L.map (MulAut.conj c).toMonoidHom : Subgroup G) : Set G) :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mp (h.commute c hceq) x.property
        simpa only [MulAut.conj_apply] using Subgroup.mem_centralizer_iff.mp hxcent
          (MulAut.conj c l) (Subgroup.mem_map.mpr ⟨l, hl, rfl⟩)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)

theorem GomiConjugatesCommute.coprime_card_center_normalClosure [Finite G] {L : Subgroup G}
    (h : GomiConjugatesCommute L) (hL : CFSG.pCore 2 ↥L = ⊥) :
    Nat.Coprime
      (Nat.card ↥(normalClosure (L : Set G) ⊓ centralizer (normalClosure (L : Set G) : Set G)))
      2 := by
  classical
  let hfin : Fintype G := Fintype.ofFinite G
  set s : Finset (Subgroup G) :=
    Finset.univ.image (fun g : G => L.map (MulAut.conj g).toMonoidHom) with hs
  have hset : (⋃ g : G, ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) =
      Group.conjugatesOfSet (L : Set G) := by
    ext x
    simp only [Set.mem_iUnion, SetLike.mem_coe, Group.mem_conjugatesOfSet_iff, isConj_iff,
      Subgroup.mem_map]
    constructor
    · rintro ⟨g, l, hl, rfl⟩
      exact ⟨l, hl, g, rfl⟩
    · rintro ⟨l, hl, g, rfl⟩
      exact ⟨g, l, hl, rfl⟩
  have hiSup : (⨆ g : G, L.map (MulAut.conj g).toMonoidHom) = normalClosure (L : Set G) := by
    rw [Subgroup.iSup_eq_closure, hset]
    rfl
  have hsup : s.sup id = normalClosure (L : Set G) := by
    have key : Finset.univ.sup (fun g : G => L.map (MulAut.conj g).toMonoidHom) =
        (⨆ g : G, L.map (MulAut.conj g).toMonoidHom) := by
      refine le_antisymm (Finset.sup_le fun g _ =>
        le_iSup (fun g : G => L.map (MulAut.conj g).toMonoidHom) g) (iSup_le fun g => ?_)
      exact Finset.le_sup (f := fun g : G => L.map (MulAut.conj g).toMonoidHom) (Finset.mem_univ g)
    rw [hs, Finset.sup_image]
    simpa using key.trans hiSup
  have hcomm : ∀ Y ∈ s, ∀ Y' ∈ s, Y ≠ Y' → ∀ a ∈ Y, ∀ b ∈ Y', a * b = b * a := by
    intro Y hY Y' hY' hne a ha b hb
    rw [hs] at hY hY'
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hY
    obtain ⟨g', -, rfl⟩ := Finset.mem_image.mp hY'
    exact (Subgroup.mem_centralizer_iff.mp (conj_le_centralizer_conj_ghc h hne ha) b hb).symm
  have hz : ∀ Y ∈ s, ∀ z ∈ Y ⊓ Subgroup.centralizer (Y : Set G), ¬ 2 ∣ orderOf z := by
    intro Y hY z hz
    rw [hs] at hY
    obtain ⟨g, -, rfl⟩ := Finset.mem_image.mp hY
    exact not_two_dvd_orderOf_center_map_conj_ghc hL g hz
  have hno := CFSG.RankThree.PartOne.K159.noP_finset_sup (p := 2) Nat.prime_two s hcomm hz
  rw [Nat.coprime_two_right]
  rw [hsup] at hno
  exact odd_card_of_no_two_dvd_order_ghc _ hno

end CFSG.GroupTheory
