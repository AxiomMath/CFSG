module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Sub
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Bridge
public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.Harada.Lemma24Defs

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Harada

open Subgroup CFSG.EvenSporadicStandard.HNRecog.HaradaLA

variable {G : Type} [Group G] {t z b z₁ : G} {S Eg T T' W0 : Subgroup G} {ι : Elem2 6 →* G}
  {a : G}

private theorem image_tInvolutions_Y (hD : HData G t z b z₁ S Eg T T' W0 ι)
    (hconj : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1)
    (hat : a ∈ centralizer ({t} : Set G)) :
    Subtype.val '' tInvolutions (tY hat) (τY a t) =
      {y : G | y ∈ centralizer ({t} : Set G) ∧ y ∈ centralizer ({a} : Set G) ∧
        y ^ 2 = 1 ∧ y ≠ 1 ∧ tTG t z z₁ y} := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simp only [tInvolutions, Set.mem_setOf_eq] at hx
    obtain ⟨hxC, hx2, hx1, hxτ⟩ := hx
    have hyT : (x : G) ∈ centralizer ({t} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hxC)
    have hy2 : (x : G) ^ 2 = 1 := by simpa using congrArg Subtype.val hx2
    have hy1 : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    exact ⟨hyT, x.2, hy2, hy1, (isConj_iff_tTG hD hconj hyT hy2 hy1).mp hxτ⟩
  · rintro ⟨hyT, hyA, hy2, hy1, hyTG⟩
    refine ⟨⟨y, hyA⟩, ?_, rfl⟩
    simp only [tInvolutions, Set.mem_setOf_eq]
    have hxT : (⟨y, hyA⟩ : Y24 a) ∈ centralizer ({tY hat} : Set (Y24 a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hyT
    have hx2 : (⟨y, hyA⟩ : Y24 a) ^ 2 = 1 := Subtype.ext (by simpa using hy2)
    have hx1 : (⟨y, hyA⟩ : Y24 a) ≠ 1 := fun h =>
      hy1 (by simpa using congrArg Subtype.val h)
    exact ⟨hxT, hx2, hx1, (isConj_iff_tTG hD hconj hyT hy2 hy1).mpr hyTG⟩

theorem τY_fusion (hD3 : HData3 G t z z₁) (hat : a ∈ centralizer ({t} : Set G))
    (ha3 : orderOf a = 3) :
    ∀ s : Y24 a, τY a t s → s ^ 2 = 1 → s ≠ 1 → ∃ y : Y24 a, y * tY hat * y⁻¹ = s := by
  intro s hs _ _
  obtain ⟨y, hya, hyt⟩ :=
    exists_centralizer_conj_of_isConj hD3 hat ha3 hs
      (Subgroup.mem_centralizer_singleton_iff.mp s.2)
  refine ⟨⟨y, Subgroup.mem_centralizer_singleton_iff.mpr hya⟩, ?_⟩
  apply Subtype.ext
  simpa [tY] using hyt

theorem card_centralizer_tY (hD3 : HData3 G t z z₁) (hat : a ∈ centralizer ({t} : Set G))
    (ha3 : orderOf a = 3) : Nat.card ↥(centralizer ({tY hat} : Set (Y24 a))) = 1440 := by
  have hmap := map_subtype_centralizer_singleton (centralizer ({a} : Set G)) (tY hat)
  rw [← Subgroup.card_map_of_injective (f := (centralizer ({a} : Set G)).subtype)
    (centralizer ({a} : Set G)).subtype_injective, hmap]
  exact hD3.card_C3 a hat ha3

theorem odd_normal_Y (hD3 : HData3 G t z z₁) (hat : a ∈ centralizer ({t} : Set G))
    (ha3 : orderOf a = 3) :
    ∀ N : Subgroup (Y24 a), N ≤ centralizer ({tY hat} : Set (Y24 a)) →
      (∀ c ∈ centralizer ({tY hat} : Set (Y24 a)), ∀ n ∈ N, c * n * c⁻¹ ∈ N) →
      Odd (Nat.card N) → N ≤ zpowers (aY a) := by
  intro N hN hNorm hodd
  let N' : Subgroup G := N.map (centralizer ({a} : Set G)).subtype
  have hN'le : N' ≤ centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G) := by
    have h1 : N' ≤
        (centralizer ({tY hat} : Set (Y24 a))).map (centralizer ({a} : Set G)).subtype :=
      Subgroup.map_mono hN
    rwa [map_subtype_centralizer_singleton (centralizer ({a} : Set G)) (tY hat)] at h1
  have hN'norm : ∀ c ∈ centralizer ({t} : Set G) ⊓ centralizer ({a} : Set G),
      ∀ n ∈ N', c * n * c⁻¹ ∈ N' := by
    intro c hc n hn
    obtain ⟨hct, hca⟩ := Subgroup.mem_inf.mp hc
    obtain ⟨m, hmN, hm_eq⟩ := Subgroup.mem_map.mp hn
    have hc' : (⟨c, hca⟩ : Y24 a) ∈ centralizer ({tY hat} : Set (Y24 a)) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp hct
    refine Subgroup.mem_map.mpr
      ⟨⟨c, hca⟩ * m * ⟨c, hca⟩⁻¹, hNorm ⟨c, hca⟩ hc' m hmN, ?_⟩
    show c * (centralizer ({a} : Set G)).subtype m * c⁻¹ = c * n * c⁻¹
    rw [hm_eq]
  have hN'card : Nat.card N' = Nat.card N :=
    Subgroup.card_map_of_injective (f := (centralizer ({a} : Set G)).subtype)
      (centralizer ({a} : Set G)).subtype_injective
  have hodd' : Odd (Nat.card N') := by rw [hN'card]; exact hodd
  have hle : N' ≤ zpowers a := hD3.odd_normal a hat ha3 N' hN'le hN'norm hodd'
  intro n hn
  have hn' : (n : G) ∈ N' := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  have hzg : (n : G) ∈ zpowers a := hle hn'
  have hmap : (zpowers (aY a)).map (centralizer ({a} : Set G)).subtype = zpowers (a : G) :=
    map_subtype_zpowers (centralizer ({a} : Set G)) (aY a)
  have hnY : (n : G) ∈ (zpowers (aY a)).map (centralizer ({a} : Set G)).subtype := by
    rw [hmap]; exact hzg
  obtain ⟨m, hm, hm_eq⟩ := Subgroup.mem_map.mp hnY
  have hmn : m = n := Subtype.ext hm_eq
  exact hmn ▸ hm

theorem card_tInvolutions_Y (hD : HData G t z b z₁ S Eg T T' W0 ι) (hD3 : HData3 G t z z₁)
    (hconj : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) (hat : a ∈ centralizer ({t} : Set G))
    (ha3 : orderOf a = 3) : (tInvolutions (tY hat) (τY a t)).ncard = 46 := by
  have hset := image_tInvolutions_Y hD hconj hat
  rw [← ncard_image_val (centralizer ({a} : Set G)) (tInvolutions (tY hat) (τY a t)), hset]
  exact hD3.card_tT a hat ha3

theorem perfect60_Y (hD3 : HData3 G t z z₁) (hat : a ∈ centralizer ({t} : Set G))
    (ha3 : orderOf a = 3) :
    ∃ M : Subgroup (Y24 a), M ≤ centralizer ({tY hat} : Set (Y24 a)) ∧ ⁅M, M⁆ = M ∧
      Nat.card M = 60 ∧ M ⊓ zpowers (aY a) = ⊥ := by
  obtain ⟨M, hMle, hMcomm, hMcard, hMinf⟩ := hD3.perfect60 a hat ha3
  have hMT : M ≤ centralizer ({t} : Set G) := hMle.trans inf_le_left
  have hMY : M ≤ centralizer ({a} : Set G) := hMle.trans inf_le_right
  refine ⟨M.subgroupOf (centralizer ({a} : Set G)), ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hMT (Subgroup.mem_subgroupOf.mp hx))
  · rw [commutator_subgroupOf_of_le (Y := centralizer ({a} : Set G)) hMY hMY, hMcomm]
  · rw [card_subgroupOf_of_le (Y := centralizer ({a} : Set G)) hMY, hMcard]
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxM, hxa⟩ := Subgroup.mem_inf.mp hx
    have hxMg : (x : G) ∈ M := Subgroup.mem_subgroupOf.mp hxM
    have hxzp : (x : G) ∈ zpowers a := by
      have h1 : (x : G) ∈ (zpowers (aY a)).map (centralizer ({a} : Set G)).subtype :=
        Subgroup.mem_map.mpr ⟨x, hxa, rfl⟩
      rwa [map_subtype_zpowers (centralizer ({a} : Set G)) (aY a)] at h1
    have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
      rw [← hMinf]
      exact Subgroup.mem_inf.mpr ⟨hxMg, hxzp⟩
    exact Subtype.ext (Subgroup.mem_bot.mp hxbot)

theorem W_comm_Y (hD : HData G t z b z₁ S Eg T T' W0 ι) (hD3 : HData3 G t z z₁)
    (hconj : ∀ v, IsConj t (coordElt ι v) ↔ qp v = 1) (hat : a ∈ centralizer ({t} : Set G))
    (ha3 : orderOf a = 3) :
    ∃ s ∈ tInvolutions (tY hat) (τY a t),
      s ∈ ⁅Wsub (tY hat) (τY a t), Wsub (tY hat) (τY a t)⁆ := by
  obtain ⟨s, hsT, _, hs2, hs1, hsTG, hsW⟩ := hD3.W_comm a hat ha3
  have hset := image_tInvolutions_Y hD hconj hat
  have hclosure : (Wsub (tY hat) (τY a t)).map (centralizer ({a} : Set G)).subtype =
      WsubG t z z₁ a := by
    rw [Wsub, map_subtype_closure (centralizer ({a} : Set G))
      (tInvolutions (tY hat) (τY a t)), hset]
    rfl
  have hcomm : (⁅Wsub (tY hat) (τY a t), Wsub (tY hat) (τY a t)⁆).map
      (centralizer ({a} : Set G)).subtype = ⁅WsubG t z z₁ a, WsubG t z z₁ a⁆ := by
    rw [Subgroup.map_commutator, hclosure]
  have hsW' : s ∈ (⁅Wsub (tY hat) (τY a t), Wsub (tY hat) (τY a t)⁆).map
      (centralizer ({a} : Set G)).subtype := by
    rw [hcomm]; exact hsW
  obtain ⟨s', hs'comm, hs'eq⟩ := Subgroup.mem_map.mp hsW'
  refine ⟨s', ?_, hs'comm⟩
  simp only [tInvolutions, Set.mem_setOf_eq]
  have hs'T : s' ∈ centralizer ({tY hat} : Set (Y24 a)) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    show (centralizer ({a} : Set G)).subtype s' * t = t * (centralizer ({a} : Set G)).subtype s'
    rw [hs'eq]
    exact Subgroup.mem_centralizer_singleton_iff.mp hsT
  have hs'2 : s' ^ 2 = 1 := by
    apply Subtype.ext
    show (centralizer ({a} : Set G)).subtype s' ^ 2 = (1 : G)
    rw [hs'eq]
    exact hs2
  have hs'1 : s' ≠ 1 := by
    intro h
    apply hs1
    calc s = (s' : G) := hs'eq.symm
      _ = (1 : G) := by rw [h]; rfl
  have hs'τ : IsConj t ((centralizer ({a} : Set G)).subtype s') := by
    rw [hs'eq]
    exact (isConj_iff_tTG hD hconj hsT hs2 hs1).mpr hsTG
  exact ⟨hs'T, hs'2, hs'1, hs'τ⟩

end CFSG.EvenSporadicStandard.HNRecog.Harada
