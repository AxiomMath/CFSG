module

public import CFSG.GroupTheory.ABGLocalTools.SylowNormalizerGrows

public section

namespace CFSG.GroupTheory

open Subgroup CFSG.ABGLocalTools

variable {G : Type*} [Group G]

theorem card_centralizer_singleton_congr_of_isConj {a b : G} (h : IsConj a b) :
    Nat.card (centralizer ({a} : Set G)) = Nat.card (centralizer ({b} : Set G)) := by
  obtain ⟨c, hc⟩ := isConj_iff.mp h
  subst hc
  have hmap : (centralizer ({a} : Set G)).map (MulAut.conj c).toMonoidHom =
      centralizer ({c * a * c⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      calc c * y * c⁻¹ * (c * a * c⁻¹) = c * (y * a) * c⁻¹ := by group
        _ = c * (a * y) * c⁻¹ := by rw [hy]
        _ = c * a * c⁻¹ * (c * y * c⁻¹) := by group
    · intro hx
      refine ⟨c⁻¹ * x * c, ?_, by group⟩
      calc c⁻¹ * x * c * a = c⁻¹ * (x * (c * a * c⁻¹)) * c := by group
        _ = c⁻¹ * (c * a * c⁻¹ * x) * c := by rw [hx]
        _ = a * (c⁻¹ * x * c) := by group
  rw [← hmap]
  exact (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm

variable [Finite G]

theorem isSylowOf_of_forall_pElement_normalizer_le {p : ℕ} [Fact p.Prime] {T H M : Subgroup G}
    (hT : IsSylowOf p T (H ⊓ M))
    (hN : ∀ g ∈ M, g ∈ normalizer (T : Set G) → IsPGroup p (zpowers g) → g ∈ H) :
    IsSylowOf p T M := by
  have hTM : T ≤ M := hT.le.trans inf_le_right
  have hTsub : IsPGroup p (T.subgroupOf M) := hT.isPGroup.comap_subtype
  obtain ⟨S, hTS⟩ := hTsub.exists_le_sylow
  let Sg : Subgroup G := (S : Subgroup M).map M.subtype
  have hTSg : T ≤ Sg := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTM]
    exact Subgroup.map_mono hTS
  have hSgM : Sg ≤ M := Subgroup.map_subtype_le _
  have hSgp : IsPGroup p Sg := S.isPGroup'.map M.subtype
  have hSyl : IsSylowOf p Sg M := ⟨S, rfl⟩
  have hT' : IsSylowOf p T (H ⊓ Sg) :=
    hT.of_le (le_inf (hT.le.trans inf_le_left) hTSg) (inf_le_inf_left H hSgM)
  have hN' : normalizer (T : Set G) ⊓ Sg ≤ H := by
    rintro g ⟨hgN, hgS⟩
    exact hN g (hSgM hgS) hgN (hSgp.to_le (Subgroup.zpowers_le.mpr hgS))
  have hTSg' : IsSylowOf p T Sg := isSylowOf_of_normalizer_inf_le hT' hN'
  have heq : Sg = T := hTSg'.eq_of_le hTSg le_rfl hSgp
  rw [← heq]
  exact hSyl

theorem dvd_relIndex_inf_centralizer_of_normal_pGroup {p : ℕ} [Fact p.Prime] {H J : Subgroup G}
    (hJH : J ≤ H) (hHN : H ≤ normalizer (J : Set G)) (hJp : IsPGroup p J) {y : G}
    (hJy : ¬ J ≤ centralizer ({y} : Set G)) :
    p ∣ (H ⊓ centralizer ({y} : Set G)).relIndex H := by
  let N : Subgroup H := J.subgroupOf H
  let P : Subgroup H := (H ⊓ centralizer ({y} : Set G)).subgroupOf H
  have : N.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mpr hHN
  have h1 : P.relIndex (N ⊔ P) = P.relIndex N := relIndex_sup_eq_relIndex_of_normal N P
  have h2 : P.relIndex (N ⊔ P) * (N ⊔ P).index = P.index :=
    Subgroup.relIndex_mul_index le_sup_right
  have hNp : IsPGroup p N := hJp.comap_subtype
  obtain ⟨n, hn⟩ := hNp.index (P.subgroupOf N)
  have hne : P.relIndex N ≠ 1 := by
    intro h
    rw [Subgroup.relIndex_eq_one] at h
    apply hJy
    intro x hx
    have hx' : (⟨x, hJH hx⟩ : H) ∈ N := hx
    exact (h hx').2
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact hne (by simpa using hn)
  have h3 : p ∣ P.relIndex N := by
    have : P.relIndex N = p ^ n := hn
    rw [this]
    exact dvd_pow_self p hn0
  have h4 : p ∣ P.index := by
    rw [← h2, h1]
    exact h3.mul_right _
  exact h4

omit [Finite G] in
theorem le_isSylowOf_of_isPGroup_of_le_normalizer {p : ℕ} [Fact p.Prime] {N P C : Subgroup G}
    (hP : IsSylowOf p P C) (hNC : N ≤ C) (hCN : C ≤ normalizer (N : Set G)) (hN : IsPGroup p N) :
    N ≤ P := by
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  have : (N.subgroupOf C).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNC).mpr hCN
  have hN' : IsPGroup p (N.subgroupOf C) := hN.comap_subtype
  have hle : N.subgroupOf C ≤ (Q : Subgroup C) := IsPGroup.le_sylow_of_normal hN' Q
  rw [hQ] at hle
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_subgroupOf.mpr hx :
    (⟨x, hNC hx⟩ : C) ∈ N.subgroupOf C))

theorem not_isConj_of_isSylowOf_inf_centralizer {p : ℕ} [Fact p.Prime] {z y : G} {K : Subgroup G}
    (hK : IsSylowOf p K (centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G)))
    (hN : ∀ g ∈ centralizer ({y} : Set G), g ∈ normalizer (K : Set G) →
      IsPGroup p (zpowers g) → g ∈ centralizer ({z} : Set G))
    (hdvd : p ∣ (centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G)).relIndex
      (centralizer ({z} : Set G))) :
    ¬ IsConj z y := by
  intro hconj
  have hKM : IsSylowOf p K (centralizer ({y} : Set G)) :=
    isSylowOf_of_forall_pElement_normalizer_le hK hN
  have hcard : Nat.card (centralizer ({y} : Set G)) = Nat.card (centralizer ({z} : Set G)) :=
    (card_centralizer_singleton_congr_of_isConj hconj).symm
  have hKH : K ≤ centralizer ({z} : Set G) := hK.le.trans inf_le_left
  have hKcard : Nat.card K = p ^ (Nat.card (centralizer ({z} : Set G))).factorization p := by
    rw [hKM.card_eq, hcard]
  have hKHs : IsSylowOf p K (centralizer ({z} : Set G)) := isSylowOf_of_card hKH hKcard
  rw [isSylowOf_iff] at hKHs
  obtain ⟨-, -, hndvd⟩ := hKHs
  apply hndvd
  rw [← Subgroup.relIndex_mul_relIndex K (centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G))
    (centralizer ({z} : Set G)) hK.le inf_le_left]
  exact hdvd.mul_left _

theorem exists_ne_one_mem_inf_of_card_eq_four {W A B : Subgroup G} (hA : A ≤ W) (hB : B ≤ W)
    (hW : Nat.card W = 8) (hAc : Nat.card A = 4) (hBc : Nat.card B = 4) :
    ∃ x ∈ A ⊓ B, x ≠ 1 := by
  have hAi : A.relIndex W = 2 := by
    have h := Subgroup.relIndex_mul_card A W
    rw [inf_eq_left.mpr hA, hAc, hW] at h
    omega
  have hBi : B.relIndex W = 2 := by
    have h := Subgroup.relIndex_mul_card B W
    rw [inf_eq_left.mpr hB, hBc, hW] at h
    omega
  have hle : (A ⊓ B).relIndex W ≤ 4 := by
    have := Subgroup.relIndex_inf_le (H := A) (K := B) (L := W)
    rw [hAi, hBi] at this
    exact this
  have hcard : Nat.card (A ⊓ B : Subgroup G) ≥ 2 := by
    have h := Subgroup.relIndex_mul_card (A ⊓ B) W
    rw [inf_eq_left.mpr (inf_le_left.trans hA), hW] at h
    by_contra hlt
    have h1 : Nat.card (A ⊓ B : Subgroup G) ≤ 1 := by omega
    have : (A ⊓ B).relIndex W * Nat.card (A ⊓ B : Subgroup G) ≤ 4 * 1 :=
      Nat.mul_le_mul hle h1
    omega
  have hnt : Nontrivial (A ⊓ B : Subgroup G) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    omega
  obtain ⟨x, hx, hx1⟩ := Subgroup.exists_ne_one_of_nontrivial (A ⊓ B : Subgroup G)
  exact ⟨x, hx, hx1⟩

theorem normalizer_le_centralizer_of_pairwise_nonconj {A W : Subgroup G} {z : G}
    (hA : Nat.card A = 4) (hW : Nat.card W = 8) (hAW : A ≤ W) (hzA : z ∈ A)
    (hnc : ∀ a ∈ A, ∀ b ∈ A, IsConj a b → a = b)
    (hfus : ∀ g : G, (∃ e ∈ A, e ≠ 1 ∧ e ≠ z ∧ g ∈ centralizer ({e} : Set G)) →
      g * z * g⁻¹ ∈ W → g * z * g⁻¹ = z) :
    normalizer (W : Set G) ≤ centralizer ({z} : Set G) := by
  intro g hg
  have hgW : ∀ x ∈ W, g * x * g⁻¹ ∈ W := fun x hx => (mem_normalizer_iff.mp hg x).mp hx
  let B : Subgroup G := A.map (MulAut.conj g).toMonoidHom
  have hBW : B ≤ W := by
    rintro _ ⟨a, ha, rfl⟩
    exact hgW a (hAW ha)
  have hBc : Nat.card B = 4 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hA]
  obtain ⟨x, ⟨hxA, hxB⟩, hx1⟩ := exists_ne_one_mem_inf_of_card_eq_four hAW hBW hW hA hBc
  obtain ⟨a, haA, rfl⟩ := hxB
  have ha1 : a ≠ 1 := by
    rintro rfl
    exact hx1 (by simp)
  have hconj : IsConj a (MulAut.conj g a) := by
    rw [isConj_iff]
    exact ⟨g, by simp⟩
  have heq : MulAut.conj g a = a := (hnc a haA _ hxA hconj).symm
  have hga : g ∈ centralizer ({a} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have : g * a * g⁻¹ = a := heq
    calc g * a = g * a * g⁻¹ * g := by group
      _ = a * g := by rw [this]
  by_cases haz : a = z
  · rw [← haz]
    exact hga
  · have hzW : g * z * g⁻¹ ∈ W := hgW z (hAW hzA)
    have hz' : g * z * g⁻¹ = z := hfus g ⟨a, haA, ha1, haz, hga⟩ hzW
    rw [mem_centralizer_singleton_iff]
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [hz']

end CFSG.GroupTheory
