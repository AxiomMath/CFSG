module

public import Mathlib.GroupTheory.SpecificGroups.Cyclic

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

namespace TenNineOneThree

open Subgroup

variable {G : Type*} [Group G]

theorem not_isCyclic_of_mem [Finite G] {R : Subgroup G} {a b : G} (haR : a ∈ R) (hbR : b ∈ R)
    (ha : orderOf a = 3) (hb : orderOf b = 3) (hab : b ∉ zpowers a) : ¬ IsCyclic R := by
  intro hcyc
  set a' : R := ⟨a, haR⟩
  set b' : R := ⟨b, hbR⟩
  have ha' : orderOf a' = 3 := by rw [Subgroup.orderOf_mk]; exact ha
  have hb' : orderOf b' = 3 := by rw [Subgroup.orderOf_mk]; exact hb
  have heq : zpowers a' = zpowers b' := by
    rw [IsCyclic.subgroup_eq_iff_card_eq, Nat.card_zpowers, Nat.card_zpowers, ha', hb']
  apply hab
  have hb'a : b' ∈ zpowers a' := heq ▸ mem_zpowers b'
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb'a
  exact mem_zpowers_iff.mpr ⟨k, by simpa [a', b'] using congrArg Subtype.val hk⟩

theorem mem_normalizer_closure_pair [Finite G] {a b n : G}
    (ha : n * a * n⁻¹ ∈ closure ({a, b} : Set G))
    (hb : n * b * n⁻¹ ∈ closure ({a, b} : Set G)) :
    n ∈ normalizer ((closure ({a, b} : Set G) : Subgroup G) : Set G) := by
  set R := closure ({a, b} : Set G)
  have hle : R.map (MulAut.conj n).toMonoidHom ≤ R := by
    rw [Subgroup.map_le_iff_le_comap, closure_le]
    rintro x (rfl | rfl)
    · simpa using ha
    · simpa using hb
  have heq : R.map (MulAut.conj n).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    exact hle ⟨h, hh, by simp⟩
  · intro hh
    rw [← heq] at hh
    obtain ⟨h', hh', he⟩ := hh
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
    have : h' = h := by simpa using he
    exact this ▸ hh'

theorem conj_mem_normalizer_map {R : Subgroup G} {n : G} (hn : n ∈ normalizer (R : Set G))
    (k : G) :
    k * n * k⁻¹ ∈ normalizer ((R.map (MulAut.conj k).toMonoidHom : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key : ∀ x : G, x ∈ R.map (MulAut.conj k).toMonoidHom ↔ k⁻¹ * x * k ∈ R := by
    intro x
    constructor
    · rintro ⟨r, hr, rfl⟩
      simpa [mul_assoc] using hr
    · intro hx
      exact ⟨k⁻¹ * x * k, hx, by simp [mul_assoc]⟩
  rw [key, key]
  have : k⁻¹ * (k * n * k⁻¹ * h * (k * n * k⁻¹)⁻¹) * k = n * (k⁻¹ * h * k) * n⁻¹ := by group
  rw [this]
  exact Subgroup.mem_normalizer_iff.mp hn _

theorem mem_normalizer_comap {H : Type*} [Group H] (ι : G →* H) {R : Subgroup H} {n : G}
    (hn : ι n ∈ normalizer (R : Set H)) :
    n ∈ normalizer ((R.comap ι : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  show ι h ∈ R ↔ ι (n * h * n⁻¹) ∈ R
  rw [map_mul, map_mul, map_inv]
  exact Subgroup.mem_normalizer_iff.mp hn _

theorem fuse_gamma_of_conj_mem [Finite G] {T : Subgroup G} {a n : G} (haT : a ∈ T)
    (hoa : orderOf a = 3) (hin : n * a * n⁻¹ ∈ T) (hout : n * a * n⁻¹ ∉ zpowers a)
    (hn : n * (n * a * n⁻¹) * n⁻¹ ∈ closure ({a, n * a * n⁻¹} : Set G)) :
    ∃ R : Subgroup G, R ≤ T ∧ ¬ IsCyclic R ∧ n ∈ normalizer (R : Set G) := by
  refine ⟨closure ({a, n * a * n⁻¹} : Set G), ?_, ?_, ?_⟩
  · rw [closure_le]
    rintro w (rfl | rfl)
    · exact haT
    · exact hin
  · refine not_isCyclic_of_mem (subset_closure (by simp)) (subset_closure (by simp)) hoa ?_ hout
    rw [show n * a * n⁻¹ = MulAut.conj n a from rfl, MulEquiv.orderOf_eq, hoa]
  · exact mem_normalizer_closure_pair (subset_closure (by simp)) hn

theorem fuse_gamma_of_sq [Finite G] {T : Subgroup G} {a n : G} (hn2 : n * n = 1) (haT : a ∈ T)
    (hoa : orderOf a = 3) (hin : n * a * n⁻¹ ∈ T) (hout : n * a * n⁻¹ ∉ zpowers a) :
    ∃ R : Subgroup G, R ≤ T ∧ ¬ IsCyclic R ∧ n ∈ normalizer (R : Set G) := by
  refine fuse_gamma_of_conj_mem haT hoa hin hout ?_
  have hni : n⁻¹ = n := inv_eq_of_mul_eq_one_right hn2
  have : n * (n * a * n⁻¹) * n⁻¹ = a := by
    rw [hni, show n * (n * a * n) * n = (n * n) * a * (n * n) by group, hn2, one_mul, mul_one]
  rw [this]
  exact subset_closure (by simp)

theorem gamma_of_fuse_sq [Finite G] {T : Subgroup G} {a : G} (haT : a ∈ T) (hoa : orderOf a = 3)
    (h : ∃ n : G, n * n = 1 ∧ n * a * n⁻¹ ∈ T ∧ n * a * n⁻¹ ∉ zpowers a) :
    ∃ (R : Subgroup G) (n : G), R ≤ T ∧ ¬ IsCyclic R ∧ n ∈ normalizer (R : Set G) ∧
      n * a * n⁻¹ ∈ T ∧ n * a * n⁻¹ ∉ zpowers a := by
  obtain ⟨n, hn2, hin, hout⟩ := h
  obtain ⟨R, hRT, hRc, hnR⟩ := fuse_gamma_of_sq hn2 haT hoa hin hout
  exact ⟨R, n, hRT, hRc, hnR, hin, hout⟩

theorem gamma_of_fuse_sq_conj [Finite G] {T : Subgroup G} {a : G} (haT : a ∈ T)
    (hoa : orderOf a = 3)
    (h : ∃ n : G, (n * n) * a * (n * n)⁻¹ ∈ zpowers a ∧ n * a * n⁻¹ ∈ T ∧
      n * a * n⁻¹ ∉ zpowers a) :
    ∃ (R : Subgroup G) (n : G), R ≤ T ∧ ¬ IsCyclic R ∧ n ∈ normalizer (R : Set G) ∧
      n * a * n⁻¹ ∈ T ∧ n * a * n⁻¹ ∉ zpowers a := by
  obtain ⟨n, hn2, hin, hout⟩ := h
  have hle : zpowers a ≤ closure ({a, n * a * n⁻¹} : Set G) :=
    (zpowers_le).2 (subset_closure (by simp))
  obtain ⟨R, hRT, hRc, hnR⟩ := fuse_gamma_of_conj_mem haT hoa hin hout
    (by rw [show n * (n * a * n⁻¹) * n⁻¹ = (n * n) * a * (n * n)⁻¹ by group]; exact hle hn2)
  exact ⟨R, n, hRT, hRc, hnR, hin, hout⟩

theorem mem_normalizer_of_conj_mem [Finite G] {R : Subgroup G} {n : G}
    (h : ∀ r ∈ R, n * r * n⁻¹ ∈ R) : n ∈ normalizer (R : Set G) := by
  have hle : R.map (MulAut.conj n).toMonoidHom ≤ R := by
    rintro _ ⟨r, hr, rfl⟩
    exact h r hr
  have heq : R.map (MulAut.conj n).toMonoidHom = R :=
    Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj n).injective])
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h x, fun hx => ?_⟩
  rw [← heq] at hx
  obtain ⟨x', hx', he⟩ := hx
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at he
  have : x' = x := by simpa using he
  exact this ▸ hx'

end TenNineOneThree

end CFSG.LocalAnalysis.RankThreeTheoremC
