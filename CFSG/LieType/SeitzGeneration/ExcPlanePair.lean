module

import CFSG.LinearAlgebra.SL2MinimalFaithfulMatrix
public import CFSG.Assembly.Defs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.Open Matrix

theorem natCard_sl2_field (K : Type*) [Field K] [Finite K] :
    Nat.card (SpecialLinearGroup (Fin 2) K) = Nat.card K * (Nat.card K ^ 2 - 1) :=
  CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two K

theorem isElemAbelian_closure_pair {G : Type*} [Group G] {p : ℕ} {a b : G} (hab : Commute a b)
    (ha : a ^ p = 1) (hb : b ^ p = 1) : IsElemAbelian p (Subgroup.closure ({a, b} : Set G)) := by
  have hc : ∀ x ∈ ({a, b} : Set G), ∀ y ∈ ({a, b} : Set G), Commute x y := by
    rintro x (rfl | rfl) y (rfl | rfl)
    exacts [Commute.refl _, hab, hab.symm, Commute.refl _]
  have hcomm : IsMulCommutative (Subgroup.closure ({a, b} : Set G)) :=
    Subgroup.isMulCommutative_closure fun x hx y hy _ => hc x hx y hy
  refine ⟨hcomm, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    exacts [ha, hb]
  | one => exact one_pow p
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := by
      have := hcomm.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
      exact congrArg Subtype.val this
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem card_closure_pair_sq {G : Type*} [Group G] {p : ℕ} (hp : p.Prime) {a b : G}
    (hab : Commute a b) (ha : orderOf a = p) (hb : orderOf b = p)
    (hind : b ∉ Subgroup.zpowers a) : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, Commute x y := by
    intro x hx y hy
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact hab.zpow_zpow m n
  have hcb : Nat.card ↥(Subgroup.zpowers b) = p := by rw [Nat.card_zpowers, hb]
  have hca : Nat.card ↥(Subgroup.zpowers a) = p := by rw [Nat.card_zpowers, ha]
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    have : Fact (Nat.card ↥(Subgroup.zpowers b)).Prime := ⟨by rw [hcb]; exact hp⟩
    have h := Subgroup.eq_bot_or_eq_top_of_prime_card
      ((Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b))
    rcases h with h | h
    · rw [Subgroup.subgroupOf_eq_bot] at h
      have h' := disjoint_iff.1 h
      rwa [inf_assoc, inf_idem] at h'
    · exfalso
      apply hind
      have hbb : (⟨b, Subgroup.mem_zpowers b⟩ : ↥(Subgroup.zpowers b)) ∈
          (Subgroup.zpowers a ⊓ Subgroup.zpowers b).subgroupOf (Subgroup.zpowers b) := by
        rw [h]; exact Subgroup.mem_top _
      exact (Subgroup.mem_subgroupOf.1 hbb).1
  let φ : Subgroup.zpowers a × Subgroup.zpowers b →* G :=
    MonoidHom.noncommCoprod (Subgroup.zpowers a).subtype (Subgroup.zpowers b).subtype
      fun x y => hcomm x x.2 y y.2
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, y⟩ hxy
    have hxy' : (x : G) * y = 1 := hxy
    have hx : (x : G) = (y : G)⁻¹ := eq_inv_of_mul_eq_one_left hxy'
    have hmem : (x : G) ∈ Subgroup.zpowers a ⊓ Subgroup.zpowers b :=
      ⟨x.2, by rw [hx]; exact (Subgroup.zpowers b).inv_mem y.2⟩
    rw [hinf, Subgroup.mem_bot] at hmem
    have hy : (y : G) = 1 := inv_eq_one.1 (hx.symm.trans hmem)
    exact Prod.ext (Subtype.ext hmem) (Subtype.ext hy)
  have hrange : φ.range = Subgroup.closure ({a, b} : Set G) := by
    have h1 : φ.range = (Subgroup.zpowers a).subtype.range ⊔ (Subgroup.zpowers b).subtype.range :=
      MonoidHom.noncommCoprod_range _ _ _
    rw [h1, Subgroup.range_subtype, Subgroup.range_subtype, Set.insert_eq,
      Subgroup.closure_union, ← Subgroup.zpowers_eq_closure, ← Subgroup.zpowers_eq_closure]
  rw [← hrange, Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_prod, hca, hcb,
    sq]

theorem exists_plane_of_commuting_sl2 {G K : Type*} [Group G] [Field K] [Finite K]
    (φ ψ : SpecialLinearGroup (Fin 2) K →* G) (hφ : Function.Injective φ)
    (hψ : Function.Injective ψ) (hcomm : ∀ g h, Commute (φ g) (ψ h)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card K * (Nat.card K ^ 2 - 1)) :
    ∃ A : Subgroup G, A ≤ φ.range ⊔ ψ.range ∧ IsElemAbelian p A ∧ Nat.card A = p ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := SpecialLinearGroup (Fin 2) K) p
    (by rw [natCard_sl2_field]; exact hdvd)
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' (G := SpecialLinearGroup (Fin 2) K) p
    (by rw [natCard_sl2_field]; exact hdvd)
  have ha : orderOf (φ g) = p := by rw [orderOf_injective φ hφ g, hg]
  have hb : orderOf (ψ h) = p := by rw [orderOf_injective ψ hψ h, hh]
  have hind : ψ h ∉ Subgroup.zpowers (φ g) := by
    intro hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hmem
    have hcen : h ∈ Subgroup.center (SpecialLinearGroup (Fin 2) K) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply hψ
      rw [map_mul, map_mul, ← hn, ← map_zpow]
      exact ((hcomm (g ^ n) y).symm).eq
    obtain ⟨r, hr, hrh⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hcen
    have hsq : h ^ 2 = 1 := by
      have hr2 : r ^ 2 = 1 := by simpa using hr
      apply Subtype.ext
      rw [sq, Matrix.SpecialLinearGroup.coe_mul, ← hrh, ← map_mul, ← sq, hr2, map_one]
      rfl
    have := orderOf_dvd_of_pow_eq_one hsq
    rw [hh] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  refine ⟨Subgroup.closure ({φ g, ψ h} : Set G), ?_, ?_, ?_⟩
  · refine (Subgroup.closure_le _).2 ?_
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_sup_left ⟨g, rfl⟩
    · exact Subgroup.mem_sup_right ⟨h, rfl⟩
  · exact isElemAbelian_closure_pair (hcomm g h) (by rw [← ha]; exact pow_orderOf_eq_one _)
      (by rw [← hb]; exact pow_orderOf_eq_one _)
  · exact card_closure_pair_sq hp (hcomm g h) ha hb hind

end CFSG.LieType.SeitzGeneration
