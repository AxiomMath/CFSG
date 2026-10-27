module

public import CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup

public section

namespace CFSG.LieType.SteinbergBR

open Subgroup

variable {G : Type*} [Group G]

theorem card_le_sq_of_orderOf [Finite G] {p : ℕ} [hp : Fact p.Prime] {g : G} {k : ℕ}
    (hg : orderOf g = p ^ k) (hG : ¬ p ^ (k + 2) ∣ Nat.card G) (A : Subgroup G)
    [IsElementaryAbelian p A] : Nat.card A ≤ p ^ 2 := by
  obtain ⟨S, hAS⟩ := (IsElementaryAbelian.isPGroup p A).exists_le_sylow
  have hgp : IsPGroup p (zpowers g) := IsPGroup.of_card (by rw [Nat.card_zpowers, hg])
  obtain ⟨S', hgS'⟩ := hgp.exists_le_sylow
  let y : S := Sylow.equiv S' S ⟨g, hgS' (mem_zpowers g)⟩
  have hy : orderOf (y : G) = p ^ k := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hg]
  have hCS : zpowers (y : G) ≤ S := zpowers_le.2 y.2
  have hCcard : Nat.card (zpowers (y : G)) = p ^ k := by rw [Nat.card_zpowers, hy]
  have hS : Nat.card S ∣ p ^ (k + 1) := by
    rw [Sylow.card_eq_multiplicity]
    apply pow_dvd_pow
    by_contra h
    exact hG ((pow_dvd_pow p (by omega)).trans (Nat.ordProj_dvd _ _))
  have h1 := relIndex_mul_card (zpowers (y : G)) S
  rw [inf_of_le_left hCS, hCcard] at h1
  have hrel : (zpowers (y : G)).relIndex S ≤ p := by
    have h2 : (zpowers (y : G)).relIndex S * p ^ k ≤ p * p ^ k := by
      rw [h1, ← pow_succ']
      exact Nat.le_of_dvd (pow_pos hp.out.pos _) hS
    exact Nat.le_of_mul_le_mul_right h2 (pow_pos hp.out.pos _)
  have hrel0 : (zpowers (y : G)).relIndex S ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact Nat.card_pos.ne' h1.symm
  have hCA : Nat.card ↥(zpowers (y : G) ⊓ A) ≤ p := by
    let K : Subgroup (zpowers (y : G)) := (zpowers (y : G) ⊓ A).subgroupOf (zpowers (y : G))
    have hK : Nat.card K = Nat.card ↥(zpowers (y : G) ⊓ A) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
    have hexp : Monoid.exponent K ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun z => by
      apply Subtype.ext
      apply Subtype.ext
      have hz : ((z : zpowers (y : G)) : G) ∈ A := (Subgroup.mem_subgroupOf.1 z.2).2
      simpa using elemPow_eq_one_of_isElementaryAbelian _ hz
    have : IsCyclic (zpowers (y : G)) := Subgroup.isCyclic_zpowers _
    rw [← hK, ← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd hp.out.pos hexp
  calc Nat.card A = (zpowers (y : G)).relIndex A * Nat.card ↥(zpowers (y : G) ⊓ A) :=
        (relIndex_mul_card _ _).symm
    _ ≤ p * p := Nat.mul_le_mul ((relIndex_le_of_le_right hAS hrel0).trans hrel) hCA
    _ = p ^ 2 := (sq p).symm

theorem pRank_le_of_card_le {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] {k : ℕ}
    (h : ∀ A : Subgroup H, IsElementaryAbelian p A → Nat.card A ≤ p ^ k) :
    CFSG.pRank p H ≤ k := by
  apply csSup_le'
  rintro r ⟨A, hA, hcard⟩
  have := h A hA
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right hp).1 this

theorem le_pRank_of_card {p : ℕ} (hp : 1 < p) {H : Type*} [Group H] [Finite H] (E : Subgroup H)
    (hE : IsElementaryAbelian p E) {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ CFSG.pRank p H := by
  refine le_csSup ⟨Nat.card H, ?_⟩ ⟨E, hE, hk⟩
  rintro r ⟨B, -, hB⟩
  calc r ≤ p ^ r := (Nat.lt_pow_self hp).le
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card H := Subgroup.card_le_card_group B

theorem pRank_two_eq_two_of [Finite G] (D : Subgroup G) {x y : G} (hx : x ∈ D) (hy : y ∈ D)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y)
    (hG : ∀ A : Subgroup G, IsElementaryAbelian 2 A → Nat.card A ≤ 2 ^ 2) :
    CFSG.pRank 2 D = 2 := by
  refine le_antisymm (pRank_le_of_card_le one_lt_two fun A hA => ?_) ?_
  · have := IsElementaryAbelian.map (p := 2) (A := A) D.subtype
    rw [← Subgroup.card_map_of_injective D.subtype_injective]
    exact hG _ this
  · obtain ⟨V, -, hV, hVcard⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.AlternatingFourGroup.exists_elementary_four_of_commute
        (x := (⟨x, hx⟩ : D)) (y := ⟨y, hy⟩) (by rw [Subgroup.orderOf_mk]; exact hx2)
        (by rw [Subgroup.orderOf_mk]; exact hy2) (Subtype.ext hxy)
        (fun h => hne (congrArg Subtype.val h))
    exact le_pRank_of_card one_lt_two V hV (by rw [hVcard]; norm_num)

end CFSG.LieType.SteinbergBR
