module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.FritzII.FzL410Def

public section

namespace CFSG.OddStandard.SmallF3.FritzII

open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem fz410x_om_eq_one_or_eq_of_mem_zpowers {W : Type*} [Group W] {a b : W}
    (ha : a ^ 2 = 1) (hb : b ∈ Subgroup.zpowers a) : b = 1 ∨ b = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
  have h2 : a ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast]
    exact ha
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left
    rw [← Int.emod_add_mul_ediv k 2, h, zero_add, zpow_mul, h2, one_zpow]
  · right
    rw [← Int.emod_add_mul_ediv k 2, h, zpow_add, zpow_mul, h2, one_zpow, mul_one, zpow_one]

theorem fz410x_om_card_comap {Q : Type*} [Group Q] (N : Subgroup Q) [N.Normal]
    (H : Subgroup (Q ⧸ N)) :
    Nat.card (H.comap (QuotientGroup.mk' N)) = Nat.card N * Nat.card H := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (QuotientGroup.preimageMkEquivSubgroupProdSet N (H : Set (Q ⧸ N)))

private theorem fz410x_om_eq_zpowers_of_card_two {W : Type*} [Group W] [Finite W]
    {X : Subgroup W} (hX : Nat.card X = 2) {x : W} (hx : x ∈ X) (hx2 : x ^ 2 = 1)
    (hx1 : x ≠ 1) : X = Subgroup.zpowers x := by
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hx) ?_).symm
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [orderOf_eq_prime hx2 hx1, hX]

private theorem fz410x_om_eq_of_card_two {W : Type*} [Group W] [Finite W]
    {X : Subgroup W} (hX : Nat.card X = 2) {x y : W} (hx : x ∈ X) (hy : y ∈ X)
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  have hXz : X = Subgroup.zpowers x := fz410x_om_eq_zpowers_of_card_two hX hx hx2 hx1
  rw [hXz] at hy
  rcases fz410x_om_eq_one_or_eq_of_mem_zpowers hx2 hy with h | h
  · exact absurd h hy1
  · exact h.symm

private noncomputable def fz410x_om_pick {W : Type*} [Group W] (H : Subgroup W)
    (hH : H ≠ ⊥) : W :=
  Subtype.val (Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp hH))

private theorem fz410x_om_pick_mem {W : Type*} [Group W] (H : Subgroup W) (hH : H ≠ ⊥) :
    fz410x_om_pick H hH ∈ H :=
  (Classical.choose (Subgroup.ne_bot_iff_exists_ne_one.mp hH)).2

private theorem fz410x_om_pick_ne_one {W : Type*} [Group W] (H : Subgroup W) (hH : H ≠ ⊥) :
    fz410x_om_pick H hH ≠ 1 :=
  fun h => Classical.choose_spec (Subgroup.ne_bot_iff_exists_ne_one.mp hH) (Subtype.ext h)

private noncomputable def fz410x_om_pickOfCard {W : Type*} [Group W] (H : Subgroup W)
    (hH : Nat.card H = 2) : W :=
  fz410x_om_pick H (by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hH
    norm_num at hH)

private theorem fz410x_om_pickOfCard_mem {W : Type*} [Group W] (H : Subgroup W)
    (hH : Nat.card H = 2) : fz410x_om_pickOfCard H hH ∈ H :=
  fz410x_om_pick_mem H _

private theorem fz410x_om_pickOfCard_ne_one {W : Type*} [Group W] (H : Subgroup W)
    (hH : Nat.card H = 2) : fz410x_om_pickOfCard H hH ≠ 1 :=
  fz410x_om_pick_ne_one H _

private theorem fz410x_om_zpowers_card {W : Type*} [Group W] (hexp : ∀ v : W, v ^ 2 = 1)
    {v : W} (hv : v ≠ 1) : Nat.card (Subgroup.zpowers v) = 2 := by
  rw [Nat.card_zpowers]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime (hexp v) hv

private theorem fz410x_om_ne_one_of_notMem {W : Type*} [Group W] (K : Subgroup W) {v : W}
    (hv : v ∉ K) : v ≠ 1 :=
  fun h => hv (by rw [h]; exact K.one_mem)

theorem fz410x_om_card_subgroups {W : Type*} [Group W] [Finite W] (K : Subgroup W)
    (hW : Nat.card W = 8) (hK : Nat.card K = 4) (hexp : ∀ v : W, v ^ 2 = 1) :
    Nat.card {H : Subgroup W // Nat.card H = 2 ∧ ¬ H ≤ K} = 4 := by
  have hcompl : Nat.card {v : W // v ∉ K} = 4 := by
    have hK' : (K : Set W).ncard = 4 := by
      rw [← Nat.card_coe_set_eq (K : Set W)]
      simpa using hK
    have h := Set.ncard_compl_of_ncard_eq_add (K : Set W) (n := 4) (by omega)
    rwa [← Nat.card_coe_set_eq ((K : Set W)ᶜ)] at h
  rw [← hcompl]
  refine Nat.card_congr ?_
  refine
  { toFun := fun H =>
      ⟨fz410x_om_pickOfCard H.1 H.2.1, by
        intro hv
        have hmem := fz410x_om_pickOfCard_mem H.1 H.2.1
        have hne := fz410x_om_pickOfCard_ne_one H.1 H.2.1
        have hz : H.1 = Subgroup.zpowers (fz410x_om_pickOfCard H.1 H.2.1) :=
          fz410x_om_eq_zpowers_of_card_two H.2.1 hmem (hexp _) hne
        exact H.2.2 (hz ▸ Subgroup.zpowers_le.mpr hv)⟩
    invFun := fun v =>
      ⟨Subgroup.zpowers v.1,
        fz410x_om_zpowers_card hexp (fz410x_om_ne_one_of_notMem K v.2),
        fun hle => v.2 (hle (Subgroup.mem_zpowers v.1))⟩
    left_inv := fun H => by
      apply Subtype.ext
      exact (fz410x_om_eq_zpowers_of_card_two H.2.1 (fz410x_om_pickOfCard_mem H.1 H.2.1)
        (hexp _) (fz410x_om_pickOfCard_ne_one H.1 H.2.1)).symm
    right_inv := fun v => by
      apply Subtype.ext
      exact fz410x_om_eq_of_card_two
        (fz410x_om_zpowers_card hexp (fz410x_om_ne_one_of_notMem K v.2))
        (fz410x_om_pickOfCard_mem (Subgroup.zpowers v.1)
          (fz410x_om_zpowers_card hexp (fz410x_om_ne_one_of_notMem K v.2)))
        (Subgroup.mem_zpowers v.1) (hexp _)
        (fz410x_om_pickOfCard_ne_one (Subgroup.zpowers v.1)
          (fz410x_om_zpowers_card hexp (fz410x_om_ne_one_of_notMem K v.2)))
        (fz410x_om_ne_one_of_notMem K v.2) }

noncomputable def fz410x_om_equiv {E P Q : Subgroup G} [(E.subgroupOf Q).Normal]
    (hEP : E ≤ P) (hPQ : P ≤ Q) :
    Fz410Om E P Q ≃
      {H : Subgroup (Q ⧸ E.subgroupOf Q) //
        Nat.card H = 2 ∧
          ¬ H ≤ (P.subgroupOf Q).map (QuotientGroup.mk' (E.subgroupOf Q))} := by
  let f : Q →* Q ⧸ E.subgroupOf Q := QuotientGroup.mk' (E.subgroupOf Q)
  let Psub : Subgroup Q := P.subgroupOf Q
  let Pbar : Subgroup (Q ⧸ E.subgroupOf Q) := Psub.map f
  change Fz410Om E P Q ≃
    {H : Subgroup (Q ⧸ E.subgroupOf Q) // Nat.card H = 2 ∧ ¬ H ≤ Pbar}
  have hfker : f.ker = E.subgroupOf Q := QuotientGroup.ker_mk' (E.subgroupOf Q)
  have hfsurj : Function.Surjective f := QuotientGroup.mk'_surjective _
  have hNP : E.subgroupOf Q ≤ Psub := fun x hx => hEP hx
  have hPbar_comap : Pbar.comap f = Psub := by
    dsimp only [Pbar]
    rw [Subgroup.comap_map_eq, hfker, sup_comm]
    exact sup_eq_right.mpr hNP
  have hcard_comap : ∀ H : Subgroup (Q ⧸ E.subgroupOf Q),
      Nat.card (H.comap f) = Nat.card (E.subgroupOf Q) * Nat.card H := by
    intro H
    rw [← Nat.card_prod]
    exact Nat.card_congr
      (QuotientGroup.preimageMkEquivSubgroupProdSet (E.subgroupOf Q) (H : Set _))
  have hEpos : 0 < Nat.card (E.subgroupOf Q) :=
    Finite.card_pos_iff.mpr ⟨⟨1, (E.subgroupOf Q).one_mem⟩⟩
  have hEN : Nat.card (E.subgroupOf Q) = Nat.card E :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_trans hEP hPQ)).toEquiv
  have hcardEK : ∀ A : Fz410Om E P Q,
      Nat.card ((A.1.subgroupOf Q).map f) = 2 := by
    intro A
    have hK : Nat.card (A.1.subgroupOf Q) = 2 * Nat.card (E.subgroupOf Q) := by
      have h1 : Nat.card (A.1.subgroupOf Q) = Nat.card A.1 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe A.2.le_Q).toEquiv
      rw [h1, A.2.card, hEN]
    have hcomp : ((A.1.subgroupOf Q).map f).comap f = A.1.subgroupOf Q := by
      rw [Subgroup.comap_map_eq, hfker, sup_comm]
      exact sup_eq_right.mpr (Subgroup.subgroupOf_mono Q A.2.E_le)
    have hc := hcard_comap ((A.1.subgroupOf Q).map f)
    rw [hcomp, hK] at hc
    exact Nat.mul_right_cancel hEpos (by
      rw [mul_comm (Nat.card ((A.1.subgroupOf Q).map f)) (Nat.card (E.subgroupOf Q))]
      exact hc.symm)
  refine
  { toFun := fun A =>
      ⟨(A.1.subgroupOf Q).map f, hcardEK A, by
        intro hle
        have hle' : A.1.subgroupOf Q ≤ Psub := by
          rw [← hPbar_comap]
          exact (Subgroup.map_le_iff_le_comap).mp hle
        have hmap : (A.1.subgroupOf Q).map Q.subtype ≤ Psub.map Q.subtype :=
          Subgroup.map_subtype_le_map_subtype.mpr hle'
        rw [Subgroup.map_subgroupOf_eq_of_le A.2.le_Q,
          Subgroup.map_subgroupOf_eq_of_le hPQ] at hmap
        exact A.2.not_le_P hmap⟩
    invFun := fun H =>
      ⟨(H.1.comap f).map Q.subtype, by
        intro e he
        refine Subgroup.mem_map.mpr ⟨⟨e, le_trans hEP hPQ he⟩, ?_, rfl⟩
        rw [Subgroup.mem_comap]
        change (QuotientGroup.mk' (E.subgroupOf Q)) ⟨e, le_trans hEP hPQ he⟩ ∈ H.1
        have h1 : (QuotientGroup.mk' (E.subgroupOf Q)) ⟨e, le_trans hEP hPQ he⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
          exact he
        rw [h1]
        exact H.1.one_mem
      , Subgroup.map_subtype_le _
      , by
        have h1 : Nat.card ((H.1.comap f).map Q.subtype) = Nat.card (H.1.comap f) :=
          Subgroup.card_map_of_injective Q.subtype_injective
        rw [h1, hcard_comap H.1, H.2.1, mul_comm (Nat.card (E.subgroupOf Q)) 2, hEN]
      , by
        intro hle
        apply H.2.2
        have hle' : H.1.comap f ≤ Psub := by
          have hmap : (H.1.comap f).map Q.subtype ≤ Psub.map Q.subtype := by
            rw [Subgroup.map_subgroupOf_eq_of_le hPQ]
            exact hle
          exact Subgroup.map_subtype_le_map_subtype.mp hmap
        rw [← Subgroup.map_comap_eq_self_of_surjective hfsurj H.1]
        exact Subgroup.map_mono hle'⟩
    left_inv := fun A => by
      apply Subtype.ext
      show (((A.1.subgroupOf Q).map f).comap f).map Q.subtype = A.1
      have hcomp : ((A.1.subgroupOf Q).map f).comap f = A.1.subgroupOf Q := by
        rw [Subgroup.comap_map_eq, hfker, sup_comm]
        exact sup_eq_right.mpr (Subgroup.subgroupOf_mono Q A.2.E_le)
      rw [hcomp, Subgroup.map_subgroupOf_eq_of_le A.2.le_Q]
    right_inv := fun H => by
      apply Subtype.ext
      show (((H.1.comap f).map Q.subtype).subgroupOf Q).map f = H.1
      have hcomp : ((H.1.comap f).map Q.subtype).subgroupOf Q = H.1.comap f :=
        Subgroup.comap_map_eq_self_of_injective Q.subtype_injective (H.1.comap f)
      rw [hcomp, Subgroup.map_comap_eq_self_of_surjective hfsurj H.1] }

end CFSG.OddStandard.SmallF3.FritzII
