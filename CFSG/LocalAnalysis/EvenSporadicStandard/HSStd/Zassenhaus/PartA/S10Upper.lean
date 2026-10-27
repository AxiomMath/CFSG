module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.PartA.S10Quot

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA

open Subgroup CFSG.Blueprint CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.HSStd.Zassenhaus

section Upper

variable {G : Type} [Group G] [Finite G] {L A : Subgroup G} {t u : G}

theorem card_cen_tu_eq (S : FusionSetup G L A t u) (hn : ¬ IsConj t u)
    (hX : IsSporadic (QuotT (t * u)) .HS) : Nat.card ↥(Cen (t * u)) = 88704000 := by
  have h := (zpowers (wOf (t * u))).card_eq_card_quotient_mul_card_subgroup
  have hw : wOf (t * u) * wOf (t * u) = 1 := Subtype.ext S.tu_sq
  have hw1 : wOf (t * u) ≠ 1 := by
    intro h1
    have h2 : t * u = 1 := congrArg Subtype.val h1
    have hu : u = t := by
      rw [eq_inv_of_mul_eq_one_right h2, inv_eq_of_mul_eq_one_right S.t_sq]
    apply hn
    rw [hu]
  have hcard2 : Nat.card (zpowers (wOf (t * u))) = 2 := by
    have : orderOf (wOf (t * u)) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hw) hw1
    rw [Nat.card_zpowers, this]
  rw [hcard2, card_eq_of_isSporadic_hs hX] at h
  omega

theorem comm_t_of_comm_tu (S : FusionSetup G L A t u) {g : G} (h1 : g * (t * u) = (t * u) * g)
    (h2 : g * u = u * g) : g * t = t * g := by
  apply mul_right_cancel (b := u)
  calc g * t * u = g * (t * u) := mul_assoc _ _ _
    _ = (t * u) * g := h1
    _ = t * (u * g) := mul_assoc _ _ _
    _ = t * (g * u) := by rw [h2]
    _ = t * g * u := (mul_assoc _ _ _).symm

theorem card_cent_uH (S : FusionSetup G L A t u) :
    Nat.card ↥(centralizer ({(⟨u, S.u_mem_Cen_tu⟩ : ↥(Cen (t * u)))} : Set ↥(Cen (t * u)))) =
      Nat.card ↥(centralizer ((Vsub t u : Subgroup G) : Set G)) := by
  refine Nat.card_congr
    { toFun := fun x => ⟨(x.1 : G), mem_centralizer_Vsub.2 ⟨?_, ?_⟩⟩
      invFun := fun y => ⟨⟨(y : G), ?_⟩, ?_⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl }
  · have h1 : (x.1 : G) * (t * u) = (t * u) * x.1 := mem_Cen.1 x.1.2
    have h2 : (x.1 : G) * u = u * x.1 :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)
    exact comm_t_of_comm_tu S h1 h2
  · exact congrArg Subtype.val (mem_centralizer_singleton_iff.1 x.2)
  · obtain ⟨h1, h2⟩ := mem_centralizer_Vsub.1 y.2
    rw [mem_Cen]
    calc (y : G) * (t * u) = (y * t) * u := (mul_assoc _ _ _).symm
      _ = (t * y) * u := by rw [h1]
      _ = t * (y * u) := mul_assoc _ _ _
      _ = t * (u * y) := by rw [h2]
      _ = (t * u) * y := (mul_assoc _ _ _).symm
  · exact mem_centralizer_singleton_iff.2 (Subtype.ext (mem_centralizer_Vsub.1 y.2).2)

theorem ncard_class_uH (S : FusionSetup G L A t u)
    (h5760 : Nat.card ↥(centralizer ((Vsub t u : Subgroup G) : Set G)) = 5760)
    (hH : Nat.card ↥(Cen (t * u)) = 88704000) :
    {x : ↥(Cen (t * u)) | IsConj (⟨u, S.u_mem_Cen_tu⟩ : ↥(Cen (t * u))) x}.ncard = 15400 := by
  have h := ncard_isConj_mul_card_centralizer (⟨u, S.u_mem_Cen_tu⟩ : ↥(Cen (t * u)))
  rw [card_cent_uH S, h5760, hH] at h
  omega

theorem ncard_invol7680_le {X : Type} [Group X] [Finite X] (hX : IsSporadic X .HS) :
    {z : X | orderOf z = 2 ∧ Nat.card (centralizer ({z} : Set X)) = 7680}.ncard ≤ 5775 := by
  by_cases hne : {z : X | orderOf z = 2 ∧ Nat.card (centralizer ({z} : Set X)) = 7680} = ∅
  · rw [hne]; simp
  obtain ⟨z₀, hz₀⟩ := Set.nonempty_iff_ne_empty.2 hne
  have hsub : {z : X | orderOf z = 2 ∧ Nat.card (centralizer ({z} : Set X)) = 7680} ⊆
      {x : X | IsConj z₀ x} := by
    intro z hz
    exact isConj_of_card_centralizer_eq_hs hX z₀ z hz₀.1 hz.1 (hz₀.2.trans hz.2.symm)
  have h := ncard_isConj_mul_card_centralizer z₀
  rw [hz₀.2, card_eq_of_isSporadic_hs hX] at h
  have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
  omega

theorem ncard_preimage_mkT_le {T : G} (hT : T * T = 1) (B : Set (QuotT T)) :
    (mkT T ⁻¹' B).ncard ≤ 2 * B.ncard := by
  classical
  let s : QuotT T → ↥(Cen T) := Function.surjInv (mkT_surjective T)
  have hs : ∀ z, mkT T (s z) = z := Function.surjInv_eq (mkT_surjective T)
  have hsub : mkT T ⁻¹' B ⊆ s '' B ∪ (fun x => x * wOf T) '' (s '' B) := by
    intro x hx
    have hxB : mkT T x ∈ B := hx
    have h : mkT T (s (mkT T x)) = mkT T x := hs _
    rcases (mkT_eq_mkT_iff hT).1 h with h1 | h1
    · left
      exact ⟨mkT T x, hxB, h1.symm⟩
    · right
      exact ⟨s (mkT T x), ⟨mkT T x, hxB, rfl⟩, h1.symm⟩
  calc (mkT T ⁻¹' B).ncard ≤ (s '' B ∪ (fun x => x * wOf T) '' (s '' B)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ (s '' B).ncard + ((fun x => x * wOf T) '' (s '' B)).ncard := Set.ncard_union_le _ _
    _ ≤ B.ncard + B.ncard := by
        refine add_le_add (Set.ncard_image_le (Set.toFinite _)) ?_
        exact (Set.ncard_image_le (Set.toFinite _)).trans (Set.ncard_image_le (Set.toFinite _))
    _ = 2 * B.ncard := by ring

theorem ncard_conj_u_le (S : FusionSetup G L A t u) (hn : ¬ IsConj t u)
    (hX : IsSporadic (QuotT (t * u)) .HS)
    (htb : Nat.card ↥(centralizer ({tBar S} : Set (QuotT (t * u)))) = 2880)
    (h5760 : Nat.card ↥(centralizer ((Vsub t u : Subgroup G) : Set G)) = 5760) :
    {g : G | IsConj u g ∧ g ∈ Cen (t * u)}.ncard ≤ 26951 := by
  have hT := S.tu_sq
  have hH := card_cen_tu_eq S hn hX
  have hu2 : orderOf u = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact orderOf_eq_prime (by rw [pow_two]; exact S.u_sq) S.u_ne
  let uH : ↥(Cen (t * u)) := ⟨u, S.u_mem_Cen_tu⟩
  let tH : ↥(Cen (t * u)) := ⟨t, S.t_mem_Cen_tu⟩
  have htu : tH * wOf (t * u) = uH := by
    refine Subtype.ext ?_
    change t * (t * u) = u
    rw [← mul_assoc, S.t_sq, one_mul]
  let SH : Set ↥(Cen (t * u)) := {x | IsConj u (x : G)}
  let B7 : Set (QuotT (t * u)) := {z | orderOf z = 2 ∧ Nat.card (centralizer ({z} : Set _)) = 7680}
  have hset : {g : G | IsConj u g ∧ g ∈ Cen (t * u)} = Subtype.val '' SH := by
    ext g
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨⟨g, h2⟩, h1, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨hx, x.2⟩
  have hsub : SH ⊆ {wOf (t * u)} ∪ ({x | IsConj uH x} ∪ mkT (t * u) ⁻¹' B7) := by
    intro x hx
    have hxo : orderOf (x : G) = 2 := (orderOf_eq_of_isConj' hx).symm.trans hu2
    have hxx : (x : G) * x = 1 := by
      have := pow_orderOf_eq_one (x : G)
      rwa [hxo, pow_two] at this
    have hxx' : x * x = 1 := Subtype.ext hxx
    by_cases hz : mkT (t * u) x = 1
    · left
      have h1 : mkT (t * u) 1 = mkT (t * u) x := by rw [map_one, hz]
      rcases (mkT_eq_mkT_iff hT).1 h1 with h2 | h2
      · exfalso
        have : (x : G) = 1 := congrArg Subtype.val h2
        rw [this, orderOf_one] at hxo
        omega
      · rw [one_mul] at h2
        exact h2
    · right
      have hzz : mkT (t * u) x * mkT (t * u) x = 1 := by rw [← map_mul, hxx', map_one]
      have hz2 : orderOf (mkT (t * u) x) = 2 := by
        have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact hzz) hz
      rcases card_centralizer_of_involution_hs hX _ hz2 with h7 | h28
      · right
        exact ⟨hz2, h7⟩
      · left
        have hconj : IsConj (mkT (t * u) x) (tBar S) :=
          isConj_of_card_centralizer_eq_hs hX _ _ hz2 (by
            have := tBar_sq S
            have hne : tBar S ≠ 1 := by
              intro h1
              have h2 : mkT (t * u) tH = mkT (t * u) 1 := by rw [map_one]; exact h1
              rcases (mkT_eq_mkT_iff hT).1 h2 with h3 | h3
              · exact S.t_ne (congrArg Subtype.val h3).symm
              · have h4 : (1 : G) = t * (t * u) := congrArg Subtype.val h3
                have : u = 1 := by
                  rw [← mul_assoc, S.t_sq, one_mul] at h4
                  exact h4.symm
                exact S.u_ne this
            have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
            exact orderOf_eq_prime (by rw [pow_two]; exact tBar_sq S) hne) (h28.trans htb.symm)
        obtain ⟨c, hc⟩ := isConj_iff.1 hconj
        obtain ⟨h, rfl⟩ := mkT_surjective (t * u) c
        have h1 : mkT (t * u) tH = mkT (t * u) (h * x * h⁻¹) := by
          rw [map_mul, map_mul, map_inv]
          exact hc.symm
        rcases (mkT_eq_mkT_iff hT).1 h1 with h2 | h2
        · exfalso
          have h3 : (h : G) * x * (h : G)⁻¹ = t := congrArg Subtype.val h2
          apply hn
          have key : (h : G)⁻¹ * ((h : G) * x * (h : G)⁻¹) * ((h : G)⁻¹)⁻¹ = x := by group
          rw [h3] at key
          have htx : IsConj t (x : G) := isConj_iff.2 ⟨(h : G)⁻¹, key⟩
          exact htx.trans hx.symm
        · rw [htu] at h2
          show IsConj uH x
          have key : h⁻¹ * (h * x * h⁻¹) * (h⁻¹)⁻¹ = x := by group
          rw [h2] at key
          exact isConj_iff.2 ⟨h⁻¹, key⟩
  have hB : (mkT (t * u) ⁻¹' B7).ncard ≤ 2 * 5775 :=
    (ncard_preimage_mkT_le hT B7).trans (Nat.mul_le_mul_left _ (ncard_invol7680_le hX))
  have hU : {x : ↥(Cen (t * u)) | IsConj uH x}.ncard = 15400 := ncard_class_uH S h5760 hH
  rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective]
  calc SH.ncard ≤ ({wOf (t * u)} ∪ ({x | IsConj uH x} ∪ mkT (t * u) ⁻¹' B7)).ncard :=
        Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ({wOf (t * u)} : Set _).ncard + (({x | IsConj uH x} ∪ mkT (t * u) ⁻¹' B7)).ncard :=
        Set.ncard_union_le _ _
    _ ≤ 1 + ({x | IsConj uH x}.ncard + (mkT (t * u) ⁻¹' B7).ncard) := by
        rw [Set.ncard_singleton]
        exact add_le_add le_rfl (Set.ncard_union_le _ _)
    _ ≤ 26951 := by omega

end Upper

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.PartA
