module

public import CFSG.Walter.Bender1970.S3.TransitivityTools
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.Assembly.Defs

public section

namespace CFSG.Goldschmidt.G37

open CFSG.GorensteinWalter

variable {G : Type*} [Group G]

section Components

theorem not_le_centralizer_self {K : Subgroup G} (hK : GorensteinWalter.IsQuasisimple K) :
    ¬ K ≤ Subgroup.centralizer (K : Set G) := by
  intro h
  obtain ⟨a, b, hab⟩ := CFSG.Walter.exists_mul_ne_mul_of_isQuasisimple hK
  apply hab
  apply Subtype.ext
  exact Subgroup.mem_centralizer_iff.mp (h b.2) a a.2

theorem le_commutator_or_commutator_eq_bot [Finite G] {K W B : Subgroup G} (hK : IsComponentOf K W)
    (hB : B ≤ Subgroup.normalizer (W : Set G)) : K ≤ ⁅K, B⁆ ∨ ⁅K, B⁆ = ⊥ := by
  have hKV : K ≤ Subgroup.normalizer ((⁅K, B⁆ : Subgroup G) : Set G) :=
    Subgroup.normalizer_commutator_ge_left K B
  have hVK : ⁅K, B⁆ ≤ Subgroup.normalizer (K : Set G) := by
    rw [Subgroup.commutator_le]
    intro k hk b hb
    have h2 : b * k⁻¹ * b⁻¹ ∈ Subgroup.normalizer (K : Set G) := by
      have hmem : b * k⁻¹ * b⁻¹ ∈ K.map (MulAut.conj b).toMonoidHom :=
        ⟨k⁻¹, K.inv_mem hk, rfl⟩
      rcases CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot
          (CFSG.Walter.isComponentOf_map_conj hK (hB hb)) hK with h | h
      · rw [h] at hmem
        exact Subgroup.le_normalizer hmem
      · apply Subgroup.centralizer_le_normalizer
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact (Subgroup.mem_centralizer_iff.mp
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hmem)) y hy
    rw [commutatorElement_def,
      show k * b * k⁻¹ * b⁻¹ = k * (b * k⁻¹ * b⁻¹) by group]
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk) h2
  rcases CFSG.Walter.commutator_eq_bot_or_le_of_isComponentOf hK hVK with h | h
  · right
    apply CFSG.LocalCores.perfect_double_commutator (Group.isPerfect_def.mpr hK.2.2.2.1)
    rw [Subgroup.commutator_comm]
    exact h
  · left
    exact h.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp hKV)

theorem le_or_commutator_eq_bot_of_le_normalizer [Finite G] {K W V : Subgroup G}
    (hK : IsComponentOf K W)
    (hVW : V ≤ Subgroup.normalizer (W : Set G)) (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ V ∨ ⁅K, V⁆ = ⊥ := by
  rcases le_commutator_or_commutator_eq_bot hK hVW with h | h
  · exact Or.inl (h.trans (Subgroup.le_normalizer_iff_commutator_le_right.mp hKV))
  · exact Or.inr h

theorem isComponentOf_of_le {K W V : Subgroup G} (hK : IsComponentOf K W) (hKV : K ≤ V)
    (hVW : V ≤ W) : IsComponentOf K V := by
  refine ⟨hKV, ?_, hK.2.2⟩
  have h1 := hK.2.1.comap (Subgroup.inclusion hVW)
  have h2 : K.subgroupOf V = (K.subgroupOf W).comap (Subgroup.inclusion hVW) := by
    ext x
    rfl
  rw [h2]
  exact h1

theorem isComponentOf_trans {K V W : Subgroup G} (hK : IsComponentOf K V) (hVW : V ≤ W)
    (hV : (V.subgroupOf W).IsSubnormal) : IsComponentOf K W :=
  ⟨hK.1.trans hVW, CFSG.Walter.isSubnormal_subgroupOf_trans hK.1 hK.2.1 hV, hK.2.2⟩

theorem eq_of_commutator_ne_bot [Finite G] {K L W : Subgroup G} (hK : IsComponentOf K W)
    (hL : IsComponentOf L W) (h : ⁅K, L⁆ ≠ ⊥) : K = L :=
  (CFSG.Walter.isComponentOf_eq_or_commutator_eq_bot hK hL).resolve_right h

theorem eq_of_isComponentOf_of_le [Finite G] {K L W : Subgroup G} (hK : IsComponentOf K W)
    (hL : IsComponentOf L W) (hKL : K ≤ L) : K = L := by
  refine eq_of_commutator_ne_bot hK hL fun h => not_le_centralizer_self hK.2.2 ?_
  have h1 : K ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  exact h1.trans (Subgroup.centralizer_le hKL)

theorem eq_or_le_centralizer_of_le_normalizer {K N : Subgroup G}
    (hK : GorensteinWalter.IsQuasisimple K) (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) :
    N = K ∨ N ≤ Subgroup.centralizer (K : Set G) := by
  have hKq : CFSG.IsQuasisimple K :=
    ⟨Group.isPerfect_def.mpr hK.2.1, hK.2.2, CFSG.Walter.IsQuasisimple.exists_mul_ne_mul hK⟩
  have hn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hKN
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hn with h | h
  · left
    apply le_antisymm hNK
    intro x hx
    have : (⟨x, hx⟩ : K) ∈ N.subgroupOf K := h ▸ Subgroup.mem_top _
    exact this
  · right
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have h1 := Subgroup.mem_center_iff.mp (h (show (⟨x, hNK hx⟩ : K) ∈ N.subgroupOf K from hx))
      ⟨y, hy⟩
    exact congrArg Subtype.val h1

end Components

section Products

theorem mem_sup_of_le_normalizer {W N : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N : Set G))
    {x : G} (hx : x ∈ W ⊔ N) : ∃ w ∈ W, ∃ n ∈ N, w * n = x := by
  have hle : W ⊔ N ≤ Subgroup.normalizer (N : Set G) := sup_le hWN Subgroup.le_normalizer
  have hNn : (N.subgroupOf (W ⊔ N)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hle
  have hx' : (⟨x, hx⟩ : ↥(W ⊔ N)) ∈ W.subgroupOf (W ⊔ N) ⊔ N.subgroupOf (W ⊔ N) := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
    exact Subgroup.mem_top _
  obtain ⟨w, hw, n, hn, hwn⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  exact ⟨w, hw, n, hn, congrArg Subtype.val hwn⟩

theorem map_subgroupOf_sup_eq_top {W N : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N : Set G))
    [(N.subgroupOf (W ⊔ N)).Normal] :
    (W.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N))) = ⊤ := by
  rw [eq_top_iff]
  rintro y -
  obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective _ y
  obtain ⟨w, hw, n, hn, hwn⟩ := mem_sup_of_le_normalizer hWN u.2
  refine ⟨⟨w, le_sup_left (a := W) hw⟩, hw, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have : (((⟨w, le_sup_left (a := W) hw⟩ : ↥(W ⊔ N))⁻¹ * u : ↥(W ⊔ N)) : G) = n := by
    show w⁻¹ * (u : G) = n
    rw [← hwn]
    group
  rw [this]
  exact hn

theorem normal_subgroupOf_sup {W N : Subgroup G} (hWN : W ≤ Subgroup.normalizer (N : Set G)) :
    (N.subgroupOf (W ⊔ N)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr
    (sup_le hWN Subgroup.le_normalizer)

theorem le_of_map_eq_bot {K W N : Subgroup G} (hKWN : K ≤ W ⊔ N)
    [(N.subgroupOf (W ⊔ N)).Normal]
    (h : (K.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N))) = ⊥) :
    K ≤ N := by
  intro x hx
  have h1 : QuotientGroup.mk' (N.subgroupOf (W ⊔ N)) (⟨x, hKWN hx⟩ : ↥(W ⊔ N)) ∈
      (K.subgroupOf (W ⊔ N)).map (QuotientGroup.mk' (N.subgroupOf (W ⊔ N))) :=
    ⟨⟨x, hKWN hx⟩, hx, rfl⟩
  rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem le_of_perfect_of_le_sup {K W N : Subgroup G} (hK : Group.IsPerfect K)
    (hKWN : K ≤ W ⊔ N) (hWN : W ≤ Subgroup.normalizer (N : Set G)) (hW : Group.IsSolvable W) :
    K ≤ N := by
  have := normal_subgroupOf_sup hWN
  set U := W ⊔ N with hU
  set π := QuotientGroup.mk' (N.subgroupOf U) with hπ
  have htop := map_subgroupOf_sup_eq_top (W := W) (N := N) hWN
  have hsolv : Group.IsSolvable (U ⧸ N.subgroupOf U) := by
    have hWs : Group.IsSolvable (W.subgroupOf U) :=
      Group.isSolvable_of_isSolvable_injective
        (f := (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ U)).toMonoidHom)
        (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ U)).injective
    have hsurj : Function.Surjective (π.comp (W.subgroupOf U).subtype) := by
      intro y
      have hy : y ∈ (W.subgroupOf U).map π := htop ▸ Subgroup.mem_top y
      obtain ⟨w, hw, rfl⟩ := hy
      exact ⟨⟨w, hw⟩, rfl⟩
    exact Group.isSolvable_of_surjective hsurj
  have hKU : Group.IsPerfect (K.subgroupOf U) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKWN).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKWN).symm.surjective
  refine le_of_map_eq_bot hKWN ?_
  by_contra hne
  have : Nontrivial ((K.subgroupOf U).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have : Group.IsPerfect ((K.subgroupOf U).map π) := Group.IsPerfect.map π
  have : Group.IsSolvable ((K.subgroupOf U).map π) :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
  exact Group.IsPerfect.not_isSolvable _ this

theorem le_of_coprime_of_le_sup {Y W N : Subgroup G} (hYWN : Y ≤ W ⊔ N)
    (hWN : W ≤ Subgroup.normalizer (N : Set G)) (hcop : Nat.Coprime (Nat.card Y) (Nat.card W)) :
    Y ≤ N := by
  have := normal_subgroupOf_sup hWN
  set U := W ⊔ N with hU
  set π := QuotientGroup.mk' (N.subgroupOf U) with hπ
  have htop := map_subgroupOf_sup_eq_top (W := W) (N := N) hWN
  refine le_of_map_eq_bot hYWN ?_
  apply Subgroup.eq_bot_of_card_eq
  apply Nat.eq_one_of_dvd_coprimes (a := Nat.card Y) (b := Nat.card W) hcop
  · refine (Subgroup.card_map_dvd _ π).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYWN).toEquiv]
  · have h1 : Nat.card ((Y.subgroupOf U).map π) ∣ Nat.card (⊤ : Subgroup (U ⧸ N.subgroupOf U)) :=
      Subgroup.card_dvd_of_le le_top
    refine h1.trans ?_
    rw [← htop]
    refine (Subgroup.card_map_dvd _ π).trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_left : W ≤ U)).toEquiv]

end Products

section OddCore

variable [Finite G]

theorem le_pPrimeCore_of_isSubnormal_of_odd {S : Subgroup G} (hS : S.IsSubnormal)
    (hodd : Odd (Nat.card S)) : S ≤ CFSG.pPrimeCore 2 G := by
  have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal hS
  have htop : CFSG.pPrimeCore 2 S = ⊤ := by
    apply le_antisymm le_top
    apply le_sSup
    exact ⟨Subgroup.normal_top, by
      rw [Subgroup.card_top]
      exact Nat.coprime_two_left.mpr hodd⟩
  rw [htop, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
  exact h1

theorem pResidualOf_eq_self_of_sup {X E Y : Subgroup G} (hX : X = E ⊔ Y)
    (hE : Group.IsPerfect E) (hY : Odd (Nat.card Y)) : pResidualOf X 2 = X := by
  have hEX : E ≤ X := hX ▸ le_sup_left
  have hYX : Y ≤ X := hX ▸ le_sup_right
  have key : ∀ N : Subgroup X, N.Normal → (∃ n, N.index = 2 ^ n) → N = ⊤ := by
    intro N hN ⟨n, hn⟩
    have hp : IsPGroup 2 (X ⧸ N) := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      apply IsPGroup.of_card (n := n)
      rw [← Subgroup.index_eq_card, hn]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hsolv : Group.IsSolvable (X ⧸ N) := by
      have := hp.isNilpotent
      infer_instance
    set π := QuotientGroup.mk' N with hπ
    have hEN : E.subgroupOf X ≤ N := by
      have hEp : Group.IsPerfect (E.subgroupOf X) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hEX).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hEX).symm.surjective
      have hbot : (E.subgroupOf X).map π = ⊥ := by
        by_contra hne
        have : Nontrivial ((E.subgroupOf X).map π) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
        have : Group.IsPerfect ((E.subgroupOf X).map π) := Group.IsPerfect.map π
        have : Group.IsSolvable ((E.subgroupOf X).map π) :=
          Group.isSolvable_of_isSolvable_injective (Subgroup.subtype_injective _)
        exact Group.IsPerfect.not_isSolvable _ this
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
      exact hbot
    have hYN : Y.subgroupOf X ≤ N := by
      have hbot : (Y.subgroupOf X).map π = ⊥ := by
        apply Subgroup.eq_bot_of_card_eq
        obtain ⟨k, hk⟩ := (hp.to_subgroup ((Y.subgroupOf X).map π)).exists_card_eq
        have h1 : Nat.card ((Y.subgroupOf X).map π) ∣ Nat.card Y := by
          refine (Subgroup.card_map_dvd _ π).trans ?_
          rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv]
        rw [hk] at h1 ⊢
        have h2 : Odd (2 ^ k) := hY.of_dvd_nat h1
        have hk0 : k = 0 := by
          by_contra hk
          exact (Nat.not_even_iff_odd.mpr h2) (Nat.even_pow.mpr ⟨even_two, hk⟩)
        rw [hk0, pow_zero]
      rw [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
      exact hbot
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx2 : x ∈ E ⊔ Y := hX ▸ hx
    have hx' : (⟨x, hx⟩ : X) ∈ (E ⊔ Y).subgroupOf X := hx2
    rw [Subgroup.subgroupOf_sup hEX hYX] at hx'
    exact (sup_le hEN hYN) hx'
  unfold pResidualOf
  have hinf : sInf {N : Subgroup X | N.Normal ∧ ∃ n, N.index = 2 ^ n} = ⊤ := by
    rw [eq_top_iff]
    refine le_sInf fun N hN => ?_
    rw [key N hN.1 hN.2]
  rw [hinf, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end OddCore

end CFSG.Goldschmidt.G37
