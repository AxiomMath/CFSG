module

public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoFus
public import CFSG.GH74.GLS.Stage2.Signalizer.L52TwoLift
public import CFSG.GH74.GLS.Stage2.Local.P27.FullFBuild

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L52Two

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Local.P27

section Iso

variable {G : Type} [Group G] [Finite G]

theorem mk_injective_of_isPGroup {H Q : Subgroup G} (hQH : Q ≤ H) (hQ2 : IsPGroup 2 ↥Q) :
    Function.Injective ((P34.mkH H).comp (Subgroup.inclusion hQH)) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have hodd : Odd (orderOf (Subgroup.inclusion hQH q)) :=
    P34.odd_orderOf_of_mem_core H ((P34.mkH_eq_one_iff H).1 hq)
  rw [orderOf_injective _ (Subgroup.inclusion_injective hQH) q] at hodd
  obtain ⟨k, hk⟩ := hQ2 q
  have hdvd : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have hcop : Nat.Coprime (orderOf q) (2 ^ k) := (Nat.coprime_two_right.2 hodd).pow_right k
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

theorem exists_mulEquiv_of_barIn_eq {H Q : Subgroup G} {W : Subgroup (HBar H)} (hQH : Q ≤ H)
    (hQ2 : IsPGroup 2 ↥Q) (hQW : barIn H Q = W) :
    ∃ e : ↥Q ≃* ↥W, ∀ q : ↥Q, (e q : HBar H) = P34.mkH H ⟨(q : G), hQH q.2⟩ := by
  subst hQW
  have hrange : ((P34.mkH H).comp (Subgroup.inclusion hQH)).range = barIn H Q := by
    ext y
    constructor
    · rintro ⟨q, rfl⟩
      exact Subgroup.mem_map.2 ⟨⟨(q : G), hQH q.2⟩, Subgroup.mem_subgroupOf.2 q.2, rfl⟩
    · intro hy
      obtain ⟨h, hh, rfl⟩ := Subgroup.mem_map.1 hy
      exact ⟨⟨(h : G), Subgroup.mem_subgroupOf.1 hh⟩, rfl⟩
  exact ⟨(MonoidHom.ofInjective (mk_injective_of_isPGroup hQH hQ2)).trans
    (MulEquiv.subgroupCongr hrange), fun q => rfl⟩

end Iso

section Jx

variable {G : Type} [Group G] [Finite G]

theorem inf_Jx_eq_bot {x : G} {Q : Subgroup G} (hQ2 : IsPGroup 2 ↥Q)
    (hQC : Q ≤ centralizer ({x} : Set G)) (hxJ : x ∉ Jx x)
    (hZ : ∀ c ∈ center ↥Q, c = 1 ∨ (c : G) = x) : Q ⊓ Jx x = ⊥ := by
  by_contra hne
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  have hg : (a : G) ∈ Q ⊓ Jx x := a.2
  have hg1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  have hN : ((Q ⊓ Jx x).subgroupOf Q).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hn' := Subgroup.mem_inf.1 hn
    refine Subgroup.mem_inf.2 ⟨Q.mul_mem (Q.mul_mem g.2 hn'.1) (Q.inv_mem g.2), ?_⟩
    exact (Subgroup.mem_normalizer_iff.1 (S45.mem_normalizer_Jx (hQC g.2)) _).1 hn'.2
  have hne' : (Q ⊓ Jx x).subgroupOf Q ≠ ⊥ := by
    intro h
    have : (⟨(a : G), (Subgroup.mem_inf.1 hg).1⟩ : ↥Q) ∈ (Q ⊓ Jx x).subgroupOf Q := hg
    rw [h, Subgroup.mem_bot] at this
    exact hg1 (congrArg Subtype.val this)
  have : Group.IsNilpotent ↥Q := hQ2.isNilpotent
  obtain ⟨c, hc1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne')
  have hcN : (c : ↥Q) ∈ (Q ⊓ Jx x).subgroupOf Q := (Subgroup.mem_inf.1 c.2).1
  have hcZ : (c : ↥Q) ∈ center ↥Q := (Subgroup.mem_inf.1 c.2).2
  rcases hZ _ hcZ with h | h
  · exact hc1 (Subtype.ext h)
  · have hcJ : ((c : ↥Q) : G) ∈ Jx x := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hcN)).2
    rw [h] at hcJ
    exact hxJ hcJ

end Jx

section Main

variable {G : Type} [Group G] [Finite G] {z t : G}

omit [Finite G] in
theorem mem_barIn_U4_sq {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H) {y : HBar H}
    (hy : y ∈ barIn H (U4 z t)) : y * y = 1 := by
  rcases (mem_barIn_U4_iff hU hz ht).1 hy with h | h | h | h <;> rw [h]
  · exact mul_one 1
  · rw [← map_mul]
    exact (congrArg (P34.mkH H) (Subtype.ext hU.z_sq : (⟨z, hz⟩ * ⟨z, hz⟩ : ↥H) = 1)).trans
      (map_one _)
  · rw [← map_mul]
    exact (congrArg (P34.mkH H) (Subtype.ext hU.t_sq : (⟨t, ht⟩ * ⟨t, ht⟩ : ↥H) = 1)).trans
      (map_one _)
  · rw [← map_mul]
    exact (congrArg (P34.mkH H) (Subtype.ext (zt_mul_self_eq_one hU) :
      (⟨z * t, H.mul_mem hz ht⟩ * ⟨z * t, H.mul_mem hz ht⟩ : ↥H) = 1)).trans (map_one _)

theorem isDihedral_barIn_U4 {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H) :
    IsDihedral ↥(barIn H (U4 z t)) := by
  set a : HBar H := P34.mkH H ⟨z, hz⟩ with ha
  set b : HBar H := P34.mkH H ⟨t, ht⟩ with hb
  have hV : ∀ y : HBar H, y ∈ barIn H (U4 z t) ↔ y = 1 ∨ y = a ∨ y = b ∨ y = a * b := fun y => by
    rw [mem_barIn_U4_iff hU hz ht, mk_zt_eq hz ht]
  have ha1 : a ≠ 1 := mk_z_ne_one hU hz
  have hb1 : b ≠ 1 := mk_t_ne_one hU ht
  have hab : a ≠ b := mk_z_ne_t hU hz ht
  have hab1 : a * b ≠ 1 := by
    rw [← mk_zt_eq hz ht]
    exact mk_zt_ne_one hU hz ht
  have haV : a ∈ barIn H (U4 z t) := (hV a).2 (Or.inr (Or.inl rfl))
  have hcard : Nat.card ↥(barIn H (U4 z t)) = 4 := by
    have hset : ((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H)) = {1, a, b, a * b} := by
      ext y
      simp only [SetLike.mem_coe, Set.mem_insert_iff, Set.mem_singleton_iff]
      exact hV y
    have h1 : (1 : HBar H) ∉ ({a, b, a * b} : Set (HBar H)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      exact ⟨ha1.symm, hb1.symm, hab1.symm⟩
    have h2 : a ∉ ({b, a * b} : Set (HBar H)) := by
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨hab, fun h => hb1 ?_⟩
      simpa using h.symm
    have h3 : b ≠ a * b := fun h => ha1 (by simpa using h.symm)
    show Nat.card ↥((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H)) = 4
    rw [Nat.card_coe_set_eq, hset, Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2,
      Set.ncard_pair h3]
  have hexp : Monoid.exponent ↥(barIn H (U4 z t)) = 2 := by
    have : Nontrivial ↥(barIn H (U4 z t)) :=
      ⟨⟨⟨a, haV⟩, 1, fun h => ha1 (congrArg Subtype.val h)⟩⟩
    rw [Monoid.exponent_eq_prime_iff Nat.prime_two]
    intro g hg
    refine orderOf_eq_prime ?_ hg
    rw [pow_two]
    exact Subtype.ext (mem_barIn_U4_sq hU hz ht g.2)
  have : IsKleinFour ↥(barIn H (U4 z t)) := ⟨hcard, hexp⟩
  obtain ⟨e⟩ := IsKleinFour.nonempty_mulEquiv (G₁ := ↥(barIn H (U4 z t))) (G₂ := DihedralGroup 2)
  exact ⟨4, 2, rfl, le_rfl, ⟨e⟩⟩

omit [Finite G] in
theorem barIn_zpowers_eq (H : Subgroup G) {g : G} (hgH : g ∈ H) :
    barIn H (zpowers g) = zpowers (P34.mkH H ⟨g, hgH⟩) := by
  have h1 : (zpowers g).subgroupOf H = zpowers (⟨g, hgH⟩ : ↥H) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨n, hn⟩
      exact ⟨n, Subtype.ext (by simpa using hn)⟩
    · rintro ⟨n, hn⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  unfold barIn
  rw [h1, MonoidHom.map_zpowers]

theorem W_cyclic_or_dihedral {H : Subgroup G} (hU : UData z t) (hz : z ∈ H) (ht : t ∈ H)
    (hDQ : DihQuot (z * t)) {W : Subgroup (HBar H)} (hW2 : IsPGroup 2 ↥W)
    (hUW : barIn H (U4 z t) ≤ W)
    (hWC : W ⊓ centralizer ((barIn H (U4 z t) : Subgroup (HBar H)) : Set (HBar H)) ≤
      barIn H (U4 z t)) :
    IsCyclic ↥W ∨ IsDihedral ↥W := by
  by_cases hWU : W = barIn H (U4 z t)
  · subst hWU
    exact Or.inr (isDihedral_barIn_U4 hU hz ht)
  obtain ⟨hxW, hWx, -, hZ⟩ := W_facts hU hz ht hW2 hUW hWC
  have hxH : z * t ∈ H := H.mul_mem hz ht
  have hxo : orderOf (z * t) = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact zt_mul_self_eq_one hU) (zt_ne_one hU)
  have hAH : zpowers (z * t) ≤ H := zpowers_le.2 hxH
  have hA2 : IsPGroup 2 ↥(zpowers (z * t)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hAcomm : ∀ a ∈ zpowers (z * t), ∀ b ∈ zpowers (z * t), a * b = b * a := by
    intro a ha b hb
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.1 ha
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    exact ((Commute.refl (z * t)).zpow_zpow m n).eq
  have hbar : barIn H (zpowers (z * t)) = zpowers (P34.mkH H ⟨z * t, hxH⟩) :=
    barIn_zpowers_eq H hxH
  have hQC : W ≤ centralizer ((barIn H (zpowers (z * t)) : Subgroup (HBar H)) : Set (HBar H)) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [SetLike.mem_coe, hbar] at hy
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
    have hc : Commute (P34.mkH H ⟨z * t, hxH⟩) w := (hWx w hw).symm
    exact (hc.zpow_left n).eq
  have hAQ : barIn H (zpowers (z * t)) ≤ W := by
    rw [hbar]
    exact zpowers_le.2 hxW
  obtain ⟨Q, hQH, hQC', hQ2, hAQ', hQW⟩ := exists_lift_centralizer hAH hA2 hAcomm hW2 hQC hAQ
  obtain ⟨e, he⟩ := exists_mulEquiv_of_barIn_eq hQH hQ2 hQW
  have hxQ : z * t ∈ Q := hAQ' (mem_zpowers _)
  have hQx : Q ≤ centralizer ({z * t} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.1 (hQC' hq) (z * t) (mem_zpowers _)).symm
  have hZQ : ∀ c ∈ center ↥Q, c = 1 ∨ (c : G) = z * t := by
    intro c hc
    have hec : e c ∈ center ↥W := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨q, rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hc q]
    rcases hZ hWU _ hec with h | h
    · exact Or.inl (e.map_eq_one_iff.1 (Subtype.ext h))
    · right
      have h1 : ((e c : ↥W) : HBar H) = ((e ⟨z * t, hxQ⟩ : ↥W) : HBar H) := by rw [h, he]
      have h2 : c = ⟨z * t, hxQ⟩ := e.injective (Subtype.ext h1)
      exact congrArg Subtype.val h2
  have hQJ : Q ⊓ Jx (z * t) = ⊥ := inf_Jx_eq_bot hQ2 hQx hDQ.1 hZQ
  exact S45.cyclic_or_dihedral_congr e (hDQ.2 Q hQx hQ2 hQJ)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.L52Two
