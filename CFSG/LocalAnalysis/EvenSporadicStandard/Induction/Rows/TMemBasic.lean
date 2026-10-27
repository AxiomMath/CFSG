module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Complement
public import CFSG.Milestones.OO_odd_order_solvable

public section

namespace CFSG.EvenSporadicStandard.Induction.TMem

open Subgroup CFSG.EvenSporadicStandard CFSG.EvenSporadicStandard.Induction.Closing
open scoped commutatorElement

variable {H : Type} [Group H]

theorem isPGroup_zpowers_two {X : Type*} [Group X] {u : X} (hu : orderOf u = 2) :
    IsPGroup 2 ↥(zpowers u) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])

theorem mem_of_odd_orderOf [Finite H] {N : Subgroup H} [N.Normal] (hidx : N.index ≤ 2) {x : H}
    (hx : Odd (orderOf x)) : x ∈ N := by
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ orderOf x := orderOf_map_dvd _ _
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ N.index := by
    rw [Subgroup.index]; exact orderOf_dvd_natCard _
  have hodd : Odd (orderOf (QuotientGroup.mk' N x)) := hx.of_dvd_nat h1
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h3 : orderOf (QuotientGroup.mk' N x) = 1 := by
    have h4 := Nat.le_of_dvd hpos h2
    have h5 : orderOf (QuotientGroup.mk' N x) ≤ 2 := h4.trans hidx
    have h6 : 0 < orderOf (QuotientGroup.mk' N x) := orderOf_pos _
    obtain ⟨k, hk⟩ := hodd
    omega
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).1 h3

theorem sq_mem_of_index_le_two [Finite H] {N : Subgroup H} [N.Normal] (hidx : N.index ≤ 2)
    (x : H) : x ^ 2 ∈ N := by
  have h := Subgroup.pow_index_mem N x
  have hpos : 0 < N.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  rcases (by omega : N.index = 1 ∨ N.index = 2) with h1 | h1
  · rw [h1, pow_one] at h
    exact pow_mem h 2
  · rwa [h1] at h

theorem le_of_perfect_of_index_le_two [Finite H] {N P : Subgroup H} [N.Normal]
    (hi : N.index ≤ 2) [hp : Group.IsPerfect ↥P] : P ≤ N := by
  have hc : IsMulCommutative (H ⧸ N) := by
    have hcard : Nat.card (H ⧸ N) ≤ 2 := by rw [← Subgroup.index_eq_card]; exact hi
    have hpos : 0 < Nat.card (H ⧸ N) := Nat.card_pos
    rcases (by omega : Nat.card (H ⧸ N) = 1 ∨ Nat.card (H ⧸ N) = 2) with h1 | h2
    · have : Subsingleton (H ⧸ N) := (Nat.card_eq_one_iff_unique.1 h1).1
      exact ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩
    · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := isCyclic_of_prime_card h2
      infer_instance
  calc P = ⁅P, P⁆ := Subgroup.commutator_eq_self.symm
    _ ≤ N := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      have hmk : (QuotientGroup.mk' N) ⁅a, b⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hc.is_comm.comm _ _)
      exact (QuotientGroup.eq_one_iff _).1 hmk

theorem isPerfect_subgroupOf {A C : Subgroup H} (h : A ≤ C) [Group.IsPerfect ↥A] :
    Group.IsPerfect ↥(A.subgroupOf C) :=
  Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe h).symm.toMonoidHom)
    (Subgroup.subgroupOfEquivOfLe h).symm.surjective

theorem card_sylow_eq_two_of_not_mem [Finite H] {N L : Subgroup H} [N.Normal] (hidx : N.index ≤ 2)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S) {t : H}
    (htC : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (htN : t ∉ N)
    (P : Sylow 2 (centralizer (L : Set H))) : Nat.card P = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t' : centralizer (L : Set H) := ⟨t, htC⟩
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  obtain ⟨P', hP'⟩ := (isPGroup_zpowers_two ht'2).exists_le_sylow
  have ht'P : t' ∈ (P' : Subgroup (centralizer (L : Set H))) := hP' (mem_zpowers t')
  obtain ⟨S₀, hS₀⟩ := hcyc
  have hcycP' : IsCyclic ↥(P' : Subgroup (centralizer (L : Set H))) := by
    let f : S₀ ≃* P' := Sylow.equiv S₀ P'
    exact isCyclic_of_surjective f.toMonoidHom f.surjective
  have hcard : Nat.card P = Nat.card P' := Nat.card_congr (Sylow.equiv P P').toEquiv
  rw [hcard]
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P'.isPGroup'
  have h2dvd : 2 ∣ Nat.card P' := by
    have h := orderOf_dvd_natCard (⟨t', ht'P⟩ : ↥(P' : Subgroup (centralizer (L : Set H))))
    rwa [Subgroup.orderOf_mk, ht'2] at h
  by_contra hne
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h | h
    · interval_cases k
      · rw [pow_zero] at hk; rw [hk] at h2dvd; omega
      · rw [pow_one] at hk; exact absurd hk hne
    · exact h
  obtain ⟨g, hg⟩ := hcycP'.exists_generator
  have hgord : orderOf g = Nat.card P' := orderOf_eq_card_of_forall_mem_zpowers hg
  have h4 : 4 ∣ orderOf g := by
    rw [hgord, hk]
    have := pow_dvd_pow 2 hk2
    simpa using this
  have hord0 : orderOf g ≠ 0 := orderOf_pos g |>.ne'
  set x := g ^ (orderOf g / 4) with hx
  have hx4 : orderOf x = 4 := orderOf_pow_orderOf_div hord0 h4
  have hy2 : orderOf (x ^ 2) = 2 := by
    rw [orderOf_pow_of_dvd (by norm_num) (by rw [hx4]; norm_num), hx4]
  have hy : (((x ^ 2 : ↥(P' : Subgroup (centralizer (L : Set H)))) :
      centralizer (L : Set H))) = t' := by
    refine eq_of_orderOf_eq_two_of_cyclic hcycP' (Subtype.property _) ht'P ?_ ht'2
    rw [Subgroup.orderOf_coe]
    exact hy2
  have hteq : t = (((x : centralizer (L : Set H)) : H)) ^ 2 := by
    have := congrArg (fun z : centralizer (L : Set H) => (z : H)) hy
    simpa [t'] using this.symm
  exact htN (hteq ▸ sq_mem_of_index_le_two hidx _)

@[expose] def OddCN (N L : Subgroup H) : Prop :=
  ∀ c ∈ centralizer (L : Set H), c ∈ N → Odd (orderOf c)

theorem oddCN_of_not_mem [Finite H] {N L : Subgroup H} [N.Normal] (hidx : N.index ≤ 2)
    (hcyc : ∃ S : Sylow 2 (centralizer (L : Set H)), IsCyclic ↥S) {t : H}
    (htC : t ∈ centralizer (L : Set H)) (ht2 : orderOf t = 2) (htN : t ∉ N) : OddCN N L := by
  have hS2 := card_sylow_eq_two_of_not_mem hidx hcyc htC ht2 htN
  obtain ⟨K₀, hK₀C, hK₀odd, htK, hmul, -⟩ := exists_K₀ hS2 htC ht2
  intro c hc hcN
  by_cases hcK : c ∈ K₀
  · exact hK₀odd c hcK
  · exfalso
    have h1 : c * t ∈ K₀ := (hmul c hc t htC).2 (iff_of_false hcK htK)
    have h2 : c * t ∈ N := mem_of_odd_orderOf hidx (hK₀odd _ h1)
    apply htN
    have : t = c⁻¹ * (c * t) := by group
    rw [this]
    exact N.mul_mem (N.inv_mem hcN) h2

theorem two_mem_of_oddCN {N L : Subgroup H} (hLN : L ≤ N) (hodd : OddCN N L) {b : H}
    (hbN : b ∈ N) (hbM : b ∈ L ⊔ centralizer (L : Set H)) {j : ℕ} (hj : orderOf b = 2 ^ j) :
    b ∈ L := by
  obtain ⟨ℓ, hℓ, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer (le_refl _) hbM
  have hcN : c ∈ N := by
    have : c = ℓ⁻¹ * (ℓ * c) := by group
    rw [this]
    exact N.mul_mem (N.inv_mem (hLN hℓ)) hbN
  have hk := hodd c hc hcN
  have hcomm : Commute ℓ c := mem_centralizer_iff.1 hc ℓ hℓ
  have hbn : (ℓ * c) ^ orderOf c = ℓ ^ orderOf c := by
    rw [hcomm.mul_pow, pow_orderOf_eq_one, mul_one]
  have hgcd : (orderOf c).gcd (orderOf (ℓ * c)) = 1 := by
    rw [hj]
    exact (Nat.coprime_two_right.2 hk).pow_right j
  have hmem : ℓ * c ∈ zpowers ((ℓ * c) ^ orderOf c) := mem_zpowers_pow_iff.2 hgcd
  have hL : (ℓ * c) ^ orderOf c ∈ L := by
    rw [hbn]
    exact pow_mem hℓ _
  exact (zpowers_le.2 hL) hmem

theorem perfect_le_of_oddCN [Finite H] {N L : Subgroup H} (hLN : L ≤ N) (hodd : OddCN N L)
    {P : Subgroup H} (hPN : P ≤ N) (hPM : P ≤ L ⊔ centralizer (L : Set H))
    [hP : Group.IsPerfect ↥P] : P ≤ L := by
  classical
  set D : Subgroup H := centralizer (L : Set H) ⊓ N with hDdef
  have hDC : D ≤ centralizer (L : Set H) := inf_le_left
  have hDodd : Odd (Nat.card D) := by
    by_contra hne
    have h2 : 2 ∣ Nat.card D := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hne)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥D) 2 h2
    have hx2 : orderOf (x : H) = 2 := by rw [Subgroup.orderOf_coe, hx]
    have := hodd x x.2.1 x.2.2
    rw [hx2] at this
    exact absurd this (by decide)
  have hDsolv : Group.IsSolvable ↥D := CFSG.Milestones.odd_order_solvable hDodd
  set Mx : Subgroup H := L ⊔ D with hMx
  have hPMx : P ≤ Mx := by
    intro b hb
    obtain ⟨ℓ, hℓ, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer (le_refl _) (hPM hb)
    have hcN : c ∈ N := by
      have : c = ℓ⁻¹ * (ℓ * c) := by group
      rw [this]
      exact N.mul_mem (N.inv_mem (hLN hℓ)) (hPN hb)
    exact mul_mem_sup hℓ (show c ∈ D from ⟨hc, hcN⟩)
  have hDMx : D ≤ Mx := le_sup_right
  have hLMx : L ≤ Mx := le_sup_left
  have hLn : (L.subgroupOf Mx).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hLMx]
    exact sup_le Subgroup.le_normalizer (hDC.trans (Subgroup.centralizer_le_normalizer _))
  have hsurj : Function.Surjective
      ((QuotientGroup.mk' (L.subgroupOf Mx)).comp (Subgroup.inclusion hDMx)) := by
    intro q
    obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨ℓ, hℓ, c, hc, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hDC hm
    refine ⟨⟨c, hc⟩, ?_⟩
    simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    show c⁻¹ * (ℓ * c) ∈ L
    have : c⁻¹ * (ℓ * c) = ℓ := by
      have hcomm : ℓ * c = c * ℓ := mem_centralizer_iff.1 (hDC hc) ℓ hℓ
      rw [hcomm]; group
    rw [this]
    exact hℓ
  have : Group.IsSolvable ↥D := hDsolv
  have hQs : Group.IsSolvable (↥Mx ⧸ L.subgroupOf Mx) := Group.isSolvable_of_surjective hsurj
  have : Group.IsPerfect ↥(P.subgroupOf Mx) := isPerfect_subgroupOf hPMx
  set π := QuotientGroup.mk' (L.subgroupOf Mx) with hπ
  have hbot : (P.subgroupOf Mx).map π = ⊥ := by
    by_contra hne
    have : Nontrivial ↥((P.subgroupOf Mx).map π) := (Subgroup.nontrivial_iff_ne_bot _).2 hne
    have : Group.IsPerfect ↥((P.subgroupOf Mx).map π) := Group.IsPerfect.map π
    exact Group.IsPerfect.not_isSolvable ↥((P.subgroupOf Mx).map π) inferInstance
  intro b hb
  have hb' : (⟨b, hPMx hb⟩ : ↥Mx) ∈ P.subgroupOf Mx := hb
  have hmem : π ⟨b, hPMx hb⟩ ∈ (P.subgroupOf Mx).map π := ⟨_, hb', rfl⟩
  rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact hmem

end CFSG.EvenSporadicStandard.Induction.TMem
