module

public import CFSG.GroupTheory.ABGQGroups.Defs
public import CFSG.CharacterTheory.Semidihedral.Local.LocalNormalizerQuotientsSupport

public section

namespace CFSG.QuasiDihedralFusion

open CFSG.ABGQGroups

universe u v w

section Involves

@[expose] def Involves (G : Type u) [Group G] (T : Type v) [Group T] : Prop :=
  ∃ (U : Subgroup G) (φ : U →* T), Function.Surjective φ

variable {G : Type u} [Group G] {T : Type v} [Group T]

theorem involves_of_surjective (φ : G →* T) (hφ : Function.Surjective φ) : Involves G T :=
  ⟨⊤, φ.comp (⊤ : Subgroup G).subtype, fun t => by
    obtain ⟨g, rfl⟩ := hφ t
    exact ⟨⟨g, Subgroup.mem_top g⟩, rfl⟩⟩

theorem Involves.of_injective {B : Type w} [Group B] (f : G →* B) (hf : Function.Injective f)
    (h : Involves G T) : Involves B T := by
  obtain ⟨U, φ, hφ⟩ := h
  let e : U ≃* U.map f := U.equivMapOfInjective f hf
  exact ⟨U.map f, φ.comp e.symm.toMonoidHom, hφ.comp e.symm.surjective⟩

end Involves

section OddElements

variable {G : Type u} [Group G]

theorem mem_of_odd_orderOf_of_isPGroup_quotient (K : Subgroup G) [K.Normal]
    (hK : IsPGroup 2 (G ⧸ K)) {g : G} (hg : Odd (orderOf g)) : g ∈ K := by
  obtain ⟨k, hk⟩ := hK (g : G ⧸ K)
  have h1 : orderOf (g : G ⧸ K) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (g : G ⧸ K) ∣ orderOf g := orderOf_map_dvd (QuotientGroup.mk' K) g
  have h3 : orderOf (g : G ⧸ K) = 1 := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    rcases j with _ | j
    · simpa using hj
    · exfalso
      rw [hj] at h2
      exact (Nat.not_even_iff_odd.mpr hg)
        (even_iff_two_dvd.mpr ((dvd_pow_self 2 (Nat.succ_ne_zero j)).trans h2))
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem mem_of_odd_orderOf_of_two_pow_index [Finite G] (K : Subgroup G) [K.Normal]
    (hK : ∃ k : ℕ, K.index = 2 ^ k) {g : G} (hg : Odd (orderOf g)) : g ∈ K := by
  obtain ⟨k, hk⟩ := hK
  exact mem_of_odd_orderOf_of_isPGroup_quotient K
    (IsPGroup.of_card (n := k) (by rw [← Subgroup.index_eq_card, hk])) hg

theorem mem_zpowers_pow_of_odd {z : G} (hz : ∃ k : ℕ, orderOf z = 2 ^ k) {m : ℕ} (hm : Odd m) :
    z ∈ Subgroup.zpowers (z ^ m) := by
  obtain ⟨k, hk⟩ := hz
  rw [mem_zpowers_pow_iff, hk]
  exact Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hm)

end OddElements

section CentralQuotient

variable {K : Type u} [Group K] [Finite K]

theorem oddCore_quotient_eq_bot_of_le_center (hO : CFSG.oddCore K = ⊥) (Z : Subgroup K)
    [Z.Normal] (hZ : Z ≤ Subgroup.center K) (hZ2 : IsPGroup 2 Z) :
    CFSG.oddCore (K ⧸ Z) = ⊥ := by
  set O := CFSG.oddCore (K ⧸ Z) with hOdef
  set N : Subgroup K := O.comap (QuotientGroup.mk' Z) with hNdef
  have hON : O.Normal := inferInstance
  have hNn : N.Normal := hON.comap _
  have hZN : Z ≤ N := by
    intro z hz
    change (QuotientGroup.mk' Z z) ∈ O
    rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff z).mpr hz]
    exact O.one_mem
  have hOodd : Odd (Nat.card O) := CFSG.Semidihedral.Local.odd_card_oddCore (K ⧸ Z)
  set Z' : Subgroup N := Z.subgroupOf N with hZ'def
  let ρ : N →* O := (QuotientGroup.mk' Z).subgroupComap O
  have hρ : Function.Surjective ρ :=
    (QuotientGroup.mk' Z).subgroupComap_surjective O (QuotientGroup.mk'_surjective Z)
  have hρker : ρ.ker = Z' := by
    ext n
    rw [MonoidHom.mem_ker, hZ'def, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      have h1 : ((QuotientGroup.mk' Z) (n : K) : K ⧸ Z) = 1 := congrArg Subtype.val h
      exact (QuotientGroup.eq_one_iff _).mp h1
    · intro h
      exact Subtype.ext ((QuotientGroup.eq_one_iff _).mpr h)
  have hidx : Z'.index = Nat.card O := by
    rw [Subgroup.index_eq_card, ← hρker]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective ρ hρ).toEquiv
  have hZ'2 : IsPGroup 2 Z' := by
    have e : Z' ≃* Z := Subgroup.subgroupOfEquivOfLe hZN
    exact hZ2.of_equiv e.symm
  have hcop : Nat.Coprime (Nat.card Z') Z'.index := by
    obtain ⟨k, hk⟩ := hZ'2.exists_card_eq
    rw [hk, hidx]
    exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hOodd)
  obtain ⟨Q, hQ⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hQodd : Odd (Nat.card Q) := by
    rw [← hQ.symm.index_eq_card, hidx]
    exact hOodd
  have hcen : ∀ a : N, a ∈ Z' → ∀ b : N, a * b = b * a := by
    intro a ha b
    apply Subtype.ext
    exact (Subgroup.mem_center_iff.mp (hZ ha) (b : K)).symm
  have hoddQ : ∀ n : N, Odd (orderOf n) → n ∈ Q := by
    intro n hn
    have hmem : n ∈ ((Z' ⊔ Q : Subgroup N) : Set N) := by
      rw [hQ.sup_eq_top]
      exact Subgroup.mem_top n
    rw [Subgroup.normal_mul] at hmem
    obtain ⟨z, hz, q, hq, rfl⟩ := hmem
    dsimp only at hn ⊢
    have hzq : Commute z q := hcen z hz q
    have hpow : z ^ orderOf (z * q) * q ^ orderOf (z * q) = 1 := by
      rw [← hzq.mul_pow, pow_orderOf_eq_one]
    have hzm : z ^ orderOf (z * q) ∈ Z' ⊓ Q := by
      refine ⟨Z'.pow_mem hz _, ?_⟩
      have : z ^ orderOf (z * q) = (q ^ orderOf (z * q))⁻¹ := eq_inv_of_mul_eq_one_left hpow
      rw [this]
      exact Q.inv_mem (Q.pow_mem hq _)
    rw [hQ.disjoint.eq_bot, Subgroup.mem_bot] at hzm
    have hz2 : ∃ k : ℕ, orderOf z = 2 ^ k := by
      obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hZ'2) ⟨z, hz⟩
      exact ⟨k, (Subgroup.orderOf_coe (⟨z, hz⟩ : Z')).trans hk⟩
    have hz1 : z = 1 := by
      have h := mem_zpowers_pow_of_odd hz2 hn
      rw [hzm, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at h
      exact h
    rw [hz1, one_mul]
    exact hq
  set Q' : Subgroup K := Q.map N.subtype with hQ'def
  have hQ'odd : Odd (Nat.card Q') := by
    rw [hQ'def, Subgroup.card_map_of_injective N.subtype_injective]
    exact hQodd
  have hQ'n : Q'.Normal := by
    refine ⟨fun x hx g => ?_⟩
    obtain ⟨q, hq, rfl⟩ := hx
    have hgN : g * (q : K) * g⁻¹ ∈ N := hNn.conj_mem _ q.property g
    let n : N := ⟨g * (q : K) * g⁻¹, hgN⟩
    have hnodd : Odd (orderOf n) := by
      have h1 : orderOf n = orderOf (g * (q : K) * g⁻¹) := Subgroup.orderOf_mk _ _
      have h2 : orderOf (g * (q : K) * g⁻¹) = orderOf (q : K) := by
        rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      have h3 : orderOf (q : K) = orderOf (⟨q, hq⟩ : Q) :=
        (Subgroup.orderOf_coe q).trans (Subgroup.orderOf_coe (⟨q, hq⟩ : Q))
      rw [h1, h2, h3]
      exact Odd.of_dvd_nat hQodd (orderOf_dvd_natCard _)
    exact ⟨n, hoddQ n hnodd, rfl⟩
  have hQ'bot : Q' = ⊥ := le_bot_iff.mp (hO ▸ CFSG.Semidihedral.Local.le_oddCore hQ'n hQ'odd)
  have hQbot : Nat.card Q = 1 := by
    rw [← Subgroup.card_map_of_injective N.subtype_injective, ← hQ'def, hQ'bot,
      Subgroup.card_bot]
  have hO1 : Nat.card O = 1 := by
    rw [← hidx, hQ.symm.index_eq_card, hQbot]
  exact (Subgroup.eq_bot_iff_card O).mpr hO1

end CentralQuotient

end CFSG.QuasiDihedralFusion
