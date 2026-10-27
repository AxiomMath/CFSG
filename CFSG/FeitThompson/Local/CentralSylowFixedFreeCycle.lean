module

import CFSG.FeitThompson.Local.OutsideNormalizedLineFixedTrivial
import CFSG.FeitThompson.Foundations.FullExponentCyclicLiftLayer
public import CFSG.FeitThompson.Definitions.ElementaryAbelianPRank
public import CFSG.FeitThompson.Local.ClassTwoPrimeTorsionCharacteristic
import CFSG.FeitThompson.Foundations.SylowExponentPrimePart

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup

variable {G : Type*} [Group G] {p : ℕ}

theorem le_map_center_iff_le_inf_centralizer {U S : Subgroup G} :
    S ≤ (Subgroup.center ↥U).map U.subtype ↔ S ≤ U ⊓ centralizer (U : Set G) := by
  constructor
  · intro h
    refine le_inf (fun x hx => ?_) (fun x hx => ?_)
    · obtain ⟨y, -, rfl⟩ := h hx
      exact y.2
    · obtain ⟨y, hy, rfl⟩ := h hx
      exact mem_centralizer_iff.2 fun g hg =>
        congrArg (Subgroup.subtype U) ((Subgroup.mem_center_iff.1 hy) ⟨g, hg⟩)
  · rintro h x hx
    obtain ⟨hxU, hxC⟩ := h hx
    exact ⟨⟨x, hxU⟩, Subgroup.mem_center_iff.2 fun g =>
      Subtype.ext (mem_centralizer_iff.1 hxC (g : G) g.2), rfl⟩

theorem normal_subgroupOf_of_le_centralizer {U Z : Subgroup G}
    (h : Z ≤ centralizer (U : Set G)) : (Z.subgroupOf U).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_subgroupOf] at hx ⊢
  have hc := mem_centralizer_iff.1 (h hx) (g : G) g.2
  push_cast
  rw [hc]
  simpa using hx

theorem normalizer_le_normalizer_map_subtype (S : Subgroup G) (T : Subgroup ↥S)
    [T.Characteristic] :
    normalizer (S : Set G) ≤ normalizer ((T.map S.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg x hx
  obtain ⟨y, hy, rfl⟩ := hx
  refine ⟨S.normalizerMonoidHom ⟨g, hg⟩ y, ?_, ?_⟩
  · rw [← Subgroup.characteristic_iff_map_eq.1 ‹T.Characteristic›
      (S.normalizerMonoidHom ⟨g, hg⟩)]
    exact ⟨y, hy, rfl⟩
  · simp [Subgroup.normalizerMonoidHom_apply_apply_coe S ⟨g, hg⟩ y]

theorem coe_inf_omega1_map_eq {A : Type*} [CommGroup A] (f : A →* G) (hf : Function.Injective f)
    {K B : Subgroup A} {K' B' : Subgroup G} (hK : K.map f = K') (hB : B.map f = B')
    (h : K ⊓ omega1 p A = B) : {x ∈ (K' : Set G) | x ^ p = 1} = (B' : Set G) := by
  subst h hK hB
  ext x
  constructor
  · rintro ⟨⟨y, hyK, rfl⟩, hx⟩
    exact ⟨y, ⟨hyK, mem_omega1_iff_pow_eq_one.2 (hf (by rw [map_pow, hx, map_one]))⟩, rfl⟩
  · rintro ⟨y, ⟨hyK, hyp⟩, rfl⟩
    exact ⟨⟨y, hyK, rfl⟩, by rw [← map_pow, mem_omega1_iff_pow_eq_one.1 hyp, map_one]⟩

theorem exists_cyclic_normal_of_omega1_eq (hp : p.Prime) {U H S B : Subgroup G}
    (hSp : IsPGroup p ↥S) (hSC : S ≤ centralizer (U : Set G))
    {z : G} (hzS : z ∈ S) (hexp : orderOf z = Monoid.exponent ↥S)
    (hOmega : {x ∈ (zpowers z : Set G) | x ^ p = 1} = (B : Set G))
    (hCB : H ⊓ centralizer (B : Set G) = ⊥) (hB : Nat.card ↥B = p) :
    ∃ Z : Subgroup G, Z ≤ S ∧ IsCyclic ↥Z ∧ (Z.subgroupOf U).Normal ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥S ∧
      ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ := by
  have hZS : zpowers z ≤ S := zpowers_le.2 hzS
  refine ⟨zpowers z, hZS, inferInstance, normal_subgroupOf_of_le_centralizer (hZS.trans hSC),
    ?_, fun w hw hw1 => ?_⟩
  · rw [IsCyclic.exponent_eq_card, Nat.card_zpowers, hexp]
  · exact inf_centralizer_singleton_eq_bot_of_inf_centralizer_eq_bot hp hSp hZS hB hOmega hCB hw hw1

theorem exists_cyclic_normal_exponent_eq [Finite G] (hp : p.Prime) {M H U S B₀ : Subgroup G}
    (hSZ : S ≤ (Subgroup.center ↥U).map U.subtype)
    (hSnt : S ≠ ⊥) (hSp : IsPGroup p ↥S) (h3 : 3 ∉ elementaryAbelianRanks p ↥S)
    (hNS : ¬ normalizer (S : Set G) ≤ M)
    (hreg : ∀ B : Subgroup G, B ≤ S → Nat.card ↥B = p →
      H ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M)
    (hB₀ : B₀ ≤ S) (hB₀card : Nat.card ↥B₀ = p)
    (hB₀C : H ⊓ centralizer (B₀ : Set G) = ⊥) :
    ∃ Z : Subgroup G, Z ≤ S ∧ IsCyclic ↥Z ∧ (Z.subgroupOf U).Normal ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥S ∧
      ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hSU : S ≤ U := le_trans (le_map_center_iff_le_inf_centralizer.1 hSZ) inf_le_left
  have hSC : S ≤ centralizer (U : Set G) :=
    le_trans (le_map_center_iff_le_inf_centralizer.1 hSZ) inf_le_right
  let _ : CommGroup ↥S :=
    { S.toGroup with
      mul_comm := fun a b => Subtype.ext ((mem_centralizer_iff.1 (hSC b.2)) a (hSU a.2)) }
  have hnt : Nontrivial ↥S := (Subgroup.nontrivial_iff_ne_bot S).2 hSnt
  obtain ⟨n, hn⟩ := hSp.exists_exponent_eq_pow
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exfalso
      rw [pow_zero] at hn
      obtain ⟨a, b, hab⟩ := hnt.exists_pair_ne
      have ha : a ^ Monoid.exponent ↥S = 1 := Monoid.pow_exponent_eq_one a
      have hb : b ^ Monoid.exponent ↥S = 1 := Monoid.pow_exponent_eq_one b
      rw [hn, pow_one] at ha hb
      exact hab (ha.trans hb.symm)
    · exact h
  rcases lt_or_eq_of_le
    (characteristic_nontrivial_range_powMonoidHom_le_omega1 hp hSp hn1 hn).2.2 with hlt | heq
  ·
    obtain ⟨hcard, hzw⟩ := card_eq_and_inf_omega1_zpowers_eq_of_lt hp hSp h3 hn1 hn hlt
    obtain ⟨w, hw⟩ := IsPGroup.exists_orderOf_eq_exponent hp hSp
    have hBS : ((powMonoidHom (p ^ (n - 1)) : ↥S →* ↥S).range).map S.subtype ≤ S :=
      Subgroup.map_subtype_le _
    have hBcard :
        Nat.card ↥(((powMonoidHom (p ^ (n - 1)) : ↥S →* ↥S).range).map S.subtype) = p := by
      rw [Subgroup.card_map_of_injective S.subtype_injective, hcard]
    have hCB := inf_centralizer_eq_bot_of_normalizer_not_le (H := H) hNS
      (normalizer_le_normalizer_map_subtype S _) (hreg _ hBS hBcard)
    exact exists_cyclic_normal_of_omega1_eq hp hSp hSC w.2
      (by rw [Subgroup.orderOf_coe, hw])
      (coe_inf_omega1_map_eq S.subtype S.subtype_injective
        (MonoidHom.map_zpowers S.subtype w) rfl (hzw w hw)) hCB hBcard
  ·
    have hB₀card' : Nat.card ↥(B₀.subgroupOf S) = p := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB₀).toEquiv, hB₀card]
    obtain ⟨z, hzexp, hzeq⟩ := exists_orderOf_eq_exponent_inf_omega1_zpowers_eq_of_eq hp hn1 hn
      heq (le_omega1_of_card_eq_prime hB₀card') hB₀card'
    exact exists_cyclic_normal_of_omega1_eq hp hSp hSC z.2
      (by rw [Subgroup.orderOf_coe, hzexp])
      (coe_inf_omega1_map_eq S.subtype S.subtype_injective (MonoidHom.map_zpowers S.subtype z)
        (by rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hB₀]) hzeq) hB₀C hB₀card

theorem exists_cyclic_normal_exponent_eq' [Finite G] (hp : p.Prime) {M H U S B₀ : Subgroup G}
    (hSZ : S ≤ U ⊓ centralizer (U : Set G))
    (hSnt : S ≠ ⊥) (hSp : IsPGroup p ↥S) (h3 : 3 ∉ elementaryAbelianRanks p ↥S)
    (hNS : ¬ normalizer (S : Set G) ≤ M)
    (hreg : ∀ B : Subgroup G, B ≤ S → Nat.card ↥B = p →
      H ⊓ centralizer (B : Set G) ≠ ⊥ → normalizer (B : Set G) ≤ M)
    (hB₀ : B₀ ≤ S) (hB₀card : Nat.card ↥B₀ = p)
    (hB₀C : H ⊓ centralizer (B₀ : Set G) = ⊥) :
    ∃ Z : Subgroup G, Z ≤ S ∧ IsCyclic ↥Z ∧ (Z.subgroupOf U).Normal ∧
      Monoid.exponent ↥Z = Monoid.exponent ↥S ∧
      ∀ z ∈ Z, z ≠ 1 → H ⊓ centralizer ({z} : Set G) = ⊥ :=
  exists_cyclic_normal_exponent_eq hp (le_map_center_iff_le_inf_centralizer.2 hSZ) hSnt hSp h3
    hNS hreg hB₀ hB₀card hB₀C

end CFSG.FeitThompson
