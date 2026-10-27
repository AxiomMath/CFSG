module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.InnerPsi
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.HSTwoBAut
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.AutA6Sylow3

public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus

open Subgroup CFSG.Open CFSG.Blueprint.NativeSporadic Wreath

def x0A6 : alternatingGroup (Fin 6) :=
  ⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

def zeta0A6 : alternatingGroup (Fin 6) :=
  ⟨(Equiv.swap 0 3 * Equiv.swap 3 1 * Equiv.swap 1 4) * Equiv.swap 2 5, by
    rw [Equiv.Perm.mem_alternatingGroup]; decide +kernel⟩

theorem x0_order : orderOf x0A6 = 3 := by
  refine orderOf_eq_prime ?_ ?_ <;> decide +kernel

theorem zeta0_sq_ne : zeta0A6 ^ 2 ≠ 1 := by decide +kernel

theorem zeta0_pow4 : zeta0A6 ^ 4 = 1 := by decide +kernel

theorem zeta0_normalizes : ∀ a : alternatingGroup (Fin 6),
    (a * x0A6 = x0A6 * a ↔ (zeta0A6 * a * zeta0A6⁻¹) * x0A6 = x0A6 * (zeta0A6 * a * zeta0A6⁻¹)) := by
  decide +kernel

theorem exists_zeta_normalizes {x : alternatingGroup (Fin 6)} (hx : orderOf x = 3) :
    ∃ z : alternatingGroup (Fin 6), z ^ 2 ≠ 1 ∧ z ^ 4 = 1 ∧ ∀ a : alternatingGroup (Fin 6),
      (a * x = x * a ↔ (z * a * z⁻¹) * x = x * (z * a * z⁻¹)) := by
  obtain ⟨α, hα⟩ := exists_mulAut_apply_eq_of_orderOf_eq_three x0_order hx
  refine ⟨α zeta0A6, ?_, ?_, fun a => ?_⟩
  · intro h
    apply zeta0_sq_ne
    apply α.injective
    rw [map_pow, h, map_one]
  · rw [← map_pow, zeta0_pow4, map_one]
  · obtain ⟨b, rfl⟩ := α.surjective a
    have h1 : α b * x = x * α b ↔ b * x0A6 = x0A6 * b := by
      rw [← hα, ← map_mul, ← map_mul, α.injective.eq_iff]
    have h2 : (α zeta0A6 * α b * (α zeta0A6)⁻¹) * x = x * (α zeta0A6 * α b * (α zeta0A6)⁻¹) ↔
        (zeta0A6 * b * zeta0A6⁻¹) * x0A6 = x0A6 * (zeta0A6 * b * zeta0A6⁻¹) := by
      rw [← hα, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, α.injective.eq_iff]
    rw [h1, h2]
    exact zeta0_normalizes b

theorem mem_innR_of_pow_eq_one_of_odd {B : MulAut (alternatingGroup (Fin 6))} {n : ℕ}
    (hn : Odd n) (hB : B ^ n = 1) : B ∈ innR := by
  have : innR.Normal := ⟨fun a ⟨b, hb⟩ g => ⟨g b, by
    rw [← hb]
    exact (conj_thetaEquiv_apply g b).symm⟩⟩
  have h4 : (QuotientGroup.mk B : MulAut (alternatingGroup (Fin 6)) ⧸ innR) ^ 4 = 1 := by
    have := pow_card_eq_one' (G := MulAut (alternatingGroup (Fin 6)) ⧸ innR)
      (x := QuotientGroup.mk B)
    rwa [← Subgroup.index_eq_card, CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6] at this
  have hq : (QuotientGroup.mk B : MulAut (alternatingGroup (Fin 6)) ⧸ innR) ^ n = 1 := by
    rw [← QuotientGroup.mk_pow, hB, QuotientGroup.mk_one]
  have h1 := pow_gcd_eq_one.2 ⟨hq, h4⟩
  have hg : Nat.gcd n 4 = 1 := Nat.Coprime.pow_right 2 hn.coprime_two_right
  rw [hg, pow_one] at h1
  exact (QuotientGroup.eq_one_iff B).1 h1

section General

variable {G : Type*} [Group G]

theorem commutator_eq_self_of_equiv_alt6 (H : Subgroup G) (e : ↥H ≃* alternatingGroup (Fin 6)) :
    ⁅H, H⁆ = H := by
  have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    ⟨commutator_alternatingGroup_eq_top (by simp)⟩
  have : Group.IsPerfect ↥H :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have h1 := Subgroup.map_commutator (⊤ : Subgroup ↥H) ⊤ H.subtype
  have h2 : (⁅(⊤ : Subgroup ↥H), ⊤⁆ : Subgroup ↥H) = ⊤ := Group.IsPerfect.commutator_eq_top
  rw [h2] at h1
  have h3 : Subgroup.map H.subtype (⊤ : Subgroup ↥H) = H := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [h3] at h1
  exact h1.symm

theorem commutator_le_self' (J : Subgroup G) : ⁅J, J⁆ ≤ J :=
  Subgroup.commutator_le.2 fun a ha b hb => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem mem_normalizer_centralizer {S : Subgroup G} {ζ : G}
    (h : ∀ g, g ∈ S ↔ ζ * g * ζ⁻¹ ∈ S) :
    ζ ∈ normalizer ((centralizer (S : Set G) : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro g
  have key : ∀ g, g ∈ centralizer (S : Set G) → ζ * g * ζ⁻¹ ∈ centralizer (S : Set G) := by
    intro g hg
    refine mem_centralizer_iff.2 fun s hs => ?_
    have hs' : ζ⁻¹ * s * ζ ∈ S := by
      have := (h (ζ⁻¹ * s * ζ)).1
      refine (h (ζ⁻¹ * s * ζ)).2 ?_
      have e : ζ * (ζ⁻¹ * s * ζ) * ζ⁻¹ = s := by group
      rw [e]
      exact hs
    have h1 := mem_centralizer_iff.1 hg _ hs'
    calc s * (ζ * g * ζ⁻¹) = ζ * ((ζ⁻¹ * s * ζ) * g) * ζ⁻¹ := by group
      _ = ζ * (g * (ζ⁻¹ * s * ζ)) * ζ⁻¹ := by rw [h1]
      _ = ζ * g * ζ⁻¹ * s := by group
  refine ⟨key g, fun hg => ?_⟩
  refine mem_centralizer_iff.2 fun s hs => ?_
  have hs' : ζ * s * ζ⁻¹ ∈ S := (h s).1 hs
  have h1 := mem_centralizer_iff.1 hg _ hs'
  have h2 : (ζ * s * ζ⁻¹) * (ζ * g * ζ⁻¹) = (ζ * g * ζ⁻¹) * (ζ * s * ζ⁻¹) := h1
  calc s * g = ζ⁻¹ * ((ζ * s * ζ⁻¹) * (ζ * g * ζ⁻¹)) * ζ := by group
    _ = ζ⁻¹ * ((ζ * g * ζ⁻¹) * (ζ * s * ζ⁻¹)) * ζ := by rw [h2]
    _ = g * s := by group

theorem mem_normalizer_commutator {J : Subgroup G} {ζ : G}
    (h : ζ ∈ normalizer (J : Set G)) : ζ ∈ normalizer ((⁅J, J⁆ : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_map_eq] at h ⊢
  rw [Subgroup.map_commutator, h]

theorem zpowers_cases {x : G} (hx : orderOf x = 2) : ∀ y ∈ zpowers x, y = 1 ∨ y = x := by
  intro y hy
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
  rw [← zpow_mod_orderOf, hx]
  rcases Int.emod_two_eq_zero_or_one n with h | h <;> simp [h]

theorem two_le_pRank_of_commuting_involutions [Finite G] {K : Subgroup G} {a b : G}
    (ha : a ∈ K) (hb : b ∈ K) (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (ha2 : a * a = 1)
    (hb2 : b * b = 1) (hc : a * b = b * a) : 2 ≤ CFSG.Open.pRank 2 K := by
  have hao : orderOf a = 2 := orderOf_eq_prime (by rwa [pow_two]) ha1
  have hbo : orderOf b = 2 := orderOf_eq_prime (by rwa [pow_two]) hb1
  have hz : ∀ (x : G), orderOf x = 2 → ∀ y ∈ zpowers x, y = 1 ∨ y = x :=
    fun _ hx => zpowers_cases hx
  have hdisj : Disjoint (zpowers a) (zpowers b) := by
    rw [Subgroup.disjoint_def]
    intro y hya hyb
    rcases hz a hao y hya with h | h
    · exact h
    · rcases hz b hbo y hyb with h' | h'
      · exact h'
      · exact absurd (h.symm.trans h') hab
  have hcent : zpowers b ≤ centralizer (zpowers a : Set G) := by
    rw [zpowers_le]
    refine mem_centralizer_iff.2 fun y hy => ?_
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hy
    exact ((Commute.zpow_left (show Commute a b from hc) n)).eq
  have hcard : Nat.card ↥(zpowers a ⊔ zpowers b) = 2 ^ 2 := by
    rw [← Nat.card_congr (mulEquivProdSup hcent hdisj).toEquiv, Nat.card_prod, Nat.card_zpowers,
      Nat.card_zpowers, hao, hbo]
    norm_num
  have hcomm : ∀ p ∈ zpowers a, ∀ q ∈ zpowers b, Commute p q := by
    intro p hp q hq
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hq
    exact Commute.zpow_zpow (show Commute a b from hc) i j
  have hAA : ∀ p ∈ zpowers a, ∀ p' ∈ zpowers a, Commute p p' := by
    intro p hp p' hp'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hp'
    exact Commute.zpow_zpow (Commute.refl a) i j
  have hBB : ∀ p ∈ zpowers b, ∀ p' ∈ zpowers b, Commute p p' := by
    intro p hp p' hp'
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hp
    obtain ⟨j, rfl⟩ := mem_zpowers_iff.1 hp'
    exact Commute.zpow_zpow (Commute.refl b) i j
  have hEab : IsElemAbelian 2 (zpowers a ⊔ zpowers b) := by
    refine ⟨isMulCommutative_iff_of_setLike.2 fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcent hx
      obtain ⟨p', hp', q', hq', rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcent hy
      have h1 : Commute (p * q) (p' * q') :=
        ((hAA p hp p' hp').mul_right (hcomm p hp q' hq')).mul_left
          ((hcomm p' hp' q hq).symm.mul_right (hBB q hq q' hq'))
      exact h1.eq
    · obtain ⟨p, hp, q, hq, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hcent hx
      have hp2 : p * p = 1 := by
        rcases hz a hao p hp with h | h <;> simp [h, ha2]
      have hq2 : q * q = 1 := by
        rcases hz b hbo q hq with h | h <;> simp [h, hb2]
      rw [(hcomm p hp q hq).mul_pow, pow_two, pow_two, hp2, hq2, one_mul]
  have hEK : zpowers a ⊔ zpowers b ≤ K := sup_le (zpowers_le.2 ha) (zpowers_le.2 hb)
  unfold CFSG.Open.pRank
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨zpowers a ⊔ zpowers b, hEK, hEab, hcard⟩
  rintro k ⟨B, -, -, hk⟩
  have h1 : k < 2 ^ k := Nat.lt_two_pow_self
  have h2 : Nat.card B ≤ Nat.card G := Subgroup.card_le_card_group B
  change k ≤ Nat.card G
  omega

end General

section Config

set_option linter.unusedSectionVars false

variable
  {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G}

namespace InnerD8Config

variable (c : InnerD8Config L t)

abbrev Zs : Subgroup G := (c.L₁ ⊓ centralizer ({c.x} : Set G)) ⊔ zpowers c.u₁

abbrev Js : Subgroup G := centralizer (c.Zs : Set G)

theorem X3_le_Zs : c.X3 ≤ c.Zs := le_sup_left

theorem u₁_mem_Zs : c.u₁ ∈ c.Zs := mem_sup_right (mem_zpowers _)

theorem comm_X3_u₁ {a : G} (ha : a ∈ c.X3) : a * c.u₁ = c.u₁ * a := c.u₁_comm_L₁ ha.1

theorem zpowers_u₁_le_centralizer_X3 : zpowers c.u₁ ≤ centralizer (c.X3 : Set G) := by
  rw [zpowers_le]
  exact mem_centralizer_iff.2 fun a ha => c.comm_X3_u₁ ha

theorem mem_centralizer_x_iff (k : ↥c.L₁) : (k : G) ∈ centralizer ({c.x} : Set G) ↔
    c.eL₁ k * c.eL₁ ⟨c.x, c.x_mem⟩ = c.eL₁ ⟨c.x, c.x_mem⟩ * c.eL₁ k := by
  rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, c.eL₁.injective.eq_iff]
  exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩

theorem zeta_X3_iff {z : alternatingGroup (Fin 6)}
    (hz : ∀ a : alternatingGroup (Fin 6), (a * c.eL₁ ⟨c.x, c.x_mem⟩ = c.eL₁ ⟨c.x, c.x_mem⟩ * a ↔
      (z * a * z⁻¹) * c.eL₁ ⟨c.x, c.x_mem⟩ = c.eL₁ ⟨c.x, c.x_mem⟩ * (z * a * z⁻¹)))
    (g : G) : g ∈ c.X3 ↔
      ((c.eL₁.symm z : ↥c.L₁) : G) * g * ((c.eL₁.symm z : ↥c.L₁) : G)⁻¹ ∈ c.X3 := by
  set ζ' : ↥c.L₁ := c.eL₁.symm z with hζ'
  set ζ : G := (ζ' : G) with hζ
  have hζL : ζ ∈ c.L₁ := ζ'.2
  have hL : g ∈ c.L₁ ↔ ζ * g * ζ⁻¹ ∈ c.L₁ := by
    refine ⟨fun hg => mul_mem (mul_mem hζL hg) (inv_mem hζL), fun h => ?_⟩
    have := mul_mem (mul_mem (inv_mem hζL) h) hζL
    have e : ζ⁻¹ * (ζ * g * ζ⁻¹) * ζ = g := by group
    rwa [e] at this
  have hkk : ∀ k k2 : ↥c.L₁, (k2 : G) = ζ * k * ζ⁻¹ →
      ((k : G) ∈ centralizer ({c.x} : Set G) ↔ (k2 : G) ∈ centralizer ({c.x} : Set G)) := by
    intro k k2 h
    rw [c.mem_centralizer_x_iff, c.mem_centralizer_x_iff]
    have h' : k2 = ζ' * k * ζ'⁻¹ := Subtype.ext h
    rw [h', map_mul, map_mul, map_inv, hζ', MulEquiv.apply_symm_apply]
    exact hz _
  constructor
  · rintro ⟨hg1, hg2⟩
    have hg1' := hL.1 hg1
    refine ⟨hg1', ?_⟩
    exact (hkk ⟨g, hg1⟩ ⟨ζ * g * ζ⁻¹, hg1'⟩ rfl).1 hg2
  · rintro ⟨hg1', hg2'⟩
    have hg1 := hL.2 hg1'
    refine ⟨hg1, ?_⟩
    exact (hkk ⟨g, hg1⟩ ⟨ζ * g * ζ⁻¹, hg1'⟩ rfl).2 hg2'

theorem u_not_mem_Zs
    (hcube : ∀ a ∈ c.X3, a ^ 3 = 1) : c.u ∉ c.Zs := by
  intro hu
  obtain ⟨a, ha, w, hw, e⟩ := exists_mul_of_mem_sup_of_le_centralizer
    c.zpowers_u₁_le_centralizer_X3 hu
  have hwc : a * w = w * a := by
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    exact ((Commute.zpow_right (show Commute a c.u₁ from c.comm_X3_u₁ ha) n)).eq
  have hw' := zpowers_cases c.u₁_ord w hw
  have hww : w * w = 1 := by rcases hw' with h | h <;> simp [h, c.u₁_sq]
  have haa : a * a = 1 := by
    have h1 := c.u_sq
    rw [e] at h1
    calc a * a = a * a * (w * w) := by rw [hww, mul_one]
      _ = a * (w * a) * w := by rw [← hwc]; group
      _ = (a * w) * (a * w) := by group
      _ = 1 := h1
  have ha1 : a = 1 := by
    have h3 := hcube a ha
    rw [pow_three, haa, mul_one] at h3
    exact h3
  rw [ha1, one_mul] at e
  rcases hw' with h | h
  · exact c.u_ne_one (e.trans h)
  · exact c.u_ne_u₁ (e.trans h)

theorem rho_of_mem_conj_L₁ (k : ↥c.L₁) (hk : t * (k : G) * t⁻¹ ∈ c.P) :
    c.rho ⟨t * (k : G) * t⁻¹, hk⟩ = base 1 (MulAut.conj (c.eL₁ k)) := by
  rw [rho_apply, c.pair.rho_of_mem_conj k k.2, mapEquiv_base, map_one, congr_conj]

theorem conjSub_le_Js : conjSub t c.L₁ ≤ c.Js := by
  intro k hk
  refine mem_centralizer_iff.2 fun z hz => ?_
  have hle : c.Zs ≤ centralizer ({k} : Set G) := by
    refine sup_le (fun a ha => mem_centralizer_singleton_iff.2 ?_)
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 ?_))
    · exact (c.comm_L₁_conj ha.1 hk).eq
    · exact (c.u₁_comm_L₁t hk).symm
  exact mem_centralizer_singleton_iff.1 (hle hz)

theorem conjSub_le_commutator : conjSub t c.L₁ ≤ ⁅c.Js, c.Js⁆ := by
  have h1 : ⁅conjSub t c.L₁, conjSub t c.L₁⁆ = conjSub t c.L₁ := by
    unfold conjSub
    rw [← Subgroup.map_commutator, commutator_eq_self_of_equiv_alt6 c.L₁ c.eL₁]
  calc conjSub t c.L₁ = ⁅conjSub t c.L₁, conjSub t c.L₁⁆ := h1.symm
    _ ≤ ⁅c.Js, c.Js⁆ := Subgroup.commutator_mono c.conjSub_le_Js c.conjSub_le_Js

theorem mem_conjSub_of_odd
    (hψ : ∀ q : ↥c.P, Commute (q : G) c.u₁ ↔ c.rho q ∈ Wreath.baseSubgroup)
    (hMZ : ⁅c.Js, c.Js⁆ ⊓ c.Zs = ⊥)
    {g : G} (hgM : g ∈ ⁅c.Js, c.Js⁆) (hgP : g ∈ c.P) (hodd : Odd (orderOf g)) :
    g ∈ conjSub t c.L₁ := by
  have hgJ : g ∈ c.Js := commutator_le_self' c.Js hgM
  have hcomm : ∀ z ∈ c.Zs, z * g = g * z := fun z hz => mem_centralizer_iff.1 hgJ z hz
  obtain ⟨q, hqdef⟩ : ∃ q : ↥c.P, q = ⟨g, hgP⟩ := ⟨_, rfl⟩
  have hqg : (q : G) = g := by rw [hqdef]
  have hc1 : Commute (q : G) c.u₁ := by
    rw [hqg]
    exact (hcomm c.u₁ c.u₁_mem_Zs).symm
  obtain ⟨⟨A, B⟩, hab⟩ := (hψ q).1 hc1
  have hq : c.rho q = base A B := hab.symm
  have hfix : ∀ b ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set (alternatingGroup (Fin 6))),
      A b = b := by
    intro b hb
    obtain ⟨k, rfl⟩ := c.eL₁.surjective b
    have hk : (k : G) ∈ c.X3 :=
      ⟨k.2, (c.mem_centralizer_x_iff k).2 (mem_centralizer_singleton_iff.1 hb)⟩
    have hcq : (k : G) * q = q * k := by
      rw [hqg]
      exact hcomm k (c.X3_le_Zs hk)
    have h1 := c.rho_base_apply q hq k
    have h2 : ((c.eL₁.symm (A (c.eL₁ k)) : ↥c.L₁) : G) = k := by
      rw [h1]
      calc (q : G) * k * (q : G)⁻¹ = (k * q) * (q : G)⁻¹ := by rw [hcq]
        _ = k := by group
    have h3 : c.eL₁.symm (A (c.eL₁ k)) = k := Subtype.ext h2
    rw [MulEquiv.symm_apply_eq] at h3
    exact h3
  obtain ⟨b, hb, hAb⟩ := mem_inner_of_fix_centralizer c.orderOf_eL₁_x A hfix
  have hqn : q ^ orderOf g = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hqg]
    exact pow_orderOf_eq_one g
  have hBn : B ^ orderOf g = 1 := by
    have h1 : c.rho q ^ orderOf g = 1 := by rw [← map_pow, hqn, map_one]
    rw [hq] at h1
    have h2 : base A B ^ orderOf g = base (A ^ orderOf g) (B ^ orderOf g) := by
      simp only [base, ← map_pow]
      rfl
    rw [h2, ← base_one, base_injective] at h1
    exact h1.2
  obtain ⟨l, hl⟩ := mem_innR_of_pow_eq_one_of_odd hodd hBn
  obtain ⟨b0, hb0⟩ : ∃ b0 : ↥c.L₁, c.eL₁ b0 = b := ⟨c.eL₁.symm b, by simp⟩
  obtain ⟨l0, hl0⟩ : ∃ l0 : ↥c.L₁, c.eL₁ l0 = l := ⟨c.eL₁.symm l, by simp⟩
  have hl'mem : t * (l0 : G) * t⁻¹ ∈ conjSub t c.L₁ := ⟨(l0 : G), l0.2, rfl⟩
  have hb'X3 : (b0 : G) ∈ c.X3 :=
    ⟨b0.2, (c.mem_centralizer_x_iff b0).2 (by
      rw [hb0]
      exact mem_centralizer_singleton_iff.1 hb)⟩
  have hb'P : (b0 : G) ∈ c.P := c.pair.K_le b0.2
  have hl'P : t * (l0 : G) * t⁻¹ ∈ c.P := c.comm_P_conjSub hl'mem
  have hρb : c.rho ⟨(b0 : G), hb'P⟩ = base (MulAut.conj b) 1 := by
    have := c.rho_of_mem_L₁ b0
    rwa [hb0] at this
  have hρl : c.rho ⟨t * (l0 : G) * t⁻¹, hl'P⟩ = base 1 (MulAut.conj l) := by
    have := c.rho_of_mem_conj_L₁ l0 hl'P
    rwa [hl0] at this
  have hw : (⟨(b0 : G), hb'P⟩ : ↥c.P)⁻¹ * q * (⟨t * (l0 : G) * t⁻¹, hl'P⟩ : ↥c.P)⁻¹ ∈
      c.rho.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, hρb, hq, hρl, hAb, ← hl]
    simp [base_inv, base_mul_base, base_one]
  obtain ⟨f, hf⟩ : ∃ f : G, f = (b0 : G)⁻¹ * g * (t * (l0 : G) * t⁻¹)⁻¹ := ⟨_, rfl⟩
  have hfF : f ∈ c.F := by
    have h1 := hw
    rw [ker_rho, c.pair.ker_rho, mem_subgroupOf, mem_inf] at h1
    rw [hf, ← hqg]
    exact ⟨⟨(⟨(b0 : G), hb'P⟩⁻¹ * q * ⟨t * (l0 : G) * t⁻¹, hl'P⟩⁻¹ : ↥c.P).2, h1.1⟩, h1.2⟩
  have hfLt : ∀ k ∈ conjSub t c.L₁, k * f = f * k := fun k hk =>
    mem_centralizer_iff.1 hfF.2 k hk
  have hbf : Commute (b0 : G) f := mem_centralizer_iff.1 hfF.1.2 _ b0.2
  have hfl : Commute f (t * (l0 : G) * t⁻¹) := (hfLt _ hl'mem).symm
  have hbl : Commute (b0 : G) (t * (l0 : G) * t⁻¹) := c.comm_L₁_conj b0.2 hl'mem
  have hff : f * f = 1 := by
    rcases c.mem_F_cases hfF with h | h | h | h <;> rw [h]
    · simp
    · exact c.u_sq
    · exact c.u₁_sq
    · calc c.u * c.u₁ * (c.u * c.u₁) = c.u * (c.u₁ * c.u) * c.u₁ := by group
        _ = c.u * (c.u * c.u₁) * c.u₁ := by rw [c.u₁_mul_u]
        _ = (c.u * c.u) * (c.u₁ * c.u₁) := by group
        _ = 1 := by rw [c.u_sq, c.u₁_sq, mul_one]
  have hgdec : g = (b0 : G) * f * (t * (l0 : G) * t⁻¹) := by rw [hf]; group
  obtain ⟨r, hr⟩ := hodd.add_one
  obtain ⟨k, hk⟩ : ∃ k, k = orderOf g + 1 := ⟨_, rfl⟩
  have hfk : f ^ k = 1 := by
    rw [hk, hr, ← two_mul, pow_mul, pow_two, hff, one_pow]
  have hgk : g ^ k = g := by rw [hk, pow_succ, pow_orderOf_eq_one, one_mul]
  have hpow : g ^ k = (b0 : G) ^ k * (t * (l0 : G) * t⁻¹) ^ k := by
    conv_lhs => rw [hgdec]
    rw [(hbl.mul_left hfl).mul_pow, hbf.mul_pow, hfk, mul_one]
  have hg_eq : g = (b0 : G) ^ k * (t * (l0 : G) * t⁻¹) ^ k := by rw [← hpow, hgk]
  have hβ : (b0 : G) ^ k ∈ c.X3 := pow_mem hb'X3 _
  have hlam : (t * (l0 : G) * t⁻¹) ^ k ∈ conjSub t c.L₁ := pow_mem hl'mem _
  have hβM : (b0 : G) ^ k ∈ ⁅c.Js, c.Js⁆ := by
    have : (b0 : G) ^ k = g * ((t * (l0 : G) * t⁻¹) ^ k)⁻¹ := by
      conv_rhs => rw [hg_eq]
      rw [mul_inv_cancel_right]
    rw [this]
    exact mul_mem hgM (inv_mem (c.conjSub_le_commutator hlam))
  have hβ1 : (b0 : G) ^ k = 1 := by
    have : (b0 : G) ^ k ∈ ⁅c.Js, c.Js⁆ ⊓ c.Zs := ⟨hβM, c.X3_le_Zs hβ⟩
    rw [hMZ, mem_bot] at this
    exact this
  rw [hg_eq, hβ1, one_mul]
  exact hlam

theorem two_le_pRank_centralizer (c : InnerD8Config L t) (hρ : c.rho.range = ⊤)
    (hψ : ∀ q : ↥c.P, Commute (q : G) c.u₁ ↔ c.rho q ∈ Wreath.baseSubgroup)
    (hM : IsSporadic ↥(⁅c.Js, c.Js⁆) .HS) (hMZ : ⁅c.Js, c.Js⁆ ⊓ c.Zs = ⊥)
    (hu : c.u ∈ ⁅c.Js, c.Js⁆ ⊔ c.Zs) :
    2 ≤ CFSG.Open.pRank 2 (centralizer ((⁅c.Js, c.Js⁆ : Subgroup G) : Set G)) := by
  obtain ⟨-, -, hcube⟩ := c.X3_facts (fun _ hx => ⟨card_centralizer_of_orderOf_eq_three hx,
    centralizer_commute_of_orderOf_eq_three hx, pow_three_of_mem_centralizer hx⟩)
  have hMJ : ⁅c.Js, c.Js⁆ ≤ c.Js := commutator_le_self' _
  have hZM : c.Zs ≤ centralizer ((⁅c.Js, c.Js⁆ : Subgroup G) : Set G) := fun z hz =>
    mem_centralizer_iff.2 fun h hh => (mem_centralizer_iff.1 (hMJ hh) z hz).symm
  obtain ⟨m, hmM, z, hzZ, hmz⟩ := exists_mul_of_mem_sup_of_le_centralizer hZM hu
  have hzm : z * m = m * z := mem_centralizer_iff.1 (hMJ hmM) z hzZ
  have hm2 : m * m = 1 := by
    have h1 := c.u_sq
    rw [hmz] at h1
    have h3 : (m * m) * (z * z) = 1 := by
      calc (m * m) * (z * z) = m * (m * z) * z := by group
        _ = m * (z * m) * z := by rw [hzm]
        _ = (m * z) * (m * z) := by group
        _ = 1 := h1
    have h4 : m * m ∈ ⁅c.Js, c.Js⁆ ⊓ c.Zs := by
      refine ⟨mul_mem hmM hmM, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h3]
      exact Subgroup.inv_mem _ (Subgroup.mul_mem _ hzZ hzZ)
    rw [hMZ, mem_bot] at h4
    exact h4
  have hm1 : m ≠ 1 := by
    rintro rfl
    rw [one_mul] at hmz
    exact c.u_not_mem_Zs hcube (by rw [hmz]; exact hzZ)
  have hmo : orderOf m = 2 := orderOf_eq_prime (by rwa [pow_two]) hm1
  have hP : ∀ g ∈ ⁅c.Js, c.Js⁆, g * m = m * g → g ∈ c.P := by
    intro g hgM hgm
    have hzg : z * g = g * z := mem_centralizer_iff.1 (hMJ hgM) z hzZ
    rw [c.mem_P_iff, hmz]
    calc g * (m * z) = (g * m) * z := by group
      _ = m * (g * z) := by rw [hgm]; group
      _ = m * (z * g) := by rw [hzg]
      _ = (m * z) * g := by group
  have hX : ∀ α : MulAut (alternatingGroup (Fin 6)),
      (∀ a ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set _), α a = a) →
      ∃ b ∈ centralizer ({c.eL₁ ⟨c.x, c.x_mem⟩} : Set _), α = MulAut.conj b :=
    fun α h => mem_inner_of_fix_centralizer c.orderOf_eL₁_x α h
  have h51 := c.card_centralizer_X_sup_u₁ hρ hψ hX
  have hcardM : Nat.card (⁅c.Js, c.Js⁆ ⊓ centralizer ({m} : Set G) : Subgroup G) = 2880 := by
    have hm' : orderOf (⟨m, hmM⟩ : ↥⁅c.Js, c.Js⁆) = 2 := by
      rw [← Subgroup.orderOf_coe]
      exact hmo
    have hcongr : Nat.card (⁅c.Js, c.Js⁆ ⊓ centralizer ({m} : Set G) : Subgroup G) =
        Nat.card (centralizer ({(⟨m, hmM⟩ : ↥⁅c.Js, c.Js⁆)} : Set ↥⁅c.Js, c.Js⁆)) := by
      refine Nat.card_congr
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, mem_centralizer_singleton_iff.2 (Subtype.ext (by
            exact mem_centralizer_singleton_iff.1 x.2.2))⟩
          invFun := fun x => ⟨x.1.1, x.1.2, mem_centralizer_singleton_iff.2 (by
            have := mem_centralizer_singleton_iff.1 x.2
            exact congrArg Subtype.val this)⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
    have hle : (⁅c.Js, c.Js⁆ ⊓ centralizer ({m} : Set G) : Subgroup G) ≤
        c.P ⊓ centralizer ((c.Zs : Subgroup G) : Set G) :=
      fun g hg => ⟨hP g hg.1 (mem_centralizer_singleton_iff.1 hg.2), hMJ hg.1⟩
    rcases card_centralizer_of_involution_hs hM ⟨m, hmM⟩ hm' with h | h
    · exfalso
      have hdvd := Subgroup.card_dvd_of_le hle
      rw [h51, hcongr, h] at hdvd
      omega
    · rw [hcongr, h]
  obtain ⟨zb, hzb2, hzb4, hznorm⟩ := exists_zeta_normalizes c.orderOf_eL₁_x
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : G, ζ = ((c.eL₁.symm zb : ↥c.L₁) : G) := ⟨_, rfl⟩
  have hζL : ζ ∈ c.L₁ := by
    rw [hζdef]
    exact (c.eL₁.symm zb).2
  have hζ2 : ζ ^ 2 ≠ 1 := by
    intro h
    apply hzb2
    have h1 : (c.eL₁.symm zb) ^ 2 = 1 := Subtype.ext (by simpa [hζdef] using h)
    have h2 := congrArg c.eL₁ h1
    simpa [map_pow] using h2
  have hζ4 : ζ ^ 4 = 1 := by
    have h1 : ((c.eL₁.symm zb ^ 4 : ↥c.L₁) : G) = 1 := by
      rw [← map_pow, hzb4, map_one]
      rfl
    rw [Subgroup.coe_pow, ← hζdef] at h1
    exact h1
  have hnormX : ∀ g, g ∈ c.X3 ↔ ζ * g * ζ⁻¹ ∈ c.X3 := by
    rw [hζdef]
    exact c.zeta_X3_iff hznorm
  have hζw : ∀ w ∈ zpowers c.u₁, ζ * w = w * ζ := by
    intro w hw
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
    exact ((Commute.zpow_right (show Commute ζ c.u₁ from c.u₁_comm_L₁ hζL) n)).eq
  have hnormZ : ∀ g, g ∈ c.Zs ↔ ζ * g * ζ⁻¹ ∈ c.Zs := by
    intro g
    constructor
    · intro hg
      obtain ⟨a, ha, w, hw, rfl⟩ :=
        exists_mul_of_mem_sup_of_le_centralizer c.zpowers_u₁_le_centralizer_X3 hg
      have e : ζ * (a * w) * ζ⁻¹ = (ζ * a * ζ⁻¹) * w := by
        calc ζ * (a * w) * ζ⁻¹ = (ζ * a * ζ⁻¹) * (ζ * w * ζ⁻¹) := by group
          _ = (ζ * a * ζ⁻¹) * w := by rw [hζw w hw]; group
      rw [e]
      exact mul_mem (c.X3_le_Zs ((hnormX a).1 ha)) (mem_sup_right hw)
    · intro hg
      obtain ⟨a, ha, w, hw, e⟩ :=
        exists_mul_of_mem_sup_of_le_centralizer c.zpowers_u₁_le_centralizer_X3 hg
      have e2 : g = (ζ⁻¹ * a * ζ) * w := by
        calc g = ζ⁻¹ * (ζ * g * ζ⁻¹) * ζ := by group
          _ = ζ⁻¹ * (a * w) * ζ := by rw [e]
          _ = (ζ⁻¹ * a * ζ) * (ζ⁻¹ * w * ζ) := by group
          _ = (ζ⁻¹ * a * ζ) * w := by
            congr 1
            calc ζ⁻¹ * w * ζ = ζ⁻¹ * (w * ζ) := by group
              _ = ζ⁻¹ * (ζ * w) := by rw [hζw w hw]
              _ = w := by group
      have ha' : ζ⁻¹ * a * ζ ∈ c.X3 := by
        refine (hnormX _).2 ?_
        have e3 : ζ * (ζ⁻¹ * a * ζ) * ζ⁻¹ = a := by group
        rw [e3]
        exact ha
      rw [e2]
      exact mul_mem (c.X3_le_Zs ha') (mem_sup_right hw)
  have hnormJ : ζ ∈ normalizer (c.Js : Set G) := mem_normalizer_centralizer hnormZ
  have hnormM : ζ ∈ normalizer ((⁅c.Js, c.Js⁆ : Subgroup G) : Set G) :=
    mem_normalizer_commutator hnormJ
  have hfix : ∀ x ∈ (⁅c.Js, c.Js⁆ : Subgroup G), x * m = m * x → Odd (orderOf x) →
      ζ * x = x * ζ := by
    intro g hgM hgm hodd
    have hg := c.mem_conjSub_of_odd hψ hMZ hgM (hP g hgM hgm) hodd
    exact (c.comm_L₁_conj hζL hg).eq
  have hsq := sq_mem_centralizer_of_normalizes (⁅c.Js, c.Js⁆ : Subgroup G) hM m hmM hmo hcardM
    ζ hnormM hfix
  refine two_le_pRank_of_commuting_involutions (a := c.u₁) (b := ζ ^ 2)
    (mem_centralizer_iff.2 fun h hh => (mem_centralizer_iff.1 (hMJ hh) c.u₁ c.u₁_mem_Zs).symm)
    (mem_centralizer_iff.2 fun h hh => (hsq h hh).symm) c.u₁_ne_one hζ2 ?_ c.u₁_sq
    ((pow_add ζ 2 2).symm.trans hζ4) (c.u₁_comm_L₁ (pow_mem hζL 2)).symm
  intro h
  have hmem : c.u₁ ∈ c.L₁ := by
    rw [h]
    exact pow_mem hζL 2
  have hz : (⟨c.u₁, hmem⟩ : ↥c.L₁) ∈ center ↥c.L₁ :=
    mem_center_iff.2 fun k => Subtype.ext (c.u₁_comm_L₁ k.2)
  rw [center_L₁_eq_bot c, mem_bot] at hz
  exact c.u₁_ne_one (congrArg Subtype.val hz)

end InnerD8Config

end Config

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus
