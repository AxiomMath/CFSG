module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.Level55
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.RankLemma
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.CoprimeFixed
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoB.CentPair

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.TwoB

open Subgroup CFSG.Blueprint.NativeSporadic CFSG.EvenSporadicStandard.TwoFi22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem centPair_le_centralizer (z t : G) : centPair z t ≤ centralizer ({t} : Set G) := by
  rw [centPair_eq_inf]; exact inf_le_right

theorem conj_mem_sup_of_invariant {A B : Subgroup G} {k : G}
    (hA : ∀ a ∈ A, k * a * k⁻¹ ∈ A) (hB : ∀ b ∈ B, k * b * k⁻¹ ∈ B) :
    ∀ x ∈ A ⊔ B, k * x * k⁻¹ ∈ A ⊔ B := by
  intro x hx
  have h1 : A.map (MulAut.conj k).toMonoidHom ≤ A := by
    rintro _ ⟨a, ha, rfl⟩; exact hA a ha
  have h2 : B.map (MulAut.conj k).toMonoidHom ≤ B := by
    rintro _ ⟨b, hb, rfl⟩; exact hB b hb
  have h3 : (A ⊔ B).map (MulAut.conj k).toMonoidHom ≤ A ⊔ B := by
    rw [Subgroup.map_sup]; exact sup_le_sup h1 h2
  exact h3 ⟨x, hx, rfl⟩

theorem isPGroup_sup_zpowers [Finite G] {C P : Subgroup G} (hPC : P ≤ C)
    (hn : (P.subgroupOf C).Normal) (hP : IsPGroup 2 P) {t : G} (htC : t ∈ C)
    (ht : orderOf t = 2) : IsPGroup 2 ↥(P ⊔ zpowers t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let t' : ↥C := ⟨t, htC⟩
  have ht' : IsPGroup 2 (zpowers t') :=
    isPGroup_zpowers_two ((Subgroup.orderOf_mk t htC).trans ht)
  obtain ⟨S, hS⟩ := ht'.exists_le_sylow
  have hP' : IsPGroup 2 (P.subgroupOf C) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
  have hPS : P.subgroupOf C ≤ S := hP'.le_sylow_of_normal S
  have hX' : IsPGroup 2 ↥(P.subgroupOf C ⊔ zpowers t') := S.isPGroup'.to_le (sup_le hPS hS)
  have hmap : (P.subgroupOf C ⊔ zpowers t').map C.subtype = P ⊔ zpowers t := by
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hPC, MonoidHom.map_zpowers]
    rfl
  have := hX'.of_equiv (Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective)
  rw [hmap] at this
  exact this


theorem mem_normalizer_O2In {H : Subgroup G} {g : G} (hg : g ∈ H) :
    g ∈ normalizer ((O2In H : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    have := (normal_subgroupOf_O2In H).conj_mem ⟨h, O2In_le H hh⟩
      (by rw [mem_subgroupOf]; exact hh) ⟨g, hg⟩
    exact this
  · intro hh
    have := (normal_subgroupOf_O2In H).conj_mem ⟨g * h * g⁻¹, H.mul_mem (H.mul_mem hg (by
      have h1 := O2In_le H hh
      have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
      rw [this]
      exact H.mul_mem (H.mul_mem (H.inv_mem hg) h1) hg)) (H.inv_mem hg)⟩
      (by rw [mem_subgroupOf]; exact hh) ⟨g⁻¹, H.inv_mem hg⟩
    have e : g⁻¹ * (g * h * g⁻¹) * g = h := by group
    have e2 : (g⁻¹ * (g * h * g⁻¹) * (g⁻¹)⁻¹ : G) = h := by group
    exact e2 ▸ this

theorem card_pair_le [Finite G] {z t : G} (hz : orderOf z = 2) (ht : orderOf t = 2)
    (hzt : z * t = t * z) : Nat.card (pair z t) ≤ 4 := by
  have hsub : ((pair z t : Subgroup G) : Set G) ⊆ {1, z, t, z * t} := by
    intro x hx
    have hle : zpowers t ≤ centralizer ((zpowers z : Subgroup G) : Set G) := by
      rw [zpowers_le, mem_centralizer_iff]
      intro a ha
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 ha
      exact ((Commute.zpow_left (show Commute z t from hzt) k).eq)
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_le_centralizer hle hx
    rcases eq_one_or_eq_of_mem_zpowers_two hz ha with rfl | rfl <;>
      rcases eq_one_or_eq_of_mem_zpowers_two ht hb with rfl | rfl <;> simp
  have h1 : Nat.card ((pair z t : Subgroup G) : Set G) ≤ Nat.card ({1, z, t, z * t} : Set G) :=
    Nat.card_mono (Set.toFinite _) hsub
  have h2 : Nat.card ({1, z, t, z * t} : Set G) ≤ 4 := by
    classical
    have : Nat.card ({1, z, t, z * t} : Set G) =
        ({1, z, t, z * t} : Finset G).card := by
      rw [Nat.card_eq_fintype_card]
      simp
    rw [this]
    exact Finset.card_le_four
  exact h1.trans h2

section Main

variable [Finite G] {t z : G}

theorem Level55.z_mem_R0 (d : Level55 G t z) : z ∈ d.R0 := by
  have h : z ∈ (center ↥d.R0).map d.R0.subtype := d.R0_center ▸ mem_zpowers z
  obtain ⟨c, -, hc⟩ := h
  have h1 : (c : G) ∈ d.R0 := c.2
  rw [show (c : G) = z from hc] at h1
  exact h1

theorem Level55.pair_le_O2K (d : Level55 G t z) : pair z t ≤ O2In (centPair z t) := by
  rw [d.O2K]
  exact sup_le_sup (zpowers_le.2 d.z_mem_R0) le_rfl

theorem Level55.R0_le_O2K (d : Level55 G t z) : d.R0 ≤ O2In (centPair z t) := by
  rw [d.O2K]; exact le_sup_left

theorem Level55.inf_le_pair_or_le (d : Level55 G t z) :
    O2In (centPair z t) ⊓ Psub z ≤ pair z t ∨ O2In (centPair z t) ≤ Psub z := by
  have hpairR1 : pair z t ≤ O2In (centPair z t) := d.pair_le_O2K
  have hR1K : O2In (centPair z t) ≤ centPair z t := O2In_le _
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hWinv : ∀ k ∈ centPair z t, ∀ w ∈ O2In (centPair z t) ⊓ Psub z,
      k * w * k⁻¹ ∈ O2In (centPair z t) ⊓ Psub z := by
    intro k hk w hw
    refine mem_inf.2 ⟨?_, ?_⟩
    · have := (normal_subgroupOf_O2In (centPair z t)).conj_mem ⟨w, hR1K hw.1⟩
        (by rw [mem_subgroupOf]; exact hw.1) ⟨k, hk⟩
      exact this
    · have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨w, O2In_le _ hw.2⟩
        (by rw [mem_subgroupOf]; exact hw.2) ⟨k, hKC hk⟩
      exact this
  have hpairinv : ∀ k ∈ centPair z t, ∀ a ∈ pair z t, k * a * k⁻¹ ∈ pair z t := by
    intro k hk a ha
    have : a * k = k * a := mem_centralizer_iff.1 hk a ha
    rw [← this, mul_inv_cancel_right]
    exact ha
  have hW'inv : ∀ k ∈ centPair z t, ∀ x ∈ (O2In (centPair z t) ⊓ Psub z) ⊔ pair z t,
      k * x * k⁻¹ ∈ (O2In (centPair z t) ⊓ Psub z) ⊔ pair z t := fun k hk =>
    conj_mem_sup_of_invariant (hWinv k hk) (hpairinv k hk)
  have hle : (O2In (centPair z t) ⊓ Psub z) ⊔ pair z t ≤ O2In (centPair z t) :=
    sup_le inf_le_left hpairR1
  rcases d.irred _ le_sup_right hle hW'inv with h0 | h0
  · left
    exact le_sup_left.trans h0.le
  · right
    have hz : z ∈ O2In (centPair z t) ⊓ Psub z :=
      mem_inf.2 ⟨hpairR1 (z_mem_pair z t), self_mem_O2In_centZ d.z_ord⟩
    have hdec : ∀ x ∈ O2In (centPair z t), ∃ w ∈ O2In (centPair z t) ⊓ Psub z,
        ∃ a ∈ pair z t, x = w * a := by
      intro x hx
      rw [← h0] at hx
      refine exists_mul_of_mem_sup_of_le_centralizer ?_ hx
      intro a ha
      rw [mem_centralizer_iff]
      intro w hw
      exact (mem_centralizer_iff.1 (hR1K hw.1) a ha).symm
    have ht : t ∈ O2In (centPair z t) ⊓ Psub z := by
      have hsub : ⁅d.R0, centPair z t⁆ ≤ O2In (centPair z t) ⊓ Psub z := by
        rw [Subgroup.commutator_le]
        intro r hr k hk
        obtain ⟨w, hw, a, ha, hra⟩ := hdec r (d.R0_le_O2K hr)
        have hak : a * k = k * a := mem_centralizer_iff.1 hk a ha
        have e1 : ⁅r, k⁆ = ⁅w, k⁆ := by
          rw [hra, commutatorElement_def, commutatorElement_def]
          calc w * a * k * (w * a)⁻¹ * k⁻¹ = w * (a * k) * a⁻¹ * w⁻¹ * k⁻¹ := by group
            _ = w * (k * a) * a⁻¹ * w⁻¹ * k⁻¹ := by rw [hak]
            _ = w * k * w⁻¹ * k⁻¹ := by group
        rw [e1]
        have h1 := hWinv k hk w⁻¹ (inv_mem hw)
        have e2 : ⁅w, k⁆ = w * (k * w⁻¹ * k⁻¹) := by rw [commutatorElement_def]; group
        rw [e2]
        exact mul_mem hw h1
      exact hsub d.t_mem_comm
    have hpair : pair z t ≤ O2In (centPair z t) ⊓ Psub z :=
      sup_le (zpowers_le.2 hz) (zpowers_le.2 ht)
    intro x hx
    obtain ⟨w, hw, a, ha, rfl⟩ := hdec x hx
    exact (mul_mem hw (hpair ha)).2

section Certified


theorem Level55.O2K_le_P (d : Level55 G t z) (h54 : IsTwoConstrained (centZ z)) :
    O2In (centPair z t) ≤ Psub z := by
  by_contra hnot
  have hW : O2In (centPair z t) ⊓ Psub z ≤ pair z t :=
    (d.inf_le_pair_or_le).resolve_right hnot
  have hKC : centPair z t ≤ centZ z := centPair_le_centZ z t
  have hPC : Psub z ≤ centZ z := O2In_le _
  have hPK : Psub z ⊓ centPair z t ≤ pair z t := by
    have hn : ((Psub z ⊓ centPair z t).subgroupOf (centPair z t)).Normal := by
      refine ⟨fun n hn g => ?_⟩
      rw [mem_subgroupOf] at hn ⊢
      refine mem_inf.2 ⟨?_, (centPair z t).mul_mem ((centPair z t).mul_mem g.2 hn.2)
        ((centPair z t).inv_mem g.2)⟩
      have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨(n : G), hPC hn.1⟩
        (by rw [mem_subgroupOf]; exact hn.1) ⟨(g : G), hKC g.2⟩
      exact this
    have hp : IsPGroup 2 (Psub z ⊓ centPair z t : Subgroup G) :=
      (isPGroup_O2In _).to_le inf_le_left
    have hle := le_O2In inf_le_right hn hp
    exact fun x hx => hW (mem_inf.2 ⟨hle hx, hx.1⟩)
  have htK : t ∈ centPair z t := mem_centPair_iff.2 ⟨d.zt_comm, rfl⟩
  have htC : t ∈ centZ z := hKC htK
  have hX : IsPGroup 2 ↥(Psub z ⊔ zpowers t) :=
    isPGroup_sup_zpowers hPC (normal_subgroupOf_O2In _) (isPGroup_O2In _) htC d.t_ord
  have htX : t ∈ Psub z ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have hLE : zpowers t ≤ normalizer ((Psub z : Subgroup G) : Set G) := by
    rw [zpowers_le]
    exact mem_normalizer_O2In htC
  have hXc : (Psub z ⊔ zpowers t) ⊓ centralizer ({t} : Set G) ≤ pair z t := by
    intro x hx
    have hxX := hx.1
    have hxt := hx.2
    have hmul : x ∈ ((Psub z : Subgroup G) : Set G) * ((zpowers t : Subgroup G) : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hLE]
      exact hxX
    obtain ⟨p, hp, b, hb, rfl⟩ := hmul
    have hbt : b * t = t * b := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      exact ((Commute.zpow_left (show Commute t t from rfl) k).eq)
    have hpt : p * t = t * p := by
      have h1 : p * b * t = t * (p * b) := mem_centralizer_singleton_iff.1 hxt
      have h2 : p * t * b = t * p * b := by
        calc p * t * b = p * (t * b) := by rw [mul_assoc]
          _ = p * (b * t) := by rw [hbt]
          _ = p * b * t := by rw [mul_assoc]
          _ = t * (p * b) := h1
          _ = t * p * b := by rw [mul_assoc]
      exact mul_right_cancel h2
    have hpK : p ∈ centPair z t :=
      mem_centPair_iff.2 ⟨(mem_centralizer_singleton_iff.1 (hPC hp)).symm, hpt.symm⟩
    exact mul_mem (hPK (mem_inf.2 ⟨hp, hpK⟩)) (mem_sup_right hb)
  have hhom : Nat.card (↥(Psub z ⊔ zpowers t) →* Multiplicative (ZMod 2)) < 23 := by
    have h1 := RankLemma.card_hom_le_card_inf_centralizer_of_mem htX
    have h2 : Nat.card ↥((Psub z ⊔ zpowers t) ⊓ centralizer ({t} : Set G)) ≤
        Nat.card (pair z t) := Subgroup.card_le_of_le hXc
    have h3 := card_pair_le d.z_ord d.t_ord d.zt_comm
    omega
  have h23 : 23 ∣ Nat.card (centPair z t) := by
    obtain ⟨e⟩ := d.quot
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (CFSG.pCore 2 ↥(centPair z t))
    have hco : Nat.card (Carrier .Co2) = 42305421312000 := CFSG.Sporadic.Co2.card_Co2
    rw [Nat.card_congr e.toEquiv, hco] at h2
    rw [h2]
    exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨σ, hσ⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centPair z t)) 23 h23
  have hσ' : orderOf (σ : G) = 23 := by rw [Subgroup.orderOf_coe]; exact hσ
  have hσt : (σ : G) * t = t * σ := by
    have := (mem_centPair_iff.1 σ.2).2
    exact this.symm
  have hnorm : ∀ x ∈ Psub z ⊔ zpowers t, (σ : G) * x * (σ : G)⁻¹ ∈ Psub z ⊔ zpowers t := by
    refine conj_mem_sup_of_invariant ?_ ?_
    · intro a ha
      have := (normal_subgroupOf_O2In (centZ z)).conj_mem ⟨a, hPC ha⟩
        (by rw [mem_subgroupOf]; exact ha) ⟨(σ : G), hKC σ.2⟩
      exact this
    · intro b hb
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hb
      have hc : (σ : G) * t ^ k = t ^ k * σ := (Commute.zpow_right (show Commute (σ : G) t from
        hσt) k).eq
      rw [hc, mul_inv_cancel_right]
      exact zpow_mem (mem_zpowers t) k
  have hcomm := commute_of_card_hom_lt hX (q := 23) (by norm_num) (by norm_num) hσ' hnorm hhom
  have hσP : (σ : G) ∈ Psub z := by
    have hσC : (σ : G) ∈ centZ z ⊓ centralizer ((O2In (centZ z) : Subgroup G) : Set G) := by
      refine mem_inf.2 ⟨hKC σ.2, ?_⟩
      rw [mem_centralizer_iff]
      intro p hp
      exact (hcomm p (mem_sup_left hp)).symm
    exact h54 hσC
  obtain ⟨k, hk⟩ := isPGroup_O2In (centZ z) ⟨(σ : G), hσP⟩
  have hk' : (σ : G) ^ 2 ^ k = 1 := congrArg Subtype.val hk
  have hdvd : orderOf (σ : G) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  rw [hσ'] at hdvd
  have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 23) hdvd
  omega

end Certified

end Main

end CFSG.EvenSporadicStandard.TwoB
