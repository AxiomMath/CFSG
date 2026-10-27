module

public import Certificates.Certificate320031
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyAlt
public import CFSG.GH74.QTGen4.DSGen4.Leaf.A5ClassifyFrame

public section

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique
open Certificates.A5GL42 (Mat4 Vec4 NormFacts NoInvCent)
open scoped commutatorElement Matrix

theorem a5Facts2 : Certificates.A5GL42.Facts2 :=
  Certificates.certificate320031

@[expose] def finsetSubgroup (N : Finset Mat4) (h1 : (1 : Mat4) ∈ N)
    (hmul : ∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) (hinv : ∀ x ∈ N, ∃ y ∈ N, x * y = 1) :
    Subgroup (GL (Fin 4) (ZMod 2)) where
  carrier := {g | glMat g ∈ N}
  one_mem' := by simpa [glMat] using h1
  mul_mem' := by
    intro a b ha hb
    simpa [glMat] using hmul _ ha _ hb
  inv_mem' := by
    intro a ha
    obtain ⟨y, hy, hxy⟩ := hinv _ ha
    have : glMat a⁻¹ = y := by
      calc glMat a⁻¹ = glMat a⁻¹ * (glMat a * y) := by rw [hxy, mul_one]
        _ = (glMat a⁻¹ * glMat a) * y := by rw [mul_assoc]
        _ = y := by rw [show glMat a⁻¹ * glMat a = 1 from Units.inv_mul a, one_mul]
    show glMat a⁻¹ ∈ N
    rw [this]; exact hy

theorem card_finsetSubgroup (N : Finset Mat4) (h1 : (1 : Mat4) ∈ N)
    (hmul : ∀ x ∈ N, ∀ y ∈ N, x * y ∈ N) (hinv : ∀ x ∈ N, ∃ y ∈ N, x * y = 1) :
    Nat.card (finsetSubgroup N h1 hmul hinv) = N.card := by
  classical
  let f : ↥(finsetSubgroup N h1 hmul hinv) → ↥N := fun g => ⟨glMat g.1, g.2⟩
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      exact Subtype.ext (Units.ext (congrArg Subtype.val hab))
    · rintro ⟨x, hx⟩
      obtain ⟨y, hy, hxy⟩ := hinv x hx
      have hyx : y * x = 1 := mul_eq_one_comm.mp hxy
      exact ⟨⟨⟨x, y, hxy, hyx⟩, hx⟩, rfl⟩
  rw [Nat.card_congr (Equiv.ofBijective f hf), Nat.card_eq_fintype_card, Fintype.card_coe]

end CFSG.GH74.QTGen4.DSGen4

namespace Certificates.A5GL42.NormFacts

open CFSG.GH74.QTGen4.DSGen4

variable {H NH T0 : Finset Mat4} (hN : NormFacts H NH T0)

@[expose] def nsub : Subgroup (GL (Fin 4) (ZMod 2)) :=
  finsetSubgroup NH hN.one_mem hN.mul_mem hN.inv_ex

@[expose] def t0sub : Subgroup (GL (Fin 4) (ZMod 2)) :=
  finsetSubgroup T0 hN.t0_one hN.t0_mul hN.t0_inv

theorem nsub_card : Nat.card hN.nsub = NH.card :=
  card_finsetSubgroup NH hN.one_mem hN.mul_mem hN.inv_ex

theorem t0sub_card : Nat.card hN.t0sub = 8 := by
  rw [show hN.t0sub = finsetSubgroup T0 hN.t0_one hN.t0_mul hN.t0_inv from rfl,
    card_finsetSubgroup]
  exact hN.t0_card

theorem t0sub_le : hN.t0sub ≤ hN.nsub := fun g hg => hN.t0_sub hg

theorem mem_nsub_of_normalizes (g : GL (Fin 4) (ZMod 2))
    (h : ∀ m ∈ H, ∃ m' ∈ H, glMat g * m = m' * glMat g) : g ∈ hN.nsub :=
  hN.complete _ ⟨glMat g⁻¹, Units.mul_inv g⟩ h

theorem free (x : ↥hN.nsub) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) :
    x ∉ Subgroup.normalizer ((hN.t0sub.subgroupOf hN.nsub : Subgroup ↥hN.nsub) : Set ↥hN.nsub) := by
  intro hnorm
  obtain ⟨g, hg⟩ := x
  have hgN : glMat g ∈ NH := hg
  have hg1 : glMat g ≠ 1 := fun h => hx1 (Subtype.ext (Units.ext h))
  have hg3 : glMat g * glMat g * glMat g = 1 := by
    have h3 : g ^ 3 = 1 := congrArg Subtype.val hx3
    have : glMat (g ^ 3) = glMat 1 := congrArg Units.val h3
    simpa [glMat, pow_succ, mul_assoc] using this
  obtain ⟨t, ht, hfree⟩ := hN.t0_free _ hgN hg1 hg3
  obtain ⟨y, hy, hty⟩ := hN.t0_inv t ht
  let tg : GL (Fin 4) (ZMod 2) := ⟨t, y, hty, mul_eq_one_comm.mp hty⟩
  have htg : tg ∈ hN.t0sub := ht
  have htgN : tg ∈ hN.nsub := hN.t0sub_le htg
  have hmem : (⟨tg, htgN⟩ : ↥hN.nsub) ∈ hN.t0sub.subgroupOf hN.nsub := htg
  have h1 := (Subgroup.mem_normalizer_iff.mp hnorm ⟨tg, htgN⟩).mp hmem
  have h2 : glMat (g * tg * g⁻¹) ∈ T0 := h1
  refine hfree _ h2 ?_
  have e : glMat (g * tg * g⁻¹) * glMat g = glMat g * t := by
    show (glMat g * t * glMat g⁻¹) * glMat g = glMat g * t
    rw [mul_assoc, show glMat g⁻¹ * glMat g = 1 from Units.inv_mul g, mul_one]
  exact e.symm

end Certificates.A5GL42.NormFacts

namespace CFSG.GH74.QTGen4.DSGen4

open CFSG.Open CFSG.QuasithinUnique
open Certificates.A5GL42 (Mat4 Vec4 NormFacts NoInvCent)
open scoped commutatorElement Matrix

theorem sylow_no_three {N : Type*} [Group N] [Finite N] {k : ℕ} (hk : ¬ 2 ∣ k)
    (hcard : Nat.card N = 8 * k) {T0 T : Subgroup N} (h0 : Nat.card T0 = 8)
    (h1 : Nat.card T = 8)
    (hfree : ∀ d : N, d ≠ 1 → d ^ 3 = 1 → d ∉ Subgroup.normalizer (T0 : Set N)) {d : N}
    (hd1 : d ≠ 1) (hd3 : d ^ 3 = 1) (hd : d ∈ Subgroup.normalizer (T : Set N)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp0 : IsPGroup 2 T0 := IsPGroup.of_card (n := 3) (by rw [h0]; norm_num)
  have hp1 : IsPGroup 2 T := IsPGroup.of_card (n := 3) (by rw [h1]; norm_num)
  have hi0 : ¬ 2 ∣ T0.index := by
    have := Subgroup.card_mul_index T0
    rw [h0, hcard] at this
    have hidx : T0.index = k := by omega
    rw [hidx]; exact hk
  have hi1 : ¬ 2 ∣ T.index := by
    have := Subgroup.card_mul_index T
    rw [h1, hcard] at this
    have hidx : T.index = k := by omega
    rw [hidx]; exact hk
  let P0 : Sylow 2 N := hp0.toSylow hi0
  let P1 : Sylow 2 N := hp1.toSylow hi1
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N P1 P0
  have hdP1 : d • P1 = P1 := Sylow.smul_eq_iff_mem_normalizer.mpr hd
  have hP0 : (n * d * n⁻¹) • P0 = P0 := by
    rw [← hn, ← mul_smul, mul_assoc, mul_assoc, inv_mul_cancel, mul_one, mul_smul, hdP1]
  have hmem : n * d * n⁻¹ ∈ Subgroup.normalizer (T0 : Set N) :=
    Sylow.smul_eq_iff_mem_normalizer.mp hP0
  refine hfree (n * d * n⁻¹) ?_ ?_ hmem
  · intro h
    apply hd1
    have : d = n⁻¹ * (n * d * n⁻¹) * n := by group
    rw [this, h]; group
  · rw [conj_pow, hd3]; group

section Core

variable {G : Type} [Group G] [Finite G]

theorem relIndex_eq_card_range {P Q : Subgroup G} (M : ↥P →* GL (Fin 4) (ZMod 2))
    (hker : ∀ p : ↥P, M p = 1 ↔ (p : G) ∈ Q) : Q.relIndex P = Nat.card M.range := by
  have hk : M.ker = Q.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [← Subgroup.index_ker, hk]
  rfl

theorem not_mem_of_pgroup_of_orderOf_three {Q : Subgroup G} (hQ : IsPGroup 2 Q) {x : G}
    (hx3 : orderOf x = 3) : x ∉ Q := by
  intro hx
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) ⟨x, hx⟩
  rw [Subgroup.orderOf_mk, hx3] at hk
  rcases k with _ | k
  · simp at hk
  · have : 2 ∣ 2 ^ (k + 1) := dvd_pow_self 2 (Nat.succ_ne_zero k)
    omega

theorem card_map_eq_relIndex {P Q S : Subgroup G} (hSP : S ≤ P) (M : ↥P →* GL (Fin 4) (ZMod 2))
    (hker : ∀ p : ↥P, M p = 1 ↔ (p : G) ∈ Q) :
    Nat.card ((S.subgroupOf P).map M) = Q.relIndex S := by
  have hk : M.ker.relIndex (S.subgroupOf P) = Nat.card ((S.subgroupOf P).map M) :=
    Subgroup.relIndex_ker (S.subgroupOf P) M
  have hkq : M.ker = Q.subgroupOf P := by
    ext p
    rw [MonoidHom.mem_ker, hker, Subgroup.mem_subgroupOf]
  rw [hkq, Subgroup.relIndex_subgroupOf hSP] at hk
  exact hk.symm

theorem map_conj_mem_iff {P S : Subgroup G} (M : ↥P →* GL (Fin 4) (ZMod 2)) {d : G} (hdP : d ∈ P)
    (hdS : d ∈ Subgroup.normalizer (S : Set G)) (g : GL (Fin 4) (ZMod 2)) :
    g ∈ (S.subgroupOf P).map M ↔
      M ⟨d, hdP⟩ * g * (M ⟨d, hdP⟩)⁻¹ ∈ (S.subgroupOf P).map M := by
  constructor
  · rintro ⟨s, hs, rfl⟩
    refine ⟨⟨d, hdP⟩ * s * ⟨d, hdP⟩⁻¹, ?_, by simp [map_mul, map_inv]⟩
    have hs : (s : G) ∈ S := hs
    show (((⟨d, hdP⟩ * s * ⟨d, hdP⟩⁻¹ : ↥P)) : G) ∈ S
    simpa using (Subgroup.mem_normalizer_iff.mp hdS (s : G)).mp hs
  · rintro ⟨s', hs', he⟩
    refine ⟨⟨d, hdP⟩⁻¹ * s' * ⟨d, hdP⟩, ?_, ?_⟩
    · have hs'' : (s' : G) ∈ S := hs'
      show ((⟨d, hdP⟩⁻¹ * s' * ⟨d, hdP⟩ : ↥P) : G) ∈ S
      have := (Subgroup.mem_normalizer_iff.mp hdS ((d⁻¹ * (s' : G) * d))).mpr
        (by simpa [mul_assoc] using hs'')
      simpa [mul_assoc] using this
    · rw [map_mul, map_mul, map_inv, he]
      group

theorem m2_index {P Q S : Subgroup G} {H NH T0 : Finset Mat4} (hN : NormFacts H NH T0)
    (hS : IsSylowTwoOf S P) (hQS : Q ≤ S)
    (M : ↥P →* GL (Fin 4) (ZMod 2)) (hker : ∀ p : ↥P, M p = 1 ↔ (p : G) ∈ Q)
    (hnorm : ∀ p : ↥P, ∀ m ∈ H, ∃ m' ∈ H, glMat (M p) * m = m' * glMat (M p))
    (h4 : 4 ∣ Nat.card M.range) : Q.relIndex S ∣ 8 ∧ 4 ∣ Q.relIndex S := by
  have hSP : S ≤ P := hS.1
  have hMN : ∀ p : ↥P, M p ∈ hN.nsub := fun p => hN.mem_nsub_of_normalizes _ (hnorm p)
  have hrange : M.range ≤ hN.nsub := by
    rintro _ ⟨p, rfl⟩
    exact hMN p
  have hindex : Q.relIndex P = Nat.card M.range := relIndex_eq_card_range M hker
  have hmulti : Q.relIndex S * S.relIndex P = Q.relIndex P :=
    Subgroup.relIndex_mul_relIndex Q S P hQS hSP
  have hSodd : ¬ 2 ∣ S.relIndex P := hS.2.2
  have hrangeN : Nat.card M.range ∣ NH.card := by
    rw [← hN.nsub_card]
    exact Subgroup.card_dvd_of_le hrange
  have hdvdN : Q.relIndex S ∣ NH.card := by
    refine (Dvd.intro _ hmulti).trans ?_
    rw [hindex]
    exact hrangeN
  obtain ⟨n, hn⟩ := hS.2.1.exists_card_eq
  have hpow : Q.relIndex S ∣ 2 ^ n := by
    rw [← hn]
    exact Subgroup.relIndex_dvd_card Q S
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hpow
  have hmod := hN.card_mod
  have hj3 : j ≤ 3 := by
    by_contra hc
    have h16 : (16 : ℕ) ∣ NH.card := by
      have : (16 : ℕ) ∣ 2 ^ j := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num]
        exact pow_dvd_pow 2 (by omega)
      exact this.trans (hjeq ▸ hdvdN)
    omega
  refine ⟨?_, ?_⟩
  · rw [hjeq, show (8 : ℕ) = 2 ^ 3 by norm_num]
    exact pow_dvd_pow 2 hj3
  · have hcop : Nat.Coprime 4 (S.relIndex P) := by
      have := (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hSodd
      simpa using Nat.Coprime.pow_left 2 this
    have : 4 ∣ Q.relIndex S * S.relIndex P := by rw [hmulti, hindex]; exact h4
    exact hcop.dvd_of_dvd_mul_right this

theorem eq_four_of_dvd_eight {r : ℕ} (h8 : r ∣ 8) (h4 : 4 ∣ r) (hne : r ≠ 8) : r = 4 := by
  obtain ⟨a, ha⟩ := h4
  have ha' : a ∣ 2 := by
    have h8' : 4 * a ∣ 4 * 2 := by rw [← ha]; exact h8
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) h8'
  have ha_pos : 0 < a := Nat.pos_of_dvd_of_pos ha' (by norm_num)
  have ha_le : a ≤ 2 := Nat.le_of_dvd (by norm_num) ha'
  interval_cases a <;> omega

theorem m2_not_eight {P Q S : Subgroup G} {H NH T0 : Finset Mat4} (hN : NormFacts H NH T0)
    (hQ2 : IsPGroup 2 Q) (hSP : S ≤ P)
    (M : ↥P →* GL (Fin 4) (ZMod 2)) (hker : ∀ p : ↥P, M p = 1 ↔ (p : G) ∈ Q)
    (hMN : ∀ p : ↥P, M p ∈ hN.nsub) (h8 : Q.relIndex S = 8) {d : G} (hdP : d ∈ P)
    (hdS : d ∈ Subgroup.normalizer (S : Set G)) (hd3 : orderOf d = 3) : False := by
  have hTcard : Nat.card ((S.subgroupOf P).map M) = 8 := by
    rw [card_map_eq_relIndex hSP M hker, h8]
  have hTle : (S.subgroupOf P).map M ≤ hN.nsub :=
    (Subgroup.map_le_range M _).trans (by rintro _ ⟨p, rfl⟩; exact hMN p)
  have hcardN : Nat.card ↥hN.nsub = 8 * (NH.card / 8) := by
    have := hN.card_mod
    rw [hN.nsub_card]; omega
  have hk8 : ¬ 2 ∣ NH.card / 8 := by
    have := hN.card_mod
    omega
  have hT'card : Nat.card (((S.subgroupOf P).map M).subgroupOf hN.nsub) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTle).toEquiv]; exact hTcard
  have hT0card : Nat.card (hN.t0sub.subgroupOf hN.nsub) = 8 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN.t0sub_le).toEquiv]; exact hN.t0sub_card
  let y : ↥P := ⟨d, hdP⟩
  let x : ↥hN.nsub := ⟨M y, hMN y⟩
  have hdpow : d ^ 3 = 1 := by
    have h1 := pow_orderOf_eq_one d
    rwa [hd3] at h1
  have hx3 : x ^ 3 = 1 := by
    apply Subtype.ext
    show (M y) ^ 3 = 1
    rw [← map_pow]
    have : y ^ 3 = 1 := Subtype.ext (by simpa using hdpow)
    rw [this, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : M y = 1 := congrArg Subtype.val h
    exact not_mem_of_pgroup_of_orderOf_three hQ2 hd3 ((hker y).mp h1)
  have hxnorm : x ∈ Subgroup.normalizer
      ((((S.subgroupOf P).map M).subgroupOf hN.nsub : Subgroup ↥hN.nsub) : Set ↥hN.nsub) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact map_conj_mem_iff M hdP hdS (h : GL (Fin 4) (ZMod 2))
  exact sylow_no_three hk8 hcardN hT0card hT'card hN.free hx1 hx3 hxnorm

theorem m2_core {P Q S : Subgroup G} {H NH T0 : Finset Mat4} (hN : NormFacts H NH T0)
    (hQ2 : IsPGroup 2 Q) (hS : IsSylowTwoOf S P) (hQS : Q ≤ S)
    (M : ↥P →* GL (Fin 4) (ZMod 2)) (hker : ∀ p : ↥P, M p = 1 ↔ (p : G) ∈ Q)
    (hnorm : ∀ p : ↥P, ∀ m ∈ H, ∃ m' ∈ H, glMat (M p) * m = m' * glMat (M p))
    (h4 : 4 ∣ Nat.card M.range) :
    Q.relIndex S ∣ 8 ∧
      ∀ d ∈ P ⊓ Subgroup.normalizer (S : Set G), orderOf d = 3 → Q.relIndex S = 4 := by
  obtain ⟨hd8, hd4⟩ := m2_index hN hS hQS M hker hnorm h4
  refine ⟨hd8, fun d hd hd3 => ?_⟩
  obtain ⟨hdP, hdS⟩ := Subgroup.mem_inf.mp hd
  refine eq_four_of_dvd_eight hd8 hd4 fun h8 => ?_
  exact m2_not_eight hN hQ2 hS.1 M hker (fun p => hN.mem_nsub_of_normalizes _ (hnorm p)) h8 hdP
    hdS hd3

theorem m2_odd {P L Q : Subgroup G} {H : Finset Mat4} (hC : NoInvCent H)
    (M : ↥P →* GL (Fin 4) (ZMod 2)) (hker : ∀ p : ↥P, M p = 1 ↔ (p : G) ∈ Q)
    (hsurj : ∀ m ∈ H, ∃ l : ↥P, (l : G) ∈ L ∧ glMat (M l) = m) :
    Odd (Q.relIndex (dsCentMod P L Q)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hCP : dsCentMod P L Q ≤ P := fun c hc => hc.1
  let g : ↥(dsCentMod P L Q) →* GL (Fin 4) (ZMod 2) := M.comp (Subgroup.inclusion hCP)
  have hgker : g.ker = Q.subgroupOf (dsCentMod P L Q) := by
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hker (Subgroup.inclusion hCP c)
  have hidx : Q.relIndex (dsCentMod P L Q) = Nat.card g.range := by
    rw [← Subgroup.index_ker, hgker]
    rfl
  rw [hidx, Nat.odd_iff]
  by_contra hodd
  have h2 : 2 ∣ Nat.card g.range := by omega
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  obtain ⟨c, hc⟩ := x.2
  have hx2 : orderOf (x : GL (Fin 4) (ZMod 2)) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hsq : glMat (x : GL (Fin 4) (ZMod 2)) * glMat (x : GL (Fin 4) (ZMod 2)) = 1 := by
    have h1 := pow_orderOf_eq_one (x : GL (Fin 4) (ZMod 2))
    rw [hx2] at h1
    rw [← Units.val_mul, ← sq, h1, Units.val_one]
  have hcomm : ∀ h ∈ H, glMat (x : GL (Fin 4) (ZMod 2)) * h = h * glMat (x : GL (Fin 4) (ZMod 2)) := by
    intro h hh
    obtain ⟨l, hlL, hlh⟩ := hsurj h hh
    have hcl := c.2.2.2 l hlL
    have hM1 : M ⁅Subgroup.inclusion hCP c, l⁆ = 1 := (hker _).mpr hcl
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at hM1
    have := congrArg Units.val hM1
    rw [Units.val_mul, Units.val_mul] at this
    rw [← hc, ← hlh]
    exact this
  have h1 := hC _ hsq hcomm
  have : (x : GL (Fin 4) (ZMod 2)) = 1 := Units.ext h1
  rw [this, orderOf_one] at hx2
  omega

end Core

end CFSG.GH74.QTGen4.DSGen4
