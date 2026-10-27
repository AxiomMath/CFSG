module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87Open
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoOddLieGamma

public section

open Subgroup CFSG CFSG.ComponentClassification.OuterAutomorphisms CFSG.Open
open scoped commutatorElement

namespace CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem autCfg_inf_inner_eq_bot {Y : Type} [Group Y] [Finite Y]
    (hinj : Function.Injective (MulAut.conj : Y →* MulAut Y))
    (hCIT : ∀ k : Y, k * k = 1 → k ≠ 1 → IsPGroup 2 (centralizer ({k} : Set Y)))
    {α : MulAut Y} {p : ℕ} {X : Subgroup (MulAut Y)} (h : AutCfg Y α p X)
    {T : Subgroup Y} (hT4 : 4 ≤ Nat.card ↥T) (hTsq : ∀ t ∈ T, t * t = 1)
    (hTfix : ∀ t ∈ T, α t = t) : X ⊓ innSub Y = ⊥ := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : Finite (MulAut Y) :=
    Finite.of_injective (fun f : MulAut Y => (f : Y → Y)) DFunLike.coe_injective
  have hIn : (innSub Y).Normal := inferInstanceAs ((inner Y).Normal)
  set I : Subgroup (MulAut Y) := innSub Y with hI
  set Q : Subgroup (MulAut Y) := X ⊓ I with hQ
  have hpodd : Odd p := h.prime.odd_of_ne_two h.odd
  have hQodd : Odd (Nat.card ↥Q) := by
    obtain ⟨k, hk⟩ := (h.pgroup.to_inf_left : IsPGroup p ↥Q).exists_card_eq
    rw [hk]
    exact hpodd.pow
  set Tb : Subgroup (MulAut Y) := T.map (MulAut.conj : Y →* MulAut Y) with hTb
  have hTbsq : ∀ x ∈ Tb, x * x = 1 := by
    rintro _ ⟨k, hk, rfl⟩
    rw [← map_mul, hTsq k hk, map_one]
  have hTbc : ∀ a ∈ Tb, ∀ b ∈ Tb, a * b = b * a := by
    intro a ha b hb
    have hab : (a * b) * (a * b) = 1 := hTbsq _ (Tb.mul_mem ha hb)
    have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hTbsq a ha)
    have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hTbsq b hb)
    have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    rw [this, mul_inv_rev, ha', hb']
  have hTbE : IsElemAbelian 2 Tb :=
    ⟨⟨⟨fun a b => Subtype.ext (hTbc a.1 a.2 b.1 b.2)⟩⟩, fun x hx => by rw [pow_two]; exact hTbsq x hx⟩
  have hTb4 : 4 ≤ Nat.card ↥Tb := by
    rw [← Nat.card_congr (Subgroup.equivMapOfInjective T _ hinj).toEquiv]
    exact hT4
  have hTbN : Tb ≤ normalizer (Q : Set (MulAut Y)) := by
    rintro _ ⟨k, hk, rfl⟩
    have hcomm : α * MulAut.conj k = MulAut.conj k * α := by
      refine MulEquiv.ext fun y => ?_
      simp [MulAut.conj_apply, hTfix k hk]
    have hkX := h.cent_norm k hcomm
    rw [mem_normalizer_iff] at hkX ⊢
    intro q
    constructor
    · rintro ⟨hqX, hqI⟩
      exact ⟨(hkX q).mp hqX, hIn.conj_mem q hqI _⟩
    · rintro ⟨hqX, hqI⟩
      refine ⟨(hkX q).mpr hqX, ?_⟩
      have := hIn.conj_mem _ hqI (MulAut.conj k)⁻¹
      simpa [mul_assoc] using this
  have hgen := CFSG.ComponentClassification.RankTwoOddLie.le_iSup_inf_centralizer_of_odd
    (T := Tb) (Q := Q) (C := Q) hTbE hTb4 hQodd hTbN le_rfl
  have hterm : ∀ t ∈ Tb, t ≠ 1 → Q ⊓ centralizer ({t} : Set (MulAut Y)) = ⊥ := by
    intro t ht ht1
    obtain ⟨k, hk, rfl⟩ := ht
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨⟨hqX, hqI⟩, hqc⟩ := Subgroup.mem_inf.mp hq |>.imp_left Subgroup.mem_inf.mp
    obtain ⟨y, rfl⟩ := hqI
    have hk1 : k ≠ 1 := fun h1 => ht1 (by rw [h1, map_one])
    have hyk : y ∈ centralizer ({k} : Set Y) := by
      rw [mem_centralizer_singleton_iff]
      apply hinj
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp hqc
    have hcit := hCIT k (hTsq k hk) hk1
    obtain ⟨a, ha⟩ := hcit ⟨y, hyk⟩
    obtain ⟨b, hb⟩ := h.pgroup ⟨_, hqX⟩
    have h1 : y ^ (2 ^ a) = 1 := congrArg Subtype.val ha
    have h2 : y ^ (p ^ b) = 1 :=
      hinj (by rw [map_pow, map_one]; exact congrArg Subtype.val hb)
    have hcop : Nat.Coprime (2 ^ a) (p ^ b) :=
      Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two h.prime).mpr (Ne.symm h.odd))
    have hdvd : orderOf y ∣ Nat.gcd (2 ^ a) (p ^ b) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one h2)
    rw [hcop.gcd_eq_one, Nat.dvd_one, orderOf_eq_one_iff] at hdvd
    rw [Subgroup.mem_bot, hdvd, map_one]
  exact eq_bot_iff.mpr (hgen.trans (iSup_le fun t => iSup_le fun ht => iSup_le fun ht1 =>
    (hterm t ht ht1).le))

theorem autCfg_false_of_inner {Y : Type} [Group Y] [Finite Y]
    {α : MulAut Y} {p : ℕ} {X : Subgroup (MulAut Y)} (h : AutCfg Y α p X)
    (hXI : X ⊓ innSub Y = ⊥) (hαI : α ∈ innSub Y) : False := by
  have hIn : (innSub Y).Normal := inferInstanceAs ((inner Y).Normal)
  have hcX : ∀ x ∈ X, α * x = x * α := by
    intro x hx
    have hmem : α * x * α⁻¹ * x⁻¹ ∈ X ⊓ innSub Y := by
      refine ⟨X.mul_mem ((mem_normalizer_iff.mp h.alpha_norm x).mp hx) (X.inv_mem hx), ?_⟩
      have := (innSub Y).mul_mem hαI (hIn.conj_mem α⁻¹ ((innSub Y).inv_mem hαI) x)
      simpa [mul_assoc] using this
    rw [hXI, Subgroup.mem_bot] at hmem
    calc α * x = α * x * α⁻¹ * x⁻¹ * x * α := by group
      _ = x * α := by rw [hmem]; group
  have hbot : ⁅X, zpowers α⁆ = ⊥ := by
    rw [commutator_eq_bot_iff_le_centralizer]
    intro x hx
    rw [mem_centralizer_iff]
    intro g hg
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
    exact (Commute.zpow_left (hcX x hx) m).eq
  exact h.ne_bot (by rw [← h.comm, hbot])

theorem autCfg_card_dvd_outer {Y : Type} [Group Y] [Finite Y]
    {X : Subgroup (MulAut Y)} (hXI : X ⊓ innSub Y = ⊥) :
    Nat.card ↥X ∣ Nat.card (Outer Y) := by
  let φ : ↥X →* Outer Y := (QuotientGroup.mk' (inner Y)).comp X.subtype
  have hφ : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxI : (x : MulAut Y) ∈ inner Y := (QuotientGroup.eq_one_iff _).mp hx
    have : (x : MulAut Y) ∈ X ⊓ innSub Y := ⟨x.2, hxI⟩
    rw [hXI, Subgroup.mem_bot] at this
    exact Subtype.ext this
  exact Subgroup.card_dvd_of_injective φ hφ

end CFSG.GH74.GLS.Stage2.Signalizer.Odd87
