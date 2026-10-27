module

public import CFSG.ClassicalInvolution.LBalance.Glauberman.PartBCore
public import CFSG.ClassicalInvolution.LBalance.Glauberman.OddActionLemma
public import CFSG.FeitThompson.OddOrderTheorem
public import Mathlib.Data.Int.Star

public section

namespace CFSG.ClassicalInvolution.GlaubermanAut

open CFSG.ABGLocalTools

section TwoPart

theorem exists_two_part_odd_part {X : Type*} [Group X] [Finite X] (y : X) :
    ∃ a b : X, y = a * b ∧ a ∈ Subgroup.zpowers y ∧ b ∈ Subgroup.zpowers y ∧
      (∃ k : ℕ, orderOf a = 2 ^ k) ∧ Odd (orderOf b) := by
  have hn : orderOf y ≠ 0 := (orderOf_pos y).ne'
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd hn
  have hcop : IsCoprime (m : ℤ) ((2 ^ k : ℕ) : ℤ) :=
    Nat.Coprime.isCoprime ((Nat.Coprime.pow_right k hm.coprime_two_right))
  obtain ⟨i, j, hij⟩ := hcop
  have hy1 : y ^ (orderOf y) = 1 := pow_orderOf_eq_one y
  refine ⟨(y ^ m) ^ i, (y ^ (2 ^ k)) ^ j, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add]
    have : (i * (m : ℤ) + j * ((2 ^ k : ℕ) : ℤ)) = 1 := by linarith
    rw [show (m : ℤ) * i + ((2 ^ k : ℕ) : ℤ) * j = 1 by linarith, zpow_one]
  · exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) m) i
  · exact Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers y) _) j
  · have h1 : ((y ^ m) ^ i) ^ (2 ^ k) = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul,
        mul_comm m, ← hkm, hy1, one_zpow]
    obtain ⟨l, -, hl⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one h1)
    exact ⟨l, hl⟩
  · have h1 : ((y ^ (2 ^ k)) ^ j) ^ m = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← pow_mul,
        ← hkm, hy1, one_zpow]
    exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one h1)

end TwoPart

section NormalSylow

variable {X : Type*} [Group X] [Finite X]

theorem mem_sylow_of_mem_normalizer_of_orderOf (P : Sylow 2 X) {a : X}
    (ha : a ∈ Subgroup.normalizer ((P : Subgroup X) : Set X)) {k : ℕ} (hk : orderOf a = 2 ^ k) :
    a ∈ (P : Subgroup X) := by
  set M : Subgroup X := Subgroup.normalizer ((P : Subgroup X) : Set X) with hM
  have hPM : IsSylowOf 2 (P : Subgroup X) M := by
    rw [isSylowOf_iff]
    refine ⟨Subgroup.le_normalizer, P.isPGroup', fun hd => P.not_dvd_index ?_⟩
    exact hd.trans (Subgroup.relIndex_dvd_index_of_le Subgroup.le_normalizer)
  have hZp : IsPGroup 2 (Subgroup.zpowers a) :=
    IsPGroup.iff_card.2 ⟨k, by rw [Nat.card_zpowers, hk]⟩
  obtain ⟨T, hZT, hT⟩ := exists_isSylowOf_ge hZp (Subgroup.zpowers_le.2 ha)
  obtain ⟨m, hm, hconj⟩ := isSylowOf_exists_conj hPM hT
  have h1 : m⁻¹ * a * m ∈ (P : Subgroup X) := (hconj a).1 (hZT (Subgroup.mem_zpowers a))
  have h2 := (Subgroup.mem_normalizer_iff.1 hm (m⁻¹ * a * m)).1 h1
  have e : m * (m⁻¹ * a * m) * m⁻¹ = a := by group
  rwa [e] at h2

end NormalSylow

section PartBMain

variable {G : Type} [Group G] [Finite G] {S : Subgroup G}

theorem sylow_comm (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (P : Sylow 2 (sylowFixingAut S)) :
    ∀ x y : P, x * y = y * x := by
  set A₀ : Subgroup (MulAut G) :=
    (P : Subgroup (sylowFixingAut S)).map (sylowFixingAut S).subtype with hA₀
  have hfix : ∀ α ∈ A₀, ∀ s ∈ S, α s = s := by
    rintro _ ⟨p, -, rfl⟩ s hs
    exact mem_sylowFixingAut.1 p.2 s hs
  have hAp : IsPGroup 2 A₀ := P.isPGroup'.map (sylowFixingAut S).subtype
  intro x y
  have h0 := isMulCommutative_of_isPGroup_two hG hSp hSi hfix hAp ⟨x.1.1, ⟨x.1, x.2, rfl⟩⟩
    ⟨y.1.1, ⟨y.1, y.2, rfl⟩⟩
  have h1 : ((x : sylowFixingAut S) : MulAut G) * ((y : sylowFixingAut S) : MulAut G) =
      ((y : sylowFixingAut S) : MulAut G) * ((x : sylowFixingAut S) : MulAut G) :=
    congrArg Subtype.val h0
  exact Subtype.ext (Subtype.ext h1)

theorem odd_mem_centralizer (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (P : Sylow 2 (sylowFixingAut S))
    (hcomm : ∀ x y : P, x * y = y * x) {b : sylowFixingAut S}
    (hb : b ∈ Subgroup.normalizer ((P : Subgroup (sylowFixingAut S)) : Set (sylowFixingAut S)))
    (hodd : Odd (orderOf b)) :
    b ∈ Subgroup.centralizer ((P : Subgroup (sylowFixingAut S)) : Set (sylowFixingAut S)) := by
  by_contra hbc
  set A₀ : Subgroup (MulAut G) :=
    (P : Subgroup (sylowFixingAut S)).map (sylowFixingAut S).subtype with hA₀
  have hcomm0 : ∀ a ∈ A₀, ∀ c ∈ A₀, a * c = c * a := by
    rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
    show (p : MulAut G) * (q : MulAut G) = (q : MulAut G) * (p : MulAut G)
    exact congrArg (fun t : P => ((t : sylowFixingAut S) : MulAut G)) (hcomm ⟨p, hp⟩ ⟨q, hq⟩)
  have hp0 : IsPGroup 2 A₀ := P.isPGroup'.map (sylowFixingAut S).subtype
  set x : MulAut G := (b : MulAut G) with hx
  have hxA : ∀ a ∈ A₀, x * a * x⁻¹ ∈ A₀ := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨b * p * b⁻¹, (Subgroup.mem_normalizer_iff.1 hb p).1 hp, rfl⟩
  have hxA' : ∀ a ∈ A₀, x⁻¹ * a * x ∈ A₀ := by
    rintro _ ⟨p, hp, rfl⟩
    refine ⟨b⁻¹ * p * b, ?_, rfl⟩
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hb) p).1 hp
    rw [inv_inv] at this
    exact this
  have hxodd : Odd (orderOf x) := by
    rwa [hx, Subgroup.orderOf_coe]
  have hnc : ∃ a ∈ A₀, x * a ≠ a * x := by
    rw [Subgroup.mem_centralizer_iff] at hbc
    push Not at hbc
    obtain ⟨z, hz, hzb⟩ := hbc
    exact ⟨(z : MulAut G), ⟨z, hz, rfl⟩, fun h => hzb (Subtype.ext h.symm)⟩
  obtain ⟨U, hUA, hUsq, hUx, hUne, hU5⟩ :=
    exists_elementary_commutator_subgroup hcomm0 hp0 hxA hxA' hxodd hnc
  refine partB_core hG hSp hSi (U := U) (x := x) ?_ ?_ hUsq ?_ hUx hUne hU5 hxodd
  · intro u hu s hs
    obtain ⟨p, -, rfl⟩ := hUA hu
    exact mem_sylowFixingAut.1 p.2 s hs
  · intro s hs
    exact mem_sylowFixingAut.1 b.2 s hs
  · intro u hu v hv
    exact hcomm0 u (hUA hu) v (hUA hv)

theorem normalizer_le_centralizer (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) (P : Sylow 2 (sylowFixingAut S)) :
    Subgroup.normalizer ((P : Subgroup (sylowFixingAut S)) : Set (sylowFixingAut S)) ≤
      Subgroup.centralizer ((P : Subgroup (sylowFixingAut S)) : Set (sylowFixingAut S)) := by
  have hcomm := sylow_comm hG hSp hSi P
  intro y hy
  obtain ⟨a, b, hyab, haZ, hbZ, ⟨k, hk⟩, hbodd⟩ := exists_two_part_odd_part y
  have hzN : Subgroup.zpowers y ≤
      Subgroup.normalizer ((P : Subgroup (sylowFixingAut S)) : Set (sylowFixingAut S)) :=
    Subgroup.zpowers_le.2 hy
  have ha := hzN haZ
  have hb := hzN hbZ
  have haP : a ∈ (P : Subgroup (sylowFixingAut S)) :=
    mem_sylow_of_mem_normalizer_of_orderOf P ha hk
  have hbc := odd_mem_centralizer hG hSp hSi P hcomm hb hbodd
  rw [hyab, Subgroup.mem_centralizer_iff]
  intro z hz
  have h1 : z * a = a * z := congrArg (fun t : P => (t : sylowFixingAut S)) (hcomm ⟨z, hz⟩ ⟨a, haP⟩)
  have h2 : z * b = b * z := Subgroup.mem_centralizer_iff.1 hbc z hz
  calc z * (a * b) = (z * a) * b := by group
    _ = (a * z) * b := by rw [h1]
    _ = a * (z * b) := by group
    _ = a * (b * z) := by rw [h2]
    _ = a * b * z := by group

theorem exists_normal_two_complement
    (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) :
    ∃ N : Subgroup (sylowFixingAut S), ∃ _ : N.Normal, Odd (Nat.card N) ∧
      IsPGroup 2 (sylowFixingAut S ⧸ N) := by
  obtain ⟨P⟩ : Nonempty (Sylow 2 (sylowFixingAut S)) := inferInstance
  have hP := normalizer_le_centralizer hG hSp hSi P
  refine ⟨(MonoidHom.transferSylow P hP).ker, MonoidHom.normal_ker _, ?_, ?_⟩
  · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (MonoidHom.not_dvd_card_ker_transferSylow P hP))
  · have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
    have h1 : (MonoidHom.transferSylow P hP).ker.index = Nat.card P := hcompl.symm.index_eq_card
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 P.isPGroup'
    exact IsPGroup.iff_card.2 ⟨k, by rw [← Subgroup.index_eq_card, h1]; exact hk⟩

theorem isSolvable_sylowFixingAut
    (hG : ∀ N : Subgroup G, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hSp : IsPGroup 2 S) (hSi : ¬ 2 ∣ S.index) : Group.IsSolvable (sylowFixingAut S) := by
  obtain ⟨N, hN, hodd, hq⟩ := exists_normal_two_complement hG hSp hSi
  have := hN
  have : Group.IsSolvable N := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : Group.IsNilpotent (sylowFixingAut S ⧸ N) := hq.isNilpotent
  have : Group.IsSolvable (sylowFixingAut S ⧸ N) := inferInstance
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by simp)

end PartBMain

end CFSG.ClassicalInvolution.GlaubermanAut
