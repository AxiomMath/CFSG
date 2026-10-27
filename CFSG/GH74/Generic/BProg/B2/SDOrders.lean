module

public import CFSG.GH74.Generic.BProg.B1.Stage3aRank

import CFSG.GH74.KGroups.M11
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.GH74.Generic.BProg.B2.SD2

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.GH74.Uniqueness
  CFSG.ABGLocalTools CFSG.Blueprint CFSG.Assembly.LowTwoRank Subgroup

@[expose] def SmallLie (J : Type) [Group J] : Prop :=
  (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ LieModel (J ⧸ center J) .PSL 2 p f) ∨
    LieModel (J ⧸ center J) .PSL 3 3 1 ∨ QShape3 (J ⧸ center J)

@[expose] def SmallAut (J : Type) [Group J] : Prop :=
  Nonempty (J ⧸ center J ≃* alternatingGroup (Fin 7)) ∨ NativeSporadic.IsSporadic (J ⧸ center J) .M11

@[expose] def SmallComp (J : Type) [Group J] : Prop := SmallLie J ∨ SmallAut J

theorem eq_one_of_card_lt {K T : Type} [Group K] [Finite K] [Group T] [Finite T]
    (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤) (hsimp : IsSimpleGroup (K ⧸ pPrimeCore 2 K))
    (hcard : Nat.card T < Nat.card (K ⧸ pPrimeCore 2 K)) (ψ : K →* T) : ψ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect K := Group.isPerfect_def.2 hperf
  set O : Subgroup K := pPrimeCore 2 K with hO
  have hNn : (ψ.ker.map (QuotientGroup.mk' O)).Normal :=
    (inferInstance : ψ.ker.Normal).map _ (QuotientGroup.mk'_surjective O)
  rcases hsimp.eq_bot_or_eq_top_of_normal (ψ.ker.map (QuotientGroup.mk' O)) with h | h
  ·
    exfalso
    have hle : ψ.ker ≤ O := by
      have := (Subgroup.map_eq_bot_iff _).1 h
      simpa using this
    have h1 : Nat.card (K ⧸ O) ≤ Nat.card (K ⧸ ψ.ker) := by
      have : O.index ∣ ψ.ker.index := Subgroup.index_dvd_of_le hle
      exact Nat.le_of_dvd (Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite) this
    have h2 : Nat.card (K ⧸ ψ.ker) ≤ Nat.card T :=
      Nat.card_le_card_of_injective _ (QuotientGroup.kerLift_injective ψ)
    omega
  ·
    have hmap : O.map ψ = ψ.range := by
      refine le_antisymm (fun y hy => ?_) (fun y hy => ?_)
      · obtain ⟨o, -, rfl⟩ := hy
        exact ⟨o, rfl⟩
      · obtain ⟨k, rfl⟩ := hy
        have hk : QuotientGroup.mk' O k ∈ ψ.ker.map (QuotientGroup.mk' O) := by rw [h]; trivial
        obtain ⟨n, hn, hnk⟩ := hk
        refine ⟨n⁻¹ * k, ?_, ?_⟩
        · exact (QuotientGroup.eq (a := n) (b := k)).1 hnk
        · rw [map_mul, map_inv, hn, inv_one, one_mul]
    have hdvd : Nat.card (O.map ψ) ∣ Nat.card O := Subgroup.card_map_dvd O ψ
    rw [hmap] at hdvd
    have hOodd : Odd (Nat.card O) :=
      Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := K))
    have hodd : Odd (Nat.card ψ.range) := Odd.of_dvd_nat hOodd hdvd
    have hsolv : Group.IsSolvable ψ.range := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    have : Group.IsPerfect ψ.range := Group.IsPerfect.range ψ
    have hsub : Subsingleton ψ.range := by
      by_contra hns
      have : Nontrivial ψ.range := not_subsingleton_iff_nontrivial.1 hns
      exact Group.IsPerfect.not_isSolvable ψ.range hsolv
    ext k
    have h1 : (⟨ψ k, k, rfl⟩ : ψ.range) = 1 := Subsingleton.elim _ _
    simpa using congrArg Subtype.val h1

theorem card_mulAut_le_of_smallAut {J : Type} [Group J] [Finite J]
    (hJ : SmallAut J) : Nat.card (MulAut (J ⧸ center J)) ≤ 7920 := by
  rcases hJ with ⟨⟨e⟩⟩ | h
  ·
    have h1 : Nat.card (MulAut (J ⧸ center J)) = Nat.card (MulAut (alternatingGroup (Fin 7))) :=
      Nat.card_congr (MulAut.congr e).toEquiv
    have hb := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
      (by norm_num) (by norm_num)
    have h2 : Nat.card (Equiv.Perm (Fin 7)) = Nat.card (MulAut (alternatingGroup (Fin 7))) :=
      Nat.card_congr (Equiv.ofBijective _ hb)
    have h3 : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      rfl
    omega
  · exact (KGroups.M11.card_mulAut h).le

namespace SDOrders

open CFSG.Open (ordA ordTwistedA)

theorem prod_Icc_two_three {M : Type*} [CommMonoid M] (f : ℕ → M) :
    ∏ i ∈ Finset.Icc 2 3, f i = f 2 * f 3 := by
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)]

theorem pow_bounds {q : ℕ} (hq : 3 < q) : 64 ≤ q ^ 3 ∧ 16 ≤ q ^ 2 := by
  have h4 : 4 ≤ q := hq
  exact ⟨(by norm_num : 64 = 4 ^ 3) ▸ Nat.pow_le_pow_left h4 3,
    (by norm_num : 16 = 4 ^ 2) ▸ Nat.pow_le_pow_left h4 2⟩

theorem lt_ordA {q : ℕ} (hq : 3 < q) : 7920 < ordA 2 q := by
  unfold ordA
  rw [prod_Icc_two_three]
  have hg0 : 0 < Nat.gcd (2 + 1) (q - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd (2 + 1) (q - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  obtain ⟨h3, h2⟩ := pow_bounds hq
  show 7921 ≤ _
  rw [Nat.le_div_iff_mul_le hg0, show 2 * (2 + 1) / 2 = 3 by norm_num]
  calc 7921 * Nat.gcd (2 + 1) (q - 1) ≤ 64 * (15 * 63) := by omega
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))

theorem lt_ordTwistedA {q : ℕ} (hq : 3 < q) : 7920 < ordTwistedA 2 q := by
  unfold ordTwistedA
  rw [prod_Icc_two_three]
  have hg0 : 0 < Nat.gcd (2 + 1) (q + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have hg3 : Nat.gcd (2 + 1) (q + 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  obtain ⟨h3, h2⟩ := pow_bounds hq
  have e2 : ((q : ℤ) ^ 2 - (-1) ^ 2).toNat = q ^ 2 - 1 := by
    have : ((q : ℤ) ^ 2 - (-1) ^ 2) = ((q ^ 2 - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this, Int.toNat_natCast]
  have e3 : ((q : ℤ) ^ 3 - (-1) ^ 3).toNat = q ^ 3 + 1 := by
    have : ((q : ℤ) ^ 3 - (-1) ^ 3) = ((q ^ 3 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  show 7921 ≤ _
  rw [Nat.le_div_iff_mul_le hg0, e2, e3, show 2 * (2 + 1) / 2 = 3 by norm_num]
  calc 7921 * Nat.gcd (2 + 1) (q + 1) ≤ 64 * (15 * 65) := by omega
    _ ≤ q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 + 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))

end SDOrders

theorem lt_card_of_qShape3SD {Kt : Type} [Group Kt] [Finite Kt] (h : B1.QShape3SD Kt) :
    7920 < Nat.card Kt := by
  obtain ⟨p, f, hp, hp2, hq, h | h⟩ := h
  · rw [card_of_lieModel_PSL (by norm_num) h.1]
    exact SDOrders.lt_ordA hq
  · rw [card_of_lieModel_PSU (by norm_num) hp2 h.1]
    exact SDOrders.lt_ordTwistedA hq

namespace SDOrders

theorem eq_one_of_smallAut {K J : Type} [Group K] [Finite K] [Group J]
    [Finite J] (hperf : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤)
    (hsimp : IsSimpleGroup (K ⧸ pPrimeCore 2 K)) (hshape : B1.QShape3SD (K ⧸ pPrimeCore 2 K))
    (hJ : SmallAut J) (ψ : K →* MulAut (J ⧸ center J)) : ψ = 1 :=
  eq_one_of_card_lt hperf hsimp
    ((card_mulAut_le_of_smallAut hJ).trans_lt (lt_card_of_qShape3SD hshape)) ψ

end SDOrders

end CFSG.GH74.Generic.BProg.B2.SD2
