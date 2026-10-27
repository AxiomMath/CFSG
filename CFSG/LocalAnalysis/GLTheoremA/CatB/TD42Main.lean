module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD42Cls
public import CFSG.LocalAnalysis.GLTheoremA.CatB.TD42Words
public import CFSG.LocalAnalysis.GLTheoremA.CatB.I269Red
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.RankThree.PartTwo.Sec4.Item434D42 CFSG.Quasithin CFSG.AGLEmbedding.ChevOuter
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace TD42

theorem isSolvable_of_card_dvd {G : Type*} [Group G] [Finite G] {a b : ℕ}
    (h : Nat.card G ∣ 2 ^ a * 3 ^ b) : Group.IsSolvable G := by
  apply CFSG.LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
  have hsub : (Nat.card G).primeFactors ⊆ ({2, 3} : Finset ℕ) := by
    intro p hp
    rw [Nat.mem_primeFactors] at hp
    obtain ⟨hpp, hdvd, -⟩ := hp
    have h2 : p ∣ 2 ^ a * 3 ^ b := hdvd.trans h
    rcases (Nat.Prime.dvd_mul hpp).1 h2 with h3 | h3
    · have := hpp.dvd_of_dvd_pow h3
      rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 this]
      simp
    · have := hpp.dvd_of_dvd_pow h3
      rw [(Nat.prime_dvd_prime_iff_eq hpp Nat.prime_three).1 this]
      simp
  calc (Nat.card G).primeFactors.card ≤ ({2, 3} : Finset ℕ).card := Finset.card_le_card hsub
    _ = 2 := by decide

theorem factorization_seven : (1512 : ℕ).factorization 7 = 1 := by
  rw [show (1512 : ℕ) = 7 ^ 1 * 216 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow (by norm_num), Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

section K3

theorem false_of_fixed_order_seven
    (hT : Nat.card lineGroup = 211341312) (hZ : Subgroup.center lineGroup = ⊥)
    (hQ : Nat.card (Outer lineGroup) = 3) {E : Subgroup (MulAut lineGroup)}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 9) {y : lineGroup} (hy7 : orderOf y = 7)
    (h1 : frobF (trT y) ≠ trT y) (h2 : frobF (frobF (trT y)) ≠ trT y)
    (hfix : ∀ α ∈ E, α y = y) : False := by
  have hinj := conj_injective hZ
  have hinner : ∀ α ∈ E, α ∈ (MulAut.conj : lineGroup →* MulAut lineGroup).range := fun α hα => by
    obtain ⟨g, rfl⟩ := inner_of_fixed_trace hQ y h1 h2 (hfix α hα)
    exact ⟨g, rfl⟩
  set Ei : Subgroup lineGroup := E.comap (MulAut.conj : lineGroup →* MulAut lineGroup) with hEidef
  have hmap : Ei.map (MulAut.conj : lineGroup →* MulAut lineGroup) = E :=
    Subgroup.map_comap_eq_self hinner
  have hcardEi : Nat.card Ei = 9 := by
    have := Subgroup.card_map_of_injective (K := Ei) hinj
    rw [hmap, hcard] at this
    exact this.symm
  have hEi3 : IsElemAbelian 3 Ei := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · have ha : (MulAut.conj (a : lineGroup)) ∈ E := a.2
      have hb : (MulAut.conj (b : lineGroup)) ∈ E := b.2
      have hc : (MulAut.conj (a : lineGroup)) * MulAut.conj (b : lineGroup) =
          MulAut.conj (b : lineGroup) * MulAut.conj (a : lineGroup) :=
        congrArg Subtype.val (hE.1.is_comm.comm ⟨_, ha⟩ ⟨_, hb⟩)
      apply Subtype.ext
      show (a : lineGroup) * b = b * a
      apply hinj
      rw [map_mul, map_mul]
      exact hc
    · apply hinj
      rw [map_pow, map_one]
      exact hE.2 _ hx
  have hEW : Ei ≤ Subgroup.normalizer ((Subgroup.zpowers y : Subgroup lineGroup) : Set lineGroup) := by
    intro g hg
    have hfixg : (MulAut.conj g) y = y := hfix _ hg
    have hgy : Commute g y := by
      have h3 : g * y * g⁻¹ = y := hfixg
      show g * y = y * g
      calc g * y = g * y * g⁻¹ * g := by group
        _ = y * g := by rw [h3]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact (hgy.zpow_right k).eq.symm
  have hW : ¬ 3 ∣ Nat.card (Subgroup.zpowers y) := by
    rw [Nat.card_zpowers, hy7]
    norm_num
  have hbot := CFSG.RankThree.PartTwo.Sec4.Item434D42.d4_k3_of_equiv
    (MulEquiv.subgroupCongr lineGroup_eq) hT hEi3 hcardEi hW hEW
  have hmem : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
  rw [hbot, Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hy7
  norm_num at hy7

end K3

section Sylow

theorem trace_ne_of_commute_is3A
    (hT : Nat.card lineGroup = 211341312) {s y : lineGroup}
    (hs : Is3A s) (hy7 : orderOf y = 7) (hys : y * s = s * y) :
    frobF (trT y) ≠ trT y ∧ frobF (frobF (trT y)) ≠ trT y := by
  have h3A0 : Is3A s0 := by
    rcases is3A_or_card648 hT s0 orderOf_s0 with h | h
    · exact h
    · exfalso
      have hy0 : y0 ∈ Subgroup.centralizer ({s0} : Set lineGroup) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact commute_y0_s0
      have := Subgroup.orderOf_dvd_natCard _ hy0
      rw [orderOf_y0, h] at this
      norm_num at this
  obtain ⟨g, hg⟩ := exists_conj_of_is3A hT hs h3A0
  set D : Subgroup lineGroup := Subgroup.centralizer ({s} : Set lineGroup) with hD
  have hDcard : Nat.card D = 1512 := card_centralizer_of_is3A hT hs
  have hDeq : Subgroup.centralizer ({g * s0 * g⁻¹} : Set lineGroup) = D := by
    rcases hg with h | h
    · rw [h]
    · rw [h, centralizer_inv]
  set y' : lineGroup := g * y0 * g⁻¹ with hy'
  have hy'D : y' ∈ D := by
    rw [← hDeq, centralizer_conj]
    refine ⟨y0, ?_, ?_⟩
    · exact Subgroup.mem_centralizer_singleton_iff.2 commute_y0_s0
    · simp [MulAut.conj_apply, hy']
  have hy'7 : orderOf y' = 7 := by
    have := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y0
    rw [orderOf_y0] at this
    simpa [MulAut.conj_apply, hy'] using this
  have hyD : y ∈ D := by
    rw [hD, Subgroup.mem_centralizer_singleton_iff]
    exact hys
  have hzle : Subgroup.zpowers y' ≤ D := by
    rw [Subgroup.zpowers_le]
    exact hy'D
  have hzcard : Nat.card (Subgroup.zpowers y') = 7 ^ (Nat.card D).factorization 7 := by
    rw [Nat.card_zpowers, hy'7, hDcard, factorization_seven, pow_one]
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨h, hhD, hmem⟩ := CFSG.RankThree.PartTwo.KFacts.K426.exists_conj_mem_of_card hzle hzcard hyD hy7
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hy0k : y0 ^ k = y0 ^ (k % 7).toNat := by
    rw [zpow_eq_zpow_emod k (n := 7) (by exact_mod_cast y0_pow_seven)]
    have : (0 : ℤ) ≤ k % 7 := Int.emod_nonneg k (by norm_num)
    rw [← zpow_natCast, Int.toNat_of_nonneg this]
  have hyeq : y = (h * g) * y0 ^ (k % 7).toNat * (h * g)⁻¹ := by
    have h1 : y = h * y' ^ k * h⁻¹ := by rw [hk]; group
    rw [h1, hy', conj_zpow, hy0k]
    group
  have hn : ¬ 7 ∣ (k % 7).toNat := by
    intro h7
    obtain ⟨c, hc⟩ := h7
    have : y0 ^ (k % 7).toNat = 1 := by rw [hc, pow_mul, y0_pow_seven, one_pow]
    rw [this] at hyeq
    have hy1 : y = 1 := by rw [hyeq]; group
    rw [hy1, orderOf_one] at hy7
    norm_num at hy7
  have htr : trT y = trT (y0 ^ (k % 7).toNat) := by
    rw [hyeq, trT_conj]
  rw [htr]
  exact trT_y0_pow _ hn

end Sylow

section Main

local instance factPrimeThreeMain : Fact (Nat.Prime 3) := ⟨by norm_num⟩
local instance factPrimeSevenMain : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem e9Solv_lineGroup
    (hT : Nat.card lineGroup = 211341312) (hZ : Subgroup.center lineGroup = ⊥)
    (hA : Nat.card (MulAut lineGroup) = 3 * 211341312) : E9Solv lineGroup := by
  have hQ : Nat.card (Outer lineGroup) = 3 := card_outer hZ hT hA (by norm_num)
  intro E hE hcard
  obtain ⟨s, hs1, hs3, hsE⟩ := exists_inner_of_card_nine hZ hQ hE hcard
  have hso : orderOf s = 3 := orderOf_eq_prime hs3 hs1
  have hle : i269Fix E ≤ Subgroup.centralizer ({s} : Set lineGroup) := by
    intro x hx
    rw [mem_i269Fix] at hx
    have h' : s * x * s⁻¹ = x := hx _ hsE
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc x * s = (s * x * s⁻¹) * s := by rw [h']
      _ = s * x := by group
  rcases is3A_or_card648 hT s hso with h3A | h648
  · have hD : Nat.card (Subgroup.centralizer ({s} : Set lineGroup)) = 1512 :=
      card_centralizer_of_is3A hT h3A
    have hCdvd : Nat.card (i269Fix E) ∣ 216 * 7 := by
      have := Subgroup.card_dvd_of_le hle
      rw [hD] at this
      simpa using this
    have h7 : ¬ 7 ∣ Nat.card (i269Fix E) := by
      intro h7
      obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(i269Fix E)) 7 h7
      have hy7 : orderOf (y : lineGroup) = 7 := by rw [Subgroup.orderOf_coe]; exact hy
      have hyE : ∀ α ∈ E, α (y : lineGroup) = y := mem_i269Fix.1 y.2
      have hyC : (y : lineGroup) * s = s * y :=
        Subgroup.mem_centralizer_singleton_iff.1 (hle y.2)
      obtain ⟨h1, h2⟩ := trace_ne_of_commute_is3A hT h3A hy7 hyC
      exact false_of_fixed_order_seven hT hZ hQ hE hcard hy7 h1 h2 hyE
    have hcop : Nat.Coprime (Nat.card (i269Fix E)) 7 :=
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 h7).symm
    exact isSolvable_of_card_dvd (a := 3) (b := 3) (by simpa using hcop.dvd_of_dvd_mul_right hCdvd)
  · have hCdvd : Nat.card (i269Fix E) ∣ 2 ^ 3 * 3 ^ 4 := by
      have := Subgroup.card_dvd_of_le hle
      rw [h648] at this
      simpa using this
    exact isSolvable_of_card_dvd hCdvd

end Main

end TD42

end CFSG.LocalAnalysis.GLTheoremA

end
