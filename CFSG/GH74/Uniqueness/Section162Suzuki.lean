module

public import CFSG.GH74.Uniqueness.Bender.Suzuki

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup

theorem three_dvd_unitary_card (m e : ℕ) :
    3 ∣ ((2 ^ m) ^ 3 + 1) * ((2 ^ m) ^ 3 * ((2 ^ m - 1) * e)) := by
  have hmod : 2 ^ m % 3 = 1 ∨ 2 ^ m % 3 = 2 := by
    have : ¬ 3 ∣ 2 ^ m := fun hd => by
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
      omega
    omega
  rcases hmod with hm | hm
  · have hd : 3 ∣ 2 ^ m - 1 := by omega
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_left (Dvd.dvd.mul_right hd e) _) _
  · have h3 : (2 ^ m) ^ 3 % 3 = 2 := by rw [Nat.pow_mod, hm]
    have hd : 3 ∣ (2 ^ m) ^ 3 + 1 := by omega
    exact Dvd.dvd.mul_right hd _

theorem BenderType.rootCenter_sup_zpowers_suzuki
    {K : Type} [Group K] [Finite K] {n e : ℕ}
    (h : BenderType K n 2 e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) :
    rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t = ⊤ := by
  have he : e = 1 := by
    rcases h.cases' with ⟨hi, -, -⟩ | ⟨-, he, -⟩ | ⟨hi, -, -⟩
    · omega
    · exact he
    · omega
  subst he
  have hc := h.benderCore Q ht htQ
  have hsimple : IsSimpleGroup K := h.isSimple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha, hn⟩ : ∃ a, 1 ≤ a ∧ n = 2 * a + 1 := by
    rcases h.cases' with ⟨hi, -, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨hi, -, -⟩
    · omega
    · exact ⟨a, ha, hn⟩
    · omega
  set L : Subgroup K := rootCenter (Q : Subgroup K) ⊔ Subgroup.zpowers t with hL
  have hZL : rootCenter (Q : Subgroup K) ≤ L := le_sup_left
  have htL : t ∈ L := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  obtain ⟨z, hz, hz1⟩ := hc.exists_involution
  have hzL : z ∈ L := hZL hz
  have hz2 : orderOf z = 2 := by
    apply orderOf_eq_prime _ hz1
    rw [sq]
    exact hc.center_sq z hz
  have hMX : IsStronglyEmbedded ((borel (Q : Subgroup K) ⊓ L).subgroupOf L) :=
    isStronglyEmbedded_subgroupOf hc.strong (le_borel _ (rootCenter_le _ hz)) hzL hz2 htL htQ
  set ZL : Subgroup ↥L := (rootCenter (Q : Subgroup K)).subgroupOf L with hZLdef
  have hZLcard : Nat.card ZL = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv, hc.card_center]
  have hZsq : ∀ x : ↥L, x ∈ ZL → x * x = 1 := by
    intro x hx
    exact Subtype.ext (hc.center_sq _ hx)
  have hE : CFSG.Open.IsElemAbelian 2 ZL := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply Subtype.ext
      have hx' := mem_rootCenter_iff.mp x.2
      have hy' := mem_rootCenter_iff.mp y.2
      exact hy'.2 _ hx'.1
    · rw [sq]
      exact hZsq x hx
  have hEle : ZL ≤ involutionClosure ↥L := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · apply Subgroup.subset_closure
      show orderOf x = 2
      apply orderOf_eq_prime _ hx1
      rw [sq]
      exact hZsq x hx
  have hkey : 2 ^ (2 * n) ∣ Nat.card L := by
    rcases S_SE_proof ↥L _ hMX with hrank | ⟨hBender, -, -⟩
    · exfalso
      have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hEle hE hZLcard
      omega
    · obtain ⟨n', i', e', hS⟩ := isBenderGroup_iff_exists_benderType.mp hBender
      set Xc : Subgroup ↥L := involutionClosure ↥L with hXc
      have hdvdK : Nat.card (↥Xc ⧸ pPrimeCore 2 ↥Xc) ∣ Nat.card K :=
        (Subgroup.card_quotient_dvd_card _).trans
          ((Subgroup.card_subgroup_dvd_card Xc).trans (Subgroup.card_subgroup_dvd_card L))
      have hK3 : ¬ 3 ∣ Nat.card K := by
        rw [h.card_eq, hn]
        exact not_three_dvd_sz_card a
      have hi' : i' = 2 := by
        rcases hS.cases' with ⟨rfl, rfl, -⟩ | ⟨hi, -, -⟩ | ⟨rfl, -, -⟩
        · exfalso
          apply hK3
          refine Dvd.dvd.trans ?_ hdvdK
          rw [hS.card_eq]
          exact three_dvd_linear_card n'
        · exact hi
        · exfalso
          apply hK3
          refine Dvd.dvd.trans ?_ hdvdK
          rw [hS.card_eq]
          exact three_dvd_unitary_card n' e'
      subst hi'
      have hnn' : n ≤ n' := by
        let f : ↥ZL →* ↥Xc ⧸ pPrimeCore 2 ↥Xc :=
          (QuotientGroup.mk' (pPrimeCore 2 ↥Xc)).comp (Subgroup.inclusion hEle)
        have hf : Function.Injective f := by
          rw [injective_iff_map_eq_one]
          intro x hx
          have hmem : Subgroup.inclusion hEle x ∈ pPrimeCore 2 ↥Xc :=
            (QuotientGroup.eq_one_iff _).mp hx
          have hodd : Odd (Nat.card (pPrimeCore 2 ↥Xc)) :=
            Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h2 =>
              (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
                (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥Xc)) h2)
          have hord : orderOf (⟨_, hmem⟩ : pPrimeCore 2 ↥Xc) ∣ 2 := by
            apply orderOf_dvd_of_pow_eq_one
            apply Subtype.ext
            apply Subtype.ext
            apply Subtype.ext
            simp only [Subgroup.coe_pow, Subgroup.coe_inclusion, Subgroup.coe_one]
            rw [sq]
            exact congrArg Subtype.val (hZsq x.1 x.2)
          have hord2 : orderOf (⟨_, hmem⟩ : pPrimeCore 2 ↥Xc) ∣ Nat.card (pPrimeCore 2 ↥Xc) :=
            orderOf_dvd_natCard _
          have h1 : orderOf (⟨_, hmem⟩ : pPrimeCore 2 ↥Xc) = 1 := by
            rcases (Nat.dvd_prime Nat.prime_two).mp hord with h1 | h1
            · exact h1
            · rw [h1] at hord2
              exact absurd (even_iff_two_dvd.mpr hord2) (Nat.not_even_iff_odd.mpr hodd)
          have h1' := orderOf_eq_one_iff.mp h1
          apply Subtype.ext
          have := congrArg (fun y : pPrimeCore 2 ↥Xc => (((y : ↥Xc) : ↥L) : K)) h1'
          simpa using this
        have hcomm : ∀ x y : ↥ZL, x * y = y * x := fun x y => hE.1.is_comm.comm x y
        have hpow : ∀ x : ↥ZL, x ^ 2 = 1 := fun x => by
          rw [sq]
          exact Subtype.ext (hZsq x.1 x.2)
        have h1 := CFSG.SectionRank.le_pRank_of_injective (by norm_num : 1 < 2) hcomm hpow
          hZLcard f hf (le_top : f.range ≤ ⊤)
        have h2 : CFSG.Open.pRank 2 (⊤ : Subgroup (↥Xc ⧸ pPrimeCore 2 ↥Xc)) = n' :=
          hS.twoRank_eq
        omega
      have hdvdL : Nat.card (↥Xc ⧸ pPrimeCore 2 ↥Xc) ∣ Nat.card L :=
        (Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card Xc)
      have h2n' : 2 ^ (2 * n') ∣ Nat.card (↥Xc ⧸ pPrimeCore 2 ↥Xc) := by
        rw [hS.card_eq, ← pow_mul, mul_comm n' 2]
        exact Dvd.dvd.mul_left (dvd_mul_right _ _) _
      exact (pow_dvd_pow 2 (by omega)).trans (h2n'.trans hdvdL)
  have hZL2 : IsPGroup 2 ZL := fun g => ⟨1, by rw [pow_one, sq]; exact Subtype.ext (hZsq g.1 g.2)⟩
  obtain ⟨W, hW⟩ := hZL2.exists_le_sylow
  have hWcard : 2 ^ (2 * n) ∣ Nat.card (W : Subgroup ↥L) := W.pow_dvd_card_of_pow_dvd_card hkey
  set W' : Subgroup K := (W : Subgroup ↥L).map L.subtype with hW'
  have hW'card : Nat.card W' = Nat.card (W : Subgroup ↥L) :=
    Subgroup.card_map_of_injective L.subtype_injective
  have hW'2 : IsPGroup 2 W' := W.isPGroup'.map L.subtype
  have hZW' : rootCenter (Q : Subgroup K) ≤ W' := fun x hx => ⟨⟨x, hZL hx⟩, hW hx, rfl⟩
  obtain ⟨Q₁, hQ₁⟩ := hW'2.exists_le_sylow
  have hZne : rootCenter (Q : Subgroup K) ≠ ⊥ := by
    intro hbot
    apply hz1
    have : z ∈ (⊥ : Subgroup K) := hbot ▸ hz
    exact Subgroup.mem_bot.mp this
  have hQ₁Q : Q₁ = Q := hc.sylow_eq_of_ne_bot hZne (rootCenter_le _) (hZW'.trans hQ₁)
  have hW'Q : W' ≤ (Q : Subgroup K) := hQ₁Q ▸ hQ₁
  have hQcard : Nat.card (Q : Subgroup K) = 2 ^ (2 * n) := by
    rw [hc.card_eq, ← pow_mul, mul_comm]
  have hW'eq : W' = (Q : Subgroup K) := by
    apply Subgroup.eq_of_le_of_card_ge hW'Q
    rw [hQcard, hW'card]
    exact Nat.le_of_dvd Nat.card_pos hWcard
  have hQL : (Q : Subgroup K) ≤ L := hW'eq ▸ Subgroup.map_subtype_le _
  rw [eq_top_iff, ← hc.sup_zpowers_eq_top htQ]
  exact sup_le hQL (Subgroup.zpowers_le.mpr htL)

end CFSG.GH74.Uniqueness.Bender
