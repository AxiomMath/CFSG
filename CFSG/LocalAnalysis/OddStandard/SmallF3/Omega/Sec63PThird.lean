module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63PSmall
public import CFSG.GH74.GLS.Balance.CompSwap
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec63Rank

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

theorem sec63P_third_swap [Finite G] {y b : G} {J : Subgroup G} (hy : orderOf y = 2)
    (hb : orderOf b = 2) (hyb : y * b = b * y)
    (hJc : IsComponentIn J (centralizer ({b} : Set G))) (hJs : IsL29 J ∨ IsL281 J)
    (hJy : CFSG.conjugate J y ≠ J) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E ∧
      E ≤ J ⊔ CFSG.conjugate J y ∧ E ≤ centralizer ({y} : Set G) ∧ b ∉ E := by
  classical
  have hyb' : y ∈ centralizer ({b} : Set G) := Subgroup.mem_centralizer_singleton_iff.mpr hyb
  have hJ'c : IsComponentIn (CFSG.conjugate J y) (centralizer ({b} : Set G)) :=
    hJc.conjugate hyb'
  have hcomm : ∀ a ∈ J, ∀ c ∈ CFSG.conjugate J y, a * c = c * a :=
    hJc.commute_of_ne hJ'c hJy.symm
  have hc : ∀ a ∈ J, ∀ c ∈ J, a * (y * c * y⁻¹) = (y * c * y⁻¹) * a := by
    intro a ha c hcJ
    exact hcomm a ha (y * c * y⁻¹) (sec63P_conj_mem_conjugate hy hcJ)
  obtain ⟨φ, hφ⟩ := CFSG.GH74.GLS.Balance.Comp.exists_diagHom hc
  have hker : φ.ker ≤ Subgroup.center ↥J :=
    CFSG.GH74.GLS.Balance.Comp.diagHom_ker_le_center hc hφ
  have hφcent : ∀ k : ↥J, φ k ∈ centralizer ({y} : Set G) := fun k =>
    CFSG.GH74.GLS.Balance.Comp.diagHom_mem_centralizer (sec63P_mul_self hy) hc hφ k
  obtain ⟨E₄, hE₄J, hE₄ea, hE₄card⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := 2) Nat.prime_two
      (H := J) (k := 2) (sec63_two_le_pRank hJc.isQuasisimple hJs)
  have key : ∀ a : ↥E₄, (∀ g ∈ J, (a : G) * g = g * (a : G)) → a = 1 := by
    intro a hcommJ
    by_contra ha
    have h1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
    have hv : orderOf (a : G) = 2 := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      exact orderOf_eq_prime (hE₄ea.2 (a : G) a.2) h1
    have hW : J ≤ centralizer ({(a : G)} : Set G) := fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mpr (hcommJ g hg).symm
    exact (sec63_involution_not_mem hv hW hJc.isQuasisimple hJs) (hE₄J a.2)
  let ψ : ↥E₄ →* G := φ.comp (Subgroup.inclusion hE₄J)
  have hψ : ∀ a : ↥E₄, ψ a = (a : G) * (y * (a : G) * y⁻¹) := by
    intro a
    show φ (Subgroup.inclusion hE₄J a) = (a : G) * (y * (a : G) * y⁻¹)
    rw [hφ, Subgroup.coe_inclusion]
  have hψker : ∀ a : ↥E₄, ψ a = 1 → a = 1 := by
    intro a ha
    apply key a
    have hmem : Subgroup.inclusion hE₄J a ∈ φ.ker := MonoidHom.mem_ker.mpr ha
    have hcen : Subgroup.inclusion hE₄J a ∈ Subgroup.center ↥J := hker hmem
    intro g hg
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hcen ⟨g, hg⟩)).symm
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff ψ]
    apply le_antisymm _ bot_le
    intro a ha
    rw [Subgroup.mem_bot]
    exact hψker a (MonoidHom.mem_ker.mp ha)
  let E : Subgroup G := (⊤ : Subgroup ↥E₄).map ψ
  have hEea : CFSG.Open.IsElemAbelian 2 E := by
    show CFSG.Open.IsElemAbelian 2 ((⊤ : Subgroup ↥E₄).map ψ)
    have htop : CFSG.Open.IsElemAbelian 2 (⊤ : Subgroup ↥E₄) := by
      rw [CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_iff]
      refine ⟨fun a _ b _ => hE₄ea.1.is_comm.comm a b, fun a _ => ?_⟩
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hE₄ea.2 (a : G) a.2
    exact htop.map ψ
  have hEcard : Nat.card E = 4 := by
    show Nat.card ((⊤ : Subgroup ↥E₄).map ψ) = 4
    rw [Subgroup.card_map_of_injective (K := (⊤ : Subgroup ↥E₄)) hψinj, Subgroup.card_top,
      hE₄card]
    norm_num
  refine ⟨E, hEea, ?_, ?_, ?_, ?_⟩
  · rw [hEcard]
  · intro e he
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp he
    rw [hψ]
    exact mul_mem (Subgroup.mem_sup_left (hE₄J a.2))
      (Subgroup.mem_sup_right (sec63P_conj_mem_conjugate hy (hE₄J a.2)))
  · intro e he
    obtain ⟨a, -, rfl⟩ := Subgroup.mem_map.mp he
    show φ (Subgroup.inclusion hE₄J a) ∈ centralizer ({y} : Set G)
    exact hφcent _
  · intro hbE
    obtain ⟨a, -, ha⟩ := Subgroup.mem_map.mp hbE
    have hcommJ : ∀ g ∈ J, (a : G) * g = g * (a : G) := by
      intro g hg
      have hgb : g * b = b * g := Subgroup.mem_centralizer_singleton_iff.mp (hJc.le hg)
      have hgd : g * (y * (a : G) * y⁻¹) = (y * (a : G) * y⁻¹) * g :=
        hcomm g hg (y * (a : G) * y⁻¹) (sec63P_conj_mem_conjugate hy (hE₄J a.2))
      have had : (a : G) = b * (y * (a : G) * y⁻¹)⁻¹ := by
        rw [← ha, hψ]
        group
      have hgbC : Commute g b := hgb
      have hgdC : Commute g (y * (a : G) * y⁻¹) := hgd
      rw [had]
      exact (hgbC.mul_right hgdC.inv_right).symm
    have ha1 : a = 1 := key a hcommJ
    have hb1 : b = 1 := by
      rw [← ha, hψ, ha1]
      simp
    exfalso
    rw [hb1] at hb
    simp only [orderOf_one] at hb
    omega

theorem sec63P_third_out [Finite G] {y b : G} {J : Subgroup G} (hy : orderOf y = 2)
    (hb : orderOf b = 2) (hyb : y * b = b * y)
    (hJc : IsComponentIn J (centralizer ({b} : Set G))) (hJs : IsL29 J ∨ IsL281 J)
    (hJy : CFSG.conjugate J y = J) (hyJ : y ∉ zpowers b ⊔ J) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E ∧
      E ≤ J ⊔ zpowers y ∧ E ≤ centralizer ({y} : Set G) ∧ b ∉ E := by
  classical
  have hyN : y ∈ normalizer (J : Set G) := sec63P_conjugate_eq_iff.mp hJy
  have hyJ' : y ∉ J := fun h => hyJ (Subgroup.mem_sup_right h)
  obtain ⟨E₄, hE₄J, hE₄ea, hE₄card⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank (p := 2) Nat.prime_two
      (H := J) (k := 2) (sec63_two_le_pRank hJc.isQuasisimple hJs)
  have h4dvd : 4 ∣ Nat.card J := by
    have h := Subgroup.card_dvd_of_le hE₄J
    rw [hE₄card] at h
    norm_num at h
    exact h
  have heven : Even (Nat.card J) :=
    even_iff_two_dvd.mpr (dvd_trans (by norm_num : 2 ∣ 4) h4dvd)
  obtain ⟨e, heJ, heo, hec⟩ := sec63P_exists_fixed_involution hy hyN heven
  have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact sec63P_mul_self hy
  have he2 : e ^ 2 = 1 := by rw [pow_two]; exact sec63P_mul_self heo
  have hzy : CFSG.Open.IsElemAbelian 2 (zpowers y) := CFSG.Open.isElemAbelian_zpowers hy2
  have hze : CFSG.Open.IsElemAbelian 2 (zpowers e) := CFSG.Open.isElemAbelian_zpowers he2
  have hcomm : ∀ a ∈ zpowers y, ∀ c ∈ zpowers e, a * c = c * a := by
    intro a ha c hc
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hc
    exact ((show Commute y e from hec.symm).zpow_zpow i j)
  let E : Subgroup G := zpowers y ⊔ zpowers e
  have hEea : CFSG.Open.IsElemAbelian 2 E := by
    show CFSG.Open.IsElemAbelian 2 (zpowers y ⊔ zpowers e)
    exact CFSG.Open.IsElemAbelian.sup_of_commute hzy hze hcomm
  have hey : e ∉ zpowers y := by
    intro he
    have hle : zpowers e ≤ zpowers y := Subgroup.zpowers_le.mpr he
    have hcarde : Nat.card (zpowers e) = 2 := by rw [Nat.card_zpowers, heo]
    have hcardy : Nat.card (zpowers y) = 2 := by rw [Nat.card_zpowers, hy]
    have heq : zpowers e = zpowers y :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hcardy, hcarde])
    have hyJ'' : y ∈ J := by
      have : y ∈ zpowers e := by rw [heq]; exact Subgroup.mem_zpowers y
      exact Subgroup.zpowers_le.mpr heJ this
    exact hyJ' hyJ''
  have hlt : zpowers y < E := by
    show zpowers y < zpowers y ⊔ zpowers e
    refine lt_of_le_of_ne le_sup_left ?_
    intro h
    have heE : e ∈ zpowers y ⊔ zpowers e := Subgroup.mem_sup_right (Subgroup.mem_zpowers e)
    rw [← h] at heE
    exact hey heE
  have h2lt : 2 < Nat.card E := by
    have h := Subgroup.card_lt_of_lt hlt
    rw [Nat.card_zpowers, hy] at h
    exact h
  have hcard : 4 ≤ Nat.card E := by
    obtain ⟨k, hk⟩ :=
      CFSG.GH74.Uniqueness.SU.SU1.IsElemAbelian.exists_card (p := 2) Nat.prime_two hEea
    have hk2 : 2 < 2 ^ k := by rw [← hk]; exact h2lt
    have h1k : 1 < k := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using hk2)
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega)
      _ = Nat.card E := hk.symm
  have hEsle : E ≤ J ⊔ zpowers y := by
    show zpowers y ⊔ zpowers e ≤ J ⊔ zpowers y
    exact sup_le le_sup_right ((Subgroup.zpowers_le.mpr heJ).trans le_sup_left)
  have hEcent : E ≤ centralizer ({y} : Set G) := by
    show zpowers y ⊔ zpowers e ≤ centralizer ({y} : Set G)
    refine sup_le ?_ ?_
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr rfl
    · rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hec
  have hbJ : b ∉ J := sec63_involution_not_mem hb hJc.le hJc.isQuasisimple hJs
  refine ⟨E, hEea, hcard, hEsle, hEcent, ?_⟩
  intro hbE
  have hbE' : b ∈ zpowers y ⊔ zpowers e := hbE
  rcases sec63P_mem_sup_zpowers hy heo hec.symm hbE' with h1 | h2 | h3 | h4
  · rw [h1] at hb
    simp only [orderOf_one] at hb
    omega
  · apply hyJ
    rw [← h2]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers b)
  · exact hbJ (h3.symm ▸ heJ)
  · apply hyJ
    have hy_be : y = b * e := by
      rw [h4, mul_assoc, sec63P_mul_self heo, mul_one]
    rw [hy_be]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers b)) (Subgroup.mem_sup_right heJ)

theorem sec63P_third_in [Finite G] {y b : G} {J : Subgroup G} (hy : orderOf y = 2)
    (hb : orderOf b = 2) (hyb : y * b = b * y) (hne : y ≠ b)
    (hJc : IsComponentIn J (centralizer ({b} : Set G))) (hJs : IsL29 J ∨ IsL281 J)
    (hyJ : y ∈ zpowers b ⊔ J) :
    ∃ E : Subgroup G, CFSG.Open.IsElemAbelian 2 E ∧ 4 ≤ Nat.card E ∧
      E ≤ J ∧ E ≤ centralizer ({y} : Set G) ∧ b ∉ E := by
  classical
  have hJb : ∀ a ∈ J, a * b = b * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJc.le ha)
  have hcomm : ∀ a ∈ zpowers b, ∀ c ∈ J, a * c = c * a := by
    intro a ha c hc
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (show Commute b c from (hJb c hc).symm).zpow_left n
  obtain ⟨t, ht, j, hjJ, hy_eq⟩ := sec63P_mem_sup_of_comm hcomm hyJ
  have ht_cases : t = 1 ∨ t = b := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
    have hmod : b ^ n = b ^ (n % 2) := by
      simpa [hb] using (zpow_mod_orderOf b n).symm
    rcases Int.emod_two_eq_zero_or_one n with h | h
    · left
      rw [hmod, h]
      simp
    · right
      rw [hmod, h]
      simp
  have hji : ∃ j ∈ J, orderOf j = 2 ∧ (y = j ∨ y = b * j) := by
    rcases ht_cases with ht1 | htb
    · refine ⟨j, hjJ, ?_, Or.inl ?_⟩
      · rw [← (by rw [hy_eq, ht1, one_mul] : y = j)]
        exact hy
      · rw [hy_eq, ht1, one_mul]
    · refine ⟨j, hjJ, ?_, Or.inr ?_⟩
      · have hbj : j = b * y := by
          rw [hy_eq, htb, ← mul_assoc, sec63P_mul_self hb, one_mul]
        have hjj : j * j = 1 := by
          rw [hbj]
          calc (b * y) * (b * y) = b * (y * b) * y := by group
            _ = b * (b * y) * y := by rw [hyb]
            _ = (b * b) * (y * y) := by group
            _ = 1 := by rw [sec63P_mul_self hb, sec63P_mul_self hy, mul_one]
        have hjne : j ≠ 1 := by
          intro hj1
          have hby : b * y = 1 := by rw [← hbj]; exact hj1
          have hyb_eq : y = b := by
            have h1 : y = b⁻¹ := eq_inv_of_mul_eq_one_right hby
            rwa [sec63P_inv_eq hb] at h1
          exact hne hyb_eq
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact orderOf_eq_prime (by rw [pow_two]; exact hjj) hjne
      · rw [hy_eq, htb]
  obtain ⟨j, hjJ, hjo, hjy⟩ := hji
  obtain ⟨E, hEJ, hjE, hEea, hE4⟩ :=
    sec63P_exists_E4 (sec63_two_le_pRank hJc.isQuasisimple hJs) hjo hjJ
  refine ⟨E, hEea, hE4, hEJ, ?_, ?_⟩
  · intro e he
    rw [Subgroup.mem_centralizer_singleton_iff]
    rcases hjy with hje | hje
    · rw [hje]
      exact hEea.comm he hjE
    · rw [hje]
      have heb : e * b = b * e := Subgroup.mem_centralizer_singleton_iff.mp (hJc.le (hEJ he))
      have hej : e * j = j * e := hEea.comm he hjE
      calc e * (b * j) = (e * b) * j := by group
        _ = (b * e) * j := by rw [heb]
        _ = b * (e * j) := by group
        _ = b * (j * e) := by rw [hej]
        _ = (b * j) * e := by group
  · intro hbE
    exact (sec63_involution_not_mem hb hJc.le hJc.isQuasisimple hJs) (hEJ hbE)

end CFSG.OddStandard.SmallF3.Omega
