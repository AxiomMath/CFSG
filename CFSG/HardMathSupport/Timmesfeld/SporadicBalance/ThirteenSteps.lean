module

public import CFSG.Assembly.Defs
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPPrimeCoreBasics
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.FixedFreeRank

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.HardMathSupport.Timmesfeld.Proving

variable {G : Type*} [Group G]

theorem odd_card_gLAPPrimeCoreOf_thirteen [Finite G] {t s : G} (hs : orderOf s = 13)
    (hP : ∃ P : Subgroup G, IsPGroup 13 P ∧ P ≤ Subgroup.centralizer ({s} : Set G) ∧
      ∀ u : G, orderOf u = 2 → ∃ g ∈ P, g * u ≠ u * g)
    (hpure : ∀ A : Subgroup G, (∀ a ∈ A, ∀ b ∈ A, a * b = b * a) → (∀ a ∈ A, a ^ 2 = 1) →
      8 ≤ Nat.card A → ∃ u ∈ A, IsConj t u)
    (hbound : ∀ x : G, orderOf x = 13 → x * t = t * x →
      Nat.card (Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) :
        Subgroup G) < 13 * 2 ^ 12) :
    Odd (Nat.card (GLAPPrimeCoreOf 13 (Subgroup.centralizer ({s} : Set G)))) := by
  have h11 : Nat.Prime 13 := by norm_num
  set N := GLAPPrimeCoreOf 13 (Subgroup.centralizer ({s} : Set G)) with hN
  by_contra hodd
  have h2N : 2 ∣ Nat.card N := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hodd)
  obtain ⟨P, hPp, hPC, hfix⟩ := hP
  have hPN : P ≤ Subgroup.normalizer (N : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      exact GLAPPrimeCoreOf_conj_mem g (hPC hg) y hy
    · intro hy
      have := GLAPPrimeCoreOf_conj_mem g⁻¹ (Subgroup.inv_mem _ (hPC hg)) _ hy
      simpa [mul_assoc] using this
  have hcopN : ¬ 13 ∣ Nat.card N := fun h =>
    (Nat.Prime.coprime_iff_not_dvd h11).1 (coprime_card_GLAPPrimeCoreOf h11 _) h
  obtain ⟨A, hAN, hA1, hA2, hAc, hAe, hAmod⟩ := exists_elemAbelian_modEq_one h11 Nat.prime_two hPp
    hcopN hPN h2N (fun a ha => by
      obtain ⟨g, hg, hga⟩ := hfix a ha
      exact ⟨g, hg, hga⟩)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hA2.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hA1 (Subgroup.eq_bot_of_card_eq A (by rw [hk, pow_zero]))
  have hk10 : 12 ≤ k := twelve_le_of_two_pow_modEq_thirteen (by rw [← hk]; exact hAmod) hk0
  have hA8 : 8 ≤ Nat.card A := by
    rw [hk]
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨u, huA, hu⟩ := hpure A hAc hAe hA8
  obtain ⟨c, hc⟩ := isConj_iff.1 hu
  set x := c⁻¹ * s * c with hxdef
  have hNs : ∀ a ∈ A, a * s = s * a := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.1 (GLAPPrimeCoreOf_le _ (hAN ha))
  have hxo : orderOf x = 13 := by
    rw [hxdef, show c⁻¹ * s * c = (MulAut.conj c⁻¹) s by simp [MulAut.conj_apply],
      MulEquiv.orderOf_eq]
    exact hs
  have hxt : x * t = t * x := by
    have h1 := hNs u huA
    rw [← hc] at h1
    calc x * t = c⁻¹ * (s * (c * t * c⁻¹)) * c := by rw [hxdef]; group
      _ = c⁻¹ * ((c * t * c⁻¹) * s) * c := by rw [h1]
      _ = t * x := by rw [hxdef]; group
  set D := Subgroup.centralizer ({t} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) with hD
  have hA'D : A.map (MulAut.conj c⁻¹).toMonoidHom ≤ D := by
    intro y hy
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_,
      Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    · have h1 := hAc a ha u huA
      rw [← hc] at h1
      calc c⁻¹ * a * c * t = c⁻¹ * (a * (c * t * c⁻¹)) * c := by group
        _ = c⁻¹ * ((c * t * c⁻¹) * a) * c := by rw [h1]
        _ = t * (c⁻¹ * a * c) := by group
    · have h1 := hNs a ha
      calc c⁻¹ * a * c * x = c⁻¹ * (a * s) * c := by rw [hxdef]; group
        _ = c⁻¹ * (s * a) * c := by rw [h1]
        _ = x * (c⁻¹ * a * c) := by rw [hxdef]; group
  have hcardA' : Nat.card (A.map (MulAut.conj c⁻¹).toMonoidHom) = 2 ^ k := by
    rw [Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective, hk]
  have h2D : 2 ^ k ∣ Nat.card D := hcardA' ▸ Subgroup.card_dvd_of_le hA'D
  have hxD : x ∈ D := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 hxt,
    Subgroup.mem_centralizer_singleton_iff.2 rfl⟩
  have h11D : 13 ∣ Nat.card D := hxo ▸ Subgroup.orderOf_dvd_natCard D hxD
  have hcop : Nat.Coprime 13 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have hdvd : 13 * 2 ^ k ∣ Nat.card D := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop h11D h2D
  have hle : 13 * 2 ^ k ≤ Nat.card D := Nat.le_of_dvd Nat.card_pos hdvd
  have h10 : 13 * 2 ^ 12 ≤ 13 * 2 ^ k :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hk10)
  have hb : Nat.card D < 13 * 2 ^ 12 := hbound x hxo hxt
  omega

theorem exists_thirteen_subgroup_of_factorization [Finite G]
    (hG : (Nat.card G).factorization 13 = 3)
    (hinv : ∀ u : G, orderOf u = 2 →
      (Nat.card (Subgroup.centralizer ({u} : Set G))).factorization 13 ≤ 1)
    {s : G} (hs : orderOf s = 13) :
    ∃ P : Subgroup G, IsPGroup 13 P ∧ P ≤ Subgroup.centralizer ({s} : Set G) ∧
      ∀ u : G, orderOf u = 2 → ∃ g ∈ P, g * u ≠ u * g := by
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  have hsz : IsPGroup 13 (Subgroup.zpowers s) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨Q, hQ⟩ := hsz.exists_le_sylow
  have hQc : Nat.card (Q : Subgroup G) = 13 ^ 3 := by rw [Q.card_eq_multiplicity, hG]
  have hsQ : s ∈ (Q : Subgroup G) := hQ (Subgroup.mem_zpowers s)
  set P := Subgroup.centralizer ({s} : Set G) ⊓ (Q : Subgroup G) with hPdef
  have hPp : IsPGroup 13 P := Q.isPGroup'.to_le inf_le_right
  have h169 : 13 ^ 2 ∣ Nat.card P := by
    obtain ⟨a, ha⟩ := hPp.exists_card_eq
    rw [ha]
    by_contra hc
    have ha1 : a ≤ 1 := by
      by_contra h2
      push_neg at h2
      exact hc (Nat.pow_dvd_pow 13 h2)
    have hsP : s ∈ P := Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 rfl, hsQ⟩
    have hzp : Subgroup.zpowers s ≤ P := (Subgroup.zpowers_le).2 hsP
    have hPz : P = Subgroup.zpowers s := by
      refine (Subgroup.eq_of_le_of_card_ge hzp ?_).symm
      rw [Nat.card_zpowers, hs, ha]
      calc 13 ^ a ≤ 13 ^ 1 := Nat.pow_le_pow_right (by norm_num) ha1
        _ = 13 := pow_one 13
    have hQp : IsPGroup 13 (Q : Subgroup G) := Q.isPGroup'
    have : Nontrivial (Q : Subgroup G) := by
      rw [Subgroup.nontrivial_iff_ne_bot]
      intro hb
      rw [hb, Subgroup.card_bot] at hQc
      norm_num at hQc
    have : Nontrivial (Subgroup.center (Q : Subgroup G)) := hQp.center_nontrivial
    obtain ⟨z, hz1⟩ := exists_ne (1 : Subgroup.center (Q : Subgroup G))
    have hzc : ∀ q ∈ (Q : Subgroup G), (z : G) * q = q * z := by
      intro q hq
      have := Subgroup.mem_center_iff.1 z.2 ⟨q, hq⟩
      exact (congrArg Subtype.val this).symm
    have hzP : ((z : (Q : Subgroup G)) : G) ∈ P :=
      Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 (hzc s hsQ), (z : Q).2⟩
    rw [hPz] at hzP
    have hz1' : ((z : (Q : Subgroup G)) : G) ≠ 1 := by
      intro h
      apply hz1
      apply Subtype.ext
      apply Subtype.ext
      exact h
    have hzo : orderOf ((z : (Q : Subgroup G)) : G) = 13 := by
      have hdvd : orderOf ((z : (Q : Subgroup G)) : G) ∣ 13 := by
        have := orderOf_dvd_of_mem_zpowers hzP
        rwa [hs] at this
      rcases (Nat.dvd_prime (by norm_num)).1 hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hz1'
      · exact h
    have hzz : Subgroup.zpowers ((z : (Q : Subgroup G)) : G) = Subgroup.zpowers s := by
      refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hzP) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hs, hzo]
    have hsz' : s ∈ Subgroup.zpowers ((z : (Q : Subgroup G)) : G) := by
      rw [hzz]; exact Subgroup.mem_zpowers s
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hsz'
    have hQP : (Q : Subgroup G) ≤ P := by
      intro q hq
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hq⟩
      rw [← hm]
      exact ((Commute.zpow_right (hzc q hq).symm m)).eq
    have := Subgroup.card_le_of_le hQP
    rw [hQc, ha] at this
    have : 13 ^ 3 ≤ 13 ^ 1 := this.trans (Nat.pow_le_pow_right (by norm_num) ha1)
    norm_num at this
  refine ⟨P, hPp, inf_le_left, fun u hu => ?_⟩
  by_contra hall
  push_neg at hall
  have hle : P ≤ Subgroup.centralizer ({u} : Set G) := fun g hg =>
    Subgroup.mem_centralizer_singleton_iff.2 (hall g hg)
  have hdvd : 13 ^ 2 ∣ Nat.card (Subgroup.centralizer ({u} : Set G)) :=
    h169.trans (Subgroup.card_dvd_of_le hle)
  have h1 := (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').1 hdvd
  have h2 := hinv u hu
  omega

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
