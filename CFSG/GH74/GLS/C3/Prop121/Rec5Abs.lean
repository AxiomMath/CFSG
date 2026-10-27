module

public import CFSG.GH74.GLS.C3.Prop121.CentralQuot
public import CFSG.GH74.GLS.C3.Prop121.GW5Three
public import CFSG.GH74.GLS.C3.Prop121.A6Cover
public import CFSG.GH74.GLS.C3.Prop121.Fin6Clause

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm

section Abstract

variable {M : Type} [Group M] [Finite M]

theorem exists_hom_alt6
    {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m) (ht₃ : t₀ ^ 3 = 1) (ht₁ : t₀ ≠ 1)
    (hodd : ∀ R : Subgroup M, Odd (Nat.card R) → (∀ m : M, ∀ r ∈ R, m * r * m⁻¹ ∈ R) →
      R ≤ zpowers t₀)
    (P : Sylow 2 M) (eP : ↥(P : Subgroup M) ≃* DihedralGroup 4) {z₀ : M} (hz₀z : z₀ * z₀ = 1)
    (hz₀1 : z₀ ≠ 1) (hcardCz : Nat.card ↥(centralizer ({z₀} : Set M)) = 24)
    (h9 : ∀ w : M, orderOf w = 2 → ¬ 9 ∣ Nat.card ↥(centralizer ({w} : Set M)))
    {K₀ : Subgroup M} (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 5))
    (hKN : ∀ k ∈ K₀, k ∈ zpowers t₀ → k = 1) (hz₀K : z₀ ∈ K₀) :
    ∃ η : M →* alternatingGroup (Fin 6), Function.Surjective η ∧ η.ker = zpowers t₀ := by
  classical
  have hNn : (zpowers t₀).Normal := zpowers_normal_of_central hc
  have hN : ∀ m ∈ zpowers t₀, m ^ 3 = 1 := by
    intro m hm
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hm
    rw [← zpow_natCast, ← zpow_mul, Int.mul_comm, zpow_mul, zpow_natCast, ht₃, one_zpow]
  have hN3 : Nat.card ↥(zpowers t₀) = 3 := card_zpowers_three ht₃ ht₁
  have hO : CFSG.pPrimeCore 2 (M ⧸ zpowers t₀) = ⊥ := pPrimeCore_eq_bot_of_forall _ hN hodd
  have hPcard : Nat.card ↥(P : Subgroup M) = 8 := by
    rw [Nat.card_congr eP.toEquiv, DihedralGroup.nat_card]
  have hPpg : IsPGroup 2 ↥(P : Subgroup M) := P.isPGroup'
  have hPidx : ¬ 2 ∣ (P : Subgroup M).index := Sylow.not_dvd_index P
  obtain ⟨S₀, hS₀, ⟨eS⟩⟩ := sylow_image (zpowers t₀) hN hN3 hPpg hPidx
  have hSyl : ∀ S : Sylow 2 (M ⧸ zpowers t₀),
      Nonempty ((S : Subgroup (M ⧸ zpowers t₀)) ≃* DihedralGroup 4) := by
    intro S
    have e1 := S.equiv S₀
    exact ⟨e1.trans ((MulEquiv.subgroupCongr hS₀).trans (eS.symm.trans eP))⟩
  have h3 : ∀ wb : M ⧸ zpowers t₀, orderOf wb = 2 →
      ¬ 3 ∣ Nat.card ↥(centralizer ({wb} : Set (M ⧸ zpowers t₀))) := by
    intro wb hwb h3dvd
    obtain ⟨w, hw, rfl⟩ := exists_lift_involution (zpowers t₀) hN hwb
    have hw2 : w * w = 1 := by
      have := pow_orderOf_eq_one w
      rwa [hw, sq] at this
    have h1 := card_centralizer_image t₀ ht₃ ht₁ hc hw2
    refine h9 w hw ?_
    rw [h1]
    simpa using Nat.mul_dvd_mul_left 3 h3dvd
  have hz₀N : z₀ ∉ zpowers t₀ := fun hz => hz₀1 (hKN z₀ hz₀K hz)
  have hzbar2 : orderOf (QuotientGroup.mk' (zpowers t₀) z₀) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul, hz₀z, map_one]
    · intro h1
      exact hz₀N ((QuotientGroup.eq_one_iff _).1 h1)
  have hCzbar : Nat.card ↥(centralizer ({QuotientGroup.mk' (zpowers t₀) z₀} :
      Set (M ⧸ zpowers t₀))) = 8 := by
    have h1 : Nat.card ↥(centralizer ({z₀} : Set M)) =
        3 * Nat.card ↥(centralizer ({QuotientGroup.mk' (zpowers t₀) z₀} :
          Set (M ⧸ zpowers t₀))) :=
      card_centralizer_image t₀ ht₃ ht₁ hc hz₀z
    rw [hcardCz] at h1
    omega
  obtain ⟨eKb⟩ := map_equiv_of_inf_zpowers_eq_bot (zpowers t₀) hKN
  have hKbar : Nonempty (↥(K₀.map (QuotientGroup.mk' (zpowers t₀))) ≃* alternatingGroup (Fin 5)) :=
    ⟨eKb.symm.trans eK₀⟩
  have hzbarK : QuotientGroup.mk' (zpowers t₀) z₀ ∈ K₀.map (QuotientGroup.mk' (zpowers t₀)) :=
    Subgroup.mem_map.2 ⟨z₀, hz₀K, rfl⟩
  obtain ⟨eX⟩ := gw5_of_three_free hO hSyl h3 hzbar2 hCzbar hKbar hzbarK
  refine ⟨eX.toMonoidHom.comp (QuotientGroup.mk' (zpowers t₀)), ?_, ?_⟩
  · exact eX.surjective.comp (QuotientGroup.mk'_surjective (zpowers t₀))
  · ext m
    rw [MonoidHom.mem_ker]
    show eX (QuotientGroup.mk' (zpowers t₀) m) = 1 ↔ m ∈ zpowers t₀
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff m

theorem exists_complement_five {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m) (ht₃ : t₀ ^ 3 = 1)
    (ht₁ : t₀ ≠ 1) {η : M →* alternatingGroup (Fin 6)} (hsurj : Function.Surjective η)
    (hker : η.ker = zpowers t₀) {ea eb : M} (hcomm : Commute ea eb)
    (hea3 : ea ^ 3 ∈ zpowers t₀) (heb3 : eb ^ 3 ∈ zpowers t₀) (hea1 : ea ∉ zpowers t₀)
    (heb : eb ∉ zpowers ea ⊔ zpowers t₀) :
    ∃ L : Subgroup M, L ⊓ zpowers t₀ = ⊥ ∧ L ⊔ zpowers t₀ = ⊤ ∧
      Nonempty (↥L ≃* alternatingGroup (Fin 6)) := by
  classical
  have hkerc : η.ker ≤ Subgroup.center M := by
    rw [hker]
    intro m hm
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hm
    rw [Subgroup.mem_center_iff]
    intro m'
    exact ((show Commute m' t₀ from hc m').zpow_right i).eq
  have hk3 : IsPGroup 3 ↥η.ker := by
    rw [hker]
    exact IsPGroup.of_card (n := 1) (by rw [card_zpowers_three ht₃ ht₁]; norm_num)
  have hηa3 : η ea ^ 3 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (hker ▸ hea3)
  have hηb3 : η eb ^ 3 = 1 := by
    rw [← map_pow]
    exact MonoidHom.mem_ker.1 (hker ▸ heb3)
  have hηa1 : η ea ≠ 1 := fun h1 => hea1 (hker ▸ MonoidHom.mem_ker.2 h1)
  have hηba : η eb ∉ zpowers (η ea) := by
    intro hmem
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hmem
    have hk : ea ^ (-i) * eb ∈ zpowers t₀ := by
      rw [← hker, MonoidHom.mem_ker, map_mul, map_zpow, zpow_neg, hi]
      group
    apply heb
    have h2 : eb = ea ^ i * (ea ^ (-i) * eb) := by group
    rw [h2]
    exact Subgroup.mul_mem_sup (Subgroup.zpow_mem _ (mem_zpowers ea) i) hk
  obtain ⟨L₀, hL0inf, hL0sup, hL0⟩ :=
    exists_complement_of_central_three_alt6 η hsurj hkerc hk3 hcomm hηa3 hηb3 hηa1 hηba
  rw [hker] at hL0inf hL0sup
  exact ⟨L₀, hL0inf, hL0sup, hL0⟩

omit [Finite M] in
theorem lifts_or_commutator
    {t₀ t' : M} {η : M →* alternatingGroup (Fin 6)}
    (hsurj : Function.Surjective η) (hker : η.ker = zpowers t₀) (ht'3 : t' ^ 3 = 1)
    (ht'1 : t' ∉ zpowers t₀) :
    ∃ eb : M, eb ^ 3 ∈ zpowers t₀ ∧ eb ∉ zpowers t' ⊔ zpowers t₀ ∧
      ∃ i : ℤ, eb * t' * eb⁻¹ * t'⁻¹ = t₀ ^ i := by
  classical
  have hā3 : η t' ^ 3 = 1 := by rw [← map_pow, ht'3, map_one]
  have hā1 : η t' ≠ 1 := fun h1 => ht'1 (hker ▸ MonoidHom.mem_ker.2 h1)
  have ht₀ : η t₀ = 1 := MonoidHom.mem_ker.1 (hker ▸ Subgroup.mem_zpowers t₀)
  have hσpow : (η t' : Perm (Fin 6)) ^ 3 = 1 := by
    have := congrArg Subtype.val hā3
    simpa using this
  have hσ3 : (η t' : Perm (Fin 6)) * (η t') * (η t') = 1 := by
    rw [← pow_three']; exact hσpow
  have hσ1 : (η t' : Perm (Fin 6)) ≠ 1 := fun h1 => hā1 (Subtype.ext h1)
  obtain ⟨k, hk3, hk1, hkσ, hkne, hkinv⟩ := exists_comm_ord3_six ⟨hσ3, hσ1⟩
  have hsk : sign k = 1 := by
    have h1 : sign k ^ 3 = 1 := by
      rw [← map_pow, pow_three', hk3, map_one]
    rcases Int.units_eq_one_or (sign k) with h | h
    · exact h
    · rw [h] at h1; exact absurd h1 (by decide)
  let b : alternatingGroup (Fin 6) := ⟨k, mem_alternatingGroup.2 hsk⟩
  obtain ⟨eb, heb⟩ := hsurj b
  have hcomm : b * η t' = η t' * b := Subtype.ext hkσ
  have hb3 : b ^ 3 = 1 := Subtype.ext (by simpa [pow_three'] using hk3)
  have hbnm : b ∉ zpowers (η t') := by
    intro hmem
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hmem
    have hi' : (η t' : Perm (Fin 6)) ^ i = k := by simpa using congrArg Subtype.val hi
    have h3z : (η t' : Perm (Fin 6)) ^ (3 : ℤ) = 1 := by
      rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]; exact hσpow
    rw [zpow_eq_zpow_emod i h3z] at hi'
    have : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
    rcases this with h | h | h
    · rw [h, zpow_zero] at hi'; exact hk1 hi'.symm
    · rw [h, zpow_one] at hi'; exact hkne hi'.symm
    · rw [h] at hi'
      apply hkinv
      rw [← hi']
      apply eq_inv_of_mul_eq_one_left
      rw [← zpow_add_one, show (2 : ℤ) + 1 = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast]
      exact hσpow
  refine ⟨eb, ?_, ?_, ?_⟩
  · rw [← hker, MonoidHom.mem_ker, map_pow, heb]; exact hb3
  · intro hmem
    apply hbnm
    have h1 : η eb ∈ Subgroup.map η (zpowers t' ⊔ zpowers t₀) := Subgroup.mem_map_of_mem η hmem
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers, ht₀,
      Subgroup.zpowers_one_eq_bot, sup_bot_eq, heb] at h1
    exact h1
  · have hx : η (eb * t' * eb⁻¹ * t'⁻¹) = 1 := by
      simp only [map_mul, map_inv, heb]
      rw [hcomm]; group
    have hx' : eb * t' * eb⁻¹ * t'⁻¹ ∈ zpowers t₀ := hker ▸ MonoidHom.mem_ker.2 hx
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hx'
    exact ⟨i, hi.symm⟩

end Abstract

end CFSG.GH74.GLS.C3.Prop121
