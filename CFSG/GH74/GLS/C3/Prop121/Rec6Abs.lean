module

public import CFSG.GH74.GLS.C3.Prop121.CentralQuot
public import CFSG.GH74.GLS.C3.Prop121.A6Class
public import CFSG.GH74.GLS.C3.Prop121.GW56
public import CFSG.GH74.GLS.C3.Prop121.A7Cover
public import CFSG.GH74.GLS.C3.Layer3.Basic

public section

namespace CFSG.GH74.GLS.C3.Prop121

open Subgroup Equiv Perm

theorem a0_b0_facts :
    let a₀ : Perm (Fin 6) := swap 0 1 * swap 1 2
    let b₀ : Perm (Fin 6) := swap 3 4 * swap 4 5
    sign a₀ = 1 ∧ sign b₀ = 1 ∧ a₀ * b₀ = b₀ * a₀ ∧ a₀ ^ 3 = 1 ∧ b₀ ^ 3 = 1 ∧ a₀ ≠ 1 ∧
      ∀ i : ℤ, a₀ ^ i ≠ b₀ := by
  intro a₀ b₀
  have ha3 : a₀ ^ 3 = 1 := by decide
  have ha1 : a₀ ≠ 1 := by decide
  refine ⟨by decide, by decide, by decide, ha3, by decide, ha1, ?_⟩
  intro i
  have hord : orderOf a₀ = 3 := orderOf_eq_prime ha3 ha1
  have h1 : a₀ ^ i = a₀ ^ (i % 3) := by
    have := zpow_mod_orderOf a₀ i
    rw [hord] at this
    exact this.symm
  have h6 : i % 3 = 0 ∨ i % 3 = 1 ∨ i % 3 = 2 := by omega
  rw [h1]
  rcases h6 with h | h | h
  · rw [h, zpow_zero]; decide
  · rw [h, zpow_one]; decide
  · rw [h]
    have : a₀ ^ (2 : ℤ) = a₀ * a₀ := zpow_two a₀
    rw [this]; decide

section Abstract

variable {M : Type} [Group M] [Finite M]

theorem isConj_of_involutions_alt6
    (K₀ : Subgroup M) (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 6))
    (P : Sylow 2 M) (hPcard : Nat.card ↥(P : Subgroup M) = 8) :
    ∀ α β : M, orderOf α = 2 → orderOf β = 2 → IsConj α β := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKcard : Nat.card ↥K₀ = 360 := by
    rw [Nat.card_congr eK₀.toEquiv, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_fin]
    decide
  have hfac : (360 : ℕ).factorization 2 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_two]
    decide +kernel
  obtain ⟨Q₀⟩ : Nonempty (Sylow 2 ↥K₀) := inferInstance
  have hQcard : Nat.card ↥(Q₀ : Subgroup ↥K₀) = 8 := by
    rw [Sylow.card_eq_multiplicity, hKcard, hfac]; norm_num
  let PK : Subgroup M := (Q₀ : Subgroup ↥K₀).map K₀.subtype
  have hPKcard : Nat.card ↥PK = 8 := by
    rw [Subgroup.card_map_of_injective K₀.subtype_injective, hQcard]
  have hPKpg : IsPGroup 2 ↥PK :=
    IsPGroup.of_card (n := 3) (by rw [hPKcard]; norm_num)
  have hPidx : ¬ 2 ∣ (P : Subgroup M).index := Sylow.not_dvd_index P
  have hPKidx : ¬ 2 ∣ PK.index := by
    have h1 := Subgroup.index_mul_card (P : Subgroup M)
    have h2 := Subgroup.index_mul_card PK
    rw [hPcard] at h1
    rw [hPKcard] at h2
    have : PK.index = (P : Subgroup M).index := by
      apply Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 8)
      rw [h1, h2]
    rw [this]; exact hPidx
  let PKs : Sylow 2 M := hPKpg.toSylow hPKidx
  have hPKs : (PKs : Subgroup M) = PK := rfl
  refine isConj_of_sylow PKs ?_
  intro α hα β hβ hα2 hβ2
  rw [hPKs] at hα hβ
  obtain ⟨a', ha'Q, rfl⟩ := hα
  obtain ⟨b', hb'Q, rfl⟩ := hβ
  have hord : ∀ c : ↥K₀, orderOf (K₀.subtype c) = orderOf c := fun c =>
    orderOf_injective K₀.subtype K₀.subtype_injective c
  have ha2' : orderOf a' = 2 := by rw [← hord]; exact hα2
  have hb2' : orderOf b' = 2 := by rw [← hord]; exact hβ2
  have hconj : IsConj (eK₀ a') (eK₀ b') :=
    isConj_of_involutions_alt_six _ _ (by rw [MulEquiv.orderOf_eq]; exact ha2')
      (by rw [MulEquiv.orderOf_eq]; exact hb2')
  have hconj' : IsConj a' b' := (CFSG.GH74.GLS.Layer3.isConj_map_iff eK₀).1 hconj
  exact (K₀.subtype).map_isConj hconj'

theorem exists_hom_alt7
    {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m) (ht₃ : t₀ ^ 3 = 1) (ht₁ : t₀ ≠ 1)
    (hodd : ∀ R : Subgroup M, Odd (Nat.card R) → (∀ m : M, ∀ r ∈ R, m * r * m⁻¹ ∈ R) →
      R ≤ zpowers t₀)
    (P : Sylow 2 M) (eP : ↥(P : Subgroup M) ≃* DihedralGroup 4) {z₀ : M} (hz₀z : z₀ * z₀ = 1)
    (hz₀1 : z₀ ≠ 1) (hcardCz : Nat.card ↥(centralizer ({z₀} : Set M)) = 72)
    {K₀ : Subgroup M} (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 6))
    (hKN : ∀ k ∈ K₀, k ∈ zpowers t₀ → k = 1) (hz₀K : z₀ ∈ K₀) :
    ∃ η : M →* alternatingGroup (Fin 7), Function.Surjective η ∧ η.ker = zpowers t₀ := by
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
  have hone : ∀ α β : M ⧸ zpowers t₀, orderOf α = 2 → orderOf β = 2 → IsConj α β :=
    fun α β hα hβ =>
      isConj_of_involutions (zpowers t₀) hN (isConj_of_involutions_alt6 K₀ eK₀ P hPcard) hα hβ
  have hz₀N : z₀ ∉ zpowers t₀ := fun hz => hz₀1 (hKN z₀ hz₀K hz)
  have hzbar2 : orderOf (QuotientGroup.mk' (zpowers t₀) z₀) = 2 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [sq, ← map_mul, hz₀z, map_one]
    · intro h1
      exact hz₀N ((QuotientGroup.eq_one_iff _).1 h1)
  have hCzbar : Nat.card ↥(centralizer ({QuotientGroup.mk' (zpowers t₀) z₀} :
      Set (M ⧸ zpowers t₀))) = 24 := by
    have h1 : Nat.card ↥(centralizer ({z₀} : Set M)) =
        3 * Nat.card ↥(centralizer ({QuotientGroup.mk' (zpowers t₀) z₀} :
          Set (M ⧸ zpowers t₀))) :=
      card_centralizer_image t₀ ht₃ ht₁ hc hz₀z
    rw [hcardCz] at h1
    omega
  obtain ⟨eKb⟩ := map_equiv_of_inf_zpowers_eq_bot (zpowers t₀) hKN
  have hKbar : Nonempty (↥(K₀.map (QuotientGroup.mk' (zpowers t₀))) ≃* alternatingGroup (Fin 6)) :=
    ⟨eKb.symm.trans eK₀⟩
  obtain ⟨eX⟩ := gw56_six hO hSyl hone hzbar2 hCzbar hKbar
  refine ⟨eX.toMonoidHom.comp (QuotientGroup.mk' (zpowers t₀)), ?_, ?_⟩
  · exact eX.surjective.comp (QuotientGroup.mk'_surjective (zpowers t₀))
  · ext m
    rw [MonoidHom.mem_ker]
    show eX (QuotientGroup.mk' (zpowers t₀) m) = 1 ↔ m ∈ zpowers t₀
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff m

theorem exists_complement_six {t₀ : M} (hc : ∀ m : M, m * t₀ = t₀ * m) (ht₃ : t₀ ^ 3 = 1)
    (ht₁ : t₀ ≠ 1) {η : M →* alternatingGroup (Fin 7)} (hsurj : Function.Surjective η)
    (hker : η.ker = zpowers t₀) {K₀ : Subgroup M} (eK₀ : ↥K₀ ≃* alternatingGroup (Fin 6))
    (hKN : ∀ k ∈ K₀, k ∈ zpowers t₀ → k = 1) :
    ∃ L : Subgroup M, L ⊓ zpowers t₀ = ⊥ ∧ L ⊔ zpowers t₀ = ⊤ ∧
      Nonempty (↥L ≃* alternatingGroup (Fin 7)) := by
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
  have hηK : ∀ k : ↥K₀, η (k : M) = 1 → k = 1 := by
    intro k hk
    have h1 : (k : M) ∈ η.ker := hk
    rw [hker] at h1
    exact Subtype.ext (hKN _ k.2 h1)
  obtain ⟨hsa, hsb, hab, ha3, hb3, ha1, hnpow⟩ := a0_b0_facts
  let Aa : alternatingGroup (Fin 6) := ⟨swap 0 1 * swap 1 2, mem_alternatingGroup.2 hsa⟩
  let Ab : alternatingGroup (Fin 6) := ⟨swap 3 4 * swap 4 5, mem_alternatingGroup.2 hsb⟩
  have hAab : Aa * Ab = Ab * Aa := Subtype.ext hab
  have hAa3 : Aa ^ 3 = 1 := Subtype.ext ha3
  have hAb3 : Ab ^ 3 = 1 := Subtype.ext hb3
  have hAa1 : Aa ≠ 1 := fun h1 => ha1 (congrArg Subtype.val h1)
  let κa : ↥K₀ := eK₀.symm Aa
  let κb : ↥K₀ := eK₀.symm Ab
  have hcomm : Commute (κa : M) (κb : M) := by
    have : κa * κb = κb * κa := by
      apply eK₀.injective
      rw [map_mul, map_mul]
      show eK₀ (eK₀.symm Aa) * eK₀ (eK₀.symm Ab) = eK₀ (eK₀.symm Ab) * eK₀ (eK₀.symm Aa)
      rw [eK₀.apply_symm_apply, eK₀.apply_symm_apply]
      exact hAab
    exact congrArg Subtype.val this
  have hκa3 : κa ^ 3 = 1 := by
    apply eK₀.injective
    rw [map_pow]
    show eK₀ (eK₀.symm Aa) ^ 3 = eK₀ 1
    rw [eK₀.apply_symm_apply, hAa3, map_one]
  have hκb3 : κb ^ 3 = 1 := by
    apply eK₀.injective
    rw [map_pow]
    show eK₀ (eK₀.symm Ab) ^ 3 = eK₀ 1
    rw [eK₀.apply_symm_apply, hAb3, map_one]
  have hea3 : (κa : M) ^ 3 = 1 := by simpa using congrArg Subtype.val hκa3
  have heb3 : (κb : M) ^ 3 = 1 := by simpa using congrArg Subtype.val hκb3
  have hηa3 : η (κa : M) ^ 3 = 1 := by rw [← map_pow, hea3, map_one]
  have hηb3 : η (κb : M) ^ 3 = 1 := by rw [← map_pow, heb3, map_one]
  have hηa1 : η (κa : M) ≠ 1 := by
    intro h1
    have h2 : κa = 1 := hηK κa h1
    have h3 : Aa = 1 := by
      have h4 : eK₀ κa = 1 := by rw [h2, map_one]
      have h5 : eK₀ κa = Aa := eK₀.apply_symm_apply Aa
      rw [← h5]; exact h4
    exact hAa1 h3
  have hηba : η (κb : M) ∉ zpowers (η (κa : M)) := by
    intro hmem
    obtain ⟨i, hi⟩ := mem_zpowers_iff.1 hmem
    let k : ↥K₀ := κb⁻¹ * κa ^ i
    have hkM : (k : M) = (κb : M)⁻¹ * (κa : M) ^ i := by simp [k]
    have hk1 : η (k : M) = 1 := by
      rw [hkM, map_mul, map_inv, map_zpow, hi, inv_mul_cancel]
    have hk : k = 1 := hηK k hk1
    have h3 : κa ^ i = κb := by
      calc κa ^ i = κb * (κb⁻¹ * κa ^ i) := by group
        _ = κb := by rw [show κb⁻¹ * κa ^ i = 1 from hk, mul_one]
    have h4 : Aa ^ i = Ab := by
      have h5 := congrArg eK₀ h3
      rw [map_zpow] at h5
      simpa [κa, κb] using h5
    exact hnpow i (by simpa using congrArg Subtype.val h4)
  obtain ⟨L₀, hL0inf, hL0sup, hL0⟩ :=
    exists_complement_of_central_three_alt7 η hsurj hkerc hk3 hcomm hηa3 hηb3 hηa1 hηba
  rw [hker] at hL0inf hL0sup
  exact ⟨L₀, hL0inf, hL0sup, hL0⟩

end Abstract

end CFSG.GH74.GLS.C3.Prop121
