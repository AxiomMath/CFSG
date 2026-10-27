module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Abs
public import CFSG.LocalAnalysis.AGLEmbedding.AltBetaRank

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Signalizer.Odd87

theorem finite_of_doubleCover {K : Type} [Group K] {n : ℕ} (hK : IsDoubleCoverOfAlt K n) :
    Finite K := by
  obtain ⟨_, hc, ⟨e⟩⟩ := hK
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  have : Nat.card K ≠ 0 := by
    rw [h1]
    exact Nat.mul_ne_zero Nat.card_pos.ne' (by norm_num)
  exact Nat.finite_of_card_ne_zero this

theorem card_doubleCover {K : Type} [Group K] [Finite K] {n : ℕ} (hK : IsDoubleCoverOfAlt K n)
    (hn : 2 ≤ n) : Nat.card K = n.factorial := by
  obtain ⟨_, hc, ⟨e⟩⟩ := hK
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)
  rw [Nat.card_congr e.toEquiv, hc] at h1
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr hn
  have h2 := two_mul_nat_card_alternatingGroup (α := Fin n)
  rw [Nat.card_eq_fintype_card (α := Equiv.Perm (Fin n)), Fintype.card_perm,
    Fintype.card_fin] at h2
  omega

theorem exists_perm_hom_doubleCover {K : Type} [Group K] {n : ℕ} (hK : IsDoubleCoverOfAlt K n) :
    ∃ ψ : K →* Equiv.Perm (Fin n), ∀ x, ψ x = 1 → x ∈ center K := by
  obtain ⟨_, _, ⟨e⟩⟩ := hK
  refine ⟨(alternatingGroup (Fin n)).subtype.comp
    (e.toMonoidHom.comp (QuotientGroup.mk' (center K))), fun x hx => ?_⟩
  have h1 : e (QuotientGroup.mk x) = 1 := Subtype.ext hx
  have h2 : (QuotientGroup.mk x : K ⧸ center K) = 1 := e.injective (by rw [h1, map_one])
  exact (QuotientGroup.eq_one_iff x).1 h2

theorem card_le_of_abelian_doubleCover {K : Type} [Group K] {n : ℕ} (hK : IsDoubleCoverOfAlt K n)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {T : Subgroup K} (hc : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x)
    (hT : IsPGroup p T) : Nat.card T ≤ p ^ (n / p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have := finite_of_doubleCover hK
  obtain ⟨ψ, hψ⟩ := exists_perm_hom_doubleCover hK
  have hcen : Nat.card (center K) = 2 := hK.2.1
  have hinj : Function.Injective (ψ.comp T.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx1 : ψ (x : K) = 1 := hx
    have hxc : (x : K) ∈ center K := hψ _ hx1
    have h1 : orderOf (⟨(x : K), hxc⟩ : ↥(center K)) ∣ 2 := by
      rw [← hcen]; exact orderOf_dvd_natCard _
    have h2 : orderOf x ∣ Nat.card T := orderOf_dvd_natCard x
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    have h3 : orderOf x ∣ p ^ k := hk ▸ h2
    have h1' : orderOf x ∣ 2 := by
      have : orderOf (x : K) = orderOf (⟨(x : K), hxc⟩ : ↥(center K)) := by
        rw [Subgroup.orderOf_mk]
      rw [← Subgroup.orderOf_coe, this]
      exact h1
    have hcop : Nat.Coprime 2 (p ^ k) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_two hp).2 (Ne.symm hp2))
    exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcop h1' h3)
  let T' : Subgroup (Equiv.Perm (Fin n)) := (ψ.comp T.subtype).range
  have hT'card : Nat.card T' = Nat.card T :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have hT'p : IsPGroup p T' := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    exact IsPGroup.of_card (hT'card.trans hk)
  have hT'c : ∀ x ∈ T', ∀ y ∈ T', x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hc a a.2 b b.2)
  have := CFSG.AGLEmbedding.card_le_pow_div_of_commute (p := p) T' hT'c hT'p
  rw [hT'card, Fintype.card_fin] at this
  exact this

theorem no_abelian_81 {K : Type} [Group K] [Finite K] {n : ℕ} (hn : n = 10 ∨ n = 11)
    (hK : IsDoubleCoverOfAlt K n) (R' : Subgroup K) (N : Subgroup ↥R') [N.Normal]
    (P : Subgroup (↥R' ⧸ N)) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hPcard : Nat.card P = 81) :
    False := by
  classical
  have hfK : Nat.card K = n.factorial := card_doubleCover hK (by omega)
  have h11 : n.factorial ∣ Nat.factorial 11 := Nat.factorial_dvd_factorial (by omega)
  have hR'K : Nat.card ↥R' ∣ Nat.factorial 11 :=
    (Subgroup.card_subgroup_dvd_card R').trans (hfK ▸ h11)
  have hcard : Nat.card (↥R' ⧸ N) ∣ Nat.factorial 11 := (Subgroup.index_dvd_card N).trans hR'K
  have h243 : ¬ 243 ∣ Nat.factorial 11 := by decide
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [hPcard]; norm_num)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hidx : ¬ 3 ∣ P.index := by
    intro h3
    have h1 := Subgroup.card_mul_index P
    rw [hPcard] at h1
    have h2 : 81 * P.index ∣ Nat.factorial 11 := h1 ▸ hcard
    exact h243 ((mul_dvd_mul_left 81 h3 : 81 * 3 ∣ 81 * P.index).trans h2)
  let S3 : Sylow 3 (↥R' ⧸ N) := hP3.toSylow hidx
  obtain ⟨T, hT⟩ := Sylow.mapSurjective_surjective (QuotientGroup.mk'_surjective N) 3 S3
  have hTmap : (T : Subgroup ↥R').map (QuotientGroup.mk' N) = P := by
    have := congrArg (fun Q : Sylow 3 (↥R' ⧸ N) => (Q : Subgroup (↥R' ⧸ N))) hT
    simpa [Sylow.coe_mapSurjective, S3] using this
  have hTcard : Nat.card (T : Subgroup ↥R') ∣ 81 := by
    obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
    have h1 : 3 ^ k ∣ Nat.factorial 11 :=
      hk ▸ (Subgroup.card_subgroup_dvd_card (T : Subgroup ↥R')).trans hR'K
    have hk4 : k ≤ 4 := by
      by_contra hk5
      have hk5 := not_le.1 hk5
      exact h243 ((pow_dvd_pow 3 hk5 : 3 ^ 5 ∣ 3 ^ k).trans h1)
    rw [hk]
    exact (pow_dvd_pow 3 hk4 : 3 ^ k ∣ 3 ^ 4)
  let φ : ↥(T : Subgroup ↥R') →* (↥R' ⧸ N) :=
    (QuotientGroup.mk' N).comp (T : Subgroup ↥R').subtype
  have hrange : φ.range = P := by
    rw [← hTmap, MonoidHom.range_comp, Subgroup.range_subtype]
  have hker : φ.ker = ⊥ := by
    have h1 := Subgroup.card_ker_mul_card_range φ
    rw [hrange, hPcard] at h1
    have h2 : 81 ∣ Nat.card (T : Subgroup ↥R') := by rw [← h1]; exact dvd_mul_left _ _
    have h3 : Nat.card (T : Subgroup ↥R') = 81 := Nat.dvd_antisymm hTcard h2
    have h4 : Nat.card φ.ker = 1 := by rw [h3] at h1; omega
    exact Subgroup.eq_bot_of_card_eq _ h4
  have hφinj : Function.Injective φ := (MonoidHom.ker_eq_bot_iff φ).1 hker
  have hTc : ∀ x y : ↥(T : Subgroup ↥R'), x * y = y * x := by
    intro x y
    apply hφinj
    rw [map_mul, map_mul]
    exact hPc _ (hrange ▸ ⟨x, rfl⟩) _ (hrange ▸ ⟨y, rfl⟩)
  let T'' : Subgroup K := (T : Subgroup ↥R').map R'.subtype
  have hT''card : Nat.card T'' = 81 := by
    rw [Nat.card_congr ((T : Subgroup ↥R').equivMapOfInjective _
      (Subgroup.subtype_injective _)).toEquiv.symm]
    exact Nat.dvd_antisymm hTcard (by
      have h1 := Subgroup.card_ker_mul_card_range φ
      rw [hrange, hPcard] at h1
      exact h1 ▸ dvd_mul_left _ _)
  have hT''c : ∀ x ∈ T'', ∀ y ∈ T'', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    have := hTc ⟨a, ha⟩ ⟨b, hb⟩
    have h2 := congrArg (fun z : ↥(T : Subgroup ↥R') => ((z : ↥R') : K)) this
    simpa using h2
  have hle := card_le_of_abelian_doubleCover hK Nat.prime_three (by norm_num) hT''c
    (IsPGroup.of_card (n := 4) (by rw [hT''card]; norm_num))
  rw [hT''card] at hle
  have hn3 : n / 3 = 3 := by omega
  rw [hn3] at hle
  norm_num at hle

theorem cbar_data {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (hfr : AFrame A zb Sb Vb) {t : A} (ht : orderOf t = 2) {R : Subgroup A}
    (hR : R ≤ centralizer ({t} : Set A)) (hcore : pPrimeCore 2 ↥R = ⊥) :
    ∃ (n : ℕ) (K : Type) (_ : Group K) (_ : Finite K) (R' : Subgroup K),
      (n = 10 ∨ n = 11) ∧ IsDoubleCoverOfAlt K n ∧
        Nonempty (↥R ≃* (↥R' ⧸ pPrimeCore 2 ↥R')) := by
  obtain ⟨n, K, _, R', hn, hK, ⟨e⟩⟩ := hfr.cbar t ht R hR
  have hfin := finite_of_doubleCover hK
  refine ⟨n, K, inferInstance, hfin, R', hn, hK, ⟨?_⟩⟩
  exact ((QuotientGroup.quotientBot).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hcore.symm)).trans e

theorem card_dvd_of_cbar {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (hfr : AFrame A zb Sb Vb) {t : A} (ht : orderOf t = 2) {R : Subgroup A}
    (hR : R ≤ centralizer ({t} : Set A)) (hcore : pPrimeCore 2 ↥R = ⊥) :
    Nat.card ↥R ∣ Nat.factorial 11 := by
  obtain ⟨n, K, _, hfin, R', hn, hK, ⟨ε⟩⟩ := cbar_data hfr ht hR hcore
  have h1 : Nat.card ↥R = (pPrimeCore 2 ↥R').index := Nat.card_congr ε.toEquiv
  have h2 : (pPrimeCore 2 ↥R').index ∣ Nat.card ↥R' := Subgroup.index_dvd_card _
  have h3 : Nat.card ↥R' ∣ Nat.card K := Subgroup.card_subgroup_dvd_card _
  have h4 : Nat.card K = n.factorial := card_doubleCover hK (by omega)
  have h5 : n.factorial ∣ Nat.factorial 11 := Nat.factorial_dvd_factorial (by omega)
  rw [h1]
  exact h2.trans (h3.trans (h4 ▸ h5))

theorem no_abelian_81_of_cbar {A : Type} [Group A] [Finite A] {zb : A} {Sb Vb : Subgroup A}
    (hfr : AFrame A zb Sb Vb) {t : A} (ht : orderOf t = 2) {R : Subgroup A}
    (hR : R ≤ centralizer ({t} : Set A)) (hcore : pPrimeCore 2 ↥R = ⊥) {P : Subgroup A}
    (hPR : P ≤ R) (hPc : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hPcard : Nat.card P = 81) :
    False := by
  obtain ⟨n, K, _, hfin, R', hn, hK, ⟨ε⟩⟩ := cbar_data hfr ht hR hcore
  let P₁ : Subgroup ↥R := P.subgroupOf R
  let Pb : Subgroup (↥R' ⧸ pPrimeCore 2 ↥R') := P₁.map ε.toMonoidHom
  have hP₁card : Nat.card P₁ = 81 := by
    rw [← hPcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPR).toEquiv
  have hPbcard : Nat.card Pb = 81 := by
    rw [← hP₁card]
    exact Nat.card_congr (P₁.equivMapOfInjective _ ε.injective).toEquiv.symm
  refine no_abelian_81 hn hK R' (pPrimeCore 2 ↥R') Pb ?_ hPbcard
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  exact Subtype.ext (hPc _ ha _ hb)

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
