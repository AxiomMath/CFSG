module

public import CFSG.Dihedral.Glauberman.DicksonMaxList
public import CFSG.CharacterTheory.Burnside
public import CFSG.Adapters.LinearSmallCatalog
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Hall32Basic
public import CFSG.LocalAnalysis.ComponentClassification.Asc76Thm3FourTwo
public import CFSG.LocalAnalysis.ComponentInitial.FieldNineAlternatingSix

public section

namespace CFSG.ComponentClassification.Asc76X.Thm3Four

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.Asc76
open CFSG.ComponentClassification.Asc76X
open CFSG.LocalAnalysis.ComponentInitial
  (unique_field_nine_projective_linear_alternating_six_isomorphism)
open scoped MatrixGroups

theorem factorization_two_pow_mul {a m : ℕ} (hm : Odd m) : (2 ^ a * m).factorization 2 = a := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact absurd hm (by decide)
  rw [Nat.factorization_mul (pow_ne_zero a two_ne_zero) hm0, Finsupp.add_apply,
    Nat.prime_two.factorization_pow, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (fun h => (Nat.not_even_iff_odd.mpr hm)
      (even_iff_two_dvd.mpr h)), add_zero]

theorem isSolvable_of_card_two_three {X : Type*} [Group X] [Finite X] {a b : ℕ}
    (h : Nat.card X = 2 ^ a * 3 ^ b) : Group.IsSolvable X := by
  have : Fintype X := Fintype.ofFinite X
  exact CFSG.Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow Nat.prime_two
    Nat.prime_three (by norm_num) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem a4_sq_mul : ∀ a b : alternatingGroup (Fin 4), a * a = 1 → b * b = 1 →
    a * b * (a * b) = 1 := by
  decide

@[expose] def a4V : Subgroup (alternatingGroup (Fin 4)) where
  carrier := {σ | σ * σ = 1}
  mul_mem' {a b} ha hb := a4_sq_mul a b ha hb
  one_mem' := mul_one 1
  inv_mem' {a} ha := by
    change a⁻¹ * a⁻¹ = 1
    rw [← mul_inv_rev, show a * a = 1 from ha, inv_one]

theorem card_a4V : Nat.card a4V = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (p := (· ∈ a4V))
    (q := fun σ => σ * σ = 1) (fun _ => Iff.rfl)), Nat.card_eq_fintype_card]
  decide

theorem s4_mul : ∀ a b : Equiv.Perm (Fin 4), (a * a = 1 ∧ Equiv.Perm.sign a = 1) →
    (b * b = 1 ∧ Equiv.Perm.sign b = 1) →
    (a * b * (a * b) = 1 ∧ Equiv.Perm.sign (a * b) = 1) := by
  decide

@[expose] def s4V : Subgroup (Equiv.Perm (Fin 4)) where
  carrier := {σ | σ * σ = 1 ∧ Equiv.Perm.sign σ = 1}
  mul_mem' {a b} ha hb := s4_mul a b ha hb
  one_mem' := ⟨mul_one 1, map_one _⟩
  inv_mem' {a} ha := by
    refine ⟨?_, by rw [map_inv, ha.2, inv_one]⟩
    change a⁻¹ * a⁻¹ = 1
    rw [← mul_inv_rev, ha.1, inv_one]

theorem card_s4V : Nat.card s4V = 4 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight (p := (· ∈ s4V))
    (q := fun σ => σ * σ = 1 ∧ Equiv.Perm.sign σ = 1) (fun _ => Iff.rfl)),
    Nat.card_eq_fintype_card]
  decide

theorem s4_trans : ∀ σ τ : Equiv.Perm (Fin 4), (σ * σ = 1 ∧ Equiv.Perm.sign σ = 1) →
    (τ * τ = 1 ∧ Equiv.Perm.sign τ = 1) → σ ≠ 1 → τ ≠ 1 →
    ∃ g : Equiv.Perm (Fin 4), g * σ * g⁻¹ = τ := by
  decide

theorem s4_pair : ∀ a b : Equiv.Perm (Fin 4), a * a = 1 → b * b = 1 → a ≠ 1 → b ≠ 1 → a ≠ b →
    a * b = b * a →
    (Equiv.Perm.sign a = 1 ∨ Equiv.Perm.sign b = 1 ∨ Equiv.Perm.sign (a * b) = 1) := by
  decide

theorem psl2_overgroup {F : Type} [Field F] [Finite F] {p f : ℕ}
    [hp : Fact p.Prime] (hF : Nat.card F = p ^ f) (hq : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9)
    (H : Subgroup PSL(2, F)) (hH : H ≠ ⊤) {P : Subgroup PSL(2, F)} (hP : IsSylowOf 2 P ⊤)
    (hPH : P ≤ H) :
    IsPGroup 2 H ∨ Nonempty (H ≃* alternatingGroup (Fin 4)) ∨
      Nonempty (H ≃* Equiv.Perm (Fin 4)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpf : (p = 5 ∧ f = 1) ∨ (p = 7 ∧ f = 1) ∨ (p = 3 ∧ f = 2) := by
    have hf0 : f ≠ 0 := by
      rintro rfl
      rcases hq with h | h | h <;> simp at h
    have hpd : p ∣ p ^ f := dvd_pow_self p hf0
    rcases hq with h | h | h <;> rw [h] at hpd
    · have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp hpd
      subst hp5
      exact Or.inl ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 5)
        (h.trans (pow_one 5).symm)⟩
    · have hp7 : p = 7 := (Nat.prime_dvd_prime_iff_eq hp.out (by norm_num)).mp hpd
      subst hp7
      exact Or.inr (Or.inl ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 7)
        (h.trans (pow_one 7).symm)⟩)
    · have hp3 : p = 3 := by
        have h1 : p ∣ 3 ^ 2 := by norm_num; exact hpd
        exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).mp
          (hp.out.dvd_of_dvd_pow h1)
      subst hp3
      exact Or.inr (Or.inr ⟨rfl, Nat.pow_right_injective (by norm_num : 2 ≤ 3)
        (h.trans (by norm_num : (9 : ℕ) = 3 ^ 2))⟩)
  have hpodd : Odd p := by
    rcases hpf with ⟨rfl, -⟩ | ⟨rfl, -⟩ | ⟨rfl, -⟩ <;> decide
  have hf1 : 1 ≤ f := by
    rcases hpf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num
  have hIOP : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card F) :=
    ⟨p, f, hp.out, hpodd, hf1, hF⟩
  have hcardX : Nat.card PSL(2, F) = p ^ f * ((p ^ f) ^ 2 - 1) / 2 := by
    rw [CFSG.GorensteinWalter.psl2_card_formula F hIOP, hF]
  have hHdvd : Nat.card H ∣ Nat.card PSL(2, F) := card_subgroup_dvd_card H
  have hHne : Nat.card H ≠ Nat.card PSL(2, F) := fun e => hH (card_eq_iff_eq_top H |>.mp e)
  have hHpos : 0 < Nat.card H := Nat.card_pos
  have hd : 2 ^ (Nat.card PSL(2, F)).factorization 2 ∣ Nat.card H := by
    have h1 := (isSylowOf_iff_card.mp hP).2
    rw [card_top] at h1
    rw [← h1]
    exact card_dvd_of_le hPH
  rw [hcardX] at hd hHdvd hHne
  have h2 : (p ^ f = 5 ∧ 4 ∣ Nat.card H) ∨ (p ^ f ≠ 5 ∧ 8 ∣ Nat.card H) := by
    rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · left
      rw [show 5 ^ 1 * ((5 ^ 1) ^ 2 - 1) / 2 = 2 ^ 2 * 15 by norm_num,
        factorization_two_pow_mul (by decide)] at hd
      exact ⟨by norm_num, hd⟩
    · right
      rw [show 7 ^ 1 * ((7 ^ 1) ^ 2 - 1) / 2 = 2 ^ 3 * 21 by norm_num,
        factorization_two_pow_mul (by decide)] at hd
      exact ⟨by norm_num, hd⟩
    · right
      rw [show 3 ^ 2 * ((3 ^ 2) ^ 2 - 1) / 2 = 2 ^ 3 * 45 by norm_num,
        factorization_two_pow_mul (by decide)] at hd
      exact ⟨by norm_num, hd⟩
  clear hd hP hPH hcardX hIOP
  have h4 : 4 ∣ Nat.card H := by
    rcases h2 with ⟨-, h⟩ | ⟨-, h⟩
    · exact h
    · exact (by norm_num : 4 ∣ 8).trans h
  rcases CFSG.Glauberman.Dickson.dickson_psl2_subgroup_list hF H with
    ⟨m, -, hcard, -⟩ | ⟨z, hz, hcard, -⟩ | ⟨z, hz2, hz, ⟨e⟩⟩ | ⟨-, eA⟩ | ⟨-, eS⟩ | ⟨-, ⟨e⟩⟩ |
      ⟨m, t, -, -, -, htq, E, C, -, -, hE, -, hC, -, -, -, φ, -, ⟨e⟩⟩ | ⟨m, hmf, ⟨e⟩⟩ |
      ⟨m, hmf, ⟨e⟩⟩
  ·
    exfalso
    have h2' : 2 ∣ p ^ m := by
      rw [← hcard]
      exact (by norm_num : 2 ∣ 4).trans h4
    exact (Nat.not_even_iff_odd.mpr hpodd.pow) (even_iff_two_dvd.mpr h2')
  ·
    exfalso
    rw [hcard] at h2 h4 hHpos
    have hz4 : 4 ≤ z := Nat.le_of_dvd hHpos h4
    rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · norm_num at hz
      rcases hz with hz | hz <;> have := Nat.le_of_dvd (by norm_num) hz <;> omega
    · norm_num at hz h2
      have hz8 := Nat.le_of_dvd hHpos h2
      rcases hz with hz | hz <;> have := Nat.le_of_dvd (by norm_num) hz <;> omega
    · norm_num at hz h2
      have hz8 := Nat.le_of_dvd hHpos h2
      rcases hz with hz | hz <;> have := Nat.le_of_dvd (by norm_num) hz <;> omega
  ·
    left
    have hcard : Nat.card H = 2 * z := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [hcard] at h2 h4 hHpos
    have hz' : z = 2 ∨ z = 4 := by
      rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · norm_num at hz
        have hzle : z ≤ 3 := by
          rcases hz with hz | hz <;> have := Nat.le_of_dvd (by norm_num) hz <;> omega
        interval_cases z <;> omega
      · norm_num at hz h2
        have hzle : z ≤ 4 := by
          rcases hz with hz | hz <;> have := Nat.le_of_dvd (by norm_num) hz <;> omega
        interval_cases z <;> omega
      · norm_num at hz h2
        have hzle : z ≤ 5 := by
          rcases hz with hz | hz <;> have := Nat.le_of_dvd (by norm_num) hz <;> omega
        interval_cases z <;> omega
    rcases hz' with rfl | rfl
    · exact IsPGroup.of_card (n := 2) (by rw [hcard]; norm_num)
    · exact IsPGroup.of_card (n := 3) (by rw [hcard]; norm_num)
  · exact Or.inr (Or.inl eA)
  · exact Or.inr (Or.inr eS)
  ·
    exfalso
    have hcard : Nat.card H = 60 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
    rw [hcard] at h2 hHdvd hHne
    rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hHne (by norm_num)
    · exact absurd hHdvd (by norm_num)
    · norm_num at h2
  ·
    exfalso
    have hcard : Nat.card H = p ^ m * t := by
      rw [Nat.card_congr (e.toEquiv.trans SemidirectProduct.equivProd), Nat.card_prod, hE, hC]
    have h2p : Nat.Coprime 2 p := Nat.coprime_two_left.mpr hpodd
    have h4t : 4 ∣ t := by
      rw [hcard] at h4
      exact (by simpa using Nat.Coprime.pow 2 m h2p : Nat.Coprime 4 (p ^ m)).dvd_of_dvd_mul_left h4
    have ht0 : t ≠ 0 := by
      rintro rfl
      rw [hcard, mul_zero] at hHpos
      exact absurd hHpos (lt_irrefl 0)
    rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> norm_num at htq h2
    · have := Nat.le_of_dvd (by norm_num) htq
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) h4t
      omega
    · have := Nat.le_of_dvd (by norm_num) htq
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) h4t
      omega
    · have h8t : 8 ∣ t := by
        rw [hcard] at h2
        exact (by simpa using Nat.Coprime.pow 3 m h2p : Nat.Coprime 8 (3 ^ m)).dvd_of_dvd_mul_left
          h2
      have := Nat.le_of_dvd (by norm_num) htq
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero ht0) h8t
      omega
  ·
    exfalso
    have hm0 : m ≠ 0 := by
      rintro rfl
      rcases hpf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num at hmf
    have hIOP' : CFSG.GorensteinWalter.IsOddPrimePower (Nat.card (GaloisField p m)) :=
      ⟨p, m, hp.out, hpodd, Nat.one_le_iff_ne_zero.mpr hm0, GaloisField.card p m hm0⟩
    have hcard : Nat.card H = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
      rw [Nat.card_congr e.toEquiv]
      change Nat.card (CFSG.GorensteinWalter.PSL2 (GaloisField p m)) = _
      rw [CFSG.GorensteinWalter.psl2_card_formula _ hIOP', GaloisField.card p m hm0]
    rw [hcard] at h2 hHne
    have hmle : m ≤ f := Nat.le_of_dvd (by omega) hmf
    rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · have : m = 1 := by omega
      subst this
      exact hHne rfl
    · have : m = 1 := by omega
      subst this
      exact hHne rfl
    · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm0
      interval_cases m
      · norm_num at h2
      · exact hHne rfl
  ·
    have hm0 : m ≠ 0 := by
      rintro rfl
      rcases hpf with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;> norm_num at hmf
    rcases hpf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exfalso
      have := Nat.le_of_dvd (by norm_num) hmf
      omega
    · exfalso
      have := Nat.le_of_dvd (by norm_num) hmf
      omega
    · have hm1 : m = 1 := by
        have := Nat.le_of_dvd (by norm_num) hmf
        omega
      subst hm1
      right; right
      exact ⟨e.trans ((CFSG.GorensteinWalter.pgl2RingEquiv
        (GaloisField.equivZmodP 3).toRingEquiv).trans CFSG.GorensteinWalter.pgl2_three_equiv_perm)⟩

variable {X : Type} [Group X]

theorem le_normalizer_of_conj {H V : Subgroup X}
    (hV : ∀ h ∈ H, ∀ v ∈ V, h * v * h⁻¹ ∈ V) : H ≤ normalizer (V : Set X) := fun h hh =>
  mem_normalizer_iff.mpr fun y => ⟨fun hy => hV h hh y hy, fun hy => by
    have h1 := hV h⁻¹ (inv_mem hh) _ hy
    have e : h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ = y := by group
    rwa [e] at h1⟩

theorem card_pullback {H : Subgroup X} {Y : Type*} [Group Y] (e : H ≃* Y) (V : Subgroup Y) :
    Nat.card ((V.comap e.toMonoidHom).map H.subtype) = Nat.card V := by
  rw [card_map_of_injective H.subtype_injective, comap_equiv_eq_map_symm',
    card_map_of_injective e.symm.injective]

variable [Finite X]

theorem local_of_psl2 {F : Type} [Field F] [Finite F] {p f : ℕ}
    [Fact p.Prime] (hF : Nat.card F = p ^ f) (hq : p ^ f = 5 ∨ p ^ f = 7 ∨ p ^ f = 9)
    (e : X ≃* PSL(2, F)) (K R S : Subgroup X) (hK : TightlyEmbedded K) (hKn : ¬ K.Normal)
    (hR : IsSylowOf 2 R K) (hRe : IsElemAbelian 2 R) (h4 : Nat.card R = 4)
    (hS : IsSylowOf 2 S ⊤) (hRS : R ≤ S)
    (hwc : ∀ g : X, rightConjugate R g ≤ S → rightConjugate R g = R) :
    (R.subgroupOf K).Normal ∧ Group.IsSolvable (normalizer (K : Set X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := normalizer (K : Set X) with hHdef
  have hHtop : H ≠ ⊤ := fun h => hKn (normalizer_eq_top_iff.mp h)
  have hRK : R ≤ K := hR.le
  have hKH : K ≤ H := le_normalizer
  have hRH : R ≤ H := hRK.trans hKH
  have hR2 : IsPGroup 2 R := hR.isPGroup
  have hRne : R ≠ ⊥ := fun h => by
    rw [h, card_bot] at h4
    exact absurd h4 (by norm_num)
  have hSN : S ≤ normalizer (R : Set X) := Hall32.le_normalizer_of_weaklyClosed hRS hwc
  have hNH : normalizer (R : Set X) ≤ H := normalizer_two_subgroup_le K R hK hR2 hRK hRne
  have hSH : S ≤ H := hSN.trans hNH
  have hsq : ∀ r ∈ R, r * r = 1 := fun r hr => by
    rw [← pow_two]
    exact hRe.2 r hr
  set H' := H.map e.toMonoidHom with hH'def
  have hH'top : H' ≠ ⊤ := fun h => hHtop (by
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ H' := by rw [h]; exact mem_top _
    obtain ⟨y, hy, hyx⟩ := hx
    rw [← e.injective hyx]
    exact hy)
  have hP : IsSylowOf 2 (S.map e.toMonoidHom) ⊤ := by
    rw [isSylowOf_iff_card] at hS ⊢
    refine ⟨le_top, ?_⟩
    rw [card_map_of_injective e.injective, hS.2, card_top, card_top, Nat.card_congr e.toEquiv]
  have eH : H ≃* H' := H.equivMapOfInjective e.toMonoidHom e.injective
  suffices hRn : H ≤ normalizer (R : Set X) ∧ Group.IsSolvable H by
    exact ⟨(normal_subgroupOf_iff_le_normalizer hRK).mpr (hKH.trans hRn.1), hRn.2⟩
  rcases psl2_overgroup hF hq H' hH'top hP (map_mono hSH) with h2 | hA | hT
  ·
    have hH2 : IsPGroup 2 H := h2.of_equiv eH.symm
    have hKR : K = R := hR.eq_of_le hRK le_rfl (hH2.to_le hKH)
    refine ⟨by rw [hHdef, hKR], ?_⟩
    have : Group.IsNilpotent H := hH2.isNilpotent
    infer_instance
  ·
    obtain ⟨eA⟩ := hA
    let eHA : H ≃* alternatingGroup (Fin 4) := eH.trans eA
    set V := (a4V.comap eHA.toMonoidHom).map H.subtype with hVdef
    have hmemV : ∀ h : H, (h : X) ∈ V ↔ h * h = 1 := fun h => by
      constructor
      · rintro ⟨w, hw, hwh⟩
        have hw' : eHA w * eHA w = 1 := hw
        rw [← map_mul, ← map_one eHA] at hw'
        have := eHA.injective hw'
        rw [← Subtype.ext hwh]
        exact this
      · intro hh
        refine ⟨h, ?_, rfl⟩
        change eHA h * eHA h = 1
        rw [← map_mul, hh, map_one]
    have hRV : R ≤ V := fun r hr => (hmemV ⟨r, hRH hr⟩).mpr (Subtype.ext (hsq r hr))
    have hVcard : Nat.card V = 4 := by rw [hVdef, card_pullback, card_a4V]
    have hRVeq : R = V := eq_of_le_of_card_ge hRV (by rw [hVcard, h4])
    refine ⟨?_, ?_⟩
    · rw [hRVeq]
      refine le_normalizer_of_conj fun h hh v hv => ?_
      have hvH : v ∈ H := by
        obtain ⟨w, -, rfl⟩ := hv
        exact w.2
      have hv' := (hmemV ⟨v, hvH⟩).mp (by exact hv)
      have hc : h * v * h⁻¹ ∈ H := mul_mem (mul_mem hh hvH) (inv_mem hh)
      refine (hmemV ⟨_, hc⟩).mpr (Subtype.ext ?_)
      have hv'' : v * v = 1 := congrArg Subtype.val hv'
      calc h * v * h⁻¹ * (h * v * h⁻¹) = h * (v * v) * h⁻¹ := by group
        _ = 1 := by rw [hv'']; group
    · refine isSolvable_of_card_two_three (a := 2) (b := 1) ?_
      rw [Nat.card_congr eHA.toEquiv, nat_card_alternatingGroup]
      simp [Nat.factorial]
  ·
    obtain ⟨eT⟩ := hT
    let eHT : H ≃* Equiv.Perm (Fin 4) := eH.trans eT
    set V := (s4V.comap eHT.toMonoidHom).map H.subtype with hVdef
    have hmemV : ∀ h : H, (h : X) ∈ V ↔ eHT h * eHT h = 1 ∧ Equiv.Perm.sign (eHT h) = 1 :=
      fun h => by
        constructor
        · rintro ⟨w, hw, hwh⟩
          rw [← Subtype.ext hwh]
          exact hw
        · intro hh
          exact ⟨h, hh, rfl⟩
    have hVcard : Nat.card V = 4 := by rw [hVdef, card_pullback, card_s4V]
    have hVH : V ≤ H := map_subtype_le _
    have hVn : H ≤ normalizer (V : Set X) := by
      refine le_normalizer_of_conj fun h hh v hv => ?_
      have hvH : v ∈ H := hVH hv
      have hv' := (hmemV ⟨v, hvH⟩).mp hv
      have hc : h * v * h⁻¹ ∈ H := mul_mem (mul_mem hh hvH) (inv_mem hh)
      refine (hmemV ⟨_, hc⟩).mpr ?_
      have e1 : eHT ⟨_, hc⟩ = eHT ⟨h, hh⟩ * eHT ⟨v, hvH⟩ * (eHT ⟨h, hh⟩)⁻¹ := by
        rw [← map_inv, ← map_mul, ← map_mul]
        rfl
      rw [e1]
      refine ⟨?_, ?_⟩
      · calc eHT ⟨h, hh⟩ * eHT ⟨v, hvH⟩ * (eHT ⟨h, hh⟩)⁻¹ *
              (eHT ⟨h, hh⟩ * eHT ⟨v, hvH⟩ * (eHT ⟨h, hh⟩)⁻¹) =
            eHT ⟨h, hh⟩ * (eHT ⟨v, hvH⟩ * eHT ⟨v, hvH⟩) * (eHT ⟨h, hh⟩)⁻¹ := by group
          _ = 1 := by rw [hv'.1]; group
      · rw [map_mul, map_mul, map_inv, hv'.2, mul_one, mul_inv_cancel]
    obtain ⟨d, hdR, hd1, hdV⟩ : ∃ d ∈ R, d ≠ 1 ∧ d ∈ V := by
      obtain ⟨a, haR, ha1, -⟩ := exists_mem_ne_ne' (T := R) (by omega) 1 1
      obtain ⟨b, hbR, hb1, hba⟩ := exists_mem_ne_ne' (T := R) (by omega) 1 a
      have hcomm : a * b = b * a := by
        have h1 : (⟨a, haR⟩ : R) * ⟨b, hbR⟩ = ⟨b, hbR⟩ * ⟨a, haR⟩ := hRe.1.is_comm.comm _ _
        exact congrArg Subtype.val h1
      set a' := eHT ⟨a, hRH haR⟩
      set b' := eHT ⟨b, hRH hbR⟩
      have ha2 : a' * a' = 1 := by
        rw [← map_mul, show (⟨a, hRH haR⟩ : H) * ⟨a, hRH haR⟩ = 1 from
          Subtype.ext (hsq a haR), map_one]
      have hb2 : b' * b' = 1 := by
        rw [← map_mul, show (⟨b, hRH hbR⟩ : H) * ⟨b, hRH hbR⟩ = 1 from
          Subtype.ext (hsq b hbR), map_one]
      have ha1' : a' ≠ 1 := fun h => ha1 (congrArg Subtype.val (eHT.injective (h.trans
        (map_one eHT).symm)))
      have hb1' : b' ≠ 1 := fun h => hb1 (congrArg Subtype.val (eHT.injective (h.trans
        (map_one eHT).symm)))
      have hab' : a' ≠ b' := fun h => hba (congrArg Subtype.val (eHT.injective h)).symm
      have hc' : a' * b' = b' * a' := by
        rw [← map_mul, ← map_mul]
        congr 1
        exact Subtype.ext hcomm
      have hab1 : a * b ≠ 1 := fun h => hba (by
        have e1 : b = a⁻¹ := eq_inv_of_mul_eq_one_right h
        rw [e1, inv_eq_of_mul_eq_one_left (hsq a haR)])
      rcases s4_pair a' b' ha2 hb2 ha1' hb1' hab' hc' with hs | hs | hs
      · exact ⟨a, haR, ha1, (hmemV ⟨a, hRH haR⟩).mpr ⟨ha2, hs⟩⟩
      · exact ⟨b, hbR, hb1, (hmemV ⟨b, hRH hbR⟩).mpr ⟨hb2, hs⟩⟩
      · refine ⟨a * b, mul_mem haR hbR, hab1, (hmemV ⟨a * b, hRH (mul_mem haR hbR)⟩).mpr ?_⟩
        have e1 : eHT ⟨a * b, hRH (mul_mem haR hbR)⟩ = a' * b' := by
          rw [← map_mul]
          rfl
        rw [e1]
        refine ⟨?_, hs⟩
        calc a' * b' * (a' * b') = a' * a' * (b' * b') := by
              rw [mul_assoc a', ← mul_assoc b', ← hc', mul_assoc a', ← mul_assoc]
          _ = 1 := by rw [ha2, hb2, one_mul]
    have hVK : V ≤ K := fun v hv => by
      by_cases hv1 : v = 1
      · rw [hv1]
        exact one_mem K
      have hvH : v ∈ H := hVH hv
      have hdH : d ∈ H := hRH hdR
      have hdV' := (hmemV ⟨d, hdH⟩).mp hdV
      have hvV' := (hmemV ⟨v, hvH⟩).mp hv
      have hd1' : eHT ⟨d, hdH⟩ ≠ 1 := fun h => hd1 (congrArg Subtype.val (eHT.injective (h.trans
        (map_one eHT).symm)))
      have hv1' : eHT ⟨v, hvH⟩ ≠ 1 := fun h => hv1 (congrArg Subtype.val (eHT.injective (h.trans
        (map_one eHT).symm)))
      obtain ⟨g, hg⟩ := s4_trans _ _ hdV' hvV' hd1' hv1'
      set h := eHT.symm g with hhdef
      have hgh : g = eHT h := (eHT.apply_symm_apply g).symm
      have hvh : (⟨v, hvH⟩ : H) = h * ⟨d, hdH⟩ * h⁻¹ := by
        apply eHT.injective
        rw [map_mul, map_mul, map_inv, ← hgh, hg]
      have hv' : v = (h : X) * d * (h : X)⁻¹ := congrArg Subtype.val hvh
      rw [hv']
      exact (mem_normalizer_iff.mp h.2 d).mp (hRK hdR)
    have hV2 : IsPGroup 2 V := IsPGroup.of_card (n := 2) (by rw [hVcard]; norm_num)
    have hVR2 : IsPGroup 2 ↥(V ⊔ R) := hV2.to_sup_of_normal_left' hR2 (hRH.trans hVn)
    have hVR : V ⊔ R = R := hR.eq_of_le le_sup_right (sup_le hVK hRK) hVR2
    have hVR' : V = R := eq_of_le_of_card_ge (hVR ▸ le_sup_left) (by rw [hVcard, h4])
    refine ⟨hVR' ▸ hVn, ?_⟩
    refine isSolvable_of_card_two_three (a := 3) (b := 1) ?_
    rw [Nat.card_congr eHT.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    norm_num

theorem local_of_small_psl2
    (hX : Nonempty (X ≃* PSL(2, ZMod 7)) ∨ Nonempty (X ≃* alternatingGroup (Fin 5)) ∨
      Nonempty (X ≃* alternatingGroup (Fin 6)))
    (K R S : Subgroup X) (hK : TightlyEmbedded K) (hKn : ¬ K.Normal) (hR : IsSylowOf 2 R K)
    (hRe : IsElemAbelian 2 R) (h4 : Nat.card R = 4) (hS : IsSylowOf 2 S ⊤) (hRS : R ≤ S)
    (hwc : ∀ g : X, rightConjugate R g ≤ S → rightConjugate R g = R) :
    (R.subgroupOf K).Normal ∧ Group.IsSolvable (normalizer (K : Set X)) := by
  rcases hX with he | he | he <;> obtain ⟨e⟩ := he
  · have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    exact local_of_psl2 (p := 7) (f := 1) ((Nat.card_zmod 7).trans (pow_one 7).symm)
      (Or.inr (Or.inl (by norm_num))) e K R S hK hKn hR hRe h4 hS hRS hwc
  · have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e5⟩ := CFSG.ClassicalModels.nonempty_statedLinearModel_equiv_alternating_five
      (ZMod 5) (Or.inr (by rw [Nat.card_zmod]))
    let e' : X ≃* PSL(2, ZMod 5) := e.trans (e5.symm.trans
      (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 (ZMod 5)).symm)
    exact local_of_psl2 (p := 5) (f := 1) ((Nat.card_zmod 5).trans (pow_one 5).symm)
      (Or.inl (by norm_num)) e' K R S hK hKn hR hRe h4 hS hRS hwc
  · have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    have : Fintype (GaloisField 3 2) := Fintype.ofFinite _
    have hcard : Nat.card (GaloisField 3 2) = 3 ^ 2 := GaloisField.card 3 2 (by norm_num)
    obtain ⟨e6⟩ := unique_field_nine_projective_linear_alternating_six_isomorphism
      (GaloisField 3 2) (by rw [← Nat.card_eq_fintype_card, hcard]; norm_num)
    exact local_of_psl2 (p := 3) (f := 2) hcard (Or.inr (Or.inr (by norm_num)))
      (e.trans e6.symm) K R S hK hKn hR hRe h4 hS hRS hwc

end CFSG.ComponentClassification.Asc76X.Thm3Four
