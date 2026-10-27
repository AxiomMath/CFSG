module

public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.TwoANine.InductionSylow

public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve

open Subgroup CFSG.Semidihedral.Principal.PrimewiseScalar

variable {G : Type} [Group G]

theorem card_sup_mul_card_inf {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) :
    Nat.card (X ⊔ Y : Subgroup G) * Nat.card (X ⊓ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  have := Subgroup.normal_subgroupOf_of_le_normalizer h
  have := Subgroup.normal_subgroupOf_sup_of_le_normalizer h
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient X Y h
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf X)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Y.subgroupOf (X ⊔ Y))
  have h3 : Nat.card (Y.subgroupOf X) = Nat.card (X ⊓ Y : Subgroup G) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_comm]
  have h4 : Nat.card (Y.subgroupOf (X ⊔ Y)) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  rw [h2, h4, h1, h3, Nat.card_congr e.toEquiv]
  ring

theorem card_sup_of_inf_eq_bot {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G))
    (hb : X ⊓ Y = ⊥) : Nat.card (X ⊔ Y : Subgroup G) = Nat.card X * Nat.card Y := by
  have := card_sup_mul_card_inf h
  rwa [hb, Subgroup.card_bot, mul_one] at this

theorem exists_mul_of_mem_sup {X Y : Subgroup G} (h : X ≤ normalizer (Y : Set G)) {g : G}
    (hg : g ∈ X ⊔ Y) : ∃ x ∈ X, ∃ y ∈ Y, x * y = g := by
  have hg' : g ∈ ((X ⊔ Y : Subgroup G) : Set G) := hg
  rw [Subgroup.coe_mul_of_left_le_normalizer_right X Y h] at hg'
  obtain ⟨x, hx, y, hy, rfl⟩ := hg'
  exact ⟨x, hx, y, hy, rfl⟩

theorem le_normalizer_of_commute {X Y : Subgroup G} (h : ∀ x ∈ X, ∀ y ∈ Y, x * y = y * x) :
    X ≤ normalizer (Y : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [h x hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have hc := h x hx _ hy
    have h1 : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
      rw [mul_assoc, ← hc, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [show x⁻¹ * (x * y * x⁻¹) * x = y by group] at h1
    rw [h1]
    exact hy

theorem oddCoreOf_map_conj (C : Subgroup G) (g : G) :
    oddCoreOf (C.map (MulAut.conj g).toMonoidHom) =
      (oddCoreOf C).map (MulAut.conj g).toMonoidHom := by
  set f : G →* G := (MulAut.conj g).toMonoidHom
  set B : Subgroup G := C.map f
  let e : C ≃* B := Subgroup.equivMapOfInjective C f (MulAut.conj g).injective
  have hmap : B.subtype.comp e.toMonoidHom = f.comp C.subtype := by
    ext x
    rfl
  calc oddCoreOf B = (CFSG.pPrimeCore 2 B).map B.subtype := rfl
    _ = ((CFSG.pPrimeCore 2 C).map e.toMonoidHom).map B.subtype := by
      rw [CFSG.pPrimeCore_map_iso 2 e]
    _ = (CFSG.pPrimeCore 2 C).map (B.subtype.comp e.toMonoidHom) := by rw [Subgroup.map_map]
    _ = (CFSG.pPrimeCore 2 C).map (f.comp C.subtype) := by rw [hmap]
    _ = ((CFSG.pPrimeCore 2 C).map C.subtype).map f := by rw [Subgroup.map_map]

theorem mem_normalizer_oddCoreOf {C : Subgroup G} {g : G} (hg : g ∈ normalizer (C : Set G)) :
    g ∈ normalizer (oddCoreOf C : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hg ⊢
  exact (oddCoreOf_map_conj C g).symm.trans (congrArg oddCoreOf hg)

theorem le_of_odd_of_card_eq_two_mul [Finite G] {V X B : Subgroup G} (hXV : X ≤ V)
    (hV : V ≤ normalizer (X : Set G)) (hcard : Nat.card V = 2 * Nat.card X) (hBV : B ≤ V)
    (hodd : Odd (Nat.card B)) : B ≤ X := by
  have h1 := card_sup_mul_card_inf (hBV.trans hV)
  have h2 : Nat.card (B ⊔ X : Subgroup G) ∣ 2 * Nat.card X :=
    hcard ▸ Subgroup.card_dvd_of_le (sup_le hBV hXV)
  obtain ⟨d, hd⟩ := Subgroup.card_dvd_of_le (le_sup_right : X ≤ B ⊔ X)
  have hX0 : 0 < Nat.card X := Nat.card_pos
  have hd2 : d ∣ 2 := by
    rw [hd, mul_comm 2] at h2
    exact (Nat.mul_dvd_mul_iff_left hX0).mp h2
  rcases (Nat.dvd_prime Nat.prime_two).mp hd2 with rfl | rfl
  · have : X = B ⊔ X := Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hd, mul_one])
    exact le_sup_left.trans this.symm.le
  · exfalso
    rw [hd] at h1
    have h3 : Nat.card X * (2 * Nat.card (B ⊓ X : Subgroup G)) = Nat.card X * Nat.card B := by
      rw [← mul_assoc, h1, mul_comm]
    have h4 := Nat.eq_of_mul_eq_mul_left hX0 h3
    exact (Nat.not_even_iff_odd.mpr hodd) ⟨_, h4.symm.trans (two_mul _)⟩

theorem le_oddCoreOf_of_card [Finite G] {C B : Subgroup G}
    (hcard : Nat.card C = 2 * Nat.card (oddCoreOf C)) (hBC : B ≤ C) (hodd : Odd (Nat.card B)) :
    B ≤ oddCoreOf C :=
  le_of_odd_of_card_eq_two_mul (oddCoreOf_le C) (le_normalizer_oddCoreOf C) hcard hBC hodd

theorem card_oddCoreOf_mul_of_isCyclic [Finite G] {C P : Subgroup G} (hP : IsSylowOf C 2 P)
    (hcyc : IsCyclic P) (hne : 1 < Nat.card P) :
    Nat.card (oddCoreOf C) * Nat.card P = Nat.card C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, rfl⟩ := hP
  have hcardQ : Nat.card ((Q : Subgroup C).map C.subtype) = Nat.card (Q : Subgroup C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hQcyc : IsCyclic (Q : Subgroup C) :=
    (MulEquiv.isCyclic (Subgroup.equivMapOfInjective _ _ C.subtype_injective)).mpr hcyc
  have hC0 : Nat.card C ≠ 0 := Nat.card_pos.ne'
  have hQcard := Sylow.card_eq_multiplicity Q
  have h2 : 2 ∣ Nat.card C := by
    have hk : (Nat.card C).factorization 2 ≠ 0 := by
      intro h0
      rw [hcardQ, hQcard, h0, pow_zero] at hne
      exact lt_irrefl _ hne
    have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hC0 (k := 1)).mpr
      (Nat.one_le_iff_ne_zero.mpr hk)
    simpa using this
  have hmin : (Nat.card C).minFac = 2 := (Nat.minFac_eq_two_iff _).mpr h2
  have hc := IsCyclic.isComplement' hmin hQcyc
  set K' := (MonoidHom.transferSylow Q (hQcyc.normalizer_le_centralizer hmin)).ker
  have hK'n : K'.Normal := MonoidHom.normal_ker _
  have hmul : Nat.card K' * Nat.card (Q : Subgroup C) = Nat.card C := hc.card_mul_card
  have hK'eq : Nat.card K' = Nat.card C / 2 ^ (Nat.card C).factorization 2 := by
    rw [← hQcard]
    exact (Nat.div_eq_of_eq_mul_left Nat.card_pos hmul.symm).symm
  have hcop : Nat.Coprime 2 (Nat.card K') := by
    rw [hK'eq]
    exact Nat.coprime_ordCompl Nat.prime_two hC0
  have hle : K' ≤ CFSG.pPrimeCore 2 C := le_sSup ⟨hK'n, hcop⟩
  have hO : Nat.card (oddCoreOf C) = Nat.card (CFSG.pPrimeCore 2 C) :=
    Subgroup.card_map_of_injective C.subtype_injective
  have hOcop : Nat.Coprime (Nat.card (CFSG.pPrimeCore 2 C)) (Nat.card (Q : Subgroup C)) := by
    rw [hQcard]
    exact Nat.Coprime.pow_right _ (Nat.coprime_comm.mp CFSG.pPrimeCore_coprime_card)
  have hdvd : Nat.card (CFSG.pPrimeCore 2 C) ∣ Nat.card K' := by
    refine hOcop.dvd_of_dvd_mul_right ?_
    rw [hmul]
    exact Subgroup.card_subgroup_dvd_card _
  have heq : Nat.card (CFSG.pPrimeCore 2 C) = Nat.card K' :=
    le_antisymm (Nat.le_of_dvd Nat.card_pos hdvd) (Subgroup.card_le_of_le hle)
  rw [hO, heq, hcardQ, hmul]

theorem oddCore_eq_pPrimeCore (X : Type) [Group X] [Finite X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  apply le_antisymm
  · exact sSup_le fun N hN => le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩
  · have hn : (CFSG.pPrimeCore 2 X).Normal := CFSG.pPrimeCore_normal
    exact le_sSup ⟨hn, Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (G := X) (p := 2))⟩

theorem exists_mul_oddCoreOf_of_quaternion [Finite G] {X T : Subgroup G} {z : G}
    (hz : orderOf z = 2) (hT : IsSylowOf X 2 T) (hzT : z ∈ T)
    (hquat : Nonempty (T ≃* QuaternionGroup 2)) :
    ∀ g ∈ X, ∃ c ∈ X ⊓ centralizer ({z} : Set G), ∃ k ∈ oddCoreOf X, g = c * k := by
  obtain ⟨φ⟩ := hquat
  obtain ⟨P, rfl⟩ := hT
  have hzX : z ∈ X := Subgroup.map_subtype_le _ hzT
  have hPq : Nonempty ((P : Subgroup X) ≃* QuaternionGroup (2 ^ (3 - 2))) :=
    ⟨(Subgroup.equivMapOfInjective _ _ X.subtype_injective).trans φ⟩
  have hzmem : (⟨z, hzX⟩ : X) ∈ (P : Subgroup X) := by
    obtain ⟨w, hw, hwz⟩ := hzT
    have : w = ⟨z, hzX⟩ := Subtype.ext hwz
    rw [← this]
    exact hw
  have hzord : orderOf (⟨z, hzX⟩ : X) = 2 := by
    rw [← hz]
    exact Subgroup.orderOf_mk z hzX
  obtain ⟨-, hcen⟩ := CFSG.Adapters.brauer_suzuki (G := X) 3 le_rfl P hPq ⟨z, hzX⟩ hzmem hzord
  have hzz : (⟨z, hzX⟩ : X) * ⟨z, hzX⟩ = 1 := by
    have := pow_orderOf_eq_one (⟨z, hzX⟩ : X)
    rwa [hzord, sq] at this
  intro g hg
  obtain ⟨c, hc, k, hk, hgck⟩ := CFSG.Adapters.eq_centralizer_mul_oddCore hzz hcen ⟨g, hg⟩
  rw [oddCore_eq_pPrimeCore] at hk
  refine ⟨c.1, Subgroup.mem_inf.mpr ⟨c.2, ?_⟩, k.1, ⟨k, hk, rfl⟩, congrArg Subtype.val hgck⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hc)

theorem card_le_of_isPGroup_le [Finite G] {B W : Subgroup G} (hB : IsPGroup 3 B) (hBW : B ≤ W) :
    Nat.card B ≤ 3 ^ (Nat.card W).factorization 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hB
  rw [hk]
  refine Nat.pow_le_pow_right (by norm_num) ?_
  have h := Subgroup.card_dvd_of_le hBW
  rw [hk] at h
  exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three Nat.card_pos.ne').mp h

theorem factorization_le_of_dvd {a n : ℕ} (hn : n ≠ 0) (h : a ∣ n) (p : ℕ) :
    a.factorization p ≤ n.factorization p :=
  (Nat.factorization_le_iff_dvd (ne_zero_of_dvd_ne_zero hn h) hn).mpr h p

theorem factorization_card_twoANine : (362880 : ℕ).factorization 3 = 4 := by
  rw [show (362880 : ℕ) = 3 ^ 4 * 4480 by norm_num,
    Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)]

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine.JankoTwelve
