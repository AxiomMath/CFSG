module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk93WLeaves
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95M12
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk95J2
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4J3
public import CFSG.GH74.GLS.IVK.Proofs2.Ivk73G4M23

public section

namespace CFSG.GH74.GLS.IVK.Proofs2

open Subgroup CFSG CFSG.ABGLocalTools CFSG.Blueprint CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore
  CFSG.Sporadic.SmallOddCore.Native CFSG.ComponentClassification.M12Cover
  CFSG.GH74.Generic.S45 CFSG.GH74.Generic.S45.EvSpor CFSG.GH74.GLS.IVK
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

theorem nu2_eq_of {n k : ℕ} (hn : n ≠ 0) (h1 : 2 ^ k ∣ n) (h2 : ¬ 2 ^ (k + 1) ∣ n) :
    n.factorization 2 = k := by
  apply le_antisymm
  · by_contra hlt
    exact h2 ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).2 (by omega))
  · exact (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).1 h1

theorem hN1920 : ∀ q : ℕ, 5 ≤ q → q * (q ^ 2 - 1) ∣ 1920 →
    ¬ (1920 : ℕ).factorization 2 ≤ (q * (q ^ 2 - 1)).factorization 2 + 3 := by
  intro q hq5 hd hle
  have h1920 : (1920 : ℕ).factorization 2 = 7 := nu2_eq_of (by norm_num) (by norm_num) (by norm_num)
  have hle' : q * (q ^ 2 - 1) ≤ 1920 := Nat.le_of_dvd (by norm_num) hd
  have hq : q ≤ 12 := by
    by_contra h
    push Not at h
    have := sl2_card_mono (show 13 ≤ q by omega)
    norm_num at this
    omega
  interval_cases q
  · have h5 : (5 * (5 ^ 2 - 1) : ℕ).factorization 2 = 3 :=
      nu2_eq_of (by norm_num) (by norm_num) (by norm_num)
    rw [h1920, h5] at hle
    omega
  all_goals (exfalso; norm_num at hd)

theorem Ivk93W.card_cent_of_model_class {M : Type} [Group M] {P R A : Subgroup M} {tX : M}
    (hM : Ivk73Model P R A tX) {J : Type} [Group J] [Finite J] {x : J} {q : ℕ} {B : Subgroup J}
    (_h : Ivk93W x q B) (θ : J ≃* ↥P) {g : M} (hg : g ∈ R)
    (hgt : ((θ x : ↥P) : M) = g * tX * g⁻¹) : Nat.card ↥(centralizer ({x} : Set J)) = 240 := by
  have hnorm : ∀ y ∈ P, g * y * g⁻¹ ∈ P := hM.autModel.conj_mem g hg
  have hnorm' : ∀ y ∈ P, g⁻¹ * y * g ∈ P := fun y hy => by
    simpa using hM.autModel.conj_mem g⁻¹ (R.inv_mem hg) y hy
  rw [GHInv.card_centralizer_eq_centralizerIn P θ x, hgt,
    GHInv.card_centralizerIn_conj_of_norm hnorm hnorm', hM.card_cent]

theorem ivk93w_m12 :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M12) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M12 := e
  have hJcard : Nat.card J = 95040 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.Mathieu.card_M12
  let θ : J ≃* ↥blockGroup := e'.trans m12EquivD
  rcases m12_inv_cases ((θ x : ↥blockGroup) : Equiv.Perm (Fin 24)) (θ x).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact h.ord) with ⟨g, hg, hgt⟩ | h192
  · have hC := h.card_cent_of_model_class m12_model θ hg hgt
    have h1 := h.cent_two_part
    rw [hC, hJcard] at h1
    have a1 : (240 : ℕ).factorization 2 = 4 := nu2_eq_of (by norm_num) (by norm_num) (by norm_num)
    have a2 : (95040 : ℕ).factorization 2 = 6 := nu2_eq_of (by norm_num) (by norm_num) (by norm_num)
    omega
  · have hcard : Nat.card ↥(centralizer ({x} : Set J)) = 192 := by
      rw [GHInv.card_centralizer_eq_centralizerIn blockGroup θ x]
      exact h192
    exact h.false_of_card_cent_dvd (N := 192) (by rw [hcard]) not_sl2_dvd_192

theorem ivk93w_j2 :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .J2) := by
  intro J _ _ hJ x q B h hB
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.J2 := e
  have hJcard : Nat.card J = 604800 := by
    rw [Nat.card_congr e'.toEquiv]
    exact CFSG.Sporadic.J2.card_J2
  let θ : J ≃* ↥j2P := e'.trans j2PermEquiv
  rcases j2_inv_cases ((θ x : ↥j2P) : Equiv.Perm (Fin 315)) (θ x).2
      (by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]; exact h.ord) with
    ⟨-, hcard⟩ | ⟨g, hg, hgt⟩
  · have hC : Nat.card ↥(centralizer ({x} : Set J)) = 1920 := by
      rw [GHInv.card_centralizer_eq_centralizerIn j2P θ x]
      exact hcard
    exact h.false_of_cent_card hB hC hN1920
  · have hC := h.card_cent_of_model_class j2_model θ hg hgt
    have h1 := h.cent_two_part
    rw [hC, hJcard] at h1
    have a1 : (240 : ℕ).factorization 2 = 4 := nu2_eq_of (by norm_num) (by norm_num) (by norm_num)
    have a2 : (604800 : ℕ).factorization 2 = 7 := nu2_eq_of (by norm_num) (by norm_num) (by norm_num)
    omega

theorem ivk93w_j3 :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .J3) := by
  intro L _ _ hL y q B h hB
  obtain ⟨e⟩ := hL
  let e' : L ≃* ↥j3P := e.trans j3PermEquiv
  have hord : orderOf ((e' y : ↥j3P) : Equiv.Perm (Fin 6156)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact h.ord
  obtain ⟨-, hcard⟩ := j3_inner_centralizer_data _ (e' y).2 hord
  have hC : Nat.card ↥(centralizer ({y} : Set L)) = 1920 := by
    rw [GHInv.card_centralizer_eq_centralizerIn j3P e' y, hcard]
  exact h.false_of_cent_card hB hC hN1920

theorem Ivk93W.false_of_perfect_cent {J : Type} [Group J] [Finite J] {x : J} {q : ℕ}
    {B : Subgroup J} (h : Ivk93W x q B) (hperf : Group.IsPerfect ↥(centralizer ({x} : Set J)))
    {a : ℕ} (hcard : Nat.card ↥(centralizer ({x} : Set J)) = Nat.card ↥B * 2 ^ (a + 1)) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({x} : Set J) with hC
  have hN : (B.subgroupOf C).Normal := h.normal_in
  have h1 : Nat.card ↥(B.subgroupOf C) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (B.subgroupOf C)
  rw [h1, hcard] at h2
  have hpos : 0 < Nat.card ↥B := Nat.card_pos
  have hQcard : Nat.card (↥C ⧸ B.subgroupOf C) = 2 ^ (a + 1) := by
    have : Nat.card ↥B * 2 ^ (a + 1) = Nat.card ↥B * Nat.card (↥C ⧸ B.subgroupOf C) := by
      rw [h2]; ring
    exact (Nat.eq_of_mul_eq_mul_left hpos this).symm
  have hQ2 : IsPGroup 2 (↥C ⧸ B.subgroupOf C) := IsPGroup.of_card hQcard
  have hQsolv : Group.IsSolvable (↥C ⧸ B.subgroupOf C) := by
    have := hQ2.isNilpotent
    infer_instance
  have hQperf : Group.IsPerfect (↥C ⧸ B.subgroupOf C) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (B.subgroupOf C))
      (QuotientGroup.mk'_surjective _)
  have hQnt : Nontrivial (↥C ⧸ B.subgroupOf C) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hQcard]
    exact Nat.one_lt_two_pow (by omega)
  exact Group.IsPerfect.not_isSolvable (↥C ⧸ B.subgroupOf C) hQsolv

theorem ivk93w_m23 :
    Ivk93WEmpty (fun X _ => NativeSporadic.IsSporadic X .M23) := by
  intro J _ _ hJ x q B h _
  obtain ⟨e⟩ := hJ
  have e' : J ≃* NativeSporadic.M23 := e
  have hord : orderOf ((e' x : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
    exact h.ord
  obtain ⟨hperf, hcard⟩ := m23_inv_centralizer_data _ (e' x).2 hord
  have hC : Nat.card ↥(centralizer ({x} : Set J)) = 2688 := by
    rw [GHInv.card_centralizer_eq_centralizerIn NativeSporadic.M23 e' x]
    exact hcard
  let φ : ↥(centralizer ({x} : Set J)) ≃* ↥(centralizerIn NativeSporadic.M23 ((e' x : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))) :=
    (GHInv.centralizerEquiv e' x (e' x) rfl).trans (GHInv.centralizerSubtypeEquiv NativeSporadic.M23 (e' x))
  have : Group.IsPerfect ↥(centralizerIn NativeSporadic.M23
      ((e' x : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))) := Subgroup.isPerfect_iff.2 hperf
  have hCperf : Group.IsPerfect ↥(centralizer ({x} : Set J)) :=
    Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  have hBcard := h.card
  have hdvd : Nat.card ↥B ∣ 2688 := hC ▸ Subgroup.card_dvd_of_le h.le
  have hq' : q * (q ^ 2 - 1) ∣ 2688 := (Dvd.intro _ hBcard.symm).trans hdvd
  have hq : q = 7 := by
    have hle : q * (q ^ 2 - 1) ≤ 2688 := Nat.le_of_dvd (by norm_num) hq'
    have hq14 : q ≤ 13 := by
      by_contra hlt
      push Not at hlt
      have := sl2_card_mono (show 14 ≤ q by omega)
      norm_num at this
      omega
    have h5 := h.five
    interval_cases q <;> first | rfl | (exfalso; norm_num at hq')
  subst hq
  have hO : Nat.card ↥(pPrimeCore 2 ↥B) = 1 := by
    have hcop : Nat.Coprime 2 (Nat.card ↥(pPrimeCore 2 ↥B)) := CFSG.pPrimeCore_coprime_card
    have h1 : 336 * Nat.card ↥(pPrimeCore 2 ↥B) ∣ 2688 := by
      have := hBcard ▸ hdvd
      simpa using this
    have h8 : Nat.card ↥(pPrimeCore 2 ↥B) ∣ 2 ^ 3 := by
      obtain ⟨c, hc⟩ := h1
      refine ⟨c, ?_⟩
      have h3 : 336 * (Nat.card ↥(pPrimeCore 2 ↥B) * c) = 336 * 8 := by
        rw [← mul_assoc, ← hc]
      have := Nat.eq_of_mul_eq_mul_left (by norm_num) h3
      simpa using this.symm
    exact (Nat.Coprime.pow_right 3 hcop.symm).eq_one_of_dvd h8
  refine h.false_of_perfect_cent hCperf (a := 2) ?_
  rw [hC, hBcard, hO]
  norm_num


end CFSG.GH74.GLS.IVK.Proofs2
