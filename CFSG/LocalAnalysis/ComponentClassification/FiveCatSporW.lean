module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.FiveCatEvenTwo
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.A5

public section

namespace CFSG.ComponentClassification.SolMax.FiveCat.Spor

open CFSG Subgroup

theorem alt_five_orderOf_ne_six (g : alternatingGroup (Fin 5)) : orderOf g ≠ 6 := by
  intro h
  have h6 : g ^ 6 = 1 := by
    have := pow_orderOf_eq_one g
    rwa [h] at this
  have h2 : g ^ 2 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have h3 : g ^ 3 ≠ 1 := fun h' => by
    have := orderOf_dvd_of_pow_eq_one h'
    rw [h] at this
    omega
  have key : ∀ g : alternatingGroup (Fin 5), g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by
    decide +kernel
  rcases key g h6 with h' | h'
  · exact h2 h'
  · exact h3 h'

variable {S : Type} [Group S] [Finite S]

theorem normal_of_not_dvd_3600 {C P : Subgroup S} (hPC : P ≤ C)
    (hP : IsPComponent 2 (P.subgroupOf C))
    (eP : Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* alternatingGroup (Fin 5)))
    (h3600 : ¬ 3600 ∣ Nat.card C) : ∀ g ∈ C, ∀ p ∈ P, g * p * g⁻¹ ∈ P := by
  intro g hg p hp
  have hconj : P.map (MulAut.conj g).toMonoidHom = P := by
    by_contra hne
    apply h3600
    set P' := P.map (MulAut.conj g).toMonoidHom with hP'
    have hP'C : P' ≤ C := by
      rintro _ ⟨q, hq, rfl⟩
      exact C.mul_mem (C.mul_mem hg (hPC hq)) (C.inv_mem hg)
    have hP'p : IsPComponent 2 (P'.subgroupOf C) := by
      have h1 := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2
        (MulAut.conj (⟨g, hg⟩ : ↥C)) hP
      have heq : P'.subgroupOf C =
          (P.subgroupOf C).map (MulAut.conj (⟨g, hg⟩ : ↥C)).toMonoidHom := by
        ext z
        constructor
        · intro hz
          obtain ⟨q, hq, hqz⟩ := (Subgroup.mem_subgroupOf.mp hz)
          refine ⟨⟨q, hPC hq⟩, Subgroup.mem_subgroupOf.mpr hq, ?_⟩
          apply Subtype.ext
          simpa [MulAut.conj_apply] using hqz
        · rintro ⟨w, hw, rfl⟩
          refine Subgroup.mem_subgroupOf.mpr ⟨(w : S), Subgroup.mem_subgroupOf.mp hw, ?_⟩
          simp [MulAut.conj_apply]
      rw [heq]
      exact h1
    obtain ⟨e5⟩ := eP
    let eg : ↥P ≃* ↥P' :=
      P.equivMapOfInjective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
    have eP' : Nonempty (↥P' ⧸ pPrimeCore 2 ↥P' ≃* alternatingGroup (Fin 5)) :=
      ⟨(QuotientGroup.congr (pPrimeCore 2 ↥P) (pPrimeCore 2 ↥P') eg
        (pPrimeCore_map_iso 2 eg)).symm.trans e5⟩
    exact Even.dvd_card_of_two_layers hPC hP hP'C hP'p (fun h => hne h.symm) ⟨e5⟩ eP'
  have hmem : (MulAut.conj g) p ∈ P.map (MulAut.conj g).toMonoidHom := ⟨p, hp, rfl⟩
  rw [hconj] at hmem
  simpa [MulAut.conj_apply] using hmem

theorem card_eq_sixty_of_dvd {C P : Subgroup S} (hPC : P ≤ C)
    (e5 : ↥P ⧸ pPrimeCore 2 ↥P ≃* alternatingGroup (Fin 5)) {k : ℕ}
    (hC : Nat.card C = 60 * 2 ^ k) : Nat.card P = 60 ∧ pPrimeCore 2 ↥P = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : Nat.Coprime 2 (Nat.card (pPrimeCore 2 ↥P)) :=
    pPrimeCore_coprime_card (p := 2) (G := ↥P)
  have h60 : Nat.card (↥P ⧸ pPrimeCore 2 ↥P) = 60 := by
    rw [Nat.card_congr e5.toEquiv]
    exact Even.card_alt_five (MulEquiv.refl _)
  have hP : Nat.card P = 60 * Nat.card (pPrimeCore 2 ↥P) := by
    rw [← h60]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥P)
  have hdvd : Nat.card P ∣ Nat.card C := Subgroup.card_dvd_of_le hPC
  rw [hP, hC] at hdvd
  have hm : Nat.card (pPrimeCore 2 ↥P) ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdvd
  have h1 : Nat.card (pPrimeCore 2 ↥P) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hodd.symm) hm
  refine ⟨by rw [hP, h1], Subgroup.card_eq_one.mp h1⟩

theorem mem_of_orderOf_five {C P : Subgroup S} (hPC : P ≤ C)
    (hPn : ∀ g ∈ C, ∀ p ∈ P, g * p * g⁻¹ ∈ P) (hP60 : Nat.card P = 60) {k : ℕ}
    (hC : Nat.card C = 60 * 2 ^ k) {x : S} (hx : x ∈ C) (hx5 : orderOf x = 5) : x ∈ P := by
  haveI : (P.subgroupOf C).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr (by
      have := hPn (g : S) g.2 (n : S) (Subgroup.mem_subgroupOf.mp hn)
      simpa using this)⟩
  have hN : Nat.card (P.subgroupOf C) = 60 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hPC).toEquiv, hP60]
  have hq : Nat.card (↥C ⧸ P.subgroupOf C) = 2 ^ k := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (P.subgroupOf C)
    rw [hC, hN] at h
    have h' : Nat.card (↥C ⧸ P.subgroupOf C) * 60 = 2 ^ k * 60 := by rw [← h]; ring
    exact Nat.eq_of_mul_eq_mul_right (by norm_num : 0 < 60) h'
  set a : ↥C := ⟨x, hx⟩ with ha
  have ha5 : orderOf a = 5 := by rw [ha, Subgroup.orderOf_mk, hx5]
  have h5 : orderOf (QuotientGroup.mk a : ↥C ⧸ P.subgroupOf C) ∣ 5 := by
    apply orderOf_dvd_of_pow_eq_one
    rw [← QuotientGroup.mk_pow, ← ha5, pow_orderOf_eq_one, QuotientGroup.mk_one]
  have h2k : orderOf (QuotientGroup.mk a : ↥C ⧸ P.subgroupOf C) ∣ 2 ^ k := by
    rw [← hq]
    exact orderOf_dvd_natCard _
  have hcop : Nat.Coprime 5 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have h1 : orderOf (QuotientGroup.mk a : ↥C ⧸ P.subgroupOf C) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h5 hcop) h2k
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact Subgroup.mem_subgroupOf.mp h1

theorem false_of_five_witness {C P : Subgroup S} (hPC : P ≤ C)
    (hP : IsPComponent 2 (P.subgroupOf C))
    (eP : Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* alternatingGroup (Fin 5))) {k : ℕ}
    (hC : Nat.card C = 60 * 2 ^ k) {x y : S} (hx : x ∈ C) (hy : y ∈ C) (hx5 : orderOf x = 5)
    (hxy : orderOf (x * (y * x * y⁻¹)) = 6) : False := by
  have h3600 : ¬ 3600 ∣ Nat.card C := by
    intro h
    rw [hC, show (3600 : ℕ) = 60 * 60 by norm_num] at h
    have h60 : 60 ∣ 2 ^ k := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h
    have h3 : 3 ∣ 2 ^ k := (by norm_num : 3 ∣ 60).trans h60
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hPn := normal_of_not_dvd_3600 hPC hP eP h3600
  obtain ⟨e5⟩ := eP
  obtain ⟨hP60, hO⟩ := card_eq_sixty_of_dvd hPC e5 hC
  have hxP : x ∈ P := mem_of_orderOf_five hPC hPn hP60 hC hx hx5
  have hyxP : y * x * y⁻¹ ∈ P := hPn y hy x hxP
  have hzP : x * (y * x * y⁻¹) ∈ P := P.mul_mem hxP hyxP
  let ψ : ↥P ≃* alternatingGroup (Fin 5) :=
    (((QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot).symm).trans e5
  have h6 : orderOf (ψ ⟨_, hzP⟩) = 6 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxy]
  exact alt_five_orderOf_ne_six _ h6

theorem false_of_five_witness_of_equiv {C P : Subgroup S} (hPC : P ≤ C)
    (hP : IsPComponent 2 (P.subgroupOf C))
    (eP : Nonempty (↥P ⧸ pPrimeCore 2 ↥P ≃* alternatingGroup (Fin 5))) {k : ℕ}
    (hC : Nat.card C = 60 * 2 ^ k) {M : Type*} [Group M] {K : Subgroup M} (E : ↥C ≃* ↥K)
    {x y : M} (hx : x ∈ K) (hy : y ∈ K) (hx5 : orderOf x = 5)
    (hxy : orderOf (x * (y * x * y⁻¹)) = 6) : False := by
  set a : ↥K := ⟨x, hx⟩ with ha
  set b : ↥K := ⟨y, hy⟩ with hb
  have ha5 : orderOf a = 5 := by rw [ha, Subgroup.orderOf_mk, hx5]
  have hab : orderOf (a * (b * a * b⁻¹)) = 6 := by
    rw [← Subgroup.orderOf_coe]
    exact hxy
  refine false_of_five_witness hPC hP eP hC (x := ((E.symm a : ↥C) : S))
    (y := ((E.symm b : ↥C) : S)) (E.symm a).2 (E.symm b).2 ?_ ?_
  · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ha5]
  · have h : (((E.symm a : ↥C) : S) * (((E.symm b : ↥C) : S) * ((E.symm a : ↥C) : S) *
        ((E.symm b : ↥C) : S)⁻¹)) = ((E.symm (a * (b * a * b⁻¹)) : ↥C) : S) := by simp
    rw [h, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hab]

end CFSG.ComponentClassification.SolMax.FiveCat.Spor
