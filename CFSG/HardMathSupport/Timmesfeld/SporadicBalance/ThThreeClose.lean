module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThThree
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThLocalSound
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.PrimeCommute
public import Certificates.Certificate13650
public import Certificates.Certificate13651
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance

open CFSG.Open CFSG.Blueprint
open CFSG.HardMathSupport.Timmesfeld.SporadicBalance.ThCent (zJ)
open scoped Pointwise

section Conj

variable {G : Type*} [Group G]

theorem map_conj_centralizer (d a : G) :
    (Subgroup.centralizer ({a} : Set G)).map (MulAut.conj d).toMonoidHom =
      Subgroup.centralizer ({d * a * d⁻¹} : Set G) := by
  ext y
  simp only [Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply]
  constructor
  · rintro ⟨x, hx, rfl⟩
    calc d * x * d⁻¹ * (d * a * d⁻¹) = d * (x * a) * d⁻¹ := by group
      _ = d * (a * x) * d⁻¹ := by rw [hx]
      _ = d * a * d⁻¹ * (d * x * d⁻¹) := by group
  · intro hy
    refine ⟨d⁻¹ * y * d, ?_, by group⟩
    calc d⁻¹ * y * d * a = d⁻¹ * (y * (d * a * d⁻¹)) * d := by group
      _ = d⁻¹ * ((d * a * d⁻¹) * y) * d := by rw [hy]
      _ = a * (d⁻¹ * y * d) := by group

theorem map_conj_le_centralizer {K : Subgroup G} {a : G} (d : G)
    (hK : K ≤ Subgroup.centralizer ({a} : Set G)) :
    K.map (MulAut.conj d).toMonoidHom ≤ Subgroup.centralizer ({d * a * d⁻¹} : Set G) := by
  rw [← map_conj_centralizer]
  exact Subgroup.map_mono hK

theorem card_map_conj (K : Subgroup G) (d : G) :
    Nat.card (K.map (MulAut.conj d).toMonoidHom) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj d).injective

theorem isElemAbelian_map_conj {p : ℕ} {E : Subgroup G} (hE : CFSG.Open.IsElemAbelian p E)
    (d : G) : CFSG.Open.IsElemAbelian p (E.map (MulAut.conj d).toMonoidHom) :=
  CFSG.Open.IsElemAbelian.map hE _

theorem centralizer_sq_eq {z : G} (hz : z ^ 3 = 1) :
    Subgroup.centralizer ({z ^ 2} : Set G) = Subgroup.centralizer ({z} : Set G) := by
  apply le_antisymm
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    have hz4 : z = (z ^ 2) ^ 2 := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, hz, one_mul, pow_one]
    rw [hz4]
    exact ((Commute.pow_right (show Commute y (z ^ 2) from hy) 2)).eq
  · intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    exact ((Commute.pow_right (show Commute y z from hy) 2)).eq

@[expose] def ResAt (s : G) : Prop :=
  (∃ P : Subgroup G, P ≤ Subgroup.centralizer ({s} : Set G) ∧ IsPGroup 3 P ∧
        3 ^ 7 ≤ Nat.card P) ∧
    ∀ q : ℕ, q.Prime → 5 ≤ q → q ∣ Nat.card (Subgroup.centralizer ({s} : Set G)) →
      ∃ A : Subgroup G, A ≤ Subgroup.centralizer ({s} : Set G) ∧
          CFSG.Open.IsElemAbelian 3 A ∧ Nat.card A = 9 ∧ ∀ x ∈ A, x ≠ 1 →
            ¬ q ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set G) ⊓
              Subgroup.centralizer ({x} : Set G))

theorem resAt_of_isConj {s t : G} (hst : IsConj s t) (ht : ResAt t) : ResAt s := by
  obtain ⟨d, hd⟩ := isConj_iff.1 hst.symm
  obtain ⟨⟨P, hPt, hP, hP7⟩, hA⟩ := ht
  refine ⟨⟨P.map (MulAut.conj d).toMonoidHom, ?_, hP.map _, ?_⟩, fun q hq hq5 hqs => ?_⟩
  · rw [← hd]
    exact map_conj_le_centralizer d hPt
  · rw [card_map_conj]
    exact hP7
  · have hqt : q ∣ Nat.card (Subgroup.centralizer ({t} : Set G)) := by
      rw [← hd, card_centralizer_conj] at hqs
      exact hqs
    obtain ⟨A, hAt, hAe, hA9, hAx⟩ := hA q hq hq5 hqt
    refine ⟨A.map (MulAut.conj d).toMonoidHom, ?_, isElemAbelian_map_conj hAe d, ?_, ?_⟩
    · rw [← hd]
      exact map_conj_le_centralizer d hAt
    · rw [card_map_conj]
      exact hA9
    · rintro _ ⟨x, hx, rfl⟩ hx1
      have hx1' : x ≠ 1 := fun h => hx1 (by rw [h, map_one])
      have hnd := hAx x hx hx1'
      intro hdvd
      apply hnd
      have e : (Subgroup.centralizer ({t} : Set G) ⊓
          Subgroup.centralizer ({x} : Set G)).map (MulAut.conj d).toMonoidHom =
          Subgroup.centralizer ({s} : Set G) ⊓
            Subgroup.centralizer ({(MulAut.conj d).toMonoidHom x} : Set G) := by
        rw [Subgroup.map_inf _ _ _ (MulAut.conj d).injective, map_conj_centralizer,
          map_conj_centralizer, hd]
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← e, card_map_conj] at hdvd
      exact hdvd

theorem exists_conj_mem_sylow_three [Finite G] (P : Sylow 3 G) {s : G} (hs : orderOf s = 3) :
    ∃ g : G, g * s * g⁻¹ ∈ (P : Subgroup G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hsP : IsPGroup 3 (Subgroup.zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  obtain ⟨R, hR⟩ := hsP.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  refine ⟨g, ?_⟩
  have h1 : s ∈ (R : Subgroup G) := hR (Subgroup.mem_zpowers s)
  have h2 := Subgroup.smul_mem_pointwise_smul s (MulAut.conj g) (R : Subgroup G) h1
  have h3 : ((g • R : Sylow 3 G) : Subgroup G) = MulAut.conj g • (R : Subgroup G) := rfl
  rw [← h3, hg] at h2
  simpa [MulAut.smul_def] using h2

end Conj


section Th


theorem finite_J : Finite ↥CFSG.Sporadic.Th.J :=
  Nat.finite_of_card_ne_zero (by rw [CFSG.Sporadic.Th.Max3.natCard_J]; norm_num)

theorem not_dvd_card_centralizer_zJ {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) {Q : Subgroup ↥CFSG.Sporadic.Th.J} (hQ : Nat.card Q = 3 ^ 10)
    (hQz : ∀ x ∈ Q, x * zJ = zJ * x) {u : ↥CFSG.Sporadic.Th.J} (hu : orderOf u = 2)
    (huz : u * zJ = zJ * u) :
    ¬ q ∣ Nat.card (Subgroup.centralizer ({zJ} : Set ↥CFSG.Sporadic.Th.J)) := by
  have := finite_J
  set C := Subgroup.centralizer ({zJ} : Set ↥CFSG.Sporadic.Th.J) with hCdef
  have hle : Nat.card C ≤ 472392 := Certificates.certificate13651
  have hQC : Q ≤ C := fun x hx => Subgroup.mem_centralizer_singleton_iff.2 (hQz x hx)
  have h3 : 3 ^ 10 ∣ Nat.card C := hQ ▸ Subgroup.card_dvd_of_le hQC
  have huC : u ∈ C := Subgroup.mem_centralizer_singleton_iff.2 huz
  have h2 : 2 ∣ Nat.card C := by
    have := Subgroup.orderOf_dvd_natCard C huC
    rwa [hu] at this
  have hJ : Nat.card C ∣ 90745943887872000 := by
    rw [← CFSG.Sporadic.Th.Max3.natCard_J]
    exact Subgroup.card_subgroup_dvd_card C
  have hpos : 0 < Nat.card C := Nat.card_pos
  obtain ⟨r, hr⟩ := h3
  have h59 : (3 : ℕ) ^ 10 = 59049 := by norm_num
  have hr8 : r ≤ 8 := by
    rw [hr, h59] at hle
    omega
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [hr, h0, mul_zero] at hpos
      exact absurd hpos (lt_irrefl 0)
    · exact h0
  have hr2 : 2 ∣ r := by
    rw [hr] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h | h
    · exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_two h) (by norm_num)
    · exact h
  have hr3 : ¬ 3 ∣ r := by
    rintro ⟨r', rfl⟩
    rw [hr] at hJ
    have : 3 ^ 11 ∣ 90745943887872000 := (Dvd.intro r' (by ring)).trans hJ
    norm_num at this
  intro hqd
  rw [hr] at hqd
  rcases (Nat.Prime.dvd_mul hq).1 hqd with h | h
  · have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).1 (hq.dvd_of_dvd_pow h)
    omega
  · have hqr : q ≤ r := Nat.le_of_dvd hr0 h
    interval_cases r <;> interval_cases q <;> revert h hr2 hr3 hq <;> norm_num

theorem thThreeResidual_holds :
    ThThreeResidual := by
  have := finite_J
  obtain ⟨Q, hQ, -, hz3, hQz, ⟨u, hu, huz⟩, hloc⟩ := Certificates.certificate13650
  have hnd : ∀ q : ℕ, q.Prime → 5 ≤ q →
      ¬ q ∣ Nat.card (Subgroup.centralizer ({zJ} : Set ↥CFSG.Sporadic.Th.J)) :=
    fun q hq hq5 => not_dvd_card_centralizer_zJ hq hq5 hQ hQz hu huz
  have hsyl : (Nat.card Q) = 3 ^ (Nat.card ↥CFSG.Sporadic.Th.J).factorization 3 := by
    rw [hQ, ThLocal.factorization_J]
  let QS : Sylow 3 ↥CFSG.Sporadic.Th.J := Sylow.ofCard Q hsyl
  intro s hs
  show ResAt s
  obtain ⟨g, hsQ⟩ := exists_conj_mem_sylow_three QS hs
  have hs' : orderOf (g * s * g⁻¹) = 3 := by rw [orderOf_conj_eq]; exact hs
  obtain ⟨t, hst, hPt, E, hEt, hEe, hE9, hEz⟩ := hloc _ hsQ hs'
  have hs_t : IsConj s t := (isConj_iff.2 ⟨g, rfl⟩).trans hst
  have hEe' : CFSG.Open.IsElemAbelian 3 E := hEe
  refine resAt_of_isConj hs_t ⟨⟨Q ⊓ Subgroup.centralizer ({t} : Set _), inf_le_right,
    ?_, hPt⟩, fun q hq hq5 _ => ⟨E, hEt, hEe', hE9, fun x hx hx1 => ?_⟩⟩
  · obtain ⟨n, hn⟩ : ∃ n : ℕ, Nat.card Q = 3 ^ n := ⟨10, hQ⟩
    exact (IsPGroup.of_card hn).to_le inf_le_left
  · intro hdvd
    have hdx : q ∣ Nat.card (Subgroup.centralizer ({x} : Set ↥CFSG.Sporadic.Th.J)) :=
      hdvd.trans (Subgroup.card_dvd_of_le inf_le_right)
    rcases hEz x hx hx1 with hxz | hxz
    · obtain ⟨c, hc⟩ := isConj_iff.1 hxz.symm
      rw [← hc, card_centralizer_conj] at hdx
      exact hnd q hq hq5 hdx
    · obtain ⟨c, hc⟩ := isConj_iff.1 hxz.symm
      rw [← hc, card_centralizer_conj, centralizer_sq_eq hz3] at hdx
      exact hnd q hq hq5 hdx

theorem sporadicOPrimeHolds_Th_three :
    SporadicOPrimeHolds .Th 3 :=
  sporadicOPrimeHolds_Th_three_of_residual thThreeResidual_holds

theorem sporadicOnePairHolds_Th_three :
    SporadicOnePairHolds .Th 3 :=
  sporadicOnePairHolds_Th_three_of_residual thThreeResidual_holds

end Th

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance
