module

public import CFSG.ClassicalInvolution.Q3.TL4SepQuot
public import CFSG.ClassicalInvolution.Q3.TL4SepFam

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight

variable {r : ℕ} {G : Type} [Group G] [Finite G] {N : Subgroup G} [N.Normal]

omit [Finite G] in
theorem mk_mem_normalizer_map {K : Subgroup G} {c : G}
    (hc : c ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' N c ∈
      Subgroup.normalizer ((K.map (QuotientGroup.mk' N) : Subgroup (G ⧸ N)) : Set (G ⧸ N)) := by
  refine mem_normalizer_of_conjSub_eq ?_
  rw [← AscQuot.map_conjSub, conjSub_eq_of_mem_normalizer hc]

omit [Finite G] in
theorem TightFam.exists_conj_of_mk_eq {Δ : Set (Subgroup G)} (h : TightFam r G Δ)
    (hN : Odd (Nat.card ↥N)) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ) {u j : G}
    (hu : IsUniqueInvolution A u) (hj : IsUniqueInvolution B j)
    (huj : QuotientGroup.mk' N u = QuotientGroup.mk' N j) : ∃ m ∈ N, conjSub m A = B := by
  set n := u⁻¹ * j with hn
  have hnN : n ∈ N := QuotientGroup.eq.mp huj
  have hjn : j = u * n := by rw [hn, mul_inv_cancel_left]
  have hodd : Odd (orderOf n) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hnN)
  obtain ⟨k, hk⟩ := OddQ.exists_conj_eq_mul hu.sq (by rw [← hjn]; exact hj.sq) hodd
  have hcj : IsUniqueInvolution (conjSub (n ^ k) A) j := by
    have := hu.conj (n ^ k)
    rwa [hk, ← hjn] at this
  exact ⟨n ^ k, N.pow_mem hnN k, h.noTwins _ (h.conjInvariant _ A hA) B hB j hcj hj⟩

theorem TightFam.exists_conj_of_map_eq {Δ : Set (Subgroup G)} (h : TightFam r G Δ)
    (hN : Odd (Nat.card ↥N)) {A B : Subgroup G} (hA : A ∈ Δ) (hB : B ∈ Δ)
    (hAB : A.map (QuotientGroup.mk' N) = B.map (QuotientGroup.mk' N)) :
    ∃ m ∈ N, conjSub m A = B := by
  obtain ⟨u, hu⟩ := h.inv A hA
  obtain ⟨j, hj⟩ := h.inv B hB
  have hu' := isUniqueInvolution_map_mk hN hu
  rw [hAB] at hu'
  exact h.exists_conj_of_mk_eq hN hA hB hu hj (hu'.eq (isUniqueInvolution_map_mk hN hj))

theorem TightFam.quot {Δ : Set (Subgroup G)} (h : TightFam r G Δ) (hN : Odd (Nat.card ↥N)) :
    TightFam r (G ⧸ N) (Set.image (fun K : Subgroup G => K.map (QuotientGroup.mk' N)) Δ) where
  conjInvariant := AscQuot.conjInvariant_quot h.conjInvariant N
  inv := by
    rintro _ ⟨K, hK, rfl⟩
    obtain ⟨u, hu⟩ := h.inv K hK
    exact ⟨_, isUniqueInvolution_map_mk hN hu⟩
  gen := by
    rintro _ ⟨K, hK, rfl⟩
    exact closure_twoElements_map (h.gen K hK)
  twoGroup := by
    rintro _ ⟨K, hK, rfl⟩
    exact isPGroup_quot_map (h.twoGroup K hK)
  quat := by
    rintro _ ⟨K, hK, rfl⟩ P' hP'
    exact quat_map hN (h.quat K hK) hP'
  tight := by
    rintro _ ⟨K, hK, rfl⟩ v hv c hc
    obtain ⟨u, hu⟩ := h.inv K hK
    have hvu : v = QuotientGroup.mk' N u := hv.eq (isUniqueInvolution_map_mk hN hu)
    rw [hvu, OddQ.centralizer_mk_eq hN hu.sq] at hc
    obtain ⟨c', hc', rfl⟩ := hc
    exact mk_mem_normalizer_map (h.tight K hK u hu hc')
  noTwins := by
    rintro _ ⟨K, hK, rfl⟩ _ ⟨J, hJ, rfl⟩ v hvK hvJ
    obtain ⟨u, hu⟩ := h.inv K hK
    obtain ⟨j, hj⟩ := h.inv J hJ
    obtain ⟨m, hm, hKJ⟩ := h.exists_conj_of_mk_eq hN hK hJ hu hj
      ((hvK.eq (isUniqueInvolution_map_mk hN hu)).symm.trans
        (hvJ.eq (isUniqueInvolution_map_mk hN hj)))
    have hm1 : QuotientGroup.mk' N m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
    dsimp only
    rw [← hKJ, AscQuot.map_conjSub, hm1, conjSub_one]

theorem TightFam.t4Hyp_quot {Δ : Set (Subgroup G)} (h : TightFam r G Δ) (hr : 3 ≤ r) :
    T4Hyp r (G ⧸ classicalInvolutionOddCore G) (Set.image
      (fun K : Subgroup G => K.map (QuotientGroup.mk' (classicalInvolutionOddCore G))) Δ) :=
  (h.quot (CFSG.ComponentClassification.OddCore.odd_card G)).toT4Hyp hr
    CFSG.ABGLocalTools.oddCore_quotient_oddCore_eq_bot

end CFSG.ClassicalInvolution.Q3.TL4
