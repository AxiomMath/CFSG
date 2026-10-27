module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46F
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4Single
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46Z

public section

namespace CFSG.ComponentClassification.GrSLit.GrS4

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem conj_mem_zStarIn_of_le_sup {J M : Subgroup G}
    (hJM : normalizer (J : Set G) ≤ M) (hMO : M ≤ oddIn M ⊔ normalizer (J : Set G)) {a : G}
    (haM : a ∈ M) (haa : a * a = 1) (haZ : a ∈ zStarIn J) {m : G} (hm : m ∈ M)
    (hmN : m⁻¹ * a * m ∈ normalizer (J : Set G)) : m⁻¹ * a * m ∈ zStarIn J := by
  have hON : M ≤ normalizer ((oddIn M : Subgroup G) : Set G) := self_le_normalizer_oddIn M
  have haJ : a ∈ normalizer (J : Set G) := le_normalizer (map_subtype_le _ haZ)
  have hm' : m ∈ ((oddIn M : Subgroup G) : Set G) * (normalizer (J : Set G) : Set G) := by
    rw [← coe_mul_of_right_le_normalizer_left _ _ (hJM.trans hON)]
    exact hMO hm
  obtain ⟨o, ho, n, hn, rfl⟩ := hm'
  set a₁ : G := o⁻¹ * a * o with ha₁
  have ha₁N : a₁ ∈ normalizer (J : Set G) := by
    have h := mul_mem (mul_mem hn hmN) (inv_mem hn)
    rwa [show n * ((o * n)⁻¹ * a * (o * n)) * n⁻¹ = a₁ by rw [ha₁]; group] at h
  set u : G := a⁻¹ * a₁ with hu
  have huO : u ∈ oddIn M := by
    have h1 : a⁻¹ * o⁻¹ * a ∈ oddIn M := by
      have := (mem_normalizer_iff.mp (inv_mem (hON haM)) o⁻¹).mp (inv_mem ho)
      rwa [inv_inv] at this
    have h2 := mul_mem h1 ho
    rwa [show a⁻¹ * o⁻¹ * a * o = u by rw [hu, ha₁]; group] at h2
  have huN : u ∈ normalizer (J : Set G) := mul_mem (inv_mem haJ) ha₁N
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right haa
  have ha₁a : a₁ * a₁ = 1 := by
    rw [ha₁, show o⁻¹ * a * o * (o⁻¹ * a * o) = o⁻¹ * (a * a) * o by group, haa]
    group
  have ha₁i : a₁⁻¹ = a₁ := inv_eq_of_mul_eq_one_right ha₁a
  have hinv : a * u * a⁻¹ = u⁻¹ := by
    rw [hu, mul_inv_rev, inv_inv, ha₁i, hai, ← mul_assoc a a a₁, haa, one_mul]
  obtain ⟨r, hr⟩ : Odd (orderOf u) :=
    (odd_card_map_pPrimeCore M).of_dvd_nat ((oddIn M).orderOf_dvd_natCard huO)
  set v : G := u ^ (r + 1) with hv
  have hvv : v * v = u := by
    rw [hv, ← pow_add, show r + 1 + (r + 1) = orderOf u + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  have hav : a * v * a⁻¹ = v⁻¹ := by rw [hv, ← conj_pow, hinv, inv_pow]
  have hconj : v⁻¹ * a * v = a₁ := by
    have h1 : a⁻¹ * v⁻¹ * a = v :=
      calc a⁻¹ * v⁻¹ * a = a⁻¹ * (a * v * a⁻¹) * a := by rw [hav]
        _ = v := by group
    calc v⁻¹ * a * v = a * (a⁻¹ * v⁻¹ * a) * v := by group
      _ = a * u := by rw [h1, mul_assoc, hvv]
      _ = a₁ := by rw [hu]; group
  have hvnN : v * n ∈ normalizer (J : Set G) := mul_mem (pow_mem huN _) hn
  have h := conj_mem_zStarIn (inv_mem hvnN) haZ
  rwa [show (v * n)⁻¹ * a * (v * n)⁻¹⁻¹ = (o * n)⁻¹ * a * (o * n) by
    rw [inv_inv, show (v * n)⁻¹ * a * (v * n) = n⁻¹ * (v⁻¹ * a * v) * n by group, hconj, ha₁]
    group] at h

theorem l34ZConjClosed_of_le_sup {J S M : Subgroup G} (hJM : normalizer (J : Set G) ≤ M)
    (hMO : M ≤ oddIn M ⊔ normalizer (J : Set G)) (hSN : S ≤ normalizer (J : Set G)) :
    L34ZConjClosed J S M := fun _ hc hcc _ hm hmS =>
  conj_mem_zStarIn_of_le_sup hJM hMO (hJM (hSN (mem_inf.mp hc).1)) hcc (mem_inf.mp hc).2 hm
    (hSN hmS)

theorem exists_conj_eq_of_isSylowTwoIn {S : Subgroup G} {a b h : G}
    (hSa : IsSylowTwoIn S (centralizer ({a} : Set G))) (hS2 : IsPGroup 2 S)
    (hb : b = h⁻¹ * a * h) :
    ∃ g : G, g⁻¹ * b * g = a ∧ ∀ y ∈ S ⊓ centralizer ({b} : Set G), g⁻¹ * y * g ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set V : Subgroup G := (S ⊓ centralizer ({b} : Set G)).map (MulAut.conj h).toMonoidHom
  have hVC : V ≤ centralizer ({a} : Set G) := by
    rintro _ ⟨y, hy, rfl⟩
    have hyb := mem_centralizer_singleton_iff.mp (mem_inf.mp hy).2
    rw [mem_centralizer_singleton_iff]
    show h * y * h⁻¹ * a = a * (h * y * h⁻¹)
    have ha : a = h * b * h⁻¹ := by rw [hb]; group
    rw [ha, show h * y * h⁻¹ * (h * b * h⁻¹) = h * (y * b) * h⁻¹ by group, hyb]
    group
  obtain ⟨c, hcC, hc⟩ := exists_conj_mem_of_isSylowTwoIn hSa hVC ((hS2.to_le inf_le_left).map _)
  refine ⟨h⁻¹ * c, ?_, fun y hy => ?_⟩
  · rw [hb, show (h⁻¹ * c)⁻¹ * (h⁻¹ * a * h) * (h⁻¹ * c) = c⁻¹ * a * c by group, mul_assoc,
      ← mem_centralizer_singleton_iff.mp hcC, ← mul_assoc, inv_mul_cancel, one_mul]
  · have h1 := hc (h * y * h⁻¹) ⟨y, hy, rfl⟩
    rwa [show c⁻¹ * (h * y * h⁻¹) * c = (h⁻¹ * c)⁻¹ * y * (h⁻¹ * c) by group] at h1

end CFSG.ComponentClassification.GrSLit.GrS4

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34Lemma46ZStep_of_inputs (hFus : L34Lemma46FusionStep)
    (hSq : L34Lemma46FieldSquareStep) (hRk : L34Lemma46SquareRankStep)
    (hMax : MaximalTwoComponentInput) : L34Lemma46ZStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl y hyS
    hya
  obtain ⟨hbase, hU3, hL34, hmax, hS, haS, -⟩ := id hset
  obtain ⟨hsimple, hnab, hK, -, hUo, -, -, -⟩ := hbase
  obtain ⟨ha2, -, -, hJa, hJc, -, -⟩ := hU3
  have hgs : GSMaximalSetting G a J := ⟨hsimple, hnab, hK, hUo, ha2, hJa, hJc,
    hmax, GrS5.three_le_pRank_of_l34 hL34, Sol78.not_psp4_of_l34 hL34, Or.inl ⟨hL34, hset.1⟩⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  have hCa : centralizer ({a} : Set G) ≤ M :=
    (GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hgs).trans hNJ
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have hZne : S ⊓ zStarIn J ≠ ⊥ := by
    intro h
    obtain ⟨z, hz, hzz⟩ := GrS4.exists_sq_ne_one_of_exponent_eq_four hexp
    rw [h, mem_bot] at hz
    rw [hz, one_mul] at hzz
    exact hzz rfl
  have haZ : a ∈ zStarIn J := (mem_inf.mp (hZ hZne)).2
  have hZM : ∀ m ∈ M, m⁻¹ * a * m ∈ S → m⁻¹ * a * m ∈ zStarIn J := fun m hm hmS =>
    hMO a (mem_inf.mpr ⟨haS, haZ⟩) haa m hm hmS
  by_contra hyZ
  by_cases hr : 3 ≤ pRank 2 ↥(S ⊓ J ⊓ centralizer ({y} : Set G))
  · obtain ⟨m, hm, hym⟩ := hFus G a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ
      hMO hNS hSyl y hyS hya hr
    rw [hym] at hyS hyZ
    exact hyZ (hZM m hm hyS)
  · obtain ⟨z, hz, hzz⟩ := hSq G a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ
      hMO hNS hSyl y hyS hya hyZ (lt_of_not_ge hr)
    obtain ⟨h, hh⟩ := hya
    have hS2 : IsPGroup 2 S := GrS4.isPGroup_of_isSylowTwoIn hS
    have hSa : IsSylowTwoIn S (centralizer ({a} : Set G)) := by
      obtain ⟨P, hPS⟩ := hSyl
      have hSC : S ≤ centralizer ({a} : Set G) := fun s hs =>
        mem_centralizer_singleton_iff.mpr (hcent s hs)
      refine GrS4.isSylowTwoIn_of_not_dvd hSC hS2 fun hd => ?_
      rw [← hPS] at hd hSC
      exact P.not_dvd_index (hd.trans (relIndex_dvd_index_of_le hSC))
    obtain ⟨g, hg, hgS⟩ := GrS4.exists_conj_eq_of_isSylowTwoIn hSa hS2 hh
    have hzg : g⁻¹ * z * g ∈ S := hgS z hz
    have hsq : g⁻¹ * z * g * (g⁻¹ * z * g) = g⁻¹ * a * g := by rw [← hzz]; group
    have hr3 := hRk G a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl
      (g⁻¹ * z * g) hzg ⟨g, hsq⟩
    rw [hsq] at hr3
    have hgaS : g⁻¹ * a * g ∈ S := hsq ▸ mul_mem hzg hzg
    obtain ⟨m, hm, hgm⟩ := hFus G a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ
      hMO hNS hSyl (g⁻¹ * a * g) hgaS ⟨g, rfl⟩ hr3
    have hc : g * m⁻¹ ∈ centralizer ({a} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc g * m⁻¹ * a = g * (m⁻¹ * a * m) * m⁻¹ := by group
        _ = g * (g⁻¹ * a * g) * m⁻¹ := by rw [← hgm]
        _ = a * (g * m⁻¹) := by group
    have hgM : g ∈ M := by
      have h1 := mul_mem (hCa hc) hm
      rwa [inv_mul_cancel_right] at h1
    have hy' : y = (g⁻¹)⁻¹ * a * g⁻¹ := by rw [← hg]; group
    rw [hy'] at hyS hyZ
    exact hyZ (hZM g⁻¹ (inv_mem hgM) hyS)

end CFSG.ComponentClassification.GrSLit
