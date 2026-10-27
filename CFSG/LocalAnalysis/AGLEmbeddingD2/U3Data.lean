module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Reduced
public import CFSG.LocalAnalysis.AGLEmbeddingD2.U3Torus
import CFSG.LocalAnalysis.AGLEmbeddingD2.HeisInverting
import CFSG.LocalAnalysis.AGLEmbeddingD2.L2Data

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.PreuniquenessRankFour.Helpers CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

section Data

variable {G : Type} [Group G] [Finite G]

structure D2HeisDataCore (p : ℕ) (M H R Z : Subgroup G) : Prop where
  pair : AGLPair p M H R
  card_R : Nat.card R = p ^ 3
  heis : Nat.card Z = p ∧ ⁅R, R⁆ = Z ∧ ∀ r ∈ R, r ^ p = 1
  lines : ∃ t ∈ H ⊓ M, t ∈ Subgroup.normalizer (R : Set G) ∧
    ∃ m lam e : ℕ, 2 ≤ m ∧
    orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ e ∧
    (∀ x ∈ R, ∃ z ∈ Z, t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
    (∀ x ∈ R, ∃ z ∈ Z, t ^ e * x * (t ^ e)⁻¹ = x⁻¹ * z) ∧
    ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup G, Z ≤ F → F ≤ R →
      F.relIndex R = p → t ^ j ∉ Subgroup.normalizer (F : Set G)
  irred : ∀ V : Subgroup G, Z ≤ V → V ≤ R →
    (H ⊓ M) ⊓ Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (V : Set G) → V = Z ∨ V = R
  normal_dichotomy : ∀ Y : Subgroup G, Y ≤ H ⊓ M → H ⊓ M ≤ Subgroup.normalizer (Y : Set G) →
    Y ≤ GLBPrimeCore p H ∨ Z ≤ Y
  centralizer_le : ∀ d ∈ H ⊓ M, (∀ x ∈ R, d * x * d⁻¹ * x⁻¹ ∈ GLBPrimeCore p H) →
    d ∈ R ⊔ GLBPrimeCore p H
  pRank_le : Open.pRank p (H ⊓ M) ≤ 2

structure D2HeisData (p : ℕ) (M H R Z : Subgroup G) : Prop extends D2HeisDataCore p M H R Z where
  perfect_le : ∀ L : Subgroup G, L ≤ H ⊓ M → ⁅L, L⁆ = L → L ≤ GLBPrimeCore p H

end Data

theorem even_lineOrbit {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    Even ((p + 1) / Nat.gcd 3 (p + 1)) := by
  have hev : Even (p + 1) := (hp.odd_of_ne_two hp2).add_one
  set g := Nat.gcd 3 (p + 1) with hg
  have hgodd : Odd g := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (Nat.gcd_dvd_left 3 (p + 1)) with h | h <;>
      rw [hg, h] <;> decide
  have hpos : 0 < g := Nat.gcd_pos_of_pos_left _ (by norm_num)
  obtain ⟨m, hm⟩ : g ∣ p + 1 := Nat.gcd_dvd_right 3 (p + 1)
  rw [hm, Nat.mul_div_cancel_left _ hpos]
  rw [hm] at hev
  rcases Nat.even_mul.mp hev with h | h
  · exact absurd h (Nat.not_even_iff_odd.mpr hgodd)
  · exact h

section Reduced

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H R : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem eq_of_mk_eq_of_mem [Fact p.Prime] {U : Subgroup G} (hU : IsPGroup p U) {a b : H}
    (ha : (a : G) ∈ U) (hb : (b : G) ∈ U)
    (hab : QuotientGroup.mk' (primeComplementCore (G := H) p) a =
      QuotientGroup.mk' (primeComplementCore (G := H) p) b) : a = b := by
  have hN : ((a⁻¹ * b : H) : G) ∈ GLBPrimeCore p H := by
    rw [mem_glbPrimeCore_iff_mk_eq_one, map_mul, map_inv, hab, inv_mul_cancel]
  have hmem : ((a⁻¹ * b : H) : G) ∈ U ⊓ GLBPrimeCore p H :=
    ⟨by simpa using U.mul_mem (U.inv_mem ha) hb, hN⟩
  rw [inf_eq_bot_of_isPGroup (Fact.out : p.Prime) hU (glbPrimeCore_coprime p H),
    Subgroup.mem_bot] at hmem
  exact inv_mul_eq_one.mp (Subtype.ext hmem)

theorem le_of_map_mk_le [Fact p.Prime] {U B C : Subgroup G} (hUH : U ≤ H) (hU : IsPGroup p U)
    (hBU : B ≤ U) (hCU : C ≤ U)
    (hle : (B.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (C.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) : B ≤ C := by
  intro b hb
  obtain ⟨c, hc, hcb⟩ := hle (Subgroup.mem_map_of_mem _
    (show (⟨b, hUH (hBU hb)⟩ : H) ∈ B.subgroupOf H from hb))
  have hcm : (c : G) ∈ U := hCU (Subgroup.mem_subgroupOf.mp hc)
  have hcb' : c = ⟨b, hUH (hBU hb)⟩ := eq_of_mk_eq_of_mem hU hcm (hBU hb) hcb
  have hc' : (⟨b, hUH (hBU hb)⟩ : H) ∈ C.subgroupOf H := hcb' ▸ hc
  exact hc'

theorem D2Escape.relIndex_map_eq (h : D2Escape p P M A H R) {F : Subgroup G} (hFR : F ≤ R) :
    ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))).relIndex
      ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) =
      F.relIndex R := by
  have hle : (F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hFR)
  have h1 := Subgroup.relIndex_mul_card
    ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    ((R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
  have h2 := Subgroup.relIndex_mul_card F R
  rw [inf_eq_left.mpr hle, h.card_map_eq hFR, h.card_map_eq le_rfl] at h1
  rw [inf_eq_left.mpr hFR] at h2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h2.symm)

theorem D2Escape.exists_lift_normalizer [Fact p.Prime] (h : D2Escape p P M A H R)
    {c : H ⧸ primeComplementCore (G := H) p}
    (hc : c ∈ ((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)))
    (hcN : c ∈ Subgroup.normalizer (((R.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _)) :
    ∃ t : H, (t : G) ∈ M ∧ (t : G) ∈ Subgroup.normalizer (R : Set G) ∧
      QuotientGroup.mk' (primeComplementCore (G := H) p) t = c := by
  obtain ⟨k, hk, hkc⟩ := hc
  have hkN : k ∈ (Subgroup.normalizer (((R.subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _)).comap
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [Subgroup.mem_comap, hkc]
    exact hcN
  obtain ⟨o, ho, t, ht, hot⟩ := Subgroup.mem_sup_of_normal_left.mp
    (comap_normalizer_map_le_sup h.prime (primeComplementCore (G := H) p)
      (primeComplementCore_coprime p) h.isPGroup.comap_subtype hkN)
  have hoN : ((o : H) : G) ∈ GLBPrimeCore p H :=
    (mem_glbPrimeCore_iff_mk_eq_one o).mpr ((QuotientGroup.eq_one_iff o).mpr ho)
  refine ⟨t, ?_, ?_, ?_⟩
  · have : (t : G) = ((o : H) : G)⁻¹ * (k : G) := by rw [← hot]; simp
    rw [this]
    exact M.mul_mem (M.inv_mem (h.primeCore_le hoN)) (Subgroup.mem_subgroupOf.mp hk).2
  · have h1 : (t : G) ∈ Subgroup.normalizer
        (((R.subgroupOf H).map H.subtype : Subgroup G) : Set G) :=
      Subgroup.le_normalizer_map H.subtype ⟨t, ht, rfl⟩
    rwa [Subgroup.map_subgroupOf_eq_of_le h.le_H] at h1
  · have ho1 : QuotientGroup.mk' (primeComplementCore (G := H) p) o = 1 :=
      (QuotientGroup.eq_one_iff o).mpr ho
    rw [← hkc, ← hot, map_mul, ho1, one_mul]

theorem D2Escape.heisData_of_u3 [Fact p.Prime] (hKU : UnitaryBorelKFacts)
    (h : D2Escape p P M A H R) (hglob : AGLGlobal G)
    (hRbar : (Rbar : Subgroup _) = (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p _ Rbar ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsUnitaryIndex p d) (hn : d.1.fieldExponent = 1)
    (e : K ≃* CatGroup d) :
    D2HeisData p M H R (R ⊓ Subgroup.centralizer (R : Set G)) := by
  have hp : p.Prime := h.prime
  have hp3 : 3 ≤ p := by have := hp.two_le; have := h.ne_two; omega
  obtain ⟨hNeq, hCR, hZcard, hcomm, hpow, hD, -, hsolv, -⟩ := hK.borel_of_u3 hKU hd hn e
  have hRK := hK.sylow_le_of_u3 hd hn e
  have hdq : ∃ q : TauCeti.PrimePower, q.p = p ∧ q.exponent = 1 ∧ d.1 = .twistedA 2 q := by
    obtain ⟨q, hq, hdq, hfe, -⟩ := hd.exists_eq
    exact ⟨q, hq, hfe ▸ hn, hdq⟩
  have hRH : R ≤ H := h.le_H
  have hRp : IsPGroup p R := h.isPGroup
  have hRN : R ⊓ GLBPrimeCore p H = ⊥ := inf_eq_bot_of_isPGroup hp hRp (glbPrimeCore_coprime p H)
  have hcardR : Nat.card R = p ^ 3 := h.card_eq_of_u3 hRbar hK hd hn e
  have hZb : ((R ⊓ Subgroup.centralizer (R : Set G)).subgroupOf H).map
      (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
      (Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) ⊓
        Subgroup.centralizer ((Rbar : Subgroup (H ⧸ primeComplementCore (G := H) p)) :
          Set (H ⧸ primeComplementCore (G := H) p)) := by
    rw [map_inf_centralizer_eq hRH hRp, hRbar]
  have hcardZ : Nat.card (R ⊓ Subgroup.centralizer (R : Set G) : Subgroup G) = p := by
    rw [← h.card_map_eq inf_le_left, hZb]
    exact hZcard
  have hcommR : ⁅R, R⁆ = R ⊓ Subgroup.centralizer (R : Set G) := by
    have hmap : ((⁅R, R⁆ : Subgroup G).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) =
        ((R ⊓ Subgroup.centralizer (R : Set G)).subgroupOf H).map
          (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
      rw [hZb, ← hcomm, hRbar, ← Subgroup.map_commutator]
      congr 1
      apply Subgroup.map_injective H.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hRH,
        Subgroup.map_subgroupOf_eq_of_le ((Subgroup.commutator_le_self R).trans hRH)]
    exact le_antisymm (le_of_map_mk_le hRH hRp (Subgroup.commutator_le_self R) inf_le_left hmap.le)
      (le_of_map_mk_le hRH hRp inf_le_left (Subgroup.commutator_le_self R) hmap.ge)
  have hpowR : ∀ r ∈ R, r ^ p = 1 := by
    intro u hu
    have hπu : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨u, hRH hu⟩ ∈
        (Rbar : Subgroup _) :=
      hRbar ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hu)
    have h1 := hpow _ hπu
    have h2 : ((⟨u, hRH hu⟩ ^ p : H) : G) ∈ GLBPrimeCore p H := by
      rw [mem_glbPrimeCore_iff_mk_eq_one, map_pow, h1]
    have h3 : ((⟨u, hRH hu⟩ ^ p : H) : G) ∈ R ⊓ GLBPrimeCore p H :=
      ⟨by simpa using R.pow_mem hu p, h2⟩
    rw [hRN, Subgroup.mem_bot] at h3
    simpa using h3
  have hZc : ∀ z ∈ R ⊓ Subgroup.centralizer (R : Set G), ∀ r ∈ R, z * r = r * z :=
    fun z hz r hr => (Subgroup.mem_centralizer_iff.mp hz.2 r hr).symm
  have hZN : ∀ g ∈ Subgroup.normalizer (R : Set G), ∀ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
      g * z * g⁻¹ ∈ R ⊓ Subgroup.centralizer (R : Set G) := fun g hg z hz =>
    ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hz.1,
      Subgroup.mem_subgroupOf.mp
        ((Subgroup.normal_subgroupOf_centralizer_normalizer (R : Set G)).conj_mem
          ⟨z, Subgroup.centralizer_le_normalizer _ hz.2⟩ (Subgroup.mem_subgroupOf.mpr hz.2)
          ⟨g, hg⟩)⟩
  have hlines : ∃ t ∈ H ⊓ M, t ∈ Subgroup.normalizer (R : Set G) ∧
      ∃ m lam n : ℕ, 2 ≤ m ∧ orderOf (lam : ZMod p) = p - 1 ∧ 6 ∣ n ∧
      (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
        t ^ m * x * (t ^ m)⁻¹ = x ^ lam * z) ∧
      (∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
        t ^ n * x * (t ^ n)⁻¹ = x⁻¹ * z) ∧
      ∀ j : ℕ, 0 < j → j < m → ∀ F : Subgroup G,
        R ⊓ Subgroup.centralizer (R : Set G) ≤ F → F ≤ R → F.relIndex R = p →
          t ^ j ∉ Subgroup.normalizer (F : Set G) := by
    obtain ⟨c, -, hcN, lam, hlam, hscal, hline⟩ :=
      exists_lines_torus_u3 hp h.ne_two e hdq hRK
    have hm2 : 2 ≤ (p + 1) / Nat.gcd 3 (p + 1) := one_lt_lineOrbit hp3
    have hmev := even_lineOrbit hp h.ne_two
    generalize (p + 1) / Nat.gcd 3 (p + 1) = m at hscal hline hm2 hmev
    obtain ⟨m₂, hm₂⟩ := hmev
    have hcX₀ : c ∈ ((H ⊓ M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := hNeq.le hcN
    obtain ⟨t, htM, htN, htc⟩ := h.exists_lift_normalizer hcX₀ (hRbar ▸ hcN)
    have hscal' : ∀ x ∈ R, ∃ z ∈ R ⊓ Subgroup.centralizer (R : Set G),
        (t : G) ^ m * x * ((t : G) ^ m)⁻¹ = x ^ lam * z := by
      intro x hx
      have hπx : QuotientGroup.mk' (primeComplementCore (G := H) p) ⟨x, hRH hx⟩ ∈
          (Rbar : Subgroup _) :=
        hRbar ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx)
      obtain ⟨zb, hzb, hzeq⟩ := hscal _ hπx
      rw [← hZb] at hzb
      obtain ⟨z, hz, hzc⟩ := hzb
      refine ⟨(z : G), Subgroup.mem_subgroupOf.mp hz, ?_⟩
      have hmem1 : (((t ^ m * ⟨x, hRH hx⟩ * (t ^ m)⁻¹ : H)) : G) ∈ R :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ htN _) x).mp hx
      have hmem2 : (((⟨x, hRH hx⟩ ^ lam * z : H)) : G) ∈ R :=
        R.mul_mem (R.pow_mem hx lam) (Subgroup.mem_subgroupOf.mp hz).1
      have := eq_of_mk_eq_of_mem hRp hmem1 hmem2 (by
        rw [map_mul, map_mul, map_inv, map_pow, htc, hzeq, map_mul, map_pow, hzc])
      exact congrArg Subtype.val this
    refine ⟨(t : G), ⟨t.2, htM⟩, htN, m, lam, m * (3 * ((p - 1) / 2)), hm2, hlam,
      ⟨m₂ * ((p - 1) / 2), by rw [hm₂]; ring⟩, hscal', fun x hx => ?_,
      fun j hj0 hjm F hZF hFR hidx => ?_⟩
    · obtain ⟨z, hz, hzx⟩ := exists_mul_of_pow_scalar_inverts_mod hp h.ne_two hpowR hZc
        (fun z hz => hZN _ (Subgroup.pow_mem _ htN m) z hz) hlam hscal' (j := 3) (by decide) hx
      exact ⟨z, hz, by rwa [pow_mul]⟩
    · intro hFn
      refine hline j hj0 hjm
        ((F.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p))) ?_ ?_ ?_ ?_
      · rw [← hZb]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hZF)
      · rw [hRbar]
        exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hFR)
      · rw [hRbar, h.relIndex_map_eq hFR]
        exact hidx
      · rw [← htc, ← map_pow]
        exact map_mk_le_normalizer_map_mk (Subgroup.zpowers_le.mpr hFn)
          ⟨t ^ j, Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers _), rfl⟩
  have hCR' : Subgroup.centralizer (((R.subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) : Subgroup _) : Set _) ≤
      (R.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
    rw [← hRbar]
    exact hCR
  refine ⟨⟨h.toPair_of_u3 hKU hglob hK hd hn e, hcardR, ⟨hcardZ, hcommR, hpowR⟩, hlines, ?_, ?_,
    centralizer_le_of_map (X := R) fun y hy => hCR' hy.2,
    pRank_inf_le_of_pRank_top_le hp hK.pRank_top_eq.le⟩,
    fun L hL hLL => le_glbPrimeCore_of_perfect hsolv hL hLL⟩
  · obtain ⟨t, htK, htN, m, -, -, hm, -, -, -, -, hline⟩ := hlines
    exact fun V hZV hVR hV => eq_or_eq_of_lines hp hm hcardR hcardZ hline hZV hVR
      (hV ⟨htK, htN⟩)
  · exact fun Y hY hYN => le_glbPrimeCore_or_le_of_forall h.primeCore_le (inf_le_left.trans hRH)
      (hRp.to_le inf_le_left) (fun W hW hWn => by rw [hZb]; exact hD W hW hWn) hY hYN

end Reduced

end CFSG.AGLEmbeddingD2
