module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413Bender
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma412
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma413Tools

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
private theorem orderOf_inv_mul_mul (c u : G) : orderOf (c⁻¹ * u * c) = orderOf u := by
  have h1 := (MulAut.conj c⁻¹).orderOf_eq u
  rwa [MulAut.conj_apply, inv_inv] at h1

theorem exists_conj_of_bender
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {t : G}
    (ht : FooteInCC M t) (htK : t ∉ footeK L t)
    (hBen : Open.fusionIsBenderGroup (footeK L t ⧸ pPrimeCore 2 (footeK L t))) {x y : G}
    (hx : x ∈ footeK L t ⊓ coreActionKernel M) (hy : y ∈ footeK L t ⊓ coreActionKernel M)
    (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) :
    ∃ m ∈ footeK L t ⊓ normalizer (M : Set G), m * x * m⁻¹ = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht' := ht
  obtain ⟨ht2, htC, hCt⟩ := ht'
  obtain ⟨-, -, hBt, -⟩ := foote_lemma_4_9_core h h47 hST hM ht2 htC hCt
  obtain ⟨hKB, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM ht2 htC hCt
  obtain ⟨R, hR, hRC⟩ := exists_isSylowOf_footeK_le h h47 hST hAsc h2An hM ht
  set K := footeK L t with hK
  set C := coreActionKernel M with hC
  have hKt : K ≤ centralizer ({t} : Set G) := hKB.trans hBt
  have hRKC : IsSylowOf 2 R (K ⊓ C) := hR.of_le (le_inf hR.le hRC) inf_le_left
  have hp : ∀ u : G, orderOf u = 2 → IsPGroup 2 (zpowers u) := fun u hu =>
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])
  obtain ⟨c₁, hc₁, hc₁x⟩ := exists_conj_le_of_isSylowOf hRKC (zpowers_le.mpr hx) (hp x hx2)
  obtain ⟨c₂, hc₂, hc₂y⟩ := exists_conj_le_of_isSylowOf hRKC (zpowers_le.mpr hy) (hp y hy2)
  have hx' : c₁⁻¹ * x * c₁ ∈ R := hc₁x x (mem_zpowers x)
  have hy' : c₂⁻¹ * y * c₂ ∈ R := hc₂y y (mem_zpowers y)
  have hrx : orderOf (c₁⁻¹ * x * c₁) = 2 := by rw [orderOf_inv_mul_mul, hx2]
  have hry : orderOf (c₂⁻¹ * y * c₂) = 2 := by rw [orderOf_inv_mul_mul, hy2]
  obtain ⟨m', hm'K, hm'R, hm'⟩ :=
    exists_mem_normalizer_conj_of_isBender_quotient hR hBen hx' hy' hrx hry
  have hm'N : m' ∈ normalizer (M : Set G) := by
    have hTC : R ⊔ zpowers t ≤ C := sup_le hRC (zpowers_le.mpr htC)
    set r := c₁⁻¹ * x * c₁ with hr
    have hrK : r ∈ K := hR.le hx'
    have hr2 : r ^ 2 = 1 := by rw [← hrx]; exact pow_orderOf_eq_one r
    have hr1 : r ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hrx; omega
    have ht2' : t ^ 2 = 1 := by rw [← ht2]; exact pow_orderOf_eq_one t
    have ht1 : t ≠ 1 := fun h1 => by rw [h1, orderOf_one] at ht2; omega
    have hrt : t ≠ r := fun h1 => htK (h1 ▸ hrK)
    have hrt' : r * t = t * r := mem_centralizer_singleton_iff.mp (hKt hrK)
    have hW := isKleinFour_sup_zpowers hr2 ht2' hr1 ht1 hrt hrt'
    have hWT : zpowers r ⊔ zpowers t ≤ R ⊔ zpowers t :=
      sup_le_sup_right (zpowers_le.mpr hx') _
    apply foote_cor_4_8_iv h h47 hST hM hTC hW hWT
    have hmt : m' ∈ normalizer (zpowers t : Set G) := by
      have hm't : m' * t = t * m' := mem_centralizer_singleton_iff.mp (hKt hm'K)
      apply mem_normalizer_of_forall_commute
      intro u hu
      obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hu
      exact ((Commute.zpow_left (Commute.symm hm't) i)).eq
    exact inf_normalizer_le_normalizer_sup R (zpowers t) (mem_inf.mpr ⟨hm'R, hmt⟩)
  have hCN : ∀ c ∈ C, c ∈ normalizer (M : Set G) := fun c hc => (mem_coreActionKernel.mp hc).1
  refine ⟨c₂ * m' * c₁⁻¹, mem_inf.mpr ⟨?_, ?_⟩, ?_⟩
  · exact mul_mem (mul_mem (mem_inf.mp hc₂).1 hm'K) (inv_mem (mem_inf.mp hc₁).1)
  · exact mul_mem (mul_mem (hCN _ (mem_inf.mp hc₂).2) hm'N) (inv_mem (hCN _ (mem_inf.mp hc₁).2))
  · calc c₂ * m' * c₁⁻¹ * x * (c₂ * m' * c₁⁻¹)⁻¹
        = c₂ * (m' * (c₁⁻¹ * x * c₁) * m'⁻¹) * c₂⁻¹ := by group
      _ = c₂ * (c₂⁻¹ * y * c₂) * c₂⁻¹ := by rw [hm']
      _ = y := by group

theorem mem_or_mul_mem_footeK
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {s : G}
    (hs : FooteInCC M s) {x : G} (hxC : x ∈ coreActionKernel M) (hxs : x * s = s * x)
    (hx2 : orderOf x = 2) : x ∈ footeK L s ∨ x * s ∈ footeK L s := by
  obtain ⟨hs2, hsC, hCs⟩ := hs
  obtain ⟨-, -, hBs, -⟩ := foote_lemma_4_9_core h h47 hST hM hs2 hsC hCs
  obtain ⟨hKB, -, -, -, -, hall⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM hs2 hsC hCs
  have hss : s * s = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
  have hxB := inf_centralizer_le_footeB h h47 hM hs2 hsC
    (mem_inf.mpr ⟨hxC, mem_centralizer_singleton_iff.mpr hxs⟩)
  exact mem_or_mul_mem_of_mem_sup_zpowers (hKB.trans hBs) hss (hall x hxB hx2)

theorem false_of_bender_pair
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M) {s : G}
    (hs : FooteInCC M s) (hsK : s ∉ footeK L s)
    (hBen : Open.fusionIsBenderGroup (footeK L s ⧸ pPrimeCore 2 (footeK L s))) {z₀ : G}
    (hz₀ : z₀ ∈ footeK L s ⊓ coreActionKernel M) (hz₀2 : orderOf z₀ = 2)
    (hz₀C : ¬ FooteInCC M z₀) (hz₁C : ¬ FooteInCC M (z₀ * s)) {n₀ : G}
    (hn₀ : n₀ ∈ normalizer (M : Set G)) (hn₀z : n₀ * z₀ * n₀⁻¹ = z₀ * s) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hs' := hs
  obtain ⟨hs2, hsC, hCs⟩ := hs'
  obtain ⟨hBN, -, hBs, -⟩ := foote_lemma_4_9_core h h47 hST hM hs2 hsC hCs
  obtain ⟨hKB, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM hs2 hsC hCs
  set K := footeK L s with hK
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  have hKs : K ≤ centralizer ({s} : Set G) := hKB.trans hBs
  have hss : s * s = 1 := by rw [← sq, ← hs2, pow_orderOf_eq_one]
  have hsi : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hs1 : s ≠ 1 := fun h1 => by rw [h1, orderOf_one] at hs2; omega
  have hCN : ∀ c ∈ C, c ∈ N := fun c hc => (mem_coreActionKernel.mp hc).1
  have hsN : s ∈ N := hCN s hsC
  have hz₀z₀ : z₀ * z₀ = 1 := by rw [← sq, ← hz₀2, pow_orderOf_eq_one]
  have hiso : ∀ n ∈ N, n * s * n⁻¹ * s = s * (n * s * n⁻¹) → n * s * n⁻¹ = s := by
    intro n hn hcomm
    by_contra hne
    set y := n * s * n⁻¹ with hy
    have hyC : FooteInCC M y := hs.conj hn
    have hy2 : orderOf y = 2 := hyC.1
    have hyy : y * y = 1 := by rw [← sq, ← hy2, pow_orderOf_eq_one]
    rcases mem_or_mul_mem_footeK h h47 hST hAsc h2An hM hs hyC.2.1 hcomm hy2 with hyK | hysK
    · obtain ⟨m, hm, hmz⟩ := exists_conj_of_bender h h47 hST hAsc h2An hM hs hsK hBen hz₀
        (mem_inf.mpr ⟨hyK, hyC.2.1⟩) hz₀2 hy2
      apply hz₀C
      have h1 := hyC.conj (inv_mem (mem_inf.mp hm).2)
      rwa [← hmz, show m⁻¹ * (m * z₀ * m⁻¹) * m⁻¹⁻¹ = z₀ by group] at h1
    · have hk2 : orderOf (y * s) = 2 := by
        apply orderOf_eq_prime
        · rw [sq]
          calc y * s * (y * s) = y * (s * y) * s := by group
            _ = y * (y * s) * s := by rw [← hcomm]
            _ = (y * y) * (s * s) := by group
            _ = 1 := by rw [hyy, hss, one_mul]
        · intro h1
          apply hne
          calc y = y * s * s := by rw [mul_assoc, hss, mul_one]
            _ = s := by rw [h1, one_mul]
      obtain ⟨m, hm, hmz⟩ := exists_conj_of_bender h h47 hST hAsc h2An hM hs hsK hBen hz₀
        (mem_inf.mpr ⟨hysK, mul_mem hyC.2.1 hsC⟩) hz₀2 hk2
      apply hz₁C
      have hms : m * s = s * m := mem_centralizer_singleton_iff.mp (hKs (mem_inf.mp hm).1)
      have h1 := hyC.conj (inv_mem (mem_inf.mp hm).2)
      have h2 : m⁻¹ * y * m⁻¹⁻¹ = z₀ * s := by
        have h3 : y = m * z₀ * m⁻¹ * s := by rw [hmz, mul_assoc, hss, mul_one]
        rw [h3]
        have h4 : m⁻¹ * s * m = s := by rw [mul_assoc, ← hms, inv_mul_cancel_left]
        calc m⁻¹ * (m * z₀ * m⁻¹ * s) * m⁻¹⁻¹ = z₀ * (m⁻¹ * s * m) := by group
          _ = z₀ * s := by rw [h4]
      rwa [h2] at h1
  have : Fintype ↥N := Fintype.ofFinite _
  obtain ⟨O, hOn, hOodd, hO⟩ := ZStar.glauberman_zStar ↥N ⟨s, hsN⟩
    (fun h1 => hs1 (congrArg Subtype.val h1)) (Subtype.ext hss)
    (fun g hg => Subtype.ext (hiso g g.2 (congrArg Subtype.val hg)))
  set O' := O.map N.subtype with hO'
  have hO'N : ∀ o ∈ O', o ∈ N := fun o ho => by
    obtain ⟨o', -, rfl⟩ := mem_map.mp ho
    exact o'.2
  have hO'conj : ∀ n ∈ N, ∀ o ∈ O', n * o * n⁻¹ ∈ O' := by
    intro n hn o ho
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    exact ⟨⟨n, hn⟩ * o' * ⟨n, hn⟩⁻¹, hOn.conj_mem o' ho' ⟨n, hn⟩, rfl⟩
  have hO'odd : ∀ o ∈ O', Odd (orderOf o) := by
    intro o ho
    obtain ⟨o', ho', rfl⟩ := mem_map.mp ho
    have h1 : orderOf o' ∣ Nat.card O := Subgroup.orderOf_dvd_natCard O ho'
    rw [subtype_apply, Subgroup.orderOf_coe]
    exact Odd.of_dvd_nat hOodd h1
  have hO's : ∀ n ∈ N, n * s * n⁻¹ * s⁻¹ ∈ O' := fun n hn => ⟨_, hO ⟨n, hn⟩, rfl⟩
  set v := n₀ * s * n₀⁻¹ with hv
  have hvv : v * v = 1 := by
    calc v * v = n₀ * (s * s) * n₀⁻¹ := by rw [hv]; group
      _ = 1 := by rw [hss]; group
  have hsv : s * v ∈ O' := by
    have h1 := hO'conj s hsN _ (hO's n₀ hn₀)
    have h2 : s * (n₀ * s * n₀⁻¹ * s⁻¹) * s⁻¹ = s * v := by
      rw [hsi, hv]
      calc s * (n₀ * s * n₀⁻¹ * s) * s = s * (n₀ * s * n₀⁻¹) * (s * s) := by group
        _ = s * (n₀ * s * n₀⁻¹) := by rw [hss, mul_one]
    rwa [h2] at h1
  obtain ⟨k, hk⟩ := exists_pow_mul_conj_eq hss hvv (hO'odd _ hsv)
  set h₁ := (s * v) ^ k with hh₁def
  have hh₁ : h₁ ∈ O' := pow_mem hsv k
  have hh₁N : h₁ ∈ N := hO'N _ hh₁
  set c := h₁⁻¹ * n₀ with hcdef
  have hcN : c ∈ N := mul_mem (inv_mem hh₁N) hn₀
  have hcs : c * s = s * c := by
    have h1 : c * s * c⁻¹ = s := by
      calc c * s * c⁻¹ = h₁⁻¹ * (n₀ * s * n₀⁻¹) * h₁ := by rw [hcdef]; group
        _ = h₁⁻¹ * (h₁ * s * h₁⁻¹) * h₁ := by rw [← hv, ← hk]
        _ = s := by group
    calc c * s = c * s * c⁻¹ * c := by group
      _ = s * c := by rw [h1]
  set k₁ := c * z₀ * c⁻¹ with hk₁def
  have hk₁K : k₁ ∈ K :=
    (mem_normalizer_iff.mp (mem_normalizer_footeK (hBN (mem_centralizer_singleton_iff.mpr hcs)))
      z₀).mp (mem_inf.mp hz₀).1
  have hk₁N : k₁ ∈ N := mul_mem (mul_mem hcN (hCN _ (mem_inf.mp hz₀).2)) (inv_mem hcN)
  have hz₁ : z₀ * s = h₁ * k₁ * h₁⁻¹ := by
    rw [← hn₀z, hk₁def, show n₀ = h₁ * c by rw [hcdef]; group]
    group
  set o₂ := z₀ * (h₁ * (k₁ * h₁⁻¹ * k₁⁻¹)) * z₀⁻¹ with ho₂def
  have ho₂ : o₂ ∈ O' := hO'conj z₀ (hCN _ (mem_inf.mp hz₀).2) _
    (mul_mem hh₁ (hO'conj k₁ hk₁N _ (inv_mem hh₁)))
  set kk := z₀ * k₁ with hkkdef
  have hkkK : kk ∈ K := mul_mem (mem_inf.mp hz₀).1 hk₁K
  have hseq : s = o₂ * kk := by
    calc s = z₀ * (z₀ * s) := by rw [← mul_assoc, hz₀z₀, one_mul]
      _ = z₀ * (h₁ * k₁ * h₁⁻¹) := by rw [hz₁]
      _ = o₂ * kk := by rw [ho₂def, hkkdef]; group
  have hkks : kk * s = s * kk := (mem_centralizer_singleton_iff.mp (hKs hkkK))
  have hcomm : o₂ * kk = kk * o₂ := by
    have ho₂' : o₂ = s * kk⁻¹ := by rw [hseq]; group
    rw [ho₂']
    calc s * kk⁻¹ * kk = kk * s * kk⁻¹ := by rw [hkks]; group
      _ = kk * (s * kk⁻¹) := by group
  have hsk := mem_zpowers_of_eq_mul_of_odd hss hseq hcomm (hO'odd o₂ ho₂)
  exact hsK (zpowers_le.mpr hkkK hsk)

omit [Finite G] in
theorem mem_rightConjugate_iff_of_footeUniqueContainment {M : Subgroup G}
    (hU : FooteUniqueContainment M) {z : G} (hz : orderOf z = 2)
    (hzC : z ∈ coreActionKernel M) (hCz : centralizer ({z} : Set G) ≤ normalizer (M : Set G))
    (g : G) :
    z ∈ AschbacherTightEmbedding.rightConjugate (normalizer (M : Set G)) g ↔
      g ∈ normalizer (M : Set G) := by
  have hzN : z ∈ normalizer (M : Set G) := (mem_coreActionKernel.mp hzC).1
  constructor
  · intro hzg
    obtain ⟨n, hn, hnz⟩ := mem_map.mp hzg
    have hnz' : g⁻¹ * n * g = z := by simpa [MulAut.conj_apply] using hnz
    have h1 : g⁻¹⁻¹ * z * g⁻¹ ∈ normalizer (M : Set G) := by
      rw [← hnz', show g⁻¹⁻¹ * (g⁻¹ * n * g) * g⁻¹ = n by group]
      exact hn
    by_contra hg
    exact hU z g⁻¹ ⟨hz, hzC, hCz, h1, fun h2 => hg (by simpa using inv_mem h2)⟩
  · intro hg
    refine mem_map.mpr ⟨g * z * g⁻¹, mul_mem (mul_mem hg hzN) (inv_mem hg), ?_⟩
    simp [mul_assoc]

theorem productUniqueContainment_of_bender
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G} (hM : IsFooteM L M)
    (hU : FooteUniqueContainment M) (hB : ∀ t : G, FooteInCC M t → t ∉ footeK L t) {z : G}
    (hz : orderOf z = 2) (hzC : z ∈ coreActionKernel M)
    (hCz : centralizer ({z} : Set G) ≤ normalizer (M : Set G)) :
    AschbacherStrongEmbedding.ProductUniqueContainment (normalizer (M : Set G)) z := by
  intro w hw hzw hne g
  obtain ⟨k, hk⟩ := hw
  change k⁻¹ * z * k = w at hk
  set N := normalizer (M : Set G) with hN
  set C := coreActionKernel M with hC
  have hCN : ∀ c ∈ C, c ∈ N := fun c hc => (mem_coreActionKernel.mp hc).1
  have hzz : z * z = 1 := by rw [← sq, ← hz, pow_orderOf_eq_one]
  have hwN : w ∈ N := hCz (mem_centralizer_singleton_iff.mpr hzw.eq.symm)
  have hkN : k ∈ N := by
    by_contra hkN
    exact hU z k ⟨hz, hzC, hCz, hk ▸ hwN, hkN⟩
  have hwC : w ∈ C := by
    rw [← hk]
    have h1 := (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M
      (inv_mem hkN)) z).mp hzC
    simpa using h1
  have hww : w * w = 1 := by
    rw [← hk]
    calc k⁻¹ * z * k * (k⁻¹ * z * k) = k⁻¹ * (z * z) * k := by group
      _ = 1 := by rw [hzz]; group
  have hzw' : z * w = w * z := hzw.eq
  have hss : z * w * (z * w) = 1 := by
    calc z * w * (z * w) = z * (w * z) * w := by group
      _ = z * (z * w) * w := by rw [hzw']
      _ = (z * z) * (w * w) := by group
      _ = 1 := by rw [hzz, hww, one_mul]
  have hs1 : z * w ≠ 1 := fun h1 => hne (by
    calc w = z * z * w := by rw [hzz, one_mul]
      _ = z * (z * w) := by group
      _ = z := by rw [h1, mul_one])
  have hs2 : orderOf (z * w) = 2 := orderOf_eq_prime (by rw [sq]; exact hss) hs1
  have hsC : z * w ∈ C := mul_mem hzC hwC
  have hzs : z * (z * w) = z * w * z := by
    calc z * (z * w) = z * (w * z) := by rw [hzw']
      _ = z * w * z := by group
  have hzsw : z * (z * w) = w := by rw [← mul_assoc, hzz, one_mul]
  have hwsz : w * (z * w) = z := by
    calc w * (z * w) = w * (w * z) := by rw [hzw']
      _ = (w * w) * z := by group
      _ = z := by rw [hww, one_mul]
  have hws : w * (z * w) = z * w * w := by rw [hwsz, mul_assoc, hww, mul_one]
  set s := z * w with hs
  have hzCC : ¬ FooteInCC M z := fun h1 => h1.2.2 hCz
  have hwCC : ¬ FooteInCC M w := by
    intro h1
    apply hzCC
    have h2 := h1.conj hkN
    rwa [← hk, show k * (k⁻¹ * z * k) * k⁻¹ = z by group] at h2
  have hsCC : ¬ FooteInCC M s := by
    intro hsc
    have hsc' := hsc
    obtain ⟨-, -, hCs⟩ := hsc'
    obtain ⟨-, -, -, -, htype, -⟩ := foote_lemma_4_9 h h47 hST hAsc h2An hM hs2 hsC hCs
    have hsK := hB s hsc
    have hBen : Open.fusionIsBenderGroup (footeK L s ⧸ pPrimeCore 2 (footeK L s)) := by
      rcases htype with ⟨hb, -⟩ | ⟨-, hin⟩
      · exact hb
      · exact absurd hin hsK
    rcases mem_or_mul_mem_footeK h h47 hST hAsc h2An hM hsc hzC hzs hz with hzK | hwK
    · refine false_of_bender_pair h h47 hST hAsc h2An hM hsc hsK hBen (mem_inf.mpr ⟨hzK, hzC⟩)
        hz hzCC (by rwa [hzsw]) (inv_mem hkN) ?_
      rw [hzsw, ← hk]
      group
    · rw [hzsw] at hwK
      have hw2 : orderOf w = 2 := by
        rw [← hk]
        rw [orderOf_inv_mul_mul, hz]
      refine false_of_bender_pair h h47 hST hAsc h2An hM hsc hsK hBen (mem_inf.mpr ⟨hwK, hwC⟩)
        hw2 hwCC (by rwa [hwsz]) hkN ?_
      rw [hwsz, ← hk]
      group
  have hCs : centralizer ({s} : Set G) ≤ N := by
    by_contra h1
    exact hsCC ⟨hs2, hsC, h1⟩
  constructor
  · intro hg
    by_contra hgN
    exact hU s g ⟨hs2, hsC, hCs, hg, hgN⟩
  · intro hg
    exact mul_mem (mul_mem (inv_mem hg) (hCN s hsC)) hg

theorem foote_lemma_4_13_bender
    (h : FooteSec4 G L) (h47 : FooteThm47Statement)
    (hST : GSThmB.SuzukiTausskyInput) (hAsc : Foote5.AschbacherCentralCoreInput)
    (h2An : GSThmB.Solomon2AnInput) (hA5 : GSThmB.AschbacherTheorem5Input)
    (hE8 : FooteL2FourgroupE8) (hK : AschbacherKnownGroup.AschbacherKnownGroupFacts)
    (hcalc : FooteSmallCentralizers) (hFI : FooteFourgroupInner) (hRO : FooteL2RootedOuter)
    {M : Subgroup G} (hM : IsFooteM L M)
    (hH : ∀ t : G, FooteInCC M t → ∀ u ∈ footeK L t, FooteInCC M u → u = t)
    (hPE : FooteEvenOrNormalizes M) (hB : ∀ t : G, FooteInCC M t → t ∉ footeK L t) :
    ∀ t : G, ¬ FooteInCC M t := by
  intro t₀ ht₀
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.simple
  obtain ⟨E, hE2, hE8', hEC⟩ := hM.exists_card_eight h
  set N := normalizer (M : Set G) with hN
  set C := coreActionKernel M with hC
  have hCN : ∀ c ∈ C, c ∈ N := fun c hc => (mem_coreActionKernel.mp hc).1
  obtain ⟨z, hzE, hz1, hCz⟩ := foote_lemma_4_11 h h47 hST hAsc h2An hM hH hEC hE2 (by omega)
  have hz : orderOf z = 2 := orderOf_eq_prime (hE2 z hzE) hz1
  have hzC : z ∈ C := hEC hzE
  have hU := foote_lemma_4_12 h h47 hST hAsc h2An hA5 hE8 hK hcalc hFI hRO hM hH hPE
  have hP := productUniqueContainment_of_bender h h47 hST hAsc h2An hM hU hB hz hzC hCz
  have huniq := mem_rightConjugate_iff_of_footeUniqueContainment hU hz hzC hCz
  have hNtop : N ≠ ⊤ := by
    intro htop
    have hCn : C.Normal := normalizer_eq_top_iff.mp
      (eq_top_iff.mpr (htop ▸ normalizer_le_normalizer_coreActionKernel M))
    rcases hCn.eq_bot_or_eq_top with h1 | h1
    · have h2 := Subgroup.card_le_of_le hEC
      rw [h1, card_bot, hE8'] at h2
      omega
    · apply hM.not_odd h
      have h1' : coreActionKernel M = ⊤ := h1
      have h2 : M ≤ oddCoreIn M := fun x hx =>
        hM.inf_coreActionKernel_le h (mem_inf.mpr ⟨hx, h1' ▸ mem_top x⟩)
      have h3 : oddCoreIn M = M := le_antisymm (map_subtype_le _) h2
      rw [← h3]
      exact odd_card_oddCoreIn M
  have hse := fusionStronglyEmbedded_of_productUniqueContainment h.simple hE2 hE8' hz hNtop
    huniq hP
  exact ht₀.2.2 (centralizer_le_of_stronglyEmbedded hse (hCN t₀ ht₀.2.1) ht₀.1)

end CFSG.ComponentClassification.FooteLit
