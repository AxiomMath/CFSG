module

public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarInputs
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarAltE27
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarSp6E27
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixICommX
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveFourOneProof
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSevenSylow
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Quot
import CFSG.GroupTheory.CoprimeCosetFixed
import CFSG.GH74.QTGen4.U42.VertexGen4B
import TauCeti.GroupTheory.QuotientGroup.MulAut
import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixInvariantX
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section12.TwelveSixKbarAltE27

public section

namespace CFSG.LocalAnalysis.AGL81TheoremCD.Section12

open CFSG.Open Subgroup CFSG.LocalAnalysis.RankThreeUC.AGL81C
open scoped commutatorElement

namespace KbarExcl

variable {G : Type} [Group G] [Finite G] {M : Subgroup G} {p : ℕ} {Q H : Subgroup G}

private theorem not_five_dvd_two_pow_mul {n : ℕ} (hn : Odd n) :
    ¬ 5 ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨k, rfl⟩ := hn
  have h16 : (2 ^ (2 * k + 1)) ^ 2 = 16 ^ k * 4 := by
    rw [← pow_mul, show (2 * k + 1) * 2 = 4 * k + 2 by ring, pow_add, pow_mul]
    norm_num
  have h5 : 16 ^ k % 5 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 h with h2 | h2
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h2
    omega
  · rw [h16] at h2
    generalize 16 ^ k = x at h2 h5
    omega

private theorem not_five_dvd_card_of_isPSLType {I : Subgroup G} {n : ℕ} (hn : Odd n)
    (hI : IsPSLType 2 (GaloisField 2 n) (modTwoCore I)) : ¬ 5 ∣ Nat.card I := by
  obtain ⟨e⟩ := hI
  have hq : Nat.card (modTwoCore I) = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr e.toEquiv]
    exact CFSG.GH74.QTGen4.U42.VertexGen4B.card_psl_galois (by obtain ⟨k, rfl⟩ := hn; omega)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥I)).exists_card_eq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥I)]
  change ¬ 5 ∣ Nat.card (modTwoCore I) * Nat.card (CFSG.pCore 2 ↥I)
  rw [hq, ha]
  intro h
  rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 h with h1 | h1
  · exact not_five_dvd_two_pow_mul hn h1
  · have := Nat.Prime.dvd_of_dvd_pow (by norm_num : Nat.Prime 5) h1
    omega

private theorem conj_mem (hKH : ((kSub p M H).subgroupOf H).Normal) (y : ↥H)
    (k : ↥(kSub p M H)) : (y : G) * k * (y : G)⁻¹ ∈ kSub p M H :=
  (mem_normalizer_iff.mp ((normal_subgroupOf_iff_le_normalizer
    (Section14.kSub_le p M H)).mp hKH y.2) (k : G)).mp k.2

private noncomputable def kbarAct (hKH : ((kSub p M H).subgroupOf H).Normal) :
    ↥H →* MulAut (kbarQuot p M H) :=
  (MulAut.mapQuotient (center (modTwoCore (kSub p M H)))).comp (kbarConj hKH)

private theorem kbarAct_apply_mk (hKH : ((kSub p M H).subgroupOf H).Normal) (y : ↥H)
    (q : modTwoCore (kSub p M H)) :
    kbarAct hKH y (QuotientGroup.mk q) = QuotientGroup.mk (kbarConj hKH y q) :=
  MulAut.mapQuotient_mk _ _ _

private theorem kbarAct_mk (hKH : ((kSub p M H).subgroupOf H).Normal) (y : ↥H)
    (k : ↥(kSub p M H)) :
    kbarAct hKH y (QuotientGroup.mk (QuotientGroup.mk k)) =
      QuotientGroup.mk (QuotientGroup.mk
        (⟨(y : G) * k * (y : G)⁻¹, conj_mem hKH y k⟩ : ↥(kSub p M H))) := by
  rw [kbarAct_apply_mk, kbarConj_mk]

private theorem kbarAct_eq_conj (hKH : ((kSub p M H).subgroupOf H).Normal)
    (k : ↥(kSub p M H)) (hk : (k : G) ∈ H) :
    kbarAct hKH ⟨k, hk⟩ =
      MulAut.conj (QuotientGroup.mk (QuotientGroup.mk k : modTwoCore (kSub p M H)) :
        kbarQuot p M H) := by
  ext q
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k', rfl⟩ := QuotientGroup.mk_surjective q
  rw [kbarAct_mk, MulAut.conj_apply]
  rfl

private theorem ker_kbarAct_le (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    (kbarAct hKH).ker ≤ (xSub p M H).subgroupOf H := by
  intro y hy
  apply TwelveCtx.ker_kbarConj_le h hKH
  rw [MonoidHom.mem_ker]
  apply CFSG.RankThree.PartTwo.Sec15.F153L3C2.mulAut_eq_one_of_central hK.2.2.1
  intro q
  have h1 : kbarAct hKH y (QuotientGroup.mk q) = QuotientGroup.mk q := by
    rw [MonoidHom.mem_ker.1 hy]
    rfl
  rw [kbarAct_apply_mk] at h1
  have h2 := QuotientGroup.eq_iff_div_mem.1 h1
  rwa [div_eq_mul_inv] at h2

private theorem xSub_le_ker_kbarAct (h : TwelveCtx G M p Q H)
    (hKH : ((kSub p M H).subgroupOf H).Normal) (hK : IsTwoPrimeComponentIn (kSub p M H) H) :
    (xSub p M H).subgroupOf H ≤ (kbarAct hKH).ker := by
  intro x hx
  rw [mem_subgroupOf] at hx
  rw [MonoidHom.mem_ker]
  ext q
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [kbarAct_mk, MulAut.one_apply]
  have hconjX : (k : G) * (x : G) * (k : G)⁻¹ ∈ xSub p M H :=
    (mem_normalizer_iff.mp (xSub_normal_of_kSub_normal hKH
      (Section14.kSub_le p M H k.2)) (x : G)).mp hx
  have hcommX : (x : G) * k * (x : G)⁻¹ * (k : G)⁻¹ ∈ xSub p M H := by
    have heq : (x : G) * k * (x : G)⁻¹ * (k : G)⁻¹ =
        (x : G) * ((k : G) * (x : G) * (k : G)⁻¹)⁻¹ := by group
    rw [heq]
    exact (xSub p M H).mul_mem hx ((xSub p M H).inv_mem hconjX)
  have hmem : (⟨(x : G) * k * (x : G)⁻¹, conj_mem hKH x k⟩ : ↥(kSub p M H)) / k ∈
      (xSub p M H).subgroupOf (kSub p M H) := by
    rw [mem_subgroupOf]
    simpa [div_eq_mul_inv] using hcommX
  rw [TwelveCtx.xSub_subgroupOf_kSub_eq h hKH hK, mem_comap, map_div] at hmem
  exact QuotientGroup.eq_iff_div_mem.2 hmem

private theorem exists_lift (hKH : ((kSub p M H).subgroupOf H).Normal) {w : G} (hwH : w ∈ H)
    (hw : orderOf w = 3) {y : kbarQuot p M H} (hy2 : y ^ 2 = 1)
    (hfix : kbarAct hKH ⟨w, hwH⟩ y = y) :
    ∃ c : ↥(kSub p M H), w * c * w⁻¹ = c ∧
      (QuotientGroup.mk (QuotientGroup.mk c : modTwoCore (kSub p M H)) : kbarQuot p M H) = y := by
  classical
  obtain ⟨yt, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨j, hj⟩ := CFSG.RankThree.PartTwo.Sec15.F153L3C2.odd_card_center_quot (kSub p M H)
  have hyt2 : yt ^ 2 ∈ center (modTwoCore (kSub p M H)) := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hy2]
  set u : modTwoCore (kSub p M H) := yt ^ (2 * j + 1) with hu
  have hu_mk : (QuotientGroup.mk u : kbarQuot p M H) = QuotientGroup.mk yt := by
    rw [hu, QuotientGroup.mk_pow, pow_succ, pow_mul, hy2, one_pow, one_mul]
  have hu2 : u ^ 2 = 1 := by
    have h := pow_card_eq_one' (G := center (modTwoCore (kSub p M H))) (x := ⟨yt ^ 2, hyt2⟩)
    rw [hj] at h
    have h' := congrArg Subtype.val h
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h'
    rw [hu, ← pow_mul, show (2 * j + 1) * 2 = 2 * (2 * j + 1) by ring, pow_mul]
    exact h'
  set α := kbarConj hKH ⟨w, hwH⟩ with hα
  have hαu : α u = u := by
    have h1 := kbarAct_apply_mk hKH ⟨w, hwH⟩ u
    rw [hu_mk, hfix] at h1
    have hz : u⁻¹ * α u ∈ center (modTwoCore (kSub p M H)) := QuotientGroup.eq.1 (hu_mk.trans h1)
    have hcz : Commute u (u⁻¹ * α u) := mem_center_iff.1 hz u
    have hz2 : (u⁻¹ * α u) ^ 2 = 1 := by
      have h2 : (u * (u⁻¹ * α u)) ^ 2 = 1 := by
        rw [mul_inv_cancel_left, ← map_pow, hu2, map_one]
      rwa [hcz.mul_pow, hu2, one_mul] at h2
    have hord : orderOf (u⁻¹ * α u) = 1 := by
      have h2 : orderOf (u⁻¹ * α u) ∣ 2 := orderOf_dvd_of_pow_eq_one hz2
      have hm : orderOf (u⁻¹ * α u) ∣ 2 * j + 1 := hj ▸ Subgroup.orderOf_dvd_natCard _ hz
      exact Nat.Coprime.eq_one_of_dvd
        (Nat.Coprime.coprime_dvd_left h2 (Nat.coprime_two_left.2 ⟨j, rfl⟩)) hm
    rw [orderOf_eq_one_iff] at hord
    exact (inv_mul_eq_one.1 hord).symm
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective u
  have hwN : w ∈ normalizer (kSub p M H : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (Section14.kSub_le p M H)).mp hKH hwH
  set β : MulAut ↥(kSub p M H) := (kSub p M H).normalizerMonoidHom ⟨w, hwN⟩ with hβ
  have hαβ : ∀ k : ↥(kSub p M H), α (QuotientGroup.mk k) = QuotientGroup.mk (β k) := by
    intro k
    rw [hα, kbarConj_mk]
    rfl
  have hnβ : n⁻¹ * β n ∈ CFSG.pCore 2 ↥(kSub p M H) := by
    have h := hαu
    rw [← hn, hαβ] at h
    exact QuotientGroup.eq.1 h.symm
  have hPβ : ∀ x ∈ CFSG.pCore 2 ↥(kSub p M H), β x ∈ CFSG.pCore 2 ↥(kSub p M H) := by
    intro x hx
    have hchar : (CFSG.pCore 2 ↥(kSub p M H)).map β.toMonoidHom =
        CFSG.pCore 2 ↥(kSub p M H) :=
      Subgroup.characteristic_iff_map_eq.mp inferInstance β
    rw [← hchar]
    exact ⟨x, hx, rfl⟩
  have hcop : Nat.Coprime (orderOf β) (Nat.card (CFSG.pCore 2 ↥(kSub p M H))) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(kSub p M H))).exists_card_eq
    rw [ha]
    have hβ3 : orderOf β ∣ 3 := by
      rw [← hw, ← Subgroup.orderOf_mk w hwN]
      exact orderOf_map_dvd _ _
    exact Nat.Coprime.coprime_dvd_left hβ3 (Nat.Coprime.pow_right a (by norm_num))
  obtain ⟨x, hx, hfixβ⟩ :=
    CFSG.GroupTheory.exists_fixed_mem_coset_of_coprime_mulAut _ β hPβ hnβ hcop
  refine ⟨n * x, congrArg Subtype.val hfixβ, ?_⟩
  have h1 : (QuotientGroup.mk (n * x) : modTwoCore (kSub p M H)) = u := by
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff x).2 hx, mul_one, hn]
  rw [h1, hu_mk]

end KbarExcl

open KbarExcl in
theorem twelveSixKbarExclusion_holds : TwelveSixKbarExclusion := by
  intro G _ _ M p Q H d L₁ L₂ L₃ n₁ n₂ n₃ hyp hK hY
  obtain ⟨hc, ⟨D⟩, -, -, -, -, hKH⟩ := hyp
  have : Finite (MulAut (kbarQuot p M H)) := MulEquiv.finite_left
  set ψ := kbarAct hKH
  have hkerX := ker_kbarAct_le hc.ctx hKH hK
  have hXker := xSub_le_ker_kbarAct hc.ctx hKH hK
  have hIH : D.I₁ ⊔ D.I₂ ⊔ D.I₃ ≤ H := (D.sup_le hc.data).trans inf_le_left
  have hI₁H : D.I₁ ≤ H := le_sup_left.trans (le_sup_left.trans hIH)
  have hI₂H : D.I₂ ≤ H := le_sup_right.trans (le_sup_left.trans hIH)
  have hI₃H : D.I₃ ≤ H := le_sup_right.trans hIH
  have hVH : D.V ≤ H := D.V_le.trans hIH
  have hW₁H : D.W₁ ≤ H := D.le₁.trans hI₁H
  have hW₂H : D.W₂ ≤ H := D.le₂.trans hI₂H
  have hW₃H : D.W₃ ≤ H := D.le₃.trans hI₃H
  have ht₁ := D.t₁_mem hc.data
  have ht₂ := D.t₂_mem hc.data
  have ht₃ := D.t₃_mem hc.data
  have hVX := hc.inf_xSub_eq_bot D.cfg (D.centralizer_le₁ hc) (D.centralizer_le₂ hc)
    (D.centralizer_le₃ hc) ht₁ ht₂ ht₃
  have hinjV : ∀ v ∈ D.V.subgroupOf H, ψ v = 1 → v = 1 := by
    intro v hv hv1
    have hvX := hkerX (MonoidHom.mem_ker.2 hv1)
    rw [mem_subgroupOf] at hv hvX
    have hvVX : (v : G) ∈ D.V ⊓ xSub p M H := ⟨hv, hvX⟩
    rw [hVX, mem_bot] at hvVX
    exact Subtype.ext hvVX
  have hcK := KbarE27.isE27InvConfig_map
    (KbarE27.isE27InvConfig_subgroupOf D.cfg hVH ht₁.1 ht₂.1 ht₃.1) ψ hinjV
  set J := ((D.I₁ ⊔ D.I₂ ⊔ D.I₃).subgroupOf H).map ψ with hJ
  have hVJ : (D.V.subgroupOf H).map ψ ≤ J := map_mono fun x hx => D.V_le hx
  have h5 : ¬ 5 ∣ Nat.card J := by
    have hne := TwelveFiveData.pairwise_ne hc.data hc.hcard
    have hcomm : ∀ {I I' L L' : Subgroup G}, L ∈ weakBlockSet M H → L' ∈ weakBlockSet M H →
        L ≠ L' → I ≤ H ⊓ L → I' ≤ H ⊓ L' → ∀ a ∈ (I.subgroupOf H).map ψ,
          ∀ b ∈ (I'.subgroupOf H).map ψ, a * b = b * a := by
      intro I I' L L' hL hL' hLL' hI hI' a ha b hb
      obtain ⟨a, ha, rfl⟩ := ha
      obtain ⟨b, hb, rfl⟩ := hb
      have hab : ⁅a, b⁆ ∈ (xSub p M H).subgroupOf H := by
        rw [mem_subgroupOf]
        have := hc.commutator_le_xSub hL hL' hLL' hI hI' (commutator_mem_commutator ha hb)
        simpa [commutatorElement_def] using this
      have h1 : ψ ⁅a, b⁆ = 1 := hXker hab
      rw [map_commutatorElement] at h1
      exact commutatorElement_eq_one_iff_mul_comm.1 h1
    have hcard : ∀ {I : Subgroup G} {n : ℕ}, I ≤ H → Odd n →
        IsPSLType 2 (GaloisField 2 n) (modTwoCore I) →
          ¬ 5 ∣ Nat.card ((I.subgroupOf H).map ψ) := by
      intro I n hIH hn hI h
      apply not_five_dvd_card_of_isPSLType hn hI
      have h1 := h.trans (card_map_dvd (I.subgroupOf H) ψ)
      rwa [Nat.card_congr (subgroupOfEquivOfLe hIH).toEquiv] at h1
    have hsup : ∀ A B : Subgroup (MulAut (kbarQuot p M H)),
        (∀ a ∈ A, ∀ b ∈ B, a * b = b * a) → ¬ 5 ∣ Nat.card A → ¬ 5 ∣ Nat.card B →
          ¬ 5 ∣ Nat.card (A ⊔ B : Subgroup _) := by
      intro A B hAB hA hB h
      have hmul := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hAB).1
      have h' : 5 ∣ Nat.card A * Nat.card B := hmul ▸ dvd_mul_of_dvd_left h _
      rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 5)).1 h' with h'' | h''
      exacts [hA h'', hB h'']
    have hJA : J = (D.I₁.subgroupOf H).map ψ ⊔ (D.I₂.subgroupOf H).map ψ ⊔
        (D.I₃.subgroupOf H).map ψ := by
      rw [hJ, subgroupOf_sup (sup_le hI₁H hI₂H) hI₃H, subgroupOf_sup hI₁H hI₂H,
        Subgroup.map_sup, Subgroup.map_sup]
    have h₁₃ := hcomm hc.data.mem₁ hc.data.mem₃ hne.2.1 D.le_inf₁ D.le_inf₃
    have h₂₃ := hcomm hc.data.mem₂ hc.data.mem₃ hne.2.2 D.le_inf₂ D.le_inf₃
    have hle : (D.I₁.subgroupOf H).map ψ ⊔ (D.I₂.subgroupOf H).map ψ ≤
        centralizer (((D.I₃.subgroupOf H).map ψ : Subgroup _) : Set _) := by
      refine sup_le (fun x hx => ?_) (fun x hx => ?_) <;> rw [mem_centralizer_iff] <;>
        intro y hy
      · exact (h₁₃ x hx y hy).symm
      · exact (h₂₃ x hx y hy).symm
    rw [hJA]
    refine hsup _ _ (fun a ha b hb => (mem_centralizer_iff.1 (hle ha) b hb).symm)
      (hsup _ _ (hcomm hc.data.mem₁ hc.data.mem₂ hne.1 D.le_inf₁ D.le_inf₂)
        (hcard hI₁H hc.data.odd₁ D.type₁) (hcard hI₂H hc.data.odd₂ D.type₂))
      (hcard hI₃H hc.data.odd₃ D.type₃)
  have hN : ∀ W : Subgroup G, W ≤ H → Nat.card W = 3 → centralizer (W : Set G) ≤ M →
      ∀ y : kbarQuot p M H, y ^ 2 = 1 → (∀ w ∈ (W.subgroupOf H).map ψ, w y = y) →
        MulAut.conj y ∈ normalizer (J : Set (MulAut (kbarQuot p M H))) := by
    intro W hWH hW3 hCW y hy2 hfix
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨w₀, hw₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥W) 3 (by simp [hW3])
    have hw3 : orderOf (w₀ : G) = 3 := (Subgroup.orderOf_coe w₀).trans hw₀
    have hWz : W = zpowers (w₀ : G) := by
      refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 w₀.2) ?_).symm
      rw [hW3, Nat.card_zpowers, hw3]
    have hwH : (w₀ : G) ∈ H := hWH w₀.2
    obtain ⟨c, hcw, rfl⟩ := exists_lift hKH hwH hw3 hy2 (hfix _ ⟨⟨w₀, hwH⟩, w₀.2, rfl⟩)
    have hcH : (c : G) ∈ H := Section14.kSub_le p M H c.2
    have hwc : Commute (w₀ : G) c := by
      calc (w₀ : G) * c = ((w₀ : G) * c * (w₀ : G)⁻¹) * w₀ := by group
        _ = c * w₀ := by rw [hcw]
    have hcC : (c : G) ∈ centralizer (W : Set G) := by
      rw [mem_centralizer_iff]
      intro g hg
      rw [hWz] at hg
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hg
      exact (hwc.zpow_left k).eq
    have hcN := D.le_normalizer hc.data ⟨hcH, hCW hcC⟩
    rw [← kbarAct_eq_conj hKH c hcH]
    exact le_normalizer_map ψ ⟨⟨c, hcH⟩, le_normalizer_comap H.subtype hcN, rfl⟩
  have hN₁ := hN D.W₁ hW₁H D.cfg.card₁ (D.centralizer_le₁ hc)
  have hN₂ := hN D.W₂ hW₂H D.cfg.card₂ (D.centralizer_le₂ hc)
  have hN₃ := hN D.W₃ hW₃H D.cfg.card₃ (D.centralizer_le₃ hc)
  rcases hY with hSp | hA | hA
  · exact h5 (KbarE27.five_dvd_card_sp6
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hSp)
      hcK hVJ hN₁ hN₂ hN₃)
  · obtain ⟨e⟩ := hA
    exact h5 (KbarE27.five_dvd_card_alt KbarE27.altE27Facts_ten (by norm_num) (by norm_num) e
      hcK hVJ hN₁ hN₂ hN₃)
  · obtain ⟨e⟩ := hA
    exact h5 (KbarE27.five_dvd_card_alt KbarE27.altE27Facts_eleven (by norm_num) (by norm_num) e
      hcK hVJ hN₁ hN₂ hN₃)

end CFSG.LocalAnalysis.AGL81TheoremCD.Section12
