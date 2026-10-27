module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32A
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxL32B
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxFiveQ
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSmallH

public section

namespace CFSG.ComponentClassification.SolMax.L32

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem false_of_exceptional_pump (hPump : Sol78.AlternatingPumpUpInput)
    (hN1 : TwoGroupAltCoverExclusion) [Finite X] [IsSimpleGroup X]
    (hnab : ∃ a b : X, a * b ≠ b * a) (hKP : Assembly.KProper Blueprint.Catalog X)
    (hunb : ∃ z : X, orderOf z = 2 ∧ oddCore (centralizer ({z} : Set X)) ≠ ⊥)
    (hnU : ¬ OutcomeLocal.UOutcome X) {t : X} {J : Subgroup X} {n : ℕ}
    (hpair : Sol78.IsSolomonPair t J n) {θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)}
    {ρJ : ↥(normalizer (J : Set X)) →* Perm (Fin n)} (hρJ : IsPermAction θ ρJ) {c e₀ : X}
    (he₀ : e₀ ∈ J) (hc : orderOf c = 2) (htc : t * c = c * t)
    (hcN : c ∈ normalizer (J : Set X)) (hce : c * e₀⁻¹ ∈ UnbalancedLayer.coreActionKernel J)
    (hs4 : (coreImage θ he₀).support.card = 4) {Jc : Subgroup X}
    (hJcJ : Jc ≤ J ⊓ centralizer ({c} : Set X))
    (hJcpc : IsPComponent 2
      (Jc.subgroupOf (centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X))))
    (hinv : ∀ (x : X) (hx : x ∈ J), x * c = c * x → (∃ k : ℕ, x ^ 2 ^ k = 1) →
      (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ → x ∈ Jc)
    (hsubP : ∀ x ∈ Jc, ∃ hx : x ∈ J, (coreImage θ hx).support ⊆ (coreImage θ he₀).supportᶜ)
    (χ : ↥Jc ⧸ pPrimeCore 2 ↥Jc ≃*
      alternatingGroup ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)))
    (hχ : ∀ (x : ↥Jc) (hx : (x : X) ∈ J),
      Perm.ofSubtype ((χ (x : ↥Jc ⧸ pPrimeCore 2 ↥Jc) : alternatingGroup _) :
        Perm ↥((coreImage θ he₀).supportᶜ : Finset (Fin n))) = coreImage θ hx)
    {M : Subgroup X} (hMC : M ≤ centralizer ({c} : Set X))
    (hMpc : IsPComponent 2 (M.subgroupOf (centralizer ({c} : Set X)))) (hJcM : Jc ≤ M)
    (htM : t ∈ normalizer (M : Set X)) {p : ℕ} (hp : p.Prime) (hpn : n < p)
    (hpM : p ∣ Nat.card (↥M ⧸ pPrimeCore 2 ↥M))
    (hpHe : n = 9 → ¬ p ∣ Nat.card Blueprint.NativeSporadic.He)
    (hE1 : ∀ w ∈ M, w * t = t * w → w ∈ UnbalancedLayer.coreActionKernel Jc → Odd (orderOf w))
    (hE2 : ∀ (y : X) (hy : y ∈ normalizer (M : Set X)), y * t = t * y →
      y ∈ UnbalancedLayer.coreActionKernel Jc →
      Odd (orderOf (TBLit.oddQuotAction M ⟨y, hy⟩)) ∨
        Odd (orderOf (TBLit.oddQuotAction M ⟨y * t, mul_mem hy htM⟩)))
    (hE3 : ∃ h ∈ M, h * t = t * h ∧ ∃ (hhJ : h ∈ normalizer (J : Set X)) (σD σF : Perm (Fin n)),
      ρJ ⟨h, hhJ⟩ = σD * σF ∧ (∀ v ∉ (coreImage θ he₀).support, σD v = v) ∧
      (∀ v ∈ (coreImage θ he₀).support, σF v = v) ∧ Perm.sign σF = -1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨h, hhM, hht, hhJ, σD, σF, hsplit, hσD, hσF, hsF⟩ := hE3
  have hn9 : 9 ≤ n := hpair.2.2.1
  have ht2 : t * t = 1 := by rw [← sq, ← hpair.1.1, pow_orderOf_eq_one]
  have hc2 : c * c = 1 := by rw [← sq, ← hc, pow_orderOf_eq_one]
  have hJC : J ≤ centralizer ({t} : Set X) := hpair.1.2.1
  have hJcJ' : Jc ≤ J := hJcJ.trans inf_le_left
  have hJcC : Jc ≤ centralizer ({t} : Set X) ⊓ centralizer ({c} : Set X) :=
    le_inf (hJcJ'.trans hJC) (hJcJ.trans inf_le_right)
  have hres := primeResidual_eq_top_of_isPComponent hJcC hJcpc
  have hJcperf : ⁅Jc, Jc⁆ = Jc := UnbalancedCorr.commutator_eq_of_isPComponent hJcC hJcpc
  have hcardF : Fintype.card ↥((coreImage θ he₀).supportᶜ : Finset (Fin n)) = n - 4 := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hs4]
  have hJcq : Nontrivial (↥Jc ⧸ pPrimeCore 2 ↥Jc) := by
    have : Nontrivial (alternatingGroup (Fin (n - 4))) :=
      alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
    exact (χ.trans (Fintype.equivFinOfCardEq hcardF).altCongrHom).toEquiv.nontrivial
  have hρJc : ρJ ⟨c, hcN⟩ = coreImage θ he₀ :=
    hρJ.apply_eq_coreImage_of_acts (by omega) hcN he₀ hce
  have hσ2 : coreImage θ he₀ * coreImage θ he₀ = 1 := by
    rw [← hρJc, ← map_mul]
    convert map_one ρJ
    exact Subtype.ext hc2
  have htKJ : t ∈ UnbalancedLayer.coreActionKernel J := mem_cak_of_forall_commute
    fun z hz => (mem_centralizer_singleton_iff.mp (hJC hz)).symm
  have hρJt : ρJ ⟨t, htKJ.1⟩ = 1 := hρJ.eq_one_of_mem_coreActionKernel (by omega) htKJ
  have hhc : h * c = c * h := mem_centralizer_singleton_iff.mp (hMC hhM)
  set π := ρJ ⟨h, hhJ⟩ with hπdef
  have hπc : π * coreImage θ he₀ = coreImage θ he₀ * π := by
    rw [← hρJc, hπdef, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hhc
  have hlift : ∀ b : alternatingGroup (Fin n),
      (b : Perm (Fin n)) * coreImage θ he₀ = coreImage θ he₀ * b →
      ∃ x : X, x ∈ J ∧ x * c = c * x ∧ ∃ hxJ : x ∈ normalizer (J : Set X),
        ρJ ⟨x, hxJ⟩ = b := by
    intro b hb
    obtain ⟨x, hxc, hxb⟩ := hρJ.exists_lift hcN hc2 (b := b) (by rw [hρJc]; exact hb)
    refine ⟨x, x.2, mem_centralizer_singleton_iff.mp hxc, le_normalizer x.2, ?_⟩
    rw [hρJ.apply_of_mem (by omega) x, hxb]
  have hnormM : ∀ (w : X) (hwN : w ∈ normalizer (J : Set X)), w * c = c * w →
      (ρJ ⟨w, hwN⟩).support ⊆ (coreImage θ he₀).support →
      w ∈ normalizer (M : Set X) ∧ w ∈ UnbalancedLayer.coreActionKernel Jc := by
    intro w hwN hwc hwD
    obtain ⟨hwJc, hwK⟩ :=
      mem_coreActionKernel_of_support_subset hρJ he₀ hJcJ hres hinv hsubP χ hχ hwN hwc hwD
    exact ⟨mem_normalizer_of_mem_normalizer_Jc hMC hMpc hJcM hJcperf hJcq
      (mem_centralizer_singleton_iff.mpr hwc) hwJc, hwK⟩
  have hstepA : ∀ (α : X), orderOf α = 2 → α * c = c * α → α * t = t * α →
      ∀ hαJ : α ∈ normalizer (J : Set X), (ρJ ⟨α, hαJ⟩).support.card ≤ 2 →
        (ρJ ⟨α, hαJ⟩).support ⊆ (coreImage θ he₀).support →
          α ∈ UnbalancedLayer.coreActionKernel M → False :=
    fun α hαo hαc hαt hαJ hα2 hαD hαM => false_of_trivial_pump hPump hN1 hnab hKP hunb hnU
      hpair hρJ he₀ hc hs4 hJcJ hJcpc hinv hsubP χ hχ hMC hMpc hJcM hp hpn hpM hpHe hαo hαc hαt
      hαJ hα2 hαD hαM
  by_cases hsD : Perm.sign σD = 1
  ·
    have hπodd : Perm.sign π = -1 := by rw [hsplit, Perm.sign_mul, hsD, hsF, one_mul]
    obtain ⟨d₁, hd₁⟩ : (coreImage θ he₀).support.Nonempty := by
      rw [← Finset.card_pos, hs4]
      norm_num
    have hd₁ne : d₁ ≠ (coreImage θ he₀) d₁ := fun h => (Perm.mem_support.mp hd₁) h.symm
    set δ : Perm (Fin n) := swap d₁ ((coreImage θ he₀) d₁) with hδdef
    have hδsupp : δ.support ⊆ (coreImage θ he₀).support := by
      rw [hδdef, Perm.support_swap hd₁ne]
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with h | h
      · rw [h]
        exact hd₁
      · rw [h]
        exact Perm.apply_mem_support.mpr hd₁
    have hδcard : δ.support.card = 2 := Perm.card_support_swap hd₁ne
    have hδsign : Perm.sign δ = -1 := Perm.sign_swap hd₁ne
    have hδ2 : δ * δ = 1 := swap_mul_self _ _
    have hδ1 : δ ≠ 1 := fun h => by
      rw [h, Perm.support_one, Finset.card_empty] at hδcard
      omega
    have hδσ : δ * coreImage θ he₀ = coreImage θ he₀ * δ := swap_apply_commute hσ2 d₁
    have hwA : π⁻¹ * δ ∈ alternatingGroup (Fin n) := by
      rw [Perm.mem_alternatingGroup, Perm.sign_mul, Perm.sign_inv, hπodd, hδsign]
      rfl
    have hπinv : π⁻¹ * coreImage θ he₀ = coreImage θ he₀ * π⁻¹ := by
      rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hπc, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨x, hxJ, hxc, hxN, hρx⟩ := hlift ⟨π⁻¹ * δ, hwA⟩ (by
      change π⁻¹ * δ * coreImage θ he₀ = coreImage θ he₀ * (π⁻¹ * δ)
      rw [mul_assoc, hδσ, ← mul_assoc, hπinv, mul_assoc])
    have hyJ : h * x ∈ normalizer (J : Set X) := mul_mem hhJ hxN
    have hρy : ρJ ⟨h * x, hyJ⟩ = δ := by
      have h1 : (⟨h * x, hyJ⟩ : ↥(normalizer (J : Set X))) = ⟨h, hhJ⟩ * ⟨x, hxN⟩ := rfl
      rw [h1, map_mul, ← hπdef, hρx]
      change π * (π⁻¹ * δ) = δ
      group
    have hxt : x * t = t * x := mem_centralizer_singleton_iff.mp (hJC hxJ)
    have hyc : h * x * c = c * (h * x) := by rw [mul_assoc, hxc, ← mul_assoc, hhc, mul_assoc]
    have hyt : h * x * t = t * (h * x) := by rw [mul_assoc, hxt, ← mul_assoc, hht, mul_assoc]
    obtain ⟨hyM, hyK⟩ := hnormM (h * x) hyJ hyc (by rw [hρy]; exact hδsupp)
    obtain ⟨y', hy'M, hy'J, hρy', hy'c, hy't, hy'odd⟩ : ∃ (y' : X) (hy'M : y' ∈
        normalizer (M : Set X)) (hy'J : y' ∈ normalizer (J : Set X)), ρJ ⟨y', hy'J⟩ = δ ∧
        y' * c = c * y' ∧ y' * t = t * y' ∧ Odd (orderOf (TBLit.oddQuotAction M ⟨y', hy'M⟩)) := by
      rcases hE2 (h * x) hyM hyt hyK with h1 | h1
      · exact ⟨h * x, hyM, hyJ, hρy, hyc, hyt, h1⟩
      · refine ⟨h * x * t, mul_mem hyM htM, mul_mem hyJ htKJ.1, ?_, ?_, ?_, h1⟩
        · have h2 : (⟨h * x * t, mul_mem hyJ htKJ.1⟩ : ↥(normalizer (J : Set X))) =
              ⟨h * x, hyJ⟩ * ⟨t, htKJ.1⟩ := rfl
          rw [h2, map_mul, hρy, hρJt, mul_one]
        · rw [mul_assoc, htc, ← mul_assoc, hyc, mul_assoc]
        · rw [← mul_assoc t, ← hyt]
    obtain ⟨m, hmodd, k, hk⟩ := exists_odd_pow_two_pow y'
    have hβJ : y' ^ m ∈ normalizer (J : Set X) := pow_mem hy'J m
    have hβM : y' ^ m ∈ normalizer (M : Set X) := pow_mem hy'M m
    have hρβ : ρJ ⟨y' ^ m, hβJ⟩ = δ := by
      have h1 : (⟨y' ^ m, hβJ⟩ : ↥(normalizer (J : Set X))) = ⟨y', hy'J⟩ ^ m := rfl
      rw [h1, map_pow, hρy', pow_odd_of_mul_self hδ2 hmodd]
    have hβK : y' ^ m ∈ UnbalancedLayer.coreActionKernel M := by
      rw [mem_coreActionKernel_iff_oddQuotAction hβM]
      set q := TBLit.oddQuotAction M ⟨y', hy'M⟩ with hqdef
      have h1 : TBLit.oddQuotAction M ⟨y' ^ m, hβM⟩ = q ^ m := by
        have h2 : (⟨y' ^ m, hβM⟩ : ↥(normalizer (M : Set X))) = ⟨y', hy'M⟩ ^ m := rfl
        rw [h2, map_pow]
      rw [h1, ← orderOf_eq_one_iff]
      have h3 : orderOf (q ^ m) ∣ orderOf q := orderOf_pow_dvd m
      have h4 : orderOf (q ^ m) ∣ 2 ^ k := by
        rw [← h1, ← hk]
        have h5 := orderOf_map_dvd (TBLit.oddQuotAction M) (⟨y' ^ m, hβM⟩ :
          ↥(normalizer (M : Set X)))
        rwa [Subgroup.orderOf_mk] at h5
      have hcop : Nat.Coprime (orderOf q) (2 ^ k) :=
        (Nat.coprime_two_right.mpr hy'odd).pow_right k
      exact Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd h3 h4)
    have hβc : y' ^ m * c = c * y' ^ m := ((show Commute y' c from hy'c).pow_left m).eq
    have hβt : y' ^ m * t = t * y' ^ m := ((show Commute y' t from hy't).pow_left m).eq
    obtain rfl | rfl | hk2 : k = 0 ∨ k = 1 ∨ 2 ≤ k := by omega
    ·
      apply hδ1
      rw [pow_zero, orderOf_eq_one_iff] at hk
      rw [← hρβ]
      have h1 : (⟨y' ^ m, hβJ⟩ : ↥(normalizer (J : Set X))) = 1 := Subtype.ext hk
      rw [h1, map_one]
    ·
      exact hstepA (y' ^ m) (by rw [hk, pow_one]) hβc hβt hβJ (by rw [hρβ, hδcard])
        (by rw [hρβ]; exact hδsupp) hβK
    ·
      have hkk : 2 ^ k = 2 ^ (k - 1) * 2 := by
        rw [← pow_succ]
        congr 1
        omega
      have hzo : orderOf ((y' ^ m) ^ 2 ^ (k - 1)) = 2 := by
        rw [orderOf_pow_of_dvd (by positivity) (hk ▸ pow_dvd_pow 2 (Nat.sub_le k 1)), hk, hkk,
          Nat.mul_div_cancel_left _ (by positivity)]
      have hzJ : (y' ^ m) ^ 2 ^ (k - 1) ∈ normalizer (J : Set X) := pow_mem hβJ _
      have hρz : ρJ ⟨_, hzJ⟩ = 1 := by
        have h1 : (⟨(y' ^ m) ^ 2 ^ (k - 1), hzJ⟩ : ↥(normalizer (J : Set X))) =
            ⟨y' ^ m, hβJ⟩ ^ 2 ^ (k - 1) := rfl
        rw [h1, map_pow, hρβ]
        obtain ⟨j, hj⟩ : 2 ∣ 2 ^ (k - 1) := dvd_pow_self 2 (by omega)
        rw [hj, pow_mul, sq, hδ2, one_pow]
      exact hstepA _ hzo ((show Commute (y' ^ m) c from hβc).pow_left _).eq
        ((show Commute (y' ^ m) t from hβt).pow_left _).eq hzJ
        (by rw [hρz, Perm.support_one, Finset.card_empty]; omega)
        (by rw [hρz, Perm.support_one]; exact Finset.empty_subset _) (pow_mem hβK _)
  · exact false_of_odd_part hρJ hn9 hJC he₀ hc2 hcN hce hs4 hJcJ hJcpc hinv hsubP χ hχ hMC hMpc
      hJcM hE1 hhM hht hhJ hsplit hσD hσF hsD

end CFSG.ComponentClassification.SolMax.L32
