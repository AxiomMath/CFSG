module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1S74Defs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1PU2
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreGamma
public import CFSG.RankThree.OddKernel.FixedPlaneKernel

public section

namespace CFSG.ComponentClassification.HarrisLit.T1.S74.L38

open CFSG Subgroup CFSG.OddStandard.Solomon75 CFSG.OddStandard.Solomon75.CoreAux

theorem mem_normalizer_of_conj_mem {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (h1 : ∀ x ∈ H, g * x * g⁻¹ ∈ H) (h2 : ∀ x ∈ H, g⁻¹ * x * g ∈ H) :
    g ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro x
  refine ⟨h1 x, fun hx => ?_⟩
  have := h2 _ hx
  rwa [show g⁻¹ * (g * x * g⁻¹) * g = x by group] at this

section Quotient

variable {Cb : Type} [Group Cb] [Finite Cb]

omit [Finite Cb] in
theorem mem_of_orderOf_eq_two_of_odd_index {Lb : Subgroup Cb} [Lb.Normal]
    (hLi : ¬ 2 ∣ Lb.index) {s : Cb} (hs : orderOf s = 2) : s ∈ Lb := by
  have h1 : orderOf (QuotientGroup.mk s : Cb ⧸ Lb) ∣ 2 :=
    hs ▸ orderOf_map_dvd (QuotientGroup.mk' Lb) s
  have h2 : orderOf (QuotientGroup.mk s : Cb ⧸ Lb) ∣ Lb.index := orderOf_dvd_natCard _
  rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
  · rwa [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h
  · exact absurd (h ▸ h2) hLi

theorem pPrimeCore_centralizer_eq_bot_of_cover {p f : ℕ} (h5 : 5 ≤ p ^ f) {Lb : Subgroup Cb}
    (hLn : Lb.Normal) (hLi : ¬ 2 ∣ Lb.index) (hL : IsCoverOf .POmegaOdd 3 p f 2 ↥Lb)
    (hCL : centralizer (Lb : Set Cb) ≤ Lb) {s : Cb} (hs : orderOf s = 2) :
    pPrimeCore 2 ↥(centralizer ({s} : Set Cb)) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsL : s ∈ Lb := mem_of_orderOf_eq_two_of_odd_index hLi hs
  have hYodd : Odd (Nat.card (oddCoreOf (cen s))) := odd_card_oddCoreOf _
  have hYs : ∀ y ∈ oddCoreOf (cen s), y * s = s * y := fun y hy =>
    mem_centralizer_singleton_iff.mp (oddCoreOf_le _ hy)
  have hYD : ∀ d ∈ cen s, ∀ y ∈ oddCoreOf (cen s), d * y * d⁻¹ ∈ oddCoreOf (cen s) :=
    fun d hd y hy => (mem_normalizer_iff.mp (le_normalizer_oddCoreOf _ hd) y).mp hy
  set s' : ↥Lb := ⟨s, hsL⟩ with hs'def
  have hs' : orderOf s' = 2 := by rw [Subgroup.orderOf_mk]; exact hs
  set Y₀ : Subgroup ↥Lb := (oddCoreOf (cen s)).comap Lb.subtype with hY₀
  have hY₀odd : Odd (Nat.card Y₀) := by
    have hle : Y₀.map Lb.subtype ≤ oddCoreOf (cen s) := map_comap_le _ _
    rw [← card_map_of_injective Lb.subtype_injective]
    exact hYodd.of_dvd_nat (card_dvd_of_le hle)
  have hY₀C : Y₀ ≤ cen s' := fun y hy =>
    mem_centralizer_singleton_iff.mpr (Subtype.ext (hYs _ hy))
  have hY₀N : cen s' ≤ normalizer (Y₀ : Set ↥Lb) := by
    intro c hc
    have hc' : (c : Cb) ∈ cen s :=
      mem_centralizer_singleton_iff.mpr (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hc))
    refine mem_normalizer_of_conj_mem (fun y hy => ?_) (fun y hy => ?_)
    · exact hYD _ hc' _ hy
    · have := hYD _ (inv_mem hc') _ hy
      rwa [inv_inv] at this
  have hY₀ : Y₀ = ⊥ := by
    by_cases hZ : s' ∈ center ↥Lb
    ·
      have hN : Y₀.Normal := by
        refine normalizer_eq_top_iff.mp (eq_top_iff.mpr fun l _ => hY₀N ?_)
        exact mem_centralizer_singleton_iff.mpr (mem_center_iff.mp hZ l)
      have h2L : 2 ∣ Nat.card ↥Lb := hs' ▸ orderOf_dvd_natCard s'
      rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hL.1 Y₀ with h | h
      · have hdvd : Nat.card Y₀ ∣ 2 := hL.2.1 ▸ card_dvd_of_le h
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
        · exact card_eq_one.mp h1
        · rw [h1] at hY₀odd
          exact absurd hY₀odd (by decide)
      · rw [h, card_top] at hY₀odd
        exact absurd h2L (Nat.not_even_iff_odd.mpr hY₀odd ∘ even_iff_two_dvd.mpr)
    · have h := le_oddCoreOf_of_normalized hY₀C hY₀N hY₀odd
      rw [oddCoreOf, pPrimeCore_centralizer_of_isCoverOf h5 hL hs' hZ, Subgroup.map_bot] at h
      exact eq_bot_iff.mpr h
  have hYL : ∀ y ∈ oddCoreOf (cen s), y ∈ Lb → y = 1 := by
    intro y hy hyL
    have h : (⟨y, hyL⟩ : ↥Lb) ∈ Y₀ := hy
    rw [hY₀] at h
    exact congrArg Subtype.val (mem_bot.mp h)
  have hYC : ∀ y ∈ oddCoreOf (cen s), ∀ c ∈ Lb, c ∈ cen s → y * c = c * y := by
    intro y hy c hcL hc
    have hk : y * c * y⁻¹ * c⁻¹ = 1 := by
      refine hYL _ ?_ ?_
      · rw [show y * c * y⁻¹ * c⁻¹ = y * (c * y⁻¹ * c⁻¹) by group]
        exact mul_mem hy (hYD c hc _ (inv_mem hy))
      · exact mul_mem (hLn.conj_mem c hcL y) (inv_mem hcL)
    calc y * c = y * c * y⁻¹ * c⁻¹ * (c * y) := by group
      _ = c * y := by rw [hk, one_mul]
  have hYcen : ∀ y ∈ oddCoreOf (cen s), ∀ l ∈ Lb, y * l = l * y := by
    intro y hy l hl
    by_cases hZ : s' ∈ center ↥Lb
    · refine hYC y hy l hl (mem_centralizer_singleton_iff.mpr ?_)
      exact congrArg Subtype.val (mem_center_iff.mp hZ ⟨l, hl⟩)
    have := hLn
    have hα : ∀ J : Subgroup ↥Lb, IsTwoComponentIn J (centralizer {s'}) →
        ∀ j ∈ J, MulAut.conjNormal y j = j := by
      intro J hJ j hj
      apply Subtype.ext
      rw [MulAut.conjNormal_apply]
      have hjs : (j : Cb) ∈ cen s := mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (mem_centralizer_singleton_iff.mp (hJ.1 hj)))
      rw [hYC y hy j j.2 hjs, mul_inv_cancel_right]
    rcases eq_one_or_eq_conj_of_fix h5 hL hs' hZ hα with h1 | h1
    · have h := congrArg (fun φ : MulAut ↥Lb => (φ ⟨l, hl⟩ : Cb)) h1
      simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h
      calc y * l = y * l * y⁻¹ * y := by group
        _ = l * y := by rw [h]
    · exfalso
      apply hZ
      have hodd : Odd (orderOf y) := by
        have h := orderOf_dvd_natCard (⟨y, hy⟩ : ↥(oddCoreOf (cen s)))
        rw [Subgroup.orderOf_mk] at h
        exact hYodd.of_dvd_nat h
      obtain ⟨k, hk⟩ := hodd
      have hpow : (MulAut.conj s') ^ orderOf y = 1 := by
        rw [← h1, ← map_pow, pow_orderOf_eq_one, map_one]
      have hs'2 : s' ^ 2 = 1 := by rw [← hs']; exact pow_orderOf_eq_one s'
      have hsk : s' ^ orderOf y = s' := by
        rw [hk, pow_succ, pow_mul, hs'2, one_pow, one_mul]
      rw [← map_pow, hsk] at hpow
      rw [mem_center_iff]
      intro g
      have h := congrArg (fun φ : MulAut ↥Lb => φ g) hpow
      simp only [MulAut.conj_apply, MulAut.one_apply] at h
      calc g * s' = s' * g * s'⁻¹ * s' := by rw [h]
        _ = s' * g := by group
  have hY : oddCoreOf (cen s) = ⊥ := by
    refine eq_bot_iff.mpr fun y hy => mem_bot.mpr (hYL y hy (hCL ?_))
    exact mem_centralizer_iff.mpr fun l hl => (hYcen y hy l hl).symm
  exact (map_eq_bot_iff_of_injective _ (cen s).subtype_injective).mp hY

end Quotient

section Balance

variable {G : Type} [Group G] [Finite G]

theorem oddCoreOf_inf_cen_le {z : G} {p f : ℕ} (h5 : 5 ≤ p ^ f) {Lb : Subgroup (CentQuot z)}
    (hLn : Lb.Normal) (hLi : ¬ 2 ∣ Lb.index) (hL : IsCoverOf .POmegaOdd 3 p f 2 ↥Lb)
    (hCL : centralizer (Lb : Set (CentQuot z)) ≤ Lb) {x : G} (hx : orderOf x = 2)
    (hxz : x * z = z * x) : oddCoreOf (cen x) ⊓ cen z ≤ oddCoreOf (cen z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxH : x ∈ cen z := mem_centralizer_singleton_iff.mpr hxz
  set π : ↥(cen z) →* CentQuot z := QuotientGroup.mk' (pPrimeCore 2 ↥(cen z)) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker = pPrimeCore 2 ↥(cen z) := QuotientGroup.ker_mk' _
  have hkodd : ¬ 2 ∣ Nat.card π.ker := by
    rw [hker]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
  set x₀ : ↥(cen z) := ⟨x, hxH⟩ with hx₀def
  have hx₀ : orderOf x₀ = 2 := by rw [Subgroup.orderOf_mk]; exact hx
  have hxb : orderOf (π x₀) = 2 := by
    have h1 : orderOf (π x₀) ∣ 2 := by
      have h := orderOf_map_dvd π x₀
      rwa [hx₀] at h
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exfalso
      rw [orderOf_eq_one_iff, ← MonoidHom.mem_ker, hker] at h
      have h1 := eq_one_of_mem_pPrimeCore_of_two_pow h ⟨1, by rw [hx₀, pow_one]⟩
      rw [h1, orderOf_one] at hx₀
      exact absurd hx₀ (by decide)
    · exact h
  have hcore := pPrimeCore_centralizer_eq_bot_of_cover h5 hLn hLi hL hCL hxb
  set E : Subgroup (CentQuot z) := ((oddCoreOf (cen x) ⊓ cen z).subgroupOf (cen z)).map π
    with hEdef
  have hEC : E ≤ cen (π x₀) := by
    rintro _ ⟨d, hd, rfl⟩
    have hdx : (d : G) * x = x * d := mem_centralizer_singleton_iff.mp (oddCoreOf_le _ hd.1)
    have hdx₀ : d * x₀ = x₀ * d := Subtype.ext hdx
    rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hdx₀]
  have hEodd : Odd (Nat.card E) := by
    refine (odd_card_oddCoreOf (cen x)).of_dvd_nat ((card_map_dvd _ _).trans ?_)
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_right :
      oddCoreOf (cen x) ⊓ cen z ≤ cen z)).toEquiv]
    exact card_dvd_of_le inf_le_left
  have hconj : ∀ h₀ : ↥(cen z), h₀ ∈ centralizer {x₀} →
      ∀ e ∈ E, π h₀ * e * (π h₀)⁻¹ ∈ E := by
    rintro h₀ hh₀ _ ⟨d, hd, rfl⟩
    refine ⟨h₀ * d * h₀⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
    have hhx : (h₀ : G) ∈ cen x := mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (mem_centralizer_singleton_iff.mp hh₀))
    refine ⟨?_, (h₀ * d * h₀⁻¹).2⟩
    exact (mem_normalizer_iff.mp (le_normalizer_oddCoreOf _ hhx) _).mp hd.1
  have hEN : cen (π x₀) ≤ normalizer (E : Set (CentQuot z)) := by
    intro c hc
    have hc' : c ∈ (centralizer ({x₀} : Set ↥(cen z))).map π := by
      rw [CFSG.RankThree.OddKernel.map_centralizer_eq_of_odd π hπs hkodd hx₀]
      exact hc
    obtain ⟨h₀, hh₀, rfl⟩ := hc'
    refine mem_normalizer_of_conj_mem (hconj h₀ hh₀) fun e he => ?_
    have := hconj h₀⁻¹ (inv_mem hh₀) e he
    rwa [map_inv, inv_inv] at this
  have hE : E = ⊥ := by
    have h := le_oddCoreOf_of_normalized hEC hEN hEodd
    rw [oddCoreOf, hcore, Subgroup.map_bot] at h
    exact eq_bot_iff.mpr h
  intro d hd
  have hmem : (⟨d, hd.2⟩ : ↥(cen z)) ∈ pPrimeCore 2 ↥(cen z) := by
    rw [← hker, MonoidHom.mem_ker]
    have h1 : π ⟨d, hd.2⟩ ∈ E := ⟨⟨d, hd.2⟩, hd, rfl⟩
    rw [hE] at h1
    exact mem_bot.mp h1
  exact ⟨⟨d, hd.2⟩, hmem, rfl⟩

theorem oddCoreBalanced_of_hyp {z : G} {p f : ℕ} (h : Hyp31i G z p f) : OddCoreBalanced G := by
  obtain ⟨Lb, hLn, hLi, hL, hCL⟩ := h.spin
  intro x y hx hy hxy _
  obtain ⟨g, hg⟩ := h.oneClass y hy
  have hx' : orderOf (g⁻¹ * x * g) = 2 := by
    have := orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective x
    simpa [MulAut.conj_apply, hx] using this
  have hx'z : g⁻¹ * x * g * z = z * (g⁻¹ * x * g) := by
    calc g⁻¹ * x * g * z = g⁻¹ * (x * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (y * x) * g := by rw [hg, hxy]
      _ = z * (g⁻¹ * x * g) := by rw [← hg]; group
  have key := balance_conj g (oddCoreOf_inf_cen_le h.h5 hLn hLi hL hCL hx' hx'z)
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group, hg] at key

end Balance

end CFSG.ComponentClassification.HarrisLit.T1.S74.L38
