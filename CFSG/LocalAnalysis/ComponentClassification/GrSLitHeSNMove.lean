module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeSNDouble
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4FieldSq
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS2
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEndS3
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4WInv

public section

namespace CFSG.ComponentClassification.GrSLit.HeSN

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS

variable {X : Type} [Group X] [Finite X]

namespace Setting

variable {a : X} {L W K : Subgroup X} (h : Setting X a L W K)
include h

section Move

variable (e₁ : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)
  (h64 : HeldSylowElementarySixtyFour) (hOut : HeldOuterInvolutionRank) {T : Subgroup X}
  (hT2 : IsPGroup 2 T) (hTM : T ≤ normalizer (W : Set X)) (h1024 : Nat.card ↥(T ⊓ K) = 1024)
include e₁ h64 hOut hT2 hTM h1024

omit h64 hOut h1024 in
theorem doubleHom_facts {c : X} (hcT : c ∈ T) (hKc : conjugate K c ≠ K) :
    ∃ hY : ∀ y ∈ T ⊓ K, ∀ y' ∈ T ⊓ K, Commute y (c⁻¹ * y' * c),
      Function.Injective (doubleHom hY) ∧
      ∀ y : ↥(T ⊓ K), doubleHom hY y ∈ T ⊓ normalizer (K : Set X) := by
  have hY : ∀ y ∈ T ⊓ K, ∀ y' ∈ T ⊓ K, Commute y (c⁻¹ * y' * c) := fun y hy y' hy' =>
    h.commute_conj_one hT2 hTM hy hy' hcT hKc
  refine ⟨hY, doubleHom_injective hY (P := coreActionKernel K)
    (fun y hy => h.conj_mem_coreActionKernel hTM (mem_inf.mp hy).2 hcT hKc)
    (fun y hy hyk => HeDiag.eq_one_of_mem_coreActionKernel e₁ hT2 (mem_inf.mp hy).1
      (mem_inf.mp hy).2 hyk), fun y => ?_⟩
  rw [doubleHom_apply]
  have hyT := (mem_inf.mp y.2).1
  have hyK := (mem_inf.mp y.2).2
  refine mem_inf.mpr ⟨mul_mem hyT (mul_mem (mul_mem (inv_mem hcT) hyT) hcT),
    mul_mem (le_normalizer hyK) ?_⟩
  exact (mem_coreActionKernel.mp (h.conj_mem_coreActionKernel hTM hyK hcT hKc)).1

theorem exists_comm_of_card_four {F : Subgroup X} (hFT : F ≤ T) (hFe : IsElemTwo F)
    (hF8 : Nat.card F = 8) (hF4 : Nat.card ↥(F ⊓ normalizer (K : Set X)) = 4) :
    ∃ B : Subgroup X, B ≤ T ⊓ normalizer (K : Set X) ∧ IsElemTwo B ∧ Nat.card B = 8 ∧
      ∀ x ∈ F, ∀ y ∈ B, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁2 : IsPGroup 2 ↥(T ⊓ normalizer (K : Set X)) := hT2.to_le inf_le_left
  have hT₁N : T ⊓ normalizer (K : Set X) ≤ normalizer (K : Set X) := inf_le_right
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [HeDiag.inf_normalizer_inf]; exact h1024
  have hTKT₁ : T ⊓ K ≤ T ⊓ normalizer (K : Set X) := inf_le_inf_left T le_normalizer
  obtain ⟨c, hcF, hcF₀⟩ : ∃ c ∈ F, c ∉ F ⊓ normalizer (K : Set X) := by
    by_contra hall
    push Not at hall
    have h1 := card_le_of_le (fun x hx => hall x hx : F ≤ F ⊓ normalizer (K : Set X))
    omega
  have hcK : c ∉ normalizer (K : Set X) := fun hc => hcF₀ (mem_inf.mpr ⟨hcF, hc⟩)
  have hcT : c ∈ T := hFT hcF
  have hcc : c * c = 1 := hFe.2 c hcF
  have hc2 : orderOf c = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hcc) fun h1 => hcK (h1 ▸ one_mem _)
  have hKc : conjugate K c ≠ K := fun h' => hcK (mem_normalizer_of_conjugate_eq h')
  have hFeq : F ⊓ normalizer (K : Set X) ⊔ zpowers c = F := by
    refine eq_of_le_of_card_ge (sup_le inf_le_left (zpowers_le.mpr hcF)) ?_
    rw [card_sup_zpowers hc2 hcF₀ (GrSLit.mem_normalizer_of_commute fun x hx =>
      hFe.1 c hcF x (mem_inf.mp hx).1), hF4, hF8]
  have hcomF : ∀ y : X, (∀ f ∈ F ⊓ normalizer (K : Set X), f * y = y * f) → c * y = y * c →
      ∀ x ∈ F, x * y = y * x := by
    intro y h1 h2 x hx
    have hle : F ⊓ normalizer (K : Set X) ⊔ zpowers c ≤ centralizer ({y} : Set X) :=
      sup_le (fun f hf => mem_centralizer_singleton_iff.mpr (h1 f hf))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h2))
    rw [hFeq] at hle
    exact mem_centralizer_singleton_iff.mp (hle hx)
  have hTKn : T ⊓ normalizer (K : Set X) ≤ normalizer ((T ⊓ K : Subgroup X) : Set X) := by
    have h1 := le_normalizer_inf_left (L := K) hT₁N
    rwa [HeDiag.inf_normalizer_inf] at h1
  have hTKne : T ⊓ K ≠ ⊥ := fun hb => by rw [hb, card_bot] at h1024; omega
  obtain ⟨ζ, hζ, hζ2, hζc⟩ := exists_central_involution hT₁2 hTKT₁ hTKn hTKne
  obtain ⟨hY, hinj, hψT⟩ := h.doubleHom_facts e₁ hT2 hTM hcT hKc
  set w : X := doubleHom hY ⟨ζ, hζ⟩ with hw
  have hwT : w ∈ T ⊓ normalizer (K : Set X) := hψT _
  have hwc : c * w = w * c := commute_doubleHom_self hY hcc _
  have hwF₀ : ∀ f ∈ F ⊓ normalizer (K : Set X), f * w = w * f := fun f hf =>
    commute_doubleHom hY (hFe.1 f (mem_inf.mp hf).1 c hcF) _ (hζc f (hFT (mem_inf.mp hf).1 |>
      fun hfT => mem_inf.mpr ⟨hfT, (mem_inf.mp hf).2⟩))
  have hwF := hcomF w hwF₀ hwc
  have hw1 : w ≠ 1 := fun h1 => by
    have h2 : (⟨ζ, hζ⟩ : ↥(T ⊓ K)) = 1 := hinj (by rw [map_one]; exact h1)
    have h3 : ζ = 1 := congrArg Subtype.val h2
    rw [h3, orderOf_one] at hζ2
    exact absurd hζ2 (by norm_num)
  have hww : w * w = 1 := by
    rw [hw, ← map_mul]
    have : (⟨ζ, hζ⟩ : ↥(T ⊓ K)) * ⟨ζ, hζ⟩ = 1 :=
      Subtype.ext (by rw [Subgroup.coe_mul, ← pow_two, ← hζ2, pow_orderOf_eq_one]; rfl)
    rw [this, map_one]
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [pow_two]; exact hww) hw1
  by_cases hwF₀' : w ∈ F ⊓ normalizer (K : Set X)
  ·
    obtain ⟨f, hfF₀, hfw⟩ : ∃ f ∈ F ⊓ normalizer (K : Set X), f ∉ zpowers w := by
      by_contra hall
      push Not at hall
      have h1 := card_le_of_le (fun x hx => hall x hx : F ⊓ normalizer (K : Set X) ≤ zpowers w)
      rw [Nat.card_zpowers, hw2, hF4] at h1
      omega
    have hfT : f ∈ T := hFT (mem_inf.mp hfF₀).1
    have hff : f * f = 1 := hFe.2 f (mem_inf.mp hfF₀).1
    have hf2 : orderOf f = 2 := orderOf_eq_prime (by rw [pow_two]; exact hff)
      fun h1 => hfw (h1 ▸ one_mem _)
    have hF₀eq : zpowers w ⊔ zpowers f = F ⊓ normalizer (K : Set X) := by
      refine eq_of_le_of_card_ge (sup_le (zpowers_le.mpr hwF₀') (zpowers_le.mpr hfF₀)) ?_
      rw [card_sup_zpowers hf2 hfw (GrSLit.mem_normalizer_of_commute fun x hx => by
        obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hx
        exact (Commute.zpow_right (show Commute f w from hwF₀ f hfF₀) k).eq),
        Nat.card_zpowers, hw2, hF4]
    obtain ⟨E, hET, hEf, hEe, hE8⟩ := HeDiag.exists_eight_fixed e₁ h64 hOut hT₁N hT₁2 h1024'
      (mem_inf.mpr ⟨hfT, (mem_inf.mp hfF₀).2⟩) hff
    rw [HeDiag.inf_normalizer_inf] at hET
    let φ : ↥E →* X := (doubleHom hY).comp (inclusion hET)
    have hφinj : Function.Injective φ := hinj.comp (inclusion_injective hET)
    refine ⟨φ.range, ?_, isElemTwo_range hEe φ, by rw [card_range_of_injective hφinj, hE8], ?_⟩
    · rintro _ ⟨y, rfl⟩
      exact hψT _
    · rintro x hx _ ⟨y, rfl⟩
      refine hcomF _ (fun f' hf' => ?_) (commute_doubleHom_self hY hcc _) x hx
      have hyw : Commute (y : X) w := by
        rw [hw, doubleHom_apply]
        exact (show Commute (y : X) ζ from hζc y (hTKT₁ (hET y.2))).mul_right
          (h.commute_conj_one hT2 hTM (hET y.2) hζ hcT hKc)
      have hyC : F ⊓ normalizer (K : Set X) ≤ centralizer ({(y : X)} : Set X) := by
        rw [← hF₀eq]
        exact sup_le (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr hyw.symm.eq))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr
            (mem_centralizer_singleton_iff.mp (hEf y.2)).symm))
      exact commute_doubleHom hY (hFe.1 f' (mem_inf.mp hf').1 c hcF) _
        (mem_centralizer_singleton_iff.mp (hyC hf'))
  ·
    have hwN : w ∈ normalizer ((F ⊓ normalizer (K : Set X) : Subgroup X) : Set X) :=
      GrSLit.mem_normalizer_of_commute fun x hx => (hwF₀ x hx).symm
    refine ⟨F ⊓ normalizer (K : Set X) ⊔ zpowers w,
      sup_le (inf_le_inf_right _ hFT) (zpowers_le.mpr hwT),
      (hFe.mono inf_le_left).sup (isElemTwo_zpowers hww) fun x hx y hy => ?_,
      by rw [card_sup_zpowers hw2 hwF₀' hwN, hF4], fun x hx => ?_⟩
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact (Commute.zpow_right (show Commute x w from hwF₀ x hx) k).eq
    · have hle : F ⊓ normalizer (K : Set X) ⊔ zpowers w ≤ centralizer ({x} : Set X) :=
        sup_le (fun f hf => mem_centralizer_singleton_iff.mpr (hFe.1 f (mem_inf.mp hf).1 x hx))
          (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (hwF x hx).symm))
      exact fun y hy => (mem_centralizer_singleton_iff.mp (hle hy)).symm

theorem exists_comm_of_card_two {F : Subgroup X} (hFT : F ≤ T) (hFe : IsElemTwo F)
    (hF8 : Nat.card F = 8) (hF2 : Nat.card ↥(F ⊓ normalizer (K : Set X)) = 2) :
    ∃ B : Subgroup X, B ≤ T ⊓ normalizer (K : Set X) ∧ IsElemTwo B ∧ Nat.card B = 8 ∧
      ∀ x ∈ F, ∀ y ∈ B, x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₁2 : IsPGroup 2 ↥(T ⊓ normalizer (K : Set X)) := hT2.to_le inf_le_left
  have hT₁N : T ⊓ normalizer (K : Set X) ≤ normalizer (K : Set X) := inf_le_right
  have h1024' : Nat.card ↥(T ⊓ normalizer (K : Set X) ⊓ K) = 1024 := by
    rw [HeDiag.inf_normalizer_inf]; exact h1024
  obtain ⟨f, hfF₀, hf1⟩ : ∃ f ∈ F ⊓ normalizer (K : Set X), f ≠ 1 := by
    by_contra hall
    push Not at hall
    have h1 : F ⊓ normalizer (K : Set X) = ⊥ :=
      eq_bot_iff.mpr fun x hx => mem_bot.mpr (hall x hx)
    rw [h1, card_bot] at hF2
    omega
  have hF₀f := eq_zpowers_of_card_two hF2 hfF₀ hf1
  have hfF : f ∈ F := (mem_inf.mp hfF₀).1
  obtain ⟨c, hcF, hcF₀⟩ : ∃ c ∈ F, c ∉ F ⊓ normalizer (K : Set X) := by
    by_contra hall
    push Not at hall
    have h1 := card_le_of_le (fun x hx => hall x hx : F ≤ F ⊓ normalizer (K : Set X))
    omega
  have hcK : c ∉ normalizer (K : Set X) := fun hc => hcF₀ (mem_inf.mpr ⟨hcF, hc⟩)
  have hcc : c * c = 1 := hFe.2 c hcF
  have hc2 : orderOf c = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hcc) fun h1 => hcK (h1 ▸ one_mem _)
  have hF₁4 : Nat.card ↥(F ⊓ normalizer (K : Set X) ⊔ zpowers c) = 4 := by
    rw [card_sup_zpowers hc2 hcF₀ (GrSLit.mem_normalizer_of_commute fun x hx =>
      hFe.1 c hcF x (mem_inf.mp hx).1), hF2]
  have hF₁F : F ⊓ normalizer (K : Set X) ⊔ zpowers c ≤ F :=
    sup_le inf_le_left (zpowers_le.mpr hcF)
  obtain ⟨d, hdF, hdF₁⟩ : ∃ d ∈ F, d ∉ F ⊓ normalizer (K : Set X) ⊔ zpowers c := by
    by_contra hall
    push Not at hall
    have h1 := card_le_of_le
      (fun x hx => hall x hx : F ≤ F ⊓ normalizer (K : Set X) ⊔ zpowers c)
    omega
  have hdd : d * d = 1 := hFe.2 d hdF
  have hd2 : orderOf d = 2 :=
    orderOf_eq_prime (by rw [pow_two]; exact hdd) fun h1 => hdF₁ (h1 ▸ one_mem _)
  have hFeq : F ⊓ normalizer (K : Set X) ⊔ zpowers c ⊔ zpowers d = F := by
    refine eq_of_le_of_card_ge (sup_le hF₁F (zpowers_le.mpr hdF)) ?_
    rw [card_sup_zpowers hd2 hdF₁ (GrSLit.mem_normalizer_of_commute fun x hx =>
      hFe.1 d hdF x (hF₁F hx)), hF₁4, hF8]
  have hcomF : ∀ y : X, f * y = y * f → c * y = y * c → d * y = y * d →
      ∀ x ∈ F, x * y = y * x := by
    intro y h1 h2 h3 x hx
    have hle : F ⊓ normalizer (K : Set X) ⊔ zpowers c ⊔ zpowers d ≤
        centralizer ({y} : Set X) := by
      refine sup_le (sup_le ?_ (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h2)))
        (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h3))
      rw [hF₀f]
      exact zpowers_le.mpr (mem_centralizer_singleton_iff.mpr h1)
    rw [hFeq] at hle
    exact mem_centralizer_singleton_iff.mp (hle hx)
  have hnot : ∀ x ∈ F, x ∈ normalizer (K : Set X) →
      x ∈ F ⊓ normalizer (K : Set X) ⊔ zpowers c :=
    fun x hx hxK => mem_sup_left (mem_inf.mpr ⟨hx, hxK⟩)
  have hcdc : c * d = d * c := hFe.1 c hcF d hdF
  have hdK : d ∉ normalizer (K : Set X) := fun hd => hdF₁ (hnot d hdF hd)
  have hcdK : c * d ∉ normalizer (K : Set X) := fun hcd => hdF₁ (by
    rw [show d = c⁻¹ * (c * d) by group]
    exact mul_mem (mem_sup_right (inv_mem (mem_zpowers c))) (hnot _ (mul_mem hcF hdF) hcd))
  have hcd' : c * d⁻¹ ∉ normalizer (K : Set X) := fun hcd => hdF₁ (by
    rw [show d = (c * d⁻¹)⁻¹ * c by group]
    exact mul_mem (inv_mem (hnot _ (mul_mem hcF (inv_mem hdF)) hcd))
      (mem_sup_right (mem_zpowers c)))
  have hKc : conjugate K c ≠ K := fun e => hcK (mem_normalizer_of_conjugate_eq e)
  have hKd : conjugate K d ≠ K := fun e => hdK (mem_normalizer_of_conjugate_eq e)
  have hKcd : conjugate K (c * d) ≠ K := fun e => hcdK (mem_normalizer_of_conjugate_eq e)
  have hKcKd : conjugate K c ≠ conjugate K d := fun e =>
    hcd' (conjugate_eq_conjugate_iff.mp e)
  have hKcKcd : conjugate K c ≠ conjugate K (c * d) := fun e => hdK (by
    have h1 := conjugate_eq_conjugate_iff.mp e
    rw [hcdc, show c * (d * c)⁻¹ = d⁻¹ by group] at h1
    simpa using inv_mem h1)
  have hKdKcd : conjugate K d ≠ conjugate K (c * d) := fun e => hcK (by
    have h1 := conjugate_eq_conjugate_iff.mp e
    rw [show d * (c * d)⁻¹ = c⁻¹ by group] at h1
    simpa using inv_mem h1)
  obtain ⟨E, hET, hEf, hEe, hE8⟩ := HeDiag.exists_eight_fixed e₁ h64 hOut hT₁N hT₁2 h1024'
    (mem_inf.mpr ⟨hFT hfF, (mem_inf.mp hfF₀).2⟩) (hFe.2 f hfF)
  rw [HeDiag.inf_normalizer_inf] at hET
  have hcT := hFT hcF
  have hdT := hFT hdF
  obtain ⟨hY, hinj, hψT⟩ := h.doubleHom_facts e₁ hT2 hTM hcT hKc
  have hconj : ∀ u ∈ (doubleHom hY).range, d⁻¹ * u * d ∈ T ⊓ coreActionKernel K := by
    rintro _ ⟨x, rfl⟩
    rw [doubleHom_apply, show d⁻¹ * ((x : X) * (c⁻¹ * x * c)) * d =
      (d⁻¹ * x * d) * ((c * d)⁻¹ * x * (c * d)) by group]
    have hxT := (mem_inf.mp x.2).1
    have hxK := (mem_inf.mp x.2).2
    exact mul_mem (mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hdT) hxT) hdT,
      h.conj_mem_coreActionKernel hTM hxK hdT hKd⟩)
      (mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem (mul_mem hcT hdT)) hxT) (mul_mem hcT hdT),
        h.conj_mem_coreActionKernel hTM hxK (mul_mem hcT hdT) hKcd⟩)
  have hY₁ : ∀ u ∈ (doubleHom hY).range, ∀ u' ∈ (doubleHom hY).range,
      Commute u (d⁻¹ * u' * d) := by
    rintro _ ⟨x, rfl⟩ _ ⟨x', rfl⟩
    rw [doubleHom_apply, doubleHom_apply, show d⁻¹ * ((x' : X) * (c⁻¹ * x' * c)) * d =
      (d⁻¹ * x' * d) * ((c * d)⁻¹ * x' * (c * d)) by group]
    exact ((h.commute_conj_one hT2 hTM x.2 x'.2 hdT hKd).mul_right
      (h.commute_conj_one hT2 hTM x.2 x'.2 (mul_mem hcT hdT) hKcd)).mul_left
      ((h.commute_conj hT2 hTM x.2 x'.2 hcT hdT hKcKd).mul_right
        (h.commute_conj hT2 hTM x.2 x'.2 hcT (mul_mem hcT hdT) hKcKcd))
  have hinj₂ : Function.Injective (doubleHom hY₁) := by
    refine doubleHom_injective hY₁ (P := coreActionKernel K)
      (fun u hu => (mem_inf.mp (hconj u hu)).2) ?_
    rintro _ ⟨x, rfl⟩ hk
    rw [doubleHom_apply] at hk
    have hxk : (x : X) ∈ coreActionKernel K := by
      have h1 := mul_mem hk (inv_mem (h.conj_mem_coreActionKernel hTM (mem_inf.mp x.2).2 hcT
        hKc))
      rwa [mul_inv_cancel_right] at h1
    have hx1 : x = 1 := Subtype.ext (HeDiag.eq_one_of_mem_coreActionKernel e₁ hT2
      (mem_inf.mp x.2).1 (mem_inf.mp x.2).2 hxk)
    rw [hx1, map_one]
  let φ : ↥E →* X := (doubleHom hY₁).comp ((doubleHom hY).rangeRestrict.comp (inclusion hET))
  have hφinj : Function.Injective φ := hinj₂.comp
    ((MonoidHom.rangeRestrict_injective_iff.mpr hinj).comp (inclusion_injective hET))
  have hφ : ∀ y : ↥E, φ y = doubleHom hY (inclusion hET y) *
      (d⁻¹ * doubleHom hY (inclusion hET y) * d) := fun y => rfl
  refine ⟨φ.range, ?_, isElemTwo_range hEe φ, by rw [card_range_of_injective hφinj, hE8], ?_⟩
  · rintro _ ⟨y, rfl⟩
    rw [hφ]
    exact mul_mem (hψT _) (mem_inf.mpr ⟨(mem_inf.mp (hconj _ ⟨_, rfl⟩)).1,
      (mem_coreActionKernel.mp (mem_inf.mp (hconj _ ⟨_, rfl⟩)).2).1⟩)
  · rintro x hx _ ⟨y, rfl⟩
    have hfy : Commute f (inclusion hET y : X) :=
      (mem_centralizer_singleton_iff.mp (hEf y.2)).symm
    have hfc : Commute f c := hFe.1 f hfF c hcF
    have hfd : Commute f d := hFe.1 f hfF d hdF
    have hcd : Commute c d := hcdc
    refine hcomF _ ?_ ?_ ?_ x hx
    · exact commute_doubleHom hY₁ hfd ⟨_, ⟨_, rfl⟩⟩
        (commute_doubleHom hY hfc (inclusion hET y) hfy)
    · exact commute_doubleHom hY₁ hcd ⟨_, ⟨_, rfl⟩⟩
        (commute_doubleHom_self hY hcc (inclusion hET y))
    · exact commute_doubleHom_self hY₁ hdd ⟨_, ⟨_, rfl⟩⟩

end Move

end Setting

end CFSG.ComponentClassification.GrSLit.HeSN
