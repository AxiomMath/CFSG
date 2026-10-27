module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76L26Lemma27

public section

namespace CFSG.ComponentClassification.Asc76.L26

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding

variable {G : Type} [Group G]

theorem fusionGen_mono {Γ Γ' : Set G} (h : Γ ⊆ Γ') : fusionGen Γ ≤ fusionGen Γ' :=
  closure_mono fun _ ⟨x, hx, hgx⟩ => ⟨x, h hx, h hgx⟩

abbrev infFamily (𝒯 : Set (Subgroup G)) (Y : Subgroup G) : Set (Subgroup G) :=
  (fun T => T ⊓ Y) '' 𝒯

theorem mem_memberSet_infFamily {𝒯 : Set (Subgroup G)} {Y : Subgroup G} {x : G} :
    x ∈ memberSet (infFamily 𝒯 Y) ↔ x ∈ memberSet 𝒯 ∧ x ∈ Y := by
  constructor
  · rintro ⟨hx1, _, ⟨T, hT, rfl⟩, hx⟩
    exact ⟨⟨hx1, T, hT, (mem_inf.mp hx).1⟩, (mem_inf.mp hx).2⟩
  · rintro ⟨⟨hx1, T, hT, hx⟩, hxY⟩
    exact ⟨hx1, _, ⟨T, hT, rfl⟩, mem_inf.mpr ⟨hx, hxY⟩⟩

theorem SylowShape.rightConjugate {P : Subgroup G} (h : SylowShape P) (y : G) :
    SylowShape (rightConjugate P y) :=
  SylowShapeT.of_mulEquiv h
    (equivMapOfInjective P (MulAut.conj y⁻¹).toMonoidHom (MulAut.conj y⁻¹).injective)

theorem SylowShape.mem_center {P : Subgroup G} (h : SylowShape P) {b : G} (hb : b ∈ P)
    (hb2 : b ^ 2 = 1) : ∀ p ∈ P, p * b = b * p := by
  intro p hp
  have hc := h.inv_center ⟨b, hb⟩ (Subtype.ext (by simpa using hb2))
  exact congrArg Subtype.val (mem_center_iff.mp hc ⟨p, hp⟩)

variable [Finite G] {S : Subgroup G} {𝒯 : Set (Subgroup G)}

theorem cstep26 (IH : Statement26 (Nat.card G - 1)) (h : HypCore S 𝒯) {P : Subgroup G}
    (hP : P ∈ 𝒯) (hbig : IsBig P)
    (hconj : ∀ g : G, rightConjugate P g ≤ S → rightConjugate P g ∈ 𝒯) {x : G}
    (hxZ : x ∉ center G) (hPx : P ≤ centralizer ({x} : Set G)) :
    ∃ h₀ ∈ fusionGen (memberSet 𝒯),
      rightConjugate (S ⊓ centralizer ({x} : Set G)) h₀ ≤ S ∧
      IsSylowOf 2 (S ⊓ centralizer ({h₀⁻¹ * x * h₀} : Set G))
        (centralizer ({h₀⁻¹ * x * h₀} : Set G)) ∧
      (centralizer ({x} : Set G) ≤ fusionGen (memberSet 𝒯) ∨
        ((∀ R' ∈ 𝒯, R' ≤ centralizer ({h₀⁻¹ * x * h₀} : Set G) → IsBig R' →
            R' = rightConjugate P h₀) ∧ SylowShape (rightConjugate P h₀))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := memberSet 𝒯 with hΓdef
  set H := fusionGen Γ with hHdef
  have hΓS : Γ ⊆ S := memberSet_subset h
  obtain ⟨E, hEP, hE4, -⟩ := exists_four_le hbig.1
  obtain ⟨v, hvE, hv1⟩ := (Subgroup.bot_or_exists_ne_one E).resolve_left (fun h' => by
    rw [h', Subgroup.card_bot] at hE4; omega)
  have hvP := hEP hvE
  have hvΓ : v ∈ Γ := mem_memberSet hP hvP hv1
  set A := S ⊓ centralizer ({x} : Set G) with hAdef
  have hA2 : IsPGroup 2 A := h.sylow.isPGroup.to_le inf_le_left
  obtain ⟨Q, hQ, hAQ⟩ := AschbacherTheorem3.exists_isSylowOf_le hA2 inf_le_right
  have hSH : S ≤ H := le_fusionGen h.closed hΓS ⟨v, hvΓ⟩
  have hvQ : v ∈ Q := hAQ (mem_inf.mpr ⟨h.le P hP hvP, hPx hvP⟩)
  have hQH : Q ≤ H := by
    obtain ⟨c, -, hc⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf h.sylow
      hQ.isPGroup le_top
    have hle := rightConjugate_mono (hc.trans hSH) c⁻¹
    rw [rightConjugate_inv] at hle
    have hvc : v ∈ rightConjugate H c⁻¹ := hle hvQ
    rw [mem_rightConjugate_fusionGen_iff h.sylow h.closed hΓS hvΓ] at hvc
    intro q hq
    have hq' := hle hq
    rw [mem_rightConjugate_iff] at hq'
    have hq'' := H.mul_mem (H.mul_mem (H.inv_mem hvc) hq') hvc
    simpa [mul_assoc] using hq''
  obtain ⟨h₀, hh₀, hQS⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf
    (h.sylow.of_le hSH le_top) hQ.isPGroup hQH
  refine ⟨h₀, hh₀, (rightConjugate_mono hAQ h₀).trans hQS, ?_⟩
  set x' := h₀⁻¹ * x * h₀ with hx'def
  set Y := centralizer ({x'} : Set G) with hYdef
  have hYeq : Y = rightConjugate (centralizer ({x} : Set G)) h₀ :=
    (rightConjugate_centralizer_singleton x h₀).symm
  have hQ'Y : rightConjugate Q h₀ ≤ Y := by
    rw [hYeq]
    exact rightConjugate_mono hQ.le h₀
  have hQ'syl : IsSylowOf 2 (rightConjugate Q h₀) Y := by
    rw [hYeq]
    apply isSylowOf_of_card (rightConjugate_mono hQ.le h₀)
    rw [rightConjugate_card, hQ.card_eq, rightConjugate_card]
  have hsyl : IsSylowOf 2 (S ⊓ Y) Y := by
    have := hQ'syl.eq_of_le (le_inf hQS hQ'Y) inf_le_right (h.sylow.isPGroup.to_le inf_le_left)
    rw [this]
    exact hQ'syl
  refine ⟨hsyl, ?_⟩
  set P' := rightConjugate P h₀ with hP'def
  have hP'Q : P' ≤ rightConjugate Q h₀ :=
    rightConjugate_mono ((le_inf (h.le P hP) hPx).trans hAQ) h₀
  have hP'S : P' ≤ S := hP'Q.trans hQS
  have hP'Y : P' ≤ Y := hP'Q.trans hQ'Y
  have hP'𝒯 : P' ∈ 𝒯 := hconj h₀ hP'S
  have hYne : Y ≠ ⊤ := by
    intro htop
    apply hxZ
    have hx'Z : x' ∈ center G := by
      rw [mem_center_iff]
      intro g
      have hg : g ∈ Y := by rw [htop]; exact mem_top g
      exact mem_centralizer_singleton_iff.mp hg
    have : x = h₀ * x' * h₀⁻¹ := by rw [hx'def]; group
    rw [this]
    exact (inferInstance : (center G).Normal).conj_mem x' hx'Z h₀
  have hres := concl26_of_sub IH (Y := Y) (𝒯 := infFamily 𝒯 Y) (card_le_pred_of_ne_top hYne)
    inf_le_right hsyl
    (by
      rintro _ ⟨T, hT, rfl⟩
      exact inf_le_inf_right Y (h.le T hT))
    (by
      intro z hz y hy hyz
      rw [mem_memberSet_infFamily] at hz ⊢
      exact ⟨h.closed z hz.1 y (mem_inf.mp hyz).1, (mem_inf.mp hyz).2⟩)
    (by
      rintro _ ⟨T₁, hT₁, rfl⟩ _ ⟨T₂, hT₂, rfl⟩ hne
      have hne' : T₁ ≠ T₂ := fun h' => hne (by rw [h'])
      exact eq_bot_iff.mpr ((commutator_mono inf_le_left inf_le_left).trans
        (h.comm T₁ hT₁ T₂ hT₂ hne').le))
    (⟨P', hP'𝒯, inf_eq_left.mpr hP'Y⟩ : P' ∈ infFamily 𝒯 Y) (hbig.rightConjugate h₀)
    (by
      intro y hy hyS
      have hS' : rightConjugate P' y ≤ S := hyS.trans inf_le_left
      rw [hP'def, rightConjugate_mul] at hS' ⊢
      exact ⟨_, hconj _ hS', inf_eq_left.mpr (by
        rw [← rightConjugate_mul]
        exact rightConjugate_le_of_mem hP'Y hy)⟩)
  rcases hres with hle | ⟨huniq, hshape⟩
  · left
    have hle' : Y ≤ H := hle.trans (fusionGen_mono fun z hz => (mem_memberSet_infFamily.mp hz).1)
    intro c hc
    have hcY : h₀⁻¹ * c * h₀ ∈ Y := by
      rw [hYeq, mem_rightConjugate_iff]
      simpa [mul_assoc] using hc
    have hc' : c = h₀ * (h₀⁻¹ * c * h₀) * h₀⁻¹ := by group
    rw [hc']
    exact H.mul_mem (H.mul_mem hh₀ (hle' hcY)) (H.inv_mem hh₀)
  · right
    exact ⟨fun R' hR' hR'Y hbig' => huniq _ ⟨R', hR', inf_eq_left.mpr hR'Y⟩ hbig', hshape⟩

theorem exists_normalizer_conj (hS : IsSylowOf 2 S ⊤) {P : Subgroup G} (hP2 : IsPGroup 2 P)
    (hwc : ∀ y : G, rightConjugate P y ≤ S → rightConjugate P y = P) {x₁ x₂ w : G}
    (hx₁ : ∀ p ∈ P, p * x₁ = x₁ * p) (hx₂ : ∀ p ∈ P, p * x₂ = x₂ * p)
    (hw : x₂ = w⁻¹ * x₁ * w) : ∃ n ∈ normalizer (P : Set G), x₂ = n⁻¹ * x₁ * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPC : P ≤ centralizer ({x₂} : Set G) := fun p hp =>
    mem_centralizer_singleton_iff.mpr (hx₂ p hp)
  have hPwC : rightConjugate P w ≤ centralizer ({x₂} : Set G) := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    rw [mem_centralizer_singleton_iff, hw]
    have h1 := hx₁ _ hy
    calc y * (w⁻¹ * x₁ * w) = w⁻¹ * ((w * y * w⁻¹) * x₁) * w := by group
      _ = w⁻¹ * (x₁ * (w * y * w⁻¹)) * w := by rw [h1]
      _ = w⁻¹ * x₁ * w * y := by group
  obtain ⟨Q, hQ, hPQ⟩ := AschbacherTheorem3.exists_isSylowOf_le hP2 hPC
  obtain ⟨c, hc, hcle⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hQ
    (hP2.map _ : IsPGroup 2 (rightConjugate P w)) hPwC
  obtain ⟨e, -, he⟩ := AschbacherTheorem3.exists_rightConjugate_le_of_isSylowOf hS hQ.isPGroup
    le_top
  have hPe : rightConjugate P e = P := hwc e ((rightConjugate_mono hPQ e).trans he)
  have hPwce : rightConjugate P (w * c * e) = P := by
    apply hwc
    rw [← rightConjugate_mul, ← rightConjugate_mul]
    exact (rightConjugate_mono hcle e).trans he
  have heN := (rightConjugate_eq_self_iff P e).mp hPe
  have hwceN := (rightConjugate_eq_self_iff P (w * c * e)).mp hPwce
  refine ⟨w * c, ?_, ?_⟩
  · have : w * c = (w * c * e) * e⁻¹ := by group
    rw [this]
    exact mul_mem hwceN (inv_mem heN)
  · have hcx : c * x₂ = x₂ * c := mem_centralizer_singleton_iff.mp hc
    calc x₂ = c⁻¹ * (c * x₂) := by group
      _ = c⁻¹ * (x₂ * c) := by rw [hcx]
      _ = (w * c)⁻¹ * x₁ * (w * c) := by rw [hw]; group

theorem beta1 (IH : Statement26 (Nat.card G - 1)) (h : HypCore S 𝒯)
    (hZ : ∀ c ∈ center G, orderOf c ≠ 2) {P : Subgroup G} (hP : P ∈ 𝒯) (hbig : IsBig P)
    (hconj : ∀ g : G, rightConjugate P g ≤ S → rightConjugate P g ∈ 𝒯) {a b : G}
    (haP : a ∈ P) (haZ : ∀ p ∈ P, p * a = a * p) (ha2 : orderOf a = 2) (hbS : b ∈ S) {w : G}
    (hbw : b = w⁻¹ * a * w) (hab : a * b = b * a) (hbP : b ∉ P) :
    centralizer ({a * b} : Set G) ≤ fusionGen (memberSet 𝒯) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Γ := memberSet 𝒯 with hΓdef
  have ha1 : a ≠ 1 := fun h' => by rw [h', orderOf_one] at ha2; omega
  have haΓ : a ∈ Γ := mem_memberSet hP haP ha1
  have haa : a * a = 1 := by rw [← sq, ← ha2]; exact pow_orderOf_eq_one a
  have hbb : b * b = 1 := by
    rw [hbw]
    calc w⁻¹ * a * w * (w⁻¹ * a * w) = w⁻¹ * (a * a) * w := by group
      _ = 1 := by rw [haa]; group
  have hbΓ : b ∈ Γ := by
    have := h.closed a haΓ w (by rw [← hbw]; exact hbS)
    rwa [← hbw] at this
  have hbC : ∀ p ∈ P, p * b = b * p := by
    obtain ⟨-, T, hT, hbT⟩ := hbΓ
    have hTP : T ≠ P := fun h' => hbP (h' ▸ hbT)
    exact fun p hp => (commute_of_commutator_eq_bot (h.comm T hT P hP hTP) hbT hp).symm
  have hx1 : a * b ≠ 1 := by
    intro hx
    apply hbP
    have : b = a := by
      calc b = a * (a * b) := by rw [← mul_assoc, haa, one_mul]
        _ = a := by rw [hx, mul_one]
    rw [this]
    exact haP
  have hxx : a * b * (a * b) = 1 := by
    calc a * b * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = 1 := by rw [← mul_assoc, haa, one_mul, hbb]
  have hxZ : a * b ∉ center G := fun hc =>
    hZ _ hc (orderOf_eq_prime (by rw [sq]; exact hxx) hx1)
  have hPx : P ≤ centralizer ({a * b} : Set G) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    calc p * (a * b) = (p * a) * b := by group
      _ = (a * p) * b := by rw [haZ p hp]
      _ = a * (p * b) := by group
      _ = a * (b * p) := by rw [hbC p hp]
      _ = a * b * p := by group
  obtain ⟨h₀, -, hAS, -, hcase⟩ := cstep26 IH h hP hbig hconj hxZ hPx
  rcases hcase with hle | ⟨huniq, hshape⟩
  · exact hle
  exfalso
  set P' := rightConjugate P h₀ with hP'def
  set a' := h₀⁻¹ * a * h₀ with ha'def
  set b' := h₀⁻¹ * b * h₀ with hb'def
  have hmemA : ∀ y ∈ S, y * (a * b) = (a * b) * y → h₀⁻¹ * y * h₀ ∈ S := by
    intro y hyS hyx
    apply hAS
    rw [mem_rightConjugate_iff]
    have : h₀ * (h₀⁻¹ * y * h₀) * h₀⁻¹ = y := by group
    rw [this]
    exact mem_inf.mpr ⟨hyS, mem_centralizer_singleton_iff.mpr hyx⟩
  have haS : a ∈ S := h.le P hP haP
  have hb'S : b' ∈ S := hmemA b hbS (by
    calc b * (a * b) = (b * a) * b := by group
      _ = (a * b) * b := by rw [hab])
  have hPS : P ≤ S := h.le P hP
  have hP'S : P' ≤ S := by
    intro y hy
    rw [hP'def, mem_rightConjugate_iff] at hy
    have := hmemA _ (hPS hy) (mem_centralizer_singleton_iff.mp (hPx hy))
    simpa [mul_assoc] using this
  have hP'𝒯 : P' ∈ 𝒯 := hconj h₀ hP'S
  have hmemP' : ∀ y, h₀⁻¹ * y * h₀ ∈ P' ↔ y ∈ P := fun y => by
    rw [hP'def, mem_rightConjugate_iff]
    simp [mul_assoc]
  have ha'P' : a' ∈ P' := (hmemP' a).mpr haP
  have hb'P' : b' ∉ P' := fun h' => hbP ((hmemP' b).mp h')
  have hconjP' : ∀ y ∈ P', ∃ p ∈ P, y = h₀⁻¹ * p * h₀ := fun y hy => by
    rw [hP'def, mem_rightConjugate_iff] at hy
    exact ⟨_, hy, by group⟩
  have hcomm_conj : ∀ {u v : G}, u * v = v * u →
      (h₀⁻¹ * u * h₀) * (h₀⁻¹ * v * h₀) = (h₀⁻¹ * v * h₀) * (h₀⁻¹ * u * h₀) := by
    intro u v huv
    calc (h₀⁻¹ * u * h₀) * (h₀⁻¹ * v * h₀) = h₀⁻¹ * (u * v) * h₀ := by group
      _ = h₀⁻¹ * (v * u) * h₀ := by rw [huv]
      _ = (h₀⁻¹ * v * h₀) * (h₀⁻¹ * u * h₀) := by group
  have ha'C : ∀ p ∈ P', p * a' = a' * p := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := hconjP' y hy
    exact hcomm_conj (haZ p hp)
  have hb'C : ∀ p ∈ P', p * b' = b' * p := by
    intro y hy
    obtain ⟨p, hp, rfl⟩ := hconjP' y hy
    exact hcomm_conj (hbC p hp)
  have hb'Γ : b' ∈ Γ := by
    have hS' : (w * h₀)⁻¹ * a * (w * h₀) ∈ S := by
      have : (w * h₀)⁻¹ * a * (w * h₀) = b' := by rw [hb'def, hbw]; group
      rw [this]
      exact hb'S
    have := h.closed a haΓ (w * h₀) hS'
    have e : (w * h₀)⁻¹ * a * (w * h₀) = b' := by rw [hb'def, hbw]; group
    rwa [e] at this
  have hb'b' : b' ^ 2 = 1 := by
    rw [hb'def, sq]
    calc h₀⁻¹ * b * h₀ * (h₀⁻¹ * b * h₀) = h₀⁻¹ * (b * b) * h₀ := by group
      _ = 1 := by rw [hbb]; group
  have hx' : h₀⁻¹ * (a * b) * h₀ = a' * b' := by rw [ha'def, hb'def]; group
  have hwc : ∀ y : G, rightConjugate P' y ≤ S → rightConjugate P' y = P' := by
    intro y hy
    by_contra hne
    have hP'y𝒯 : rightConjugate P' y ∈ 𝒯 := by
      rw [hP'def, rightConjugate_mul] at hy ⊢
      exact hconj _ hy
    have hc' := h.comm _ hP'y𝒯 P' hP'𝒯 hne
    have hY : rightConjugate P' y ≤ centralizer ({h₀⁻¹ * (a * b) * h₀} : Set G) := by
      intro q hq
      rw [mem_centralizer_singleton_iff, hx']
      have h1 : q * a' = a' * q := commute_of_commutator_eq_bot hc' hq ha'P'
      have h2 : q * b' = b' * q := by
        obtain ⟨-, T', hT', hb'T'⟩ := hb'Γ
        by_cases hTT : T' = rightConjugate P' y
        · subst hTT
          exact ((hshape.rightConjugate y).mem_center hb'T' hb'b' q hq)
        · exact (commute_of_commutator_eq_bot (h.comm T' hT' _ hP'y𝒯 hTT) hb'T' hq).symm
      calc q * (a' * b') = (q * a') * b' := by group
        _ = (a' * q) * b' := by rw [h1]
        _ = a' * (q * b') := by group
        _ = a' * (b' * q) := by rw [h2]
        _ = a' * b' * q := by group
    exact hne (huniq _ hP'y𝒯 hY (by rw [hP'def, rightConjugate_mul]; exact hbig.rightConjugate _))
  have hw' : b' = (h₀⁻¹ * w * h₀)⁻¹ * a' * (h₀⁻¹ * w * h₀) := by
    rw [hb'def, ha'def, hbw]; group
  obtain ⟨n, hnN, hn⟩ := exists_normalizer_conj h.sylow
    (h.sylow.isPGroup.to_le hP'S) hwc ha'C hb'C hw'
  apply hb'P'
  rw [hn]
  exact (mem_normalizer_iff''.mp hnN a').mp ha'P'

end CFSG.ComponentClassification.Asc76.L26
