module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D20

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem MinCounter.inv_or_cent (h22 : Asc76Lemma22) {S : Subgroup G} (hM : MinCounter Ω S)
    {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω) (hJD : J ∉ omegaD Ω (sec4W Ω S))
    (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀) (ht1 : t ≠ 1)
    (htt : t * t = 1) {K₃ R₃ U₃ : Subgroup G} (hK₃ : K₃ ∈ omegaD Ω (sec4W Ω S))
    (htK₃ : t ∈ normalizer (K₃ : Set G)) (hR₃ : IsSylowOf 2 R₃ K₃) (hU₃ : IsDihedralRot U₃ R₃)
    (htR₃ : t ∈ normalizer (R₃ : Set G)) :
    ((∀ u ∈ U₃, t * u * t⁻¹ = u⁻¹) ∧ IsDihedralTwoGroup (zpowers t ⊔ R₃)) ∨
      ((∀ u ∈ U₃, t * u * t⁻¹ = u) ∧ ∃ y ∈ R₃, t * y * t⁻¹ ≠ y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hK₃Ω := hK₃.1
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  have hnotJ : ¬ J ≤ normalizer (K₃ : Set G) := fun h =>
    hJD (hM.mem_omegaD_of_le_normalizer hK₃ hJ h)
  have hnc : ∃ y ∈ R₃, t * y * t⁻¹ ≠ y := by
    by_contra hcon
    push Not at hcon
    apply hJD
    refine hM.mem_omegaD_of_sylow_le_normalizer h22 hK₃ hJ hR₃ fun y hy => ?_
    apply Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) htJ ht1 htt
    rw [mem_centralizer_singleton_iff]
    calc y * t = (t * y * t⁻¹) * t := by rw [hcon y hy]
      _ = t * y := by group
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  obtain ⟨V₁, hV₁, htV₁⟩ := exists_isSylowOf_le htP
    ((zpowers_le).mpr (mem_inf.mpr ⟨htJ, htK₃⟩) : zpowers t ≤ J ⊓ normalizer (K₃ : Set G))
  have hV₁1 : V₁ ≠ ⊥ := by
    intro h
    rw [h] at htV₁
    exact ht1 (mem_bot.mp (htV₁ (mem_zpowers t)))
  obtain ⟨R', hR', hV₁R'⟩ := exists_isSylowOf_normalized hV₁.isPGroup (hV₁.le.trans inf_le_right)
  obtain ⟨U', hU'⟩ := Assumption41.exists_rot hΩ hK₃Ω hR'
  rcases lemma415 h22 hΩ hK₃Ω hJ hR' hU' hV₁ hV₁1 hV₁R' with ⟨-, hJK, -⟩ | ⟨-, hcomm, -, -⟩ |
    ⟨hV2, -, -⟩
  · exact absurd hJK hnotJ
  ·
    right
    refine ⟨?_, hnc⟩
    have htC : t ∈ centralizer (U' : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) (htV₁ (mem_zpowers t))
    have htR' : t ∈ normalizer (R' : Set G) := hV₁R' (htV₁ (mem_zpowers t))
    obtain ⟨o, ho, hReq⟩ :=
      exists_oddCoreIn_eq_rightConjugate hR₃ hR' (hM.twoNil K₃ hK₃Ω R' hR')
    have hU'o := hU'.rightConjugate o
    rw [← hReq] at hU'o
    have hUeq : AschbacherTightEmbedding.rightConjugate U' o = U₃ :=
      hU₃.eq_of_isCyclic hU'o.le hU'o.isCyclic hU'o.relIndex_eq
    intro u hu
    rw [← hUeq, mem_rightConjugate_iff] at hu
    have htu : t * (o * u * o⁻¹) * t⁻¹ = o * u * o⁻¹ := by
      have h1 := mem_centralizer_iff.mp htC _ hu
      calc t * (o * u * o⁻¹) * t⁻¹ = (o * u * o⁻¹) * t * t⁻¹ := by rw [← h1]
        _ = o * u * o⁻¹ := by group
    have h1 := conj_rightConjugate_of_normalizes hR' ho htK₃ htR' (hReq ▸ htR₃)
      (hU'.le hu) htu
    have e : o⁻¹ * (o * u * o⁻¹) * o = u := by group
    rwa [e] at h1
  ·
    left
    have hVt : zpowers t = V₁ := by
      apply eq_of_le_of_card_ge htV₁
      rw [hV2, Nat.card_zpowers, orderOf_eq_prime (by rw [pow_two]; exact htt) ht1]
    have hVt' : IsSylowOf 2 (zpowers t) (J ⊓ normalizer (K₃ : Set G)) := hVt ▸ hV₁
    have hVt1 : zpowers t ≠ ⊥ := hVt ▸ hV₁1
    rcases lemma415 h22 hΩ hK₃Ω hJ hR₃ hU₃ hVt' hVt1 ((zpowers_le).mpr htR₃) with
      ⟨-, hJK, -⟩ | ⟨⟨e⟩, -, -, -⟩ | ⟨-, hD, hinv⟩
    · exact absurd hJK hnotJ
    · exfalso
      have h1 : Nat.card (zpowers t) = Nat.card U₃ := Nat.card_congr e.toEquiv
      rw [hVt, hV2] at h1
      have := hU₃.four_le
      omega
    · exact ⟨fun u hu => hinv t (mem_zpowers t) ht1 u hu, hD⟩

theorem MinCounter.false_of_not_le_normalizer_of_not_mem (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω)
    (hJD : J ∉ omegaD Ω (sec4W Ω S)) (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀)
    {t : G} (htV : t ∈ V₀) (ht1 : t ≠ 1) (htt : t * t = 1)
    (htW : t ∈ normalizer (sec4W Ω S : Set G)) {K R U : Subgroup G} (hK : K ∈ Ω)
    (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) (hRW : R ≤ normalizer (sec4W Ω S : Set G))
    (hU'R : AschbacherTightEmbedding.rightConjugate U t ≤ normalizer (R : Set G))
    (hKt : AschbacherTightEmbedding.rightConjugate K t ≠ K)
    (hRt : ¬ AschbacherTightEmbedding.rightConjugate R t ≤ normalizer (K : Set G)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb => sec4W_mul_comm hΩ hS ha hb
  have H : Sec4Hyp Ω := ⟨h22, hΩ, hM.twoNil⟩
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  set K' := AschbacherTightEmbedding.rightConjugate K t with hK'def
  set R' := AschbacherTightEmbedding.rightConjugate R t with hR'def
  set U' := AschbacherTightEmbedding.rightConjugate U t with hU'def
  have hK' : K' ∈ Ω := hΩ.conj_mem K hK t
  have hR' : IsSylowOf 2 R' K' := isSylowOf_rightConjugate hR t
  have hU' : IsDihedralRot U' R' := hU.rightConjugate t
  have hR'W : R' ≤ normalizer (W : Set G) := rightConjugate_le_normalizer hRW htW
  have hKK' : K ≠ K' := fun h => hKt h.symm
  have hUW : U ≤ W := rot_le_sec4W hΩ hS hK hR hU hRW
  have hU'W : U' ≤ W := rot_le_sec4W hΩ hS hK' hR' hU' hR'W
  obtain ⟨z, hzU, hz1, hzz, hzuniq, hzR⟩ := hU.exists_involution
  set z' := t⁻¹ * z * t with hz'def
  have hz'U' : z' ∈ U' := conj_mem_rightConjugate hzU t
  have hz'1 : z' ≠ 1 := by
    intro h
    apply hz1
    calc z = t * z' * t⁻¹ := by rw [hz'def]; group
      _ = 1 := by rw [h]; group
  have hz'z' : z' * z' = 1 := by
    calc z' * z' = t⁻¹ * (z * z) * t := by rw [hz'def]; group
      _ = 1 := by rw [hzz]; group
  have hzZ : IsZOf R z := ⟨U, hU, hzU, hz1, hzz⟩
  have hz'Z : IsZOf R' z' := ⟨U', hU', hz'U', hz'1, hz'z'⟩
  have htz : t * z * t⁻¹ = z' := by rw [hz'def, htinv]
  have htz' : t * z' * t⁻¹ = z := by rw [hz'def]; group
  have hzz'c : z * z' = z' * z := hWc z (hUW hzU) z' (hU'W hz'U')
  have hRK' : ¬ R ≤ normalizer (K' : Set G) := by
    intro h
    exact hRt (hR'.le.trans (le_normalizer_of_sylow h22 hΩ hK' hK hKK'.symm hR h).2)
  have hA : ∀ x ∈ R, x ∉ U → x⁻¹ * z' * x = z' * z := fun x hx hxU =>
    conj_z_of_not_sylow H hS hK hK' hKK' hR hR' hRW hR'W hU hRt hzZ hz'Z hx hxU
  obtain ⟨x, hxR, hxU⟩ := hU.exists_not_mem
  have hxW : x ∈ normalizer (W : Set G) := hRW hxR
  set z₃ := z' * z with hz₃def
  set K₃ := AschbacherTightEmbedding.rightConjugate K' x with hK₃def
  set R₃' := AschbacherTightEmbedding.rightConjugate R' x with hR₃'def
  set U₃' := AschbacherTightEmbedding.rightConjugate U' x with hU₃'def
  have hK₃ : K₃ ∈ Ω := hΩ.conj_mem K' hK' x
  have hR₃' : IsSylowOf 2 R₃' K₃ := isSylowOf_rightConjugate hR' x
  have hU₃' : IsDihedralRot U₃' R₃' := hU'.rightConjugate x
  have hR₃'W : R₃' ≤ normalizer (W : Set G) := rightConjugate_le_normalizer hR'W hxW
  have hU₃'W : U₃' ≤ W := rightConjugate_le_of_le_normalizer hU'W hxW
  have hz₃U₃' : z₃ ∈ U₃' := by
    have := conj_mem_rightConjugate hz'U' x
    rwa [hA x hxR hxU] at this
  have hz₃z₃ : z₃ * z₃ = 1 := by
    calc z₃ * z₃ = z' * (z * z') * z := by rw [hz₃def]; group
      _ = z' * (z' * z) * z := by rw [hzz'c]
      _ = (z' * z') * (z * z) := by group
      _ = 1 := by rw [hz'z', hzz, one_mul]
  have hzK : z ∈ K := hR.le (hU.le hzU)
  have hz'K' : z' ∈ K' := hR'.le (hU'.le hz'U')
  have hz₃1 : z₃ ≠ 1 := by
    intro h
    have : z' = z := by
      calc z' = z' * z * z := by rw [mul_assoc, hzz, mul_one]
        _ = z := by rw [← hz₃def, h, one_mul]
    exact hKK' (eq_of_mem_of_mem hΩ hK hK' hzK (this ▸ hz'K') hz1 hzz)
  have hz₃z' : z₃ ≠ z' := by
    intro h
    apply hz1
    calc z = z'⁻¹ * z₃ := by rw [hz₃def]; group
      _ = 1 := by rw [h, inv_mul_cancel]
  have hz₃K₃ : z₃ ∈ K₃ := hR₃'.le (hU₃'.le hz₃U₃')
  have htz₃ : t * z₃ * t⁻¹ = z₃ := by
    calc t * z₃ * t⁻¹ = (t * z' * t⁻¹) * (t * z * t⁻¹) := by rw [hz₃def]; group
      _ = z * z' := by rw [htz', htz]
      _ = z₃ := hzz'c
  have htK₃ : t ∈ normalizer (K₃ : Set G) := by
    apply Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK₃) hz₃K₃ hz₃1 hz₃z₃
    rw [mem_centralizer_singleton_iff]
    calc t * z₃ = t * z₃ * t⁻¹ * t := by group
      _ = z₃ * t := by rw [htz₃]
  have hK₃D : K₃ ∈ omegaD Ω W := ⟨hK₃, R₃', hR₃', hR₃'W⟩
  have hJK₃ : J ≠ K₃ := fun h => hJD (h ▸ hK₃D)
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  obtain ⟨R₃, hR₃, hR₃W, htR₃⟩ := exists_isSylowOf_le_normalizer_normalized hR₃' hR₃'W htP
    ((zpowers_le).mpr htK₃) ((zpowers_le).mpr htW)
  have htR₃' : t ∈ normalizer (R₃ : Set G) := htR₃ (mem_zpowers t)
  obtain ⟨U₃, hU₃⟩ := Assumption41.exists_rot hΩ hK₃ hR₃
  have hU₃W : U₃ ≤ W := rot_le_sec4W hΩ hS hK₃ hR₃ hU₃ hR₃W
  have hU₃eq : U₃ = U₃' := rot_eq_of_le_sec4W hΩ hS hK₃ hR₃ hU₃ hR₃' hU₃' hU₃W hU₃'W
  have htR₃n : t ∉ R₃ := by
    intro h
    exact ht1 (mem_bot.mp ((Assumption41.inf_eq_bot hΩ hJ hK₃ hJK₃ htP ((zpowers_le).mpr htJ)
      ((zpowers_le).mpr (hR₃.le h))) ▸ mem_inf.mpr ⟨mem_zpowers t, mem_zpowers t⟩))
  have hz₃U₃ : z₃ ∈ U₃ := hU₃eq ▸ hz₃U₃'
  obtain ⟨z₃', -, -, -, hz₃uniq', hz₃R'⟩ := hU₃.exists_involution
  have hz₃eq : z₃ = z₃' := (hz₃uniq' z₃ hz₃U₃ hz₃z₃).resolve_left hz₃1
  have hz₃uniq : ∀ y ∈ U₃, y * y = 1 → y = 1 ∨ y = z₃ := by
    rw [hz₃eq]
    exact hz₃uniq'
  have hz₃R : ∀ y ∈ R₃, y * z₃ = z₃ * y := by
    rw [hz₃eq]
    exact hz₃R'
  obtain ⟨s, hsR₃, hsU₃⟩ := hU₃.exists_not_mem
  have hss : s * s = 1 := hU₃.mul_self s hsR₃ hsU₃
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have hsW : s ∈ normalizer (W : Set G) := hR₃W hsR₃
  set h := t * s with hhdef
  have htst : t * s * t⁻¹ ∈ R₃ := (mem_normalizer_iff.mp htR₃' s).mp hsR₃
  have hconjt : ∀ y : G, t * (t * y * t⁻¹) * t⁻¹ = y := by
    intro y
    calc t * (t * y * t⁻¹) * t⁻¹ = (t * t) * y * (t * t)⁻¹ := by group
      _ = y := by rw [htt]; group
  have hU₃UU' : U₃ ≤ U ⊔ U' := by
    rw [hU₃eq]
    intro y hy
    rw [hU₃'def, mem_rightConjugate_iff] at hy
    set u' := x * y * x⁻¹ with hu'
    have hyeq : y = x⁻¹ * u' * x := by rw [hu']; group
    have hcR : x⁻¹ * (u' * x * u'⁻¹) ∈ R :=
      R.mul_mem (inv_mem hxR) ((mem_normalizer_iff.mp (hU'R hy) x).mp hxR)
    have hyW : y ∈ W := hU₃'W (by rw [hU₃'def, mem_rightConjugate_iff]; exact hy)
    have hcW : x⁻¹ * (u' * x * u'⁻¹) ∈ W := by
      have : x⁻¹ * (u' * x * u'⁻¹) = y * u'⁻¹ := by rw [hyeq]; group
      rw [this]
      exact mul_mem hyW (inv_mem (hU'W hy))
    have hcU : x⁻¹ * (u' * x * u'⁻¹) ∈ U :=
      hU.mem_of_commute hcR fun u hu => hWc _ hcW u (hUW hu)
    have : y = (x⁻¹ * (u' * x * u'⁻¹)) * u' := by rw [hyeq]; group
    rw [this]
    exact mul_mem (mem_sup_left hcU) (mem_sup_right hy)
  have hK₃K : K₃ ≠ K := by
    intro h1
    apply hKK'
    have hz₃K : z₃ ∈ K := h1 ▸ hz₃K₃
    have hz'K : z' ∈ K := by
      have : z' = z₃ * z := by rw [hz₃def, mul_assoc, hzz, mul_one]
      rw [this]
      exact mul_mem hz₃K hzK
    exact eq_of_mem_of_mem hΩ hK hK' hz'K hz'K' hz'1 hz'z'
  have hRK₃ : ¬ R ≤ normalizer (K₃ : Set G) := by
    intro h1
    apply hRK'
    intro r hr
    have h2 := h1 (R.mul_mem (R.mul_mem (inv_mem hxR) hr) hxR)
    rw [hK₃def, normalizer_rightConjugate, mem_rightConjugate_iff] at h2
    have e : x * (x⁻¹ * r * x) * x⁻¹ = r := by group
    rwa [e] at h2
  have hz₃Z : IsZOf R₃ z₃ := ⟨U₃, hU₃, hz₃U₃, hz₃1, hz₃z₃⟩
  have hsz : s⁻¹ * z * s = z' := by
    have h1 := conj_z_of_not_sylow H hS hK₃ hK hK₃K hR₃ hR hR₃W hRW hU₃ hRK₃ hz₃Z hzZ hsR₃
      hsU₃
    rw [h1, hz₃def, ← mul_assoc, hzz'c, mul_assoc, hzz, mul_one]
  have hKs : AschbacherTightEmbedding.rightConjugate K s = K' := by
    have h1 := conj_mem_rightConjugate hzK s
    rw [hsz] at h1
    exact eq_of_mem_of_mem hΩ (hΩ.conj_mem K hK s) hK' h1 hz'K' hz'1 hz'z'
  have hUs : AschbacherTightEmbedding.rightConjugate U s = U' := by
    have hRs := isSylowOf_rightConjugate hR s
    rw [hKs] at hRs
    exact rot_eq_of_le_sec4W hΩ hS hK' hRs (hU.rightConjugate s) hR' hU'
      (rightConjugate_le_of_le_normalizer hUW hsW) hU'W
  have hUU'W : U ⊔ U' ≤ W := sup_le hUW hU'W
  have hab : ∀ a ∈ U ⊔ U', ∀ b ∈ U ⊔ U', a * b = b * a := fun a ha b hb =>
    hWc a (hUU'W ha) b (hUU'W hb)
  have hUU' : U ⊓ U' = ⊥ := Assumption41.inf_eq_bot hΩ hK hK' hKK'
    (hU.isPGroup.to_le hU.le) (hU.le.trans hR.le) (hU'.le.trans hR'.le)
  have hcardU₃ : Nat.card U₃ = Nat.card U := by
    have h1 := hU₃.card_eq
    have h2 := hU.card_eq
    rw [Assumption41.card_sylow_eq hΩ hK₃ hK hR₃ hR] at h1
    omega
  have hconj : ∀ {τ : G}, τ * τ = 1 → AschbacherTightEmbedding.rightConjugate U τ = U' →
      (∀ u ∈ U, τ * u * τ⁻¹ ∈ U') ∧ (∀ u ∈ U', τ * u * τ⁻¹ ∈ U) := by
    intro τ hττ hUτ
    refine ⟨fun u hu => ?_, fun u hu => ?_⟩
    · rw [← hUτ, mem_rightConjugate_iff]
      have e : τ * (τ * u * τ⁻¹) * τ⁻¹ = u := by
        calc τ * (τ * u * τ⁻¹) * τ⁻¹ = (τ * τ) * u * (τ * τ)⁻¹ := by group
          _ = u := by rw [hττ]; group
      rw [e]
      exact hu
    · rw [← hUτ, mem_rightConjugate_iff] at hu
      exact hu
  obtain ⟨htU, htU'⟩ := hconj htt rfl
  obtain ⟨hsU, hsU'⟩ := hconj hss hUs
  have hφs := mul_inv_conj_mem_of_inv hab hUU' hsU hsU' hU₃UU' hU₃.isCyclic
    (fun w hw => hU₃.conj_eq s hsR₃ hsU₃ w hw) hcardU₃
  have hK₃K' : K₃ ≠ K' := by
    intro h1
    have hR₃K' : IsSylowOf 2 R₃ K' := h1 ▸ hR₃
    have := rot_eq_of_le_sec4W hΩ hS hK' hR₃K' hU₃ hR' hU' hU₃W hU'W
    apply hz₃z'
    have hz₃U' : z₃ ∈ U' := this ▸ hz₃U₃
    obtain ⟨z'', -, -, -, hz''uniq, -⟩ := hU'.exists_involution
    have e1 := (hz''uniq z₃ hz₃U' hz₃z₃).resolve_left hz₃1
    have e2 := (hz''uniq z' hz'U' hz'z').resolve_left hz'1
    rw [e1, e2]
  have hU₃U' : U₃ ⊓ U' = ⊥ := Assumption41.inf_eq_bot hΩ hK₃ hK' hK₃K'
    (hU₃.isPGroup.to_le hU₃.le) (hU₃.le.trans hR₃.le) (hU'.le.trans hR'.le)
  have hhW : h ∈ normalizer (W : Set G) := mul_mem htW hsW
  have hP2 : IsPGroup 2 (zpowers t ⊔ R₃ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' htP hR₃.isPGroup ((zpowers_le).mpr htR₃')
  have hhP : h ∈ zpowers t ⊔ R₃ := mul_mem (mem_sup_left (mem_zpowers t)) (mem_sup_right hsR₃)
  have hhP2 : IsPGroup 2 (zpowers h) := hP2.to_le ((zpowers_le).mpr hhP)
  have key : h * z * h⁻¹ = z → ∃ x₀ u₁ : G, u₁ ∈ U ∧ h * x₀ * h⁻¹ = x₀ * u₁ ∧
      x₀⁻¹ * z₃ * x₀ = z' ∧ AschbacherTightEmbedding.rightConjugate U₃ x₀ = U' := by
    intro hhz
    have hhz' : h ∈ centralizer ({z} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc h * z = h * z * h⁻¹ * h := by group
        _ = z * h := by rw [hhz]
    have hhK : h ∈ normalizer (K : Set G) :=
      Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK) hzK hz1 hzz hhz'
    obtain ⟨R0, hR0, hR0W, hhR0⟩ := exists_isSylowOf_le_normalizer_normalized hR hRW hhP2
      ((zpowers_le).mpr hhK) ((zpowers_le).mpr hhW)
    have hhR0' : h ∈ normalizer (R0 : Set G) := hhR0 (mem_zpowers h)
    obtain ⟨U0, hU0⟩ := Assumption41.exists_rot hΩ hK hR0
    have hU0eq : U0 = U := rot_eq_of_le_sec4W hΩ hS hK hR0 hU0 hR hU
      (rot_le_sec4W hΩ hS hK hR0 hU0 hR0W) hUW
    rw [hU0eq] at hU0
    have hhU0 : h ∈ normalizer (U : Set G) := hU0.normalizer_le hhR0'
    obtain ⟨x₀, hx₀R, hx₀U⟩ := hU0.exists_not_mem
    have hhx₀R : h * x₀ * h⁻¹ ∈ R0 := (mem_normalizer_iff.mp hhR0' x₀).mp hx₀R
    have hhx₀U : h * x₀ * h⁻¹ ∉ U := fun h1 => hx₀U ((mem_normalizer_iff.mp hhU0 x₀).mpr h1)
    have hx₀x₀ : x₀ * x₀ = 1 := hU0.mul_self x₀ hx₀R hx₀U
    have hx₀inv : x₀⁻¹ = x₀ := inv_eq_of_mul_eq_one_right hx₀x₀
    set u₁ := x₀⁻¹ * (h * x₀ * h⁻¹) with hu₁def
    have hu₁U : u₁ ∈ U := by
      rw [hu₁def, hx₀inv]
      exact hU0.mul_mem_of_not_mem hx₀R hhx₀R hx₀U hhx₀U
    have hhx₀ : h * x₀ * h⁻¹ = x₀ * u₁ := by rw [hu₁def]; group
    have hx₀W : x₀ ∈ normalizer (W : Set G) := hR0W hx₀R
    have hzZ0 : IsZOf R0 z := ⟨U, hU0, hzU, hz1, hzz⟩
    have hx₀z' : x₀⁻¹ * z' * x₀ = z' * z :=
      conj_z_of_not_sylow H hS hK hK' hKK' hR0 hR' hR0W hR'W hU0 hRt hzZ0 hz'Z hx₀R hx₀U
    have hx₀z : x₀⁻¹ * z * x₀ = z := by
      have hc : x₀ * z = z * x₀ := by
        obtain ⟨z1, hz1U, hz11, hz1z1, hz1uniq, hz1R⟩ := hU0.exists_involution
        have e := (hz1uniq z hzU hzz).resolve_left hz1
        rw [e]
        exact hz1R x₀ hx₀R
      calc x₀⁻¹ * z * x₀ = x₀⁻¹ * (z * x₀) := by group
        _ = x₀⁻¹ * (x₀ * z) := by rw [hc]
        _ = z := by group
    have hx₀z₃ : x₀⁻¹ * z₃ * x₀ = z' := by
      calc x₀⁻¹ * z₃ * x₀ = (x₀⁻¹ * z' * x₀) * (x₀⁻¹ * z * x₀) := by rw [hz₃def]; group
        _ = z' := by rw [hx₀z', hx₀z, mul_assoc, hzz, mul_one]
    have hK₃x : AschbacherTightEmbedding.rightConjugate K₃ x₀ = K' := by
      have h1 := conj_mem_rightConjugate hz₃K₃ x₀
      rw [hx₀z₃] at h1
      exact eq_of_mem_of_mem hΩ (hΩ.conj_mem K₃ hK₃ x₀) hK' h1 hz'K' hz'1 hz'z'
    have hU₃x : AschbacherTightEmbedding.rightConjugate U₃ x₀ = U' := by
      have hR₃x := isSylowOf_rightConjugate hR₃ x₀
      rw [hK₃x] at hR₃x
      exact rot_eq_of_le_sec4W hΩ hS hK' hR₃x (hU₃.rightConjugate x₀) hR' hU'
        (rightConjugate_le_of_le_normalizer hU₃W hx₀W) hU'W
    exact ⟨x₀, u₁, hu₁U, hhx₀, hx₀z₃, hU₃x⟩
  rcases hM.inv_or_cent h22 hJ hJD hT₀ hV₀ htV ht1 htt hK₃D htK₃ hR₃ hU₃ htR₃' with
    ⟨htinvU₃, hD⟩ | ⟨htcU₃, y, hyR₃, hty⟩
  ·
    set g := h * h with hgdef
    have htstU : t * s * t⁻¹ ∉ U₃ := by
      intro h1
      apply hsU₃
      have h2 := htinvU₃ _ h1
      rw [hconjt] at h2
      rw [h2]
      exact inv_mem h1
    have hgU₃ : g ∈ U₃ := by
      have h1 := hU₃.mul_mem_of_not_mem htst hsR₃ htstU hsU₃
      have e : g = t * s * t⁻¹ * s := by rw [hgdef, hhdef, htinv]; group
      rw [e]
      exact h1
    have hgsq := hU₃.not_sq_of_isDihedral htt htR₃n htinvU₃ hD hsR₃ hsU₃
    have hgpow : g ^ (Nat.card U₃ / 2) = z₃ := by
      rcases hU₃.pow_half_eq hz₃uniq hgU₃ with h1 | h1
      · exfalso
        obtain ⟨v, hv, hgv⟩ := hU₃.exists_sq_of_pow_half_eq_one hgU₃ h1
        exact hgsq v hv hgv
      · exact h1
    have hφt := mul_inv_conj_mem_of_inv hab hUU' htU htU' hU₃UU' hU₃.isCyclic htinvU₃ hcardU₃
    have hts : ∀ u ∈ U, t * u * t⁻¹ = s * u * s⁻¹ := by
      intro u hu
      have h1 : (t * u * t⁻¹) * (s * u * s⁻¹)⁻¹ ∈ U₃ ⊓ U' := by
        refine mem_inf.mpr ⟨?_, mul_mem (htU u hu) (inv_mem (hsU u hu))⟩
        have := mul_mem (inv_mem (hφt u hu)) (hφs u hu)
        have e : (u * (t * u * t⁻¹)⁻¹)⁻¹ * (u * (s * u * s⁻¹)⁻¹) =
            (t * u * t⁻¹) * (s * u * s⁻¹)⁻¹ := by group
        rwa [e] at this
      rw [hU₃U', mem_bot] at h1
      exact mul_inv_eq_one.mp h1
    have hhU : ∀ u ∈ U, h * u * h⁻¹ = u := by
      intro u hu
      calc h * u * h⁻¹ = t * (s * u * s⁻¹) * t⁻¹ := by rw [hhdef]; group
        _ = t * (t * u * t⁻¹) * t⁻¹ := by rw [hts u hu]
        _ = u := hconjt u
    obtain ⟨x₀, u₁, hu₁U, hhx₀, -, hU₃x⟩ := key (hhU z hzU)
    have hgx₀ : x₀⁻¹ * g * x₀ = u₁ * u₁ * g := by
      have h1 : g * x₀ * g⁻¹ = x₀ * (u₁ * u₁) := by
        calc g * x₀ * g⁻¹ = h * (h * x₀ * h⁻¹) * h⁻¹ := by rw [hgdef]; group
          _ = h * (x₀ * u₁) * h⁻¹ := by rw [hhx₀]
          _ = (h * x₀ * h⁻¹) * (h * u₁ * h⁻¹) := by group
          _ = x₀ * (u₁ * u₁) := by rw [hhx₀, hhU u₁ hu₁U, mul_assoc]
      calc x₀⁻¹ * g * x₀ = x₀⁻¹ * (g * x₀ * g⁻¹) * g := by group
        _ = u₁ * u₁ * g := by rw [h1]; group
    have hwU' : u₁ * u₁ * g ∈ U' := by
      rw [← hgx₀, ← hU₃x]
      exact conj_mem_rightConjugate hgU₃ x₀
    obtain ⟨z'', -, -, -, hz''uniq, -⟩ := hU'.exists_involution
    have hz'uniq : ∀ y ∈ U', y * y = 1 → y = 1 ∨ y = z' := by
      have e := (hz''uniq z' hz'U' hz'z').resolve_left hz'1
      rw [e]
      exact hz''uniq
    have hcardU' : Nat.card U' = Nat.card U := rightConjugate_card U t
    have hpow := hU'.pow_half_eq hz'uniq hwU'
    rw [hcardU'] at hpow
    have hcomm : Commute (u₁ * u₁) g :=
      hWc _ (hUW (mul_mem hu₁U hu₁U)) g (hU₃W hgU₃)
    obtain ⟨m, hm⟩ := hU.two_dvd_card
    have hm0 : Nat.card U / 2 = m := by omega
    have hu₁pow : (u₁ * u₁) ^ m = 1 := by
      rw [← pow_two, ← pow_mul, ← hm]
      have h1 : (⟨u₁, hu₁U⟩ : U) ^ Nat.card U = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    have hgpow' : g ^ m = z₃ := by rw [← hm0, ← hcardU₃]; exact hgpow
    rw [hm0, hcomm.mul_pow, hu₁pow, one_mul, hgpow'] at hpow
    rcases hpow with h1 | h1
    · exact hz₃1 h1
    · exact hz₃z' h1
  ·
    have htc' : ∀ w ∈ U₃, t⁻¹ * w * t = w := by
      intro w hw
      calc t⁻¹ * w * t = t⁻¹ * (t * w * t⁻¹) * t := by rw [htcU₃ w hw]
        _ = w := by group
    have htstU : t * s * t⁻¹ ∉ U₃ := by
      intro h1
      apply hsU₃
      have e : s = t⁻¹ * (t * s * t⁻¹) * t := by group
      rw [e, htc' _ h1]
      exact h1
    set u := s⁻¹ * (t * s * t⁻¹) with hudef
    have huU₃ : u ∈ U₃ := hU₃.mul_mem_of_not_mem (inv_mem hsR₃) htst
      (by rw [hsinv]; exact hsU₃) htstU
    have htsu : t * s * t⁻¹ = s * u := by rw [hudef]; group
    have huu : u * u = 1 := by
      have h1 : s = s * u * u := by
        calc s = t * (t * s * t⁻¹) * t⁻¹ := (hconjt s).symm
          _ = t * (s * u) * t⁻¹ := by rw [htsu]
          _ = (t * s * t⁻¹) * (t * u * t⁻¹) := by group
          _ = s * u * u := by rw [htsu, htcU₃ u huU₃]
      calc u * u = s⁻¹ * (s * u * u) := by group
        _ = 1 := by rw [← h1, inv_mul_cancel]
    have huz : u = z₃ := by
      rcases hz₃uniq u huU₃ huu with h1 | h1
      · exfalso
        apply hty
        have hts' : t * s * t⁻¹ = s := by rw [htsu, h1, mul_one]
        by_cases hyU : y ∈ U₃
        · exact htcU₃ y hyU
        · have h2 : s⁻¹ * y ∈ U₃ :=
            hU₃.mul_mem_of_not_mem (inv_mem hsR₃) hyR₃ (by rw [hsinv]; exact hsU₃) hyU
          calc t * y * t⁻¹ = (t * s * t⁻¹) * (t * (s⁻¹ * y) * t⁻¹) := by group
            _ = s * (s⁻¹ * y) := by rw [hts', htcU₃ _ h2]
            _ = y := by group
      · exact h1
    have hh2 : h * h = z₃ := by
      calc h * h = (t * s * t⁻¹) * s := by rw [hhdef, htinv]; group
        _ = s * z₃ * s := by rw [htsu, huz]
        _ = z₃ * s * s := by rw [(hz₃R s hsR₃)]
        _ = z₃ := by rw [mul_assoc, hss, mul_one]
    have hhinv : ∀ u ∈ U, h * u * h⁻¹ = u⁻¹ := by
      intro u hu
      set a := t * u * t⁻¹ with hadef
      set b := h * u * h⁻¹ with hbdef
      set c := s * u * s⁻¹ with hcdef
      have haU' : a ∈ U' := htU u hu
      have hcU' : c ∈ U' := hsU u hu
      have hbU : b ∈ U := by
        have h1 := htU' c hcU'
        have e : t * c * t⁻¹ = b := by rw [hcdef, hbdef, hhdef]; group
        rwa [e] at h1
      have hw := htcU₃ _ (hφs u hu)
      have hab' : a * b⁻¹ = u * c⁻¹ := by
        have e : t * (u * c⁻¹) * t⁻¹ = a * b⁻¹ := by
          rw [hadef, hbdef, hcdef, hhdef]; group
        rw [← e]
        exact hw
      have hau : a⁻¹ * u = u * a⁻¹ := hab _ (mem_sup_right (inv_mem haU')) _ (mem_sup_left hu)
      have h1 : u⁻¹ * b⁻¹ ∈ U ⊓ U' := by
        refine mem_inf.mpr ⟨mul_mem (inv_mem hu) (inv_mem hbU), ?_⟩
        have e : u⁻¹ * b⁻¹ = a⁻¹ * c⁻¹ := by
          calc u⁻¹ * b⁻¹ = u⁻¹ * a⁻¹ * (a * b⁻¹) := by group
            _ = u⁻¹ * a⁻¹ * (u * c⁻¹) := by rw [hab']
            _ = u⁻¹ * (a⁻¹ * u) * c⁻¹ := by group
            _ = u⁻¹ * (u * a⁻¹) * c⁻¹ := by rw [hau]
            _ = a⁻¹ * c⁻¹ := by group
        rw [e]
        exact mul_mem (inv_mem haU') (inv_mem hcU')
      rw [hUU', mem_bot] at h1
      calc b = (u⁻¹ * b⁻¹)⁻¹ * u⁻¹ := by group
        _ = u⁻¹ := by rw [h1, inv_one, one_mul]
    have hhz : h * z * h⁻¹ = z := by
      rw [hhinv z hzU, inv_eq_of_mul_eq_one_right hzz]
    obtain ⟨x₀, u₁, hu₁U, hhx₀, hx₀z₃, -⟩ := key hhz
    have hx₀h : x₀⁻¹ * h * x₀ = u₁ * h := by
      calc x₀⁻¹ * h * x₀ = x₀⁻¹ * (h * x₀ * h⁻¹) * h := by group
        _ = x₀⁻¹ * (x₀ * u₁) * h := by rw [hhx₀]
        _ = u₁ * h := by group
    apply hz₃z'
    rw [← hx₀z₃]
    calc z₃ = u₁ * (h * u₁ * h⁻¹) * (h * h) := by rw [hhinv u₁ hu₁U, hh2]; group
      _ = (u₁ * h) * (u₁ * h) := by group
      _ = (x₀⁻¹ * h * x₀) * (x₀⁻¹ * h * x₀) := by rw [hx₀h]
      _ = x₀⁻¹ * z₃ * x₀ := by rw [← hh2]; group

theorem MinCounter.rightConjugate_eq_or_le_normalizer_of_not_mem (h22 : Asc76Lemma22)
    {S : Subgroup G} (hM : MinCounter Ω S) {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω)
    (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀) (ht1 : t ≠ 1)
    (htt : t * t = 1) (htW : t ∈ normalizer (sec4W Ω S : Set G)) (htW' : t ∉ sec4W Ω S)
    {K R : Subgroup G} (hK : K ∈ Ω) (hR : IsSylowOf 2 R K)
    (hRW : R ≤ normalizer (sec4W Ω S : Set G)) :
    AschbacherTightEmbedding.rightConjugate K t = K ∨
      AschbacherTightEmbedding.rightConjugate R t ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  have hJD : J ∉ omegaD Ω (sec4W Ω S) := fun h =>
    htW' (mem_sec4W_of_mem_omegaD hΩ hM.twoNil hS h hT₀ hV₀ htV htW)
  by_contra hcon
  push Not at hcon
  obtain ⟨hKt, hRt⟩ := hcon
  set W := sec4W Ω S
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  have hUW : U ≤ W := rot_le_sec4W hΩ hS hK hR hU hRW
  obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
  set U' := AschbacherTightEmbedding.rightConjugate U t with hU'def
  have hK' := hΩ.conj_mem K hK t
  have hR' : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate R t)
      (AschbacherTightEmbedding.rightConjugate K t) := isSylowOf_rightConjugate hR t
  have hU' : IsDihedralRot U' (AschbacherTightEmbedding.rightConjugate R t) := hU.rightConjugate t
  have hU'W : U' ≤ W := rot_le_sec4W hΩ hS hK' hR' hU' (rightConjugate_le_normalizer hRW htW)
  have hU'K : U' ≤ normalizer (K : Set G) := by
    intro u hu
    apply Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK)
      (hR.le (hU.le hzU)) hz1 hzz
    rw [mem_centralizer_singleton_iff]
    exact sec4W_mul_comm hΩ hS (hU'W hu) (hUW hzU)
  have hU'2 : IsPGroup 2 U' := hU'.isPGroup.to_le hU'.le
  obtain ⟨R₁, hR₁, hR₁W, hU'R₁⟩ := exists_isSylowOf_le_normalizer_normalized hR hRW hU'2 hU'K
    (hU'W.trans le_normalizer)
  obtain ⟨U₁, hU₁⟩ := Assumption41.exists_rot hΩ hK hR₁
  have hU₁eq : U₁ = U := rot_eq_of_le_sec4W hΩ hS hK hR₁ hU₁ hR hU
    (rot_le_sec4W hΩ hS hK hR₁ hU₁ hR₁W) hUW
  rw [hU₁eq] at hU₁
  have hR₁t : ¬ AschbacherTightEmbedding.rightConjugate R₁ t ≤ normalizer (K : Set G) := by
    intro h
    have hKK' : K ≠ AschbacherTightEmbedding.rightConjugate K t := fun h' => hKt h'.symm
    exact hRt (hR'.le.trans (le_normalizer_of_sylow h22 hΩ hK hK' hKK'
      (isSylowOf_rightConjugate hR₁ t) h).1)
  exact hM.false_of_not_le_normalizer_of_not_mem h22 hJ hJD hT₀ hV₀ htV ht1 htt htW hK hR₁ hU₁
    hR₁W hU'R₁ hKt hR₁t

end CFSG.ComponentClassification.Asc76.Sec4
