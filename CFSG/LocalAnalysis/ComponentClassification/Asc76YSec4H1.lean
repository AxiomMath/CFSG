module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D22

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem conj_rightConjugate_eq_of_normalizes {K R' : Subgroup G} (hR' : IsSylowOf 2 R' K)
    {o t : G} (ho : o ∈ oddCoreIn K) (htK : t ∈ normalizer (K : Set G))
    (htR' : t ∈ normalizer (R' : Set G))
    (htR : t ∈ normalizer (AschbacherTightEmbedding.rightConjugate R' o : Set G)) {u : G}
    (hu : u ∈ R') : t * (o⁻¹ * u * o) * t⁻¹ = o⁻¹ * (t * u * t⁻¹) * o := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c := o * t * o⁻¹ * t⁻¹ with hcdef
  have hcO : c ∈ oddCoreIn K := by
    have h1 : t * o⁻¹ * t⁻¹ ∈ oddCoreIn K :=
      (mem_normalizer_iff.mp (normalizer_le_normalizer_oddCoreIn K htK) _).mp (inv_mem ho)
    have e : c = o * (t * o⁻¹ * t⁻¹) := by rw [hcdef]; group
    rw [e]
    exact mul_mem ho h1
  have hcR : ∀ y ∈ R', c * y * c⁻¹ ∈ R' := by
    intro y hy
    have h1 : t⁻¹ * y * t⁻¹⁻¹ ∈ R' := (mem_normalizer_iff.mp (inv_mem htR') y).mp hy
    have h2 : o⁻¹ * (t⁻¹ * y * t⁻¹⁻¹) * o ∈ AschbacherTightEmbedding.rightConjugate R' o := by
      rw [mem_rightConjugate_iff]
      have e : o * (o⁻¹ * (t⁻¹ * y * t⁻¹⁻¹) * o) * o⁻¹ = t⁻¹ * y * t⁻¹⁻¹ := by group
      rw [e]
      exact h1
    have h3 := (mem_normalizer_iff.mp htR _).mp h2
    rw [mem_rightConjugate_iff] at h3
    have e : o * (t * (o⁻¹ * (t⁻¹ * y * t⁻¹⁻¹) * o) * t⁻¹) * o⁻¹ = c * y * c⁻¹ := by
      rw [hcdef]; group
    rwa [e] at h3
  have hbot : R' ⊓ oddCoreIn K = ⊥ :=
    eq_bot_of_isPGroup_of_odd (hR'.isPGroup.to_le inf_le_left)
      ((odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_right))
  have hcy : ∀ y ∈ R', c * y = y * c := by
    intro y hy
    have h1 : c * y * c⁻¹ * y⁻¹ ∈ R' ⊓ oddCoreIn K := by
      refine mem_inf.mpr ⟨mul_mem (hcR y hy) (inv_mem hy), ?_⟩
      have h2 : y * c⁻¹ * y⁻¹ ∈ oddCoreIn K :=
        (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K (hR'.le hy)) _).mp (inv_mem hcO)
      have e : c * y * c⁻¹ * y⁻¹ = c * (y * c⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem hcO h2
    rw [hbot, mem_bot] at h1
    calc c * y = c * y * c⁻¹ * y⁻¹ * (y * c) := by group
      _ = y * c := by rw [h1, one_mul]
  have hcu := hcy _ ((mem_normalizer_iff.mp htR' u).mp hu)
  calc t * (o⁻¹ * u * o) * t⁻¹ = o⁻¹ * c * (t * u * t⁻¹) * c⁻¹ * o := by rw [hcdef]; group
    _ = o⁻¹ * (c * (t * u * t⁻¹)) * c⁻¹ * o := by group
    _ = o⁻¹ * ((t * u * t⁻¹) * c) * c⁻¹ * o := by rw [hcu]
    _ = o⁻¹ * (t * u * t⁻¹) * o := by group

theorem rot_eq_of_le_isPGroup {K R₁ R₂ U₁ U₂ X : Subgroup G} (hR₁ : IsSylowOf 2 R₁ K)
    (hR₂ : IsSylowOf 2 R₂ K) (hnil : IsTwoNil K R₁) (hU₁ : IsDihedralRot U₁ R₁)
    (hU₂ : IsDihedralRot U₂ R₂) (hX : IsPGroup 2 X) (hU₁X : U₁ ≤ X) (hU₂X : U₂ ≤ X) :
    U₁ = U₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨o, ho, hR₂eq⟩ := exists_oddCoreIn_eq_rightConjugate hR₂ hR₁ hnil
  have h1 := hU₁.rightConjugate o
  rw [← hR₂eq] at h1
  have hU₂eq : AschbacherTightEmbedding.rightConjugate U₁ o = U₂ :=
    hU₂.eq_of_isCyclic h1.le h1.isCyclic h1.relIndex_eq
  have hbot : X ⊓ oddCoreIn K = ⊥ :=
    eq_bot_of_isPGroup_of_odd (hX.to_le inf_le_left)
      ((odd_card_oddCoreIn K).of_dvd_nat (card_dvd_of_le inf_le_right))
  have hle : U₂ ≤ U₁ := by
    intro y hy
    have hyK : y ∈ K := hR₂.le (hU₂.le hy)
    have hy' : o * y * o⁻¹ ∈ U₁ := by
      rw [← hU₂eq, mem_rightConjugate_iff] at hy
      exact hy
    have hd : o * y * o⁻¹ * y⁻¹ ∈ X ⊓ oddCoreIn K := by
      refine mem_inf.mpr ⟨mul_mem (hU₁X hy') (inv_mem (hU₂X (by exact hy))), ?_⟩
      have h2 : y * o⁻¹ * y⁻¹ ∈ oddCoreIn K :=
        (mem_normalizer_iff.mp (le_normalizer_oddCoreIn K hyK) _).mp (inv_mem ho)
      have e : o * y * o⁻¹ * y⁻¹ = o * (y * o⁻¹ * y⁻¹) := by group
      rw [e]
      exact mul_mem ho h2
    rw [hbot, mem_bot] at hd
    have e : y = o * y * o⁻¹ := by
      calc y = (o * y * o⁻¹ * y⁻¹)⁻¹ * (o * y * o⁻¹) := by group
        _ = o * y * o⁻¹ := by rw [hd, inv_one, one_mul]
    rw [e]
    exact hy'
  have hcard : Nat.card U₁ ≤ Nat.card U₂ := by
    have h1 := hU₁.card_eq
    have h2 := hU₂.card_eq
    rw [hR₁.card_eq] at h1
    rw [hR₂.card_eq] at h2
    omega
  exact (eq_of_le_of_card_ge hle hcard).symm

theorem mem_sec4W_of_mem_centralizer (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω) (hT₀ : IsSylowOf 2 T₀ J)
    (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀)
    (htC : t ∈ centralizer (sec4W Ω S : Set G)) : t ∈ sec4W Ω S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  obtain ⟨S', hS', hT₀S'⟩ := exists_isSylowOf_le hT₀.isPGroup (le_top : T₀ ≤ ⊤)
  obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem hS hS'
  have hS'eq : S' = AschbacherTightEmbedding.rightConjugate S k⁻¹ := by
    ext x
    rw [mem_rightConjugate_iff, inv_inv, hk]
  have htW' : t ∈ sec4W Ω S' := le_sec4W (hV₀.le.trans hT₀S') (isRot_of hJ hT₀ hV₀) htV
  rw [hS'eq, ← rightConjugate_sec4W hΩ.conj_mem S k⁻¹, mem_rightConjugate_iff, inv_inv] at htW'
  set w := k⁻¹ * t * k with hwdef
  have hwt : k * w * k⁻¹ = t := by rw [hwdef]; group
  obtain ⟨n, hn, hnw⟩ := exists_mem_normalizer_conj_eq hΩ hS (A := {w}) (h := k⁻¹)
    (fun a ha w' hw' => by
      rw [Set.mem_singleton_iff] at ha
      rw [ha]
      exact sec4W_comm hΩ hS htW' hw')
    (fun a ha w' hw' => by
      rw [Set.mem_singleton_iff] at ha
      rw [ha, inv_inv, hwt]
      exact (mem_centralizer_iff.mp htC w' hw').symm)
  have h1 := hnw w (Set.mem_singleton w)
  rw [inv_inv, hwt] at h1
  rw [h1]
  have := (mem_normalizer_iff.mp (inv_mem hn) w).mp htW'
  rwa [inv_inv] at this

theorem commute_dBar_of_normalizes (H : Sec4Hyp Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {t : normalizer (sec4W Ω S : Set G)}
    (hH : ∀ K ∈ omegaD Ω (sec4W Ω S), AschbacherTightEmbedding.rightConjugate K t = K)
    {d : NBar (sec4W Ω S)} (hd : d ∈ DBar Ω (sec4W Ω S)) :
    (t : NBar (sec4W Ω S)) * d = d * t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, ⟨⟨L, hL, hTL⟩, hTW⟩, hTd⟩ := DBar.exists_isBarOf hd
  have hLt := hH L ⟨hL, T, hTL, hTW⟩
  have hd' := hTd.rightConjugate t
  have hT' : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate T t) L := by
    have := isSylowOf_rightConjugate hTL (t : G)
    rwa [hLt] at this
  have e := bar_eq_of_same H hS hL hTL hT' hTW (rightConjugate_le_normalizer hTW t.2) hTd hd'
  calc (t : NBar (sec4W Ω S)) * d = t * ((t : NBar (sec4W Ω S))⁻¹ * d * t) := by rw [← e]
    _ = d * t := by group

theorem MinCounter.exists_transfer (h22 : Asc76Lemma22) {S : Subgroup G} (hM : MinCounter Ω S)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) {t : G}
    (htW : t ∈ normalizer (sec4W Ω S : Set G))
    (hH : ∀ K ∈ omegaD Ω (sec4W Ω S), AschbacherTightEmbedding.rightConjugate K t = K)
    {K₁ R₁ U₁ K₂ R₂ U₂ : Subgroup G} (hK₁ : K₁ ∈ Ω) (hR₁ : IsSylowOf 2 R₁ K₁)
    (hR₁W : R₁ ≤ normalizer (sec4W Ω S : Set G)) (hU₁ : IsDihedralRot U₁ R₁) (hK₂ : K₂ ∈ Ω)
    (hR₂ : IsSylowOf 2 R₂ K₂) (hR₂W : R₂ ≤ normalizer (sec4W Ω S : Set G))
    (hU₂ : IsDihedralRot U₂ R₂) :
    ∃ n ∈ normalizer (sec4W Ω S : Set G), AschbacherTightEmbedding.rightConjugate U₁ n = U₂ ∧
      ∀ u ∈ U₁, t * (n⁻¹ * u * n) * t⁻¹ = n⁻¹ * (t * u * t⁻¹) * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  have H : Sec4Hyp Ω := ⟨h22, hΩ, hM.twoNil⟩
  set W := sec4W Ω S with hWdef
  set t' : normalizer (W : Set G) := ⟨t, htW⟩ with ht'def
  have hR₁D : R₁ ∈ DSet Ω W := ⟨⟨K₁, hK₁, hR₁⟩, hR₁W⟩
  have hR₂D : R₂ ∈ DSet Ω W := ⟨⟨K₂, hK₂, hR₂⟩, hR₂W⟩
  obtain ⟨d₁, hd₁⟩ := IsBarOf.exists_of_mem hΩ hR₁D
  obtain ⟨d₂, hd₂⟩ := IsBarOf.exists_of_mem hΩ hR₂D
  have hd₁D := IsBarOf.mem_dBar hR₁D hd₁
  have hd₂D := IsBarOf.mem_dBar hR₂D hd₂
  have hcomm : ∀ c ∈ MBar Ω W, (t' : NBar W) * c = c * t' := by
    intro c hc
    have hle : MBar Ω W ≤ centralizer ({(t' : NBar W)} : Set (NBar W)) := by
      refine (closure_le _).mpr fun d hd => ?_
      rw [SetLike.mem_coe, mem_centralizer_singleton_iff]
      exact (commute_dBar_of_normalizes H hS hH hd).symm
    exact (mem_centralizer_singleton_iff.mp (hle hc)).symm
  obtain ⟨φ, -, -, -, -, hconj⟩ := DBar.exists_hom_perm_three H hS ⟨K₁, hK₁⟩ hdis
  have hDM : DBar Ω W ⊆ (MBar Ω W : Set (NBar W)) := subset_closure
  obtain ⟨c, hc⟩ := isConj_iff.mp (hconj ⟨d₁, hDM hd₁D⟩ ⟨d₂, hDM hd₂D⟩ hd₁D hd₂D)
  have hc' : (c : NBar W) * d₁ * (c : NBar W)⁻¹ = d₂ := congrArg Subtype.val hc
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (c : NBar W)
  set n : normalizer (W : Set G) := m⁻¹ with hndef
  have hnbar : (n : NBar W) = (c : NBar W)⁻¹ := by
    rw [hndef, QuotientGroup.mk_inv, hm]
  have hd' : IsBarOf W (AschbacherTightEmbedding.rightConjugate R₁ n) d₂ := by
    have h1 := hd₁.rightConjugate n
    rwa [hnbar, inv_inv, hc'] at h1
  have hR₁'W : AschbacherTightEmbedding.rightConjugate R₁ n ≤ normalizer (W : Set G) :=
    rightConjugate_le_normalizer hR₁W n.2
  have hKeq : AschbacherTightEmbedding.rightConjugate K₁ n = K₂ :=
    eq_of_isBarOf H hS (hΩ.conj_mem K₁ hK₁ n) hK₂ (isSylowOf_rightConjugate hR₁ n) hR₂ hR₁'W
      hR₂W hd' hd₂
  have hR₁' : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate R₁ n) K₂ := by
    have := isSylowOf_rightConjugate hR₁ (n : G)
    rwa [hKeq] at this
  have hU₁W : U₁ ≤ W := rot_le_sec4W hΩ hS hK₁ hR₁ hU₁ hR₁W
  have hU₂W : U₂ ≤ W := rot_le_sec4W hΩ hS hK₂ hR₂ hU₂ hR₂W
  have hUeq : AschbacherTightEmbedding.rightConjugate U₁ n = U₂ :=
    rot_eq_of_le_isPGroup hR₁' hR₂ (hM.twoNil K₂ hK₂ _ hR₁') (hU₁.rightConjugate n) hU₂
      (sec4W_isPGroup hS) (rightConjugate_le_of_le_normalizer hU₁W n.2) hU₂W
  have hnt : (n : NBar W) * t' = t' * n := by
    rw [hnbar]
    exact (hcomm _ (inv_mem c.2)).symm
  have he : (n : G) * t * (n : G)⁻¹ * t⁻¹ ∈ centralizer (W : Set G) := by
    have h1 : ((n * t' * n⁻¹ * t'⁻¹ : normalizer (W : Set G)) : NBar W) = 1 := by
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [hnt]
      group
    have h2 := (mk_eq_one_iff _).mp h1
    simpa [ht'def] using h2
  refine ⟨n, n.2, hUeq, fun u hu => ?_⟩
  set e := (n : G) * t * (n : G)⁻¹ * t⁻¹ with hedef
  have htu : t * u * t⁻¹ ∈ W := (mem_normalizer_iff.mp htW u).mp (hU₁W hu)
  have hec : e * (t * u * t⁻¹) = (t * u * t⁻¹) * e :=
    (mem_centralizer_iff.mp he _ htu).symm
  calc t * ((n : G)⁻¹ * u * n) * t⁻¹ = (n : G)⁻¹ * e * (t * u * t⁻¹) * e⁻¹ * n := by
        rw [hedef]; group
    _ = (n : G)⁻¹ * (e * (t * u * t⁻¹)) * e⁻¹ * n := by group
    _ = (n : G)⁻¹ * ((t * u * t⁻¹) * e) * e⁻¹ * n := by rw [hec]
    _ = (n : G)⁻¹ * (t * u * t⁻¹) * n := by group

theorem MinCounter.conj_eq_inv_of_transfer (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) {t : G}
    (htW : t ∈ normalizer (sec4W Ω S : Set G))
    (hH : ∀ K ∈ omegaD Ω (sec4W Ω S), AschbacherTightEmbedding.rightConjugate K t = K)
    {K₁ R₁ U₁ K₂ R₂ U₂ : Subgroup G} (hK₁ : K₁ ∈ Ω) (hR₁ : IsSylowOf 2 R₁ K₁)
    (hR₁W : R₁ ≤ normalizer (sec4W Ω S : Set G)) (hU₁ : IsDihedralRot U₁ R₁) (hK₂ : K₂ ∈ Ω)
    (hR₂ : IsSylowOf 2 R₂ K₂) (hR₂W : R₂ ≤ normalizer (sec4W Ω S : Set G))
    (hU₂ : IsDihedralRot U₂ R₂) (hinv : ∀ u ∈ U₁, t * u * t⁻¹ = u⁻¹) :
    ∀ y ∈ U₂, t * y * t⁻¹ = y⁻¹ := by
  obtain ⟨n, -, hUeq, htr⟩ := hM.exists_transfer h22 hdis htW hH hK₁ hR₁ hR₁W hU₁ hK₂ hR₂ hR₂W hU₂
  intro y hy
  rw [← hUeq, mem_rightConjugate_iff] at hy
  have e : y = n⁻¹ * (n * y * n⁻¹) * n := by group
  rw [e, htr _ hy, hinv _ hy]
  group

theorem MinCounter.conj_eq_self_of_transfer (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) {t : G}
    (htW : t ∈ normalizer (sec4W Ω S : Set G))
    (hH : ∀ K ∈ omegaD Ω (sec4W Ω S), AschbacherTightEmbedding.rightConjugate K t = K)
    {K₁ R₁ U₁ K₂ R₂ U₂ : Subgroup G} (hK₁ : K₁ ∈ Ω) (hR₁ : IsSylowOf 2 R₁ K₁)
    (hR₁W : R₁ ≤ normalizer (sec4W Ω S : Set G)) (hU₁ : IsDihedralRot U₁ R₁) (hK₂ : K₂ ∈ Ω)
    (hR₂ : IsSylowOf 2 R₂ K₂) (hR₂W : R₂ ≤ normalizer (sec4W Ω S : Set G))
    (hU₂ : IsDihedralRot U₂ R₂) (hcen : ∀ u ∈ U₁, t * u * t⁻¹ = u) :
    ∀ y ∈ U₂, t * y * t⁻¹ = y := by
  obtain ⟨n, -, hUeq, htr⟩ := hM.exists_transfer h22 hdis htW hH hK₁ hR₁ hR₁W hU₁ hK₂ hR₂ hR₂W hU₂
  intro y hy
  rw [← hUeq, mem_rightConjugate_iff] at hy
  have e : y = n⁻¹ * (n * y * n⁻¹) * n := by group
  rw [e, htr _ hy, hcen _ hy]

theorem MinCounter.card_le_two_of_inv (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) {J M R U : Subgroup G} (hJ : J ∈ Ω)
    (hJD : J ∉ omegaD Ω (sec4W Ω S)) (hMD : M ∈ omegaD Ω (sec4W Ω S))
    (hR : IsSylowOf 2 R M) (hU : IsDihedralRot U R) {t : G} (htJ : t ∈ J) (ht1 : t ≠ 1)
    (htt : t * t = 1) (htM : t ∈ normalizer (M : Set G)) (htR : t ∈ normalizer (R : Set G))
    (hinv : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹) {Q : Subgroup G} (hQ : IsPGroup 2 Q) (hQJ : Q ≤ J)
    (hQM : Q ≤ normalizer (M : Set G)) : Nat.card Q ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hMΩ := hMD.1
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  obtain ⟨V₁, hV₁, htV₁⟩ := exists_isSylowOf_le htP
    ((zpowers_le).mpr (mem_inf.mpr ⟨htJ, htM⟩) : zpowers t ≤ J ⊓ normalizer (M : Set G))
  have htV : t ∈ V₁ := htV₁ (mem_zpowers t)
  have hV₁1 : V₁ ≠ ⊥ := fun h => ht1 (mem_bot.mp (h ▸ htV))
  obtain ⟨R₁, hR₁, hV₁R₁⟩ :=
    exists_isSylowOf_normalized hV₁.isPGroup (hV₁.le.trans inf_le_right)
  obtain ⟨U₁, hU₁⟩ := Assumption41.exists_rot hΩ hMΩ hR₁
  have hcard : Nat.card V₁ = 2 := by
    rcases lemma415 h22 hΩ hMΩ hJ hR₁ hU₁ hV₁ hV₁1 hV₁R₁ with ⟨-, hJM, -⟩ |
      ⟨-, hcomm, -, -⟩ | ⟨h2, -, -⟩
    · exact absurd (hM.mem_omegaD_of_le_normalizer hMD hJ hJM) hJD
    · exfalso
      have htc : ∀ u ∈ U₁, t * u * t⁻¹ = u := by
        intro u hu
        have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) htV
        rw [← (mem_centralizer_iff.mp h1) u hu]
        group
      obtain ⟨o, ho, hR₁eq⟩ := exists_oddCoreIn_eq_rightConjugate hR₁ hR (hM.twoNil M hMΩ R hR)
      have h1 := hU.rightConjugate o
      rw [← hR₁eq] at h1
      have hU₁eq : AschbacherTightEmbedding.rightConjugate U o = U₁ :=
        hU₁.eq_of_isCyclic h1.le h1.isCyclic h1.relIndex_eq
      have htR₁ : t ∈ normalizer (AschbacherTightEmbedding.rightConjugate R o : Set G) := by
        rw [← hR₁eq]
        exact hV₁R₁ htV
      obtain ⟨ρ, hρ, hρo⟩ := hU.exists_gen
      have hρU : ρ ∈ U := hρ ▸ mem_zpowers ρ
      have hmem : o⁻¹ * ρ * o ∈ U₁ := hU₁eq ▸ conj_mem_rightConjugate hρU o
      have h2 := conj_rightConjugate_eq_of_normalizes hR ho htM htR htR₁ (hU.le hρU)
      rw [hinv ρ hρU, htc _ hmem] at h2
      have h3 : ρ = ρ⁻¹ := mul_left_cancel (mul_right_cancel h2)
      apply hU.gen_mul_self_ne_one hρo
      calc ρ * ρ = ρ * ρ⁻¹ := by rw [← h3]
        _ = 1 := mul_inv_cancel ρ
    · exact h2
  obtain ⟨V', hV', hQV'⟩ := exists_isSylowOf_le hQ (le_inf hQJ hQM)
  have hV'card : Nat.card V' = Nat.card V₁ := by rw [hV'.card_eq, hV₁.card_eq]
  calc Nat.card Q ≤ Nat.card V' := card_le_of_le hQV'
    _ = 2 := by rw [hV'card, hcard]

theorem MinCounter.conj_eq_inv_of_mem_omegaD (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) {J M R U : Subgroup G} (hJ : J ∈ Ω)
    (hJD : J ∉ omegaD Ω (sec4W Ω S)) (hMD : M ∈ omegaD Ω (sec4W Ω S))
    (hR : IsSylowOf 2 R M) (hU : IsDihedralRot U R) {t : G} (htJ : t ∈ J) (ht1 : t ≠ 1)
    (htt : t * t = 1) (htM : t ∈ normalizer (M : Set G)) (htR : t ∈ normalizer (R : Set G))
    (hinv : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹) {v : G} (hvM : v ∈ M) (hv1 : v ≠ 1) (hvv : v * v = 1)
    (hvJ : v ∈ normalizer (J : Set G)) {T V : Subgroup G} (hT : IsSylowOf 2 T J)
    (hV : IsDihedralRot V T) (hvT : v ∈ normalizer (T : Set G)) :
    ∀ y ∈ V, v * y * v⁻¹ = y⁻¹ := by
  have hnot : ¬ DStarAdj Ω J M := by
    rintro ⟨-, -, -, R', U', hR', hU', hU'M⟩
    have h1 := hM.card_le_two_of_inv h22 hJ hJD hMD hR hU htJ ht1 htt htM htR hinv
      (hR'.isPGroup.to_le hU'.le) (hU'.le.trans hR'.le) hU'M
    have h2 := hU'.four_le
    omega
  exact conj_eq_inv_of_not_dStarAdj h22 hM.assumption hMD.1 hJ hnot hvM hv1 hvv hvJ hT hV hvT

theorem exists_not_commute_of_not_connected (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hΩne : Ω.Nonempty)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) :
    ∃ d₁ ∈ DBar Ω (sec4W Ω S), ∃ d₂ ∈ DBar Ω (sec4W Ω S), d₁ * d₂ ≠ d₂ * d₁ := by
  by_contra hcon
  push Not at hcon
  apply hdis
  obtain ⟨d₀, hd₀⟩ := DBar.nonempty hΩ hS hΩne
  have : Nonempty (DBar Ω (sec4W Ω S)) := ⟨⟨d₀, hd₀⟩⟩
  refine ⟨fun a b => ?_⟩
  by_cases hab : a = b
  · subst hab
    exact SimpleGraph.Reachable.refl _
  · exact SimpleGraph.Adj.reachable ⟨hab, hcon a a.2 b b.2⟩

theorem MinCounter.false_of_situationH (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected)
    {J T₀ V₀ : Subgroup G} (hJ : J ∈ Ω) (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀)
    {t : G} (htV : t ∈ V₀) (ht1 : t ≠ 1) (htt : t * t = 1)
    (htW : t ∈ normalizer (sec4W Ω S : Set G)) (htW' : t ∉ sec4W Ω S)
    (hH : ∀ K ∈ omegaD Ω (sec4W Ω S), AschbacherTightEmbedding.rightConjugate K t = K) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  have H : Sec4Hyp Ω := ⟨h22, hΩ, hM.twoNil⟩
  set W := sec4W Ω S with hWdef
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  have hJD : J ∉ omegaD Ω W := fun hJD =>
    htW' (mem_sec4W_of_mem_omegaD hΩ hM.twoNil hS hJD hT₀ hV₀ htV htW)
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  have htWz : zpowers t ≤ normalizer (W : Set G) := (zpowers_le).mpr htW
  have htN : ∀ K ∈ omegaD Ω W, t ∈ normalizer (K : Set G) := fun K hK =>
    (rightConjugate_eq_self_iff K t).mp (hH K hK)
  have hSyl : ∀ K ∈ omegaD Ω W, ∃ R, IsSylowOf 2 R K ∧ R ≤ normalizer (W : Set G) ∧
      t ∈ normalizer (R : Set G) := by
    rintro K ⟨hKΩ, R₀, hR₀, hR₀W⟩
    obtain ⟨R, hR, hRW, hRt⟩ := exists_isSylowOf_le_normalizer_normalized hR₀ hR₀W htP
      ((zpowers_le).mpr (htN K ⟨hKΩ, R₀, hR₀, hR₀W⟩)) htWz
    exact ⟨R, hR, hRW, hRt (mem_zpowers t)⟩
  obtain ⟨K₀, hK₀, -⟩ := hM.single
  obtain ⟨d₁, hd₁, d₂, hd₂, hnc⟩ := exists_not_commute_of_not_connected hΩ hS ⟨K₀, hK₀⟩ hdis
  obtain ⟨T₁, ⟨⟨K₁, hK₁, hT₁⟩, hT₁W⟩, hT₁d⟩ := DBar.exists_isBarOf hd₁
  obtain ⟨T₂, ⟨⟨K₂, hK₂, hT₂⟩, hT₂W⟩, hT₂d⟩ := DBar.exists_isBarOf hd₂
  have hK₁D : K₁ ∈ omegaD Ω W := ⟨hK₁, T₁, hT₁, hT₁W⟩
  have hK₂D : K₂ ∈ omegaD Ω W := ⟨hK₂, T₂, hT₂, hT₂W⟩
  obtain ⟨R₁, hR₁, hR₁W, htR₁⟩ := hSyl K₁ hK₁D
  obtain ⟨R₂, hR₂, hR₂W, htR₂⟩ := hSyl K₂ hK₂D
  have hR₁D : R₁ ∈ DSet Ω W := ⟨⟨K₁, hK₁, hR₁⟩, hR₁W⟩
  have hR₂D : R₂ ∈ DSet Ω W := ⟨⟨K₂, hK₂, hR₂⟩, hR₂W⟩
  obtain ⟨e₁, he₁⟩ := IsBarOf.exists_of_mem hΩ hR₁D
  obtain ⟨e₂, he₂⟩ := IsBarOf.exists_of_mem hΩ hR₂D
  have he₁d : e₁ = d₁ := bar_eq_of_same H hS hK₁ hR₁ hT₁ hR₁W hT₁W he₁ hT₁d
  have he₂d : e₂ = d₂ := bar_eq_of_same H hS hK₂ hR₂ hT₂ hR₂W hT₂W he₂ hT₂d
  rw [he₁d] at he₁
  rw [he₂d] at he₂
  obtain ⟨U₁, hU₁⟩ := Assumption41.exists_rot hΩ hK₁ hR₁
  obtain ⟨U₂, hU₂⟩ := Assumption41.exists_rot hΩ hK₂ hR₂
  rcases hM.inv_or_cent h22 hJ hJD hT₀ hV₀ htV ht1 htt hK₁D (htN K₁ hK₁D) hR₁ hU₁ htR₁ with
    ⟨hinv₁, -⟩ | ⟨hcen₁, -⟩
  swap
  ·
    apply htW'
    apply mem_sec4W_of_mem_centralizer hΩ hS hJ hT₀ hV₀ htV
    have hle : W ≤ centralizer ({t} : Set G) := by
      refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
      obtain ⟨K, hK, R₀, hR₀, hU'⟩ := IsRot.exists_isDihedralRot hΩ hU
      have hUW : U ≤ W := le_sec4W hUS hU
      obtain ⟨R, hR, hUR, hRW⟩ := exists_isSylowOf_le_normalizer_of_isRot hΩ hS hK hR₀ hU' hUW
      have hc := hM.conj_eq_self_of_transfer h22 hdis htW hH hK₁ hR₁ hR₁W hU₁ hK hR hRW hUR
        hcen₁
      intro u hu
      rw [mem_centralizer_singleton_iff]
      have h1 := hc u hu
      calc u * t = (t * u * t⁻¹) * t := by rw [h1]
        _ = t * u := by group
    rw [mem_centralizer_iff]
    intro w hw
    exact mem_centralizer_singleton_iff.mp (hle hw)
  have hinvAll : ∀ K R U : Subgroup G, K ∈ Ω → IsSylowOf 2 R K → R ≤ normalizer (W : Set G) →
      IsDihedralRot U R → ∀ u ∈ U, t * u * t⁻¹ = u⁻¹ := fun K R U hK hR hRW hU =>
    hM.conj_eq_inv_of_transfer h22 hdis htW hH hK₁ hR₁ hR₁W hU₁ hK hR hRW hU hinv₁
  obtain ⟨z₁, hz₁U, hz₁1, hz₁z₁, -, -⟩ := hU₁.exists_involution
  obtain ⟨z₂, hz₂U, hz₂1, hz₂z₂, -, -⟩ := hU₂.exists_involution
  obtain ⟨x, hxR, hxU⟩ := hU₁.exists_not_mem
  have hx := conj_z_of_not_commute H hS hR₁D hR₂D hU₁ ⟨U₁, hU₁, hz₁U, hz₁1, hz₁z₁⟩
    ⟨U₂, hU₂, hz₂U, hz₂1, hz₂z₂⟩ he₁ he₂ hnc hxR hxU
  have hxW : x ∈ normalizer (W : Set G) := hR₁W hxR
  have hK₃D : AschbacherTightEmbedding.rightConjugate K₂ x ∈ omegaD Ω W :=
    ⟨hΩ.conj_mem K₂ hK₂ x, _, isSylowOf_rightConjugate hR₂ x,
      rightConjugate_le_normalizer hR₂W hxW⟩
  have hz₃K : z₂ * z₁ ∈ AschbacherTightEmbedding.rightConjugate K₂ x :=
    hx ▸ conj_mem_rightConjugate (hR₂.le (hU₂.le hz₂U)) x
  obtain ⟨R₃, hR₃, hR₃W, htR₃⟩ := hSyl _ hK₃D
  obtain ⟨U₃, hU₃⟩ := Assumption41.exists_rot hΩ hK₃D.1 hR₃
  have hW₁ : z₁ ∈ W := rot_le_sec4W hΩ hS hK₁ hR₁ hU₁ hR₁W hz₁U
  have hW₂ : z₂ ∈ W := rot_le_sec4W hΩ hS hK₂ hR₂ hU₂ hR₂W hz₂U
  have hzz : z₂ * z₁ = z₁ * z₂ := sec4W_comm hΩ hS hW₂ hW₁
  have hz12 : z₂ ≠ z₁ := by
    intro e
    apply hz₂1
    have h1 : x⁻¹ * z₂ * x = 1 := by rw [hx, e, hz₁z₁]
    calc z₂ = x * (x⁻¹ * z₂ * x) * x⁻¹ := by group
      _ = 1 := by rw [h1]; group
  have hE4 : Nat.card (fourGroup z₂ z₁ hz₂z₂ hz₁z₁ hzz) = 4 :=
    card_fourGroup hz₂z₂ hz₁z₁ hzz hz₂1 hz₁1 hz12
  have hE2 : IsPGroup 2 (fourGroup z₂ z₁ hz₂z₂ hz₁z₁ hzz) :=
    IsPGroup.of_card (n := 2) (by rw [hE4]; norm_num)
  have hcomm_inv : ∀ z : G, z * z = 1 → t * z * t⁻¹ = z⁻¹ → t * z = z * t := by
    intro z hzz' h
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz'
    calc t * z = t * z * t⁻¹ * t := by group
      _ = z * t := by rw [h, hzinv]
  have htz₁ : t * z₁ = z₁ * t := hcomm_inv z₁ hz₁z₁ (hinv₁ z₁ hz₁U)
  have htz₂ : t * z₂ = z₂ * t :=
    hcomm_inv z₂ hz₂z₂ (hinvAll K₂ R₂ U₂ hK₂ hR₂ hR₂W hU₂ z₂ hz₂U)
  have hEt : fourGroup z₂ z₁ hz₂z₂ hz₁z₁ hzz ≤ centralizer ({t} : Set G) := by
    intro e he
    rw [mem_centralizer_singleton_iff]
    rcases mem_fourGroup.mp he with rfl | rfl | rfl | rfl
    · group
    · exact htz₂.symm
    · exact htz₁.symm
    · calc z₂ * z₁ * t = z₂ * (z₁ * t) := by group
        _ = z₂ * (t * z₁) := by rw [htz₁]
        _ = (z₂ * t) * z₁ := by group
        _ = (t * z₂) * z₁ := by rw [htz₂]
        _ = t * (z₂ * z₁) := by group
  have hJt : centralizer ({t} : Set G) ≤ normalizer (J : Set G) :=
    Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) htJ ht1 htt
  obtain ⟨T, hT, hET⟩ := exists_isSylowOf_normalized hE2 (hEt.trans hJt)
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hJ hT
  have hinvV : ∀ (M R U : Subgroup G) (v : G), M ∈ omegaD Ω W → IsSylowOf 2 R M →
      R ≤ normalizer (W : Set G) → IsDihedralRot U R → t ∈ normalizer (R : Set G) → v ∈ M →
      v ≠ 1 → v * v = 1 → v ∈ fourGroup z₂ z₁ hz₂z₂ hz₁z₁ hzz → ∀ y ∈ V, v * y * v⁻¹ = y⁻¹ := by
    intro M R U v hMD hR hRW hU htR hvM hv1 hvv hvE
    exact hM.conj_eq_inv_of_mem_omegaD h22 hJ hJD hMD hR hU htJ ht1 htt (htN M hMD) htR
      (hinvAll M R U hMD.1 hR hRW hU) hvM hv1 hvv (hJt (hEt hvE)) hT hV (hET hvE)
  have h1 := hinvV K₁ R₁ U₁ z₁ hK₁D hR₁ hR₁W hU₁ htR₁ (hR₁.le (hU₁.le hz₁U)) hz₁1 hz₁z₁
    (mem_fourGroup.mpr (Or.inr (Or.inr (Or.inl rfl))))
  have h2 := hinvV K₂ R₂ U₂ z₂ hK₂D hR₂ hR₂W hU₂ htR₂ (hR₂.le (hU₂.le hz₂U)) hz₂1 hz₂z₂
    (mem_fourGroup.mpr (Or.inr (Or.inl rfl)))
  have hz₃1 : z₂ * z₁ ≠ 1 := by
    intro e
    apply hz12
    calc z₂ = z₂ * z₁ * z₁ := by rw [mul_assoc, hz₁z₁, mul_one]
      _ = z₁ := by rw [e, one_mul]
  have hz₃z₃ : z₂ * z₁ * (z₂ * z₁) = 1 := by
    calc z₂ * z₁ * (z₂ * z₁) = z₂ * (z₁ * z₂) * z₁ := by group
      _ = z₂ * (z₂ * z₁) * z₁ := by rw [hzz]
      _ = (z₂ * z₂) * (z₁ * z₁) := by group
      _ = 1 := by rw [hz₂z₂, hz₁z₁, one_mul]
  have h3 := hinvV _ R₃ U₃ (z₂ * z₁) hK₃D hR₃ hR₃W hU₃ htR₃ hz₃K hz₃1 hz₃z₃
    (mem_fourGroup.mpr (Or.inr (Or.inr (Or.inr rfl))))
  obtain ⟨w, hw, hwo⟩ := hV.exists_gen
  have hwV : w ∈ V := hw ▸ mem_zpowers w
  apply hV.gen_mul_self_ne_one hwo
  have e1 : z₂ * z₁ * w * (z₂ * z₁)⁻¹ = w := by
    calc z₂ * z₁ * w * (z₂ * z₁)⁻¹ = z₂ * (z₁ * w * z₁⁻¹) * z₂⁻¹ := by group
      _ = (z₂ * w * z₂⁻¹)⁻¹ := by rw [h1 w hwV]; group
      _ = w := by rw [h2 w hwV, inv_inv]
  rw [h3 w hwV] at e1
  calc w * w = w⁻¹ * w := by rw [e1]
    _ = 1 := inv_mul_cancel w

theorem MinCounter.mem_sec4W_of_isZInv_of_not_connected (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S)
    (hdis : ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) {t : G}
    (htZ : IsZInv Ω t) (htW : t ∈ normalizer (sec4W Ω S : Set G)) : t ∈ sec4W Ω S := by
  by_contra htW'
  obtain ⟨J, hJ, T₀, V₀, hT₀, hV₀, htV, ht1, htt⟩ := htZ
  exact hM.false_of_situationH h22 hdis hJ hT₀ hV₀ htV ht1 htt htW htW' fun K hK =>
    hM.rightConjugate_eq_of_mem_omegaD_of_not_mem h22 hJ hT₀ hV₀ htV ht1 htt htW htW' hK

end CFSG.ComponentClassification.Asc76.Sec4
