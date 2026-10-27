module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D9

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem MinCounter.of_sylow {S S' : Subgroup G} (hM : MinCounter Ω S) (hS' : IsSylowOf 2 S' ⊤) :
    MinCounter Ω S' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  refine ⟨hΩ, hM.twoNil, hS', hM.single, ?_, hM.ihQuot⟩
  intro hn
  apply hM.not_normal
  obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem hM.sylow hS'
  have hS'eq : S' = AschbacherTightEmbedding.rightConjugate S k⁻¹ := by
    ext x
    rw [hk x, mem_rightConjugate_iff, inv_inv]
  have h1 : AschbacherTightEmbedding.rightConjugate (sec4W Ω S) k⁻¹ = sec4W Ω S' := by
    rw [rightConjugate_sec4W hΩ.conj_mem S k⁻¹, hS'eq]
  have h2 : sec4W Ω S = AschbacherTightEmbedding.rightConjugate (sec4W Ω S') k := by
    rw [← h1, rightConjugate_mul, inv_mul_cancel, rightConjugate_one]
  rw [h2, (rightConjugate_eq_self_iff _ k).mpr
    (by rw [normalizer_eq_top_iff.mpr hn]; exact mem_top k)]
  exact hn

theorem exists_mem_omegaD (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {K : Subgroup G} (hK : K ∈ Ω) : ∃ L, L ∈ omegaD Ω (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
  obtain ⟨S₀, hS₀, hRS₀⟩ := exists_isSylowOf_le hR.isPGroup (le_top : R ≤ ⊤)
  obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem hS hS₀
  refine ⟨AschbacherTightEmbedding.rightConjugate K k, hΩ.conj_mem K hK k, _,
    isSylowOf_rightConjugate hR k, ?_⟩
  intro y hy
  rw [mem_rightConjugate_iff] at hy
  have h1 := (hk _).mp (hRS₀ hy)
  have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
  rw [e] at h1
  exact le_normalizer_sec4W hΩ.conj_mem S h1

theorem sSup_dStarComp_ne_top_of_not_conn (hΩ : Assumption41 Ω)
    (hsingle : ∃ K₀ ∈ Ω, ∀ K ∈ Ω, ∃ g : G, K = AschbacherTightEmbedding.rightConjugate K₀ g)
    (hdis : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dStarComp Ω K) {L : Subgroup G} (hL : L ∈ Ω) :
    sSup (dStarComp Ω L) ≠ ⊤ := by
  obtain ⟨K, hK, J, hJ, hJK⟩ := hdis
  by_cases hKL : K ∈ dStarComp Ω L
  · by_cases hJL : J ∈ dStarComp Ω L
    · exact absurd (Relation.ReflTransGen.trans (reflTransGen_dStarAdj_symm hKL) hJL) hJK
    · exact sSup_dStarComp_ne_top hΩ hsingle hL hJ hJL
  · exact sSup_dStarComp_ne_top hΩ hsingle hL hK hKL

theorem mem_of_isSylowOf_of_commute {H T : Subgroup G} (hT : IsSylowOf 2 T H) {x : G}
    (hxH : x ∈ H) (hxx : x * x = 1) (hc : ∀ y ∈ T, x * y = y * x) : x ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxP : IsPGroup 2 (zpowers x) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hxx)
  have hP : IsPGroup 2 (zpowers x ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hxP hT.isPGroup
      ((zpowers_le).mpr (mem_normalizer_of_forall_mul_comm hc))
  have heq := hT.eq_of_le le_sup_right (sup_le ((zpowers_le).mpr hxH) hT.le) hP
  rw [← heq]
  exact mem_sup_left (mem_zpowers x)

theorem exists_isSylowOf_rot_mem_normalized (hΩ : Assumption41 Ω) {J T₀ V₀ B A : Subgroup G}
    (hJ : J ∈ Ω) (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀)
    (ht1 : t ≠ 1) (htt : t * t = 1) (hT₀B : T₀ ≤ B) (hA : IsPGroup 2 A)
    (hAt : A ≤ centralizer ({t} : Set G)) (hAB : A ≤ normalizer (B : Set G)) :
    ∃ T V : Subgroup G, IsSylowOf 2 T J ∧ IsDihedralRot V T ∧ t ∈ V ∧ T ≤ B ∧
      A ≤ normalizer (T : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  obtain ⟨z₀, -, -, -, hz₀uniq, hz₀T⟩ := hV₀.exists_involution
  have htz₀ : t = z₀ := (hz₀uniq t htV htt).resolve_left ht1
  set H : Subgroup G := J ⊓ centralizer ({t} : Set G) ⊓ B with hHdef
  have hT₀H : T₀ ≤ H := by
    refine le_inf (le_inf hT₀.le fun y hy => ?_) hT₀B
    rw [mem_centralizer_singleton_iff, htz₀]
    exact hz₀T y hy
  have hAH : A ≤ normalizer (H : Set G) := by
    intro a ha
    have haJ : a ∈ normalizer (J : Set G) :=
      Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) htJ ht1 htt (hAt ha)
    exact inf_le_normalizer_inf (mem_inf.mpr
      ⟨inf_le_normalizer_inf (mem_inf.mpr ⟨haJ, le_normalizer (hAt ha)⟩), hAB ha⟩)
  obtain ⟨T, hT, hAT⟩ := exists_isSylowOf_normalized hA hAH
  have hTJ : IsSylowOf 2 T J :=
    isSylowOf_of_isSylowOf_le hT₀ hT₀H (inf_le_left.trans inf_le_left) hT
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hJ hTJ
  have hTt : ∀ y ∈ T, t * y = y * t := fun y hy =>
    (mem_centralizer_singleton_iff.mp (mem_inf.mp (mem_inf.mp (hT.le hy)).1).2).symm
  have htH : t ∈ H :=
    mem_inf.mpr ⟨mem_inf.mpr ⟨htJ, mem_centralizer_singleton_iff.mpr rfl⟩, hT₀B (hV₀.le htV)⟩
  have htT : t ∈ T := mem_of_isSylowOf_of_commute hT htH htt hTt
  obtain ⟨z₁, hz₁V, -, -, hz₁uniq, -⟩ := hV.exists_involution
  have htV' : t ∈ V := by
    rcases hV.eq_of_central hz₁uniq htT hTt with h | h
    · exact absurd h ht1
    · rw [h]
      exact hz₁V
  exact ⟨T, V, hTJ, hV, htV', hT.le.trans inf_le_right, hAT⟩

theorem exists_isSylowOf_le_normalizer_of_mem (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {L T₀ V₀ : Subgroup G} (hL : L ∈ Ω) (hT₀ : IsSylowOf 2 T₀ L)
    (hV₀ : IsDihedralRot V₀ T₀) {x : G} (hxV : x ∈ V₀) (hx1 : x ≠ 1) (hxx : x * x = 1)
    (hxW : x ∈ sec4W Ω S) :
    ∃ T V : Subgroup G, IsSylowOf 2 T L ∧ IsDihedralRot V T ∧ x ∈ V ∧
      T ≤ normalizer (sec4W Ω S : Set G) ∧ V ≤ sec4W Ω S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  have hWx : W ≤ centralizer ({x} : Set G) := fun w hw =>
    mem_centralizer_singleton_iff.mpr (sec4W_mul_comm hΩ hS hw hxW)
  obtain ⟨T, V, hT, hV, hxV', -, hWT⟩ := exists_isSylowOf_rot_mem_normalized hΩ hL hT₀ hV₀ hxV
    hx1 hxx (le_top : T₀ ≤ ⊤) hW2 hWx (fun a _ => le_normalizer (mem_top a))
  have hP : IsPGroup 2 (W ⊔ T : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hW2 hT.isPGroup hWT
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_le hP (le_top : W ⊔ T ≤ ⊤)
  have hWS' : sec4W Ω S' = W := sec4W_eq_of_le hΩ hS hS' (le_sup_left.trans hPS')
  have hTW : T ≤ normalizer (W : Set G) := by
    rw [← hWS']
    exact (le_sup_right.trans hPS').trans (le_normalizer_sec4W hΩ.conj_mem S')
  exact ⟨T, V, hT, hV, hxV', hTW, rot_le_sec4W hΩ hS hL hT hV hTW⟩

theorem mem_sec4W_of_mem_omegaD (hΩ : Assumption41 Ω)
    (hnil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) {S : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) {J T₀ V₀ : Subgroup G} (hJ : J ∈ omegaD Ω (sec4W Ω S))
    (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀)
    (htW : t ∈ normalizer (sec4W Ω S : Set G)) : t ∈ sec4W Ω S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  obtain ⟨hJΩ, T₁, hT₁, hT₁W⟩ := hJ
  have htT₀ : t ∈ T₀ := hV₀.le htV
  have htP : IsPGroup 2 (zpowers t) := hT₀.isPGroup.to_le ((zpowers_le).mpr htT₀)
  obtain ⟨T₂, hT₂A, htT₂⟩ := exists_isSylowOf_le htP
    ((zpowers_le).mpr (mem_inf.mpr ⟨hT₀.le htT₀, htW⟩) :
      zpowers t ≤ J ⊓ normalizer (W : Set G))
  have hT₂ : IsSylowOf 2 T₂ J := isSylowOf_of_isSylowOf_le hT₁ (le_inf hT₁.le hT₁W) inf_le_left hT₂A
  have hT₂W : T₂ ≤ normalizer (W : Set G) := hT₂A.le.trans inf_le_right
  obtain ⟨k, hkJ, hk⟩ := L26.IsSylowOf.exists_conj_mem hT₂ hT₀
  have hT₂eq : AschbacherTightEmbedding.rightConjugate T₀ k = T₂ := by
    ext y
    rw [mem_rightConjugate_iff, hk]
    have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [e]
  set V₂ := AschbacherTightEmbedding.rightConjugate V₀ k with hV₂def
  have hV₂ : IsDihedralRot V₂ T₂ := hT₂eq ▸ hV₀.rightConjugate k
  have hV₂W : V₂ ≤ W := rot_le_sec4W hΩ hS hJΩ hT₂ hV₂ hT₂W
  have ht' : k⁻¹ * t * k ∈ V₂ := conj_mem_rightConjugate htV k
  obtain ⟨o, ho, r, hr, rfl⟩ := hnil J hJΩ T₂ hT₂ k hkJ
  set t'' := r * ((o * r)⁻¹ * t * (o * r)) * r⁻¹ with ht''def
  have ht''V : t'' ∈ V₂ :=
    (mem_normalizer_iff.mp ((le_normalizer.trans hV₂.normalizer_le) hr) _).mp ht'
  have ht''T : t'' ∈ T₂ := hV₂.le ht''V
  have hteq : t = o * t'' * o⁻¹ := by rw [ht''def]; group
  have hc : t''⁻¹ * t ∈ T₂ ⊓ oddCoreIn J := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem ht''T) (htT₂ (mem_zpowers t)), ?_⟩
    have h1 : t''⁻¹ * o * t'' ∈ oddCoreIn J := by
      have := (mem_normalizer_iff.mp (le_normalizer_oddCoreIn J (hT₂.le (inv_mem ht''T))) o).mp ho
      simpa using this
    have e : t''⁻¹ * t = (t''⁻¹ * o * t'') * o⁻¹ := by rw [hteq]; group
    rw [e]
    exact mul_mem h1 (inv_mem ho)
  have hbot : T₂ ⊓ oddCoreIn J = ⊥ :=
    eq_bot_of_isPGroup_of_odd (hT₂.isPGroup.to_le inf_le_left)
      ((odd_card_oddCoreIn J).of_dvd_nat (card_dvd_of_le inf_le_right))
  rw [hbot, mem_bot] at hc
  have : t = t'' := by
    calc t = t'' * (t''⁻¹ * t) := by group
      _ = t'' := by rw [hc, mul_one]
  rw [this]
  exact hV₂W ht''V

theorem MinCounter.conj_eq_inv_of_not_mem (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dStarComp Ω K) {J T₀ V₀ : Subgroup G}
    (hJ : J ∈ Ω) (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀)
    (ht1 : t ≠ 1) (htt : t * t = 1) (htW : t ∈ normalizer (sec4W Ω S : Set G))
    (htW' : t ∉ sec4W Ω S) : ∀ w ∈ sec4W Ω S, t * w * t⁻¹ = w⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  obtain ⟨K₁, hK₁, -⟩ := hM.single
  obtain ⟨K₀, hK₀⟩ := exists_mem_omegaD hΩ hS hK₁
  have hX := sSup_dStarComp_ne_top_of_not_conn hΩ hM.single hdis hK₀.1
  have hCeq := hM.dStarComp_eq_omegaD hK₀ hX
  have hJD : J ∉ omegaD Ω W := fun hJD =>
    htW' (mem_sec4W_of_mem_omegaD hΩ hM.twoNil hS hJD hT₀ hV₀ htV htW)
  have hJC : J ∉ dStarComp Ω K₀ := by rw [hCeq]; exact hJD
  have hnorm : ∀ L ∈ omegaD Ω W, AschbacherTightEmbedding.rightConjugate L t = L := fun L hL =>
    hM.rightConjugate_eq_of_mem_omegaD h22 hK₀ hX hJ hJC hT₀ hV₀ htV ht1 htt htW hL
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  have htP : IsPGroup 2 (zpowers t) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact htt)
  let I : Subgroup G :=
    { carrier := {w | w ∈ W ∧ t * w * t⁻¹ = w⁻¹}
      one_mem' := ⟨W.one_mem, by group⟩
      mul_mem' := by
        rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
        refine ⟨W.mul_mem ha hb, ?_⟩
        calc t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
          _ = a⁻¹ * b⁻¹ := by rw [ha', hb']
          _ = (a * b)⁻¹ := by
            rw [mul_inv_rev, sec4W_mul_comm hΩ hS (inv_mem hb) (inv_mem ha)]
      inv_mem' := by
        rintro a ⟨ha, ha'⟩
        refine ⟨W.inv_mem ha, ?_⟩
        calc t * a⁻¹ * t⁻¹ = (t * a * t⁻¹)⁻¹ := by group
          _ = a⁻¹⁻¹ := by rw [ha'] }
  have hWI : W ≤ I := by
    refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
    obtain ⟨K, hK, R₀, hR₀, hU₀⟩ := IsRot.exists_isDihedralRot hΩ hU
    have hUW : U ≤ W := le_sec4W hUS hU
    obtain ⟨R, hR, hUR, hRW⟩ := exists_isSylowOf_le_normalizer_of_isRot hΩ hS hK hR₀ hU₀ hUW
    have hKD : K ∈ omegaD Ω W := ⟨hK, R, hR, hRW⟩
    have htK : t ∈ normalizer (K : Set G) := (rightConjugate_eq_self_iff K t).mp (hnorm K hKD)
    obtain ⟨R₁, hR₁, hR₁W, htR₁⟩ := exists_isSylowOf_le_normalizer_normalized hR hRW htP
      ((zpowers_le).mpr htK) ((zpowers_le).mpr htW)
    obtain ⟨U₁, hU₁⟩ := Assumption41.exists_rot hΩ hK hR₁
    have hU₁eq : U₁ = U := rot_eq_of_le_sec4W hΩ hS hK hR₁ hU₁ hR hUR
      (rot_le_sec4W hΩ hS hK hR₁ hU₁ hR₁W) hUW
    have hKC : K ∈ dStarComp Ω K₀ := by rw [hCeq]; exact hKD
    have hnadj : ¬ DStarAdj Ω K J := fun h => hJC (Relation.ReflTransGen.tail hKC h)
    have hinv := conj_eq_inv_of_not_dStarAdj h22 hΩ hJ hK hnadj htJ ht1 htt htK hR₁ hU₁
      (htR₁ (mem_zpowers t))
    intro u hu
    exact ⟨hUW hu, hinv u (by rw [hU₁eq]; exact hu)⟩
  intro w hw
  exact (hWI hw).2

end CFSG.ComponentClassification.Asc76.Sec4
