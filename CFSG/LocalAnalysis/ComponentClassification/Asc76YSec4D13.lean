module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D12
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D10

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem IsDihedralRot.exists_sq_of_mul_self {V T : Subgroup G} (hV : IsDihedralRot V T) {x : G}
    (hxV : x ∈ V) (hxx : x * x = 1) : ∃ v ∈ V, x = v * v := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply hV.exists_sq_of_pow_half_eq_one hxV
  obtain ⟨k, hk⟩ := (hV.isPGroup.to_le hV.le).exists_card_eq
  have h4 := hV.four_le
  rw [hk] at h4
  have hk2 : 2 ≤ k := by
    rcases k with _ | _ | k
    · simp at h4
    · simp at h4
    · omega
  have h4dvd : 4 ∣ Nat.card V := by
    rw [hk]
    have := Nat.pow_dvd_pow 2 hk2
    simpa using this
  obtain ⟨m, hm⟩ := h4dvd
  have e : Nat.card V / 2 = 2 * m := by omega
  rw [e, pow_mul, pow_two, hxx, one_pow]

omit [Finite G] in
theorem mem_of_mem_dStarComp {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ dStarComp Ω K) :
    J ∈ Ω := by
  induction hJ with
  | refl => exact hK
  | tail _ hab _ => exact hab.2.1

omit [Finite G] in
theorem dStarComp_eq_of_mem {K J : Subgroup G} (hJ : J ∈ dStarComp Ω K) :
    dStarComp Ω J = dStarComp Ω K := by
  ext L
  constructor
  · intro hL
    exact Relation.ReflTransGen.trans hJ hL
  · intro hL
    exact Relation.ReflTransGen.trans (reflTransGen_dStarAdj_symm hJ) hL

omit [Finite G] in
theorem sSup_members_eq {K : Subgroup G} (hK : K ∈ Ω) :
    sSup {L | L ∈ Ω ∧ L ≤ sSup (dStarComp Ω K)} = sSup (dStarComp Ω K) :=
  le_antisymm (sSup_le fun _ hL => hL.2)
    (sSup_le fun _ hJ => le_sSup ⟨mem_of_mem_dStarComp hK hJ, le_sSup hJ⟩)

theorem MinCounter.false_of_two_mem_sec4W (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hdis : ∃ K ∈ Ω, ∃ J ∈ Ω, J ∉ dStarComp Ω K) {J T₀ V₀ : Subgroup G}
    (hJ : J ∈ Ω) (hT₀ : IsSylowOf 2 T₀ J) (hV₀ : IsDihedralRot V₀ T₀) {t : G} (htV : t ∈ V₀)
    (ht1 : t ≠ 1) (htt : t * t = 1) (htW : t ∈ normalizer (sec4W Ω S : Set G))
    (htW' : t ∉ sec4W Ω S) {a b : G} (haW : a ∈ sec4W Ω S) (haZ : IsZInv Ω a)
    (hbW : b ∈ sec4W Ω S) (hbZ : IsZInv Ω b) (hab : a ≠ b) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  obtain ⟨K₁, hK₁, -⟩ := hM.single
  obtain ⟨K₀, hK₀⟩ := exists_mem_omegaD hΩ hS hK₁
  have hX := sSup_dStarComp_ne_top_of_not_conn hΩ hM.single hdis hK₀.1
  have hCeq := hM.dStarComp_eq_omegaD hK₀ hX
  have hJD : J ∉ omegaD Ω W := fun hJD =>
    htW' (mem_sec4W_of_mem_omegaD hΩ hM.twoNil hS hJD hT₀ hV₀ htV htW)
  have hJC : J ∉ dStarComp Ω K₀ := by rw [hCeq]; exact hJD
  have htJ : t ∈ J := hT₀.le (hV₀.le htV)
  have htZ : IsZInv Ω t := ⟨J, hJ, T₀, V₀, hT₀, hV₀, htV, ht1, htt⟩
  have htinv := hM.conj_eq_inv_of_not_mem h22 hdis hJ hT₀ hV₀ htV ht1 htt htW htW'
  set A : Subgroup G := W ⊓ centralizer ({t} : Set G) with hAdef
  have hA2 : IsPGroup 2 A := hW2.to_le inf_le_left
  have hZA : ∀ x ∈ W, x * x = 1 → x ∈ A := by
    intro x hx hxx
    refine mem_inf.mpr ⟨hx, mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 := htinv x hx
    rw [inv_eq_of_mul_eq_one_right hxx] at h1
    calc x * t = t * x * t⁻¹ * t := by rw [h1]
      _ = t * x := by group
  obtain ⟨Ts, Vs, hTs, hVs, htVs, -, hATs⟩ := exists_isSylowOf_rot_mem_normalized hΩ hJ hT₀ hV₀
    htV ht1 htt (le_top : T₀ ≤ ⊤) hA2 inf_le_right (fun a _ => le_normalizer (mem_top a))
  have hP : IsPGroup 2 (A ⊔ Ts : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hA2 hTs.isPGroup hATs
  obtain ⟨S₂, hS₂, hPS₂⟩ := exists_isSylowOf_le hP (le_top : A ⊔ Ts ≤ ⊤)
  have hM₂ := hM.of_sylow hS₂
  set W₂ := sec4W Ω S₂ with hW₂def
  have hAN₂ : A ≤ normalizer (W₂ : Set G) :=
    (le_sup_left.trans hPS₂).trans (le_normalizer_sec4W hΩ.conj_mem S₂)
  have hTsW₂ : Ts ≤ normalizer (W₂ : Set G) :=
    (le_sup_right.trans hPS₂).trans (le_normalizer_sec4W hΩ.conj_mem S₂)
  have hVsW₂ : Vs ≤ W₂ := rot_le_sec4W hΩ hS₂ hJ hTs hVs hTsW₂
  have hJD₂ : J ∈ omegaD Ω W₂ := ⟨hJ, Ts, hTs, hTsW₂⟩
  have hX₂ := sSup_dStarComp_ne_top_of_not_conn hΩ hM.single hdis hJ
  have hCeq₂ := hM₂.dStarComp_eq_omegaD hJD₂ hX₂
  obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem hS hS₂
  have hW₂eq : W₂ = AschbacherTightEmbedding.rightConjugate W k⁻¹ := by
    have hS₂eq : S₂ = AschbacherTightEmbedding.rightConjugate S k⁻¹ := by
      ext x
      rw [hk x, mem_rightConjugate_iff, inv_inv]
    rw [hW₂def, hS₂eq, ← rightConjugate_sec4W hΩ.conj_mem S k⁻¹]
  have hΛnot : ∀ x ∈ W, IsZInv Ω x → x ∉ W₂ := by
    rintro x hx ⟨L, hL, TL, VL, hTL, hVL, hxVL, hx1, hxx⟩ hxW₂
    obtain ⟨T₁, -, hT₁, -, -, hT₁W, -⟩ :=
      exists_isSylowOf_le_normalizer_of_mem hΩ hS hL hTL hVL hxVL hx1 hxx hx
    obtain ⟨T₂, -, hT₂, -, -, hT₂W, -⟩ :=
      exists_isSylowOf_le_normalizer_of_mem hΩ hS₂ hL hTL hVL hxVL hx1 hxx hxW₂
    have hLC : L ∈ dStarComp Ω K₀ := by rw [hCeq]; exact ⟨hL, T₁, hT₁, hT₁W⟩
    exact hJC (Relation.ReflTransGen.tail hLC
      (dStarAdj_of_mem_omegaD hΩ hS₂ ⟨hL, T₂, hT₂, hT₂W⟩ hJD₂))
  have hΛinv : ∀ x ∈ W, IsZInv Ω x → ∀ w ∈ W₂, x * w * x⁻¹ = w⁻¹ := by
    intro x hx hxZ
    have hxnot := hΛnot x hx hxZ
    obtain ⟨L, hL, TL, VL, hTL, hVL, hxVL, hx1, hxx⟩ := hxZ
    exact hM₂.conj_eq_inv_of_not_mem h22 hdis hL hTL hVL hxVL hx1 hxx (hAN₂ (hZA x hx hxx))
      hxnot
  have hconjW₂ : ∀ x ∈ W, IsZInv Ω x →
      k⁻¹⁻¹ * x * k⁻¹ ∈ W₂ ∧ IsZInv Ω (k⁻¹⁻¹ * x * k⁻¹) := fun x hx hxZ =>
    ⟨hW₂eq ▸ conj_mem_rightConjugate hx k⁻¹, hxZ.conj hΩ k⁻¹⟩
  obtain ⟨t', ht'W₂, ht'Z, htt'⟩ : ∃ t', t' ∈ W₂ ∧ IsZInv Ω t' ∧ t ≠ t' := by
    by_cases h : t = k⁻¹⁻¹ * a * k⁻¹
    · refine ⟨_, (hconjW₂ b hbW hbZ).1, (hconjW₂ b hbW hbZ).2, ?_⟩
      rw [h]
      intro h'
      exact hab (mul_left_cancel (mul_right_cancel h'))
    · exact ⟨_, (hconjW₂ a haW haZ).1, (hconjW₂ a haW haZ).2, h⟩
  have htt'W : t * t' ∈ W :=
    mul_mem_sec4W_of_inv hΩ hS (g := k⁻¹) (fun x hx hxZ w hw => hΛinv x hx hxZ w (hW₂eq ▸ hw))
      (hW₂eq ▸ hVsW₂ htVs) htZ (hW₂eq ▸ ht'W₂) ht'Z
  obtain ⟨K, hK, R, U, hR, hU, hzU, hz1, hzz⟩ := haZ
  obtain ⟨R₁, -, hR₁, -, -, hR₁W, -⟩ :=
    exists_isSylowOf_le_normalizer_of_mem hΩ hS hK hR hU hzU hz1 hzz haW
  have hKC : K ∈ dStarComp Ω K₀ := by rw [hCeq]; exact ⟨hK, R₁, hR₁, hR₁W⟩
  have hzK : a ∈ K := hR.le (hU.le hzU)
  have hzA : a ∈ A := hZA a haW hzz
  have hzJ : a ∈ normalizer (J : Set G) :=
    Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ) htJ ht1 htt
      (mem_inf.mp hzA).2
  have hnadj : ¬ DStarAdj Ω J K := fun h => hJC (Relation.ReflTransGen.tail hKC h.symm)
  have hzTs : a ∉ Ts := by
    intro h
    have := eq_of_mem_of_mem hΩ hK hJ hzK (hTs.le h) hz1 hzz
    exact hJC (this ▸ hKC)
  have hzinv := conj_eq_inv_of_not_dStarAdj h22 hΩ hK hJ hnadj hzK hz1 hzz hzJ hTs hVs
    (hATs hzA)
  have hDz := isDihedralTwoGroup_of_not_dStarAdj h22 hΩ hK hJ hnadj hzK hz1 hzz hzJ hTs hVs
    (hATs hzA)
  obtain ⟨u, huVs, htu⟩ := hVs.exists_sq_of_mul_self htVs htt
  obtain ⟨c, hc⟩ := exists_conj_eq_mul_of_isDihedral hVs hzTs hzz hDz hzinv huVs
  have huW₂ : u ∈ W₂ := hVsW₂ huVs
  have hzuN : a * u ∈ normalizer (W₂ : Set G) :=
    mul_mem (hAN₂ hzA) (le_normalizer huW₂)
  have hzuW₂ : a * u ∉ W₂ := fun h => hΛnot a haW ⟨K, hK, R, U, hR, hU, hzU, hz1, hzz⟩ (by
    have := mul_mem h (inv_mem huW₂)
    rwa [mul_inv_cancel_right] at this)
  set K' := AschbacherTightEmbedding.rightConjugate K c with hK'def
  have hK' : K' ∈ Ω := hΩ.conj_mem K hK c
  have hR' := isSylowOf_rightConjugate hR c
  have hU' := hU.rightConjugate c
  have hzuU' : a * u ∈ AschbacherTightEmbedding.rightConjugate U c := by
    rw [← hc]
    exact conj_mem_rightConjugate hzU c
  have hzu1 : a * u ≠ 1 := by
    rw [← hc]
    intro h
    apply hz1
    calc a = c * (c⁻¹ * a * c) * c⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hzuzu : a * u * (a * u) = 1 := by
    rw [← hc]
    calc c⁻¹ * a * c * (c⁻¹ * a * c) = c⁻¹ * (a * a) * c := by group
      _ = 1 := by rw [hzz]; group
  have hzuinv := hM₂.conj_eq_inv_of_not_mem h22 hdis hK' hR' hU' hzuU' hzu1 hzuzu hzuN hzuW₂
  have hK'D : K' ∉ omegaD Ω W₂ := fun h =>
    hzuW₂ (mem_sec4W_of_mem_omegaD hΩ hM.twoNil hS₂ h hR' hU' hzuU' hzuN)
  have hK'C : K' ∉ dStarComp Ω J := by rw [hCeq₂]; exact hK'D
  obtain ⟨J', hJ', T'₀, V'₀, hT'₀, hV'₀, ht'V'₀, ht'1, ht't'⟩ := ht'Z
  obtain ⟨T'₁, V'₁, hT'₁, hV'₁, ht'V'₁, hT'₁W, -⟩ :=
    exists_isSylowOf_le_normalizer_of_mem hΩ hS₂ hJ' hT'₀ hV'₀ ht'V'₀ ht'1 ht't' ht'W₂
  have hJ'C : J' ∈ dStarComp Ω J := by rw [hCeq₂]; exact ⟨hJ', T'₁, hT'₁, hT'₁W⟩
  have hzut' : a * u ∈ centralizer ({t'} : Set G) := by
    rw [mem_centralizer_singleton_iff]
    have h1 := hzuinv t' ht'W₂
    rw [inv_eq_of_mul_eq_one_right ht't'] at h1
    calc a * u * t' = a * u * t' * (a * u)⁻¹ * (a * u) := by group
      _ = t' * (a * u) := by rw [h1]
  have hzuP : IsPGroup 2 (zpowers (a * u)) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hzuzu)
  obtain ⟨T', V', hT', hV', ht'V', hT'W, hzuT'⟩ := exists_isSylowOf_rot_mem_normalized hΩ hJ'
    hT'₁ hV'₁ ht'V'₁ ht'1 ht't' hT'₁W hzuP ((zpowers_le).mpr hzut')
    ((zpowers_le).mpr (le_normalizer hzuN))
  have hV'W₂ : V' ≤ W₂ := rot_le_sec4W hΩ hS₂ hJ' hT' hV' hT'W
  have hzuJ' : a * u ∈ normalizer (J' : Set G) :=
    Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ')
      (hT'₀.le (hV'₀.le ht'V'₀)) ht'1 ht't' hzut'
  have hnadj' : ¬ DStarAdj Ω J' K' := fun h => hK'C (Relation.ReflTransGen.tail hJ'C h)
  have hzuT'n : a * u ∉ T' := by
    intro h
    have := eq_of_mem_of_mem hΩ hK' hJ' (hR'.le (hU'.le hzuU')) (hT'.le h) hzu1 hzuzu
    exact hK'C (this ▸ hJ'C)
  have hDzu := isDihedralTwoGroup_of_not_dStarAdj h22 hΩ hK' hJ' hnadj'
    (hR'.le (hU'.le hzuU')) hzu1 hzuzu hzuJ' hT' hV' (hzuT' (mem_zpowers _))
  obtain ⟨u', hu'V', ht'u'⟩ := hV'.exists_sq_of_mul_self ht'V' ht't'
  obtain ⟨c', hc'⟩ := exists_conj_eq_mul_of_isDihedral hV' hzuT'n hzuzu hDzu
    (fun v hv => hzuinv v (hV'W₂ hv)) hu'V'
  set s := a * u * u' with hsdef
  have hsZ : IsZInv Ω s := by
    have h1 : IsZInv Ω (c'⁻¹ * (c⁻¹ * a * c) * c') :=
      (IsZInv.conj hΩ ⟨K, hK, R, U, hR, hU, hzU, hz1, hzz⟩ c).conj hΩ c'
    rwa [hc, hc'] at h1
  obtain ⟨-, -, -, -, -, -, -, -, hss⟩ := id hsZ
  have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hss
  have huu' : u' * u = u * u' := sec4W_mul_comm hΩ hS₂ (hV'W₂ hu'V') huW₂
  have hzs : s⁻¹ * a * s = a * (t * t') := by
    rw [hsinv, hsdef, htu, ht'u']
    calc a * u * u' * a * (a * u * u') = a * u * u' * (a * a) * u * u' := by group
      _ = a * u * (u' * u) * u' := by rw [hzz]; group
      _ = a * (u * u * (u' * u')) := by rw [huu']; group
  have hzsW : s⁻¹ * a * s ∈ W := by rw [hzs]; exact mul_mem haW htt'W
  have hzs1 : s⁻¹ * a * s ≠ 1 := by
    intro h
    apply hz1
    calc a = s * (s⁻¹ * a * s) * s⁻¹ := by group
      _ = 1 := by rw [h]; group
  have hzszs : s⁻¹ * a * s * (s⁻¹ * a * s) = 1 := by
    calc s⁻¹ * a * s * (s⁻¹ * a * s) = s⁻¹ * (a * a) * s := by group
      _ = 1 := by rw [hzz]; group
  obtain ⟨T₃, -, hT₃, -, -, hT₃W, -⟩ := exists_isSylowOf_le_normalizer_of_mem hΩ hS
    (hΩ.conj_mem K hK s) (isSylowOf_rightConjugate hR s) (hU.rightConjugate s)
    (conj_mem_rightConjugate hzU s) hzs1 hzszs hzsW
  have hKs : AschbacherTightEmbedding.rightConjugate K s ∈ dStarComp Ω K := by
    rw [dStarComp_eq_of_mem hKC, hCeq]
    exact ⟨hΩ.conj_mem K hK s, T₃, hT₃, hT₃W⟩
  have hsStab : s ∈ setStab (dStarComp Ω K₀) := by
    have h2 := mem_setStab_dStarComp hΩ hKs
    rwa [dStarComp_eq_of_mem hKC] at h2
  have hsX := setStab_le_normalizer_sSup _ hsStab
  have hsD : ∀ L ∈ omegaD Ω W,
      AschbacherTightEmbedding.rightConjugate L s ∈ omegaD Ω W := fun L hL => by
    have := (hsStab L).mp (by rw [hCeq]; exact hL)
    rwa [hCeq] at this
  have hD : ∀ L ∈ omegaD Ω W, L ≤ sSup (dStarComp Ω K₀) := fun L hL =>
    le_sSup (by rw [hCeq]; exact hL)
  have hsB := hM.mem_normalizer_sup_oddCoreIn hX (sSup_members_eq hK₀.1) hD hsX hsD
  have hWX := sec4W_le_of_omegaD_le hΩ hS hD
  have hs2 : IsPGroup 2 (zpowers s) :=
    isPGroup_zpowers_of_pow_eq_one (n := 1) (by rw [pow_one, pow_two]; exact hss)
  obtain ⟨o, ho, hos⟩ := exists_conj_mem_normalizer_of_mem_normalizer_sup hW2 hWX hs2 hsB
  set X := sSup (dStarComp Ω K₀) with hXdef
  set s'' := o * s * o⁻¹ with hs''def
  have hq : s''⁻¹ * a * s'' ∈ W := by
    have := (mem_normalizer_iff.mp (inv_mem hos) a).mp haW
    simpa using this
  have hzX : a ∈ X := hWX haW
  have hpX : s⁻¹ * a * s ∈ X := hWX hzsW
  have hsO : s ∈ normalizer (oddCoreIn X : Set G) := normalizer_le_normalizer_oddCoreIn X hsX
  have hc₁ : a⁻¹ * o⁻¹ * a * o ∈ oddCoreIn X := by
    have h1 := (mem_normalizer_iff.mp (le_normalizer_oddCoreIn X (inv_mem hzX)) o⁻¹).mp
      (inv_mem ho)
    simp only [inv_inv] at h1
    exact mul_mem h1 ho
  have hc₂ : s⁻¹ * (a⁻¹ * o⁻¹ * a * o) * s ∈ oddCoreIn X := by
    have := (mem_normalizer_iff.mp (inv_mem hsO) _).mp hc₁
    simpa using this
  have hc₃ : (s⁻¹ * a * s)⁻¹ * o * (s⁻¹ * a * s) ∈ oddCoreIn X := by
    have := (mem_normalizer_iff.mp (le_normalizer_oddCoreIn X (inv_mem hpX)) o).mp ho
    simpa using this
  have hpq : (s⁻¹ * a * s)⁻¹ * (s''⁻¹ * a * s'') ∈ W ⊓ oddCoreIn X := by
    refine mem_inf.mpr ⟨mul_mem (inv_mem hzsW) hq, ?_⟩
    have e : (s⁻¹ * a * s)⁻¹ * (s''⁻¹ * a * s'') =
        ((s⁻¹ * a * s)⁻¹ * o * (s⁻¹ * a * s)) * (s⁻¹ * (a⁻¹ * o⁻¹ * a * o) * s) * o⁻¹ := by
      rw [hs''def]
      group
    rw [e]
    exact mul_mem (mul_mem hc₃ hc₂) (inv_mem ho)
  have hbot : W ⊓ oddCoreIn X = ⊥ :=
    eq_bot_of_isPGroup_of_odd (hW2.to_le inf_le_left)
      ((odd_card_oddCoreIn X).of_dvd_nat (card_dvd_of_le inf_le_right))
  rw [hbot, mem_bot] at hpq
  have hqp : s''⁻¹ * a * s'' = a * (t * t') := by
    rw [← hzs]
    calc s''⁻¹ * a * s'' = (s⁻¹ * a * s) * ((s⁻¹ * a * s)⁻¹ * (s''⁻¹ * a * s'')) := by group
      _ = s⁻¹ * a * s := by rw [hpq, mul_one]
  have hs''Z : IsZInv Ω s'' := by
    have := hsZ.conj hΩ o⁻¹
    rwa [inv_inv] at this
  have hfix : s''⁻¹ * a * s'' = a := by
    by_cases hs''W : s'' ∈ W
    · have := sec4W_mul_comm hΩ hS haW hs''W
      calc s''⁻¹ * a * s'' = s''⁻¹ * (a * s'') := by group
        _ = s''⁻¹ * (s'' * a) := by rw [this]
        _ = a := by group
    · obtain ⟨M'', hM'', T'', V'', hT'', hV'', hs''V'', hs''1, hs''s''⟩ := hs''Z
      have h1 := hM.conj_eq_inv_of_not_mem h22 hdis hM'' hT'' hV'' hs''V'' hs''1 hs''s'' hos
        hs''W a haW
      rw [inv_eq_of_mul_eq_one_right hzz] at h1
      calc s''⁻¹ * a * s'' = s''⁻¹ * (s'' * a * s''⁻¹) * s'' := by rw [h1]
        _ = a := by group
  rw [hqp] at hfix
  have h1 : t * t' = 1 := mul_left_cancel (hfix.trans (mul_one a).symm)
  apply htt'
  calc t = t * (t * t') := by rw [h1, mul_one]
    _ = t' := by rw [← mul_assoc, htt, one_mul]

end CFSG.ComponentClassification.Asc76.Sec4
