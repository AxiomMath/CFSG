module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D17

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

omit [Finite G] in
theorem isPGroup_imgOf_o22In (X : Subgroup G) : IsPGroup 2 (imgOf X (o22In X)) := by
  rintro ⟨_, y, hy, rfl⟩
  obtain ⟨k, o, ho, hoy⟩ :=
    exists_pow_mem_oddCoreIn_of_mem_o22In (show (y : G) ∈ o22In X from hy)
  have hoy' : o = y ^ 2 ^ k := Subtype.ext (by simpa using hoy)
  refine ⟨k, Subtype.ext ?_⟩
  change (QuotientGroup.mk' (CFSG.Assembly.oddCore X) y) ^ 2 ^ k = 1
  rw [← map_pow, ← hoy', QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact ho

theorem exists_conj_le_of_le_o22In {X P Q : Subgroup G} (hP : IsSylowOf 2 P (o22In X))
    (hQ : IsPGroup 2 Q) (hQX : Q ≤ o22In X) :
    ∃ o ∈ oddCoreIn X, ∀ x ∈ Q, o * x * o⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOX : o22In X ≤ X := map_subtype_le _
  have heq : imgOf X (o22In X) = imgOf X P :=
    (isSylowOf_imgOf hP hOX).eq_of_le (imgOf_mono hP.le) le_rfl (isPGroup_imgOf_o22In X)
  exact exists_conj_le_of_imgOf_le (hQX.trans hOX) hP.isPGroup hQ
    ((imgOf_mono hQX).trans heq.le)

theorem mem_omegaD_of_conj_le (hΩ : Assumption41 Ω) {S' L T V : Subgroup G}
    (hS' : IsSylowOf 2 S' ⊤) (hL : L ∈ Ω) (hT : IsSylowOf 2 T L) (hV : IsDihedralRot V T)
    {o : G} (ho : o ∈ normalizer (L : Set G)) (hoV : ∀ x ∈ V, o * x * o⁻¹ ∈ S') :
    L ∈ omegaD Ω (sec4W Ω S') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLo : AschbacherTightEmbedding.rightConjugate L o⁻¹ = L :=
    (rightConjugate_eq_self_iff L o⁻¹).mpr (inv_mem ho)
  have hT' : IsSylowOf 2 (AschbacherTightEmbedding.rightConjugate T o⁻¹) L := by
    have := isSylowOf_rightConjugate hT o⁻¹
    rwa [hLo] at this
  have hV' := hV.rightConjugate o⁻¹
  have hVS : AschbacherTightEmbedding.rightConjugate V o⁻¹ ≤ S' := by
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv] at hy
    have e : o * (o⁻¹ * y * o) * o⁻¹ = y := by group
    have := hoV _ hy
    rwa [e] at this
  obtain ⟨R, hR, -, hRW⟩ := exists_isSylowOf_le_normalizer_of_isRot hΩ hS' hL hT' hV'
    (le_sec4W hVS (isRot_of hL hT' hV'))
  exact ⟨hL, R, hR, hRW⟩

theorem MinCounter.mem_omegaD_of_le_normalizer {S : Subgroup G} (hM : MinCounter Ω S)
    {J L : Subgroup G} (hJ : J ∈ omegaD Ω (sec4W Ω S)) (hL : L ∈ Ω)
    (hLJ : L ≤ normalizer (J : Set G)) : L ∈ omegaD Ω (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hS := hM.sylow
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hS.isPGroup.to_le (sec4W_le S)
  obtain ⟨hJΩ, T, hT, hTW⟩ := hJ
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hJΩ hT
  have hVW : V ≤ W := rot_le_sec4W hΩ hS hJΩ hT hV hTW
  obtain ⟨z, hzV, hz1, hzz, -, -⟩ := hV.exists_involution
  have hWJ : W ≤ normalizer (J : Set G) := fun w hw =>
    Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJΩ) (hT.le (hV.le hzV))
      hz1 hzz (mem_centralizer_singleton_iff.mpr (sec4W_mul_comm hΩ hS hw (hVW hzV)))
  set Y := xPerp Ω J with hYdef
  have hWQ : W ≤ normalizer (o22In Y : Set G) :=
    hWJ.trans ((normalizer_le_normalizer_xPerp hΩ J).trans (normalizer_le_normalizer_o22In Y))
  obtain ⟨Q, hQ, hWQ'⟩ := exists_isSylowOf_normalized hW2 hWQ
  have hP : IsPGroup 2 (W ⊔ Q : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' hW2 hQ.isPGroup hWQ'
  obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_le hP (le_top : W ⊔ Q ≤ ⊤)
  have hWS' : sec4W Ω S' = W := sec4W_eq_of_le hΩ hS hS' (le_sup_left.trans hPS')
  obtain ⟨T', hT'⟩ := exists_isSylowOf 2 L
  obtain ⟨V', hV'⟩ := Assumption41.exists_rot hΩ hL hT'
  have hV'Q := hM.rot_le_o22In_xPerp hJΩ ⟨hL, hLJ⟩ hT' hV'
  obtain ⟨o, ho, hoV⟩ := exists_conj_le_of_le_o22In hQ (hT'.isPGroup.to_le hV'.le) hV'Q
  have hoL : o ∈ normalizer (L : Set G) :=
    oddCoreIn_le_normalizer_of_le hΩ hL
      (show L ≤ Y from le_sSup (show L ∈ perp Ω J from ⟨hL, hLJ⟩)) ho
  have h := mem_omegaD_of_conj_le hΩ hS' hL hT' hV' hoL fun x hx =>
    hPS' (mem_sup_right (hoV x hx))
  rwa [hWS'] at h

theorem MinCounter.mem_omegaD_of_sylow_le_normalizer (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) {J L T : Subgroup G} (hJ : J ∈ omegaD Ω (sec4W Ω S)) (hL : L ∈ Ω)
    (hT : IsSylowOf 2 T J) (hTL : T ≤ normalizer (L : Set G)) :
    L ∈ omegaD Ω (sec4W Ω S) := by
  by_cases hLJ : L = J
  · rw [hLJ]
    exact hJ
  exact hM.mem_omegaD_of_le_normalizer hJ hL
    (le_normalizer_of_sylow h22 hM.assumption hL hJ.1 hLJ hT hTL).2

theorem MinCounter.mem_omegaD_of_reflTransGen {S : Subgroup G} (hM : MinCounter Ω S)
    {J L : Subgroup G} (hJ : J ∈ omegaD Ω (sec4W Ω S))
    (h : Relation.ReflTransGen (DAdj Ω) J L) : L ∈ omegaD Ω (sec4W Ω S) := by
  induction h with
  | refl => exact hJ
  | tail _ hab ih => exact hM.mem_omegaD_of_le_normalizer ih hab.2.1 hab.2.2.1

theorem MinCounter.mem_omegaD_of_le_of_isSylowOf {S : Subgroup G} (hM : MinCounter Ω S)
    {X : Subgroup G} (hX : X ≠ ⊤) (hgen : sSup {L | L ∈ Ω ∧ L ≤ X} = X) {P S' : Subgroup G}
    (hP : IsSylowOf 2 P X) (hS' : IsSylowOf 2 S' ⊤) (hPS' : P ≤ S') {L : Subgroup G}
    (hL : L ∈ Ω) (hLX : L ≤ X) : L ∈ omegaD Ω (sec4W Ω S') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hP₀ : IsSylowOf 2 (imgOf X P) ⊤ := by
    have := isSylowOf_imgOf hP le_rfl
    rwa [imgOf_self] at this
  have hW := hM.ihQuot X _ hX (fun L hL => hL.1) (membersIn_inv hΩ X) hgen _ hP₀
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 L
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hL hT
  have h1 := imgOf_rot_le_sec4W hΩ (fun L hL => hL.1) (membersIn_inv hΩ X) hgen hP₀ hW
    ⟨hL, hLX⟩ hT hV
  obtain ⟨o, ho, hoV⟩ := exists_conj_le_of_imgOf_le ((hV.le.trans hT.le).trans hLX)
    hP.isPGroup (hT.isPGroup.to_le hV.le) (h1.trans (sec4W_le _))
  exact mem_omegaD_of_conj_le hΩ hS' hL hT hV (oddCoreIn_le_normalizer_of_le hΩ hL hLX ho)
    fun x hx => hPS' (hoV x hx)

@[expose] def dComp (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | Relation.ReflTransGen (DAdj Ω) K J}

omit [Finite G] in
theorem reflTransGen_dAdj_symm {K J : Subgroup G} (h : Relation.ReflTransGen (DAdj Ω) K J) :
    Relation.ReflTransGen (DAdj Ω) J K := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head hab.symm ih

omit [Finite G] in
theorem mem_of_mem_dComp {K J : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ dComp Ω K) : J ∈ Ω := by
  induction hJ with
  | refl => exact hK
  | tail _ hab _ => exact hab.2.1

omit [Finite G] in
theorem rightConjugate_mem_dComp (hΩ : Assumption41 Ω) {K L J : Subgroup G}
    (hL : L ∈ dComp Ω K) (hJ : J ∈ dComp Ω K) {x : G} (hx : x ∈ normalizer (L : Set G)) :
    AschbacherTightEmbedding.rightConjugate J x ∈ dComp Ω K := by
  have h1 := reflTransGen_dAdj_rightConjugate hΩ hL x
  rw [(rightConjugate_eq_self_iff L x).mpr hx] at h1
  exact (hL.trans (reflTransGen_dAdj_symm h1)).trans (reflTransGen_dAdj_rightConjugate hΩ hJ x)

omit [Finite G] in
theorem le_setStab_dComp (hΩ : Assumption41 Ω) {K L : Subgroup G} (hL : L ∈ dComp Ω K) :
    L ≤ setStab (dComp Ω K) := by
  intro x hx J
  constructor
  · intro hJ
    exact rightConjugate_mem_dComp hΩ hL hJ (le_normalizer hx)
  · intro hJ
    have := rightConjugate_mem_dComp hΩ hL hJ (le_normalizer (inv_mem hx))
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this

omit [Finite G] in
theorem mem_setStab_dComp (hΩ : Assumption41 Ω) {J : Subgroup G} {r : G}
    (hr : AschbacherTightEmbedding.rightConjugate J r ∈ dComp Ω J) :
    r ∈ setStab (dComp Ω J) := by
  have hr' : AschbacherTightEmbedding.rightConjugate J r⁻¹ ∈ dComp Ω J := by
    have h1 := reflTransGen_dAdj_rightConjugate hΩ hr r⁻¹
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    exact reflTransGen_dAdj_symm h1
  intro L
  constructor
  · intro hL
    exact Relation.ReflTransGen.trans hr (reflTransGen_dAdj_rightConjugate hΩ hL r)
  · intro hL
    have h1 := reflTransGen_dAdj_rightConjugate hΩ hL r⁻¹
    rw [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at h1
    exact Relation.ReflTransGen.trans hr' h1

omit [Finite G] in
theorem sSup_members_dComp {K : Subgroup G} (hK : K ∈ Ω) :
    sSup {L | L ∈ Ω ∧ L ≤ sSup (dComp Ω K)} = sSup (dComp Ω K) :=
  le_antisymm (sSup_le fun _ hL => hL.2)
    (sSup_le fun _ hJ => le_sSup ⟨mem_of_mem_dComp hK hJ, le_sSup hJ⟩)

theorem MinCounter.sSup_dComp_ne_top {S : Subgroup G} (hM : MinCounter Ω S) {K : Subgroup G}
    (hK : K ∈ Ω) : sSup (dComp Ω K) ≠ ⊤ := by
  intro htop
  have hΩ := hM.assumption
  have hle : (⊤ : Subgroup G) ≤ setStab (dComp Ω K) := by
    rw [← htop]
    exact sSup_le fun L hL => le_setStab_dComp hΩ hL
  obtain ⟨K₀, -, hall⟩ := hM.single
  have hmem : ∀ L ∈ Ω, L ∈ dComp Ω K := by
    intro L hL
    obtain ⟨a, ha⟩ := hall K hK
    obtain ⟨b, rfl⟩ := hall L hL
    have h1 := (hle (mem_top (a⁻¹ * b)) K).mp Relation.ReflTransGen.refl
    have e : AschbacherTightEmbedding.rightConjugate K (a⁻¹ * b) =
        AschbacherTightEmbedding.rightConjugate K₀ b := by
      rw [ha, rightConjugate_mul, mul_inv_cancel_left]
    rwa [e] at h1
  apply hM.not_dConnected
  intro L hL J hJ
  exact Relation.ReflTransGen.trans (reflTransGen_dAdj_symm (hmem L hL)) (hmem J hJ)

end CFSG.ComponentClassification.Asc76.Sec4
