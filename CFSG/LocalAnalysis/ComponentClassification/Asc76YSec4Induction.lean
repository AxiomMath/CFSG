module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Quot

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def Thm5Flat : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)), Assumption41 Ω →
    (∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) → ∀ S : Subgroup G, IsSylowOf 2 S ⊤ →
      (sec4W Ω S).Normal

@[expose] def o22In (X : Subgroup G) : Subgroup G :=
  ((CFSG.pCore 2 (X ⧸ CFSG.Assembly.oddCore X)).comap
    (QuotientGroup.mk' (CFSG.Assembly.oddCore X))).map X.subtype

theorem twoNil_imgΩ {X : Subgroup G} {ΩX : Set (Subgroup G)} (hgen : sSup ΩX = X)
    (hnil : ∀ K ∈ ΩX, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) :
    ∀ K ∈ imgΩ X ΩX, ∀ R, IsSylowOf 2 R K → IsTwoNil K R := by
  rintro _ ⟨J, hJ, rfl⟩ R hR
  exact isTwoNil_imgOf ((le_sSup hJ).trans hgen.le) (hnil J hJ) hR

theorem imgOf_rot_le_sec4W (hΩ : Assumption41 Ω) {X : Subgroup G} {ΩX : Set (Subgroup G)}
    (hsub : ΩX ⊆ Ω) (hinv : ∀ J ∈ ΩX, ∀ x ∈ X, AschbacherTightEmbedding.rightConjugate J x ∈ ΩX)
    (hgen : sSup ΩX = X) {S : Subgroup (X ⧸ CFSG.Assembly.oddCore X)} (hS : IsSylowOf 2 S ⊤)
    (hW : (sec4W (imgΩ X ΩX) S).Normal) {J T U : Subgroup G} (hJ : J ∈ ΩX)
    (hT : IsSylowOf 2 T J) (hU : IsDihedralRot U T) : imgOf X U ≤ sec4W (imgΩ X ΩX) S := by
  have hJX : J ≤ X := (le_sSup hJ).trans hgen.le
  have hU' : IsDihedralRot (imgOf X U) (imgOf X T) :=
    (hU.subgroupOf (hT.le.trans hJX)).map _ (mk_injOn hT.isPGroup)
  exact rot_le_sec4W (assumption41_imgΩ hΩ hsub hinv hgen) hS ⟨J, hJ, rfl⟩
    (isSylowOf_imgOf hT hJX) hU' (le_top.trans (normalizer_eq_top_iff.mpr hW).ge)

theorem rot_le_o22In_of_normal (hΩ : Assumption41 Ω) {X : Subgroup G} {ΩX : Set (Subgroup G)}
    (hsub : ΩX ⊆ Ω) (hinv : ∀ J ∈ ΩX, ∀ x ∈ X, AschbacherTightEmbedding.rightConjugate J x ∈ ΩX)
    (hgen : sSup ΩX = X) {S : Subgroup (X ⧸ CFSG.Assembly.oddCore X)} (hS : IsSylowOf 2 S ⊤)
    (hW : (sec4W (imgΩ X ΩX) S).Normal) {J T U : Subgroup G} (hJ : J ∈ ΩX)
    (hT : IsSylowOf 2 T J) (hU : IsDihedralRot U T) : U ≤ o22In X := by
  have hJX : J ≤ X := (le_sSup hJ).trans hgen.le
  have hUW := imgOf_rot_le_sec4W hΩ hsub hinv hgen hS hW hJ hT hU
  have hWP : sec4W (imgΩ X ΩX) S ≤ CFSG.pCore 2 (X ⧸ CFSG.Assembly.oddCore X) :=
    le_sSup ⟨hW, hS.isPGroup.to_le (sec4W_le S)⟩
  intro u hu
  have huX : u ∈ X := hJX (hT.le (hU.le hu))
  exact ⟨⟨u, huX⟩, hWP (hUW (Subgroup.mem_map.mpr ⟨⟨u, huX⟩, hu, rfl⟩)), rfl⟩

structure MinCounter (Ω : Set (Subgroup G)) (S : Subgroup G) : Prop where
  assumption : Assumption41 Ω
  twoNil : ∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R
  sylow : IsSylowOf 2 S ⊤
  single : ∃ K₀ ∈ Ω, ∀ K ∈ Ω, ∃ g : G, K = AschbacherTightEmbedding.rightConjugate K₀ g
  not_normal : ¬ (sec4W Ω S).Normal
  ihQuot : ∀ (X : Subgroup G) (ΩX : Set (Subgroup G)), X ≠ ⊤ → ΩX ⊆ Ω →
    (∀ J ∈ ΩX, ∀ x ∈ X, AschbacherTightEmbedding.rightConjugate J x ∈ ΩX) → sSup ΩX = X →
    ∀ S' : Subgroup (X ⧸ CFSG.Assembly.oddCore X), IsSylowOf 2 S' ⊤ →
      (sec4W (imgΩ X ΩX) S').Normal

theorem MinCounter.rot_le_o22In {S : Subgroup G} (hM : MinCounter Ω S) {X : Subgroup G}
    {ΩX : Set (Subgroup G)} (hX : X ≠ ⊤) (hsub : ΩX ⊆ Ω)
    (hinv : ∀ J ∈ ΩX, ∀ x ∈ X, AschbacherTightEmbedding.rightConjugate J x ∈ ΩX)
    (hgen : sSup ΩX = X) {J T U : Subgroup G} (hJ : J ∈ ΩX) (hT : IsSylowOf 2 T J)
    (hU : IsDihedralRot U T) : U ≤ o22In X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S', hS'⟩ := exists_isSylowOf 2 (⊤ : Subgroup (X ⧸ CFSG.Assembly.oddCore X))
  exact rot_le_o22In_of_normal hM.assumption hsub hinv hgen hS'
    (hM.ihQuot X ΩX hX hsub hinv hgen S' hS') hJ hT hU

theorem o22In_le_of_normal (hO : CFSG.Open.standardComponentOddCore G = ⊥) {X : Subgroup G}
    (hX : X.Normal) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤) : o22In X ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXn : X.subgroupOf ⊤ |>.Normal :=
    (normal_subgroupOf_iff_le_normalizer le_top).mpr (normalizer_eq_top_iff.mpr hX).ge
  have hOX : CFSG.Assembly.oddCore X = ⊥ := standardComponentOddCore_eq_bot_of_isSubnormal hO
    (CFSG.Assembly.IsSubnormal.step le_top hXn (CFSG.Assembly.IsSubnormal.refl ⊤))
  have hP2 : IsPGroup 2 (o22In X) := by
    rintro ⟨_, y, hy, rfl⟩
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2)
      (G := X ⧸ CFSG.Assembly.oddCore X)) ⟨_, hy⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : QuotientGroup.mk' (CFSG.Assembly.oddCore X) (y ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hOX, mem_bot] at h1
    have := congrArg Subtype.val h1
    simpa using this
  have hPn : (o22In X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨y, hy, rfl⟩ := hn
    have hg : g ∈ normalizer (X : Set G) := by
      rw [normalizer_eq_top_iff.mpr hX]
      exact mem_top g
    have hxg : g * (y : G) * g⁻¹ ∈ X := (mem_normalizer_iff.mp hg _).mp y.2
    exact ⟨⟨_, hxg⟩, mk_conj_mem_pCore hg y.2 hxg hy, rfl⟩
  have h1 := hS.eq_of_le (le_sup_left : S ≤ S ⊔ o22In X) le_top
    (IsPGroup.to_sup_of_normal_right hS.isPGroup hP2)
  exact h1 ▸ le_sup_right

omit [Finite G] in
theorem assumption41_of_subset (hΩ : Assumption41 Ω) {Ω' : Set (Subgroup G)} (hsub : Ω' ⊆ Ω)
    (hinv : ∀ J ∈ Ω', ∀ g : G, AschbacherTightEmbedding.rightConjugate J g ∈ Ω')
    (hgen : sSup Ω' = ⊤) : Assumption41 Ω' :=
  ⟨hΩ.oddCore, hinv, hgen, fun K hK J hJ => hΩ.twoPart K (hsub hK) J (hsub hJ),
    fun K hK J hJ => hΩ.inter K (hsub hK) J (hsub hJ), fun K hK => hΩ.perfect K (hsub hK),
    fun K hK => hΩ.dihedral K (hsub hK)⟩

theorem sSup_normal {Ω' : Set (Subgroup G)}
    (hinv : ∀ J ∈ Ω', ∀ g : G, AschbacherTightEmbedding.rightConjugate J g ∈ Ω') :
    (sSup Ω').Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  apply mem_normalizer_of_map_conj_le
  have h1 : AschbacherTightEmbedding.rightConjugate (sSup Ω') g⁻¹ ≤ sSup Ω' := by
    rw [rightConjugate_le_iff]
    refine sSup_le fun J hJ => ?_
    rw [← rightConjugate_le_iff]
    exact le_sSup (hinv J hJ g⁻¹)
  simpa [AschbacherTightEmbedding.rightConjugate] using h1

theorem sec4W_normal_of_rot_le (hΩ : Assumption41 Ω) {S : Subgroup G}
    (hrot : ∀ J ∈ Ω, ∀ T U : Subgroup G, IsSylowOf 2 T J → IsDihedralRot U T → U ≤ S) :
    (sec4W Ω S).Normal := by
  rw [← normalizer_eq_top_iff, eq_top_iff]
  intro g _
  apply mem_normalizer_of_map_conj_le
  have h1 : AschbacherTightEmbedding.rightConjugate (sec4W Ω S) g⁻¹ ≤ sec4W Ω S := by
    rw [rightConjugate_sec4W hΩ.conj_mem]
    refine iSup_le fun U => iSup_le fun _ => iSup_le fun hU => ?_
    obtain ⟨J, hJ, T, hT, hUT⟩ := IsRot.exists_isDihedralRot hΩ hU
    exact le_sec4W (hrot J hJ T U hT hUT) hU
  simpa [AschbacherTightEmbedding.rightConjugate] using h1

theorem rot_le_of_subset (hΩ : Assumption41 Ω) {Ω' : Set (Subgroup G)} {X : Subgroup G}
    (hsub : Ω' ⊆ Ω) (hinv : ∀ J ∈ Ω', ∀ g : G, AschbacherTightEmbedding.rightConjugate J g ∈ Ω')
    (hgen : sSup Ω' = X) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (htop : X = ⊤ → Assumption41 Ω' → (sec4W Ω' S).Normal)
    (hquot : X ≠ ⊤ → ∀ S' : Subgroup (X ⧸ CFSG.Assembly.oddCore X), IsSylowOf 2 S' ⊤ →
      (sec4W (imgΩ X Ω') S').Normal) :
    ∀ J ∈ Ω', ∀ T U : Subgroup G, IsSylowOf 2 T J → IsDihedralRot U T → U ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro J hJ T U hT hU
  by_cases hX : X = ⊤
  · have hΩ' := assumption41_of_subset hΩ hsub hinv (hgen.trans hX)
    have hW := htop hX hΩ'
    exact (rot_le_sec4W hΩ' hS hJ hT hU
      (le_top.trans (normalizer_eq_top_iff.mpr hW).ge)).trans (sec4W_le S)
  · obtain ⟨S', hS'⟩ := exists_isSylowOf 2 (⊤ : Subgroup (X ⧸ CFSG.Assembly.oddCore X))
    have h1 := rot_le_o22In_of_normal hΩ hsub (fun J hJ x _ => hinv J hJ x) hgen hS'
      (hquot hX S' hS') hJ hT hU
    exact h1.trans (o22In_le_of_normal hΩ.oddCore (hgen ▸ sSup_normal hinv) hS)

theorem thm5Flat_of
    (hstep : ∀ (G : Type) [Group G] [Finite G] (Ω : Set (Subgroup G)) (S : Subgroup G),
      MinCounter Ω S → False) : Thm5Flat := by
  suffices h : ∀ n m : ℕ, ∀ (G : Type) [Group G] [Finite G], Nat.card G = n →
      ∀ Ω : Set (Subgroup G), Ω.ncard = m → Assumption41 Ω →
      (∀ K ∈ Ω, ∀ R, IsSylowOf 2 R K → IsTwoNil K R) → ∀ S : Subgroup G, IsSylowOf 2 S ⊤ →
      (sec4W Ω S).Normal by
    intro G _ _ Ω hΩ hnil S hS
    exact h _ _ G rfl Ω rfl hΩ hnil S hS
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ihn =>
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ihm =>
  intro G _ _ hn Ω hm hΩ hnil S hS
  by_contra hW
  have ihQuot : ∀ (X : Subgroup G) (ΩX : Set (Subgroup G)), X ≠ ⊤ → ΩX ⊆ Ω →
      (∀ J ∈ ΩX, ∀ x ∈ X, AschbacherTightEmbedding.rightConjugate J x ∈ ΩX) → sSup ΩX = X →
      ∀ S' : Subgroup (X ⧸ CFSG.Assembly.oddCore X), IsSylowOf 2 S' ⊤ →
        (sec4W (imgΩ X ΩX) S').Normal := by
    intro X ΩX hX hsub hinv hgen S' hS'
    have hlt : Nat.card (X ⧸ CFSG.Assembly.oddCore X) < n := by
      rw [← hn]
      calc Nat.card (X ⧸ CFSG.Assembly.oddCore X) ≤ Nat.card X :=
            Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
        _ < Nat.card G := lt_of_le_of_ne (card_le_card_group X)
            fun h => hX (eq_top_of_card_eq X h)
    exact ihn _ hlt _ _ rfl _ rfl (assumption41_imgΩ hΩ hsub hinv hgen)
      (twoNil_imgΩ hgen fun K hK => hnil K (hsub hK)) S' hS'
  by_cases hsingle : ∃ K₀ ∈ Ω, ∀ K ∈ Ω, ∃ g : G, K = AschbacherTightEmbedding.rightConjugate K₀ g
  · exact hstep G Ω S ⟨hΩ, hnil, hS, hsingle, hW, ihQuot⟩
  apply hW
  apply sec4W_normal_of_rot_le hΩ
  intro J hJ T U hT hU
  set Ω₁ : Set (Subgroup G) :=
    {K | K ∈ Ω ∧ ∃ g : G, K = AschbacherTightEmbedding.rightConjugate J g} with hΩ₁
  have hsub : Ω₁ ⊆ Ω := fun K hK => hK.1
  have hinv : ∀ K ∈ Ω₁, ∀ g : G, AschbacherTightEmbedding.rightConjugate K g ∈ Ω₁ := by
    rintro K ⟨hK, h, rfl⟩ g
    exact ⟨hΩ.conj_mem _ hK g, h * g, rightConjugate_mul J h g⟩
  have hJ₁ : J ∈ Ω₁ := ⟨hJ, 1, (rightConjugate_one J).symm⟩
  have hlt : Ω₁.ncard < m := by
    rw [← hm]
    apply Set.ncard_lt_ncard _ (Set.toFinite Ω)
    refine ⟨hsub, fun hle => hsingle ⟨J, hJ, fun K hK => ?_⟩⟩
    exact (hle hK).2
  exact rot_le_of_subset hΩ hsub hinv rfl hS
    (fun _ hΩ₁' => ihm _ hlt G hn Ω₁ rfl hΩ₁' (fun K hK => hnil K (hsub hK)) S hS)
    (fun hX S' hS' => ihQuot _ Ω₁ hX hsub (fun K hK x _ => hinv K hK x) rfl S' hS')
    J hJ₁ T U hT hU

end CFSG.ComponentClassification.Asc76.Sec4
