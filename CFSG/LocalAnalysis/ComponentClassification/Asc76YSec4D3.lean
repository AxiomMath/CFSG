module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D2
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4Conn

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def omegaD (Ω : Set (Subgroup G)) (W : Subgroup G) : Set (Subgroup G) :=
  {L | L ∈ Ω ∧ ∃ T : Subgroup G, IsSylowOf 2 T L ∧ T ≤ normalizer (W : Set G)}

theorem exists_conj_le_of_imgOf_le {X P Q : Subgroup G} (hQX : Q ≤ X)
    (hP : IsPGroup 2 P) (hQ : IsPGroup 2 Q) (hle : imgOf X Q ≤ imgOf X P) :
    ∃ o ∈ oddCoreIn X, ∀ x ∈ Q, o * x * o⁻¹ ∈ P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P' : Subgroup X := P.subgroupOf X
  set Q' : Subgroup X := Q.subgroupOf X
  have hP' : IsPGroup 2 P' := hP.comap_subtype
  have hQ' : IsPGroup 2 Q' := hQ.comap_subtype
  have hsyl := isSylowOf_oddCore_sup hP'
  have hQle : Q' ≤ CFSG.Assembly.oddCore X ⊔ P' := by
    rw [← comap_eq_oddCore_sup (rfl : P'.map (QuotientGroup.mk' (CFSG.Assembly.oddCore X)) =
      imgOf X P)]
    intro q hq
    exact hle (mem_map_of_mem _ hq)
  obtain ⟨Q₁, hQ₁, hQQ₁⟩ := exists_isSylowOf_le hQ' hQle
  obtain ⟨c, hc, hcQ⟩ := CFSG.ComponentClassification.Asc76.L26.IsSylowOf.exists_conj_mem hsyl hQ₁
  have hc' : c ∈ ((CFSG.Assembly.oddCore X ⊔ P' : Subgroup X) : Set X) := hc
  rw [Subgroup.normal_mul] at hc'
  obtain ⟨o, ho, p, hp, rfl⟩ := hc'
  refine ⟨((o⁻¹ : X) : G), ⟨o⁻¹, inv_mem ho, rfl⟩, fun x hx => ?_⟩
  have hxX := hQX hx
  have h1 := (hcQ ⟨x, hxX⟩).mp (hQQ₁ (show (⟨x, hxX⟩ : X) ∈ Q' from hx))
  have h2 : (p : X) * ((o * p)⁻¹ * ⟨x, hxX⟩ * (o * p)) * p⁻¹ ∈ P' :=
    (mem_normalizer_iff.mp (le_normalizer hp) _).mp h1
  have h3 : (p : X) * ((o * p)⁻¹ * ⟨x, hxX⟩ * (o * p)) * p⁻¹ = o⁻¹ * ⟨x, hxX⟩ * o := by group
  rw [h3] at h2
  have h4 : ((o⁻¹ * ⟨x, hxX⟩ * o : X) : G) = ((o⁻¹ : X) : G) * x * ((o⁻¹ : X) : G)⁻¹ := by
    simp
  rw [← h4]
  exact h2

omit [Finite G] in
theorem imgOf_self (X : Subgroup G) : imgOf X X = ⊤ := by
  rw [imgOf, subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
  exact QuotientGroup.mk'_surjective _

theorem exists_rot_imgOf_eq (hΩ : Assumption41 Ω) {X L : Subgroup G} (hL : L ∈ Ω) (hLX : L ≤ X)
    {R U : Subgroup (X ⧸ CFSG.Assembly.oddCore X)} (hR : IsSylowOf 2 R (imgOf X L))
    (hU : IsDihedralRot U R) :
    ∃ T V : Subgroup G, IsSylowOf 2 T L ∧ IsDihedralRot V T ∧ imgOf X V = U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT, hRT⟩ := exists_sylow_imgOf_le hLX hR.isPGroup hR.le
  have hTs := isSylowOf_imgOf hT hLX
  have hReq : imgOf X T = R := hR.eq_of_le hRT hTs.le hTs.isPGroup
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hL hT
  have hV' : IsDihedralRot (imgOf X V) (imgOf X T) :=
    (hV.subgroupOf (hT.le.trans hLX)).map _ (mk_injOn hT.isPGroup)
  rw [hReq] at hV'
  exact ⟨T, V, hT, hV, (hV'.eq_of_isCyclic hU.le hU.isCyclic hU.relIndex_eq).symm⟩

omit [Finite G] in
theorem membersIn_inv (hΩ : Assumption41 Ω) (X : Subgroup G) :
    ∀ J ∈ {L | L ∈ Ω ∧ L ≤ X}, ∀ x ∈ X,
      AschbacherTightEmbedding.rightConjugate J x ∈ {L | L ∈ Ω ∧ L ≤ X} := by
  rintro J ⟨hJ, hJX⟩ x hx
  refine ⟨hΩ.conj_mem J hJ x, (rightConjugate_le_rightConjugate hJX x).trans ?_⟩
  rw [(rightConjugate_eq_self_iff X x).mpr (le_normalizer hx)]

theorem sec4W_le_of_omegaD_le (hΩ : Assumption41 Ω) {S X : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hD : ∀ L ∈ omegaD Ω (sec4W Ω S), L ≤ X) : sec4W Ω S ≤ X := by
  refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
  obtain ⟨K, hK, R₀, hR₀, hU₀⟩ := IsRot.exists_isDihedralRot hΩ hU
  obtain ⟨R, hR, hUR, hRW⟩ := exists_isSylowOf_le_normalizer_of_isRot hΩ hS hK hR₀ hU₀
    (le_sec4W hUS hU)
  exact (hUR.le.trans hR.le).trans (hD K ⟨hK, R, hR, hRW⟩)

theorem imgOf_sec4W_eq (hΩ : Assumption41 Ω) {S X : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hgen : sSup {L | L ∈ Ω ∧ L ≤ X} = X) (hD : ∀ L ∈ omegaD Ω (sec4W Ω S), L ≤ X)
    {P₀ : Subgroup G} (hP₀ : IsSylowOf 2 P₀ X) (hWP₀ : sec4W Ω S ≤ P₀) :
    imgOf X (sec4W Ω S) = sec4W (imgΩ X {L | L ∈ Ω ∧ L ≤ X}) (imgOf X P₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set W := sec4W Ω S with hWdef
  set ΩX : Set (Subgroup G) := {L | L ∈ Ω ∧ L ≤ X} with hΩX
  set π := QuotientGroup.mk' (CFSG.Assembly.oddCore X) with hπ
  have hWX : W ≤ X := sec4W_le_of_omegaD_le hΩ hS hD
  have hΩ' := assumption41_imgΩ hΩ (fun L hL => hL.1) (membersIn_inv hΩ X) hgen
  obtain ⟨S', hS', hP₀S'⟩ := exists_isSylowOf_le hP₀.isPGroup (le_top : P₀ ≤ ⊤)
  have hWS' : sec4W Ω S' = W := sec4W_eq_of_le hΩ hS hS' (hWP₀.trans hP₀S')
  apply le_antisymm
  ·
    rintro _ ⟨⟨w, hwX⟩, hw, rfl⟩
    have hw' : w ∈ W := hw
    set Wpre : Subgroup G :=
      ((sec4W (imgΩ X ΩX) (imgOf X P₀)).comap π).map X.subtype with hWpre
    have hle : W ≤ Wpre := by
      refine iSup_le fun U => iSup_le fun hUS => iSup_le fun hU => ?_
      obtain ⟨K, hK, R₀, hR₀, hU₀⟩ := IsRot.exists_isDihedralRot hΩ hU
      obtain ⟨R, hR, hUR, hRW⟩ := exists_isSylowOf_le_normalizer_of_isRot hΩ hS hK hR₀ hU₀
        (le_sec4W hUS hU)
      have hKX : K ≤ X := hD K ⟨hK, R, hR, hRW⟩
      have hUX : U ≤ X := (hUR.le.trans hR.le).trans hKX
      have hUrot : IsRot (imgΩ X ΩX) (imgOf X U) :=
        isRot_of ⟨K, ⟨hK, hKX⟩, rfl⟩ (isSylowOf_imgOf hR hKX)
          ((hUR.subgroupOf (hR.le.trans hKX)).map _ (mk_injOn hR.isPGroup))
      have hUP : imgOf X U ≤ imgOf X P₀ := imgOf_mono ((le_sec4W hUS hU).trans hWP₀)
      intro u hu
      exact ⟨⟨u, hUX hu⟩, le_sec4W hUP hUrot (mem_map_of_mem _ hu), rfl⟩
    obtain ⟨y, hy, hyw⟩ := hle hw'
    have : y = ⟨w, hwX⟩ := Subtype.ext hyw
    rw [← this]
    exact hy
  ·
    refine iSup_le fun Ub => iSup_le fun hUbS => iSup_le fun hUb => ?_
    obtain ⟨Kb, ⟨L, hL, rfl⟩, Rb, hRb, hUbR⟩ := IsRot.exists_isDihedralRot hΩ' hUb
    obtain ⟨T, V, hT, hV, hVeq⟩ := exists_rot_imgOf_eq hΩ hL.1 hL.2 hRb hUbR
    have hVX : V ≤ X := (hV.le.trans hT.le).trans hL.2
    have hle' : imgOf X V ≤ imgOf X P₀ := by rw [hVeq]; exact hUbS
    obtain ⟨o, ho, hoV⟩ := exists_conj_le_of_imgOf_le hVX hP₀.isPGroup
      (hV.isPGroup.to_le hV.le) hle'
    obtain ⟨o', ho', rfl⟩ := ho
    have hV'S : AschbacherTightEmbedding.rightConjugate V ((o'⁻¹ : X) : G) ≤ S' := by
      intro y hy
      rw [mem_rightConjugate_iff, coe_inv, inv_inv] at hy
      have h1 := hoV _ hy
      have h2 : X.subtype o' * ((o' : G)⁻¹ * y * o') * (X.subtype o')⁻¹ = y := by
        simp only [coe_subtype]
        group
      rw [h2] at h1
      exact hP₀S' h1
    have hV'rot : IsRot Ω (AschbacherTightEmbedding.rightConjugate V ((o'⁻¹ : X) : G)) :=
      (isRot_of hL.1 hT hV).rightConjugate hΩ _
    have hV'W : AschbacherTightEmbedding.rightConjugate V ((o'⁻¹ : X) : G) ≤ W :=
      hWS' ▸ le_sec4W hV'S hV'rot
    have himg : imgOf X (AschbacherTightEmbedding.rightConjugate V ((o'⁻¹ : X) : G)) =
        imgOf X V := by
      rw [imgOf_rightConjugate]
      have : QuotientGroup.mk' (CFSG.Assembly.oddCore X) o'⁻¹ = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact inv_mem ho'
      rw [this, rightConjugate_one]
    rw [← hVeq, ← himg]
    exact imgOf_mono hV'W

theorem MinCounter.imgOf_sec4W_normal {S : Subgroup G} (hM : MinCounter Ω S) {X : Subgroup G}
    (hX : X ≠ ⊤) (hgen : sSup {L | L ∈ Ω ∧ L ≤ X} = X)
    (hD : ∀ L ∈ omegaD Ω (sec4W Ω S), L ≤ X) : (imgOf X (sec4W Ω S)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  have hWX := sec4W_le_of_omegaD_le hΩ hM.sylow hD
  obtain ⟨P₀, hP₀, hWP₀⟩ := exists_isSylowOf_le (hM.sylow.isPGroup.to_le (sec4W_le S)) hWX
  have hS₀ : IsSylowOf 2 (imgOf X P₀) ⊤ := by
    have := isSylowOf_imgOf hP₀ le_rfl
    rwa [imgOf_self] at this
  rw [imgOf_sec4W_eq hΩ hM.sylow hgen hD hP₀ hWP₀]
  exact hM.ihQuot X _ hX (fun L hL => hL.1) (membersIn_inv hΩ X) hgen _ hS₀

omit [Finite G] in
theorem imgOf_sup_oddCoreIn_le {X W : Subgroup G} (hWX : W ≤ X) :
    imgOf X (W ⊔ oddCoreIn X) ≤ imgOf X W := by
  have hON : W ≤ normalizer (oddCoreIn X : Set G) := hWX.trans (le_normalizer_oddCoreIn X)
  rintro _ ⟨⟨y, hyX⟩, hy, rfl⟩
  have hy' : y ∈ ((W ⊔ oddCoreIn X : Subgroup G) : Set G) := hy
  rw [Subgroup.coe_mul_of_left_le_normalizer_right W (oddCoreIn X) hON] at hy'
  obtain ⟨w, hw, o, ho, rfl⟩ := hy'
  obtain ⟨o', ho', rfl⟩ := ho
  refine ⟨⟨w, hWX hw⟩, hw, ?_⟩
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
  have e : (⟨w, hWX hw⟩ : X)⁻¹ * ⟨(fun x1 x2 => x1 * x2) w (X.subtype o'), hyX⟩ = o' :=
    Subtype.ext (by simp)
  rw [e]
  exact ho'

theorem MinCounter.mem_omegaD_of_le {S : Subgroup G} (hM : MinCounter Ω S) {X : Subgroup G}
    (hX : X ≠ ⊤) (hgen : sSup {L | L ∈ Ω ∧ L ≤ X} = X)
    (hD : ∀ L ∈ omegaD Ω (sec4W Ω S), L ≤ X) {L : Subgroup G} (hL : L ∈ Ω) (hLX : L ≤ X) :
    L ∈ omegaD Ω (sec4W Ω S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hΩ := hM.assumption
  set W := sec4W Ω S with hWdef
  have hW2 : IsPGroup 2 W := hM.sylow.isPGroup.to_le (sec4W_le S)
  have hWX := sec4W_le_of_omegaD_le hΩ hM.sylow hD
  have hWn := hM.imgOf_sec4W_normal hX hgen hD
  set B : Subgroup G := W ⊔ oddCoreIn X with hB
  have hBX : B ≤ X := sup_le hWX (oddCoreIn_le X)
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 L
  have hTX : T ≤ X := hT.le.trans hLX
  have hTB : T ≤ normalizer (B : Set G) := by
    intro x hx
    have hxX := hTX hx
    apply mem_normalizer_of_map_conj_le
    rw [map_le_iff_le_comap]
    refine sup_le (fun w hw => ?_) (fun o ho => ?_)
    · have h1 := conj_mem_sup_of_mem_normalizer_imgOf hWX hxX
        ((normalizer_eq_top_iff.mpr hWn).ge (mem_top _)) w hw
      simpa [MulAut.conj_apply] using h1
    · have := (mem_normalizer_iff.mp (le_normalizer_oddCoreIn X hxX) o).mp ho
      exact mem_sup_right (by simpa [MulAut.conj_apply] using this)
  obtain ⟨P, hP, hTP⟩ := exists_isSylowOf_normalized hT.isPGroup hTB
  have hPimg : imgOf X P ≤ imgOf X W :=
    (imgOf_mono hP.le).trans (imgOf_sup_oddCoreIn_le hWX)
  obtain ⟨o, ho, hoP⟩ := exists_conj_le_of_imgOf_le (hP.le.trans hBX) hW2 hP.isPGroup hPimg
  obtain ⟨W₁, hW₁, hWW₁⟩ := exists_isSylowOf_le hW2 (le_sup_left : W ≤ B)
  have hcard : Nat.card W ≤ Nat.card P := by
    rw [hP.card_eq, ← hW₁.card_eq]
    exact card_le_of_le hWW₁
  have hPW : AschbacherTightEmbedding.rightConjugate P o⁻¹ = W := by
    apply eq_of_le_of_card_ge
    · intro y hy
      rw [mem_rightConjugate_iff, inv_inv] at hy
      have := hoP _ hy
      have e : o * (o⁻¹ * y * o) * o⁻¹ = y := by group
      rwa [e] at this
    · rw [rightConjugate_card]
      exact hcard
  have hON := oddCoreIn_le_normalizer_of_le hΩ hL hLX
  refine ⟨hL, AschbacherTightEmbedding.rightConjugate T o⁻¹, ?_, ?_⟩
  · have h1 := isSylowOf_rightConjugate hT o⁻¹
    rwa [(rightConjugate_eq_self_iff L _).mpr (inv_mem (hON ho))] at h1
  · rw [← hPW]
    intro y hy
    rw [mem_rightConjugate_iff, inv_inv] at hy
    have h2 := hTP hy
    rw [mem_normalizer_iff] at h2 ⊢
    intro p
    rw [mem_rightConjugate_iff, mem_rightConjugate_iff, inv_inv]
    have e : o⁻¹ * (y * p * y⁻¹) * o = (o⁻¹ * y * o) * (o⁻¹ * p * o) * (o⁻¹ * y * o)⁻¹ := by
      group
    rw [e]
    exact h2 _

end CFSG.ComponentClassification.Asc76.Sec4
