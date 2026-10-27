module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D3

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def DStarAdj (Ω : Set (Subgroup G)) (K J : Subgroup G) : Prop :=
  K ∈ Ω ∧ J ∈ Ω ∧
    (∃ T V : Subgroup G, IsSylowOf 2 T J ∧ IsDihedralRot V T ∧ V ≤ normalizer (K : Set G)) ∧
    ∃ R U : Subgroup G, IsSylowOf 2 R K ∧ IsDihedralRot U R ∧ U ≤ normalizer (J : Set G)

@[expose] def dStarComp (Ω : Set (Subgroup G)) (K : Subgroup G) : Set (Subgroup G) :=
  {J | Relation.ReflTransGen (DStarAdj Ω) K J}

omit [Finite G] in
theorem DStarAdj.symm {K J : Subgroup G} (h : DStarAdj Ω K J) : DStarAdj Ω J K :=
  ⟨h.2.1, h.1, h.2.2.2, h.2.2.1⟩

theorem dStarAdj_of_le_normalizer (hΩ : Assumption41 Ω) {K J : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hJK : J ≤ normalizer (K : Set G)) (hKJ : K ≤ normalizer (J : Set G)) :
    DStarAdj Ω K J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hT⟩ := exists_isSylowOf 2 J
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hJ hT
  obtain ⟨R, hR⟩ := exists_isSylowOf 2 K
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  exact ⟨hK, hJ, ⟨T, V, hT, hV, (hV.le.trans hT.le).trans hJK⟩,
    ⟨R, U, hR, hU, (hU.le.trans hR.le).trans hKJ⟩⟩

theorem dStarAdj_of_commute (hΩ : Assumption41 Ω) {K J R U T V : Subgroup G} (hK : K ∈ Ω)
    (hJ : J ∈ Ω) (hR : IsSylowOf 2 R K) (hU : IsDihedralRot U R) (hT : IsSylowOf 2 T J)
    (hV : IsDihedralRot V T) (hc : ∀ u ∈ U, ∀ v ∈ V, u * v = v * u) : DStarAdj Ω K J := by
  obtain ⟨z, hzU, hz1, hzz, -, -⟩ := hU.exists_involution
  obtain ⟨t, htV, ht1, htt, -, -⟩ := hV.exists_involution
  refine ⟨hK, hJ, ⟨T, V, hT, hV, fun v hv => ?_⟩, ⟨R, U, hR, hU, fun u hu => ?_⟩⟩
  · exact Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hK)
      (hR.le (hU.le hzU)) hz1 hzz (mem_centralizer_singleton_iff.mpr (hc z hzU v hv).symm)
  · exact Sec4.centralizer_le_normalizer (Assumption41.tightlyEmbedded hΩ hJ)
      (hT.le (hV.le htV)) ht1 htt (mem_centralizer_singleton_iff.mpr (hc u hu t htV))

theorem dStarAdj_of_mem_omegaD (hΩ : Assumption41 Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {K J : Subgroup G} (hK : K ∈ omegaD Ω (sec4W Ω S)) (hJ : J ∈ omegaD Ω (sec4W Ω S)) :
    DStarAdj Ω K J := by
  obtain ⟨hKΩ, R, hR, hRW⟩ := hK
  obtain ⟨hJΩ, T, hT, hTW⟩ := hJ
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hKΩ hR
  obtain ⟨V, hV⟩ := Assumption41.exists_rot hΩ hJΩ hT
  have hUW := rot_le_sec4W hΩ hS hKΩ hR hU hRW
  have hVW := rot_le_sec4W hΩ hS hJΩ hT hV hTW
  exact dStarAdj_of_commute hΩ hKΩ hJΩ hR hU hT hV fun u hu v hv =>
    sec4W_mul_comm hΩ hS (hUW hu) (hVW hv)

theorem DStarAdj.rightConjugate (hΩ : Assumption41 Ω) {K J : Subgroup G} (h : DStarAdj Ω K J)
    (g : G) : DStarAdj Ω (AschbacherTightEmbedding.rightConjugate K g)
      (AschbacherTightEmbedding.rightConjugate J g) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK, hJ, ⟨T, V, hT, hV, hVK⟩, ⟨R, U, hR, hU, hUJ⟩⟩ := h
  refine ⟨hΩ.conj_mem K hK g, hΩ.conj_mem J hJ g,
    ⟨_, _, isSylowOf_rightConjugate hT g, hV.rightConjugate g, ?_⟩,
    ⟨_, _, isSylowOf_rightConjugate hR g, hU.rightConjugate g, ?_⟩⟩
  · rw [normalizer_rightConjugate]
    exact rightConjugate_le_rightConjugate hVK g
  · rw [normalizer_rightConjugate]
    exact rightConjugate_le_rightConjugate hUJ g

theorem reflTransGen_dStarAdj_rightConjugate (hΩ : Assumption41 Ω) {K J : Subgroup G}
    (h : Relation.ReflTransGen (DStarAdj Ω) K J) (g : G) :
    Relation.ReflTransGen (DStarAdj Ω) (AschbacherTightEmbedding.rightConjugate K g)
      (AschbacherTightEmbedding.rightConjugate J g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact ih.tail (hab.rightConjugate hΩ g)

omit [Finite G] in
theorem reflTransGen_dStarAdj_symm {K J : Subgroup G}
    (h : Relation.ReflTransGen (DStarAdj Ω) K J) : Relation.ReflTransGen (DStarAdj Ω) J K := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact Relation.ReflTransGen.head hab.symm ih

theorem rightConjugate_mem_dStarComp (hΩ : Assumption41 Ω) {K L J : Subgroup G}
    (hL : L ∈ dStarComp Ω K) (hJ : J ∈ dStarComp Ω K) {x : G}
    (hx : x ∈ normalizer (L : Set G)) :
    AschbacherTightEmbedding.rightConjugate J x ∈ dStarComp Ω K := by
  have h1 := reflTransGen_dStarAdj_rightConjugate hΩ hL x
  rw [(rightConjugate_eq_self_iff L x).mpr hx] at h1
  exact (hL.trans (reflTransGen_dStarAdj_symm h1)).trans
    (reflTransGen_dStarAdj_rightConjugate hΩ hJ x)

@[expose] def setStab (Λ : Set (Subgroup G)) : Subgroup G where
  carrier := {g | ∀ J, J ∈ Λ ↔ AschbacherTightEmbedding.rightConjugate J g ∈ Λ}
  one_mem' := fun J => by rw [rightConjugate_one]
  mul_mem' := by
    intro a b ha hb J
    rw [← rightConjugate_mul]
    exact (ha J).trans (hb _)
  inv_mem' := by
    intro a ha J
    have := ha (AschbacherTightEmbedding.rightConjugate J a⁻¹)
    rw [rightConjugate_mul, inv_mul_cancel, rightConjugate_one] at this
    exact this.symm

theorem le_setStab_dStarComp (hΩ : Assumption41 Ω) {K L : Subgroup G}
    (hL : L ∈ dStarComp Ω K) : L ≤ setStab (dStarComp Ω K) := by
  intro x hx J
  constructor
  · intro hJ
    exact rightConjugate_mem_dStarComp hΩ hL hJ (le_normalizer hx)
  · intro hJ
    have := rightConjugate_mem_dStarComp hΩ hL hJ (le_normalizer (inv_mem hx))
    rwa [rightConjugate_mul, mul_inv_cancel, rightConjugate_one] at this

theorem sSup_dStarComp_ne_top (hΩ : Assumption41 Ω)
    (hsingle : ∃ K₀ ∈ Ω, ∀ K ∈ Ω, ∃ g : G, K = AschbacherTightEmbedding.rightConjugate K₀ g)
    {K : Subgroup G} (hK : K ∈ Ω) {J : Subgroup G} (hJ : J ∈ Ω) (hJK : J ∉ dStarComp Ω K) :
    sSup (dStarComp Ω K) ≠ ⊤ := by
  intro htop
  have hle : (⊤ : Subgroup G) ≤ setStab (dStarComp Ω K) := by
    rw [← htop]
    exact sSup_le fun L hL => le_setStab_dStarComp hΩ hL
  obtain ⟨K₀, -, hall⟩ := hsingle
  obtain ⟨a, rfl⟩ := hall K hK
  obtain ⟨b, rfl⟩ := hall J hJ
  apply hJK
  have h1 := (hle (mem_top (a⁻¹ * b)) (AschbacherTightEmbedding.rightConjugate K₀ a)).mp
    Relation.ReflTransGen.refl
  rwa [rightConjugate_mul, mul_inv_cancel_left] at h1

theorem MinCounter.mem_omegaD_of_le_sSup_dStarComp {S : Subgroup G} (hM : MinCounter Ω S)
    {K : Subgroup G} (hK : K ∈ omegaD Ω (sec4W Ω S)) (hX : sSup (dStarComp Ω K) ≠ ⊤)
    {L : Subgroup G} (hL : L ∈ Ω) (hLX : L ≤ sSup (dStarComp Ω K)) :
    L ∈ omegaD Ω (sec4W Ω S) := by
  have hΩ := hM.assumption
  set X := sSup (dStarComp Ω K) with hXdef
  have hCΩ : ∀ J ∈ dStarComp Ω K, J ∈ Ω := by
    intro J hJ
    induction hJ with
    | refl => exact hK.1
    | tail _ hab _ => exact hab.2.1
  have hgen : sSup {L | L ∈ Ω ∧ L ≤ X} = X :=
    le_antisymm (sSup_le fun _ hL => hL.2)
      (sSup_le fun J hJ => le_sSup ⟨hCΩ J hJ, le_sSup hJ⟩)
  have hD : ∀ L ∈ omegaD Ω (sec4W Ω S), L ≤ X := fun L hL' =>
    le_sSup (Relation.ReflTransGen.single (dStarAdj_of_mem_omegaD hΩ hM.sylow hK hL'))
  exact hM.mem_omegaD_of_le hX hgen hD hL hLX

theorem MinCounter.dStarComp_eq_omegaD {S : Subgroup G} (hM : MinCounter Ω S)
    {K : Subgroup G} (hK : K ∈ omegaD Ω (sec4W Ω S)) (hX : sSup (dStarComp Ω K) ≠ ⊤) :
    dStarComp Ω K = omegaD Ω (sec4W Ω S) := by
  have hΩ := hM.assumption
  ext J
  constructor
  · intro hJ
    have hJΩ : J ∈ Ω := by
      induction hJ with
      | refl => exact hK.1
      | tail _ hab _ => exact hab.2.1
    exact hM.mem_omegaD_of_le_sSup_dStarComp hK hX hJΩ (le_sSup hJ)
  · intro hJ
    exact Relation.ReflTransGen.single (dStarAdj_of_mem_omegaD hΩ hM.sylow hK hJ)

end CFSG.ComponentClassification.Asc76.Sec4
