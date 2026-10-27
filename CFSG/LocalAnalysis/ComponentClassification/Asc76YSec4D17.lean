module

public import CFSG.LocalAnalysis.ComponentClassification.Asc76S4AFacts
public import CFSG.LocalAnalysis.ComponentClassification.Asc76YSec4D5

public section

namespace CFSG.ComponentClassification.Asc76.Sec4

open Subgroup CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.AschbacherTheorem3

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

@[expose] def DConnOn (Ω Λ : Set (Subgroup G)) : Prop :=
  ∀ K ∈ Λ, ∀ J ∈ Λ, Relation.ReflTransGen (DAdj Ω) K J

theorem eq_or_dAdj_of_commute (H : Sec4Hyp Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    {K J T₁ T₂ : Subgroup G} (hK : K ∈ Ω) (hJ : J ∈ Ω) (h₁ : IsSylowOf 2 T₁ K)
    (h₂ : IsSylowOf 2 T₂ J) (hT₁W : T₁ ≤ normalizer (sec4W Ω S : Set G))
    (hT₂W : T₂ ≤ normalizer (sec4W Ω S : Set G)) {d₁ d₂ : NBar (sec4W Ω S)}
    (hd₁ : IsBarOf (sec4W Ω S) T₁ d₁) (hd₂ : IsBarOf (sec4W Ω S) T₂ d₂)
    (hc : d₁ * d₂ = d₂ * d₁) : K = J ∨ DAdj Ω K J := by
  by_cases hKJ : K = J
  · exact Or.inl hKJ
  right
  have hsyl : T₂ ≤ normalizer (K : Set G) := by
    by_contra hnot
    exact bar_not_commute_of_not_sylow H hS hK hJ hKJ h₁ h₂ hT₁W hT₂W hnot hd₁ hd₂ hc
  obtain ⟨hJK, hKJ'⟩ := le_normalizer_of_sylow H.h22 H.hΩ hK hJ hKJ h₂ hsyl
  exact ⟨hK, hJ, hJK, hKJ'⟩

theorem dConnOn_omegaD_of_connected (H : Sec4Hyp Ω) {S : Subgroup G} (hS : IsSylowOf 2 S ⊤)
    (hc : (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected) :
    DConnOn Ω (omegaD Ω (sec4W Ω S)) := by
  set W := sec4W Ω S with hWdef
  have key : ∀ (a b : DBar Ω W) (p : (CFSG.Fischer.commGraph (DBar Ω W)).Walk a b),
      ∀ K T₁, K ∈ Ω → IsSylowOf 2 T₁ K → T₁ ≤ normalizer (W : Set G) →
        IsBarOf W T₁ (a : NBar W) →
      ∀ J T₂, J ∈ Ω → IsSylowOf 2 T₂ J → T₂ ≤ normalizer (W : Set G) →
        IsBarOf W T₂ (b : NBar W) → Relation.ReflTransGen (DAdj Ω) K J := by
    intro a b p
    induction p with
    | nil =>
      intro K T₁ hK h₁ hT₁W hd₁ J T₂ hJ h₂ hT₂W hd₂
      rcases eq_or_dAdj_of_commute H hS hK hJ h₁ h₂ hT₁W hT₂W hd₁ hd₂ rfl with h | h
      · rw [h]
      · exact Relation.ReflTransGen.single h
    | cons hadj p ih =>
      rename_i u v w
      intro K T₁ hK h₁ hT₁W hd₁ J T₂ hJ h₂ hT₂W hd₂
      obtain ⟨T, ⟨⟨L, hL, hTL⟩, hTW⟩, hdT⟩ := DBar.exists_isBarOf v.2
      have h1 := ih L T hL hTL hTW hdT J T₂ hJ h₂ hT₂W hd₂
      rcases eq_or_dAdj_of_commute H hS hK hL h₁ hTL hT₁W hTW hd₁ hdT hadj.2 with h | h
      · rw [h]
        exact h1
      · exact Relation.ReflTransGen.head h h1
  intro K hK J hJ
  obtain ⟨hKΩ, T₁, h₁, hT₁W⟩ := hK
  obtain ⟨hJΩ, T₂, h₂, hT₂W⟩ := hJ
  have hT₁D : T₁ ∈ DSet Ω W := ⟨⟨K, hKΩ, h₁⟩, hT₁W⟩
  have hT₂D : T₂ ∈ DSet Ω W := ⟨⟨J, hJΩ, h₂⟩, hT₂W⟩
  obtain ⟨d₁, hd₁⟩ := IsBarOf.exists_of_mem H.hΩ hT₁D
  obtain ⟨d₂, hd₂⟩ := IsBarOf.exists_of_mem H.hΩ hT₂D
  obtain ⟨p⟩ := hc.preconnected ⟨d₁, IsBarOf.mem_dBar hT₁D hd₁⟩ ⟨d₂, IsBarOf.mem_dBar hT₂D hd₂⟩
  exact key _ _ p K T₁ hKΩ h₁ hT₁W hd₁ J T₂ hJΩ h₂ hT₂W hd₂

omit [Finite G] in
theorem DAdj.rightConjugate (hΩ : Assumption41 Ω) {K J : Subgroup G} (h : DAdj Ω K J) (g : G) :
    DAdj Ω (AschbacherTightEmbedding.rightConjugate K g)
      (AschbacherTightEmbedding.rightConjugate J g) := by
  obtain ⟨hK, hJ, hJK, hKJ⟩ := h
  refine ⟨hΩ.conj_mem K hK g, hΩ.conj_mem J hJ g, ?_, ?_⟩
  · rw [normalizer_rightConjugate]
    exact rightConjugate_le_rightConjugate hJK g
  · rw [normalizer_rightConjugate]
    exact rightConjugate_le_rightConjugate hKJ g

omit [Finite G] in
theorem reflTransGen_dAdj_rightConjugate (hΩ : Assumption41 Ω) {K J : Subgroup G}
    (h : Relation.ReflTransGen (DAdj Ω) K J) (g : G) :
    Relation.ReflTransGen (DAdj Ω) (AschbacherTightEmbedding.rightConjugate K g)
      (AschbacherTightEmbedding.rightConjugate J g) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact ih.tail (hab.rightConjugate hΩ g)

theorem rightConjugate_mem_omegaD (hΩ : Assumption41 Ω) {S L : Subgroup G}
    (hL : L ∈ omegaD Ω (sec4W Ω S)) (g : G) :
    AschbacherTightEmbedding.rightConjugate L g ∈
      omegaD Ω (sec4W Ω (AschbacherTightEmbedding.rightConjugate S g)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hLΩ, T, hT, hTW⟩ := hL
  refine ⟨hΩ.conj_mem L hLΩ g, _, isSylowOf_rightConjugate hT g, ?_⟩
  rw [← rightConjugate_sec4W hΩ.conj_mem S g, normalizer_rightConjugate]
  exact rightConjugate_le_rightConjugate hTW g

theorem dConnOn_omegaD_of_sylow (hΩ : Assumption41 Ω) {S S' : Subgroup G}
    (hS : IsSylowOf 2 S ⊤) (hS' : IsSylowOf 2 S' ⊤) (h : DConnOn Ω (omegaD Ω (sec4W Ω S))) :
    DConnOn Ω (omegaD Ω (sec4W Ω S')) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, -, hk⟩ := L26.IsSylowOf.exists_conj_mem hS' hS
  have hSeq : S = AschbacherTightEmbedding.rightConjugate S' k⁻¹ := by
    ext x
    rw [hk x, mem_rightConjugate_iff, inv_inv]
  intro K hK J hJ
  have hK' := rightConjugate_mem_omegaD hΩ hK k⁻¹
  have hJ' := rightConjugate_mem_omegaD hΩ hJ k⁻¹
  rw [← hSeq] at hK' hJ'
  have h1 := reflTransGen_dAdj_rightConjugate hΩ (h _ hK' _ hJ') k
  rwa [rightConjugate_mul, inv_mul_cancel, rightConjugate_one, rightConjugate_mul,
    inv_mul_cancel, rightConjugate_one] at h1

theorem dAdj_or_exists_omegaD_of_dStarAdj (h22 : Asc76Lemma22) (hΩ : Assumption41 Ω)
    {K J : Subgroup G} (h : DStarAdj Ω K J) :
    DAdj Ω K J ∨ ∃ S' : Subgroup G, IsSylowOf 2 S' ⊤ ∧ K ∈ omegaD Ω (sec4W Ω S') ∧
      J ∈ omegaD Ω (sec4W Ω S') := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hK, hJ, ⟨T, V₀, hT, hV₀, hV₀K⟩, -⟩ := h
  by_cases hadj : DAdj Ω K J
  · exact Or.inl hadj
  right
  have hV₀2 : IsPGroup 2 V₀ := hV₀.isPGroup.to_le hV₀.le
  obtain ⟨V, hV, hV₀V⟩ := exists_isSylowOf_le hV₀2 (le_inf (hV₀.le.trans hT.le) hV₀K)
  have hV1 : V ≠ ⊥ := by
    intro hb
    have := card_le_of_le hV₀V
    rw [hb, card_bot] at this
    have := hV₀.four_le
    omega
  obtain ⟨R, hR, hVR⟩ := exists_isSylowOf_normalized hV.isPGroup (hV.le.trans inf_le_right)
  obtain ⟨U, hU⟩ := Assumption41.exists_rot hΩ hK hR
  rcases lemma415 h22 hΩ hK hJ hR hU hV hV1 hVR with ⟨-, hJK, hKJ⟩ | ⟨⟨e⟩, -, -, -⟩ |
    ⟨hV2, -, -⟩
  · exact absurd ⟨hK, hJ, hJK, hKJ⟩ hadj
  · have hcardV : Nat.card V = Nat.card U := Nat.card_congr e.toEquiv
    have hVc : IsCyclic V := by
      have := hU.isCyclic
      exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
    obtain ⟨T', hT', hVT'⟩ := exists_isDihedralRot_of_isCyclic hΩ hJ hK hR hU
      (hV.le.trans inf_le_left) hV.isPGroup hVc hcardV
    have hP : IsPGroup 2 (V ⊔ R : Subgroup G) :=
      IsPGroup.to_sup_of_normal_right' hV.isPGroup hR.isPGroup hVR
    obtain ⟨S', hS', hPS'⟩ := exists_isSylowOf_le hP (le_top : V ⊔ R ≤ ⊤)
    have hRW : R ≤ normalizer (sec4W Ω S' : Set G) :=
      (le_sup_right.trans hPS').trans (le_normalizer_sec4W hΩ.conj_mem S')
    have hVW : V ≤ sec4W Ω S' := le_sec4W (le_sup_left.trans hPS') (isRot_of hJ hT' hVT')
    obtain ⟨T₁, hT₁, -, hT₁W⟩ := exists_isSylowOf_le_normalizer_of_isRot hΩ hS' hJ hT' hVT' hVW
    exact ⟨S', hS', ⟨hK, R, hR, hRW⟩, ⟨hJ, T₁, hT₁, hT₁W⟩⟩
  · exfalso
    have := card_le_of_le hV₀V
    have := hV₀.four_le
    omega

theorem MinCounter.not_connected_commGraph (h22 : Asc76Lemma22) {S : Subgroup G}
    (hM : MinCounter Ω S) (hconn : ∀ K ∈ Ω, ∀ J ∈ Ω, J ∈ dStarComp Ω K) :
    ¬ (CFSG.Fischer.commGraph (DBar Ω (sec4W Ω S))).Connected := by
  intro hc
  have hΩ := hM.assumption
  have H : Sec4Hyp Ω := ⟨h22, hΩ, hM.twoNil⟩
  have hD := dConnOn_omegaD_of_connected H hM.sylow hc
  have hedge : ∀ K J, DStarAdj Ω K J → Relation.ReflTransGen (DAdj Ω) K J := by
    intro K J h
    rcases dAdj_or_exists_omegaD_of_dStarAdj h22 hΩ h with h' | ⟨S', hS', hK, hJ⟩
    · exact Relation.ReflTransGen.single h'
    · exact dConnOn_omegaD_of_sylow hΩ hM.sylow hS' hD K hK J hJ
  apply hM.not_dConnected
  intro K hK J hJ
  have hp : Relation.ReflTransGen (DStarAdj Ω) K J := hconn K hK J hJ
  induction hp with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hab ih => exact (ih hab.1).trans (hedge _ _ hab)

end CFSG.ComponentClassification.Asc76.Sec4
