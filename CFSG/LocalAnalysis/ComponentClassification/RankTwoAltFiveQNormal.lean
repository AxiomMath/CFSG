module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveQ
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltFiveQbar

public section

open Subgroup CFSG.GH74.Uniqueness.SU.SU5 CFSG.Open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding CFSG.ComponentClassification.AS76b

namespace CFSG.ComponentClassification.RankTwoAltFive

variable {G : Type} [Group G] [Finite G]

namespace Setting310

variable {A R T V₀ : Subgroup G} {g : G} (h : Setting310 A R g T V₀)
include h

section PStructure

variable {P : Subgroup G} (hP : IsSylowOf 2 P (transvGroup (R ⊔ T) V₀))
  (hPC : P ⊓ centralizer ((R ⊔ T : Subgroup G) : Set G) = R ⊔ T)
include hP hPC

section IIa

variable (hIIa : ¬ centralizer (A : Set G) ⊓ normalizer (R : Set G) ≤ centralizer (R : Set G))
include hIIa

theorem qbarNoComponent_of_eps_one
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} {Q : Subgroup G} (hQ : QFacts (S : Subgroup G) V₀ z Q) :
    AS81.QbarNoComponent z Q := by
  classical
  have : Fintype G := Fintype.ofFinite G
  have hV₀2 : ∀ w ∈ V₀, w * w = 1 := fun w hw => h.mul_self (h.V₀_le hw)
  have hz2 : z * z = 1 := hV₀2 z hQ.z_mem_V₀
  have hzP : z ∈ P := hVP (h.V₀_le hQ.z_mem_V₀)
  obtain ⟨x, -, hemb⟩ := h.j2Emb_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16
    hinf hsup hV'inv S hPS hQ.z_mem_V₀ hQ.z_ne_one
  obtain ⟨zS, hzS⟩ := hemb.exists_zgen
  have hzzS : z = zS :=
    ((hzS.2.2 z (hQ.le hQ.z_mem)).mp fun s hs => hQ.z_central s hs).resolve_left hQ.z_ne_one
  rw [← hzzS] at hzS
  have hJ := hemb.facts hzS
  obtain ⟨R', -, -, -, -, -, huniq, -, -, -, -, -, hinv, -, -, -⟩ := hJ.RV
  have hQR' : Q = R' := huniq Q hQ.le hQ.normal hQ.q8d8
  obtain ⟨hQ32, ζ, -, -, hcen, hsq⟩ := hQ.q8d8.facts
  have hzζ : z = ζ :=
    ((hcen z hQ.z_mem).mp fun m hm => hQ.z_central m (hQ.le hm)).resolve_left hQ.z_ne_one
  rw [← hzζ] at hsq
  have hQsq : ∀ y ∈ Q, y * y ∈ zpowers z := fun y hy => by
    rcases hsq y hy with h1 | h1
    · rw [h1]; exact one_mem _
    · rw [h1]; exact mem_zpowers z
  have hzpow : ∀ y : G, y ∈ zpowers z ↔ y = 1 ∨ y = z := fun y =>
    ⟨eq_one_or_eq_of_mem_zpowers_of_sq hz2, by
      rintro (h1 | h1) <;> rw [h1]
      · exact one_mem _
      · exact mem_zpowers z⟩
  have hZcP : ∀ v, v ∈ Zc P ↔ v ∈ V₀ := fun v =>
    ⟨h.mem_V₀_of_mem_Zc hP hPC hP64 hVP, fun hv =>
      mem_Zc.mpr ⟨hVP (h.V₀_le hv), fun y hy => (P_comm_V₀ hP hv hy).symm⟩⟩
  have hinvQ : ∀ y : G, (y ∈ Q ∧ y * y = 1 ∧ y ∉ zpowers z) ↔
      ((y ∈ V₀ ∧ y ≠ 1 ∧ y ≠ z) ∨ (y ∈ (S : Subgroup G) ∧ y ∉ P ∧ y * y = 1)) := by
    intro y
    constructor
    · rintro ⟨hyQ, hy2, hyz⟩
      rw [hzpow] at hyz
      push Not at hyz
      rcases (hinv y (hQ.le hyQ)).mp ⟨hQR' ▸ hyQ, hyz.1, by rw [sq]; exact hy2⟩ with
        ⟨hyZ, -⟩ | ⟨hyP, -⟩
      · exact Or.inl ⟨(hZcP y).mp hyZ, hyz.1, hyz.2⟩
      · exact Or.inr ⟨hQ.le hyQ, hyP, hy2⟩
    · rintro (⟨hyV, hy1, hyz⟩ | ⟨hyS, hyP, hy2⟩)
      · refine ⟨hQ.V₀_le hyV, hV₀2 y hyV, ?_⟩
        rw [hzpow]
        push Not
        exact ⟨hy1, hyz⟩
      · have h1 := (hinv y hyS).mpr (Or.inr ⟨hyP, by rw [sq]; exact hy2⟩)
        refine ⟨hQR' ▸ h1.1, hy2, ?_⟩
        rw [hzpow]
        push Not
        exact ⟨h1.2.1, fun he => hyP (he ▸ hzP)⟩
  set F₁ := Finset.univ.filter fun y : G => y ∈ V₀ ∧ y ≠ 1 ∧ y ≠ z with hF₁
  set F₂ := Finset.univ.filter fun y : G => y ∈ (S : Subgroup G) ∧ y ∉ P ∧ y * y = 1 with hF₂
  have hF₂card : F₂.card = 8 := by
    have h8 := hJ.card_invol
    rw [← h8, ← Set.ncard_coe_finset]
    congr 1
    ext y
    simp [hF₂, sq]
  have hF₁card : F₁.card = 2 := by
    have hV₀card : (Finset.univ.filter fun y : G => y ∈ V₀).card = 4 := by
      rw [← h.card_V₀, ← Nat.card_eq_finsetCard]
      exact Nat.card_congr (Equiv.subtypeEquivRight fun y => by simp)
    have hsplit : Finset.univ.filter (fun y : G => y ∈ V₀) = F₁ ∪ {1, z} := by
      ext y
      simp only [hF₁, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union,
        Finset.mem_insert, Finset.mem_singleton]
      constructor
      · intro hy
        by_cases hy1 : y = 1
        · exact Or.inr (Or.inl hy1)
        by_cases hyz : y = z
        · exact Or.inr (Or.inr hyz)
        · exact Or.inl ⟨hy, hy1, hyz⟩
      · rintro (⟨hy, -, -⟩ | rfl | rfl)
        · exact hy
        · exact one_mem _
        · exact hQ.z_mem_V₀
    have hdisj : Disjoint F₁ {1, z} := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      simp only [hF₁, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy'
      rcases hy' with rfl | rfl
      · exact hy.2.1 rfl
      · exact hy.2.2 rfl
    rw [hsplit, Finset.card_union_of_disjoint hdisj,
      Finset.card_pair (Ne.symm hQ.z_ne_one)] at hV₀card
    omega
  have hdisj12 : Disjoint F₁ F₂ := by
    rw [Finset.disjoint_left]
    intro y hy hy'
    simp only [hF₁, hF₂, Finset.mem_filter, Finset.mem_univ, true_and] at hy hy'
    exact hy'.2.1 (hVP (h.V₀_le hy.1))
  have hI : Nat.card {y : Q // (y : G) * y = 1 ∧ (y : G) ∉ zpowers z} = 10 := by
    have h1 : Nat.card {y : Q // (y : G) * y = 1 ∧ (y : G) ∉ zpowers z} = (F₁ ∪ F₂).card := by
      rw [← Nat.card_eq_finsetCard]
      refine Nat.card_congr
        { toFun := fun y => ⟨y.1, ?_⟩
          invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
          left_inv := fun y => rfl
          right_inv := fun y => rfl }
      · have := (hinvQ y.1).mp ⟨y.1.2, y.2⟩
        simpa [hF₁, hF₂] using this
      · have hy : y.1 ∈ F₁ ∪ F₂ := y.2
        simp only [hF₁, hF₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and] at hy
        exact ((hinvQ y.1).mpr hy).1
      · have hy : y.1 ∈ F₁ ∪ F₂ := y.2
        simp only [hF₁, hF₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
          true_and] at hy
        exact ((hinvQ y.1).mpr hy).2
    rw [h1, Finset.card_union_of_disjoint hdisj12, hF₁card, hF₂card]
  have horb : ∀ B : Subgroup G, z ∈ B → B ≤ Q →
      (∀ s ∈ (S : Subgroup G), ∀ b ∈ B, s * b * s⁻¹ ∈ B) → Nat.card B = 8 →
      Nat.card {y : B // (y : G) * y = 1 ∧ (y : G) ∉ zpowers z} ≠ 4 := by
    intro B hzB hBQ hBS hB8 h4
    set FB := Finset.univ.filter fun y : G => y ∈ B ∧ y * y = 1 ∧ y ∉ zpowers z with hFB
    have hFBcard : Nat.card {y : B // (y : G) * y = 1 ∧ (y : G) ∉ zpowers z} = FB.card := by
      rw [← Nat.card_eq_finsetCard]
      refine Nat.card_congr
        { toFun := fun y => ⟨y.1, by simp [hFB, y.2]⟩
          invFun := fun y => ⟨⟨y.1, ?_⟩, ?_⟩
          left_inv := fun y => rfl
          right_inv := fun y => rfl }
      · have hy : y.1 ∈ FB := y.2
        simp only [hFB, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy.1
      · have hy : y.1 ∈ FB := y.2
        simp only [hFB, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        exact hy.2
    rw [hFBcard] at h4
    by_cases hex : ∃ u ∈ FB, u ∉ P
    ·
      obtain ⟨u, hu, huP⟩ := hex
      simp only [hFB, Finset.mem_filter, Finset.mem_univ, true_and] at hu
      have huS : u ∈ (S : Subgroup G) := hQ.le (hBQ hu.1)
      obtain ⟨g₁, hg₁S, hg₁⟩ := hJ.conj_invol u huS huP (by rw [sq]; exact hu.2.1)
      have hsub : F₂ ⊆ FB := by
        intro s hs
        simp only [hF₂, Finset.mem_filter, Finset.mem_univ, true_and] at hs
        obtain ⟨g₂, hg₂S, hg₂⟩ := hJ.conj_invol s hs.1 hs.2.1 (by rw [sq]; exact hs.2.2)
        have hsB : s ∈ B := by
          have := hBS (g₂ * g₁⁻¹) (mul_mem hg₂S (inv_mem hg₁S)) u hu.1
          rwa [← hg₁, show g₂ * g₁⁻¹ * (g₁ * x * g₁⁻¹) * (g₂ * g₁⁻¹)⁻¹ = g₂ * x * g₂⁻¹ by group,
            hg₂] at this
        simp only [hFB, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨hsB, hs.2.2, ?_⟩
        rw [hzpow]
        push Not
        exact ⟨fun he => hs.2.1 (he ▸ one_mem P), fun he => hs.2.1 (he ▸ hzP)⟩
      have := Finset.card_le_card hsub
      omega
    ·
      push Not at hex
      have hsub : FB ⊆ F₁ := by
        intro y hy
        have hyP := hex y hy
        simp only [hFB, Finset.mem_filter, Finset.mem_univ, true_and] at hy
        rcases (hinvQ y).mp ⟨hBQ hy.1, hy.2.1, hy.2.2⟩ with h1 | h1
        · simpa [hF₁] using h1
        · exact absurd hyP h1.2.1
      have := Finset.card_le_card hsub
      omega
  have hSC : (S : Subgroup G) ≤ centralizer ({z} : Set G) := fun y hy =>
    mem_centralizer_singleton_iff.mpr (hQ.z_central y hy).symm
  exact qbarNoComponent_of_card hGold hz2 hQ.z_ne_one (isSylowOf_of_sylow_le S hSC) hQ.le
    hQ.z_mem hQ.comm_mem hQsq hQ.closed hQ.normal
    (h.oddCoreIn_centralizer_eq_bot_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e
      hV'16 hinf hsup hV'inv S hPS hQ.z_mem_V₀ hQ.z_ne_one hQ.z_central) hQ32 hI horb

theorem centralizer_le_normalizer_Q_of_eps_one
    (hGold : Asc76X.GoldschmidtTheoremA) (hGs : IsSimpleGroup G)
    (hP64 : Nat.card P = 64) (hVP : R ⊔ T ≤ P) (hε : EpsOne (R ⊔ T) P)
    {V' : Subgroup G} (hV'P : V' ≤ P) (hV'e : IsElemAbelian 2 V') (hV'16 : Nat.card V' = 16)
    (hinf : (R ⊔ T) ⊓ V' = V₀) (hsup : (R ⊔ T) ⊔ V' = P)
    (hV'inv : ∀ x ∈ P, x * x = 1 → x ∉ R ⊔ T → x ∈ V') (S : Sylow 2 G) (hPS : P ≤ S)
    {z : G} {Q : Subgroup G} (hQ : QFacts (S : Subgroup G) V₀ z Q) :
    centralizer ({z} : Set G) ≤ normalizer (Q : Set G) :=
  h.centralizer_le_normalizer_of_QFacts hP hPC hIIa hGold hGs hP64 hVP hε hV'P hV'e hV'16 hinf
    hsup hV'inv S hPS hQ (h.qbarNoComponent_of_eps_one hP hPC hIIa hGold hGs hP64 hVP hε hV'P
      hV'e hV'16 hinf hsup hV'inv S hPS hQ)

end IIa

end PStructure

end Setting310

end CFSG.ComponentClassification.RankTwoAltFive
