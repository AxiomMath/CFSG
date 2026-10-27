module

public import CFSG.LocalAnalysis.RankThreeTheoremC.NGK3LayerComp
import CFSG.LocalAnalysis.RankThreeTheoremC.ZLayer3Comp
import CFSG.LocalAnalysis.RankThreeTheoremC.ReducedLayer

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup

variable {X : Type} [Group X] [Finite X] {P : Sylow 3 X} {z : X} {D : Subgroup X}

omit [Finite X] in
private lemma ngk3_isElemAbelian_zpowers {x : X} (hx : orderOf x = 3) :
    IsElemAbelian 3 (zpowers x) ∧ Nat.card (zpowers x) = 3 ^ 1 := by
  refine ⟨(CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1 ?_, ?_⟩
  · exact CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one (hx ▸ pow_orderOf_eq_one x)
  · rw [Nat.card_zpowers, hx, pow_one]

private lemma ngk3_isElemAbelian_sup_zpowers {E : Subgroup X} {f : X} {k : ℕ}
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ k) (hf : f ^ 3 = 1)
    (hfE : f ∉ E) (hcomm : ∀ e ∈ E, e * f = f * e) :
    IsElemAbelian 3 (E ⊔ zpowers f) ∧
      Nat.card (E ⊔ zpowers f : Subgroup X) = 3 ^ (k + 1) := by
  refine ⟨?_, ?_⟩
  · have : CFSG.IsElementaryAbelian 3 E :=
      (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 E).2 hE
    have : CFSG.IsElementaryAbelian 3 (zpowers f) :=
      CFSG.IsElementaryAbelian.zpowers_of_pow_eq_one hf
    refine (CFSG.SectionRank.isElementaryAbelian_iff_isElemAbelian 3 _).1
      (CFSG.IsElementaryAbelian.sup_of_le_centralizer ?_)
    rw [zpowers_le, mem_centralizer_iff]
    exact hcomm
  · rw [CFSG.RankThree.PartOne.Planes.card_sup_zpowers Nat.prime_three E hf hfE hcomm, hcard,
      pow_succ]

private lemma ngk3_mem_zpowers_of_central (h : NGKData X P z D)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥) {d : X} (hdK : d ∈ K) (hd3 : d ^ 3 = 1)
    (hdc : ∀ k ∈ K, d * k = k * d) : d ∈ zpowers z :=
  hB d ((h.component_data hB hK hZ).2.2.1 ⟨d, hdK⟩
    (mem_center_iff.2 fun k => Subtype.ext (hdc k k.2).symm)) hd3

private lemma ngk3_zpowers_le_centralizer_z (h : NGKData X P z D) (K : Subgroup X) :
    zpowers z ≤ centralizer (K : Set X) :=
  zpowers_le.2 (mem_centralizer_iff.2 fun k _ => (h.zc' k).symm)

private lemma ngk3_zpowers_le_centralizer {K K' : Subgroup X} (hK : IsComponentOf K ⊤)
    (hK' : IsComponentOf K' ⊤) (hne : K ≠ K') {d : X} (hd : d ∈ K) :
    zpowers d ≤ centralizer (K' : Set X) :=
  zpowers_le.2 (mem_centralizer_iff.2 fun k hk =>
    (commute_of_isComponentOf_ne hK hK' hne d hd k hk).symm)

private lemma ngk3_extend (h : NGKData X P z D)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥) {d : X} (hdK : d ∈ K) (hd3 : orderOf d = 3)
    (hdz : d ∉ zpowers z) {E : Subgroup X} {k : ℕ} (hE : IsElemAbelian 3 E)
    (hcard : Nat.card E = 3 ^ k) (hEK : E ≤ centralizer (K : Set X)) :
    IsElemAbelian 3 (E ⊔ zpowers d) ∧ Nat.card (E ⊔ zpowers d : Subgroup X) = 3 ^ (k + 1) := by
  have hd1 : d ^ 3 = 1 := hd3 ▸ pow_orderOf_eq_one d
  refine ngk3_isElemAbelian_sup_zpowers hE hcard hd1 (fun hdE => hdz ?_) fun e he => ?_
  · exact ngk3_mem_zpowers_of_central h hB hK hZ hdK hd1 fun k hk =>
      (mem_centralizer_iff.1 (hEK hdE) k hk).symm
  · exact (mem_centralizer_iff.1 (hEK he) d hdK).symm

theorem NGKData.three_components_false (h : NGKData X P z D)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z)
    (hnc : ∀ K : Subgroup X, IsComponentOf K ⊤ → center K ≠ ⊥)
    {K₁ K₂ K₃ : Subgroup X} (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤)
    (h₃ : IsComponentOf K₃ ⊤) (h₁₂ : K₁ ≠ K₂) (h₁₃ : K₁ ≠ K₃) (h₂₃ : K₂ ≠ K₃) : False := by
  obtain ⟨d₁, hd₁, hd₁3, hd₁z⟩ := h.exists_inf_order_three hB h₁ (hnc K₁ h₁)
  obtain ⟨d₂, hd₂, hd₂3, hd₂z⟩ := h.exists_inf_order_three hB h₂ (hnc K₂ h₂)
  obtain ⟨d₃, hd₃, hd₃3, hd₃z⟩ := h.exists_inf_order_three hB h₃ (hnc K₃ h₃)
  have hzP : z ∈ (P : Subgroup X) := h.plane.1 h.zD
  obtain ⟨hE₁, hc₁⟩ := ngk3_isElemAbelian_zpowers h.ord
  obtain ⟨hE₂, hc₂⟩ := ngk3_extend h hB h₁ (hnc K₁ h₁) hd₁.2 hd₁3 hd₁z hE₁ hc₁
    (ngk3_zpowers_le_centralizer_z h K₁)
  obtain ⟨hE₃, hc₃⟩ := ngk3_extend h hB h₂ (hnc K₂ h₂) hd₂.2 hd₂3 hd₂z hE₂ hc₂
    (sup_le (ngk3_zpowers_le_centralizer_z h K₂) (ngk3_zpowers_le_centralizer h₁ h₂ h₁₂ hd₁.2))
  obtain ⟨hE₄, hc₄⟩ := ngk3_extend h hB h₃ (hnc K₃ h₃) hd₃.2 hd₃3 hd₃z hE₃ hc₃
    (sup_le (sup_le (ngk3_zpowers_le_centralizer_z h K₃)
      (ngk3_zpowers_le_centralizer h₁ h₃ h₁₃ hd₁.2))
      (ngk3_zpowers_le_centralizer h₂ h₃ h₂₃ hd₂.2))
  have hle : zpowers z ⊔ zpowers d₁ ⊔ zpowers d₂ ⊔ zpowers d₃ ≤ (P : Subgroup X) :=
    sup_le (sup_le (sup_le (zpowers_le.2 hzP) (zpowers_le.2 hd₁.1)) (zpowers_le.2 hd₂.1))
      (zpowers_le.2 hd₃.1)
  have h4 := CFSG.SectionRank.le_pRank (by norm_num) hle hE₄ hc₄
  rw [h.prank] at h4
  omega

omit [Finite X] in
private lemma ngk3_mem_normalizer_of_sq {Q : Subgroup X} (hQ : IsPGroup 3 Q) {g : X} (hg : g ∈ Q)
    {K : Subgroup X} (hsq : g * g ∈ normalizer (K : Set X)) : g ∈ normalizer (K : Set X) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hQ ⟨g, hg⟩
  rw [Subgroup.orderOf_mk] at hk
  have hcop : Nat.Coprime 2 (orderOf g) := by
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact Subgroup.pow_mem _ (by rwa [sq]) m

private lemma ngk3_mem_normalizer_of_two {Q : Subgroup X} (hQ : IsPGroup 3 Q)
    {K₁ K₂ : Subgroup X} (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) (h₁₂ : K₁ ≠ K₂)
    (hall : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = K₁ ∨ K = K₂) {g : X} (hg : g ∈ Q) :
    g ∈ normalizer (K₁ : Set X) := by
  rcases hall _ (isComponentOf_map_conj h₁ g) with hK | hK
  · exact mem_normalizer_iff_map_conj_eq.2 hK
  · exfalso
    have h2 : K₂.map (MulAut.conj g).toMonoidHom = K₁ := by
      rcases hall _ (isComponentOf_map_conj h₂ g) with h' | h'
      · exact h'
      · exact absurd (Subgroup.map_injective (MulAut.conj g).injective (h'.trans hK.symm))
          h₁₂.symm
    have hcomp : (MulAut.conj (g * g)).toMonoidHom =
        (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    have hsq : g * g ∈ normalizer (K₁ : Set X) := by
      rw [mem_normalizer_iff_map_conj_eq]
      change K₁.map (MulAut.conj (g * g)).toMonoidHom = K₁
      rw [hcomp, ← Subgroup.map_map, hK, h2]
    have hg' := ngk3_mem_normalizer_of_sq hQ hg hsq
    rw [mem_normalizer_iff_map_conj_eq] at hg'
    exact h₁₂ (hg'.symm.trans hK)

private lemma ngk3_plane_le (h : NGKData X P z D) (hF : PlaneFacts (P : Subgroup X) D z)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z) {K : Subgroup X}
    (hK : IsComponentOf K ⊤) (hZ : center K ≠ ⊥)
    (hPK : (P : Subgroup X) ≤ normalizer (K : Set X)) :
    ∃ B : Subgroup X, B ≤ K ∧ B ≤ D ∧ Nat.card B = 9 ∧ IsElemAbelian 3 B := by
  have hN : (P : Subgroup X) ≤ normalizer (((P : Subgroup X) ⊓ K : Subgroup X) : Set X) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    simp only [mem_inf]
    rw [mem_normalizer_iff.1 (le_normalizer hg) x, mem_normalizer_iff.1 (hPK hg) x]
  obtain ⟨B, hBR, hBD, hB9, hBe, -, -⟩ := hF.inf_plane _ inf_le_left hN
    (h.not_isMulCommutative_inf hB hK hZ)
  exact ⟨B, hBR.trans inf_le_right, hBD, hB9, hBe⟩

theorem NGKData.two_components_false (h : NGKData X P z D) (hF : PlaneFacts (P : Subgroup X) D z)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z)
    {K₁ K₂ : Subgroup X} (h₁ : IsComponentOf K₁ ⊤) (h₂ : IsComponentOf K₂ ⊤) (h₁₂ : K₁ ≠ K₂) :
    False := by
  have hnc := h.no_centerless hF
  have hall : ∀ K : Subgroup X, IsComponentOf K ⊤ → K = K₁ ∨ K = K₂ := by
    intro K hK
    by_contra hne
    rw [not_or] at hne
    exact h.three_components_false hB hnc h₁ h₂ hK h₁₂ (Ne.symm hne.1) (Ne.symm hne.2)
  obtain ⟨B₁, hB₁K, hB₁D, hB₁9, hB₁e⟩ := ngk3_plane_le h hF hB h₁ (hnc K₁ h₁)
    fun g hg => ngk3_mem_normalizer_of_two P.isPGroup' h₁ h₂ h₁₂ hall hg
  obtain ⟨B₂, hB₂K, hB₂D, hB₂9, hB₂e⟩ := ngk3_plane_le h hF hB h₂ (hnc K₂ h₂)
    fun g hg => ngk3_mem_normalizer_of_two P.isPGroup' h₂ h₁ h₁₂.symm
      (fun K hK => (hall K hK).symm) hg
  have hEq : B₁ = B₂ := hF.eq_of_comm B₁ B₂ hB₁D hB₂D hB₁9 hB₂9 fun b hb b' hb' =>
    commute_of_isComponentOf_ne h₁ h₂ h₁₂ b (hB₁K hb) b' (hB₂K hb')
  have hle : B₁ ≤ zpowers z := fun b hb =>
    ngk3_mem_zpowers_of_central h hB h₁ (hnc K₁ h₁) (hB₁K hb) (hB₁e.2 b hb) fun k hk =>
      commute_of_isComponentOf_ne h₂ h₁ h₁₂.symm b (hB₂K (hEq ▸ hb)) k hk
  have hcard := Subgroup.card_le_of_le hle
  rw [hB₁9, Nat.card_zpowers, h.ord] at hcard
  omega

theorem NGKData.exists_unique_component (h : NGKData X P z D)
    (hF : PlaneFacts (P : Subgroup X) D z)
    (hB : ∀ w ∈ layerCenter X, w ^ 3 = 1 → w ∈ zpowers z) :
    ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ ∀ K : Subgroup X, IsComponentOf K ⊤ → K = L := by
  have hz1 : z ≠ 1 := fun h1 => by
    have := h.ord
    rw [h1, orderOf_one] at this
    omega
  obtain ⟨L, hL, -⟩ := exists_component_center_ne_bot_of_mem_layer h.layer hz1 fun e _ => h.zc' e
  refine ⟨L, hL, fun K hK => ?_⟩
  by_contra hne
  exact h.two_components_false hF hB hK hL hne

end CFSG.LocalAnalysis.RankThreeTheoremC
