module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltLocal
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltFrattini
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallFamAltPerm
import CFSG.LocalAnalysis.AGLEmbedding.AltBeta
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.SporadicBeta

public section

namespace CFSG.AGLEmbedding.KFactProofs.SmallIdent

open CFSG.Open Equiv CFSG.AGLEmbeddingD2.AltSurvivor

section Perm

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

omit [Fintype Ω] in
theorem exists_cross_of_not_pres {O₁ O₂ : Finset Ω} (hc : O₁.card = O₂.card)
    (hcov : ∀ x, x ∈ O₁ ∨ x ∈ O₂) {y : Perm Ω}
    (h : ¬ ((∀ x, x ∈ O₁ ↔ y x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ y x ∈ O₂))) :
    (∃ w ∈ O₁, y w ∈ O₂) ∧ ∃ u ∈ O₁, y u ∈ O₁ := by
  constructor
  · by_contra hcon
    push Not at hcon
    refine h (iff_of_forall_mem_or hc (Or.inl fun x hx => ?_))
    exact (hcov (y x)).resolve_right (hcon x hx)
  · by_contra hcon
    push Not at hcon
    refine h (iff_of_forall_mem_or hc (Or.inr fun x hx => ?_))
    exact (hcov (y x)).resolve_left (hcon x hx)

theorem conj_mem_sup_altOn {O₁ O₂ : Finset Ω} (hd : Disjoint O₁ O₂)
    (hcov : ∀ x, x ∈ O₁ ∨ x ∈ O₂) {σ : Perm Ω}
    (hσ : (∀ x, x ∈ O₁ ↔ σ x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ σ x ∈ O₂)) {b : Perm Ω}
    (hb : b ∈ altOn O₁ ⊔ altOn O₂) : σ * b * σ⁻¹ ∈ altOn O₁ ⊔ altOn O₂ := by
  have hmem : ∀ {A A' : Finset Ω}, (∀ x, x ∈ A ↔ σ x ∈ A') → altOn A' ≤ altOn O₁ ⊔ altOn O₂ →
      ∀ {g}, g ∈ altOn A → σ * g * σ⁻¹ ∈ altOn O₁ ⊔ altOn O₂ :=
    fun hs hle _ hg => hle (conj_mem_altOn hs hg)
  have hc : ∀ x, x ∈ O₂ ↔ x ∉ O₁ := fun x =>
    ⟨fun h h1 => Finset.disjoint_left.1 hd h1 h, fun h => (hcov x).resolve_left h⟩
  have hc₁ : ∀ x, x ∈ O₁ ↔ x ∉ O₂ := fun x =>
    ⟨fun h h2 => Finset.disjoint_left.1 hd h h2, fun h => (hcov x).resolve_right h⟩
  have hle : altOn O₁ ⊔ altOn O₂ ≤
      (altOn O₁ ⊔ altOn O₂).comap (MulAut.conj σ).toMonoidHom := by
    rcases hσ with h | h
    · have h2 : ∀ x, x ∈ O₂ ↔ σ x ∈ O₂ := fun x =>
        (hc x).trans ((not_congr (h x)).trans (hc (σ x)).symm)
      exact sup_le (fun g hg => hmem h le_sup_left hg) (fun g hg => hmem h2 le_sup_right hg)
    · have h2 : ∀ x, x ∈ O₂ ↔ σ x ∈ O₁ := fun x =>
        (hc x).trans ((not_congr (h x)).trans (hc₁ (σ x)).symm)
      exact sup_le (fun g hg => hmem h le_sup_right hg) (fun g hg => hmem h2 le_sup_left hg)
  exact hle hb

end Perm

section KLevel

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem normalizer_le_glbCore_one (hp : p.Prime) (T : Sylow p K) (hT : (T : Subgroup K) ≠ ⊥) :
    Subgroup.normalizer ((T : Subgroup K) : Set K) ≤ GLBCore p 1 (T : Subgroup K) :=
  CFSG.AGLEmbeddingD2.normalizer_le_glbCore p 1 le_rfl
    (CFSG.AGLEmbedding.one_le_pRank_of_isPGroup_of_ne_bot hp T.isPGroup' hT)

theorem eq_or_eq_top_of_glbCore_le_of_five_le (hp : p.Prime) (hp5 : 5 ≤ p) (hK : IsAltTwoP p K)
    (T : Sylow p K) {Y : Subgroup K} (hY : GLBCore p 1 (T : Subgroup K) ≤ Y) :
    Y = GLBCore p 1 (T : Subgroup K) ∨ Y = ⊤ := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e⟩ := hK
  set ι := altPermEmbed e with hι'
  have hι : Function.Injective ι := altPermEmbed_injective e
  obtain ⟨hEab, hEcard⟩ := isElemAbelian_map_sylow hp hp2 e T
  obtain ⟨a₁, ha₁, a₂, ha₂, O₁, O₂, hO₁, hO₂, hd, hm₁, hm₂⟩ :=
    CFSG.AGLEmbeddingD2.exists_cycles_of_isElemAbelian hp hp2 (by omega) hEab hEcard
  have hcov := mem_or_mem_of_card hO₁ hO₂ hd (Fintype.card_fin _)
  obtain ⟨t₁, ht₁, ht₁ι⟩ := Subgroup.mem_map.1 ha₁
  obtain ⟨t₂, ht₂, ht₂ι⟩ := Subgroup.mem_map.1 ha₂
  set Γ := GLBCore p 1 (T : Subgroup K) with hΓ
  have hT0 : (T : Subgroup K) ≠ ⊥ := by
    intro h
    have : t₁ ∈ (⊥ : Subgroup K) := h ▸ ht₁
    have h1 : t₁ = 1 := this
    obtain ⟨x, hx⟩ : O₁.Nonempty := Finset.card_pos.1 (by rw [hO₁]; exact hp.pos)
    exact (hm₁ x).2 hx (by rw [← ht₁ι, h1, map_one]; rfl)
  have hord : ∀ {t : K} {a : Perm (Fin (2 * p))} {O : Finset (Fin (2 * p))}, t ∈ (T : Subgroup K) →
      ι t = a → (∀ x, a x ≠ x ↔ x ∈ O) → O.card = p → orderOf t = p := by
    intro t a O ht hta hm hO
    have hne : t ≠ 1 := by
      intro h1
      obtain ⟨x, hx⟩ : O.Nonempty := Finset.card_pos.1 (by rw [hO]; exact hp.pos)
      exact (hm x).2 hx (by rw [← hta, h1, map_one]; rfl)
    exact orderOf_eq_prime (pow_eq_one_of_mem_isAltTwoP hp hp2 ⟨e⟩ T ht) hne
  have ho₁ := hord ht₁ ht₁ι hm₁ hO₁
  have ho₂ := hord ht₂ ht₂ι hm₂ hO₂
  have hAlt : ∀ {t : K} {a : Perm (Fin (2 * p))} {O O' : Finset (Fin (2 * p))},
      t ∈ (T : Subgroup K) → ι t = a → orderOf t = p → (∀ x, a x ≠ x ↔ x ∈ O) →
      Disjoint O O' → altOn O' ≤ Γ.map ι := by
    intro t a O O' ht hta hot hm hOO' g hg
    have hgA : g ∈ alternatingGroup (Fin (2 * p)) := Perm.mem_alternatingGroup.2 (mem_altOn.1 hg).1
    set k : K := e.symm ⟨g, hgA⟩ with hk
    have hιk : ι k = g := by simp [hk, hι', altPermEmbed]
    have hdis : Perm.Disjoint g a := by
      intro x
      by_cases hx : x ∈ O
      · left
        exact (mem_altOn.1 hg).2 x (fun h => Finset.disjoint_left.1 hOO' hx h)
      · right
        by_contra h
        exact hx ((hm x).1 h)
    have hcomm : k * t = t * k := by
      apply hι
      rw [map_mul, map_mul, hιk, hta]
      exact hdis.commute.eq
    have hkΓ : k ∈ Γ := by
      refine CFSG.AGLEmbedding.normalizer_zpowers_le_glbCore hp ht hot ?_
      apply Subgroup.centralizer_le_normalizer
      exact CFSG.AGLEmbedding.mem_centralizer_zpowers hcomm
    exact ⟨k, hkΓ, hιk⟩
  have hAlt₁ : altOn O₁ ≤ Γ.map ι := hAlt ht₂ ht₂ι ho₂ hm₂ hd.symm
  have hAlt₂ : altOn O₂ ≤ Γ.map ι := hAlt ht₁ ht₁ι ho₁ hm₁ hd
  have hΓY : Γ.map ι ≤ Y.map ι := Subgroup.map_mono hY
  by_cases hall : ∀ y ∈ Y, (∀ x, x ∈ O₁ ↔ ι y x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ ι y x ∈ O₂)
  · left
    refine le_antisymm (fun y hy => ?_) hY
    set B : Subgroup (Perm (Fin (2 * p))) := altOn O₁ ⊔ altOn O₂ with hB
    have hsign : ∀ {a : Perm (Fin (2 * p))} {O : Finset (Fin (2 * p))} {t : K}, ι t = a →
        (∀ x, a x ≠ x ↔ x ∈ O) → a ∈ altOn O := by
      intro a O t hta hm
      refine mem_altOn.2 ⟨?_, fun x hx => ?_⟩
      · rw [← hta]
        exact sign_altPermEmbed e t
      · by_contra h
        exact hx ((hm x).1 h)
    have ha₁B : a₁ ∈ altOn O₁ := hsign ht₁ι hm₁
    have ha₂B : a₂ ∈ altOn O₂ := hsign ht₂ι hm₂
    have hTB : (T : Subgroup K) ≤ B.comap ι := by
      intro t ht
      have hcomm : ∀ a ∈ (T : Subgroup K).map ι, ι t * a = a * ι t := by
        intro a ha
        exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨ι t, t, ht, rfl⟩ ⟨a, ha⟩)
      obtain ⟨i, j, hij⟩ := exists_zpow_mul_zpow_eq
        (isCycle_of_moves hp (hEab.2 a₁ ha₁) hO₁ hm₁) (isCycle_of_moves hp (hEab.2 a₂ ha₂) hO₂ hm₂)
        hm₁ hm₂ hd hcov (hcomm a₁ ha₁) (hcomm a₂ ha₂)
      show ι t ∈ B
      rw [hij]
      exact mul_mem (Subgroup.mem_sup_left (zpow_mem ha₁B i))
        (Subgroup.mem_sup_right (zpow_mem ha₂B j))
    have hyB : ∀ b ∈ B.comap ι, y * b * y⁻¹ ∈ B.comap ι := by
      intro b hb
      show ι (y * b * y⁻¹) ∈ B
      rw [map_mul, map_mul, map_inv]
      exact conj_mem_sup_altOn hd hcov (hall y hy) hb
    obtain ⟨b, hb, hbn⟩ := exists_mem_of_conj_sylow_le T hTB hyB
    have hbΓ : b ∈ Γ := by
      have : ι b ∈ Γ.map ι := (sup_le hAlt₁ hAlt₂ : B ≤ Γ.map ι) hb
      obtain ⟨γ, hγ, hγb⟩ := this
      exact hι hγb ▸ hγ
    have hnΓ := normalizer_le_glbCore_one hp T hT0 hbn
    have := Γ.mul_mem hbΓ hnΓ
    simpa using this
  · right
    have hex : ∃ y ∈ Y, ¬ ((∀ x, x ∈ O₁ ↔ ι y x ∈ O₁) ∨ (∀ x, x ∈ O₁ ↔ ι y x ∈ O₂)) := by
      by_contra hcon
      exact hall fun y hy => by_contra fun h => hcon ⟨y, hy, h⟩
    obtain ⟨y, hyY, hy⟩ := hex
    obtain ⟨⟨w, hw, hyw⟩, u, hu, hyu⟩ :=
      exists_cross_of_not_pres (by rw [hO₁, hO₂]) hcov hy
    have hA : alternatingGroup (Fin (2 * p)) ≤ Y.map ι :=
      alternatingGroup_le_of_cross hd hcov (by omega) (by omega) (hAlt₁.trans hΓY)
        (hAlt₂.trans hΓY) (Subgroup.mem_map_of_mem ι hyY) hw hyw hu hyu
    rw [eq_top_iff]
    intro k _
    obtain ⟨y', hy', hιy⟩ := hA (Perm.mem_alternatingGroup.2 (sign_altPermEmbed e k))
    exact (hι hιy) ▸ hy'

end KLevel

end CFSG.AGLEmbedding.KFactProofs.SmallIdent
