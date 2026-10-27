module

public import CFSG.LocalAnalysis.ComponentClassification.WittDesignPlaneCollineation
public import CFSG.Monster.B.Classical.HyperovalOrbits
import all CFSG.Fischer.F4

public section

namespace CFSG.EvenSmallLie.UnitarySix.MathieuExt

open CFSG.ComponentClassification.WittDesign CFSG.Monster.B.Classical.Plane CFSG.Fischer
open scoped MatrixGroups Matrix

section Parity

variable {P : Type*} [Fintype P] [DecidableEq P]

omit [Fintype P] in
theorem card_filter_fixed_mod_two {σ : Equiv.Perm P} (hσ : σ * σ = 1) {X : Finset P}
    (hX : ∀ x ∈ X, σ x ∈ X) : (X.filter fun x => σ x = x).card % 2 = X.card % 2 := by
  have hX' : ∀ x, σ x ∈ X ↔ x ∈ X := fun x => ⟨fun h => by
    have := hX _ h
    rwa [← Equiv.Perm.mul_apply, hσ, Equiv.Perm.one_apply] at this, hX x⟩
  have hτ : (σ.subtypePerm hX') ^ 2 = 1 := by
    rw [sq, Equiv.Perm.subtypePerm_mul]
    ext x
    simp [hσ]
  have h2 := Equiv.Perm.two_dvd_card_support hτ
  rw [Equiv.Perm.support_subtypePerm] at h2
  have hcard : (Finset.univ.filter fun x : {x // x ∈ X} => σ x ≠ x).card =
      (X.filter fun x => ¬σ x = x).card := by
    rw [← Finset.card_map (Function.Embedding.subtype _)]
    congr 1
    ext x
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
      Function.Embedding.coe_subtype]
    exact ⟨fun ⟨y, hy, e⟩ => e ▸ ⟨y.2, hy⟩, fun ⟨hx, h⟩ => ⟨⟨x, hx⟩, h, rfl⟩⟩
  rw [hcard] at h2
  have := Finset.card_filter_add_card_filter_not (s := X) (p := fun x => σ x = x)
  omega

end Parity

section Steiner

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)}

theorem mapsTo_line_of_fix (h : IsSteinerPlane 𝓛) {σ : Equiv.Perm P}
    (hσ : σ ∈ blockAut 𝓛) {M : Finset P} (hM : M ∈ 𝓛) {x y : P} (hxy : x ≠ y) (hx : x ∈ M)
    (hy : y ∈ M) (hσx : σ x = x) (hσy : σ y = y) : ∀ p ∈ M, σ p ∈ M := by
  have hM' : M.map σ.toEmbedding ∈ 𝓛 := (hσ M).2 hM
  have hxM' : x ∈ M.map σ.toEmbedding := hσx ▸ Finset.mem_map_of_mem _ hx
  have hyM' : y ∈ M.map σ.toEmbedding := hσy ▸ Finset.mem_map_of_mem _ hy
  have e := h.eq_of_mem_of_mem hM' hM hxy hxM' hyM' hx hy
  intro p hp
  rw [← e]
  exact Finset.mem_map_of_mem _ hp

theorem fixes_line_of_involution (h : IsSteinerPlane 𝓛) {σ : Equiv.Perm P}
    (hσ : σ ∈ blockAut 𝓛) (hσ2 : σ * σ = 1)
    (h5 : (Finset.univ.filter fun p => σ p = p).card = 5) {L : Finset P} (hL : L ∈ 𝓛)
    {α β : P} (hαβ : α ≠ β) (hα : α ∈ L) (hβ : β ∈ L) (hσα : σ α = α) (hσβ : σ β = β) :
    ∀ p ∈ L, σ p = p := by
  set F := Finset.univ.filter fun p => σ p = p with hF
  have memF : ∀ {p}, p ∈ F ↔ σ p = p := by simp [hF]
  have odd : ∀ {M : Finset P}, M ∈ 𝓛 → (∀ p ∈ M, σ p ∈ M) →
      (M.filter fun p => σ p = p).card % 2 = 1 := by
    intro M hM hinv
    rw [card_filter_fixed_mod_two hσ2 hinv, h.card_line hM]
  by_contra hne
  push Not at hne
  obtain ⟨p₀, hp₀L, hp₀⟩ := hne
  have hLinv := mapsTo_line_of_fix h hσ hL hαβ hα hβ hσα hσβ
  have hL3 : (L.filter fun p => σ p = p).card = 3 := by
    have hodd := odd hL hLinv
    have hle : (L.filter fun p => σ p = p).card < 5 := by
      rw [← h.card_line hL]
      refine Finset.card_lt_card (Finset.filter_ssubset.2 ⟨p₀, hp₀L, hp₀⟩)
    have hge : 2 ≤ (L.filter fun p => σ p = p).card := by
      rw [← Finset.card_pair hαβ]
      refine Finset.card_le_card fun q hq => ?_
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hα, hσα⟩
      · exact Finset.mem_filter.2 ⟨hβ, hσβ⟩
    omega
  have hR : (F.filter fun p => p ∉ L).card = 2 := by
    have hsplit := Finset.card_filter_add_card_filter_not (s := F) (p := fun p => p ∈ L)
    have hFL : F.filter (fun p => p ∈ L) = L.filter fun p => σ p = p := by
      ext q
      simp only [Finset.mem_filter, memF]
      tauto
    rw [hFL, hL3, h5] at hsplit
    omega
  obtain ⟨r, s, hrs, hRe⟩ := Finset.card_eq_two.1 hR
  have hrR : r ∈ F.filter fun p => p ∉ L := hRe ▸ Finset.mem_insert_self _ _
  have hsR : s ∈ F.filter fun p => p ∉ L := hRe ▸ by simp
  obtain ⟨hrF, hrL⟩ := Finset.mem_filter.1 hrR
  obtain ⟨hsF, hsL⟩ := Finset.mem_filter.1 hsR
  have hσr : σ r = r := memF.1 hrF
  have key : ∀ x ∈ L, σ x = x → ∃ M ∈ 𝓛, r ∈ M ∧ x ∈ M ∧ s ∈ M := by
    intro x hxL hσx
    have hrx : r ≠ x := fun e => hrL (e ▸ hxL)
    obtain ⟨M, ⟨hM, hrM, hxM⟩, -⟩ := h.existsUnique_line hrx
    have hMinv := mapsTo_line_of_fix h hσ hM hrx hrM hxM hσr hσx
    have hodd := odd hM hMinv
    have hsub : ({r, x} : Finset P) ⊆ M.filter fun p => σ p = p := by
      intro q hq
      simp only [Finset.mem_insert, Finset.mem_singleton] at hq
      rcases hq with rfl | rfl
      · exact Finset.mem_filter.2 ⟨hrM, hσr⟩
      · exact Finset.mem_filter.2 ⟨hxM, hσx⟩
    have h3 : 3 ≤ (M.filter fun p => σ p = p).card := by
      have := Finset.card_le_card hsub
      rw [Finset.card_pair hrx] at this
      omega
    obtain ⟨y, hy'⟩ : ((M.filter fun p => σ p = p) \ {r, x}).Nonempty := by
      rw [← Finset.card_pos, Finset.card_sdiff_of_subset hsub, Finset.card_pair hrx]
      omega
    obtain ⟨hy, hyrx⟩ := Finset.mem_sdiff.1 hy'
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hyrx
    obtain ⟨hyM, hσy⟩ := Finset.mem_filter.1 hy
    have hyL : y ∉ L := fun hyL => hrL ((h.eq_of_mem_of_mem hM hL (Ne.symm hyrx.2) hxM hyM
      hxL hyL) ▸ hrM)
    have hyR : y ∈ F.filter fun p => p ∉ L := Finset.mem_filter.2 ⟨memF.2 hσy, hyL⟩
    rw [hRe, Finset.mem_insert, Finset.mem_singleton] at hyR
    rcases hyR with e | e
    · exact absurd e hyrx.1
    · exact ⟨M, hM, hrM, hxM, e ▸ hyM⟩
  obtain ⟨Mα, hMα, hrα, hαα, hsα⟩ := key α hα hσα
  obtain ⟨Mβ, hMβ, hrβ, hββ, hsβ⟩ := key β hβ hσβ
  have e₁ := h.eq_of_mem_of_mem hMα hMβ hrs hrα hsα hrβ hsβ
  have e₂ := h.eq_of_mem_of_mem hMα hL hαβ hαα (e₁ ▸ hββ) hα hβ
  exact hrL (e₂ ▸ hrα)

end Steiner

@[expose] def elPt (a : Fin 21) : Fin 21 := meet a (if a = 0 then 1 else 0)

@[expose] def elMat (a : Fin 21) : Matrix (Fin 3) (Fin 3) F4 :=
  1 + Matrix.vecMulVec (Ω (elPt a)) (Ω a)

theorem elMat_det : ∀ a : Fin 21, (elMat a).det = 1 := by
  intro a
  rw [Matrix.det_fin_three]
  revert a
  decide +kernel

theorem elMat_facts : ∀ a i : Fin 21,
    normIdx (elMat a *ᵥ Ω (normIdx (elMat a *ᵥ Ω i))) = i ∧
      (normIdx (elMat a *ᵥ Ω i) = i ↔ i ∈ projLine a) := by
  decide +kernel

@[expose] def elSL (a : Fin 21) : Matrix.SpecialLinearGroup (Fin 3) F4 := ⟨elMat a, elMat_det a⟩

theorem exists_elation_projLine (a : Fin 21) :
    ∃ g : PSL(3, F4), pslPerm g * pslPerm g = 1 ∧ ∀ i, pslPerm g i = i ↔ i ∈ projLine a := by
  refine ⟨(elSL a : PSL(3, F4)), Equiv.ext fun i => ?_, fun i => ?_⟩
  · rw [Equiv.Perm.mul_apply, pslPerm_mk_apply, pslPerm_mk_apply]
    exact (elMat_facts a i).1
  · rw [pslPerm_mk_apply]
    exact (elMat_facts a i).2

theorem mulVec_ne_zero_SL (M : Matrix.SpecialLinearGroup (Fin 3) F4) {v : Fin 3 → F4}
    (hv : v ≠ 0) : (M : Matrix (Fin 3) (Fin 3) F4) *ᵥ v ≠ 0 := by
  intro h0
  apply hv
  have h1 : ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F4) : Matrix (Fin 3) (Fin 3) F4) *
      (M : Matrix (Fin 3) (Fin 3) F4) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one]
  have := congrArg (fun w => ((M⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F4) :
    Matrix (Fin 3) (Fin 3) F4) *ᵥ w) h0
  simpa only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.mulVec_zero] using this

theorem rhoGL_slHom_ptEquiv (M : Matrix.SpecialLinearGroup (Fin 3) F4) (i : Fin 21) :
    rhoGL (slHom M) (ptEquiv i) = ptEquiv (normIdx ((M : Matrix (Fin 3) (Fin 3) F4) *ᵥ Ω i)) := by
  refine Subtype.ext ?_
  rw [coe_rhoGL_apply, coe_ptEquiv, coe_ptEquiv]
  have himg : imgSub (slHom M) (Submodule.span F4 {Ω i}) =
      (Submodule.span F4 {Ω i}).map (Matrix.mulVecLin (M : Matrix (Fin 3) (Fin 3) F4)) := by
    ext v
    rw [mem_imgSub, Submodule.mem_map]
    rfl
  rw [himg, Submodule.map_span, Set.image_singleton]
  obtain ⟨c, hc, hv⟩ := exists_smul_Ω_normIdx _ (mulVec_ne_zero_SL M (Ω_ne_zero i))
  change Submodule.span F4 {(M : Matrix (Fin 3) (Fin 3) F4) *ᵥ Ω i} = _
  conv_lhs => rw [hv]
  exact Submodule.span_singleton_smul_eq (IsUnit.mk0 c hc) _

theorem pslPerm_mk_eq (M : Matrix.SpecialLinearGroup (Fin 3) F4) :
    pslPerm (M : PSL(3, F4)) = ptEquiv.symm.permCongr (rhoGL (slHom M)) := by
  ext i
  rw [pslPerm_mk_apply, Equiv.permCongr_apply, Equiv.symm_symm, rhoGL_slHom_ptEquiv,
    Equiv.symm_apply_apply]

theorem card_range_pslPerm : Nat.card pslPerm.range = 20160 := by
  have hrange : pslPerm.range =
      ((rhoGL.comp slHom).range).map (Equiv.permCongrHom ptEquiv.symm).toMonoidHom := by
    ext τ
    constructor
    · rintro ⟨g, rfl⟩
      obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective g
      exact ⟨rhoGL (slHom M), ⟨M, rfl⟩, (pslPerm_mk_eq M).symm⟩
    · rintro ⟨_, ⟨M, rfl⟩, rfl⟩
      exact ⟨(M : PSL(3, F4)), pslPerm_mk_eq M⟩
  rw [hrange, Subgroup.card_map_of_injective (Equiv.permCongrHom ptEquiv.symm).injective,
    card_range_rhoGL_comp_slHom]

theorem mem_blockAut_of_mem_lineAut {σ : Equiv.Perm (Fin 21)} (hσ : σ ∈ lineAut) :
    σ ∈ blockAut (Finset.univ.image projLine) := by
  intro B
  simp only [Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨b, hb⟩
    obtain ⟨c, hc⟩ := (inv_mem hσ) b
    refine ⟨c, ?_⟩
    rw [← hc, hb, ← map_perm_mul', inv_mul_cancel]
    exact Finset.map_refl
  · rintro ⟨a, rfl⟩
    obtain ⟨b, hb⟩ := hσ a
    exact ⟨b, hb.symm⟩

theorem pslPerm_mem_lineAut (g : PSL(3, F4)) : pslPerm g ∈ lineAut := by
  obtain ⟨M, rfl⟩ := QuotientGroup.mk_surjective g
  have h := conj_mem_lineAut (rhoGL_mem_blockAut (slHom M))
  have e : ptEquiv.trans ((rhoGL (slHom M)).trans ptEquiv.symm) = pslPerm (M : PSL(3, F4)) := by
    refine Equiv.ext fun i => ?_
    rw [pslPerm_mk_eq, Equiv.permCongr_apply, Equiv.symm_symm]
    rfl
  rw [e] at h
  exact h

theorem card_PSL : Nat.card PSL(3, F4) = 20160 := by
  have := Nat.card_congr rangeSLEquivPSL.toEquiv
  rw [card_range_rhoGL_comp_slHom] at this
  exact this.symm

theorem pslPerm_injective : Function.Injective pslPerm := by
  have hfin : Finite PSL(3, F4) := Nat.finite_of_card_ne_zero (by rw [card_PSL]; norm_num)
  rw [← MonoidHom.ker_eq_bot_iff, ← Subgroup.card_eq_one]
  have h := Subgroup.card_mul_index pslPerm.ker
  rw [Subgroup.index_ker, card_range_pslPerm, card_PSL] at h
  have h' : Nat.card pslPerm.ker * 20160 = 1 * 20160 := by rw [h, one_mul]
  exact Nat.eq_of_mul_eq_mul_right (by norm_num) h'

section Normalizer

variable {P : Type*} [Fintype P] [DecidableEq P] {𝓛 : Finset (Finset P)}

omit [Fintype P] in
theorem mem_blockAut_of_forall {σ : Equiv.Perm P} (h : ∀ B ∈ 𝓛, B.map σ.toEmbedding ∈ 𝓛) :
    σ ∈ blockAut 𝓛 := by
  intro B
  refine ⟨fun hB => ?_, h B⟩
  have himg : 𝓛.image (fun B => B.map σ.toEmbedding) = 𝓛 := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro C hC
      obtain ⟨B, hB, rfl⟩ := Finset.mem_image.1 hC
      exact h B hB
    · rw [Finset.card_image_of_injective _ (Finset.map_injective _)]
  rw [← himg] at hB
  obtain ⟨B', hB', e⟩ := Finset.mem_image.1 hB
  rwa [← Finset.map_injective _ e]

theorem mem_blockAut_of_normalizes (h : IsSteinerPlane 𝓛) {G : Subgroup (Equiv.Perm P)}
    (hG : G ≤ blockAut 𝓛) (hel : ∀ L ∈ 𝓛, ∃ τ ∈ G, τ * τ = 1 ∧ ∀ p, τ p = p ↔ p ∈ L)
    {σ : Equiv.Perm P} (hσ : ∀ τ ∈ G, σ * τ * σ⁻¹ ∈ G) : σ ∈ blockAut 𝓛 := by
  refine mem_blockAut_of_forall fun L hL => ?_
  obtain ⟨τ, hτG, hτ2, hτL⟩ := hel L hL
  set τ' := σ * τ * σ⁻¹ with hτ'
  have hτ'G : τ' ∈ G := hσ τ hτG
  have hτ'2 : τ' * τ' = 1 := by
    rw [hτ', show σ * τ * σ⁻¹ * (σ * τ * σ⁻¹) = σ * (τ * τ) * σ⁻¹ by group, hτ2, mul_one,
      mul_inv_cancel]
  have hfix : ∀ p, τ' p = p ↔ p ∈ L.map σ.toEmbedding := by
    intro p
    rw [Finset.mem_map_equiv, ← hτL, hτ']
    simp only [Equiv.Perm.mul_apply, Equiv.Perm.inv_def]
    exact ⟨fun e => by simpa using congrArg σ.symm e,
      fun e => by rw [e, Equiv.apply_symm_apply]⟩
  have hF : (Finset.univ.filter fun p => τ' p = p) = L.map σ.toEmbedding := by
    ext p
    simp [hfix]
  have h5 : (Finset.univ.filter fun p => τ' p = p).card = 5 := by
    rw [hF, Finset.card_map, h.card_line hL]
  obtain ⟨α, hα, β, hβ, hαβ⟩ := Finset.one_lt_card.1 (show 1 < (L.map σ.toEmbedding).card by
    rw [Finset.card_map, h.card_line hL]; norm_num)
  obtain ⟨M, ⟨hM, hαM, hβM⟩, -⟩ := h.existsUnique_line hαβ
  have hfixM := fixes_line_of_involution h (hG hτ'G) hτ'2 h5 hM hαβ hαM hβM
    ((hfix α).2 hα) ((hfix β).2 hβ)
  have hsub : M ⊆ L.map σ.toEmbedding := fun p hp => (hfix p).1 (hfixM p hp)
  have heq := Finset.eq_of_subset_of_card_le hsub (by
    rw [Finset.card_map, h.card_line hL, h.card_line hM])
  exact heq ▸ hM

end Normalizer

theorem mem_lineAut_of_normalizes {σ : Equiv.Perm (Fin 21)}
    (hσ : ∀ τ ∈ pslPerm.range, σ * τ * σ⁻¹ ∈ pslPerm.range) : σ ∈ lineAut := by
  have hG : pslPerm.range ≤ blockAut (Finset.univ.image projLine) := by
    rintro _ ⟨g, rfl⟩
    exact mem_blockAut_of_mem_lineAut (pslPerm_mem_lineAut g)
  have hel : ∀ L ∈ Finset.univ.image projLine, ∃ τ ∈ pslPerm.range, τ * τ = 1 ∧
      ∀ p, τ p = p ↔ p ∈ L := by
    intro L hL
    obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hL
    obtain ⟨g, hg2, hgL⟩ := exists_elation_projLine a
    exact ⟨pslPerm g, ⟨g, rfl⟩, hg2, hgL⟩
  have h := mem_blockAut_of_normalizes isSteinerPlane_projLine hG hel hσ
  intro a
  have := (h (projLine a)).2 (Finset.mem_image_of_mem _ (Finset.mem_univ a))
  obtain ⟨b, -, hb⟩ := Finset.mem_image.1 this
  exact ⟨b, hb.symm⟩

end CFSG.EvenSmallLie.UnitarySix.MathieuExt
