module

public import CFSG.GH74.Uniqueness.SU.SU7L193c

public section

namespace CFSG.GH74.Uniqueness.SU.SU7

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU5 CFSG

namespace L194

variable {G : Type} [Group G] [Finite G] {S : Sylow 2 G} {U M V : Subgroup G} {x z : G}
  {A B R : Subgroup G}

omit [Finite G] in
theorem pPrimeCore_eq_bot_of_core {a : G} (h : L193.core a = ⊥) :
    pPrimeCore 2 ↥(centralizer ({a} : Set G)) = ⊥ :=
  (Subgroup.map_eq_bot_iff_of_injective _ (centralizer ({a} : Set G)).subtype_injective).1 h

theorem O_invariant (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) {n : G}
    (hn : n ∈ normalizer (R : Set G)) {w : G} (hw : w ∈ (pPrimeCore 2 ↥M).map M.subtype) :
    n * w * n⁻¹ ∈ (pPrimeCore 2 ↥M).map M.subtype := by
  classical
  set O : Subgroup G := (pPrimeCore 2 ↥M).map M.subtype with hO
  have hc193 := L193.lemma193_c hKI3 hKI4 hc
  have hnR : ∀ r ∈ R, n⁻¹ * r * n ∈ R := fun r hr => by
    have := (mem_normalizer_iff.1 ((normalizer (R : Set G)).inv_mem hn) r).1 hr
    simpa using this
  set φ : G →* G := (MulAut.conj n).toMonoidHom with hφ
  have hsup : (⨆ (Y : Subgroup G) (_ : Odd (Nat.card Y)) (_ : R ≤ normalizer (Y : Set G)), Y) ≤
      O.comap φ := by
    refine iSup_le fun Y => iSup_le fun hYodd => iSup_le fun hRY => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hY'odd : Odd (Nat.card (Y.map φ)) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj n).injective]; exact hYodd
    have hRY' : R ≤ normalizer ((Y.map φ : Subgroup G) : Set G) := by
      intro r hr
      apply Gen.mem_normalizer_of_conj_le
      rintro _ ⟨y, hy, rfl⟩
      have h1 : (n⁻¹ * r * n) * y * (n⁻¹ * r * n)⁻¹ ∈ Y :=
        (mem_normalizer_iff.1 (hRY (hnR r hr)) y).1 hy
      refine ⟨(n⁻¹ * r * n) * y * (n⁻¹ * r * n)⁻¹, h1, ?_⟩
      simp only [hφ, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have hY'le : Y.map φ ≤ ⨆ (Y : Subgroup G) (_ : Odd (Nat.card Y))
        (_ : R ≤ normalizer (Y : Set G)), Y :=
      le_iSup_of_le (Y.map φ) (le_iSup_of_le hY'odd (le_iSup_of_le hRY' le_rfl))
    rw [hc193] at hY'le
    exact hY'le
  rw [hc193] at hsup
  exact hsup hw

theorem lemma194_of_ctx (hKI3 : K.KI3) (hKI4 : K.KI4) (hc : Ctx19 S U M V x z A B R) :
    pPrimeCore 2 ↥M = ⊥ ∧
      ∀ t ∈ (S : Subgroup G), orderOf t = 2 → pPrimeCore 2 ↥(centralizer ({t} : Set G)) = ⊥ := by
  classical
  have hOM : pPrimeCore 2 ↥M = ⊥ := by
    by_contra hne
    set O : Subgroup G := (pPrimeCore 2 ↥M).map M.subtype with hO
    have hOne : O ≠ ⊥ := fun h =>
      hne ((Subgroup.map_eq_bot_iff_of_injective _ M.subtype_injective).1 h)
    have hMN : M ≤ normalizer (O : Set G) := fun m hm => by
      apply Gen.mem_normalizer_of_conj_le
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨⟨m, hm⟩ * w * ⟨m, hm⟩⁻¹,
        (inferInstance : (pPrimeCore 2 ↥M).Normal).conj_mem w hw ⟨m, hm⟩, rfl⟩
    have hNtop : normalizer (O : Set G) ≠ ⊤ := by
      intro htop
      have hnorm : O.Normal := Subgroup.normalizer_eq_top_iff.1 htop
      have hs := hc.hyp.simple
      have := hs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal O with h | h
      · exact hOne h
      · have hMtop : M = ⊤ := by
          rw [eq_top_iff]
          intro g _
          have : g ∈ O := by rw [h]; exact Subgroup.mem_top g
          exact Subgroup.map_subtype_le _ this
        exact hc.hyp.maximal.ne_top hMtop
    have hNM : normalizer (O : Set G) = M := (hc.hyp.maximal.le_iff_eq hNtop).1 hMN
    apply L192.lemma192_b hKI3 hKI4 hc
    intro n hn
    rw [← hNM]
    exact Gen.mem_normalizer_of_conj_le (fun w hw => O_invariant hKI3 hKI4 hc hn hw)
  refine ⟨hOM, ?_⟩
  intro t htS ht2
  have hOMimg : (pPrimeCore 2 ↥M).map M.subtype = ⊥ := by rw [hOM]; exact Subgroup.map_bot _
  by_cases htT : t ∈ Tsub S U
  · apply pPrimeCore_eq_bot_of_core
    rw [eq_bot_iff, ← hOMimg]
    exact L193.lemma193_a hKI3 hc t htT ht2
  ·
    obtain ⟨u₀, hu₀U, hu₀1, hu₀z⟩ := RF.exists_u₀ hc
    obtain ⟨g, hgC, hg⟩ := lemma191 G S U M V x z A B R hc t htS htT ht2 u₀ hu₀U hu₀1 hu₀z
    have hu₀T : u₀ ∈ Tsub S U := Base.U_le_T hc.hyp hc.conf hc.concl hu₀U
    have hu₀2 : orderOf u₀ = 2 := by
      have hvv : u₀ * u₀ = 1 := by
        rw [← pow_two]; exact (isElemAbelian_iff.1 hc.hyp.four.2.1).2 u₀ hu₀U
      exact orderOf_eq_prime (by rw [pow_two]; exact hvv) hu₀1
    have hcore : L193.core u₀ = ⊥ := by
      rw [eq_bot_iff, ← hOMimg]
      exact L193.lemma193_a hKI3 hc u₀ hu₀T hu₀2
    apply pPrimeCore_eq_bot_of_core
    rw [eq_bot_iff]
    intro w hw
    have h1 := L193.core_conj_le (z := t) (v := u₀) (h := g⁻¹) (by simpa using hg) hw
    rw [hcore, Subgroup.mem_bot] at h1
    rw [Subgroup.mem_bot]
    have : w = g * (g⁻¹ * w * g⁻¹⁻¹) * g⁻¹ := by group
    rw [this, h1]; group

end L194

theorem lemma194 (hKI3 : K.KI3) (hKI4 : K.KI4) : Lemma194Stmt := by
  intro G _ _ S U M V x z A B R hc
  exact L194.lemma194_of_ctx hKI3 hKI4 hc

end CFSG.GH74.Uniqueness.SU.SU7
