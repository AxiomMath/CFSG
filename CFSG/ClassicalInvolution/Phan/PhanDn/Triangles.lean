module

public import CFSG.ClassicalInvolution.Phan.PhanDn.Solid
public import CFSG.ClassicalInvolution.Phan.Geometry.ShortCycleMoves

public section

namespace CFSG.ClassicalInvolution.PhanDn

open QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.BorelTits
open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}

theorem exists_flipflop_of_rad (hσ : ∀ x, σ (σ x) = x)
    {L : Submodule K (Fin n ⊕ Fin n → K)} (hL : IsFlipLine σ L)
    {r : Fin n ⊕ Fin n → K} (hr : r ≠ 0) (hrs : quadPlus n K r = 0)
    (hrL : K ∙ r ≤ qPerp n K L) (hrh : K ∙ r ≤ flipOrth σ L)
    (hrr : flipHerm σ r r = 0) (hinv : dFlip σ r ∉ K ∙ r) :
    ∃ U, IsFlipflopSub σ U ∧ L ⊔ K ∙ r ≤ U := by
  classical
  have _ : r ≠ 0 := hr
  have hrL' : r ∈ qPerp n K L := hrL (Submodule.mem_span_singleton_self r)
  have hrh' : r ∈ flipOrth σ L := hrh (Submodule.mem_span_singleton_self r)
  obtain ⟨hMnd, -, -, hMinv⟩ := hL.1.sup_dFlipSub hσ
  have hW'nd : QNondeg (qPerp n K (L ⊔ dFlipSub σ L)) := hMnd.qPerp
  have hW'inv : dFlipSub σ (qPerp n K (L ⊔ dFlipSub σ L)) =
      qPerp n K (L ⊔ dFlipSub σ L) := by
    have h := qPerp_dFlipSub hσ (L ⊔ dFlipSub σ L)
    rw [hMinv] at h
    exact h.symm
  have hrW' : r ∈ qPerp n K (L ⊔ dFlipSub σ L) := by
    rw [mem_qPerp]
    intro w hw
    obtain ⟨l, hl, x, hx, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨l', hl', rfl⟩ : ∃ l' ∈ L, dFlip σ l' = x :=
      ⟨dFlip σ x, (mem_dFlipSub hσ).mp hx, dFlip_dFlip hσ x⟩
    rw [polar_add_left]
    have h1 : polar (quadPlus n K) l r = 0 := (mem_qPerp.mp hrL') l hl
    have h2 : polar (quadPlus n K) (dFlip σ l') r = 0 := by
      have h := polar_dFlip (σ := σ) l' (dFlip σ r)
      rw [dFlip_dFlip hσ r] at h
      rw [h, ← flipHerm]
      rw [(mem_flipOrth.mp hrh') l' hl', map_zero]
    rw [h1, h2, add_zero]
  have hσrW' : dFlip σ r ∈ qPerp n K (L ⊔ dFlipSub σ L) := by
    have hmem : dFlip σ r ∈ dFlipSub σ (qPerp n K (L ⊔ dFlipSub σ L)) :=
      (mem_dFlipSub hσ).mpr (by rwa [dFlip_dFlip hσ])
    rwa [hW'inv] at hmem
  have hv : dFlip σ r ∈ qPerp n K (L ⊔ dFlipSub σ L) ⊓ qPerp n K (K ∙ r) := by
    refine ⟨hσrW', mem_qPerp.mpr ?_⟩
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [polar_smul_left]
    have h : polar (quadPlus n K) r (dFlip σ r) = 0 := hrr
    rw [h, smul_zero]
  have hvs : quadPlus n K (dFlip σ r) = 0 := by
    rw [quadPlus_dFlip, hrs, map_zero]
  obtain ⟨t, ht, hts, hrt⟩ := exists_singular_polar_eq_one hW'nd
    (show K ∙ r ≤ qPerp n K (L ⊔ dFlipSub σ L) from
      (Submodule.span_singleton_le_iff_mem _ _).mpr hrW') hv hinv hvs
  have hbt : polar (quadPlus n K) r t = 0 :=
    (mem_qPerp.mp ht.2) r (Submodule.mem_span_singleton_self r)
  have hB : IsFlipflopSub σ (K ∙ r ⊔ K ∙ t) := by
    refine ⟨?_, ?_⟩
    · intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
      rw [QuadraticMap.map_add (quadPlus n K), QuadraticMap.map_smul (quadPlus n K),
        QuadraticMap.map_smul (quadPlus n K), hrs, hts,
        polar_smul_left, polar_smul_right, hbt]
      simp
    · intro u hu hper
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb
      have htr : flipHerm σ t r = 1 := by
        rw [flipHerm, polar_comm]
        exact hrt
      have hrt' : flipHerm σ r t = 1 := by
        have h := flipHerm_conj hσ r t
        rw [htr] at h
        exact σ.injective (by rw [h, map_one])
      have h1 := hper r (Submodule.mem_sup_left (Submodule.mem_span_singleton_self r))
      have h2 := hper t (Submodule.mem_sup_right (Submodule.mem_span_singleton_self t))
      simp only [flipHerm_add_left, flipHerm_smul_left, hrr, htr, hrt', mul_one, mul_zero,
        zero_add] at h1 h2
      rw [h1, zero_mul, add_zero] at h2
      rw [h1, h2, zero_smul, zero_smul, add_zero]
  have hLB : L ≤ qPerp n K (K ∙ r ⊔ K ∙ t) := by
    intro l hl
    rw [mem_qPerp]
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hlr : polar (quadPlus n K) r l = 0 := by
      rw [polar_comm]
      exact (mem_qPerp.mp hrL') l hl
    have hlt : polar (quadPlus n K) t l = 0 := by
      rw [polar_comm]
      exact (mem_qPerp.mp ht.1) l (Submodule.mem_sup_left hl)
    rw [polar_add_left, polar_smul_left, polar_smul_left, hlr, hlt]
    simp
  have hLflipOrth : L ≤ flipOrth σ (K ∙ r ⊔ K ∙ t) := by
    intro l hl
    rw [mem_flipOrth]
    intro w hw
    obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hy
    have hrl : flipHerm σ r l = 0 := by
      rw [← flipHerm_conj hσ l r]
      rw [(mem_flipOrth.mp hrh') l hl, map_zero]
    have hdt : dFlip σ t ∈ qPerp n K (L ⊔ dFlipSub σ L) := by
      have hmem : dFlip σ t ∈ dFlipSub σ (qPerp n K (L ⊔ dFlipSub σ L)) :=
        (mem_dFlipSub hσ).mpr (by rw [dFlip_dFlip hσ]; exact ht.1)
      rwa [hW'inv] at hmem
    have hlt : flipHerm σ l t = 0 := by
      rw [flipHerm]
      exact (mem_qPerp.mp hdt) l (Submodule.mem_sup_left hl)
    have htl : flipHerm σ t l = 0 := by
      rw [← flipHerm_conj hσ l t, hlt, map_zero]
    rw [flipHerm_add_left, flipHerm_smul_left, flipHerm_smul_left, hrl, htl]
    simp
  have hsup := IsFlipflopSub.sup_of_orth hσ hL.1 hB hLB hLflipOrth
  exact ⟨L ⊔ (K ∙ r ⊔ K ∙ t), hsup.1, sup_le le_sup_left (le_trans le_sup_left le_sup_right)⟩

theorem isFlipflopSub_of_compl_rad (hσ : ∀ x, σ (σ x) = x)
    {W Y A : Submodule K (Fin n ⊕ Fin n → K)}
    (hW : QSing W) (hY : Y ≤ W ⊓ flipOrth σ W)
    (hrad : W ⊓ flipOrth σ W ≤ Y) (hA : A ≤ W) (hAY : A ⊓ Y = ⊥)
    (hAW : A ⊔ Y = W) : IsFlipflopSub σ A := by
  have hWfun : ∀ w ∈ W, quadPlus n K w = 0 := by
    intro w hw
    have h : (quadPlusForm n K).Q w = 0 := (qSing_iff_isTotallySingular W).mp hW w hw
    rwa [quadPlusForm_Q] at h
  refine ⟨fun a ha => hWfun a (hA ha), fun a ha hper => ?_⟩
  have hper' : a ∈ flipOrth σ W := by
    rw [mem_flipOrth]
    intro w hw
    have hw' : w ∈ A ⊔ Y := by rw [hAW]; exact hw
    obtain ⟨a', ha', y, hy, rfl⟩ := Submodule.mem_sup.mp hw'
    rw [flipHerm_add_left]
    have haa' : flipHerm σ a' a = 0 := by
      rw [← flipHerm_conj hσ a a']
      rw [hper a' ha', map_zero]
    have hya : flipHerm σ y a = 0 := by
      have hay : flipHerm σ a y = 0 := (mem_flipOrth.mp (hY hy).2) a (hA ha)
      rw [← flipHerm_conj hσ a y, hay, map_zero]
    rw [haa', hya, add_zero]
  have harad : a ∈ Y := hrad ⟨hA ha, hper'⟩
  have hmem : a ∈ A ⊓ Y := ⟨ha, harad⟩
  rw [hAY] at hmem
  simpa using hmem


private theorem smul_eq_zero_of_mem_span_singleton {s r : Fin n ⊕ Fin n → K}
    (hs : s ∉ K ∙ r) {c : K} (h : c • s ∈ K ∙ r) : c = 0 := by
  by_contra hc
  apply hs
  have h' : s = c⁻¹ • (c • s) := (inv_smul_smul₀ hc s).symm
  rw [h']
  exact (K ∙ r).smul_mem _ h

private theorem diff_eq_of_two_mem {s r : Fin n ⊕ Fin n → K} {ρ : K}
    (hρr : dFlip σ r = ρ • r) {μ μ' c c' : K}
    (h : dFlip σ (s + μ • r) = c • (s + μ • r))
    (h' : dFlip σ (s + μ' • r) = c' • (s + μ' • r)) :
    c • (s + μ • r) - c' • (s + μ' • r) = ((σ μ - σ μ') * ρ) • r := by
  rw [← h, ← h', dFlip_add, dFlip_add, dFlip_smul, dFlip_smul, hρr, smul_smul, smul_smul]
  have h1 : dFlip σ s + (σ μ * ρ) • r - (dFlip σ s + (σ μ' * ρ) • r) =
      (σ μ * ρ) • r - (σ μ' * ρ) • r := by abel
  rw [h1, ← sub_smul]
  congr 1
  ring

private theorem scalar_eq_of_two_mem {s r : Fin n ⊕ Fin n → K} {ρ : K}
    (hρr : dFlip σ r = ρ • r) (hs : s ∉ K ∙ r) {μ μ' c c' : K}
    (h : dFlip σ (s + μ • r) = c • (s + μ • r))
    (h' : dFlip σ (s + μ' • r) = c' • (s + μ' • r)) : c = c' := by
  have hkey := diff_eq_of_two_mem (σ := σ) hρr h h'
  have hA : (c - c') • s + (c * μ - c' * μ') • r = ((σ μ - σ μ') * ρ) • r := by
    rw [sub_smul, sub_smul]
    calc c • s - c' • s + ((c * μ) • r - (c' * μ') • r)
        = c • (s + μ • r) - c' • (s + μ' • r) := by
          rw [smul_add, smul_add, smul_smul, smul_smul]
          abel
      _ = _ := hkey
  have hmem : (c - c') • s ∈ K ∙ r := by
    have hsub : (c - c') • s = ((σ μ - σ μ') * ρ) • r - (c * μ - c' * μ') • r :=
      eq_sub_iff_add_eq.mpr hA
    rw [hsub, ← sub_smul]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self r)
  exact sub_eq_zero.mp (smul_eq_zero_of_mem_span_singleton hs hmem)

private theorem coef_rel_of_two_mem {s r : Fin n ⊕ Fin n → K} {ρ : K}
    (hρr : dFlip σ r = ρ • r) (hr0 : r ≠ 0) {μ μ' c : K}
    (h : dFlip σ (s + μ • r) = c • (s + μ • r))
    (h' : dFlip σ (s + μ' • r) = c • (s + μ' • r)) :
    ρ * σ (μ - μ') = c * (μ - μ') := by
  have hkey := diff_eq_of_two_mem (σ := σ) hρr h h'
  have hkey' : (c * μ - c * μ') • r = ((σ μ - σ μ') * ρ) • r := by
    rw [sub_smul]
    calc (c * μ) • r - (c * μ') • r
        = c • (s + μ • r) - c • (s + μ' • r) := by
          rw [smul_add, smul_add, smul_smul, smul_smul]
          abel
      _ = _ := hkey
  have hcoef : c * μ - c * μ' = (σ μ - σ μ') * ρ := smul_left_injective K hr0 hkey'
  rw [← map_sub] at hcoef
  rw [mul_comm ρ (σ (μ - μ')), ← hcoef, mul_sub]

theorem ncard_inv_le (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) {s r : Fin n ⊕ Fin n → K}
    (hs : s ∉ K ∙ r) (hr0 : r ≠ 0) (hρ : dFlip σ r ∈ K ∙ r) :
    {μ : K | dFlip σ (s + μ • r) ∈ K ∙ (s + μ • r)}.ncard ≤ q := by
  classical
  obtain ⟨ρ, hρr⟩ := Submodule.mem_span_singleton.mp hρ
  have hρr' : dFlip σ r = ρ • r := hρr.symm
  have hρ0 : ρ ≠ 0 := by
    intro h0
    apply hr0
    have hdr : dFlip σ r = 0 := by rw [hρr', h0, zero_smul]
    have hd0 : dFlip σ (0 : Fin n ⊕ Fin n → K) = 0 := by
      funext x
      cases x <;> simp [dFlip]
    have h : dFlip σ (dFlip σ r) = 0 := by rw [hdr, hd0]
    rwa [dFlip_dFlip hσ.invol] at h
  have hq1 : 1 ≤ q := by
    have hpos : 0 < q ^ 2 := by
      rw [← hK]
      exact Nat.card_pos_iff.mpr ⟨⟨0⟩, inferInstance⟩
    exact Nat.one_le_iff_ne_zero.mpr (by rintro rfl; simp at hpos)
  by_cases hsmall : {μ : K | dFlip σ (s + μ • r) ∈ K ∙ (s + μ • r)}.ncard ≤ 1
  · omega
  · have h2 : 1 < {μ : K | dFlip σ (s + μ • r) ∈ K ∙ (s + μ • r)}.ncard := by omega
    have hne0 : {μ : K | dFlip σ (s + μ • r) ∈ K ∙ (s + μ • r)}.ncard ≠ 0 := by
      omega
    obtain ⟨μ₂, hμ₂⟩ := Set.nonempty_of_ncard_ne_zero hne0
    obtain ⟨μ₁, hμ₁, hne⟩ := Set.exists_ne_of_one_lt_ncard h2 μ₂
    obtain ⟨c₁, hc₁⟩ := Submodule.mem_span_singleton.mp hμ₁
    obtain ⟨c₂, hc₂⟩ := Submodule.mem_span_singleton.mp hμ₂
    have hc₁' : dFlip σ (s + μ₁ • r) = c₁ • (s + μ₁ • r) := hc₁.symm
    have hc₂' : dFlip σ (s + μ₂ • r) = c₂ • (s + μ₂ • r) := hc₂.symm
    have hc_eq : c₁ = c₂ := scalar_eq_of_two_mem hρr' hs hc₁' hc₂'
    have hc₂'' : dFlip σ (s + μ₂ • r) = c₁ • (s + μ₂ • r) := by rw [hc₂', hc_eq]
    let δ : K := μ₁ - μ₂
    have hδ0 : δ ≠ 0 := sub_ne_zero.mpr hne
    have hrel : ρ * σ δ = c₁ * δ := coef_rel_of_two_mem hρr' hr0 hc₁' hc₂''
    have hσδ0 : σ δ ≠ 0 := (map_ne_zero σ).mpr hδ0
    let g : {μ : K | dFlip σ (s + μ • r) ∈ K ∙ (s + μ • r)} → {c : K // σ c = c} :=
      fun μ => ⟨(μ.1 - μ₁) / δ, by
        obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp μ.2
        have hc' : dFlip σ (s + μ.1 • r) = c • (s + μ.1 • r) := hc.symm
        have hcc : c = c₁ := scalar_eq_of_two_mem hρr' hs hc' hc₁'
        have hc₁'' : dFlip σ (s + μ₁ • r) = c • (s + μ₁ • r) := by rw [hc₁', hcc]
        have hcoef : ρ * σ (μ.1 - μ₁) = c * (μ.1 - μ₁) :=
          coef_rel_of_two_mem hρr' hr0 hc' hc₁''
        have hrelc : ρ * σ δ = c * δ := by rw [hrel, hcc]
        have h1 : ρ * (σ (μ.1 - μ₁) * δ) = c * ((μ.1 - μ₁) * δ) := by
          rw [← mul_assoc, hcoef, mul_assoc]
        have h2 : ρ * ((μ.1 - μ₁) * σ δ) = c * ((μ.1 - μ₁) * δ) := by
          rw [mul_comm (μ.1 - μ₁) (σ δ), ← mul_assoc, hrelc, mul_assoc,
            mul_comm δ (μ.1 - μ₁)]
        have hcross : σ (μ.1 - μ₁) * δ = (μ.1 - μ₁) * σ δ :=
          mul_left_cancel₀ hρ0 (h1.trans h2.symm)
        rw [map_sub] at hcross
        rw [map_div₀, map_sub]
        field_simp [hδ0, hσδ0]
        rw [mul_comm (σ δ) (μ.1 - μ₁)]
        exact hcross⟩
    have hginj : Function.Injective g := by
      intro μ ν hμν
      have h : (μ.1 - μ₁) / δ = (ν.1 - μ₁) / δ := congrArg Subtype.val hμν
      have h' : μ.1 = ν.1 := by
        have h2 : μ.1 - μ₁ = ν.1 - μ₁ := by
          have := congrArg (fun x => x * δ) h
          rwa [div_mul_cancel₀ _ hδ0, div_mul_cancel₀ _ hδ0] at this
        linear_combination h2
      exact Subtype.ext h'
    have hcard : Nat.card {μ : K | dFlip σ (s + μ • r) ∈ K ∙ (s + μ • r)} ≤
        Nat.card {c : K // σ c = c} := Nat.card_le_card_of_injective g hginj
    rwa [Nat.card_coe_set_eq, card_fixed_eq hσ hK] at hcard


private theorem isFlipflopSub_of_flipPt {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : IsFlipflopSub σ p := by
  obtain ⟨v, hv, hq, hh⟩ := hp.exists_eq_span
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hh (by simp)
  rw [hv]
  exact (isFlipflopSub_span_singleton_iff hv0).mpr ⟨hq, hh⟩

private theorem finrank_of_flipPt {p : Submodule K (Fin n ⊕ Fin n → K)}
    (hp : IsFlipflopPt σ p) : Module.finrank K p = 1 := by
  obtain ⟨v, hv, -, hh⟩ := hp.exists_eq_span
  have hv0 : v ≠ 0 := by
    rintro rfl
    exact hh (by simp)
  rw [hv, finrank_span_singleton hv0]

private theorem quadPlus_eq_zero_of_qSing {W : Submodule K (Fin n ⊕ Fin n → K)}
    (hW : QSing W) {w : Fin n ⊕ Fin n → K} (hw : w ∈ W) : quadPlus n K w = 0 := by
  have h : (quadPlusForm n K).Q w = 0 := (qSing_iff_isTotallySingular W).mp hW w hw
  rwa [quadPlusForm_Q] at h

private theorem polar_eq_zero_of_qSing {W : Submodule K (Fin n ⊕ Fin n → K)} (hW : QSing W)
    {u v : Fin n ⊕ Fin n → K} (hu : u ∈ W) (hv : v ∈ W) :
    polar (quadPlus n K) u v = 0 := by
  have h := (mem_qPerp.mp (QSing.le_qPerp hW hu)) v hv
  rwa [polar_comm] at h

private theorem exists_flipflop_of_rad_side (hσ : ∀ x, σ (σ x) = x)
    {M U W Y : Submodule K (Fin n ⊕ Fin n → K)} (hM : IsFlipLine σ M)
    (hMU : M ≤ U) (hUW : U ≤ W) (hYW : Y ≤ W) (hW : QSing W)
    (hYflip : Y ≤ flipOrth σ W) (hYiso : ∀ y ∈ Y, flipHerm σ y y = 0)
    {y : Fin n ⊕ Fin n → K} (hyY : y ∈ Y) (hyU : y ∉ U)
    (hinv : dFlip σ y ∉ K ∙ y) :
    ∃ V, IsFlipflopSub σ V ∧ M ⊔ K ∙ y ≤ V := by
  have hy0 : y ≠ 0 := fun h => hyU (h ▸ U.zero_mem)
  have hyW : y ∈ W := hYW hyY
  have hq : quadPlus n K y = 0 := quadPlus_eq_zero_of_qSing hW hyW
  have hperp : K ∙ y ≤ qPerp n K M := by
    refine (Submodule.span_singleton_le_iff_mem _ _).mpr ?_
    refine (mem_qPerp (n := n) (K := K) (W := M)).mpr fun m hm => ?_
    exact polar_eq_zero_of_qSing hW (hUW (hMU hm)) hyW
  have hflip : K ∙ y ≤ flipOrth σ M :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (mem_flipOrth.mpr fun m hm =>
      (mem_flipOrth.mp (hYflip hyY)) m (hUW (hMU hm)))
  exact exists_flipflop_of_rad hσ hM hy0 hq hperp hflip (hYiso y hyY) hinv

private theorem isFlipflopSub_compl_of_WY (hσ : ∀ x, σ (σ x) = x)
    {W Y A : Submodule K (Fin n ⊕ Fin n → K)} (hW : QSing W)
    (hYW : Y ≤ W) (hYflip : Y ≤ flipOrth σ W)
    (hYrad : W ⊓ flipOrth σ W ≤ Y) (hA : A ≤ W) (hAW : A ⊔ Y = W)
    (hdimA : Module.finrank K A = 2) (hdimY : Module.finrank K Y = 2)
    (hdimW : Module.finrank K W = 4) : IsFlipflopSub σ A := by
  have hYle : Y ≤ W ⊓ flipOrth σ W := le_inf hYW hYflip
  have hdim : Module.finrank K ↥(A ⊓ Y) = 0 := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq A Y
    rw [hAW, hdimA, hdimY, hdimW] at h
    omega
  exact isFlipflopSub_of_compl_rad hσ hW hYle hYrad hA (Submodule.finrank_eq_zero.mp hdim)
    hAW

private structure RadData (σ : K ≃+* K) (L U : Submodule K (Fin n ⊕ Fin n → K)) where
  r : Fin n ⊕ Fin n → K
  mem_U : r ∈ U
  perp : ∀ v ∈ U, flipHerm σ r v = 0
  ne_zero : r ≠ 0
  not_mem_L : r ∉ L
  dim_U : Module.finrank K U = 3
  U_eq : U = L ⊔ K ∙ r
  radical : U ⊓ flipOrth σ U = K ∙ r
  L_perp : K ∙ r ≤ qPerp n K L
  L_flip : K ∙ r ≤ flipOrth σ L
  self : flipHerm σ r r = 0

private structure BDiv (σ : K ≃+* K) (U : Submodule K (Fin n ⊕ Fin n → K)) where
  X : Submodule K (Fin n ⊕ Fin n → K)
  s : Fin n ⊕ Fin n → K
  hXsing : QSing X
  hUX : U ≤ X
  hsU : s ∉ U
  hsX : s ∈ X
  hsdX : dFlip σ s ∈ X

private structure BData (σ : K ≃+* K) (L U : Submodule K (Fin n ⊕ Fin n → K))
    (r : Fin n ⊕ Fin n → K) where
  W : Submodule K (Fin n ⊕ Fin n → K)
  Y : Submodule K (Fin n ⊕ Fin n → K)
  s : Fin n ⊕ Fin n → K
  hYdef : Y = K ∙ r ⊔ K ∙ s
  hUW : U ≤ W
  hYW : Y ≤ W
  hdimW : Module.finrank K W = 4
  hdimY : Module.finrank K Y = 2
  hWsing : QSing W
  hYflip : Y ≤ flipOrth σ W
  hYiso : ∀ y ∈ Y, flipHerm σ y y = 0
  hWrad : W ⊓ flipOrth σ W = Y
  hWLY : W = L ⊔ Y
  hsU : s ∉ U
  hsKr : s ∉ K ∙ r

private structure BCoords (σ : K ≃+* K) (a b c : FlipPt σ n)
    (L : Submodule K (Fin n ⊕ Fin n → K)) (r : Fin n ⊕ Fin n → K) where
  u : Fin n ⊕ Fin n → K
  v : Fin n ⊕ Fin n → K
  w : Fin n ⊕ Fin n → K
  α : K
  β : K
  δ : K
  hua : u ∈ a.1
  hvb : v ∈ b.1
  hwc : w ∈ c.1
  hu0 : u ≠ 0
  hv0 : v ≠ 0
  hw0 : w ≠ 0
  haK : a.1 = K ∙ u
  hbK : b.1 = K ∙ v
  hcK : c.1 = K ∙ w
  hwL : w ∉ L
  hδ0 : δ ≠ 0
  hα0 : α ≠ 0
  hβ0 : β ≠ 0
  hwdecomp : w = α • u + β • v + δ • r

private structure BZ (σ : K ≃+* K) (a b c : FlipPt σ n)
    (L : Submodule K (Fin n ⊕ Fin n → K)) (r : Fin n ⊕ Fin n → K)
    (C : BCoords σ a b c L r) where
  θ : K
  zvec : Fin n ⊕ Fin n → K
  hθ0 : θ ≠ 0
  hθβ : θ ≠ C.β / C.α
  hzvecL : zvec ∈ L
  hzvecdef : zvec = C.u + θ • C.v
  hzvecaniso : flipHerm σ zvec zvec ≠ 0

private structure BLam (σ : K ≃+* K) (L U : Submodule K (Fin n ⊕ Fin n → K))
    (r : Fin n ⊕ Fin n → K) (S : BData σ L U r)
    {a b c : FlipPt σ n} (C : BCoords σ a b c L r) (Z : BZ σ a b c L r C) where
  lam : K
  μ₂ : K
  μ₃ : K
  hμ₂ : μ₂ = C.δ / C.α
  hμ₃ : μ₃ = Z.θ * C.δ / C.β
  hlamB : dFlip σ (S.s + lam • r) ∉ K ∙ (S.s + lam • r)
  hlam2 : dFlip σ (S.s + (lam - μ₂) • r) ∉ K ∙ (S.s + (lam - μ₂) • r)
  hlam3 : dFlip σ (S.s + (lam - μ₃) • r) ∉ K ∙ (S.s + (lam - μ₃) • r)

private structure BApex (σ : K ≃+* K) (L U : Submodule K (Fin n ⊕ Fin n → K))
    (r : Fin n ⊕ Fin n → K) (S : BData σ L U r)
    {a b c : FlipPt σ n} (C : BCoords σ a b c L r) (Z : BZ σ a b c L r C)
    (Λ : BLam σ L U r S C Z) where
  y : Fin n ⊕ Fin n → K
  y₂ : Fin n ⊕ Fin n → K
  y₃ : Fin n ⊕ Fin n → K
  t : Fin n ⊕ Fin n → K
  hyY : y ∈ S.Y
  hyU : y ∉ U
  hy2Y : y₂ ∈ S.Y
  hy2U : y₂ ∉ U
  hy3Y : y₃ ∈ S.Y
  hy3U : y₃ ∉ U
  hydef : y = S.s + Λ.lam • r
  hy2def : y₂ = S.s + (Λ.lam - Λ.μ₂) • r
  hy3def : y₃ = S.s + (Λ.lam - Λ.μ₃) • r
  htdef : t = Z.zvec + y
  htL : t ∉ L
  htW : t ∈ S.W
  htq : quadPlus n K t = 0
  ht0 : t ≠ 0
  hth : flipHerm σ t t ≠ 0
  htpt : IsFlipflopPt σ (K ∙ t)
  htmem_y : t ∈ L ⊔ K ∙ y
  htmem_bc : t ∈ (b.1 ⊔ c.1) ⊔ K ∙ y₂
  htmem_ca : t ∈ (c.1 ⊔ a.1) ⊔ K ∙ y₃
  hkey : t - (Z.θ / C.β) • C.w - y₃ = (1 - Z.θ * C.α / C.β) • C.u

private noncomputable def radical_data (hσ : IsUnitaryInvolution σ)
    {L U : Submodule K (Fin n ⊕ Fin n → K)} (hLline : IsFlipLine σ L)
    (hUsing : QSing U) (hUflip : ¬ IsFlipflopSub σ U)
    {c : FlipPt σ n} (hcL : ¬ c.1 ≤ L) (hUeq : U = L ⊔ c.1) :
    RadData σ L U := by
  have hLU : L ≤ U := by
    rw [hUeq]
    exact le_sup_left
  have hcU : c.1 ≤ U := by
    rw [hUeq]
    exact le_sup_right
  classical
  have hex : ∃ r, r ∈ U ∧ (∀ v ∈ U, flipHerm σ r v = 0) ∧ r ≠ 0 := by
    have hUsing' : ∀ u ∈ U, quadPlus n K u = 0 := by
      intro u hu
      have h : (quadPlusForm n K).Q u = 0 := (qSing_iff_isTotallySingular U).mp hUsing u hu
      rwa [quadPlusForm_Q] at h
    by_contra hcon
    push Not at hcon
    exact hUflip ⟨hUsing', fun u hu hper => hcon u hu hper⟩
  let r := Classical.choose hex
  have hrU : r ∈ U := (Classical.choose_spec hex).1
  have hrperp : ∀ v ∈ U, flipHerm σ r v = 0 := (Classical.choose_spec hex).2.1
  have hr0 : r ≠ 0 := (Classical.choose_spec hex).2.2
  have hrnotL : r ∉ L := by
    intro hrL
    have hmem : r ∈ L ⊓ flipOrth σ L :=
      ⟨hrL, mem_flipOrth.mpr fun y hy => by
        rw [← flipHerm_conj hσ.invol r y, hrperp y (hLU hy), map_zero]⟩
    rw [inf_flipOrth_eq_bot hσ.invol hLline.1] at hmem
    exact hr0 (by simpa using hmem)
  have hdimU : Module.finrank K U = 3 := by
    have hinf : L ⊓ c.1 = ⊥ := by
      by_contra hne
      have hpos : 0 < Module.finrank K ↥(L ⊓ c.1) := by
        by_contra h0
        exact hne (Submodule.finrank_eq_zero.mp (by omega))
      have hle1 : Module.finrank K ↥(L ⊓ c.1) ≤ 1 := by
        have h := Submodule.finrank_mono (inf_le_right : L ⊓ c.1 ≤ c.1)
        rwa [finrank_of_flipPt c.2] at h
      have h1 : Module.finrank K ↥(L ⊓ c.1) = 1 := by omega
      have heq : L ⊓ c.1 = c.1 :=
        Submodule.eq_of_le_of_finrank_eq inf_le_right (by rw [h1, finrank_of_flipPt c.2])
      exact hcL (heq ▸ inf_le_left)
    have hd := Submodule.finrank_sup_add_finrank_inf_eq L c.1
    rw [hinf, finrank_bot, add_zero, hLline.2, finrank_of_flipPt c.2] at hd
    rw [hUeq]
    omega
  have hUeqR : U = L ⊔ K ∙ r := by
    have hle : L ⊔ K ∙ r ≤ U :=
      sup_le hLU ((Submodule.span_singleton_le_iff_mem _ _).mpr hrU)
    have hdim : Module.finrank K ↥(L ⊔ K ∙ r) = 3 := by
      have hdisj : L ⊓ K ∙ r = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        obtain ⟨hxL, hxr⟩ := Submodule.mem_inf.mp hx
        obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxr
        by_cases hc : c = 0
        · simp [hc]
        · exfalso
          apply hrnotL
          have h : r = c⁻¹ • (c • r) := (inv_smul_smul₀ hc r).symm
          rw [h]
          exact L.smul_mem _ hxL
      have hd := Submodule.finrank_sup_add_finrank_inf_eq L (K ∙ r)
      rw [hdisj, finrank_bot, add_zero, hLline.2, finrank_span_singleton hr0] at hd
      omega
    exact (Submodule.eq_of_le_of_finrank_eq hle (by rw [hdim, hdimU])).symm
  have hrflip : r ∈ flipOrth σ U := mem_flipOrth.mpr fun v hv => by
    rw [← flipHerm_conj hσ.invol r v]
    rw [hrperp v hv, map_zero]
  have hrad : U ⊓ flipOrth σ U = K ∙ r := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxU, hxperp⟩ := Submodule.mem_inf.mp hx
      rw [hUeqR] at hxU
      obtain ⟨l, hl, a, ha, rfl⟩ := Submodule.mem_sup.mp hxU
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      have hl0 : l = 0 := by
        have hmem : l ∈ L ⊓ flipOrth σ L := by
          refine ⟨hl, mem_flipOrth.mpr fun y hy => ?_⟩
          have hyU : y ∈ U := hLU hy
          have hvU : l + c • r ∈ U := by
            rw [hUeqR]
            exact Submodule.add_mem _ (Submodule.mem_sup_left hl)
              (Submodule.smul_mem _ c
                (Submodule.mem_sup_right (Submodule.mem_span_singleton_self r)))
          have h1 : flipHerm σ y (l + c • r) = 0 := (mem_flipOrth.mp hxperp) y hyU
          have hyr : flipHerm σ y r = 0 := by
            rw [← flipHerm_conj hσ.invol r y, hrperp y hyU, map_zero]
          have h2 : flipHerm σ y (c • r) = 0 := by
            rw [flipHerm_smul_right, hyr, mul_zero]
          rw [flipHerm_add_right, h2, add_zero] at h1
          exact h1
        rw [inf_flipOrth_eq_bot hσ.invol hLline.1] at hmem
        simpa using hmem
      rw [hl0, zero_add]
      exact Submodule.mem_span_singleton.mpr ⟨c, rfl⟩
    · intro x hx
      rw [Submodule.mem_span_singleton] at hx
      obtain ⟨c, rfl⟩ := hx
      exact ⟨Submodule.smul_mem _ _ hrU, Submodule.smul_mem _ _ hrflip⟩
  have hrLperp : K ∙ r ≤ qPerp n K L := by
    have hUperp : U ≤ qPerp n K U := QSing.le_qPerp hUsing
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr (qPerp_antitone hLU (hUperp hrU))
  have hrLflip : K ∙ r ≤ flipOrth σ L :=
    (Submodule.span_singleton_le_iff_mem _ _).mpr (mem_flipOrth.mpr fun y hy => by
      rw [← flipHerm_conj hσ.invol r y, hrperp y (hLU hy), map_zero])
  exact
    { r := r
      mem_U := hrU
      perp := hrperp
      ne_zero := hr0
      not_mem_L := hrnotL
      dim_U := hdimU
      U_eq := hUeqR
      radical := hrad
      L_perp := hrLperp
      L_flip := hrLflip
      self := hrperp r hrU }

private noncomputable def bDataD (hσ : IsUnitaryInvolution σ)
    {L U : Submodule K (Fin n ⊕ Fin n → K)} (R : RadData σ L U)
    (hUsing : QSing U) (hAmem : dFlip σ R.r ∈ K ∙ R.r) : BDiv σ U := by
  classical
  let r := R.r
  have hXex : ∃ X, (quadPlusForm n K).IsLagrangian X ∧ U ≤ X :=
    QuadForm.exists_isLagrangian_le (Φ := quadPlusForm n K) (isLagrangian_stdLag n K)
      ((qSing_iff_isTotallySingular U).mp hUsing)
  let X := Classical.choose hXex
  have hXlag : (quadPlusForm n K).IsLagrangian X := (Classical.choose_spec hXex).1
  have hUX : U ≤ X := (Classical.choose_spec hXex).2
  have hXsing : QSing X := (qSing_iff_isTotallySingular X).mpr hXlag.1
  have hdfliprX : dFlip σ r ∈ X :=
    hUX ((Submodule.span_singleton_le_iff_mem _ _).mpr R.mem_U hAmem)
  let D : Submodule K (Fin n ⊕ Fin n → K) := X ⊓ dFlipSub σ X
  have hDeven : Even (Module.finrank K D) := even_finrank_inf_dFlipSub hσ.invol hXlag
  have hrD : r ∈ D := ⟨hUX R.mem_U, (mem_dFlipSub hσ.invol).mpr hdfliprX⟩
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h] at hrD
    exact R.ne_zero (by simpa using hrD)
  have hDpos : 0 < Module.finrank K D := by
    by_contra h0
    exact hDne (Submodule.finrank_eq_zero.mp (by omega))
  have hD2 : 2 ≤ Module.finrank K D := by
    obtain ⟨k, hk⟩ := hDeven
    omega
  have hDU : D ⊓ U ≤ K ∙ r := by
    intro x hx
    obtain ⟨hxD, hxU⟩ := Submodule.mem_inf.mp hx
    obtain ⟨hxX, hxd⟩ := Submodule.mem_inf.mp hxD
    have hxperp : x ∈ flipOrth σ U := mem_flipOrth.mpr fun y hy => by
      rw [flipHerm]
      exact polar_eq_zero_of_qSing hXsing (hUX hy) ((mem_dFlipSub hσ.invol).mp hxd)
    rw [← R.radical]
    exact ⟨hxU, hxperp⟩
  have hDnotU : ¬ D ≤ U := by
    intro hDU'
    have hle : D ≤ K ∙ r := fun x hx => hDU ⟨hx, hDU' hx⟩
    have hfin : Module.finrank K D ≤ 1 := by
      have hmono := Submodule.finrank_mono hle
      rwa [finrank_span_singleton R.ne_zero] at hmono
    omega
  have hsex : ∃ s, s ∈ D ∧ s ∉ U := by
    by_contra hcon
    push Not at hcon
    exact hDnotU fun x hx => hcon x hx
  let s := Classical.choose hsex
  have hsD : s ∈ D := (Classical.choose_spec hsex).1
  have hsU : s ∉ U := (Classical.choose_spec hsex).2
  have hsX : s ∈ X := (Submodule.mem_inf.mp hsD).1
  have hsd : s ∈ dFlipSub σ X := (Submodule.mem_inf.mp hsD).2
  have hsdX : dFlip σ s ∈ X := (mem_dFlipSub hσ.invol).mp hsd
  exact ⟨X, s, hXsing, hUX, hsU, hsX, hsdX⟩

private structure BW (σ : K ≃+* K) (U : Submodule K (Fin n ⊕ Fin n → K))
    (s : Fin n ⊕ Fin n → K) where
  W : Submodule K (Fin n ⊕ Fin n → K)
  hWdef : W = U ⊔ K ∙ s
  hs0 : s ≠ 0
  hWsing : QSing W
  hdimW : Module.finrank K W = 4

private noncomputable def bDataW
    {L U : Submodule K (Fin n ⊕ Fin n → K)} (R : RadData σ L U)
    (B : BDiv σ U) (hUsing : QSing U) : BW σ U B.s := by
  classical
  let X := B.X
  let s := B.s
  have hXsing := B.hXsing
  have hUX := B.hUX
  have hsU := B.hsU
  have hsX := B.hsX
  have hdimU := R.dim_U
  let W : Submodule K (Fin n ⊕ Fin n → K) := U ⊔ K ∙ s
  have hsW : s ∈ W := Submodule.mem_sup_right (Submodule.mem_span_singleton_self s)
  have hs0 : s ≠ 0 := by
    intro h
    apply hsU
    rw [show B.s = s from rfl, h]
    exact U.zero_mem
  have hWsing : QSing W := by
    have hUt : (quadPlusForm n K).IsTotallySingular U :=
      (qSing_iff_isTotallySingular U).mp hUsing
    have hKst : (quadPlusForm n K).IsTotallySingular (K ∙ s) := by
      refine (quadPlusForm n K).isTotallySingular_span_singleton ?_
      rw [quadPlusForm_Q]
      exact quadPlus_eq_zero_of_qSing hXsing hsX
    have horth : U ≤ (quadPlusForm n K).polar.perp (K ∙ s) := by
      intro u hu
      rw [ReflForm.mem_perp]
      intro x hx
      rw [quadPlusForm_polar, polar_comm]
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hx
      rw [polar_smul_right, polar_eq_zero_of_qSing hXsing (hUX hu) hsX, smul_zero]
    exact (qSing_iff_isTotallySingular W).mpr (hUt.sup hKst horth)
  have hWdim : Module.finrank K W = 4 := by
    dsimp only [W]
    have hdisj : U ⊓ K ∙ s = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxU, hxs⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply hsU
        change s ∈ U
        have h : s = c⁻¹ • (c • s) := (inv_smul_smul₀ hc s).symm
        rw [h]
        exact U.smul_mem _ hxU
    have hd := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ s)
    rw [hdisj, finrank_bot, add_zero, hdimU, finrank_span_singleton hs0] at hd
    omega
  exact ⟨W, rfl, hs0, hWsing, hWdim⟩

private noncomputable def bData (hσ : IsUnitaryInvolution σ)
    {L U : Submodule K (Fin n ⊕ Fin n → K)}
    (hLline : IsFlipLine σ L) (R : RadData σ L U) (B : BDiv σ U)
    (hAmem : dFlip σ R.r ∈ K ∙ R.r) (BW : BW σ U B.s) : BData σ L U R.r := by
  classical
  let X := B.X
  let s := B.s
  have hXsing := B.hXsing
  have hUX := B.hUX
  have hsU := B.hsU
  have hsX := B.hsX
  have hsdX := B.hsdX
  let r := R.r
  have hrU := R.mem_U
  have hrperp := R.perp
  have hr0 := R.ne_zero
  have hUeqR := R.U_eq
  have hLU : L ≤ U := by
    rw [hUeqR]
    exact le_sup_left
  have hdfliprX : dFlip σ r ∈ X :=
    hUX ((Submodule.span_singleton_le_iff_mem _ _).mpr hrU hAmem)
  let W := BW.W
  have hWdef : W = U ⊔ K ∙ s := BW.hWdef
  have hsW : s ∈ W := by
    rw [hWdef]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self s)
  have hUW : U ≤ W := by
    rw [hWdef]
    exact le_sup_left
  have hs0 : s ≠ 0 := BW.hs0
  have hWsing : QSing W := BW.hWsing
  have hWdim : Module.finrank K W = 4 := BW.hdimW
  let Y : Submodule K (Fin n ⊕ Fin n → K) := K ∙ r ⊔ K ∙ s
  have hYW : Y ≤ W :=
    sup_le (le_trans ((Submodule.span_singleton_le_iff_mem _ _).mpr hrU) hUW)
      ((Submodule.span_singleton_le_iff_mem _ _).mpr hsW)
  have hYdim : Module.finrank K Y = 2 := by
    dsimp only [Y]
    have hdisj : K ∙ r ⊓ K ∙ s = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxr, hxs⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxr
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply hsU
        change s ∈ U
        obtain ⟨d, hd⟩ := Submodule.mem_span_singleton.mp hxs
        have hd0 : d ≠ 0 := by
          rintro rfl
          rw [zero_smul] at hd
          exact hc ((smul_eq_zero.mp hd.symm).resolve_right hr0)
        have hs : s = (d⁻¹ * c) • r := by
          calc s = d⁻¹ • (d • s) := (inv_smul_smul₀ hd0 s).symm
            _ = d⁻¹ • (c • r) := by rw [hd]
            _ = (d⁻¹ * c) • r := by rw [mul_smul]
        rw [hs]
        exact U.smul_mem _ hrU
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ r) (K ∙ s)
    rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hr0,
      finrank_span_singleton hs0] at hd
    omega
  have hsr : flipHerm σ s r = 0 := by
    rw [flipHerm]
    exact polar_eq_zero_of_qSing hXsing hsX hdfliprX
  have hss : flipHerm σ s s = 0 := by
    rw [flipHerm]
    exact polar_eq_zero_of_qSing hXsing hsX hsdX
  have hrFlipW : r ∈ flipOrth σ W := by
    rw [mem_flipOrth]
    intro w' hw'
    have hw'' : w' ∈ U ⊔ K ∙ s := by
      rw [← BW.hWdef]
      exact hw'
    obtain ⟨u', hu', c, hc, rfl⟩ := Submodule.mem_sup.mp hw''
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hc
    have hu'r : flipHerm σ u' r = 0 := by
      rw [← flipHerm_conj hσ.invol r u', hrperp u' hu', map_zero]
    rw [flipHerm_add_left, flipHerm_smul_left, hu'r, hsr, mul_zero, add_zero]
  have hsFlipW : s ∈ flipOrth σ W := by
    rw [mem_flipOrth]
    intro w' hw'
    have hw'' : w' ∈ U ⊔ K ∙ s := by
      rw [← BW.hWdef]
      exact hw'
    obtain ⟨u', hu', c, hc, rfl⟩ := Submodule.mem_sup.mp hw''
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.mp hc
    rw [flipHerm_add_left, flipHerm_smul_left]
    have h1 : flipHerm σ u' s = 0 := by
      rw [flipHerm]
      exact polar_eq_zero_of_qSing hXsing (hUX hu') hsdX
    rw [h1, hss, mul_zero, add_zero]
  have hYflip : Y ≤ flipOrth σ W := by
    intro y hy
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha'
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb'
    rw [mem_flipOrth]
    intro w' hw'
    rw [flipHerm_add_right, flipHerm_smul_right, flipHerm_smul_right]
    rw [(mem_flipOrth.mp hrFlipW) w' hw', (mem_flipOrth.mp hsFlipW) w' hw']
    simp
  have hYiso : ∀ y ∈ Y, flipHerm σ y y = 0 := by
    intro y hy
    obtain ⟨a', ha', b', hb', rfl⟩ := Submodule.mem_sup.mp hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha'
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hb'
    have hrs : flipHerm σ r s = 0 := by
      rw [← flipHerm_conj hσ.invol s r, hsr, map_zero]
    have hrr : flipHerm σ r r = 0 := R.self
    simp only [flipHerm_add_left, flipHerm_add_right, flipHerm_smul_left,
      flipHerm_smul_right, hrr, hrs, hsr, hss, mul_zero, add_zero]
  have hWLY : W = L ⊔ Y := by
    calc W = U ⊔ K ∙ s := hWdef
      _ = (L ⊔ K ∙ r) ⊔ K ∙ s := congrArg (fun X => X ⊔ K ∙ s) hUeqR
      _ = L ⊔ (K ∙ r ⊔ K ∙ s) := sup_assoc L (K ∙ r) (K ∙ s)
      _ = L ⊔ Y := by rw [show Y = K ∙ r ⊔ K ∙ s from rfl]
  have hWrad : W ⊓ flipOrth σ W = Y := by
    apply le_antisymm
    · intro x hx
      obtain ⟨hxW, hxperp⟩ := Submodule.mem_inf.mp hx
      rw [hWLY] at hxW
      obtain ⟨l, hl, y, hy, rfl⟩ := Submodule.mem_sup.mp hxW
      have hlperp : l ∈ flipOrth σ W := by
        have h1 : l + y ∈ flipOrth σ W := hxperp
        have h2 : y ∈ flipOrth σ W := hYflip hy
        have := (flipOrth σ W).sub_mem h1 h2
        simpa using this
      have hlperpL : l ∈ flipOrth σ L := mem_flipOrth.mpr fun z hz =>
        (mem_flipOrth.mp hlperp) z (hUW (hLU hz))
      have hl0 : l = 0 := by
        have hmem : l ∈ L ⊓ flipOrth σ L := ⟨hl, hlperpL⟩
        rw [inf_flipOrth_eq_bot hσ.invol hLline.1] at hmem
        simpa using hmem
      rw [hl0, zero_add]
      exact hy
    · exact le_inf hYW hYflip
  have hsKr : s ∉ K ∙ r := fun h => hsU ((Submodule.span_singleton_le_iff_mem _ _).mpr hrU h)
  exact ⟨W, Y, s, rfl, hUW, hYW, hWdim, hYdim, hWsing, hYflip, hYiso, hWrad, hWLY, hsU, hsKr⟩

private noncomputable def bCoords (hσ : IsUnitaryInvolution σ)
    {a b c : FlipPt σ n} (hbc : (flipGraph σ n).Adj b c)
    (hca : (flipGraph σ n).Adj c a)
    {L U : Submodule K (Fin n ⊕ Fin n → K)} (hLdef : L = a.1 ⊔ b.1)
    (hLU : L ≤ U) (hcU : c.1 ≤ U) (hcL : ¬ c.1 ≤ L) (R : RadData σ L U) :
    BCoords σ a b c L R.r := by
  classical
  let r := R.r
  have hrU : r ∈ U := R.mem_U
  have hrperp : ∀ v ∈ U, flipHerm σ r v = 0 := R.perp
  have hr0 : r ≠ 0 := R.ne_zero
  have hUeqR : U = L ⊔ K ∙ r := R.U_eq
  have haL : a.1 ≤ L := by
    rw [hLdef]
    exact le_sup_left
  have hbL : b.1 ≤ L := by
    rw [hLdef]
    exact le_sup_right
  have hUbc : b.1 ⊔ c.1 ≤ U := sup_le (le_trans hbL hLU) hcU
  have hUac : a.1 ⊔ c.1 ≤ U := sup_le (le_trans haL hLU) hcU
  have ha_ne : a.1 ≠ ⊥ := by
    intro h
    have h1 := finrank_of_flipPt a.2
    rw [h, finrank_bot] at h1
    omega
  have hb_ne : b.1 ≠ ⊥ := by
    intro h
    have h1 := finrank_of_flipPt b.2
    rw [h, finrank_bot] at h1
    omega
  have hc_ne : c.1 ≠ ⊥ := by
    intro h
    have h1 := finrank_of_flipPt c.2
    rw [h, finrank_bot] at h1
    omega
  have huaex : ∃ u, u ∈ a.1 ∧ u ≠ 0 := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot ha_ne
    exact ⟨u, hu, hu0⟩
  let u := Classical.choose huaex
  have hua : u ∈ a.1 := (Classical.choose_spec huaex).1
  have hu0 : u ≠ 0 := (Classical.choose_spec huaex).2
  have hvbe : ∃ v, v ∈ b.1 ∧ v ≠ 0 := by
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hb_ne
    exact ⟨v, hv, hv0⟩
  let v := Classical.choose hvbe
  have hvb : v ∈ b.1 := (Classical.choose_spec hvbe).1
  have hv0 : v ≠ 0 := (Classical.choose_spec hvbe).2
  have hwce : ∃ w, w ∈ c.1 ∧ w ≠ 0 := by
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hc_ne
    exact ⟨w, hw, hw0⟩
  let w := Classical.choose hwce
  have hwc : w ∈ c.1 := (Classical.choose_spec hwce).1
  have hw0 : w ≠ 0 := (Classical.choose_spec hwce).2
  have haK : a.1 = K ∙ u := (Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hua)
    (by rw [finrank_span_singleton hu0, finrank_of_flipPt a.2])).symm
  have hbK : b.1 = K ∙ v := (Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hvb)
    (by rw [finrank_span_singleton hv0, finrank_of_flipPt b.2])).symm
  have hcK : c.1 = K ∙ w := (Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hwc)
    (by rw [finrank_span_singleton hw0, finrank_of_flipPt c.2])).symm
  have hwL : w ∉ L := by
    intro hw
    apply hcL
    rw [hcK]
    exact (Submodule.span_singleton_le_iff_mem _ _).mpr hw
  have hwU : w ∈ U := hcU hwc
  rw [hUeqR] at hwU
  choose l₀ hl₀ xr hxr hwl using Submodule.mem_sup.mp hwU
  choose δ hδ using Submodule.mem_span_singleton.mp hxr
  have hwl' : l₀ + δ • r = w := by
    rw [hδ]
    exact hwl
  have hδ0 : δ ≠ 0 := by
    intro hδ0
    rw [hδ0, zero_smul, add_zero] at hwl'
    exact hwL (hwl' ▸ hl₀)
  rw [hLdef] at hl₀
  choose lu hlu lv hlv hluv using Submodule.mem_sup.mp hl₀
  rw [haK] at hlu
  choose α hα using Submodule.mem_span_singleton.mp hlu
  rw [hbK] at hlv
  choose β hβ using Submodule.mem_span_singleton.mp hlv
  have hwdecomp : w = α • u + β • v + δ • r := by
    rw [← hwl', ← hluv, ← hα, ← hβ]
  have hα0 : α ≠ 0 := by
    intro hα
    have hwac : w = β • v + δ • r := by
      rw [hwdecomp, hα, zero_smul, zero_add]
    have hrbc : r ∈ b.1 ⊔ c.1 := by
      have hwr : w - β • v = δ • r := by
        rw [hwac]
        abel
      have hrw : r = δ⁻¹ • (w - β • v) := by
        rw [hwr, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
      rw [hrw]
      refine (b.1 ⊔ c.1).smul_mem _ ?_
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hwc)
        (Submodule.smul_mem _ _ (Submodule.mem_sup_left (by
          rw [hbK]
          exact Submodule.mem_span_singleton_self v)))
    have hrflipbc : r ∈ flipOrth σ (b.1 ⊔ c.1) := mem_flipOrth.mpr fun z hz => by
      rw [← flipHerm_conj hσ.invol r z, hrperp z (hUbc hz), map_zero]
    have hmem : r ∈ (b.1 ⊔ c.1) ⊓ flipOrth σ (b.1 ⊔ c.1) := ⟨hrbc, hrflipbc⟩
    rw [inf_flipOrth_eq_bot hσ.invol (hbc.isFlipLine b.2 c.2).1] at hmem
    exact hr0 (by simpa using hmem)
  have hβ0 : β ≠ 0 := by
    intro hβ
    have hwac : w = α • u + δ • r := by
      rw [hwdecomp, hβ, zero_smul, add_zero]
    have hrac : r ∈ a.1 ⊔ c.1 := by
      have hwr : w - α • u = δ • r := by
        rw [hwac]
        abel
      have hrw : r = δ⁻¹ • (w - α • u) := by
        rw [hwr, smul_smul, inv_mul_cancel₀ hδ0, one_smul]
      rw [hrw]
      refine (a.1 ⊔ c.1).smul_mem _ ?_
      exact Submodule.sub_mem _ (Submodule.mem_sup_right hwc)
        (Submodule.smul_mem _ _ (Submodule.mem_sup_left (by
          rw [haK]
          exact Submodule.mem_span_singleton_self u)))
    have hrflipac : r ∈ flipOrth σ (a.1 ⊔ c.1) := mem_flipOrth.mpr fun z hz => by
      rw [← flipHerm_conj hσ.invol r z, hrperp z (hUac hz), map_zero]
    have hmem : r ∈ (a.1 ⊔ c.1) ⊓ flipOrth σ (a.1 ⊔ c.1) := ⟨hrac, hrflipac⟩
    rw [inf_flipOrth_eq_bot hσ.invol (hca.symm.isFlipLine a.2 c.2).1] at hmem
    exact hr0 (by simpa using hmem)
  exact
    { u := u, v := v, w := w, α := α, β := β, δ := δ,
      hua := hua, hvb := hvb, hwc := hwc,
      hu0 := hu0, hv0 := hv0, hw0 := hw0,
      haK := haK, hbK := hbK, hcK := hcK, hwL := hwL,
      hδ0 := hδ0, hα0 := hα0, hβ0 := hβ0, hwdecomp := hwdecomp }

private noncomputable def bZ (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    {a b c : FlipPt σ n} {L : Submodule K (Fin n ⊕ Fin n → K)}
    {r : Fin n ⊕ Fin n → K} (hLline : IsFlipLine σ L) (hLdef : L = a.1 ⊔ b.1)
    (C : BCoords σ a b c L r) : BZ σ a b c L r C := by
  classical
  have hptn : 3 < q ^ 2 - q := by
    have hle : q ≤ q ^ 2 := by
      have h := le_mul_of_one_le_right (Nat.zero_le q) (by omega : 1 ≤ q)
      simpa [pow_two] using h
    have hcast : ((q ^ 2 - q : ℕ) : ℤ) = (q : ℤ) ^ 2 - q := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    have h3' : (3 : ℤ) < (q : ℤ) ^ 2 - q := by
      have h4 : (4 : ℤ) ≤ q := by exact_mod_cast hq
      nlinarith
    rw [← hcast] at h3'
    exact_mod_cast h3'
  have hbadfin : ({K ∙ C.u, K ∙ C.v, K ∙ (C.u + (C.β / C.α) • C.v)} :
      Set (Submodule K (Fin n ⊕ Fin n → K))).Finite :=
    ((Set.finite_singleton _).insert _).insert _
  have hbadn : ({K ∙ C.u, K ∙ C.v, K ∙ (C.u + (C.β / C.α) • C.v)} :
      Set (Submodule K (Fin n ⊕ Fin n → K))).ncard ≤ 3 := by
    have h1 := Set.ncard_insert_le (K ∙ C.u) ({K ∙ C.v, K ∙ (C.u + (C.β / C.α) • C.v)} :
      Set (Submodule K (Fin n ⊕ Fin n → K)))
    have h2 := Set.ncard_insert_le (K ∙ C.v) ({K ∙ (C.u + (C.β / C.α) • C.v)} :
      Set (Submodule K (Fin n ⊕ Fin n → K)))
    rw [Set.ncard_singleton] at h2
    omega
  have hltz : ({K ∙ C.u, K ∙ C.v, K ∙ (C.u + (C.β / C.α) • C.v)} :
      Set (Submodule K (Fin n ⊕ Fin n → K))).ncard < (ptsOn σ L).ncard := by
    rw [ncard_ptsOn hσ hK hLline]
    omega
  choose z hzpts hznot using Set.exists_mem_notMem_of_ncard_lt_ncard hltz hbadfin
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hznot
  obtain ⟨hzu, hzv, hzθ⟩ := hznot
  obtain ⟨hzp, hzL⟩ := hzpts
  have hz_ne : z ≠ ⊥ := by
    intro h
    have h1 := finrank_of_flipPt hzp
    rw [h, finrank_bot] at h1
    omega
  choose z₀ hz₀z hz₀0 using Submodule.exists_mem_ne_zero_of_ne_bot hz_ne
  have hzK : z = K ∙ z₀ := (Submodule.eq_of_le_of_finrank_eq
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hz₀z)
    (by rw [finrank_span_singleton hz₀0, finrank_of_flipPt hzp])).symm
  have hz₀L : z₀ ∈ L := hzL hz₀z
  rw [hLdef] at hz₀L
  choose zu hzu' zv hzv' hzuv using Submodule.mem_sup.mp hz₀L
  rw [C.haK] at hzu'
  choose c₁ hc₁ using Submodule.mem_span_singleton.mp hzu'
  rw [C.hbK] at hzv'
  choose c₂ hc₂ using Submodule.mem_span_singleton.mp hzv'
  have hzuv' : c₁ • C.u + c₂ • C.v = z₀ := by
    rw [← hc₁, ← hc₂] at hzuv
    exact hzuv
  have hc₁0 : c₁ ≠ 0 := by
    intro hc
    have hc₂0 : c₂ ≠ 0 := by
      intro hc2
      rw [hc, hc2, zero_smul, zero_smul, add_zero] at hzuv'
      exact hz₀0 hzuv'.symm
    apply hzv
    rw [hzK]
    have hz0 : z₀ = c₂ • C.v := by
      rw [← hzuv', hc, zero_smul, zero_add]
    rw [hz0, Submodule.span_singleton_smul_eq (IsUnit.mk0 c₂ hc₂0)]
  have hc₂0 : c₂ ≠ 0 := by
    intro hc
    have hc₁' : c₁ ≠ 0 := by
      intro hc1
      rw [hc, hc1, zero_smul, zero_smul, add_zero] at hzuv'
      exact hz₀0 hzuv'.symm
    apply hzu
    rw [hzK]
    have hz0 : z₀ = c₁ • C.u := by
      rw [← hzuv', hc, zero_smul, add_zero]
    rw [hz0, Submodule.span_singleton_smul_eq (IsUnit.mk0 c₁ hc₁')]
  let u := C.u
  let v := C.v
  let θ : K := c₂ / c₁
  have hθ0 : θ ≠ 0 := div_ne_zero hc₂0 hc₁0
  have hz0eq : z₀ = c₁ • (C.u + θ • C.v) := by
    rw [smul_add, smul_smul, mul_div_cancel₀ c₂ hc₁0]
    exact hzuv'.symm
  have huL : u ∈ L := hLdef ▸ (show u ∈ a.1 ⊔ b.1 from Submodule.mem_sup_left C.hua)
  have hvL : v ∈ L := hLdef ▸ (show v ∈ a.1 ⊔ b.1 from Submodule.mem_sup_right C.hvb)
  have hzvecL : u + θ • v ∈ L := L.add_mem huL (L.smul_mem θ hvL)
  have hzKvec : z = K ∙ (C.u + θ • C.v) := by
    calc z = K ∙ z₀ := hzK
      _ = K ∙ (c₁ • (C.u + θ • C.v)) := by rw [hz0eq]
      _ = K ∙ (C.u + θ • C.v) :=
        Submodule.span_singleton_smul_eq (IsUnit.mk0 c₁ hc₁0) (C.u + θ • C.v)
  have hθβ : θ ≠ C.β / C.α := by
    intro h
    exact hzθ (by rw [hzKvec, h])
  have hz₀aniso : flipHerm σ z₀ z₀ ≠ 0 := by
    have hsub : IsFlipflopSub σ (K ∙ z₀) := by
      rw [← hzK]
      exact isFlipflopSub_of_flipPt hzp
    exact (isFlipflopSub_span_singleton_iff hz₀0).mp hsub |>.2
  have hzvecaniso : flipHerm σ (C.u + θ • C.v) (C.u + θ • C.v) ≠ 0 := by
    intro h0
    apply hz₀aniso
    rw [hz0eq, flipHerm_smul_left, flipHerm_smul_right, h0, mul_zero, mul_zero]
  exact
    { θ := θ, zvec := C.u + θ • C.v, hθ0 := hθ0, hθβ := hθβ,
      hzvecL := hzvecL, hzvecdef := rfl, hzvecaniso := hzvecaniso }

private noncomputable def bLam (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    {a b c : FlipPt σ n} {L U : Submodule K (Fin n ⊕ Fin n → K)}
    (R : RadData σ L U) (S : BData σ L U R.r)
    (C : BCoords σ a b c L R.r) (Z : BZ σ a b c L R.r C)
    (hAmem : dFlip σ R.r ∈ K ∙ R.r) : BLam σ L U R.r S C Z := by
  classical
  let Bset : Set K := {μ : K | dFlip σ (S.s + μ • R.r) ∈ K ∙ (S.s + μ • R.r)}
  have hBcard : Bset.ncard ≤ q := ncard_inv_le hσ hK S.hsKr R.ne_zero hAmem
  let μ₂ : K := C.δ / C.α
  let μ₃ : K := Z.θ * C.δ / C.β
  let badSet : Set K :=
    Bset ∪ (fun x : K => x + μ₂) '' Bset ∪ (fun x : K => x + μ₃) '' Bset
  have hshift2 : ((fun x : K => x + μ₂) '' Bset).ncard ≤ q := by
    rw [Set.ncard_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hBcard
  have hshift3 : ((fun x : K => x + μ₃) '' Bset).ncard ≤ q := by
    rw [Set.ncard_image_of_injective _ (fun a b h => add_right_cancel h)]
    exact hBcard
  have hbadSetcard : badSet.ncard ≤ 3 * q := by
    have h1 : badSet.ncard ≤ (Bset ∪ (fun x : K => x + μ₂) '' Bset).ncard +
        ((fun x : K => x + μ₃) '' Bset).ncard :=
      Set.ncard_union_le (Bset ∪ (fun x : K => x + μ₂) '' Bset)
        ((fun x : K => x + μ₃) '' Bset)
    have h2 : (Bset ∪ (fun x : K => x + μ₂) '' Bset).ncard ≤
        Bset.ncard + ((fun x : K => x + μ₂) '' Bset).ncard :=
      Set.ncard_union_le Bset ((fun x : K => x + μ₂) '' Bset)
    have h23 : (Bset ∪ (fun x : K => x + μ₂) '' Bset).ncard ≤ q + q :=
      le_trans h2 (Nat.add_le_add hBcard hshift2)
    have hall : badSet.ncard ≤ (q + q) + q :=
      le_trans h1 (Nat.add_le_add h23 hshift3)
    omega
  have huniv : (Set.univ : Set K).ncard = q ^ 2 := by
    rw [Set.ncard_univ, hK]
  have h3q : 3 * q < q ^ 2 := by nlinarith [hq]
  have hltSet : badSet.ncard < (Set.univ : Set K).ncard := by
    rw [huniv]
    exact lt_of_le_of_lt hbadSetcard h3q
  choose lam hlamnot using
    Set.exists_mem_notMem_of_ncard_lt_ncard hltSet (Set.toFinite badSet)
  have hlamB : lam ∉ Bset := by
    intro h
    exact hlamnot.2 (by
      dsimp only [badSet]
      exact Or.inl (Or.inl h))
  have hlam2 : lam - μ₂ ∉ Bset := by
    intro h
    exact hlamnot.2 (by
      dsimp only [badSet]
      exact Or.inl (Or.inr ⟨lam - μ₂, h, sub_add_cancel lam μ₂⟩))
  have hlam3 : lam - μ₃ ∉ Bset := by
    intro h
    exact hlamnot.2 (by
      dsimp only [badSet]
      exact Or.inr ⟨lam - μ₃, h, sub_add_cancel lam μ₃⟩)
  exact
    { lam := lam, μ₂ := μ₂, μ₃ := μ₃, hμ₂ := rfl, hμ₃ := rfl,
      hlamB := hlamB, hlam2 := hlam2, hlam3 := hlam3 }

private noncomputable def bApex (hσ : IsUnitaryInvolution σ)
    {a b c : FlipPt σ n} {L U : Submodule K (Fin n ⊕ Fin n → K)}
    (R : RadData σ L U) (S : BData σ L U R.r)
    (C : BCoords σ a b c L R.r) (Z : BZ σ a b c L R.r C)
    (Λ : BLam σ L U R.r S C Z) (hLU : L ≤ U) :
    BApex σ L U R.r S C Z Λ := by
  classical
  let s := S.s
  let y := s + Λ.lam • R.r
  let y₂ := s + (Λ.lam - Λ.μ₂) • R.r
  let y₃ := s + (Λ.lam - Λ.μ₃) • R.r
  let zvec := C.u + Z.θ • C.v
  let t := zvec + y
  have hyY : y ∈ S.Y := by
    rw [S.hYdef]
    dsimp only [y]
    rw [add_comm]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self R.r)))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self s))
  have hyU : y ∉ U := by
    intro h
    apply S.hsU
    have h2 : Λ.lam • R.r ∈ U := U.smul_mem _ R.mem_U
    have h3 := U.sub_mem h h2
    simpa only [y, s, add_sub_cancel_right] using h3
  have hy2Y : y₂ ∈ S.Y := by
    rw [S.hYdef]
    dsimp only [y₂]
    rw [add_comm]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self R.r)))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self s))
  have hy2U : y₂ ∉ U := by
    intro h
    apply S.hsU
    have h2 : (Λ.lam - Λ.μ₂) • R.r ∈ U := U.smul_mem _ R.mem_U
    have h3 := U.sub_mem h h2
    simpa only [y₂, s, add_sub_cancel_right] using h3
  have hy3Y : y₃ ∈ S.Y := by
    rw [S.hYdef]
    dsimp only [y₃]
    rw [add_comm]
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self R.r)))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self s))
  have hy3U : y₃ ∉ U := by
    intro h
    apply S.hsU
    have h2 : (Λ.lam - Λ.μ₃) • R.r ∈ U := U.smul_mem _ R.mem_U
    have h3 := U.sub_mem h h2
    simpa only [y₃, s, add_sub_cancel_right] using h3
  have hy2eq : y₂ = y - Λ.μ₂ • R.r := by
    dsimp only [y₂, y]
    rw [sub_smul]
    abel
  have hy3eq : y₃ = y - Λ.μ₃ • R.r := by
    dsimp only [y₃, y]
    rw [sub_smul]
    abel
  have hzvec_eq : zvec = Z.zvec := by
    dsimp only [zvec]
    rw [← Z.hzvecdef]
  have hzvecL : zvec ∈ L := hzvec_eq ▸ Z.hzvecL
  have hyL : y ∉ L := fun h => hyU (hLU h)
  have htL : t ∉ L := by
    intro h
    apply hyL
    have h4 := L.sub_mem h hzvecL
    simpa only [t, add_sub_cancel_left] using h4
  have htW : t ∈ S.W := by
    have hzU : zvec ∈ U := hLU hzvecL
    exact S.W.add_mem (S.hUW hzU) (S.hYW hyY)
  have htq : quadPlus n K t = 0 := quadPlus_eq_zero_of_qSing S.hWsing htW
  have ht0 : t ≠ 0 := fun h => htL (h ▸ L.zero_mem)
  have htz : flipHerm σ t t = flipHerm σ zvec zvec := by
    have h1 : flipHerm σ zvec y = 0 :=
      (mem_flipOrth.mp (S.hYflip hyY)) zvec (S.hUW (hLU hzvecL))
    have h2 : flipHerm σ y zvec = 0 := by
      rw [← flipHerm_conj hσ.invol zvec y, h1, map_zero]
    dsimp only [t]
    simp only [flipHerm_add_left, flipHerm_add_right, h1, h2, S.hYiso y hyY,
      add_zero]
  have hth : flipHerm σ t t ≠ 0 := by
    rw [htz, hzvec_eq]
    exact Z.hzvecaniso
  have htpt : IsFlipflopPt σ (K ∙ t) :=
    (isFlipflopPt_span_singleton_iff ht0).mpr ⟨htq, hth⟩
  have htmem_y : t ∈ L ⊔ K ∙ y := by
    dsimp only [t]
    exact Submodule.add_mem _ (Submodule.mem_sup_left hzvecL)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y))
  have hzbc : C.α⁻¹ • C.w + (Z.θ - C.β * C.α⁻¹) • C.v = zvec + Λ.μ₂ • R.r := by
    rw [Λ.hμ₂, C.hwdecomp]
    dsimp only [zvec]
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul, inv_mul_cancel₀ C.hα0]
    module
  have ht_eq_bc : t = (C.α⁻¹ • C.w + (Z.θ - C.β * C.α⁻¹) • C.v) + y₂ := by
    calc t = zvec + y := rfl
      _ = (zvec + Λ.μ₂ • R.r) + y₂ := by rw [hy2eq]; abel
      _ = (C.α⁻¹ • C.w + (Z.θ - C.β * C.α⁻¹) • C.v) + y₂ := by rw [hzbc]
  have htmem_bc : t ∈ (b.1 ⊔ c.1) ⊔ K ∙ y₂ := by
    rw [ht_eq_bc]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₂))
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right C.hwc))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left C.hvb))
  have hkey : t - (Z.θ / C.β) • C.w - y₃ = (1 - Z.θ * C.α / C.β) • C.u := by
    rw [hy3eq, Λ.hμ₃, C.hwdecomp]
    dsimp only [t, zvec, y]
    rw [smul_add, smul_add, smul_smul, smul_smul, smul_smul,
      div_mul_cancel₀ Z.θ C.hβ0, div_mul_eq_mul_div, div_mul_eq_mul_div]
    module
  have ht_eq_ca : t = ((Z.θ / C.β) • C.w + (1 - Z.θ * C.α / C.β) • C.u) + y₃ := by
    calc t = (t - (Z.θ / C.β) • C.w - y₃) + (Z.θ / C.β) • C.w + y₃ := by abel
      _ = (1 - Z.θ * C.α / C.β) • C.u + (Z.θ / C.β) • C.w + y₃ := by rw [hkey]
      _ = ((Z.θ / C.β) • C.w + (1 - Z.θ * C.α / C.β) • C.u) + y₃ := by abel
  have htmem_ca : t ∈ (c.1 ⊔ a.1) ⊔ K ∙ y₃ := by
    rw [ht_eq_ca]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self y₃))
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.mem_sup_left C.hwc))
      (Submodule.smul_mem _ _ (Submodule.mem_sup_right C.hua))
  exact
    { y := y, y₂ := y₂, y₃ := y₃, t := t,
      hyY := hyY, hyU := hyU, hy2Y := hy2Y, hy2U := hy2U, hy3Y := hy3Y, hy3U := hy3U,
      hydef := rfl, hy2def := rfl, hy3def := rfl,
      htdef := by dsimp only [t]; rw [hzvec_eq],
      htL := htL, htW := htW, htq := htq, ht0 := ht0, hth := hth, htpt := htpt,
      htmem_y := htmem_y, htmem_bc := htmem_bc, htmem_ca := htmem_ca, hkey := hkey }

private theorem bLineAB (hσ : IsUnitaryInvolution σ)
    {a b c : FlipPt σ n} {L U : Submodule K (Fin n ⊕ Fin n → K)}
    {r : Fin n ⊕ Fin n → K} (hLdef : L = a.1 ⊔ b.1) (hLU : L ≤ U)
    (S : BData σ L U r) (C : BCoords σ a b c L r) (Z : BZ σ a b c L r C)
    (Λ : BLam σ L U r S C Z) (P : BApex σ L U r S C Z Λ)
    (tpt : FlipPt σ n) (htpt : tpt.1 = K ∙ P.t) :
    (flipGraph σ n).Adj a tpt := by
  let W := S.W
  let Y := S.Y
  let u := C.u
  let v := C.v
  let t := P.t
  let y := P.y
  let θ := Z.θ
  let zvec := Z.zvec
  have hUW : U ≤ W := S.hUW
  have hYW : Y ≤ W := S.hYW
  have hWsing : QSing W := S.hWsing
  have hYflip : Y ≤ flipOrth σ W := S.hYflip
  have hWrad : W ⊓ flipOrth σ W = Y := S.hWrad
  have hWLY : W = L ⊔ Y := S.hWLY
  have hYdim : Module.finrank K Y = 2 := S.hdimY
  have hWdim : Module.finrank K W = 4 := S.hdimW
  have hua : u ∈ a.1 := C.hua
  have huaL : a.1 ≤ L := by
    rw [hLdef]
    exact le_sup_left
  have haU : a.1 ≤ U := le_trans huaL hLU
  have haK : a.1 = K ∙ u := C.haK
  have hbK : b.1 = K ∙ v := C.hbK
  have hu0 : u ≠ 0 := C.hu0
  have ht0 : t ≠ 0 := P.ht0
  have htW : t ∈ W := P.htW
  have htL : t ∉ L := P.htL
  have hyY : y ∈ Y := P.hyY
  have htdef : t = zvec + y := P.htdef
  have hzvecdef : zvec = u + θ • v := Z.hzvecdef
  have hθ0 : θ ≠ 0 := Z.hθ0
  have hAabW : K ∙ u ⊔ K ∙ t ≤ W :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hUW (haU hua)))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr htW)
  have hu_mem : u ∈ (K ∙ u ⊔ K ∙ t) ⊔ Y :=
    Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_span_singleton_self u))
  have hv_eq : v = θ⁻¹ • (t - u - y) := by
    rw [htdef, hzvecdef]
    rw [show u + θ • v + y - u - y = θ • v by abel]
    rw [smul_smul, inv_mul_cancel₀ hθ0, one_smul]
  have hv_mem : v ∈ (K ∙ u ⊔ K ∙ t) ⊔ Y := by
    rw [hv_eq]
    refine ((K ∙ u ⊔ K ∙ t) ⊔ Y).smul_mem _ ?_
    exact Submodule.sub_mem _ (Submodule.sub_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self t)))
      (Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self u))))
      (Submodule.mem_sup_right hyY)
  have hLmem_ab : L ≤ (K ∙ u ⊔ K ∙ t) ⊔ Y := by
    intro z hz
    rw [hLdef] at hz
    obtain ⟨zu, hzu, zv, hzv, rfl⟩ := Submodule.mem_sup.mp hz
    rw [haK] at hzu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzu
    rw [hbK] at hzv
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hzv
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu_mem)
      (Submodule.smul_mem _ _ hv_mem)
  have hAabY : K ∙ u ⊔ K ∙ t ⊔ Y = W := by
    apply le_antisymm
    · exact sup_le hAabW hYW
    · rw [hWLY]
      exact sup_le hLmem_ab le_sup_right
  have htu : t ∉ K ∙ u := by
    intro h
    apply htL
    have huL : u ∈ L := huaL hua
    exact ((Submodule.span_singleton_le_iff_mem _ _).mpr huL) h
  have hdimAab : Module.finrank K ↥(K ∙ u ⊔ K ∙ t) = 2 := by
    have hdisj : K ∙ u ⊓ K ∙ t = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxu, hxt⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxu
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply htu
        have hu : u = c⁻¹ • (c • u) := (inv_smul_smul₀ hc u).symm
        have hxu' : u ∈ K ∙ t := by
          rw [hu]
          exact (K ∙ t).smul_mem _ hxt
        have hle : K ∙ u ≤ K ∙ t :=
          (Submodule.span_singleton_le_iff_mem _ _).mpr hxu'
        have hKeq : K ∙ u = K ∙ t := Submodule.eq_of_le_of_finrank_eq hle
          (by rw [finrank_span_singleton hu0, finrank_span_singleton ht0])
        rw [hKeq]
        exact Submodule.mem_span_singleton_self t
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ u) (K ∙ t)
    rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hu0,
      finrank_span_singleton ht0] at hd
    omega
  have hAabflip : IsFlipflopSub σ (K ∙ u ⊔ K ∙ t) :=
    isFlipflopSub_compl_of_WY hσ.invol hWsing hYW hYflip (le_of_eq hWrad) hAabW hAabY
      hdimAab hYdim hWdim
  have hat : (flipGraph σ n).Adj a tpt := by
    refine ⟨?_, ?_⟩
    · intro h
      apply htL
      have hta : t ∈ a.1 := by
        rw [h, htpt]
        exact Submodule.mem_span_singleton_self t
      exact huaL hta
    · rw [haK, htpt]
      exact hAabflip
  exact hat

private theorem bLineBC (hσ : IsUnitaryInvolution σ)
    {a b c : FlipPt σ n} {L U : Submodule K (Fin n ⊕ Fin n → K)}
    {r : Fin n ⊕ Fin n → K} (hLdef : L = a.1 ⊔ b.1) (hLU : L ≤ U)
    (S : BData σ L U r) (C : BCoords σ a b c L r) (Z : BZ σ a b c L r C)
    (Λ : BLam σ L U r S C Z) (P : BApex σ L U r S C Z Λ)
    (tpt : FlipPt σ n) (htpt : tpt.1 = K ∙ P.t) :
    (flipGraph σ n).Adj b tpt := by
  let W := S.W
  let Y := S.Y
  let u := C.u
  let v := C.v
  let t := P.t
  let y := P.y
  let θ := Z.θ
  let zvec := Z.zvec
  have hUW : U ≤ W := S.hUW
  have hYW : Y ≤ W := S.hYW
  have hWsing : QSing W := S.hWsing
  have hYflip : Y ≤ flipOrth σ W := S.hYflip
  have hWrad : W ⊓ flipOrth σ W = Y := S.hWrad
  have hWLY : W = L ⊔ Y := S.hWLY
  have hYdim : Module.finrank K Y = 2 := S.hdimY
  have hWdim : Module.finrank K W = 4 := S.hdimW
  have hvb : v ∈ b.1 := C.hvb
  have hbL : b.1 ≤ L := by
    rw [hLdef]
    exact le_sup_right
  have hbU : b.1 ≤ U := le_trans hbL hLU
  have hbK : b.1 = K ∙ v := C.hbK
  have haK : a.1 = K ∙ u := C.haK
  have hv0 : v ≠ 0 := C.hv0
  have ht0 : t ≠ 0 := P.ht0
  have htW : t ∈ W := P.htW
  have htL : t ∉ L := P.htL
  have hyY : y ∈ Y := P.hyY
  have htdef : t = zvec + y := P.htdef
  have hzvecdef : zvec = u + θ • v := Z.hzvecdef
  have hAabW' : K ∙ v ⊔ K ∙ t ≤ W :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hUW (hbU hvb)))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr htW)
  have hv_mem' : v ∈ (K ∙ v ⊔ K ∙ t) ⊔ Y :=
    Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_span_singleton_self v))
  have hu_eq' : u = t - θ • v - y := by
    rw [htdef, hzvecdef]
    abel
  have hu_mem' : u ∈ (K ∙ v ⊔ K ∙ t) ⊔ Y := by
    rw [hu_eq']
    refine ((K ∙ v ⊔ K ∙ t) ⊔ Y).sub_mem (((K ∙ v ⊔ K ∙ t) ⊔ Y).sub_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self t))
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)))
    · exact Submodule.mem_sup_right hyY
  have hLmem_bc : L ≤ (K ∙ v ⊔ K ∙ t) ⊔ Y := by
    intro z hz
    rw [hLdef] at hz
    obtain ⟨zu, hzu, zv, hzv, rfl⟩ := Submodule.mem_sup.mp hz
    rw [haK] at hzu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzu
    rw [hbK] at hzv
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hzv
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu_mem')
      (Submodule.smul_mem _ _ hv_mem')
  have hAbcY : K ∙ v ⊔ K ∙ t ⊔ Y = W := by
    apply le_antisymm
    · exact sup_le hAabW' hYW
    · rw [hWLY]
      exact sup_le hLmem_bc le_sup_right
  have htv : t ∉ K ∙ v := by
    intro h
    apply htL
    have hvL : v ∈ L := hbL hvb
    exact ((Submodule.span_singleton_le_iff_mem _ _).mpr hvL) h
  have hdimAbc : Module.finrank K ↥(K ∙ v ⊔ K ∙ t) = 2 := by
    have hdisj : K ∙ v ⊓ K ∙ t = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxv, hxt⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxv
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply htv
        have hv : v = c⁻¹ • (c • v) := (inv_smul_smul₀ hc v).symm
        have hxv' : v ∈ K ∙ t := by
          rw [hv]
          exact (K ∙ t).smul_mem _ hxt
        have hle : K ∙ v ≤ K ∙ t :=
          (Submodule.span_singleton_le_iff_mem _ _).mpr hxv'
        have hKeq : K ∙ v = K ∙ t := Submodule.eq_of_le_of_finrank_eq hle
          (by rw [finrank_span_singleton hv0, finrank_span_singleton ht0])
        rw [hKeq]
        exact Submodule.mem_span_singleton_self t
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ v) (K ∙ t)
    rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hv0,
      finrank_span_singleton ht0] at hd
    omega
  have hAbcflip : IsFlipflopSub σ (K ∙ v ⊔ K ∙ t) :=
    isFlipflopSub_compl_of_WY hσ.invol hWsing hYW hYflip (le_of_eq hWrad) hAabW' hAbcY
      hdimAbc hYdim hWdim
  have hbt : (flipGraph σ n).Adj b tpt := by
    refine ⟨?_, ?_⟩
    · intro h
      apply htL
      have htb : t ∈ b.1 := by
        rw [h, htpt]
        exact Submodule.mem_span_singleton_self t
      exact hbL htb
    · rw [hbK, htpt]
      exact hAbcflip
  exact hbt

private theorem bLineCA (hσ : IsUnitaryInvolution σ)
    {a b c : FlipPt σ n} {L U : Submodule K (Fin n ⊕ Fin n → K)}
    {r : Fin n ⊕ Fin n → K} (hLdef : L = a.1 ⊔ b.1) (hLU : L ≤ U) (hcU : c.1 ≤ U)
    (S : BData σ L U r) (C : BCoords σ a b c L r) (Z : BZ σ a b c L r C)
    (Λ : BLam σ L U r S C Z) (P : BApex σ L U r S C Z Λ)
    (tpt : FlipPt σ n) (htpt : tpt.1 = K ∙ P.t) :
    (flipGraph σ n).Adj c tpt := by
  let W := S.W
  let Y := S.Y
  let u := C.u
  let v := C.v
  let w := C.w
  let t := P.t
  let y := P.y
  let y₃ := P.y₃
  let θ := Z.θ
  let α := C.α
  let β := C.β
  let δ := C.δ
  let zvec := Z.zvec
  have hUW : U ≤ W := S.hUW
  have hYW : Y ≤ W := S.hYW
  have hWsing : QSing W := S.hWsing
  have hYflip : Y ≤ flipOrth σ W := S.hYflip
  have hWrad : W ⊓ flipOrth σ W = Y := S.hWrad
  have hWLY : W = L ⊔ Y := S.hWLY
  have hYdim : Module.finrank K Y = 2 := S.hdimY
  have hWdim : Module.finrank K W = 4 := S.hdimW
  have hYdef : Y = K ∙ r ⊔ K ∙ S.s := S.hYdef
  have hwc : w ∈ c.1 := C.hwc
  have hcK : c.1 = K ∙ w := C.hcK
  have haK : a.1 = K ∙ u := C.haK
  have hbK : b.1 = K ∙ v := C.hbK
  have hw0 : w ≠ 0 := C.hw0
  have hwdecomp : w = α • u + β • v + δ • r := C.hwdecomp
  have hα0 : α ≠ 0 := C.hα0
  have hβ0 : β ≠ 0 := C.hβ0
  have hθβ : θ ≠ C.β / C.α := Z.hθβ
  have ht0 : t ≠ 0 := P.ht0
  have htW : t ∈ W := P.htW
  have hyU : y ∉ U := P.hyU
  have hy3Y : y₃ ∈ Y := P.hy3Y
  have htdef : t = zvec + y := P.htdef
  have hzvecL' : zvec ∈ L := Z.hzvecL
  have hkey : t - (θ / β) • w - y₃ = (1 - θ * α / β) • u := P.hkey
  have hAcaW : K ∙ w ⊔ K ∙ t ≤ W :=
    sup_le ((Submodule.span_singleton_le_iff_mem _ _).mpr (hUW (hcU hwc)))
      ((Submodule.span_singleton_le_iff_mem _ _).mpr htW)
  have hw_mem : w ∈ (K ∙ w ⊔ K ∙ t) ⊔ Y :=
    Submodule.mem_sup_left (Submodule.mem_sup_left
      (Submodule.mem_span_singleton_self w))
  have hmu0 : 1 - θ * α / β ≠ 0 := by
    intro h
    have h1 : θ * α / β = 1 := by linear_combination -h
    have h2 : θ * α = β := by
      rwa [div_eq_one_iff_eq hβ0] at h1
    have h3 : θ = β / α := by
      rw [eq_div_iff hα0]
      exact h2
    exact hθβ h3
  have hu_eq'' : u = (1 - θ * α / β)⁻¹ • (t - (θ / β) • w - y₃) := by
    rw [hkey, smul_smul, inv_mul_cancel₀ hmu0, one_smul]
  have hu_mem'' : u ∈ (K ∙ w ⊔ K ∙ t) ⊔ Y := by
    rw [hu_eq'']
    refine ((K ∙ w ⊔ K ∙ t) ⊔ Y).smul_mem _ ?_
    refine ((K ∙ w ⊔ K ∙ t) ⊔ Y).sub_mem (((K ∙ w ⊔ K ∙ t) ⊔ Y).sub_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_right
        (Submodule.mem_span_singleton_self t))
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ _
        (Submodule.mem_sup_left (Submodule.mem_span_singleton_self w)))
    · exact Submodule.mem_sup_right hy3Y
  have hv_eq'' : v = β⁻¹ • (w - α • u - δ • r) := by
    rw [hwdecomp]
    rw [show α • u + β • v + δ • r - α • u - δ • r = β • v by abel]
    rw [smul_smul, inv_mul_cancel₀ hβ0, one_smul]
  have hv_mem'' : v ∈ (K ∙ w ⊔ K ∙ t) ⊔ Y := by
    rw [hv_eq'']
    refine ((K ∙ w ⊔ K ∙ t) ⊔ Y).smul_mem _ ?_
    refine ((K ∙ w ⊔ K ∙ t) ⊔ Y).sub_mem (((K ∙ w ⊔ K ∙ t) ⊔ Y).sub_mem ?_ ?_) ?_
    · exact Submodule.mem_sup_left (Submodule.mem_sup_left
        (Submodule.mem_span_singleton_self w))
    · exact Submodule.smul_mem _ _ hu_mem''
    · exact Submodule.mem_sup_right (by
        rw [hYdef]
        exact Submodule.mem_sup_left (Submodule.smul_mem _ δ
          (Submodule.mem_span_singleton_self r)))
  have hLmem_ca : L ≤ (K ∙ w ⊔ K ∙ t) ⊔ Y := by
    intro z hz
    rw [hLdef] at hz
    obtain ⟨zu, hzu, zv, hzv, rfl⟩ := Submodule.mem_sup.mp hz
    rw [haK] at hzu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hzu
    rw [hbK] at hzv
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hzv
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hu_mem'')
      (Submodule.smul_mem _ _ hv_mem'')
  have hAcaY : K ∙ w ⊔ K ∙ t ⊔ Y = W := by
    apply le_antisymm
    · exact sup_le hAcaW hYW
    · rw [hWLY]
      exact sup_le hLmem_ca le_sup_right
  have htw : t ∉ K ∙ w := by
    intro h
    apply hyU
    have htU : t ∈ U := hcU (hcK ▸ h)
    have hzU : zvec ∈ U := hLU hzvecL'
    have hyUt : y ∈ U := by
      have h5 := U.sub_mem htU hzU
      simpa only [htdef, add_sub_cancel_left] using h5
    exact hyUt
  have hdimAca : Module.finrank K ↥(K ∙ w ⊔ K ∙ t) = 2 := by
    have hdisj : K ∙ w ⊓ K ∙ t = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro x hx
      obtain ⟨hxw, hxt⟩ := Submodule.mem_inf.mp hx
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxw
      by_cases hc : c = 0
      · simp [hc]
      · exfalso
        apply htw
        have hw : w = c⁻¹ • (c • w) := (inv_smul_smul₀ hc w).symm
        have hxw' : w ∈ K ∙ t := by
          rw [hw]
          exact (K ∙ t).smul_mem _ hxt
        have hle : K ∙ w ≤ K ∙ t :=
          (Submodule.span_singleton_le_iff_mem _ _).mpr hxw'
        have hKeq : K ∙ w = K ∙ t := Submodule.eq_of_le_of_finrank_eq hle
          (by rw [finrank_span_singleton hw0, finrank_span_singleton ht0])
        rw [hKeq]
        exact Submodule.mem_span_singleton_self t
    have hd := Submodule.finrank_sup_add_finrank_inf_eq (K ∙ w) (K ∙ t)
    rw [hdisj, finrank_bot, add_zero, finrank_span_singleton hw0,
      finrank_span_singleton ht0] at hd
    omega
  have hAcaflip : IsFlipflopSub σ (K ∙ w ⊔ K ∙ t) :=
    isFlipflopSub_compl_of_WY hσ.invol hWsing hYW hYflip (le_of_eq hWrad) hAcaW hAcaY
      hdimAca hYdim hWdim
  have hct : (flipGraph σ n).Adj c tpt := by
    refine ⟨?_, ?_⟩
    · intro h
      apply hyU
      have htc : t ∈ c.1 := by
        rw [h, htpt]
        exact Submodule.mem_span_singleton_self t
      have htU : t ∈ U := hcU htc
      have hzU : zvec ∈ U := hLU hzvecL'
      have hyUt : y ∈ U := by
        have h5 := U.sub_mem htU hzU
        simpa only [htdef, add_sub_cancel_left] using h5
      exact hyUt
    · rw [hcK, htpt]
      exact hAcaflip
  exact hct

private theorem bFinal (hσ : IsUnitaryInvolution σ)
    {a b c : FlipPt σ n} (hab : (flipGraph σ n).Adj a b)
    (hbc : (flipGraph σ n).Adj b c) (hca : (flipGraph σ n).Adj c a)
    {L U : Submodule K (Fin n ⊕ Fin n → K)} {r : Fin n ⊕ Fin n → K}
    (hLdef : L = a.1 ⊔ b.1) (hLline : IsFlipLine σ L) (hLU : L ≤ U) (hcU : c.1 ≤ U)
    (S : BData σ L U r) (C : BCoords σ a b c L r) (Z : BZ σ a b c L r C)
    (Λ : BLam σ L U r S C Z) (P : BApex σ L U r S C Z Λ)
    (tpt : FlipPt σ n) (htpt : tpt.1 = K ∙ P.t)
    (hat : (flipGraph σ n).Adj a tpt) (hbt : (flipGraph σ n).Adj b tpt)
    (hct : (flipGraph σ n).Adj c tpt) :
    CycleHomotopic (solidWalks σ n) (triWalk hab hbc hca) .nil := by
  have hat' : (flipGraph σ n).Adj a tpt := hat
  have hbt' : (flipGraph σ n).Adj b tpt := hbt
  have hct' : (flipGraph σ n).Adj c tpt := hct
  let u := C.u
  let v := C.v
  let w := C.w
  let y := P.y
  let y₂ := P.y₂
  let y₃ := P.y₃
  let t := P.t
  have hu : u ∈ a.1 := C.hua
  have hv : v ∈ b.1 := C.hvb
  have hw : w ∈ c.1 := C.hwc
  have hyY : y ∈ S.Y := P.hyY
  have hyU : y ∉ U := P.hyU
  have hy2Y : y₂ ∈ S.Y := P.hy2Y
  have hy2U : y₂ ∉ U := P.hy2U
  have hy3Y : y₃ ∈ S.Y := P.hy3Y
  have hy3U : y₃ ∉ U := P.hy3U
  have htmem_y : t ∈ L ⊔ K ∙ y := P.htmem_y
  have htmem_bc : t ∈ (b.1 ⊔ c.1) ⊔ K ∙ y₂ := P.htmem_bc
  have htmem_ca : t ∈ (c.1 ⊔ a.1) ⊔ K ∙ y₃ := P.htmem_ca
  have hlamB : dFlip σ y ∉ K ∙ y := by
    rw [show y = S.s + Λ.lam • r from P.hydef]
    exact Λ.hlamB
  have hlam2 : dFlip σ y₂ ∉ K ∙ y₂ := by
    rw [show y₂ = S.s + (Λ.lam - Λ.μ₂) • r from P.hy2def]
    exact Λ.hlam2
  have hlam3 : dFlip σ y₃ ∉ K ∙ y₃ := by
    rw [show y₃ = S.s + (Λ.lam - Λ.μ₃) • r from P.hy3def]
    exact Λ.hlam3
  have hUW : U ≤ S.W := S.hUW
  have hYW : S.Y ≤ S.W := S.hYW
  have hWsing : QSing S.W := S.hWsing
  have hYflip : S.Y ≤ flipOrth σ S.W := S.hYflip
  have hYiso : ∀ y' ∈ S.Y, flipHerm σ y' y' = 0 := S.hYiso
  have haK : a.1 = K ∙ C.u := C.haK
  have hbK : b.1 = K ∙ C.v := C.hbK
  have hcK : c.1 = K ∙ C.w := C.hcK
  have hua : C.u ∈ a.1 := C.hua
  have hvb : C.v ∈ b.1 := C.hvb
  have hwc : C.w ∈ c.1 := C.hwc
  have haL : a.1 ≤ L := by
    rw [hLdef]
    exact le_sup_left
  have hbL : b.1 ≤ L := by
    rw [hLdef]
    exact le_sup_right
  have hUbc : b.1 ⊔ c.1 ≤ U := sup_le (le_trans hbL hLU) hcU
  have hUca : c.1 ⊔ a.1 ≤ U := by
    rw [sup_comm]
    exact sup_le (le_trans haL hLU) hcU
  have hT1 : CycleHomotopic (solidWalks σ n) (triWalk hab hbt' hat'.symm) .nil := by
    obtain ⟨V1, hV1flip, hV1le⟩ := exists_flipflop_of_rad_side hσ.invol hLline hLU
      hUW hYW hWsing hYflip hYiso hyY hyU hlamB
    refine cycleHomotopic_of_mem (solidWalks σ n) ?_
    refine mem_solidWalks_of_le hσ hV1flip fun z' hz' => ?_
    simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with h1 | h2 | h3 | h4
    · rw [h1, haK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem u L).mpr (by
        rw [hLdef]
        exact Submodule.mem_sup_left hua)) (le_trans le_sup_left hV1le)
    · rw [h2, hbK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem v L).mpr (by
        rw [hLdef]
        exact Submodule.mem_sup_right hvb)) (le_trans le_sup_left hV1le)
    · rw [h3, htpt]
      exact le_trans ((Submodule.span_singleton_le_iff_mem t (L ⊔ K ∙ y)).mpr htmem_y)
        hV1le
    · rw [h4, haK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem u L).mpr (by
        rw [hLdef]
        exact Submodule.mem_sup_left hua)) (le_trans le_sup_left hV1le)
  have hT2 : CycleHomotopic (solidWalks σ n) (triWalk hbc hct' hbt'.symm) .nil := by
    obtain ⟨V2, hV2flip, hV2le⟩ := exists_flipflop_of_rad_side hσ.invol
      (hbc.isFlipLine b.2 c.2) hUbc hUW hYW hWsing hYflip hYiso hy2Y hy2U hlam2
    refine cycleHomotopic_of_mem (solidWalks σ n) ?_
    refine mem_solidWalks_of_le hσ hV2flip fun z' hz' => ?_
    simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with h1 | h2 | h3 | h4
    · rw [h1, hbK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem v (b.1 ⊔ c.1)).mpr
        (show C.v ∈ b.1 ⊔ c.1 from Submodule.mem_sup_left hvb))
        (le_trans le_sup_left hV2le)
    · rw [h2, hcK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem w (b.1 ⊔ c.1)).mpr
        (show C.w ∈ b.1 ⊔ c.1 from Submodule.mem_sup_right hwc))
        (le_trans le_sup_left hV2le)
    · rw [h3, htpt]
      exact le_trans ((Submodule.span_singleton_le_iff_mem t ((b.1 ⊔ c.1) ⊔ K ∙ y₂)).mpr
        htmem_bc) hV2le
    · rw [h4, hbK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem v (b.1 ⊔ c.1)).mpr
        (show C.v ∈ b.1 ⊔ c.1 from Submodule.mem_sup_left hvb))
        (le_trans le_sup_left hV2le)
  have hT3 : CycleHomotopic (solidWalks σ n) (triWalk hca hat' hct'.symm) .nil := by
    obtain ⟨V3, hV3flip, hV3le⟩ := exists_flipflop_of_rad_side hσ.invol
      (hca.isFlipLine c.2 a.2) hUca hUW hYW hWsing hYflip hYiso hy3Y hy3U hlam3
    refine cycleHomotopic_of_mem (solidWalks σ n) ?_
    refine mem_solidWalks_of_le hσ hV3flip fun z' hz' => ?_
    simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hz'
    rcases hz' with h1 | h2 | h3 | h4
    · rw [h1, hcK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem w (c.1 ⊔ a.1)).mpr
        (show C.w ∈ c.1 ⊔ a.1 from Submodule.mem_sup_left hwc))
        (le_trans le_sup_left hV3le)
    · rw [h2, haK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem u (c.1 ⊔ a.1)).mpr
        (show C.u ∈ c.1 ⊔ a.1 from Submodule.mem_sup_right hua))
        (le_trans le_sup_left hV3le)
    · rw [h3, htpt]
      exact le_trans ((Submodule.span_singleton_le_iff_mem t ((c.1 ⊔ a.1) ⊔ K ∙ y₃)).mpr
        htmem_ca) hV3le
    · rw [h4, hcK]
      exact le_trans ((Submodule.span_singleton_le_iff_mem w (c.1 ⊔ a.1)).mpr
        (show C.w ∈ c.1 ⊔ a.1 from Submodule.mem_sup_left hwc))
        (le_trans le_sup_left hV3le)
  refine cycleHomotopic_cone_nil (solidWalks σ n)
    (S := fun x y => (x = a ∧ y = b) ∨ (x = b ∧ y = c) ∨ (x = c ∧ y = a))
    ?_ (triWalk hab hbc hca) hat' ?_
  · rintro x y (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨hab, hat', hbt', hT1⟩
    · exact ⟨hbc, hbt', hct', hT2⟩
    · exact ⟨hca, hct', hat', hT3⟩
  · intro d hd
    simp only [triWalk, SimpleGraph.Walk.darts_cons, SimpleGraph.Walk.darts_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hd
    rcases hd with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨rfl, rfl⟩)
    · exact Or.inr (Or.inr ⟨rfl, rfl⟩)

private theorem caseA (hσ : IsUnitaryInvolution σ)
    {a b c : FlipPt σ n} (hab : (flipGraph σ n).Adj a b)
    (hbc : (flipGraph σ n).Adj b c) (hca : (flipGraph σ n).Adj c a)
    {L U : Submodule K (Fin n ⊕ Fin n → K)} (hLline : IsFlipLine σ L)
    (hUsing : QSing U) (hcU : c.1 ≤ U) (hLdef : L = a.1 ⊔ b.1)
    (R : RadData σ L U) (hA : dFlip σ R.r ∉ K ∙ R.r) :
    CycleHomotopic (solidWalks σ n) (triWalk hab hbc hca) .nil := by
  obtain ⟨U', hU'flip, hUU'⟩ := exists_flipflop_of_rad hσ.invol hLline R.ne_zero
    (quadPlus_eq_zero_of_qSing hUsing R.mem_U) R.L_perp R.L_flip R.self hA
  refine cycleHomotopic_of_mem (solidWalks σ n) ?_
  refine mem_solidWalks_of_le hσ hU'flip fun y hy => ?_
  simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact le_trans (le_trans (by rw [hLdef]; exact le_sup_left) le_sup_left) hUU'
  · exact le_trans (le_trans (by rw [hLdef]; exact le_sup_right) le_sup_left) hUU'
  · exact le_trans (R.U_eq ▸ hcU) hUU'
  · exact le_trans (le_trans (by rw [hLdef]; exact le_sup_left) le_sup_left) hUU'

private theorem caseB (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    {a b c : FlipPt σ n} (hab : (flipGraph σ n).Adj a b)
    (hbc : (flipGraph σ n).Adj b c) (hca : (flipGraph σ n).Adj c a)
    {L U : Submodule K (Fin n ⊕ Fin n → K)}
    (hLdef : L = a.1 ⊔ b.1) (hLline : IsFlipLine σ L)
    (hUsing : QSing U) (hcL : ¬ c.1 ≤ L) (hLU : L ≤ U) (hcU : c.1 ≤ U)
    (R : RadData σ L U) (hAmem : dFlip σ R.r ∈ K ∙ R.r) :
    CycleHomotopic (solidWalks σ n) (triWalk hab hbc hca) .nil := by
  classical
  let B := bDataD hσ R hUsing hAmem
  let BW := bDataW R B hUsing
  let S := bData hσ hLline R B hAmem BW
  let C := bCoords hσ hbc hca hLdef hLU hcU hcL R
  let Z := bZ hσ hK hq hLline hLdef C
  let Λ := bLam hσ hK hq R S C Z hAmem
  let P := bApex hσ R S C Z Λ hLU
  let tpt : FlipPt σ n := ⟨K ∙ P.t, P.htpt⟩
  have htpt : tpt.1 = K ∙ P.t := rfl
  have hat := bLineAB hσ hLdef hLU S C Z Λ P tpt htpt
  have hbt := bLineBC hσ hLdef hLU S C Z Λ P tpt htpt
  have hct := bLineCA hσ hLdef hLU hcU S C Z Λ P tpt htpt
  exact bFinal hσ hab hbc hca hLdef hLline hLU hcU S C Z Λ P tpt htpt hat hbt hct

theorem cycleHomotopic_triangle (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q)
    {a b c : FlipPt σ n} (hab : (flipGraph σ n).Adj a b)
    (hbc : (flipGraph σ n).Adj b c) (hca : (flipGraph σ n).Adj c a) :
    CycleHomotopic (solidWalks σ n) (triWalk hab hbc hca) .nil := by
  classical
  set L : Submodule K (Fin n ⊕ Fin n → K) := a.1 ⊔ b.1 with hLdef
  set U : Submodule K (Fin n ⊕ Fin n → K) := a.1 ⊔ b.1 ⊔ c.1 with hUdef
  have hLline : IsFlipLine σ L := by
    rw [hLdef]
    exact FlipColl.isFlipLine hab a.2 b.2
  have hcPerpL : c.1 ≤ qPerp n K L := by
    intro x hx
    refine (mem_qPerp (n := n) (K := K) (W := L)).mpr fun l hl => ?_
    rw [hLdef] at hl
    obtain ⟨l₁, hl₁, l₂, hl₂, rfl⟩ := Submodule.mem_sup.mp hl
    rw [polar_add_left, (mem_qPerp.mp (hca.le_qPerp hx)) l₁ hl₁,
      (mem_qPerp.mp (hbc.symm.le_qPerp hx)) l₂ hl₂, add_zero]
  have hLsing : (quadPlusForm n K).IsTotallySingular L := by
    intro u hu
    rw [quadPlusForm_Q]
    exact hLline.1.total u hu
  have hcsing : (quadPlusForm n K).IsTotallySingular c.1 := by
    intro u hu
    rw [quadPlusForm_Q]
    exact (isFlipflopSub_of_flipPt c.2).total u hu
  have hLorthc : L ≤ (quadPlusForm n K).polar.perp c.1 := by
    intro l hl
    rw [ReflForm.mem_perp]
    intro x hx
    rw [quadPlusForm_polar, polar_comm]
    exact (mem_qPerp (n := n) (K := K) (W := L)).mp (hcPerpL hx) l hl
  have hUsing : QSing U := by
    rw [hUdef]
    exact (qSing_iff_isTotallySingular _).mpr (hLsing.sup hcsing hLorthc)
  by_cases hcL : c.1 ≤ L
  · refine cycleHomotopic_of_mem (solidWalks σ n) ?_
    refine mem_solidWalks_of_le hσ hLline.1 fun y hy => ?_
    simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · rw [hLdef]
      exact le_sup_left
    · rw [hLdef]
      exact le_sup_right
    · exact hcL
    · rw [hLdef]
      exact le_sup_left
  by_cases hUflip : IsFlipflopSub σ U
  · have haU : a.1 ≤ U := by
      rw [hUdef]
      exact le_sup_left.trans le_sup_left
    have hbU : b.1 ≤ U := by
      rw [hUdef]
      exact le_sup_right.trans le_sup_left
    have hcU' : c.1 ≤ U := by
      rw [hUdef]
      exact le_sup_right
    refine cycleHomotopic_of_mem (solidWalks σ n) ?_
    refine mem_solidWalks_of_le hσ hUflip fun y hy => ?_
    simp only [triWalk, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.mem_cons, List.not_mem_nil, or_false] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact haU
    · exact hbU
    · exact hcU'
    · exact haU
  · have hLU : L ≤ U := by
      rw [hLdef, hUdef]
      exact le_sup_left
    have hcU : c.1 ≤ U := by
      rw [hUdef]
      exact le_sup_right
    have hUeq : U = L ⊔ c.1 := by
      rw [hUdef, hLdef]
    let R := radical_data hσ hLline hUsing hUflip hcL hUeq
    by_cases hA : dFlip σ R.r ∉ K ∙ R.r
    · exact caseA hσ hab hbc hca hLline hUsing hcU hLdef R hA
    · have hAmem : dFlip σ R.r ∈ K ∙ R.r := not_not.mp hA
      exact caseB hσ hK hq hab hbc hca hLdef hLline hUsing hcL hLU hcU R hAmem

theorem nullLen_three (hσ : IsUnitaryInvolution σ) [Finite K] {q : ℕ}
    (hK : Nat.card K = q ^ 2) (hq : 4 ≤ q) : NullLen (solidWalks σ n) 3 := by
  intro u p hp
  match u, p, hp with
  | _, .cons hab (.cons hbc (.cons hca .nil)), _ =>
    exact cycleHomotopic_triangle hσ hK hq hab hbc hca

end CFSG.ClassicalInvolution.PhanDn
