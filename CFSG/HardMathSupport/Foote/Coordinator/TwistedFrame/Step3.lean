module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Hyp
public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ScalarTorus
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

set_option linter.unusedSectionVars false


variable {τ : Tag} {K : Type} [Field K]

theorem exists_of_mem_span_coord (Y : Subgroup (ModGL τ K)) (hY : Y ≤ Qθ τ K)
    (hs : ∀ a : K, a ≠ 0 → ∃ h : ModGL τ K, ∀ y ∈ Y, h * y * h⁻¹ ∈ Y ∧
      heisCoord τ K (h * y * h⁻¹) = a • heisCoord τ K y) {f : (Fin τ.rank → ℤ) → K}
    (hf : f ∈ Submodule.span K (heisCoord τ K '' (Y : Set (ModGL τ K)))) :
    ∃ y ∈ Y, heisCoord τ K y = f := by
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨y, hy, rfl⟩
  | zero => exact ⟨1, one_mem _, heisCoord_one⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, rfl⟩ := hx
    obtain ⟨b, hb, rfl⟩ := hy
    exact ⟨a * b, mul_mem ha hb, (heisCoord_spec τ K).mul a (hY ha) b (hY hb)⟩
  | smul a x _ hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    by_cases ha : a = 0
    · subst ha
      exact ⟨1, one_mem _, by rw [heisCoord_one, zero_smul]⟩
    · obtain ⟨h, hh⟩ := hs a ha
      exact ⟨h * y * h⁻¹, (hh y hy).1, (hh y hy).2⟩

theorem mul_inv_mem_Uθ_of_coord_eq {q q' : ModGL τ K} (hq : q ∈ Qθ τ K) (hq' : q' ∈ Qθ τ K)
    (h : heisCoord τ K q = heisCoord τ K q') : q * q'⁻¹ ∈ Uθ τ K := by
  have hm := (heisCoord_spec τ K).mul q hq q'⁻¹ (inv_mem hq')
  rw [heisCoord_inv hq', ← h, add_neg_cancel] at hm
  exact ((heisCoord_spec τ K).eq_zero_iff _ (mul_mem hq (inv_mem hq'))).1 hm

theorem Lθ_conj_mem_Qθ {l q : ModGL τ K} (hl : l ∈ Lθ τ K) (hq : q ∈ Qθ τ K) :
    l * q * l⁻¹ ∈ Qθ τ K :=
  (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical (τ := τ)
    (K := K) (Jθ τ) (parabolicLevi_le_parabolicSubgroup (Jθ τ) hl)) q).1 hq

theorem Lθ_conj_mem_Uθ {l u : ModGL τ K} (hl : l ∈ Lθ τ K) (hu : u ∈ Uθ τ K) :
    l * u * l⁻¹ ∈ Uθ τ K :=
  (Subgroup.mem_normalizer_iff.1 (Pθ_le_normalizer_Uθ τ K
    (parabolicLevi_le_parabolicSubgroup (Jθ τ) hl)) u).1 hu

theorem Qθ_le_of_M_element {X₁ X₂ H : Subgroup (ModGL τ K)} (h : TwFrameHyp X₁ X₂)
    (hXH : X₁ ⊔ X₂ ≤ H) {m : ModGL τ K} (hmH : m ∈ H) (hmQ : m ∈ Qθ τ K)
    (hmS : heisCoord τ K m ∉ VS (X₁ ⊔ X₂)) : Qθ τ K ≤ H := by
  classical
  set X := X₁ ⊔ X₂ with hX
  have hX₁X : X₁ ≤ X := le_sup_left
  have hUθH : Uθ τ K ≤ H := (h.basic.Uθ_le.trans hX₁X).trans hXH
  have hsc : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, t ∈ X ∧ t ∈ Lθ τ K ∧ ∀ q ∈ Qθ τ K,
      t * q * t⁻¹ ∈ Qθ τ K ∧ heisCoord τ K (t * q * t⁻¹) = a • heisCoord τ K q := by
    intro a ha
    obtain ⟨t, ht, htL, hts⟩ := exists_scalarTorus τ K ha
    exact ⟨t, hX₁X (sup_le h.basic.Uθ_le h.basic.Uneg_le ht), htL, hts⟩
  have hRconj : ∀ l ∈ X ⊓ Lθ τ K, ∀ r ∈ Rθ X, l * r * l⁻¹ ∈ Rθ X := fun l hl r hr =>
    ⟨X.mul_mem (X.mul_mem hl.1 hr.1) (X.inv_mem hl.1), Lθ_conj_mem_Qθ hl.2 hr.2⟩
  have hsH : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, ∀ y ∈ H ⊓ Qθ τ K, t * y * t⁻¹ ∈ H ⊓ Qθ τ K ∧
      heisCoord τ K (t * y * t⁻¹) = a • heisCoord τ K y := by
    intro a ha
    obtain ⟨t, htX, -, hts⟩ := hsc a ha
    refine ⟨t, fun y hy => ⟨⟨H.mul_mem (H.mul_mem (hXH htX) hy.1) (H.inv_mem (hXH htX)),
      (hts y hy.2).1⟩, (hts y hy.2).2⟩⟩
  have hsR : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, ∀ y ∈ Rθ X, t * y * t⁻¹ ∈ Rθ X ∧
      heisCoord τ K (t * y * t⁻¹) = a • heisCoord τ K y := by
    intro a ha
    obtain ⟨t, htX, htL, hts⟩ := hsc a ha
    exact ⟨t, fun y hy => ⟨hRconj t ⟨htX, htL⟩ y hy, (hts y hy.2).2⟩⟩
  have hCQconj : ∀ l ∈ X ⊓ Lθ τ K, ∀ y ∈ CQθ X, l * y * l⁻¹ ∈ CQθ X := by
    intro l hl y hy
    refine ⟨Lθ_conj_mem_Qθ hl.2 hy.1, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro r hr
    have hr' : l⁻¹ * r * l ∈ Rθ X := by
      have := hRconj l⁻¹ (Subgroup.mem_inf.2 ⟨X.inv_mem hl.1, (Lθ τ K).inv_mem hl.2⟩) r hr
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hy.2 _ hr'
    calc r * (l * y * l⁻¹) = l * ((l⁻¹ * r * l) * y) * l⁻¹ := by group
      _ = l * (y * (l⁻¹ * r * l)) * l⁻¹ := by rw [hc]
      _ = (l * y * l⁻¹) * r := by group
  have hsCQ : ∀ a : K, a ≠ 0 → ∃ t : ModGL τ K, ∀ y ∈ CQθ X, t * y * t⁻¹ ∈ CQθ X ∧
      heisCoord τ K (t * y * t⁻¹) = a • heisCoord τ K y := by
    intro a ha
    obtain ⟨t, htX, htL, hts⟩ := hsc a ha
    exact ⟨t, fun y hy => ⟨hCQconj t ⟨htX, htL⟩ y hy, (hts y hy.1).2⟩⟩
  set W : Submodule K ((Fin τ.rank → ℤ) → K) :=
    Submodule.span K (heisCoord τ K '' ((H ⊓ Qθ τ K : Subgroup (ModGL τ K)) : Set (ModGL τ K)))
    with hWdef
  have hW : ∀ f ∈ W, ∃ y ∈ H ⊓ Qθ τ K, heisCoord τ K y = f := fun f hf =>
    exists_of_mem_span_coord (H ⊓ Qθ τ K) inf_le_right hsH hf
  have hWmem : ∀ y ∈ H ⊓ Qθ τ K, heisCoord τ K y ∈ W := fun y hy =>
    Submodule.subset_span ⟨y, hy, rfl⟩
  have hVS : VS X ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨r, hr, rfl⟩
    exact hWmem r ⟨hXH hr.1, hr.2⟩
  have hQmem : ∀ q ∈ Qθ τ K, heisCoord τ K q ∈ W → q ∈ H := by
    intro q hq hqW
    obtain ⟨q', hq'H, hq'c⟩ := hW _ hqW
    have hd := mul_inv_mem_Uθ_of_coord_eq hq hq'H.2 hq'c.symm
    have := H.mul_mem (hUθH hd) hq'H.1
    simpa using this
  have hcm : heisCoord τ K m ∈ VS X ⊔ VM X := by
    rw [h.coords.sup_eq_top]
    exact fun β hβ => (heisCoord_spec τ K).support m hmQ β hβ
  obtain ⟨uS, huS, uM, huM, hsum⟩ := Submodule.mem_sup.1 hcm
  have huMW : uM ∈ W := by
    have : uM = heisCoord τ K m - uS := by rw [← hsum]; abel
    rw [this]
    exact W.sub_mem (hWmem m ⟨hmH, hmQ⟩) (hVS huS)
  have huM0 : uM ≠ 0 := by
    intro h0
    apply hmS
    rw [← hsum, h0, add_zero]
    exact huS
  have hstable : ∀ l ∈ X ⊓ Lθ τ K, ∀ q ∈ Qθ τ K, heisCoord τ K q ∈ W ⊓ VM X →
      heisCoord τ K (l * q * l⁻¹) ∈ W ⊓ VM X := by
    intro l hl q hq hqW
    have hlq : l * q * l⁻¹ ∈ Qθ τ K := Lθ_conj_mem_Qθ hl.2 hq
    refine ⟨?_, ?_⟩
    · have hqH : q ∈ H := hQmem q hq hqW.1
      exact hWmem _ ⟨H.mul_mem (H.mul_mem (hXH hl.1) hqH) (H.inv_mem (hXH hl.1)), hlq⟩
    · obtain ⟨q'', hq''C, hq''c⟩ := exists_of_mem_span_coord (CQθ X) inf_le_left hsCQ hqW.2
      have hdiff : q * q''⁻¹ ∈ Uθ τ K := mul_inv_mem_Uθ_of_coord_eq hq hq''C.1 hq''c.symm
      have hlu : l * (q * q''⁻¹) * l⁻¹ ∈ Uθ τ K := Lθ_conj_mem_Uθ hl.2 hdiff
      have hlq'' : l * q'' * l⁻¹ ∈ CQθ X := hCQconj l hl q'' hq''C
      have hsplit : l * q * l⁻¹ = (l * (q * q''⁻¹) * l⁻¹) * (l * q'' * l⁻¹) := by group
      have hu'Q : l * (q * q''⁻¹) * l⁻¹ ∈ Qθ τ K := by
        have : l * (q * q''⁻¹) * l⁻¹ = (l * q * l⁻¹) * (l * q'' * l⁻¹)⁻¹ := by group
        rw [this]
        exact mul_mem hlq (inv_mem hlq''.1)
      have hu'0 : heisCoord τ K (l * (q * q''⁻¹) * l⁻¹) = 0 :=
        ((heisCoord_spec τ K).eq_zero_iff _ hu'Q).2 hlu
      have hcoord : heisCoord τ K (l * q * l⁻¹) = heisCoord τ K (l * q'' * l⁻¹) := by
        rw [hsplit, (heisCoord_spec τ K).mul _ hu'Q _ hlq''.1, hu'0, zero_add]
      rw [hcoord]
      exact Submodule.subset_span ⟨l * q'' * l⁻¹, hlq'', rfl⟩
  have hirr := h.irred (W ⊓ VM X) inf_le_right hstable
  have hVMW : VM X ≤ W := by
    rcases hirr with h0 | h1
    · exfalso
      have : uM ∈ W ⊓ VM X := ⟨huMW, huM⟩
      rw [h0] at this
      exact huM0 ((Submodule.mem_bot K).1 this)
    · intro v hv
      have : v ∈ W ⊓ VM X := by rw [h1]; exact hv
      exact this.1
  have hall : HeisSpace τ K ≤ W := by
    rw [← h.coords.sup_eq_top]
    exact sup_le hVS hVMW
  intro q hq
  exact hQmem q hq (hall fun β hβ => (heisCoord_spec τ K).support q hq β hβ)

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame
