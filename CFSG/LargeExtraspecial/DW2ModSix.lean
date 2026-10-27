module

public import CFSG.LargeExtraspecial.DW2ModSixA
public import CFSG.LargeExtraspecial.DW2ModTv
public import CFSG.LargeExtraspecial.DW2ModFour
public import CFSG.LargeExtraspecial.DW2ModSec

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.DW

open Module Submodule CFSG.RankThree.OrthogonalInvolutions
open CFSG.ComponentClassification.OutcomeLocal (IsF2Transvection)

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

theorem symm_of_isAlt {f : LinearMap.BilinForm (ZMod 2) V} (halt : f.IsAlt) (u v : V) :
    f u v = f v u := by
  have h := halt (u + v)
  simp only [map_add, LinearMap.add_apply, halt u, halt v, zero_add, add_zero] at h
  calc f u v = f u v + (f v u + f u v) := by rw [h, add_zero]
    _ = f v u + (f u v + f u v) := by ring
    _ = f v u := by rw [add_self_zmod2, add_zero]

variable {Y : Subgroup (V ≃ₗ[ZMod 2] V)} {f : LinearMap.BilinForm (ZMod 2) V}
  {D : Set (V ≃ₗ[ZMod 2] V)}

theorem IsA2Class.mem {hD : IsA2Class f Y D} {d : V ≃ₗ[ZMod 2] V} (hd : d ∈ D) : d ∈ Y :=
  hD.1 ▸ Subgroup.subset_closure hd

theorem IsA2Class.not_isUnip (hD : IsA2Class f Y D) (hO2 : S12NoNormalTwo Y) :
    ¬ IsUnip Y ⊥ ⊤ := by
  intro h
  obtain ⟨d₀, hd₀, -⟩ := hD.2.1
  have hY1 := eq_bot_of_isUnip hO2 h
  have hd₀Y : d₀ ∈ Y := hD.1 ▸ Subgroup.subset_closure hd₀
  rw [hY1, Subgroup.mem_bot] at hd₀Y
  exact (hD.2.2 d₀ hd₀).2.1 hd₀Y

theorem rad_orth_of_le (halt : f.IsAlt) {F : Submodule (ZMod 2) V} (hFU : F ≤ stab Y ⊤) :
    ∀ a ∈ rad f (stab Y ⊤), ∀ b ∈ F, f a b = 0 ∧ f b a = 0 := by
  intro a ha b hb
  have h := LinearMap.BilinForm.mem_orthogonal_iff.mp ha.2 b (hFU hb)
  exact ⟨halt.isRefl _ _ h, h⟩

variable [FiniteDimensional (ZMod 2) V]

theorem fourGroup_secHom (hD : IsA2Class f Y D) {A B : Submodule (ZMod 2) V} (hA : IsInv Y A)
    (hB : IsInv Y B) (hAB : A ≤ B) (h1 : ∀ d ∈ D, secRank d A B = 1) {a b : V ≃ₗ[ZMod 2] V}
    (ha : a ∈ D) (hb : b ∈ D) (hab : a * b ∈ D) :
    IsF2Transvection (secHom A B Y hA hB ⟨a, hD.mem ha⟩) ∧
      IsF2Transvection (secHom A B Y hA hB ⟨b, hD.mem hb⟩) ∧
      secHom A B Y hA hB ⟨a, hD.mem ha⟩ ≠ secHom A B Y hA hB ⟨b, hD.mem hb⟩ ∧
      IsF2Transvection
        (secHom A B Y hA hB ⟨a, hD.mem ha⟩ * secHom A B Y hA hB ⟨b, hD.mem hb⟩) := by
  have htab : IsF2Transvection (secHom A B Y hA hB ⟨a, hD.mem ha⟩ *
      secHom A B Y hA hB ⟨b, hD.mem hb⟩) := by
    rw [← map_mul]
    exact isF2Transvection_secHom hA hB hAB (h1 _ hab)
  refine ⟨isF2Transvection_secHom hA hB hAB (h1 a ha),
    isF2Transvection_secHom hA hB hAB (h1 b hb), fun heq => htab.1 ?_, htab⟩
  rw [← heq, ← map_mul]
  have haa : (⟨a, hD.mem ha⟩ : Y) * ⟨a, hD.mem ha⟩ = 1 :=
    Subtype.ext (hD.2.2 a ha).2.2.1
  rw [haa, map_one]

variable (hf : f.Nondegenerate) (halt : f.IsAlt) (hY : Y ≤ TauCeti.BilinForm.isometryGroup f)
include hf halt hY

theorem exists_minimal_factor (hD : IsA2Class f Y D) (hO2 : S12NoNormalTwo Y)
    (h2 : ¬ OneFactor Y) :
    ∃ F, IsNontrivFactor Y (rad f (stab Y ⊤)) F ∧ F < stab Y ⊤ ∧ ¬ IsUnip Y F ⊤ := by
  have hr : f.IsRefl := halt.isRefl
  have hU : IsInv Y (stab Y ⊤) := isInv_stab isInv_top
  have hR : IsInv Y (rad f (stab Y ⊤)) := hU.inf (isInv_orth hY hU)
  have hRu : IsUnip Y ⊥ (rad f (stab Y ⊤)) :=
    (isUnip_orth_stab hf hr hY).mono le_rfl inf_le_right
  have hUnu := not_isUnip_stab (hD.not_isUnip hO2)
  have hex : ∃ W, IsInv Y W ∧ rad f (stab Y ⊤) < W ∧ W ≤ stab Y ⊤ ∧ W ≠ stab Y ⊤ := by
    by_contra hcon
    push Not at hcon
    apply h2
    refine ⟨isInv_bot, isInv_top, rad f (stab Y ⊤), stab Y ⊤, bot_le, hRu,
      ⟨hR, hU, inf_le_left, ?_, ?_⟩, le_top, isUnip_stab ⊤⟩
    · rw [commSub_stab isInv_top]
      intro hle
      exact hUnu (hRu.mono le_rfl hle)
    · intro W hW hRW hWU
      by_cases h : W = rad f (stab Y ⊤)
      · exact Or.inl h
      · exact Or.inr (hcon W hW (lt_of_le_of_ne hRW (Ne.symm h)) hWU)
  obtain ⟨W, hW, hRW, hWU, hWne⟩ := hex
  obtain ⟨F, hF, hRF, hFU, hmin⟩ := exists_minimal ⟨W, hW, hRW, hWU⟩
  have hFneU : F ≠ stab Y ⊤ := by
    intro h
    rw [h] at hmin
    exact hWne (hmin W hW hRW hWU)
  refine ⟨F, ⟨hR, hF, hRF.le, ?_, ?_⟩, lt_of_le_of_ne hFU hFneU, ?_⟩
  · intro hle
    have hFu : IsUnip Y ⊥ F := hRu.trans (isUnip_of_commSub_le hle)
    exact lt_irrefl _ (lt_of_lt_of_le hRF (le_inf hFU (le_orth_stab_of_isUnip hY hF hFu)))
  · intro W' hW' hRW' hW'F
    by_cases h : W' = rad f (stab Y ⊤)
    · exact Or.inl h
    · exact Or.inr (hmin W' hW' (lt_of_le_of_ne hRW' (Ne.symm h)) hW'F)
  · intro hFt
    exact hFneU (le_antisymm hFU (hFt.stab_le hF isInv_top))

omit hf in
theorem false_of_inf_orth_le (hD : IsA2Class f Y D) (h4 : HasFourGroup D)
    {F : Submodule (ZMod 2) V} (hFac : IsNontrivFactor Y (rad f (stab Y ⊤)) F)
    (hFU : F ≤ stab Y ⊤) (hFt : ¬ IsUnip Y F ⊤)
    (hreg : F ⊓ f.orthogonal F ≤ rad f (stab Y ⊤)) : False := by
  have hr : f.IsRefl := halt.isRefl
  have hnuRF := hFac.not_isUnip
  obtain ⟨hR, hF, hRF, -, -⟩ := hFac
  have hcl : ∀ d ∈ D, ∀ d' ∈ D, ∃ g ∈ Y, d' = g * d * g⁻¹ := fun d hd d' hd' =>
    hD.exists_conj hd hd'
  have h1 : ∀ d ∈ D, secRank d (rad f (stab Y ⊤)) F = 1 := by
    intro d hd
    have hdY := hD.mem hd
    have r1 := one_le_secRank hD.1 hcl hR hF hnuRF hd
    have r2 := one_le_secRank hD.1 hcl hF isInv_top hFt hd
    have s1 := secRank_add_le (g := d) hRF le_top (hF d hdY)
    have s2 := secRank_add_le (g := d) (bot_le : ⊥ ≤ rad f (stab Y ⊤)) le_top (hR d hdY)
    have hrk := secRank_bot_top d
    rw [(hD.2.2 d hd).2.2.2.1] at hrk
    omega
  obtain ⟨a, ha, b, hb, -, -, hab⟩ := h4
  obtain ⟨ht₁, ht₂, hne, ht₁₂⟩ := fourGroup_secHom hD hR hF hRF h1 ha hb hab
  have hAB := rad_orth_of_le halt hFU
  exact false_of_fourGroup_of_isometry (secForm f hAB) (secForm_self hAB halt)
    (secForm_comm hAB (symm_of_isAlt halt)) (fun u hu => secForm_nondeg hAB hr hreg u hu)
    ht₁ ht₂ hne ht₁₂
    (fun x z => secForm_secLin hAB (hF a (hD.mem ha)) (hR a (hD.mem ha))
      (apply_apply_eq hY (hD.mem ha)) x z)
    (fun x z => secForm_secLin hAB (hF b (hD.mem hb)) (hR b (hD.mem hb))
      (apply_apply_eq hY (hD.mem hb)) x z)

theorem bijective_of_le_orth (hD : IsA2Class f Y D) (hO2 : S12NoNormalTwo Y)
    (h4 : HasFourGroup D) {F : Submodule (ZMod 2) V}
    (hFac : IsNontrivFactor Y (rad f (stab Y ⊤)) F) (hFU : F < stab Y ⊤)
    (hiso : F ≤ f.orthogonal F) :
    (∀ y ∈ Y, ∀ r ∈ rad f (stab Y ⊤), y r = r) ∧
      (∀ y ∈ Y, ∀ v ∈ stab Y ⊤ ⊓ f.orthogonal F, y v - v ∈ F) ∧
      (∀ y ∈ Y, ∀ v, y v - v ∈ stab Y ⊤) ∧
      IsNontrivFactor Y (stab Y ⊤ ⊓ f.orthogonal F) (stab Y ⊤) ∧
      Function.Bijective (secHom (rad f (stab Y ⊤)) F Y hFac.1 hFac.2.1) := by
  have hr : f.IsRefl := halt.isRefl
  have hnuRF := hFac.not_isUnip
  have hR := hFac.1
  have hF := hFac.2.1
  have hRF := hFac.2.2.1
  have hirrRF := hFac.2.2.2.2
  have hU : IsInv Y (stab Y ⊤) := isInv_stab isInv_top
  have hF' : IsInv Y (stab Y ⊤ ⊓ f.orthogonal F) := hU.inf (isInv_orth hY hF)
  have hFF' : F ≤ stab Y ⊤ ⊓ f.orthogonal F := le_inf hFU.le hiso
  have hRU : rad f (stab Y ⊤) ≤ f.orthogonal (stab Y ⊤) := inf_le_right
  have hFR : F ⊓ f.orthogonal (stab Y ⊤) ≤ rad f (stab Y ⊤) := fun x hx => ⟨hFU.le hx.1, hx.2⟩
  have hcl : ∀ d ∈ D, ∀ d' ∈ D, ∃ g ∈ Y, d' = g * d * g⁻¹ := fun d hd d' hd' =>
    hD.exists_conj hd hd'
  have hrank : ∀ d ∈ D, secRank d ⊥ (rad f (stab Y ⊤)) = 0 ∧
      secRank d (rad f (stab Y ⊤)) F = 1 ∧ secRank d F (stab Y ⊤ ⊓ f.orthogonal F) = 0 ∧
      secRank d (stab Y ⊤) ⊤ = 0 := by
    intro d hd
    have hdY := hD.mem hd
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right (hD.2.2 d hd).2.2.1
    have r1 := one_le_secRank hD.1 hcl hR hF hnuRF hd
    have r4 : 1 ≤ secRank d (stab Y ⊤ ⊓ f.orthogonal F) (stab Y ⊤) := by
      by_contra h0
      have htriv := secRank_eq_zero_iff.mp
        (show secRank d (stab Y ⊤ ⊓ f.orthogonal F) (stab Y ⊤) = 0 by omega)
      have hinv := inv_sub_mem_of_forall hr hY hF hFR hdY fun u hu => (htriv u hu).2
      rw [hdinv] at hinv
      have h5 := secRank_eq_zero_iff.mpr hinv
      omega
    have s1 := secRank_add_le (g := d) hRF hFF' (hF d hdY)
    have s2 := secRank_add_le (g := d) (hRF.trans hFF') inf_le_left (hF' d hdY)
    have s3 := secRank_add_le (g := d) ((hRF.trans hFF').trans inf_le_left)
      (le_top : stab Y ⊤ ≤ ⊤) (hU d hdY)
    have s4 := secRank_add_le (g := d) (bot_le : ⊥ ≤ rad f (stab Y ⊤)) le_top (hR d hdY)
    have hrk := secRank_bot_top d
    rw [(hD.2.2 d hd).2.2.2.1] at hrk
    omega
  have htR := forall_sub_mem_of_secRank_eq_zero hD.1 hR fun d hd => (hrank d hd).1
  have htF' := forall_sub_mem_of_secRank_eq_zero hD.1 hF' fun d hd => (hrank d hd).2.2.1
  have htU := forall_sub_mem_of_secRank_eq_zero hD.1 (isInv_top (Y := Y)) fun d hd =>
    (hrank d hd).2.2.2
  refine ⟨fun y hy r hr' => by simpa [sub_eq_zero] using htR y hy r hr', htF',
    fun y hy v => htU y hy v mem_top, ⟨hF', hU, inf_le_left, ?_, ?_⟩, ?_, ?_⟩
  ·
    rw [commSub_stab isInv_top]
    intro hle
    have hFN : F ≤ f.orthogonal (stab Y ⊤) := fun w hw =>
      LinearMap.BilinForm.mem_orthogonal_iff.mpr fun u hu =>
        hr _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp (hle hu).2 w hw)
    exact hFac.ne (le_antisymm hRF (le_inf hFU.le hFN))
  ·
    intro W hW hF'W hWU
    have hX : IsInv Y (F ⊓ f.orthogonal W) := hF.inf (isInv_orth hY hW)
    have hRX : rad f (stab Y ⊤) ≤ F ⊓ f.orthogonal W :=
      le_inf hRF (hRU.trans (LinearMap.BilinForm.orthogonal_le hWU))
    rcases hirrRF _ hX hRX inf_le_left with h | h
    · right
      have hperp : f.orthogonal (rad f (stab Y ⊤)) = f.orthogonal F ⊔ W := by
        rw [← h, orth_inf hf, LinearMap.BilinForm.orthogonal_orthogonal hf hr]
      have hUle : stab Y ⊤ ≤ f.orthogonal (rad f (stab Y ⊤)) := fun u hu =>
        LinearMap.BilinForm.mem_orthogonal_iff.mpr fun r hr' =>
          hr _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp hr'.2 u hu)
      rw [hperp] at hUle
      refine le_antisymm hWU ?_
      calc stab Y ⊤ = stab Y ⊤ ⊓ (f.orthogonal F ⊔ W) := (inf_eq_left.mpr hUle).symm
        _ = stab Y ⊤ ⊓ f.orthogonal F ⊔ W := (inf_sup_assoc_of_le _ hWU).symm
        _ ≤ W := sup_le hF'W le_rfl
    · left
      refine le_antisymm (le_inf hWU fun w hw =>
        LinearMap.BilinForm.mem_orthogonal_iff.mpr fun x hx => ?_) hF'W
      exact hr _ _ (LinearMap.BilinForm.mem_orthogonal_iff.mp (h.ge hx).2 w hw)
  ·
    set K := Y ⊓ secCent (rad f (stab Y ⊤)) F with hK
    have hKu : IsUnip K ⊥ ⊤ := by
      have c1 : IsUnip K ⊥ (rad f (stab Y ⊤)) :=
        isUnip_of_commSub_le (commSub_le_iff.mpr fun k hk r hr' => htR k hk.1 r hr')
      have c2 : IsUnip K (rad f (stab Y ⊤)) F :=
        isUnip_of_commSub_le (commSub_le_of_le_secCent inf_le_right)
      have c3 : IsUnip K F (stab Y ⊤ ⊓ f.orthogonal F) :=
        isUnip_of_commSub_le (commSub_le_iff.mpr fun k hk v hv => htF' k hk.1 v hv)
      have c4 : IsUnip K (stab Y ⊤ ⊓ f.orthogonal F) (stab Y ⊤) :=
        isUnip_of_commSub_le (commSub_le_iff.mpr fun k hk u hu =>
          sub_mem_inf_orth_of_forall hr hY hU hRU hk.1 (fun w hw => (K.inv_mem hk).2.2.2 w hw)
            u hu)
      have c5 : IsUnip K (stab Y ⊤) ⊤ :=
        isUnip_of_commSub_le (commSub_le_iff.mpr fun k hk v hv => htU k hk.1 v hv)
      exact (((c1.trans c2).trans c3).trans c4).trans c5
    have hKn : Y ≤ Subgroup.normalizer (K : Set (V ≃ₗ[ZMod 2] V)) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro k
      constructor
      · rintro ⟨hkY, hkS⟩
        exact ⟨Y.mul_mem (Y.mul_mem hy hkY) (Y.inv_mem hy), conj_mem_secCent hR hF hy hkS⟩
      · rintro ⟨hkY, hkS⟩
        have hk : k = y⁻¹ * (y * k * y⁻¹) * y⁻¹⁻¹ := by group
        rw [hk]
        exact ⟨Y.mul_mem (Y.mul_mem (Y.inv_mem hy) hkY) (Y.inv_mem (Y.inv_mem hy)),
          conj_mem_secCent hR hF (Y.inv_mem hy) hkS⟩
    have hK1 := hO2 K inf_le_left (isPGroup_of_isUnip hKu) hKn
    refine (injective_iff_map_eq_one _).mpr fun y hy => ?_
    have hyK : (y : V ≃ₗ[ZMod 2] V) ∈ K :=
      ⟨y.2, mem_secCent_of_isInv hF y.2 ((secHom_eq_one_iff hR hF).mp hy)⟩
    rw [hK1, Subgroup.mem_bot] at hyK
    exact Subtype.ext hyK
  ·
    have h1 : ∀ d ∈ D, secRank d (rad f (stab Y ⊤)) F = 1 := fun d hd => (hrank d hd).2.1
    obtain ⟨a, ha, b, hb, -, -, hab⟩ := h4
    obtain ⟨ht₁, ht₂, hne, ht₁₂⟩ := fourGroup_secHom hD hR hF hRF h1 ha hb hab
    have hgen := genByTransvections_secHom hD.1 hR hF fun d _ hdD =>
      isF2Transvection_secHom hR hF hRF (h1 d hdD)
    have htop := eq_top_of_fourGroup hgen (isIrreducibleOn_secHom hFac) ⟨_, rfl⟩ ⟨_, rfl⟩ ht₁
      ht₂ hne ht₁₂
    exact MonoidHom.range_eq_top.mp htop

theorem exists_bijective_secHom (hD : IsA2Class f Y D) (hO2 : S12NoNormalTwo Y)
    (h4 : HasFourGroup D) (h2 : ¬ OneFactor Y) :
    ∃ (F : Submodule (ZMod 2) V) (hR : IsInv Y (rad f (stab Y ⊤))) (hF : IsInv Y F),
      IsNontrivFactor Y (rad f (stab Y ⊤)) F ∧ F < stab Y ⊤ ∧ F ≤ f.orthogonal F ∧
      IsNontrivFactor Y (stab Y ⊤ ⊓ f.orthogonal F) (stab Y ⊤) ∧
      (∀ y ∈ Y, ∀ r ∈ rad f (stab Y ⊤), y r = r) ∧
      (∀ y ∈ Y, ∀ v ∈ stab Y ⊤ ⊓ f.orthogonal F, y v - v ∈ F) ∧
      (∀ y ∈ Y, ∀ v, y v - v ∈ stab Y ⊤) ∧
      Function.Bijective (secHom (rad f (stab Y ⊤)) F Y hR hF) := by
  obtain ⟨F, hFac, hFU, hFt⟩ := exists_minimal_factor hf halt hY hD hO2 h2
  have hRFp : rad f (stab Y ⊤) ≤ F ⊓ f.orthogonal F :=
    le_inf hFac.2.2.1 (inf_le_right.trans (LinearMap.BilinForm.orthogonal_le hFU.le))
  rcases hFac.2.2.2.2 (F ⊓ f.orthogonal F) (hFac.2.1.inf (isInv_orth hY hFac.2.1)) hRFp
      inf_le_left with h | h
  · exact (false_of_inf_orth_le halt hY hD h4 hFac hFU.le hFt h.le).elim
  · have hiso : F ≤ f.orthogonal F := h.ge.trans inf_le_right
    obtain ⟨htR, htF', htU, hfac2, hbij⟩ := bijective_of_le_orth hf halt hY hD hO2 h4 hFac hFU hiso
    exact ⟨F, hFac.1, hFac.2.1, hFac, hFU, hiso, hfac2, htR, htF', htU, hbij⟩

omit [FiniteDimensional (ZMod 2) V] hf halt hY in
theorem finrank_sec [FiniteDimensional (ZMod 2) V] {A B : Submodule (ZMod 2) V} (hAB : A ≤ B) :
    finrank (ZMod 2) (Sec A B) = finrank (ZMod 2) B - finrank (ZMod 2) A := by
  have h := finrank_map_secMk (A := A) (B := B) hAB le_rfl
  rw [Submodule.comap_subtype_self, Submodule.map_top, Submodule.range_mkQ, finrank_top] at h
  omega

end CFSG.LargeExtraspecial.DW
