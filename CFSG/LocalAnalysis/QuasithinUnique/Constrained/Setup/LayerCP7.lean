module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP6
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP4

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6
open scoped commutatorElement

section Incl

variable {H : Type*} [Group H] {T M L₀ : Subgroup H}

theorem locL_le_normL : locL T L₀ ≤ normL L₀ := sup_le Subgroup.le_normalizer inf_le_right

theorem normT_le_locL : normT T L₀ ≤ locL T L₀ := le_sup_right

theorem normT_le_maxL : normT T L₀ ≤ maxL T M L₀ := le_sup_right

theorem maxL_le_locL : maxL T M L₀ ≤ locL T L₀ := sup_le_sup_right inf_le_right _

theorem maxL_le_normL : maxL T M L₀ ≤ normL L₀ := maxL_le_locL.trans locL_le_normL

theorem comap_actImg_maxL (T M L₀ : Subgroup H) :
    (actImg L₀ (maxL T M L₀)).comap L₀.normalizerMonoidHom =
      (centL L₀ ⊔ maxL T M L₀).subgroupOf (normL L₀) := by
  ext n
  obtain ⟨n, hn⟩ := n
  have e : (L₀).normalizerMonoidHom ⟨n, hn⟩ = actOf (L₀) n := (actOf_of_mem hn).symm
  rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf, e]
  constructor
  · intro h
    obtain ⟨x, hx, hxN, hxe⟩ := mem_actImg.1 h
    have hker : n * x⁻¹ ∈ centL (L₀) := by
      rw [← actOf_eq_one_iff ((normL _).mul_mem hn ((normL _).inv_mem hxN)),
        actOf_mul hn ((normL _).inv_mem hxN), actOf_inv hxN, hxe, mul_inv_cancel]
    have e2 : n = (n * x⁻¹) * x := by group
    show n ∈ centL (L₀) ⊔ maxL T M (L₀)
    rw [e2]
    exact Subgroup.mul_mem_sup hker hx
  · intro h
    have hmN : maxL T M (L₀) ≤ Subgroup.normalizer (centL (L₀) : Set H) :=
      maxL_le_normL.trans (normL_le_normalizer_centL _)
    have h' : n ∈ centL (L₀) ⊔ maxL T M (L₀) := h
    obtain ⟨c, hc, x, hx, rfl⟩ := exists_mul_of_mem_sup hmN h'
    have hcN : c ∈ normL (L₀) := Subgroup.centralizer_le_normalizer _ hc
    have hxN : x ∈ normL (L₀) := maxL_le_normL hx
    rw [actOf_mul hcN hxN, (actOf_eq_one_iff hcN).2 hc, one_mul]
    exact actOf_mem_actImg hxN hx

end Incl

section Main

variable {H : Type*} [Group H] [Finite H] {p : ℕ} {T M : Subgroup H} {ι : Type*} [Finite ι]
  {L : ι → Subgroup H}

omit [Finite H] [Finite ι] in
theorem CPSetting.normT_le_normalizer_inf (hS : CPSetting p T M L) (i₀ : ι) :
    normT T (L i₀) ≤ Subgroup.normalizer ((M ⊓ L i₀ : Subgroup H) : Set H) := by
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have h1 := Subgroup.mem_normalizer_iff.1 (Subgroup.le_normalizer (hS.T_le_M ht.1)) h
  have h2 := Subgroup.mem_normalizer_iff.1 ht.2 h
  exact ⟨fun hh => ⟨h1.1 hh.1, h2.1 hh.2⟩, fun hh => ⟨h1.2 hh.1, h2.2 hh.2⟩⟩

omit [Finite ι] in
theorem CPSetting.actImg_maxL_inf_inn (hS : CPSetting p T M L) (i₀ : ι) :
    actImg (L i₀) (maxL T M (L i₀)) ⊓ innGroup (L i₀) = actImg (L i₀) (M ⊓ L i₀) := by
  apply le_antisymm
  · rintro d ⟨hdP, hdD⟩
    obtain ⟨x, hx, hxN, rfl⟩ := mem_actImg.1 hdP
    obtain ⟨m, hm, t, ht, rfl⟩ := exists_mul_of_mem_sup (hS.normT_le_normalizer_inf i₀) hx
    have hmN : m ∈ normL (L i₀) := Subgroup.le_normalizer hm.2
    have htN : t ∈ normL (L i₀) := ht.2
    rw [actOf_mul hmN htN] at hdD ⊢
    have hmD : actOf (L i₀) m ∈ innGroup (L i₀) := by
      rw [← actImg_self]
      exact actOf_mem_actImg hmN hm.2
    have htD : actOf (L i₀) t ∈ innGroup (L i₀) := by
      have := (innGroup (L i₀)).mul_mem ((innGroup (L i₀)).inv_mem hmD) hdD
      simpa using this
    have htS : actOf (L i₀) t ∈ actImg (L i₀) (normT T (L i₀)) := actOf_mem_actImg htN ht
    have h2 : actOf (L i₀) t ∈ actImg (L i₀) (T ⊓ L i₀) := by
      rw [← hS.actImg_inf_inn i₀]
      exact ⟨htS, htD⟩
    obtain ⟨u, hu, huN, hut⟩ := mem_actImg.1 h2
    rw [← hut, ← actOf_mul hmN huN]
    exact actOf_mem_actImg ((normL _).mul_mem hmN huN)
      ((M ⊓ L i₀).mul_mem hm ⟨hS.T_le_M hu.1, hu.2⟩)
  · refine le_inf (actImg_mono le_sup_left) ?_
    rw [← actImg_self]
    exact actImg_mono inf_le_right

omit [Finite ι] in
theorem CPSetting.actImg_maxL_lt [Nonempty ι] (hS : CPSetting p T M L) (i₀ : ι) :
    actImg (L i₀) (maxL T M (L i₀)) < actImg (L i₀) (normL (L i₀)) := by
  refine lt_of_le_of_ne (actImg_mono maxL_le_normL) fun h => ?_
  have hDP : innGroup (L i₀) ≤ actImg (L i₀) (maxL T M (L i₀)) := h ▸ innGroup_le_actImg _
  have hLM : L i₀ ≤ M := by
    intro l hl
    have hcl : (MulAut.conj (⟨l, hl⟩ : ↥(L i₀)) : MulAut ↥(L i₀)) ∈ innGroup (L i₀) :=
      mem_innGroup.2 ⟨_, rfl⟩
    have hP : (MulAut.conj (⟨l, hl⟩ : ↥(L i₀)) : MulAut ↥(L i₀)) ∈ actImg (L i₀) (M ⊓ L i₀) := by
      rw [← hS.actImg_maxL_inf_inn i₀]
      exact ⟨hDP hcl, hcl⟩
    obtain ⟨m, hm, hmN, hme⟩ := mem_actImg.1 hP
    have e1 : actOf (L i₀) m = MulAut.conj (⟨m, hm.2⟩ : ↥(L i₀)) := actOf_of_mem_self hm.2
    have hlm : (MulAut.conj (⟨l, hl⟩ : ↥(L i₀)) : MulAut ↥(L i₀)) = MulAut.conj ⟨m, hm.2⟩ :=
      hme.symm.trans e1
    have hone : (MulAut.conj ((⟨l, hl⟩ : ↥(L i₀)) * (⟨m, hm.2⟩ : ↥(L i₀))⁻¹) : MulAut ↥(L i₀)) =
        1 := by
      rw [map_mul, map_inv, hlm]
      exact mul_inv_cancel _
    have hcen := (conj_eq_one_iff _).1 hone
    have hzc : l * m⁻¹ ∈ centL (L i₀) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.1 hcen ⟨g, hg⟩
      exact congrArg Subtype.val this
    have hzL : l * m⁻¹ ∈ L i₀ := (L i₀).mul_mem hl ((L i₀).inv_mem hm.2)
    have hZ : l * m⁻¹ ∈ M := hS.Z0_le_M i₀ ⟨hzL, hzc⟩
    have e : l = (l * m⁻¹) * m := by group
    rw [e]
    exact M.mul_mem hZ hm.1
  exact (hS.inf_lt i₀).ne (inf_eq_right.2 hLM)

omit [Finite ι] in
theorem CPSetting.ker_locL (hS : CPSetting p T M L) (i₀ : ι) {h : H}
    (hh : h ∈ locL T (L i₀)) (hker : actOf (L i₀) h = 1) :
    h ∈ (L i₀ ⊓ centL (L i₀)) ⊔ normT T (L i₀) := by
  obtain ⟨l, hl, t, ht, rfl⟩ := exists_mul_of_mem_sup (inf_le_right : normT T (L i₀) ≤ _) hh
  have hlN : l ∈ normL (L i₀) := Subgroup.le_normalizer hl
  have htN : t ∈ normL (L i₀) := ht.2
  rw [actOf_mul hlN htN] at hker
  have hD : actOf (L i₀) l ∈ innGroup (L i₀) := by
    rw [← actImg_self]
    exact actOf_mem_actImg hlN hl
  have hS' : actOf (L i₀) l ∈ actImg (L i₀) (normT T (L i₀)) := by
    have e : actOf (L i₀) l = actOf (L i₀) t⁻¹ := by
      rw [actOf_inv htN]
      exact eq_inv_of_mul_eq_one_left hker
    rw [e]
    exact actOf_mem_actImg ((normL _).inv_mem htN) ((normT T (L i₀)).inv_mem ht)
  have h2 : actOf (L i₀) l ∈ actImg (L i₀) (T ⊓ L i₀) := by
    rw [← hS.actImg_inf_inn i₀]
    exact ⟨hS', hD⟩
  obtain ⟨u, hu, huN, hul⟩ := mem_actImg.1 h2
  have hzN : l * u⁻¹ ∈ normL (L i₀) := (normL _).mul_mem hlN ((normL _).inv_mem huN)
  have hzc : l * u⁻¹ ∈ centL (L i₀) := by
    rw [← actOf_eq_one_iff hzN, actOf_mul hlN ((normL _).inv_mem huN), actOf_inv huN, hul,
      mul_inv_cancel]
  have hzL : l * u⁻¹ ∈ L i₀ := (L i₀).mul_mem hl ((L i₀).inv_mem hu.2)
  have e2 : l * t = (l * u⁻¹) * (u * t) := by group
  rw [e2]
  exact Subgroup.mul_mem_sup ⟨hzL, hzc⟩ ((normT T (L i₀)).mul_mem ⟨hu.1, huN⟩ ht)

omit [Finite ι] in
theorem CPSetting.ker_locL_mem_maxL [Nonempty ι] (hS : CPSetting p T M L) (i₀ : ι) {h : H}
    (hh : h ∈ locL T (L i₀)) (hker : actOf (L i₀) h = 1) : h ∈ maxL T M (L i₀) :=
  (sup_le_sup_right (le_inf (hS.Z0_le_M i₀) inf_le_left) _) (hS.ker_locL i₀ hh hker)

theorem CPSetting.maxL_unique [Nonempty ι] (hS : CPSetting p T M L) (i₀ : ι) {Y : Subgroup H}
    (hYH : Y ≤ locL T (L i₀)) (hTY : normT T (L i₀) ≤ Y) (hYlt : Y < locL T (L i₀)) :
    Y ≤ maxL T M (L i₀) := by
  have hZ0L : L i₀ ⊓ centL (L i₀) ≤ L i₀ := inf_le_left
  have hZ0c : ∀ z ∈ L i₀ ⊓ centL (L i₀), ∀ x ∈ L i₀, z * x = x * z :=
    fun z hz x hx => ((Subgroup.mem_centralizer_iff.1 hz.2) x hx).symm
  have hYn : Y ≤ Subgroup.normalizer ((L i₀ ⊓ centL (L i₀) : Subgroup H) : Set H) :=
    hYH.trans (locL_le_normL.trans (normL_le_normalizer_Z0 _))
  obtain ⟨Y', hY'⟩ : ∃ Y' : Subgroup H, Y' = (L i₀ ⊓ centL (L i₀)) ⊔ Y := ⟨_, rfl⟩
  have hZY' : L i₀ ⊓ centL (L i₀) ≤ Y' := hY' ▸ le_sup_left
  have hYY' : Y ≤ Y' := hY' ▸ le_sup_right
  have hY'loc : Y' ≤ locL T (L i₀) := hY' ▸ sup_le (hZ0L.trans le_sup_left) hYH
  have hA : Y' ≠ locL T (L i₀) := by
    intro hEq
    have hperf : ⁅L i₀, L i₀⁆ = L i₀ := Subgroup.isPerfect_iff.1 (hS.qs i₀).1
    have hLY : L i₀ ≤ Y := by
      have hcomm : ⁅L i₀, L i₀⁆ ≤ Y := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        have ha' : a ∈ (L i₀ ⊓ centL (L i₀)) ⊔ Y := by
          rw [← hY', hEq]
          exact (le_sup_left : L i₀ ≤ locL T (L i₀)) ha
        have hb' : b ∈ (L i₀ ⊓ centL (L i₀)) ⊔ Y := by
          rw [← hY', hEq]
          exact (le_sup_left : L i₀ ≤ locL T (L i₀)) hb
        obtain ⟨z₁, hz₁, y₁, hy₁, rfl⟩ := exists_mul_of_mem_sup hYn ha'
        obtain ⟨z₂, hz₂, y₂, hy₂, rfl⟩ := exists_mul_of_mem_sup hYn hb'
        have hy₁L : y₁ ∈ L i₀ := by
          have := (L i₀).mul_mem ((L i₀).inv_mem (hZ0L hz₁)) ha
          simpa using this
        have hy₂L : y₂ ∈ L i₀ := by
          have := (L i₀).mul_mem ((L i₀).inv_mem (hZ0L hz₂)) hb
          simpa using this
        rw [commutator_mul_mul_of_commute (hZ0c z₁ hz₁ y₁ hy₁L) (hZ0c z₁ hz₁ y₂ hy₂L)
          (hZ0c z₂ hz₂ y₁ hy₁L) (hZ0c z₂ hz₂ y₂ hy₂L) (hZ0c z₁ hz₁ z₂ (hZ0L hz₂)),
          commutatorElement_def]
        exact Y.mul_mem (Y.mul_mem (Y.mul_mem hy₁ hy₂) (Y.inv_mem hy₁)) (Y.inv_mem hy₂)
      rwa [hperf] at hcomm
    exact hYlt.not_ge (sup_le hLY hTY)
  have hB : actImg (L i₀) Y' < actImg (L i₀) (normL (L i₀)) := by
    refine lt_of_le_of_ne (actImg_mono (hY'loc.trans locL_le_normL)) fun hEq => hA ?_
    apply le_antisymm hY'loc
    intro h hh
    have hhN : h ∈ normL (L i₀) := locL_le_normL hh
    have hmem : actOf (L i₀) h ∈ actImg (L i₀) Y' := by
      rw [hEq]
      exact actOf_mem_actImg hhN hhN
    obtain ⟨y, hy, hyN, hye⟩ := mem_actImg.1 hmem
    have hkerm : h * y⁻¹ ∈ locL T (L i₀) :=
      (locL T (L i₀)).mul_mem hh ((locL T (L i₀)).inv_mem (hY'loc hy))
    have hker : actOf (L i₀) (h * y⁻¹) = 1 := by
      rw [actOf_mul hhN ((normL _).inv_mem hyN), actOf_inv hyN, hye, mul_inv_cancel]
    have h3 : h * y⁻¹ ∈ Y' :=
      (sup_le hZY' (hTY.trans (hYY'.trans' le_rfl))) (hS.ker_locL i₀ hkerm hker)
    have e : h = (h * y⁻¹) * y := by group
    rw [e]
    exact Y'.mul_mem h3 hy
  have hSY' : actImg (L i₀) (normT T (L i₀)) ≤ actImg (L i₀) Y' :=
    actImg_mono (hTY.trans hYY')
  have hle := hS.le_actImg_maxL i₀ hSY' hB
  intro y hy
  have hy' : y ∈ Y' := hYY' hy
  have hyN : y ∈ normL (L i₀) := locL_le_normL (hY'loc hy')
  obtain ⟨x, hx, hxN, hxe⟩ := mem_actImg.1 (hle (actOf_mem_actImg hyN hy'))
  have hkerm : y * x⁻¹ ∈ locL T (L i₀) :=
    (locL T (L i₀)).mul_mem (hY'loc hy') ((locL T (L i₀)).inv_mem (maxL_le_locL hx))
  have hker : actOf (L i₀) (y * x⁻¹) = 1 := by
    rw [actOf_mul hyN ((normL _).inv_mem hxN), actOf_inv hxN, hxe, mul_inv_cancel]
  have hmem := hS.ker_locL_mem_maxL i₀ hkerm hker
  have e : y = (y * x⁻¹) * x := by group
  rw [e]
  exact (maxL T M (L i₀)).mul_mem hmem hx

omit [Finite ι] in
theorem CPSetting.maxL_lt_locL [Nonempty ι] (hS : CPSetting p T M L) (i₀ : ι) :
    maxL T M (L i₀) < locL T (L i₀) := by
  refine lt_of_le_of_ne maxL_le_locL fun h => ?_
  have h1 : actImg (L i₀) (maxL T M (L i₀)) = actImg (L i₀) (normL (L i₀)) := by
    rw [h, ← hS.actImg_normL_eq_locL i₀]
  exact (hS.actImg_maxL_lt i₀).ne h1

omit [Finite ι] in
theorem CPSetting.normT_not_normal_locL [Nonempty ι] (hS : CPSetting p T M L) (i₀ : ι)
    {E : Subgroup H} (hEp : IsPGroup p ↥E) (hEn : E ≤ normL (L i₀)) (hEc : ⁅L i₀, E⁆ ≠ ⊥) :
    ¬ ((normT T (L i₀)).subgroupOf (locL T (L i₀))).Normal := by
  intro hn
  apply hS.actImg_normT_not_normal i₀ hEp hEn hEc
  have hSA : actImg (L i₀) (normT T (L i₀)) ≤ actImg (L i₀) (normL (L i₀)) :=
    actImg_mono inf_le_right
  refine (Subgroup.normal_subgroupOf_iff hSA).2 fun s a hs ha => ?_
  rw [hS.actImg_normL_eq_locL i₀] at ha
  obtain ⟨h, hh, hhN, rfl⟩ := mem_actImg.1 ha
  obtain ⟨t, ht, htN, rfl⟩ := mem_actImg.1 hs
  have htn : h * t * h⁻¹ ∈ normT T (L i₀) :=
    (Subgroup.normal_subgroupOf_iff normT_le_locL).1 hn t h ht hh
  have e : actOf (L i₀) h * actOf (L i₀) t * (actOf (L i₀) h)⁻¹ = actOf (L i₀) (h * t * h⁻¹) := by
    rw [actOf_mul ((normL _).mul_mem hhN htN) ((normL _).inv_mem hhN), actOf_mul hhN htN,
      actOf_inv hhN]
  rw [e]
  exact actOf_mem_actImg ((normL _).mul_mem ((normL _).mul_mem hhN htN) ((normL _).inv_mem hhN)) htn

end Main

end CFSG.QuasithinUnique.Setup.Layer
