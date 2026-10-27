module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerCP5

public section

namespace CFSG.QuasithinUnique.Setup.Layer

open CFSG.ABGLocalTools CFSG.LocalCores CFSG.Quasithin.B6
open scoped commutatorElement

section Main

variable {H : Type*} [Group H] [Finite H] {p : ℕ} {T M : Subgroup H} {ι : Type*} [Finite ι]
  {L : ι → Subgroup H}

theorem CPSetting.uSub_le_M (hS : CPSetting p T M L) (i₀ : ι) {Y : Subgroup (MulAut ↥(L i₀))}
    (hSY : actImg (L i₀) (normT T (L i₀)) ≤ Y) (hYA : Y < actImg (L i₀) (normL (L i₀))) :
    uSub (L i₀) Y ≤ M := by
  classical
  have : Nonempty ι := ⟨i₀⟩
  have hUL : uSub (L i₀) Y ≤ L i₀ := uSub_le
  have hZU : ∀ c ∈ L i₀, c ∈ centL (L i₀) → c ∈ uSub (L i₀) Y := by
    intro c hc hcc
    refine mem_uSub.2 ⟨hc, ?_⟩
    have : (MulAut.conj (⟨c, hc⟩ : ↥(L i₀)) : MulAut ↥(L i₀)) = 1 := by
      rw [conj_eq_one_iff, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.1 hcc) g g.2)
    rw [this]
    exact Y.one_mem
  have hnotL : ¬ L i₀ ≤ uSub (L i₀) Y := by
    intro hle
    have hD : innGroup (L i₀) ≤ Y := by
      intro a ha
      obtain ⟨l, rfl⟩ := mem_innGroup.1 ha
      exact (mem_uSub.1 (hle l.2)).2
    have : actImg (L i₀) (normL (L i₀)) ≤ Y := by
      rw [hS.actImg_normL i₀]
      exact sup_le hD hSY
    exact hYA.not_ge this
  have hTL : T ⊓ L i₀ ≤ uSub (L i₀) Y := by
    intro t ht
    refine mem_uSub.2 ⟨ht.2, ?_⟩
    have htN : t ∈ normL (L i₀) := Subgroup.le_normalizer ht.2
    have e : actOf (L i₀) t = MulAut.conj (⟨t, ht.2⟩ : ↥(L i₀)) := actOf_of_mem_self ht.2
    rw [← e]
    exact hSY (actOf_mem_actImg htN ⟨ht.1, htN⟩)
  have hTU : normT T (L i₀) ≤ Subgroup.normalizer (uSub (L i₀) Y : Set H) := by
    have key : ∀ t ∈ normT T (L i₀), ∀ u ∈ uSub (L i₀) Y, t * u * t⁻¹ ∈ uSub (L i₀) Y := by
      intro t ht u hu
      obtain ⟨hul, huY⟩ := mem_uSub.1 hu
      have htN : t ∈ normL (L i₀) := ht.2
      have htl : t * u * t⁻¹ ∈ L i₀ := (Subgroup.mem_normalizer_iff.1 htN u).1 hul
      refine mem_uSub.2 ⟨htl, ?_⟩
      rw [conj_mul_eq htN hul htl]
      have hS' : actOf (L i₀) t ∈ Y := hSY (actOf_mem_actImg htN ht)
      exact Y.mul_mem (Y.mul_mem hS' huY) (Y.inv_mem hS')
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => key t ht u hu, fun hu => ?_⟩
    have h2 := key t⁻¹ ((normT T (L i₀)).inv_mem ht) _ hu
    have e : t⁻¹ * (t * u * t⁻¹) * t⁻¹⁻¹ = u := by group
    rwa [e] at h2
  obtain ⟨B, hB⟩ : ∃ B : Subgroup H, B = ⨆ t : ↥T, conjSub (t : H) (uSub (L i₀) Y) := ⟨_, rfl⟩
  have hfB : ∀ t : ↥T, conjSub (t : H) (uSub (L i₀) Y) ≤ B := fun t => by
    rw [hB]
    exact le_iSup (fun t : ↥T => conjSub (t : H) (uSub (L i₀) Y)) t
  have hUB : uSub (L i₀) Y ≤ B := by
    have := hfB ⟨1, T.one_mem⟩
    rwa [show ((⟨1, T.one_mem⟩ : ↥T) : H) = 1 from rfl, conjSub_one] at this
  have hBK : B ≤ ⨆ i, L i := by
    rw [hB]
    refine iSup_le fun t => ?_
    have h1 : conjSub (t : H) (uSub (L i₀) Y) ≤ conjSub (t : H) (⨆ i, L i : Subgroup H) :=
      (conjSub (t : H)).monotone (hUL.trans (le_iSup L i₀))
    rwa [conjSub_eq_self (hS.T_le_normalizer_K t.2)] at h1
  have hBT : T ≤ Subgroup.normalizer (B : Set H) := by
    have hcl : ∀ s ∈ T, conjSub s B ≤ B := by
      intro s hs
      have e : conjSub s B = ⨆ t : ↥T, conjSub s (conjSub (t : H) (uSub (L i₀) Y)) := by
        rw [hB, OrderIso.map_iSup]
      rw [e]
      refine iSup_le fun t => ?_
      rw [← conjSub_mul]
      exact hfB ⟨s * t, T.mul_mem hs t.2⟩
    intro s hs
    exact mem_normalizer_of_conjSub_le (hcl s hs) (hcl s⁻¹ (T.inv_mem hs))
  have hTKB : T ⊓ (⨆ i, L i : Subgroup H) ≤ B := by
    rw [hS.T_inf_K]
    refine iSup_le fun i => ?_
    obtain ⟨t, ht, hti⟩ := hS.trans i₀ i
    have h1 : T ⊓ L i = conjSub t (T ⊓ L i₀) := by
      rw [OrderIso.map_inf, conjSub_eq_self (Subgroup.le_normalizer ht), hti]
    rw [h1]
    exact ((conjSub t).monotone hTL).trans (hfB ⟨t, ht⟩)
  have hBL : B ⊓ L i₀ ≤ uSub (L i₀) Y := by
    obtain ⟨C, hC⟩ : ∃ C : Subgroup H, C = ⨆ j : {j // j ≠ i₀}, L j := ⟨_, rfl⟩
    have hCcent : C ≤ centL (L i₀) := by
      rw [hC]
      exact iSup_le fun j => hS.centralizes j.2
    have hBle : B ≤ uSub (L i₀) Y ⊔ C := by
      rw [hB]
      refine iSup_le fun t => ?_
      obtain ⟨j, hj⟩ := hS.perm t t.2 i₀
      by_cases hji : j = i₀
      · rw [hji] at hj
        have htN : (t : H) ∈ normL (L i₀) := by
          refine mem_normalizer_of_conjSub_le (le_of_eq hj) ?_
          have : conjSub (t : H)⁻¹ (L i₀) = L i₀ := by
            calc conjSub (t : H)⁻¹ (L i₀) = conjSub (t : H)⁻¹ (conjSub (t : H) (L i₀)) := by
                  rw [hj]
              _ = L i₀ := by rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
          exact le_of_eq this
        rw [conjSub_eq_self (hTU ⟨t.2, htN⟩)]
        exact le_sup_left
      · calc conjSub (t : H) (uSub (L i₀) Y) ≤ conjSub (t : H) (L i₀) :=
            (conjSub (t : H)).monotone hUL
          _ = L j := hj
          _ ≤ C := by
            rw [hC]
            exact le_iSup (fun j : {j // j ≠ i₀} => L j) ⟨j, hji⟩
          _ ≤ uSub (L i₀) Y ⊔ C := le_sup_right
    intro b hb
    have hbU : b ∈ uSub (L i₀) Y ⊔ C := hBle hb.1
    have hCn : C ≤ Subgroup.normalizer (uSub (L i₀) Y : Set H) := by
      intro c hc
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      exact (Subgroup.mem_centralizer_iff.1 (hCcent hc)) u (hUL hu)
    obtain ⟨u, hu, c, hc, rfl⟩ := exists_mul_of_mem_sup hCn hbU
    have hcL : c ∈ L i₀ := by
      have := (L i₀).mul_mem ((L i₀).inv_mem (hUL hu)) hb.2
      simpa using this
    exact (uSub (L i₀) Y).mul_mem hu (hZU c hcL (hCcent hc))
  have hBlt : B < ⨆ i, L i := by
    refine lt_of_le_of_ne hBK fun h => hnotL ?_
    intro l hl
    refine hBL ⟨?_, hl⟩
    rw [h]
    exact le_iSup L i₀ hl
  have hproper : B ⊔ T ≠ ⊤ := by
    intro htop
    have hKB : (⨆ i, L i : Subgroup H) ≤ B := by
      intro k hk
      have hk' : k ∈ B ⊔ T := by
        rw [htop]
        trivial
      obtain ⟨b, hb, t, ht, rfl⟩ := exists_mul_of_mem_sup hBT hk'
      have htK : t ∈ T ⊓ (⨆ i, L i : Subgroup H) := by
        refine ⟨ht, ?_⟩
        have := (⨆ i, L i : Subgroup H).mul_mem ((⨆ i, L i : Subgroup H).inv_mem (hBK hb)) hk
        simpa using this
      exact B.mul_mem hb (hTKB htK)
    exact hBlt.ne (le_antisymm hBK hKB)
  have hBTM : B ⊔ T ≤ M := hS.M_max _ le_sup_right (lt_top_iff_ne_top.2 hproper)
  exact hUB.trans (le_sup_left.trans hBTM)

theorem CPSetting.le_actImg_maxL (hS : CPSetting p T M L) (i₀ : ι)
    {Y : Subgroup (MulAut ↥(L i₀))} (hSY : actImg (L i₀) (normT T (L i₀)) ≤ Y)
    (hYA : Y < actImg (L i₀) (normL (L i₀))) : Y ≤ actImg (L i₀) (maxL T M (L i₀)) := by
  have hUM := hS.uSub_le_M i₀ hSY hYA
  intro y hy
  have hyA : y ∈ actImg (L i₀) (normL (L i₀)) := hYA.le hy
  rw [hS.actImg_normL i₀] at hyA
  have hSn : actImg (L i₀) (normT T (L i₀)) ≤
      Subgroup.normalizer (innGroup (L i₀) : Set (MulAut ↥(L i₀))) :=
    (actImg_mono inf_le_right).trans (actImg_normL_le_normalizer _)
  obtain ⟨d, hd, s, hs, rfl⟩ := exists_mul_of_mem_sup hSn hyA
  have hdY : d ∈ Y := by
    have e : d = (d * s) * s⁻¹ := by group
    rw [e]
    exact Y.mul_mem hy (Y.inv_mem (hSY hs))
  obtain ⟨l, rfl⟩ := mem_innGroup.1 hd
  have hlM : (l : H) ∈ M := hUM (mem_uSub.2 ⟨l.2, hdY⟩)
  have e : actOf (L i₀) (l : H) = MulAut.conj l := actOf_of_mem_self l.2
  have hdP : MulAut.conj l ∈ actImg (L i₀) (maxL T M (L i₀)) := by
    rw [← e]
    exact actOf_mem_actImg (Subgroup.le_normalizer l.2) (Subgroup.mem_sup_left ⟨hlM, l.2⟩)
  have hsP : s ∈ actImg (L i₀) (maxL T M (L i₀)) := actImg_mono le_sup_right hs
  exact (actImg (L i₀) (maxL T M (L i₀))).mul_mem hdP hsP

end Main

end CFSG.QuasithinUnique.Setup.Layer
