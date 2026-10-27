module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D1Def
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D1Pair
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec8T84D2Rho

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint
open CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

variable {G : Type} [Group G] [Finite G] {t : G} {E X1 X2 : Subgroup G}

private theorem mem_centralizer_of_conj_eq {Y : Subgroup G} {x : G}
    (h : ∀ e ∈ Y, x * e * x⁻¹ = e) : x ∈ centralizer (Y : Set G) := by
  rw [mem_centralizer_iff]
  intro e he
  have h' := h e he
  have hx : x * e = e * x := by
    calc x * e = (x * e * x⁻¹) * x := by group
      _ = e * x := by rw [h']
  exact hx.symm

private theorem isElemAbelian_map_subtype {Y : Subgroup G} {Y' : Subgroup ↥Y}
    (hY : CFSG.Open.IsElemAbelian 2 Y) : CFSG.Open.IsElemAbelian 2 (Y'.map Y.subtype) := by
  refine ⟨IsMulCommutative.of_comm (fun a b => ?_), fun x hx => ?_⟩
  · apply Subtype.ext
    have ha : (a : G) ∈ Y := Subgroup.map_subtype_le Y' a.2
    have hb : (b : G) ∈ Y := Subgroup.map_subtype_le Y' b.2
    simpa using congrArg (Subtype.val : ↥Y → G)
      (hY.1.is_comm.comm ⟨(a : G), ha⟩ ⟨(b : G), hb⟩)
  · exact hY.2 x (Subgroup.map_subtype_le Y' hx)

private theorem sec8t84d2_faith_aux {Y : Subgroup G} {F1' F2' : Subgroup ↥E}
    (hY : Y ≤ normalizer (E : Set G)) (hsup : F1' ⊔ F2' = ⊤)
    (htriv : ∀ a ∈ autIn Y E, ∀ x ∈ F2', a x = x)
    {x : G} (hx : x ∈ Y) (hfix : ∀ e ∈ F1'.map E.subtype, x * e * x⁻¹ = e) :
    x ∈ centralizer (E : Set G) := by
  obtain ⟨a, ha, hae⟩ := sec8t84d2_conj_mem hY hx
  have h1 : F1' ≤ fixSub a := by
    intro e' he'
    rw [mem_fixSub]
    apply Subtype.ext
    have h := hfix (e' : G) (Subgroup.mem_map_of_mem E.subtype he')
    rw [hae e']
    exact h
  have h2 : F2' ≤ fixSub a := by
    intro e' he'
    rw [mem_fixSub]
    exact htriv a ha e' he'
  have htop : fixSub a = ⊤ := by
    rw [eq_top_iff, ← hsup]
    exact sup_le h1 h2
  have ha1 : a = 1 := MulEquiv.ext (fun e => by
    have he : e ∈ fixSub a := by rw [htop]; exact Subgroup.mem_top e
    simpa using (mem_fixSub.mp he))
  apply mem_centralizer_of_conj_eq
  intro e he
  have h := hae ⟨e, he⟩
  rw [ha1] at h
  simpa using h.symm

private theorem sec8t84d2_swap_aux {Y Y' : Subgroup G} {F1' F2' : Subgroup ↥E}
    (hY' : Y' ≤ normalizer (E : Set G)) (htN : t ∈ normalizer (E : Set G)) (htsq : t * t = 1)
    (hswap : ∀ a ∈ Y, t * a * t⁻¹ ∈ Y')
    (hfix : ∀ x : ↥E, (∀ a ∈ autIn Y E, a x = x) → x ∈ F2')
    (htriv : ∀ b ∈ autIn Y' E, ∀ x ∈ F1', b x = x) :
    ∀ e ∈ F1'.map E.subtype, t * e * t⁻¹ ∈ F2'.map E.subtype := by
  intro e he
  obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htsq
  have hmem : t * (e' : G) * t⁻¹ ∈ E := (mem_normalizer_iff.mp htN (e' : G)).mp e'.2
  let f : ↥E := ⟨t * (e' : G) * t⁻¹, hmem⟩
  have hffix : ∀ a ∈ autIn Y E, a f = f := by
    intro a ha
    obtain ⟨x, hx, hae⟩ := sec8t84d2_mem_autIn ha
    have hy : t⁻¹ * x * t ∈ Y' := by simpa [htinv] using hswap x hx
    obtain ⟨b, hb, hbx⟩ := sec8t84d2_conj_mem hY' hy
    have hbe : ((b e' : ↥E) : G) = (e' : G) := congrArg Subtype.val (htriv b hb e' he')
    have hye : (t⁻¹ * x * t) * (e' : G) * (t⁻¹ * x * t)⁻¹ = (e' : G) := by
      rw [← hbx e']; exact hbe
    have hxfx : x * (t * (e' : G) * t⁻¹) * x⁻¹ = t * (e' : G) * t⁻¹ := by
      have h := congrArg (fun z => t * z * t⁻¹) hye
      calc x * (t * (e' : G) * t⁻¹) * x⁻¹
          = t * ((t⁻¹ * x * t) * (e' : G) * (t⁻¹ * x * t)⁻¹) * t⁻¹ := by group
        _ = t * (e' : G) * t⁻¹ := by rw [h]
    apply Subtype.ext
    rw [hae f]
    exact hxfx
  exact Subgroup.mem_map_of_mem E.subtype (hfix f hffix)

theorem sec8t84d2_dec_of_dec33 (h : Sec8T84DCtx G t E X1 X2) {E1' E2' : Subgroup ↥E}
    (h33 : Sec8T84Dec33 (autIn X1 E) (autIn X2 E) E1' E2') :
    Sec8T84DDec G t E X1 X2 (E1'.map E.subtype) (E2'.map E.subtype) := by
  have htN : t ∈ normalizer (E : Set G) := by
    have hmem : t ∈ X1 ⊔ X2 ⊔ zpowers t := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
    rwa [h.hX.sup] at hmem
  refine
    { le1 := Subgroup.map_subtype_le E1'
      le2 := Subgroup.map_subtype_le E2'
      e16_1 := ⟨isElemAbelian_map_subtype h.elem.1,
        by rw [Subgroup.card_subtype E E1']; exact h33.card1⟩
      e16_2 := ⟨isElemAbelian_map_subtype h.elem.1,
        by rw [Subgroup.card_subtype E E2']; exact h33.card2⟩
      inf := by
        rw [← Subgroup.map_inf_eq E1' E2' E.subtype E.subtype_injective, h33.inf,
          Subgroup.map_bot]
      sup := by
        rw [← Subgroup.map_sup E1' E2' E.subtype, h33.sup, Subgroup.map_top,
          Subgroup.range_subtype]
      inv1 := fun x hx e he => by
        obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
        obtain ⟨a, ha, hae⟩ := sec8t84d2_conj_mem h.hX.le1 hx
        simp only [Subgroup.coe_subtype]
        rw [← hae e']
        exact Subgroup.mem_map_of_mem E.subtype (h33.inv1 a ha e' he')
      inv2 := fun x hx e he => by
        obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
        obtain ⟨a, ha, hae⟩ := sec8t84d2_conj_mem h.hX.le2 hx
        simp only [Subgroup.coe_subtype]
        rw [← hae e']
        exact Subgroup.mem_map_of_mem E.subtype (h33.inv2 a ha e' he')
      triv1 := fun x hx e he => by
        obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
        obtain ⟨a, ha, hae⟩ := sec8t84d2_conj_mem h.hX.le1 hx
        simp only [Subgroup.coe_subtype]
        rw [← hae e', h33.triv1 a ha e' he']
      triv2 := fun x hx e he => by
        obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
        obtain ⟨a, ha, hae⟩ := sec8t84d2_conj_mem h.hX.le2 hx
        simp only [Subgroup.coe_subtype]
        rw [← hae e', h33.triv2 a ha e' he']
      faith1 := fun x hx hfix => sec8t84d2_faith_aux h.hX.le1 h33.sup h33.triv1 hx hfix
      faith2 := fun x hx hfix =>
        sec8t84d2_faith_aux h.hX.le2 (by rw [sup_comm]; exact h33.sup) h33.triv2 hx hfix
      fpf1 := fun x hx hx5 hxnot e he hefix => by
        obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
        obtain ⟨a, ha, hae⟩ := sec8t84d2_conj_mem h.hX.le1 hx
        have hord : orderOf a = 5 :=
          (sec8t84d2_orderOf_five_iff (h.hX.le1 hx) hae).mpr ⟨hx5, hxnot⟩
        have heq : a e' = e' := by
          apply Subtype.ext
          rw [hae e']
          exact hefix
        exact congrArg Subtype.val (h33.fpf1 a ha hord e' he' heq)
      fpf2 := fun x hx hx5 hxnot e he hefix => by
        obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.mp he
        obtain ⟨a, ha, hae⟩ := sec8t84d2_conj_mem h.hX.le2 hx
        have hord : orderOf a = 5 :=
          (sec8t84d2_orderOf_five_iff (h.hX.le2 hx) hae).mpr ⟨hx5, hxnot⟩
        have heq : a e' = e' := by
          apply Subtype.ext
          rw [hae e']
          exact hefix
        exact congrArg Subtype.val (h33.fpf2 a ha hord e' he' heq)
      ex5_1 := by
        obtain ⟨a, ha, ha5⟩ := sec8t84d1_exists_order5
          (A := autIn X1 E) (sec8t84d2_equiv h.hX.le1 h.hX.c_le1 h.hX.quot1)
        obtain ⟨x, hx, hae⟩ := sec8t84d2_mem_autIn ha
        exact ⟨x, hx, (sec8t84d2_orderOf_five_iff (h.hX.le1 hx) hae).mp ha5⟩
      ex5_2 := by
        obtain ⟨a, ha, ha5⟩ := sec8t84d1_exists_order5
          (A := autIn X2 E) (sec8t84d2_equiv h.hX.le2 h.hX.c_le2 h.hX.quot2)
        obtain ⟨x, hx, hae⟩ := sec8t84d2_mem_autIn ha
        exact ⟨x, hx, (sec8t84d2_orderOf_five_iff (h.hX.le2 hx) hae).mp ha5⟩
      trans1 := fun v hv hv1 w hw hw1 => by
        obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
        obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
        obtain ⟨a, ha, hav⟩ :=
          h33.trans1 v' hv' (fun h => hv1 (by simpa [h])) w' hw'
            (fun h => hw1 (by simpa [h]))
        obtain ⟨x, hx, hae⟩ := sec8t84d2_mem_autIn ha
        refine ⟨x, hx, ?_⟩
        simp only [Subgroup.coe_subtype]
        rw [← hae v', hav]
      trans2 := fun v hv hv1 w hw hw1 => by
        obtain ⟨v', hv', rfl⟩ := Subgroup.mem_map.mp hv
        obtain ⟨w', hw', rfl⟩ := Subgroup.mem_map.mp hw
        obtain ⟨a, ha, hav⟩ :=
          h33.trans2 v' hv' (fun h => hv1 (by simpa [h])) w' hw'
            (fun h => hw1 (by simpa [h]))
        obtain ⟨x, hx, hae⟩ := sec8t84d2_mem_autIn ha
        refine ⟨x, hx, ?_⟩
        simp only [Subgroup.coe_subtype]
        rw [← hae v', hav]
      swap1 := sec8t84d2_swap_aux h.hX.le2 htN h.t_sq h.hX.swap1 h33.fix1 h33.triv2
      swap2 := sec8t84d2_swap_aux h.hX.le1 htN h.t_sq h.hX.swap2 h33.fix2 h33.triv1 }

end CFSG.OddStandard.SmallF3.Omega
