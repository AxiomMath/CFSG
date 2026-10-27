module

public import CFSG.LocalAnalysis.SeitzReduction.RankOneProjectiveEightStageZero
public import CFSG.LocalAnalysis.SeitzReduction.RankOneStageTransportQuot

public section

namespace CFSG.SeitzReduction.RankOne

open Equiv Subgroup DegreeEight CFSG.LocalAnalysis CFSG.LocalAnalysis.SteinbergBV
  CFSG.LocalAnalysis.SteinbergBX
open scoped LinearAlgebra.Projectivization

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

theorem RelSmallRootStage.exists_conj_eq_mul {N W R X U P : Subgroup G} {n : ℕ} {t : G}
    [(W.subgroupOf N).Normal] (hst : RelSmallRootStage N W R X U P n)
    (h3 : 3 ≤ (gmsRootConjugates (relImg N W U ⊔ relImg N W R) (relImg N W R)).ncard)
    (htR : t ∈ R) (htW : t ∉ W) (hW : ∀ w ∈ W, ∃ g : G, g⁻¹ * t * g = t * w) :
    ∀ u ∈ U, ∃ g : G, g⁻¹ * t * g = t * u := by
  intro u hu
  obtain ⟨-, -, -, hWU, -, hRN, -, hUN, -, hS⟩ := hst
  have hS := @hS inferInstance
  have hWN : W ≤ N := hWU.trans hUN
  set t' : N := ⟨t, hRN htR⟩ with ht'
  set u' : N := ⟨u, hUN hu⟩ with hu'
  have ht'R : QuotientGroup.mk' (W.subgroupOf N) t' ∈ relImg N W R := relMk_mem_relImg _ htR
  have ht'1 : QuotientGroup.mk' (W.subgroupOf N) t' ≠ 1 := fun h1 =>
    htW ((relMk_eq_one_iff _).mp h1)
  have hSet := hS.setup h3 ht'R ht'1
  have hu'U : QuotientGroup.mk' (W.subgroupOf N) u' ∈ relImg N W U := relMk_mem_relImg _ hu
  obtain ⟨gb, hgQ, -⟩ := hSet.zpowers_mul_t_mem hu'U
  have h1 : QuotientGroup.mk' (W.subgroupOf N) u' * QuotientGroup.mk' (W.subgroupOf N) t' ∈
      (relImg N W R).map (MulAut.conj gb⁻¹).toMonoidHom := hgQ ▸ mem_zpowers _
  obtain ⟨r, hr, hrut⟩ := h1
  have hgb : gb⁻¹ * QuotientGroup.mk' (W.subgroupOf N) t' * gb =
      QuotientGroup.mk' (W.subgroupOf N) t' * QuotientGroup.mk' (W.subgroupOf N) u' := by
    rcases hSet.eq_one_or_eq_t hr with rfl | rfl
    · exfalso
      apply hSet.mul_t_ne_one hu'U
      rw [← hrut]
      simp
    · rw [← hSet.commute_t hu'U, ← hrut]
      simp
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (W.subgroupOf N) gb
  have hw₀ : (g⁻¹ * t' * g)⁻¹ * (t' * u') ∈ W.subgroupOf N := by
    rw [← QuotientGroup.eq]
    simpa [map_mul, map_inv] using hgb
  rw [mem_subgroupOf] at hw₀
  set w₀ : G := ((g : G)⁻¹ * t * g)⁻¹ * (t * u) with hw₀def
  have hw₀W : w₀ ∈ W := by simpa [hw₀def, ht', hu'] using hw₀
  have hgw : (g : G) * w₀ * (g : G)⁻¹ ∈ W := by
    have h2 := (inferInstance : (W.subgroupOf N).Normal).conj_mem ⟨w₀, hWN hw₀W⟩
      (mem_subgroupOf.mpr hw₀W) g
    rw [mem_subgroupOf] at h2
    simpa using h2
  obtain ⟨h, hh⟩ := hW _ hgw
  refine ⟨h * g, ?_⟩
  have e1 : t * u = ((g : G)⁻¹ * t * g) * w₀ := by rw [hw₀def]; group
  rw [e1]
  calc (h * (g : G))⁻¹ * t * (h * g) = (g : G)⁻¹ * (h⁻¹ * t * h) * g := by group
    _ = (g : G)⁻¹ * (t * ((g : G) * w₀ * (g : G)⁻¹)) * g := by rw [hh]
    _ = (g : G)⁻¹ * t * g * w₀ := by group

omit [Finite G] in
theorem inv_of_forall_conj_eq_mul {U : Subgroup G} {t : G} (htt : t * t = 1)
    (hconj : ∀ u ∈ U, ∃ g : G, g⁻¹ * t * g = t * u) : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹ := by
  intro u hu
  obtain ⟨g, hg⟩ := hconj u hu
  have h1 : (t * u) * (t * u) = 1 := by
    rw [← hg]
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [htt]; group
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  rw [htinv]
  calc t * u * t = (t * u * t) * (u * u⁻¹) := by group
    _ = ((t * u) * (t * u)) * u⁻¹ := by group
    _ = u⁻¹ := by rw [h1, one_mul]

omit [Finite G] in
theorem comm_of_forall_conj_eq_inv {U : Subgroup G} {t : G} (hinv : ∀ u ∈ U, t * u * t⁻¹ = u⁻¹) :
    ∀ a ∈ U, ∀ b ∈ U, a * b = b * a := by
  intro a ha b hb
  have h1 := hinv _ (mul_mem ha hb)
  have h2 : t * (a * b) * t⁻¹ = (t * a * t⁻¹) * (t * b * t⁻¹) := by group
  rw [h2, hinv a ha, hinv b hb] at h1
  have h3 : (a * b)⁻¹ = (b * a)⁻¹ := by rw [← h1, mul_inv_rev]
  exact inv_injective h3

theorem ncard_eq_eight_of_projectiveEight {D : Type} [Group D] {U R : Subgroup D}
    (hproj : GMSProjectiveEight U R) : (gmsRootConjugates (U ⊔ R) R).ncard = 8 := by
  obtain ⟨β, -⟩ := hproj
  rw [← Nat.card_coe_set_eq, Nat.card_congr (β.trans projEquiv.symm), Finite.card_option,
    Nat.card_zmod]

theorem exists_normal_index_two_of_relSmallRootStage_projectiveEight
    {N W X U P : Subgroup G} {t : G} [(W.subgroupOf N).Normal]
    (hst : RelSmallRootStage N W (W ⊔ zpowers t) X U P 3)
    (hproj : GMSProjectiveEight (relImg N W U) (relImg N W (W ⊔ zpowers t)))
    (htt : t * t = 1) (hW2 : IsPGroup 2 W) (hW : ∀ w ∈ W, ∃ g : G, g⁻¹ * t * g = t * w)
    (hN : normalizer (U : Set G) ≤ N) (hUt : ∀ u ∈ U, u * t = t * u → u ∈ W)
    (hCt : ∀ x : G, x * t = t * x → (∃ j : ℕ, x ^ 2 ^ j = 1) → x * x = 1) :
    ∃ M : Subgroup G, M.Normal ∧ M.index = 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, hWU, -, hRN, -, hUN, -, hS⟩ := id hst
  have hS := @hS inferInstance
  have htR : t ∈ W ⊔ zpowers t := mem_sup_right (mem_zpowers t)
  have htN : t ∈ N := hRN htR
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have htW : t ∉ W := by
    intro htW
    have h1 := hS.card_eq_two
    rw [sup_eq_left.mpr (zpowers_le.mpr htW), relImg_eq_bot_of_le le_rfl, card_bot] at h1
    exact absurd h1 (by norm_num)
  have ht1 : t ≠ 1 := fun h1 => htW (h1 ▸ one_mem W)
  have h3 : 3 ≤ (gmsRootConjugates (relImg N W U ⊔ relImg N W (W ⊔ zpowers t))
      (relImg N W (W ⊔ zpowers t))).ncard := by
    rw [ncard_eq_eight_of_projectiveEight hproj]
    norm_num
  set tb := QuotientGroup.mk' (W.subgroupOf N) (⟨t, htN⟩ : N) with htb
  have htbR : tb ∈ relImg N W (W ⊔ zpowers t) := relMk_mem_relImg _ htR
  have htb1 : tb ≠ 1 := fun h1 => htW ((relMk_eq_one_iff _).mp h1)
  have hSet := hS.setup h3 htbR htb1
  have hC := hS.normalizer_inf_centralizer
  have hconjtU := hst.exists_conj_eq_mul h3 htR htW hW
  have hinv := inv_of_forall_conj_eq_mul htt hconjtU
  have hUab := comm_of_forall_conj_eq_inv hinv
  have htNU : t ∈ normalizer (U : Set G) := by
    rw [mem_normalizer_iff]
    intro u
    refine ⟨fun hu => by rw [hinv u hu]; exact inv_mem hu, fun hu => ?_⟩
    have h1 := hinv _ hu
    have h2 : t * (t * u * t⁻¹) * t⁻¹ = u := by
      rw [htinv]
      calc t * (t * u * t) * t = (t * t) * u * (t * t) := by group
        _ = u := by rw [htt, one_mul, mul_one]
    rw [h2] at h1
    rw [h1]
    exact inv_mem hu
  have hUbcard : Nat.card (relImg N W U) = 2 ^ 3 := hS.1.2.2.2.2.1.2.2.2
  have hU2 : IsPGroup 2 U := isPGroup_of_relImg hW2 hWU hUN (IsPGroup.of_card hUbcard)
  have hex : ∃ u₀ ∈ U, u₀ ∉ W := by
    have : Nontrivial (relImg N W U) :=
      Finite.one_lt_card_iff_nontrivial.mp (by rw [hUbcard]; norm_num)
    obtain ⟨⟨ub, hub⟩, hub1⟩ := exists_ne (1 : relImg N W U)
    obtain ⟨x, hxU, rfl⟩ := exists_of_mem_relImg hub
    exact ⟨x, hxU, fun hxW => hub1 (Subtype.ext ((relMk_eq_one_iff x).mpr hxW))⟩
  have hinvW : ∀ u ∈ U, u * u = 1 → u ∈ W := by
    intro u hu huu
    apply hUt u hu
    have h1 := hinv u hu
    rw [inv_eq_of_mul_eq_one_right huu] at h1
    calc u * t = t * u * t⁻¹ * t := by rw [h1]
      _ = t * u := by group
  have hsqW : ∀ u ∈ U, u * u ∈ W := by
    intro u hu
    have h1 := gms_sq_V hS.1 _ (mem_sup_left (relMk_mem_relImg (W := W) ⟨u, hUN hu⟩ hu))
    rw [sq, ← map_mul, relMk_eq_one_iff] at h1
    simpa using h1
  have hconjU : ∀ g : G, g⁻¹ * t * g ∉ U := by
    intro g hg
    obtain ⟨u₀, hu₀, hu₀W⟩ := hex
    have hc := hUab _ hg u₀ hu₀
    have h1 : (g * u₀ * g⁻¹) * t = t * (g * u₀ * g⁻¹) := by
      calc (g * u₀ * g⁻¹) * t = g * (u₀ * (g⁻¹ * t * g)) * g⁻¹ := by group
        _ = g * ((g⁻¹ * t * g) * u₀) * g⁻¹ := by rw [← hc]
        _ = t * (g * u₀ * g⁻¹) := by group
    have h2 : ∃ j : ℕ, (g * u₀ * g⁻¹) ^ 2 ^ j = 1 := by
      obtain ⟨j, hj⟩ := hU2 ⟨u₀, hu₀⟩
      have hj' : u₀ ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
      exact ⟨j, by rw [conj_pow, hj']; group⟩
    have h3 := hCt _ h1 h2
    apply hu₀W
    apply hinvW u₀ hu₀
    calc u₀ * u₀ = g⁻¹ * ((g * u₀ * g⁻¹) * (g * u₀ * g⁻¹)) * g := by group
      _ = 1 := by rw [h3]; group
  have htU : t ∉ U := fun h1 => hconjU 1 (by simpa using h1)
  set V : Subgroup G := U ⊔ zpowers t with hVdef
  have hzU : zpowers t ≤ normalizer (U : Set G) := zpowers_le.mpr htNU
  have hVU : ∀ v ∈ V, v ∉ U → t * v ∈ U := by
    intro v hv hvU
    obtain ⟨u, hu, h1 | h1⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt hzU hv
    · exact absurd (h1 ▸ hu) hvU
    · rw [← h1]
      have h2 : t * (u * t) = t * u * t⁻¹ := by rw [htinv]; group
      rw [h2, hinv u hu]
      exact inv_mem hu
  have hsqV : ∀ v ∈ V, v * v ∈ U := by
    intro v hv
    obtain ⟨u, hu, h1 | h1⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt hzU hv
    · rw [← h1]; exact mul_mem hu hu
    · rw [← h1]
      have h2 : u * t * (u * t) = u * (t * u * t⁻¹) := by rw [htinv]; group
      rw [h2, hinv u hu, mul_inv_cancel]
      exact one_mem U
  have hot : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact htt) ht1
  have hz2 : IsPGroup 2 (zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hot, pow_one])
  have hV2 : IsPGroup 2 V := IsPGroup.to_sup_of_normal_left' hU2 hz2 hzU
  have hmapU : ∀ g ∈ normalizer (V : Set G), ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hg u hu
    have h1 : g * u * g⁻¹ ∈ V := (mem_normalizer_iff.mp hg u).mp (mem_sup_left hu)
    obtain ⟨u', hu', h2 | h2⟩ := Endings.exists_eq_or_eq_mul_of_mem_sup_zpowers htt hzU h1
    · rw [← h2]; exact hu'
    · exfalso
      obtain ⟨k, hk⟩ := hconjtU _ (inv_mem hu')
      have h3 : u' * t = t * u'⁻¹ := by
        calc u' * t = (t * t) * u' * t := by rw [htt, one_mul]
          _ = t * (t * u' * t⁻¹) := by rw [htinv]; group
          _ = t * u'⁻¹ := by rw [hinv u' hu']
      apply hconjU (k * g)
      have h4 : (k * g)⁻¹ * t * (k * g) = u :=
        calc (k * g)⁻¹ * t * (k * g) = g⁻¹ * (k⁻¹ * t * k) * g := by group
          _ = g⁻¹ * (g * u * g⁻¹) * g := by rw [hk, ← h3, h2]
          _ = u := by group
      rw [h4]
      exact hu
  have hUn : normalizer (V : Set G) ≤ normalizer (U : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro u
    refine ⟨hmapU g hg u, fun hu => ?_⟩
    have h1 := hmapU g⁻¹ (inv_mem hg) _ hu
    rwa [show g⁻¹ * (g * u * g⁻¹) * g⁻¹⁻¹ = u by group] at h1
  have hNV : normalizer (V : Set G) ≤ N := hUn.trans hN
  have hWV : W ≤ V := hWU.trans le_sup_left
  have hVN : V ≤ N := sup_le hUN (zpowers_le.mpr htN)
  have hrelV : relImg N W V = relImg N W U ⊔ relImg N W (W ⊔ zpowers t) := by
    rw [← relImg_sup hUN hRN, hVdef, ← sup_assoc, sup_eq_left.mpr hWU]
  let ψ : normalizer (V : Set G) →* normalizer ((relImg N W U ⊔ relImg N W (W ⊔ zpowers t) :
      Subgroup (↥N ⧸ W.subgroupOf N)) : Set (↥N ⧸ W.subgroupOf N)) :=
    ((QuotientGroup.mk' (W.subgroupOf N)).comp (inclusion hNV)).codRestrict _ fun y => by
      rw [← hrelV]
      exact (relMk_mem_normalizer_iff hWV hVN _).mpr y.2
  have hψ : Function.Surjective ψ := fun z => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (W.subgroupOf N) (z : _)
    have hxV : (x : G) ∈ normalizer (V : Set G) := by
      rw [← relMk_mem_normalizer_iff hWV hVN, hrelV, hx]
      exact z.2
    exact ⟨⟨x, hxV⟩, Subtype.ext hx⟩
  have hψapply : ∀ y : normalizer (V : Set G), ((ψ y : _) : ↥N ⧸ W.subgroupOf N) =
      QuotientGroup.mk' (W.subgroupOf N) ⟨(y : G), hNV y.2⟩ := fun y => rfl
  obtain ⟨πD, e, hrange, hker, hequiv⟩ := exists_coords_of_gms_projective_eight hSet hC hproj
  have hNT := normalizer_inf_centralizer_eq_of_gms_projective_eight hSet hC hproj
  set π := πD.comp ψ with hπ
  have hrange' : π.range = natPSL := by
    rw [hπ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, ← MonoidHom.range_eq_map, hrange]
  have hmemV : ∀ y : normalizer (V : Set G), ((ψ y : _) : ↥N ⧸ W.subgroupOf N) ∈
      relImg N W U ⊔ relImg N W (W ⊔ zpowers t) ↔ (y : G) ∈ V := by
    intro y
    rw [hψapply, ← hrelV]
    exact relMk_mem_relImg_iff hWV _
  have hker' : ∀ x : normalizer (V : Set G), π x = 1 ↔ (x : G) ∈ V := by
    intro x
    rw [← hmemV]
    exact hker (ψ x)
  have hfix : ∀ x : normalizer (V : Set G), ∀ v ∈ V, v ∉ U → (x : G) * v = v * x →
      ∃ z, π x z = z := by
    intro x v hv hvU hxv
    set vb := QuotientGroup.mk' (W.subgroupOf N) (⟨v, hVN hv⟩ : N) with hvb
    have hvbV : vb ∈ relImg N W U ⊔ relImg N W (W ⊔ zpowers t) := by
      rw [← hrelV]; exact relMk_mem_relImg _ hv
    have hvbU : vb ∉ relImg N W U := fun h1 => hvU ((relMk_mem_relImg_iff hWU _).mp h1)
    have hvt : vb * tb ∈ relImg N W U := (hSet.mem_or_mul_mem hvbV).resolve_left hvbU
    have hQ := hSet.zpowers_mul_t_mem hvt
    rw [mul_assoc, hSet.mul_self_t, mul_one] at hQ
    refine ⟨e ⟨zpowers vb, hQ⟩, ?_⟩
    change πD (ψ x) (e _) = _
    rw [hequiv]
    congr 1
    apply Subtype.ext
    rw [gmsRootConjugateAction_apply, MonoidHom.map_zpowers]
    congr 1
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hψapply, hvb, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hxv, mul_inv_cancel_right]
  have hlayer : ∀ w : normalizer (V : Set G), (w : G) ∉ V →
      ∃ u ∈ U, (w : G) * u * (w : G)⁻¹ * u⁻¹ ∉ W := by
    intro w hwV
    by_contra hall
    push Not at hall
    apply hwV
    apply (hmemV w).mp
    suffices hmem : ((ψ w : _) : ↥N ⧸ W.subgroupOf N) ∈
        normalizer ((relImg N W U ⊔ relImg N W (W ⊔ zpowers t) :
          Subgroup (↥N ⧸ W.subgroupOf N)) : Set (↥N ⧸ W.subgroupOf N)) ⊓
        centralizer ((relImg N W U : Subgroup (↥N ⧸ W.subgroupOf N)) :
          Set (↥N ⧸ W.subgroupOf N)) by
      rwa [hNT] at hmem
    refine mem_inf.mpr ⟨(ψ w).2, mem_centralizer_iff.mpr fun ub hub => ?_⟩
    obtain ⟨u, huU, rfl⟩ := exists_of_mem_relImg hub
    have h1 := hall u huU
    have h2 : QuotientGroup.mk' (W.subgroupOf N) (⟨(w : G), hNV w.2⟩ * u *
        (⟨(w : G), hNV w.2⟩ : N)⁻¹ * u⁻¹) = 1 := (relMk_eq_one_iff _).mpr (by simpa using h1)
    simp only [map_mul, map_inv] at h2
    rw [hψapply]
    set a := QuotientGroup.mk' (W.subgroupOf N) (⟨(w : G), hNV w.2⟩ : N)
    set b := QuotientGroup.mk' (W.subgroupOf N) u
    have h3 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h2
    calc b * a = (a * b * a⁻¹) * a := by rw [h3]
      _ = a * b := by group
  exact exists_normal_index_two_of_projective_eight_layer hV2 le_sup_left (mem_sup_right
    (mem_zpowers t)) htU htt hVU hsqV hUn π hrange' hker' hfix hconjU hconjtU hUab hsqW hinvW
    hlayer hCt

end CFSG.SeitzReduction.RankOne
