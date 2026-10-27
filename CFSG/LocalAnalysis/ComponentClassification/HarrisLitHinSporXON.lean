module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXONFix
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXONOut
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinSporXElem
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitHinAut
public import CFSG.Sporadic.ONOddCore.LocalComp

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.Hin

open CFSG Subgroup CFSG.ONSchreier CFSG.Sporadic.ONOddCore SporX
open CFSG.ComponentClassification.UnbalancedCatalog.EvenCatalog
  (le_oddCore_of_normal oddCore_eq_bot_of_mulEquiv)

namespace SporX

theorem psl2_card_ne_20160 (q : ℕ) : q * (q ^ 2 - 1) / 2 ≠ 20160 := by
  intro h
  rcases Nat.lt_or_ge q 35 with hq | hq
  · interval_cases q <;> norm_num at h
  · have h1 : 35 * (35 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
      Nat.mul_le_mul hq (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq 2) 1)
    have h2 := Nat.div_le_div_right (c := 2) h1
    norm_num at h2
    omega

theorem length_le_natCard {G : Type*} [Group G] [Finite G] {K : Subgroup G} {l : List G}
    (hl : l.Nodup) (hK : ∀ x ∈ l, x ∈ K) : l.length ≤ Nat.card K := by
  classical
  rw [← List.toFinset_card_of_nodup hl, ← Set.ncard_coe_finset, ← Nat.card_coe_set_eq]
  exact Set.ncard_le_ncard (fun x hx => hK x (List.mem_toFinset.1 hx)) (Set.toFinite _)

theorem eight_le_card_closure {G : Type*} [Group G] [Finite G] {L : Subgroup G} {a b s : G}
    (ha : orderOf a = 2) (hb : orderOf b = 2) (hab : a ≠ b) (haL : a ∈ L) (hbL : b ∈ L)
    (hsL : s ∉ L) :
    8 ≤ Nat.card (closure {x | x ∈ [s, a, b]}) := by
  have ha1 : a ≠ 1 := fun h => by rw [h, orderOf_one] at ha; omega
  have hb1 : b ≠ 1 := fun h => by rw [h, orderOf_one] at hb; omega
  have hbb : b * b = 1 := by rw [← pow_two, ← hb, pow_orderOf_eq_one]
  set V : List G := [1, a, b, a * b] with hV
  have hVL : ∀ v ∈ V, v ∈ L := by
    intro v hv
    simp only [hV, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h <;> rw [h]
    · exact L.one_mem
    · exact haL
    · exact hbL
    · exact L.mul_mem haL hbL
  have hVnd : V.Nodup := by
    have h1 : (1 : G) ≠ a * b := fun h => hab (by
      calc a = a * b * b := by rw [mul_assoc, hbb, mul_one]
        _ = b := by rw [← h, one_mul])
    have h2 : a ≠ a * b := fun h => hb1 (by
      calc b = a⁻¹ * (a * b) := by group
        _ = 1 := by rw [← h, inv_mul_cancel])
    have h3 : b ≠ a * b := fun h => ha1 (by
      calc a = a * b * b⁻¹ := by group
        _ = 1 := by rw [← h, mul_inv_cancel])
    rw [hV, List.nodup_cons, List.nodup_cons, List.nodup_cons]
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
    exact ⟨⟨ha1.symm, hb1.symm, h1⟩, ⟨hab, h2⟩, h3, List.nodup_singleton _⟩
  have hW : (V ++ V.map (s * ·)).Nodup := by
    refine List.nodup_append.2 ⟨hVnd, hVnd.map (fun x y h => mul_left_cancel h), ?_⟩
    intro v hv w hw hvw
    obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hw
    apply hsL
    have h1 : s = v * u⁻¹ := by rw [hvw, mul_inv_cancel_right]
    rw [h1]
    exact L.mul_mem (hVL v hv) (L.inv_mem (hVL u hu))
  set K := closure {x | x ∈ [s, a, b]} with hK
  have hs' : s ∈ K := subset_closure (by simp)
  have ha' : a ∈ K := subset_closure (by simp)
  have hb' : b ∈ K := subset_closure (by simp)
  have hV' : ∀ v ∈ V, v ∈ K := by
    intro v hv
    simp only [hV, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with h | h | h | h <;> rw [h]
    · exact one_mem _
    · exact ha'
    · exact hb'
    · exact mul_mem ha' hb'
  have hmem : ∀ x ∈ V ++ V.map (s * ·), x ∈ K := by
    intro x hx
    rcases List.mem_append.1 hx with hx | hx
    · exact hV' x hx
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hx
      exact mul_mem hs' (hV' u hu)
  have h8 := length_le_natCard hW hmem
  simpa [hV] using h8

theorem comm_of_three {G : Type*} [Group G] {s a b : G} (hsa : s * a = a * s)
    (hsb : s * b = b * s) (hab : a * b = b * a) :
    ∀ x ∈ {x | x ∈ [s, a, b]}, ∀ y ∈ {x | x ∈ [s, a, b]}, x * y = y * x := by
  intro x hx y hy
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hx hy
  rcases hx with rfl | rfl | rfl <;> rcases hy with rfl | rfl | rfl
  all_goals first | rfl | assumption | (symm; assumption)

theorem sq_of_three {G : Type*} [Group G] {s a b : G} (hs : orderOf s = 2)
    (ha : orderOf a = 2) (hb : orderOf b = 2) : ∀ x ∈ {x | x ∈ [s, a, b]}, x ^ 2 = 1 := by
  intro x hx
  simp only [Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl
  · rw [← hs, pow_orderOf_eq_one]
  · rw [← ha, pow_orderOf_eq_one]
  · rw [← hb, pow_orderOf_eq_one]

variable {Y : Type} [Group Y]

theorem congr_not_inner_of {Z : Type*} [Group Z] (ψ : Y ≃* Z) {τ : MulAut Y}
    (hτ : τ ∉ innAut Y) : MulAut.congr ψ τ ∉ (MulAut.conj : Z →* MulAut Z).range := by
  rintro ⟨h, hh⟩
  apply hτ
  refine ⟨ψ.symm h, ?_⟩
  have h1 := OuterAutomorphisms.congr_conj ψ.symm h
  rw [hh] at h1
  rw [← h1]
  ext y
  simp [MulAut.congr_apply]

theorem exists_fixed_odd_ON
    (ψ : Y ≃* Pv) {τ : MulAut Y}
    (hτ : τ ∉ innAut Y) (hτ2 : τ * τ = 1) {a : Y} (ha : orderOf a = 2) (hτa : τ a = a) :
    ∃ x : Y, τ x = x ∧ x * a = a * x ∧ (orderOf x = 5 ∨ orderOf x = 7) := by
  have h2 : MulAut.congr ψ τ * MulAut.congr ψ τ = 1 := by rw [← map_mul, hτ2, map_one]
  have ha' : orderOf (ψ a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
  have hτa' : MulAut.congr ψ τ (ψ a) = ψ a := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hτa]
  obtain ⟨x, hx, hxa, hxo⟩ := exists_fixed_odd_of_fix (congr_not_inner_of ψ hτ) h2 ha' hτa'
  refine ⟨ψ.symm x, ?_, ?_, ?_⟩
  · apply ψ.injective
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply] at hx
    rw [MulEquiv.apply_symm_apply]
    exact hx
  · apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hxa
  · rw [MulEquiv.orderOf_eq]
    exact hxo

theorem oddCore_fixed_ON
    (ψ : Y ≃* Pv) {τ : MulAut Y}
    (hτ : τ ∉ innAut Y) (hτ2 : τ * τ = 1) {a : Y} (ha : orderOf a = 2) (hτa : τ a = a) :
    CFSG.oddCore ↥(fixedPoints τ ⊓ centralizer {a}) = ⊥ := by
  have h2 : MulAut.congr ψ τ * MulAut.congr ψ τ = 1 := by rw [← map_mul, hτ2, map_one]
  have ha' : orderOf (ψ a) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha
  have hτa' : MulAut.congr ψ τ (ψ a) = ψ a := by
    rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hτa]
  exact oddCore_eq_bot_of_mulEquiv (fixedCentCongr ψ τ a).symm
    (oddCore_fixed_centralizer (congr_not_inner_of ψ hτ) h2 ha' hτa')

theorem layerIn_le_self (C : Subgroup Y) : GSThmB.layerIn C ≤ C :=
  map_subtype_le _

theorem eq_one_of_mem_layerIn {C : Subgroup Y} {p m : ℕ}
    (hL : Blueprint.LieModel ↥(GSThmB.layerIn C) .PSL 2 p m) {s : Y}
    (hsL : s ∈ GSThmB.layerIn C) (hs : ∀ l ∈ GSThmB.layerIn C, l * s = s * l) : s = 1 := by
  have hZ : (⟨s, hsL⟩ : ↥(GSThmB.layerIn C)) ∈ center ↥(GSThmB.layerIn C) :=
    mem_center_iff.2 fun l => Subtype.ext (hs l l.2)
  have hZ' : layerInEquiv C ⟨s, hsL⟩ ∈ center ↥(pLayer ↥C 2) := mem_center_iff.2 fun w => by
    have h1 := congrArg (layerInEquiv C) ((mem_center_iff.1 hZ) ((layerInEquiv C).symm w))
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h1
  rw [center_pLayer_eq_bot hL, mem_bot, map_eq_one_iff _ (layerInEquiv C).injective] at hZ'
  exact congrArg Subtype.val hZ'

end SporX

open scoped MatrixGroups in
theorem hinFor_spor_ON :
    HinFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .ONan := by
  intro Y _ _ _ ⟨e₀⟩ hnab p m hp hp2 hm h16 _ τ hτ hL
  have hZY : center Y = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  set ψ : Y ≃* Pv := e₀.trans onEquivPv with hψ
  obtain ⟨-, -, -, F', _, _, hF', ⟨eL⟩⟩ := exists_psl2_of_lieModel hL
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hcardL : Nat.card (GSThmB.layerIn (fixedPoints τ)) = p ^ m * ((p ^ m) ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eL.toEquiv,
      GorensteinWalter.psl2_card_formula F' ⟨p, m, hp, hpodd, hm, hF'⟩, hF']
  by_cases hinn : τ ∈ innAut Y
  ·
    exfalso
    obtain ⟨t, rfl⟩ := hinn
    have ht2 : orderOf t = 2 := by
      rw [← orderOf_injective _ (conj_injective_of_center hZY) t]
      exact hτ
    obtain ⟨B, hB, ⟨eB⟩⟩ := exists_isComponent_of_eq (centralizer_eq_fixedPoints_conj t) hL
    have h20160 :=
      cti_on_involution_local_components_projective_linear_quotient_order ⟨e₀⟩ t ht2 B hB
    have hs := isSimpleGroup_pLayer hL
    have hBs : IsSimpleGroup B := (eB.trans (layerInEquiv _)).isSimpleGroup
    have hBnab : ∃ a b : B, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := nonabelian_pLayer hL
      exact ⟨(eB.trans (layerInEquiv _)).symm a, (eB.trans (layerInEquiv _)).symm b, fun h =>
        hab ((eB.trans (layerInEquiv _)).symm.injective (by rw [map_mul, map_mul, h]))⟩
    have hZB : center B = ⊥ := (LocalCores.isQuasisimple_of_isSimpleGroup hBnab).2
    have hcardB : Nat.card B = 20160 := by
      rw [← h20160]
      exact (Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZB).trans
        QuotientGroup.quotientBot).toEquiv).symm
    rw [Nat.card_congr eB.toEquiv, hcardL] at hcardB
    exact SporX.psl2_card_ne_20160 _ hcardB
  · refine hinConcl_of_not_inner hinn fun hrank => ?_
    set C := fixedPoints τ with hC
    set L := GSThmB.layerIn C with hLdef
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Fact p.Prime := ⟨hp⟩
    have hcardY : Nat.card Y = 460815505920 := by rw [Nat.card_congr ψ.toEquiv, card_Pv]
    have h16' : 16 ∣ (p ^ m) ^ 2 - 1 := by rwa [← pow_mul, mul_comm]
    have hq := SporX.on_q_cases hp hp2 hm h16' (by
      rw [← hcardL, ← hcardY]
      exact Subgroup.card_subgroup_dvd_card L)
    have h2L : 2 ∣ Nat.card L := by
      rw [hcardL]
      rcases hq with h | h | h <;> rw [h] <;> norm_num
    obtain ⟨a₀, ha₀⟩ := exists_prime_orderOf_dvd_card' 2 h2L
    have ha : orderOf (a₀ : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact ha₀
    have haC : (a₀ : Y) ∈ C := SporX.layerIn_le_self C a₀.2
    have hτ2 : τ * τ = 1 := by rw [← pow_two, ← hτ, pow_orderOf_eq_one]
    have hτa : τ a₀ = a₀ := mem_fixedPoints.1 haC
    have hta : orderOf (eL a₀) = 2 := by rw [MulEquiv.orderOf_eq]; exact ha₀
    obtain ⟨hC32, b', hb'C, hb'2, hb'a⟩ :=
      SporX.psl2_centralizer_involution_small hF' hpodd (by omega) hq hta
    by_cases hinv : ∃ s ∈ C ⊓ centralizer (L : Set Y), orderOf s = 2
    ·
      obtain ⟨s, hs, hs2⟩ := hinv
      obtain ⟨hsC, hsL⟩ := mem_inf.1 hs
      set b : Y := ((eL.symm b' : L) : Y) with hb
      have hb2 : orderOf b = 2 := by
        rw [hb, Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
        exact hb'2
      have hab : (a₀ : Y) ≠ b := fun h => hb'a (by
        have h1 : eL.symm b' = a₀ := Subtype.ext h.symm
        rw [← h1, MulEquiv.apply_symm_apply])
      have hab' : (a₀ : Y) * b = b * a₀ := by
        have h1 := congrArg eL.symm (mem_centralizer_singleton_iff.1 hb'C)
        rw [map_mul, map_mul, MulEquiv.symm_apply_apply] at h1
        exact (congrArg Subtype.val h1).symm
      have hsa : s * a₀ = a₀ * s := (mem_centralizer_iff.1 hsL _ a₀.2).symm
      have hsb : s * b = b * s := (mem_centralizer_iff.1 hsL _ (eL.symm b').2).symm
      have hsnL : s ∉ L := fun h => by
        have h1 := SporX.eq_one_of_mem_layerIn hL h fun l hl => mem_centralizer_iff.1 hsL l hl
        rw [h1, orderOf_one] at hs2
        omega
      have hE : closure {x | x ∈ [s, (a₀ : Y), b]} ≤ C := by
        rw [closure_le]
        intro x hx
        simp only [SetLike.mem_coe, Set.mem_ofPred_eq, List.mem_cons, List.not_mem_nil,
          or_false] at hx ⊢
        rcases hx with h | h | h <;> rw [h]
        · exact hsC
        · exact haC
        · exact SporX.layerIn_le_self C (eL.symm b').2
      obtain ⟨hEc, hEs⟩ := closure_comm_sq (SporX.comm_of_three hsa hsb hab')
        (SporX.sq_of_three hs2 ha hb2)
      exact not_sectionalTwoRankLE_of_le hE hEc hEs (lt_of_lt_of_le (by norm_num)
        (SporX.eight_le_card_closure ha hb2 hab a₀.2 (eL.symm b').2 hsnL)) hrank
    ·
      push Not at hinv
      set N := C ⊓ centralizer (L : Set Y) with hN
      set D := C ⊓ centralizer {(a₀ : Y)} with hD
      have hND : N ≤ D := fun n hn => mem_inf.2 ⟨(mem_inf.1 hn).1,
        mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 (mem_inf.1 hn).2 _ a₀.2).symm⟩
      have hNn : (N.subgroupOf D).Normal := ⟨fun n hn g => by
        rw [mem_subgroupOf] at hn ⊢
        obtain ⟨hnC, hnL⟩ := mem_inf.1 hn
        have hgC : (g : Y) ∈ C := (mem_inf.1 g.2).1
        rw [coe_mul, coe_mul, coe_inv]
        refine mem_inf.2 ⟨C.mul_mem (C.mul_mem hgC hnC) (C.inv_mem hgC), ?_⟩
        rw [mem_centralizer_iff]
        intro h hh
        have h2 := mem_centralizer_iff.1 hnL _ (conj_mem_layerIn (C.inv_mem hgC) hh)
        calc h * ((g : Y) * n * (g : Y)⁻¹)
            = g * ((g : Y)⁻¹ * h * (g : Y)⁻¹⁻¹ * n) * (g : Y)⁻¹ := by group
          _ = g * (n * ((g : Y)⁻¹ * h * (g : Y)⁻¹⁻¹)) * (g : Y)⁻¹ := by rw [h2]
          _ = (g : Y) * n * (g : Y)⁻¹ * h := by group⟩
      have hodd : Odd (Nat.card (N.subgroupOf D)) := by
        rw [Nat.card_congr (subgroupOfEquivOfLe hND).toEquiv, ← Nat.not_even_iff_odd,
          even_iff_two_dvd]
        intro h2
        obtain ⟨n, hn⟩ := exists_prime_orderOf_dvd_card' 2 h2
        exact hinv n n.2 (by rw [Subgroup.orderOf_coe]; exact hn)
      have hcore := SporX.oddCore_fixed_ON ψ hinn hτ2 ha hτa
      have hNbot : ∀ n ∈ N, n = 1 := by
        intro n hn
        have h1 : (⟨n, hND hn⟩ : D) ∈ N.subgroupOf D := hn
        have h2 := le_oddCore_of_normal hNn hodd h1
        rw [hcore, mem_bot] at h2
        exact congrArg Subtype.val h2
      obtain ⟨x, hxτ, hxa, hxo⟩ := SporX.exists_fixed_odd_ON ψ hinn hτ2 ha hτa
      have hxC : x ∈ C := mem_fixedPoints.2 hxτ
      have : (pLayer ↥C 2).Normal := pLayer_two_normal C
      set e' : ↥(pLayer ↥C 2) ≃* PSL(2, F') := (layerInEquiv C).symm.trans eL with he'
      set β₀ : MulAut ↥(pLayer ↥C 2) := MulAut.conjNormal (⟨x, hxC⟩ : C) with hβ₀def
      have hr : (orderOf x).Prime ∧ 3 < orderOf x := by
        rcases hxo with h | h <;> rw [h] <;> norm_num
      have hβ : (MulAut.congr e' β₀) ^ orderOf x = 1 := by
        have h1 : (⟨x, hxC⟩ : C) ^ orderOf x = 1 :=
          Subtype.ext (by rw [SubgroupClass.coe_pow, pow_orderOf_eq_one]; rfl)
        rw [← map_pow, hβ₀def, ← map_pow, h1, map_one, map_one]
      have hp3 : 3 ≤ p := by
        have := hp.two_le
        omega
      have hmr : m < orderOf x := by
        have h1 : 3 ^ m ≤ p ^ m := Nat.pow_le_pow_left hp3 m
        have h2 : p ^ m ≤ 31 := by rcases hq with h | h | h <;> omega
        have h3 : m < 5 := by
          by_contra h
          push Not at h
          have h4 := Nat.pow_le_pow_right (show 0 < 3 by norm_num) h
          norm_num at h4
          omega
        rcases hxo with h | h <;> omega
      have hq3 : 3 < p ^ m := by rcases hq with h | h | h <;> omega
      obtain ⟨y, hy⟩ := SporX.psl2_aut_mem_inner hp hp2 hm hF' hq3 hr.1 hr.2 hmr hβ
      have hβ₀ : β₀ = MulAut.conj (e'.symm y) := by
        apply (MulAut.congr e').injective
        rw [OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply, hy]
      set l : Y := (((e'.symm y : pLayer ↥C 2) : C) : Y) with hl
      have hlL : l ∈ L := ⟨(e'.symm y : pLayer ↥C 2), (e'.symm y).2, rfl⟩
      have hlC : l ∈ C := SporX.layerIn_le_self C hlL
      have hlx : l⁻¹ * x ∈ N := by
        refine mem_inf.2 ⟨C.mul_mem (C.inv_mem hlC) hxC, mem_centralizer_iff.2 fun v hv => ?_⟩
        obtain ⟨w, hw, rfl⟩ := hv
        have h1 := congrArg (fun f : MulAut ↥(pLayer ↥C 2) =>
          (((f ⟨w, hw⟩ : pLayer ↥C 2) : C) : Y)) hβ₀
        simp only [hβ₀def, MulAut.conjNormal_apply, MulAut.conj_apply, coe_mul, coe_inv] at h1
        change (w : Y) * (l⁻¹ * x) = l⁻¹ * x * w
        calc (w : Y) * (l⁻¹ * x) = l⁻¹ * (l * w * l⁻¹) * x := by group
          _ = l⁻¹ * (x * w * x⁻¹) * x := by rw [hl, h1]
          _ = l⁻¹ * x * w := by group
      have hxl : x = l := by
        have h1 := hNbot _ hlx
        rw [inv_mul_eq_one] at h1
        exact h1.symm
      have hxL : x ∈ L := hxl ▸ hlL
      have hx₀ : eL ⟨x, hxL⟩ ∈ centralizer {eL a₀} := by
        rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
        exact congrArg eL (Subtype.ext hxa)
      have hdvd := (Subgroup.orderOf_dvd_natCard _ hx₀).trans hC32
      rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe] at hdvd
      rcases hxo with h | h <;> rw [h] at hdvd <;> norm_num at hdvd

end CFSG.ComponentClassification.HarrisLit.Hin
