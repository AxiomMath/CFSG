module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3Defs

public section

namespace CFSG.OddStandard.SmallF3.Omega

private abbrev SL23' : Type := Matrix.SpecialLinearGroup (Fin 2) (ZMod 3)

private def genU : SL23' := ⟨!![1, 1; 0, 1], by rw [Matrix.det_fin_two_of]; decide⟩

private def genV : SL23' := ⟨!![1, 0; 1, 1], by rw [Matrix.det_fin_two_of]; decide⟩

private def genGrow (W : Finset SL23') : Finset SL23' :=
  W ∪ W.image (· * genU) ∪ W.image (· * genU⁻¹) ∪ W.image (· * genV) ∪
    W.image (· * genV⁻¹)

private theorem genGrow4 : genGrow (genGrow (genGrow (genGrow {1}))) = Finset.univ := by
  decide +kernel

private theorem genGrow_mem (W : Finset SL23')
    (h : ∀ w ∈ W, w ∈ Subgroup.closure {genU, genV}) :
    ∀ w ∈ genGrow W, w ∈ Subgroup.closure {genU, genV} := by
  have hU : genU ∈ Subgroup.closure ({genU, genV} : Set SL23') :=
    Subgroup.subset_closure (by simp)
  have hV : genV ∈ Subgroup.closure ({genU, genV} : Set SL23') :=
    Subgroup.subset_closure (by simp)
  intro w hw
  simp only [genGrow, Finset.mem_union, Finset.mem_image] at hw
  rcases hw with ((((hw | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩) | ⟨u, hu, rfl⟩)
  · exact h w hw
  · exact mul_mem (h u hu) hU
  · exact mul_mem (h u hu) (inv_mem hU)
  · exact mul_mem (h u hu) hV
  · exact mul_mem (h u hu) (inv_mem hV)

private theorem mem_closure_gen (s : SL23') :
    s ∈ Subgroup.closure ({genU, genV} : Set SL23') := by
  have h : s ∈ genGrow (genGrow (genGrow (genGrow ({1} : Finset SL23')))) := by
    rw [genGrow4]
    exact Finset.mem_univ s
  exact genGrow_mem _ (genGrow_mem _ (genGrow_mem _ (genGrow_mem _ (by simp)))) s h

private theorem odd_order_genU : Odd (orderOf genU) := by
  have h3 : orderOf genU ∣ 3 := orderOf_dvd_of_pow_eq_one (by decide)
  exact Odd.of_dvd_nat (by decide : Odd 3) h3

private theorem odd_order_genV : Odd (orderOf genV) := by
  have h3 : orderOf genV ∣ 3 := orderOf_dvd_of_pow_eq_one (by decide)
  exact Odd.of_dvd_nat (by decide : Odd 3) h3

theorem l34g_closure_odd_sl23 :
    Subgroup.closure
      {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) | Odd (orderOf g)} = ⊤ := by
  rw [eq_top_iff]
  intro s _
  have hsub : ({genU, genV} : Set SL23') ⊆ {g : SL23' | Odd (orderOf g)} := by
    rintro x (rfl | rfl)
    · exact odd_order_genU
    · exact odd_order_genV
  exact Subgroup.closure_mono hsub (mem_closure_gen s)

private theorem odd_card_oddCore (X : Type*) [Group X] [Finite X] :
    Odd (Nat.card (CFSG.oddCore X)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.oddCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore 2 (G := X)]
  exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := X))

private theorem l34g_exists_odd_lift_aux {A C : Type} [Group A] [Group C] [Finite A]
    (φ : A →* C) (hφ : Function.Surjective φ) {c : C} (hc : Odd (orderOf c)) :
    ∃ a : A, φ a = c ∧ Odd (orderOf a) := by
  obtain ⟨a, ha⟩ := hφ c
  let k : ℕ := ordProj[2] (orderOf a)
  have hk_ne : k ≠ 0 := (Nat.ordProj_pos (orderOf a) 2).ne'
  have hk_dvd : k ∣ orderOf a := Nat.ordProj_dvd (orderOf a) 2
  have hcop : Nat.Coprime k (orderOf c) := by
    have h2 : Nat.Coprime 2 (orderOf c) := Nat.coprime_two_left.mpr hc
    simpa [k] using h2.pow_left ((orderOf a).factorization 2)
  have hodd_ak : Odd (orderOf (a ^ k)) := by
    have horder : orderOf (a ^ k) = ordCompl[2] (orderOf a) := by
      rw [orderOf_pow_of_dvd hk_ne hk_dvd]
    rw [horder]
    exact Nat.not_even_iff_odd.mp fun hev =>
      Nat.not_dvd_ordCompl Nat.prime_two (orderOf_pos a).ne' (even_iff_two_dvd.mp hev)
  have hc_mem : c ∈ Subgroup.zpowers (φ (a ^ k)) := by
    rw [map_pow, ha]
    exact mem_zpowers_pow_iff.mpr hcop
  obtain ⟨u, hu⟩ := Subgroup.mem_zpowers_iff.mp hc_mem
  refine ⟨(a ^ k) ^ u, ?_, ?_⟩
  · rw [map_zpow, hu]
  · exact Odd.of_dvd_nat hodd_ak (by
      rw [orderOf_zpow]
      exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _))

theorem l34g_le_closure_odd {C : Type} [Group C] [Finite C] {B : Subgroup C}
    (hB : IsSL23Mod ↥B) : B ≤ Subgroup.closure {c : C | c ∈ B ∧ Odd (orderOf c)} := by
  obtain ⟨e⟩ := hB
  set π : ↥B →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 3) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (oddCore ↥B)) with hπdef
  have hπ : Function.Surjective π := by
    intro g
    obtain ⟨q, hq⟩ := e.surjective g
    obtain ⟨b, hb⟩ := QuotientGroup.mk'_surjective (oddCore ↥B) q
    exact ⟨b, by rw [hπdef, MonoidHom.comp_apply, hb]; exact hq⟩
  set Mo : Subgroup ↥B := Subgroup.closure {b : ↥B | Odd (orderOf b)} with hModef
  have hker : π.ker ≤ Mo := by
    intro b hb
    rw [MonoidHom.mem_ker] at hb
    rw [hπdef, MonoidHom.comp_apply] at hb
    have hmk : QuotientGroup.mk' (oddCore ↥B) b = 1 := by
      apply e.injective
      simpa using hb
    have hbmem : b ∈ oddCore ↥B := by
      have hmk' : (b : ↥B ⧸ oddCore ↥B) = 1 := by simpa using hmk
      exact (QuotientGroup.eq_one_iff (N := oddCore ↥B) b).mp hmk'
    have hodd : Odd (orderOf b) :=
      Odd.of_dvd_nat (odd_card_oddCore ↥B) (Subgroup.orderOf_dvd_natCard _ hbmem)
    rw [hModef]
    exact Subgroup.subset_closure hodd
  have hmap : Mo.map π = ⊤ := by
    rw [eq_top_iff, ← l34g_closure_odd_sl23]
    refine (Subgroup.closure_le (Mo.map π)).mpr ?_
    intro g hg
    obtain ⟨b, hπb, hbodd⟩ := l34g_exists_odd_lift_aux π hπ hg
    refine ⟨b, ?_, hπb⟩
    rw [hModef]
    exact Subgroup.subset_closure hbodd
  have hMo : Mo = ⊤ := by
    rw [eq_top_iff]
    have h1 : (⊤ : Subgroup ↥B).map π ≤ Mo.map π := by
      rw [hmap]
      exact le_top
    have h2 : (⊤ : Subgroup ↥B) ≤ Mo ⊔ π.ker := Subgroup.map_le_map_iff.mp h1
    rw [sup_eq_left.mpr hker] at h2
    exact h2
  have hgen : {b : ↥B | Odd (orderOf b)} ⊆
      (Subgroup.closure {c : C | c ∈ B ∧ Odd (orderOf c)}).comap B.subtype := by
    intro b hb
    change B.subtype b ∈ Subgroup.closure {c : C | c ∈ B ∧ Odd (orderOf c)}
    refine Subgroup.subset_closure ⟨b.property, ?_⟩
    simpa only [Set.mem_ofPred_eq, Subgroup.subtype_apply, Subgroup.orderOf_coe] using hb
  have hMo_le : Mo ≤
      (Subgroup.closure {c : C | c ∈ B ∧ Odd (orderOf c)}).comap B.subtype := by
    rw [hModef]
    exact (Subgroup.closure_le
      ((Subgroup.closure {c : C | c ∈ B ∧ Odd (orderOf c)}).comap B.subtype)).mpr hgen
  have hmap_sub : Mo.map B.subtype ≤
      Subgroup.closure {c : C | c ∈ B ∧ Odd (orderOf c)} :=
    Subgroup.map_le_iff_le_comap.mpr hMo_le
  have hB_eq : (⊤ : Subgroup ↥B).map B.subtype = B := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  calc B = (⊤ : Subgroup ↥B).map B.subtype := hB_eq.symm
    _ = Mo.map B.subtype := by rw [hMo]
    _ ≤ Subgroup.closure {c : C | c ∈ B ∧ Odd (orderOf c)} := hmap_sub

end CFSG.OddStandard.SmallF3.Omega
