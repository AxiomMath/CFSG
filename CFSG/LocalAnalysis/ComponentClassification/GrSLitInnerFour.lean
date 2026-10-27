module

public import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.RankThree.GroupTheory.SteinbergBMCoprimeGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.KleinFourOfCommutingInvolutions
public import CFSG.RankThree.OddKernel.OddLift

public section

namespace CFSG.ComponentClassification.GrSLit.L34Sec5S

open Subgroup

private lemma card_inf_centralizer_conj {G : Type*} [Group G] {A : Subgroup G} [A.Normal]
    {a b g : G} (h : b = g * a * g⁻¹) :
    Nat.card ↥(A ⊓ Subgroup.centralizer ({a} : Set G)) =
      Nat.card ↥(A ⊓ Subgroup.centralizer ({b} : Set G)) := by
  let e : G ≃* G := MulAut.conj g
  have hmap : (A ⊓ Subgroup.centralizer ({a} : Set G)).map e.toMonoidHom =
      A ⊓ Subgroup.centralizer ({b} : Set G) := by
    refine le_antisymm ?_ ?_
    · intro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      change MulAut.conj g w ∈ A ⊓ Subgroup.centralizer ({b} : Set G)
      rw [Subgroup.mem_inf] at hw ⊢
      rw [MulAut.conj_apply]
      refine ⟨?_, ?_⟩
      · exact Subgroup.Normal.conj_mem inferInstance w hw.1 g
      · rw [Subgroup.mem_centralizer_singleton_iff] at hw ⊢
        rw [h]
        calc g * w * g⁻¹ * (g * a * g⁻¹) = g * (w * a) * g⁻¹ := by group
          _ = g * (a * w) * g⁻¹ := by rw [hw.2]
          _ = g * a * g⁻¹ * (g * w * g⁻¹) := by group
    · intro z hz
      rw [Subgroup.mem_inf] at hz
      refine Subgroup.mem_map.mpr ⟨g⁻¹ * z * g, ?_, ?_⟩
      · rw [Subgroup.mem_inf]
        refine ⟨?_, ?_⟩
        · exact Subgroup.Normal.conj_mem' inferInstance z hz.1 g
        · rw [Subgroup.mem_centralizer_singleton_iff] at hz ⊢
          rw [h] at hz
          calc g⁻¹ * z * g * a = g⁻¹ * (z * (g * a * g⁻¹)) * g := by group
            _ = g⁻¹ * (g * a * g⁻¹ * z) * g := by rw [hz.2]
            _ = a * (g⁻¹ * z * g) := by group
      · show MulAut.conj g (g⁻¹ * z * g) = z
        rw [MulAut.conj_apply]
        group
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

theorem le_center_of_four_fixed {P : Type*} [Group P] [Finite P] {U : Subgroup P} [U.Normal]
    (hU : Odd (Nat.card U)) (hperf : commutator P = ⊤) (hsimp : IsSimpleGroup (P ⧸ U))
    (hconj : ∀ a b : P ⧸ U, orderOf a = 2 → orderOf b = 2 → IsConj a b)
    {x y : P} (hx : orderOf x = 2) (hy : orderOf y = 2) (hxy : x * y = y * x) (hne : x ≠ y)
    (hfix : ∀ u ∈ U, x * u = u * x → y * u = u * y) :
    U ≤ center P := by
  have hx2 : x * x = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    simpa [pow_two] using h
  have hy2 : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rw [hy] at h
    simpa [pow_two] using h
  have hxy_comm : Commute x y := hxy
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hy
    exact absurd hy (by norm_num)
  have hx2sq : x ^ 2 = 1 := by simpa [pow_two] using hx2
  have hy2sq : y ^ 2 = 1 := by simpa [pow_two] using hy2
  have hxy2 : (x * y) ^ 2 = 1 := by
    rw [hxy_comm.mul_pow, hx2sq, hy2sq, one_mul]
  have hxyne1 : x * y ≠ 1 := by
    intro h
    apply hne
    calc x = x * (y * y) := by rw [hy2, mul_one]
      _ = (x * y) * y := by group
      _ = 1 * y := by rw [h]
      _ = y := one_mul y
  have hxy_ord : orderOf (x * y) = 2 := orderOf_eq_prime hxy2 hxyne1
  let V : Subgroup P :=
    CFSG.GorensteinWalter.kleinFourOfCommutingInvolutions x y hx2 hy2 hxy_comm
  have hVK : IsKleinFour V :=
    CFSG.GorensteinWalter.isKleinFour_kleinFourOfCommutingInvolutions x y hx2 hy2 hx1 hy1 hne
      hxy_comm
  have hB_le_V : Subgroup.closure ({x, y} : Set P) ≤ V := by
    rw [Subgroup.closure_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with hzx | hzy
    · rw [hzx]
      change x ∈ ({x * y, x, y, 1} : Set P)
      simp
    · rw [hzy]
      change y ∈ ({x * y, x, y, 1} : Set P)
      simp
  have hV_le_B : V ≤ Subgroup.closure ({x, y} : Set P) := by
    intro z hz
    change z ∈ ({x * y, x, y, 1} : Set P) at hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    obtain h1 | h2 | h3 | h4 := hz
    · rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.subset_closure (by simp))
        (Subgroup.subset_closure (by simp))
    · rw [h2]
      exact Subgroup.subset_closure (by simp)
    · rw [h3]
      exact Subgroup.subset_closure (by simp)
    · rw [h4]
      exact Subgroup.one_mem _
  have hB_eq : Subgroup.closure ({x, y} : Set P) = V := le_antisymm hB_le_V hV_le_B
  have hB_ea : CFSG.IsElementaryAbelian 2 (Subgroup.closure ({x, y} : Set P)) := by
    rw [hB_eq]
    haveI : IsKleinFour V := hVK
    refine { toIsMulCommutative := IsKleinFour.isMulCommutative (G := V), exponent_dvd_p := ?_ }
    rw [IsKleinFour.exponent_two (G := V)]
  have hB_card : 2 ^ 2 ≤ Nat.card ↥(Subgroup.closure ({x, y} : Set P)) := by
    rw [hB_eq, hVK.card_four]
    norm_num
  have hB_normalizes : Subgroup.closure ({x, y} : Set P) ≤ normalizer (U : Set P) := by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  have hle_x_y : U ⊓ Subgroup.centralizer ({x} : Set P) ≤
      U ⊓ Subgroup.centralizer ({y} : Set P) := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨hu.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
    exact (hfix u hu.1 hu.2.symm).symm
  have hle_x_xy : U ⊓ Subgroup.centralizer ({x} : Set P) ≤
      U ⊓ Subgroup.centralizer ({x * y} : Set P) := by
    intro u hu
    rw [Subgroup.mem_inf] at hu ⊢
    refine ⟨hu.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hu ⊢
    have huy : y * u = u * y := hfix u hu.1 hu.2.symm
    calc u * (x * y) = (u * x) * y := by group
      _ = (x * u) * y := by rw [hu.2]
      _ = x * (u * y) := by group
      _ = x * (y * u) := by rw [huy]
      _ = (x * y) * u := by group
  have hcard_y : Nat.card ↥(U ⊓ Subgroup.centralizer ({x} : Set P)) =
      Nat.card ↥(U ⊓ Subgroup.centralizer ({y} : Set P)) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (CFSG.RankThree.OddKernel.isConj_of_isConj_quotient U hU hconj hx hy)
    exact card_inf_centralizer_conj (A := U) hg.symm
  have hcard_xy : Nat.card ↥(U ⊓ Subgroup.centralizer ({x} : Set P)) =
      Nat.card ↥(U ⊓ Subgroup.centralizer ({x * y} : Set P)) := by
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (CFSG.RankThree.OddKernel.isConj_of_isConj_quotient U hU hconj hx hxy_ord)
    exact card_inf_centralizer_conj (A := U) hg.symm
  have hC_y_eq : U ⊓ Subgroup.centralizer ({y} : Set P) =
      U ⊓ Subgroup.centralizer ({x} : Set P) :=
    (Subgroup.eq_of_le_of_card_ge hle_x_y (le_of_eq hcard_y.symm)).symm
  have hC_xy_eq : U ⊓ Subgroup.centralizer ({x * y} : Set P) =
      U ⊓ Subgroup.centralizer ({x} : Set P) :=
    (Subgroup.eq_of_le_of_card_ge hle_x_xy (le_of_eq hcard_xy.symm)).symm
  have hx_cent : U ≤ Subgroup.centralizer ({x} : Set P) := by
    haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
    refine CFSG.RankThree.GroupTheory.SteinbergBM.le_of_forall_inf_centralizer_le
      (p := 2) (B := Subgroup.closure ({x, y} : Set P)) (V := U)
      (W := Subgroup.centralizer ({x} : Set P)) hB_ea hB_card ?_ hB_normalizes ?_
    · intro h
      exact absurd h (Odd.not_two_dvd_nat hU)
    · intro b hb hb1
      rw [hB_eq] at hb
      change b ∈ ({x * y, x, y, 1} : Set P) at hb
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hb
      rcases hb with hbxy | hbx | hby | hb1'
      · rw [hbxy, hC_xy_eq]
        exact inf_le_right
      · rw [hbx]
        exact inf_le_right
      · rw [hby, hC_y_eq]
        exact inf_le_right
      · exact absurd hb1' hb1
  have hxU : ∀ u ∈ U, x * u = u * x := by
    intro u hu
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hx_cent hu)).symm
  have hx_not_mem : x ∉ U := by
    intro hxmem
    have hdvd : orderOf x ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hxmem
    rw [hx] at hdvd
    exact absurd hdvd (Odd.not_two_dvd_nat hU)
  have hgen : ∀ a : P, orderOf a = 2 → ∀ u ∈ U, a * u = u * a := by
    intro a ha u hu
    obtain ⟨g, hg⟩ := isConj_iff.mp
      (CFSG.RankThree.OddKernel.isConj_of_isConj_quotient U hU hconj ha hx)
    have hg' : a = g⁻¹ * x * g := by
      rw [← hg]
      group
    have hv : g * u * g⁻¹ ∈ U := Subgroup.Normal.conj_mem inferInstance u hu g
    have hxu : x * (g * u * g⁻¹) = (g * u * g⁻¹) * x := hxU _ hv
    rw [hg']
    calc g⁻¹ * x * g * u = g⁻¹ * (x * (g * u * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * u * g⁻¹) * x) * g := by rw [hxu]
      _ = u * (g⁻¹ * x * g) := by group
  let C : Subgroup P := Subgroup.centralizer (U : Set P)
  have hCnorm : C.Normal := Subgroup.normal_centralizer
  haveI : C.Normal := hCnorm
  have hx_C : x ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hxU u hu).symm
  let q : P →* P ⧸ U := QuotientGroup.mk' U
  have hq_surj : Function.Surjective q := QuotientGroup.mk'_surjective U
  have hCmap_ne_bot : C.map q ≠ ⊥ := by
    intro hbot
    have hxq : q x = 1 := by
      have hmem : q x ∈ C.map q := Subgroup.mem_map_of_mem q hx_C
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact hx_not_mem ((QuotientGroup.eq_one_iff x).mp hxq)
  have hCmap_top : C.map q = ⊤ := by
    haveI : IsSimpleGroup (P ⧸ U) := hsimp
    haveI : (C.map q).Normal := hCnorm.map q hq_surj
    rcases Subgroup.Normal.eq_bot_or_eq_top (C.map q) with h | h
    · exact absurd h hCmap_ne_bot
    · exact h
  have hCU_top : C ⊔ U = ⊤ := by
    rw [eq_top_iff]
    intro p _
    have hp : q p ∈ C.map q := by
      rw [hCmap_top]
      exact Subgroup.mem_top (q p)
    obtain ⟨c, hc, hcp⟩ := Subgroup.mem_map.mp hp
    have hmem : c⁻¹ * p ∈ U := by
      have hq : q (c⁻¹ * p) = 1 := by
        rw [map_mul, map_inv, hcp, inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff (c⁻¹ * p)).mp hq
    have hp_eq : p = c * (c⁻¹ * p) := by group
    rw [hp_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc)
      (Subgroup.mem_sup_right hmem)
  let r : U →* P ⧸ C := (QuotientGroup.mk' C).comp U.subtype
  have hr : Function.Surjective r := by
    intro z
    obtain ⟨p, rfl⟩ := QuotientGroup.mk'_surjective C z
    have hp : p ∈ C ⊔ U := by
      rw [hCU_top]
      exact Subgroup.mem_top p
    obtain ⟨c, hc, u, hu, hcu⟩ := Subgroup.mem_sup_of_normal_right.mp hp
    rw [← hcu]
    refine ⟨⟨u, hu⟩, ?_⟩
    show QuotientGroup.mk' C u = QuotientGroup.mk' C (c * u)
    have hc1 : QuotientGroup.mk' C c = 1 := (QuotientGroup.eq_one_iff c).mpr hc
    rw [map_mul, hc1, one_mul]
  have hQsolv : Group.IsSolvable (P ⧸ C) := by
    haveI : Group.IsSolvable U := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hU
    exact Group.isSolvable_of_surjective (f := r) hr
  have hC_top : C = ⊤ := by
    have hsub : Subsingleton (P ⧸ C) := by
      by_contra h
      haveI : Nontrivial (P ⧸ C) := not_subsingleton_iff_nontrivial.mp h
      haveI hPperf : Group.IsPerfect P := Group.isPerfect_def.mpr hperf
      haveI : Group.IsPerfect (P ⧸ C) :=
        Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' C) (QuotientGroup.mk'_surjective C)
      exact Group.IsPerfect.not_isSolvable (P ⧸ C) hQsolv
    rw [eq_top_iff]
    intro p _
    by_contra hp
    have h1 : QuotientGroup.mk' C p = 1 := Subsingleton.elim _ _
    exact hp ((QuotientGroup.eq_one_iff p).mp h1)
  intro u hu
  rw [Subgroup.mem_center_iff]
  intro p
  have hp : p ∈ C := by
    rw [hC_top]
    exact Subgroup.mem_top p
  exact (Subgroup.mem_centralizer_iff.mp hp u hu).symm

end CFSG.ComponentClassification.GrSLit.L34Sec5S
