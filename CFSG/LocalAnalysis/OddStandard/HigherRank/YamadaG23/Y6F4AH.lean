module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AB
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AJ
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AY
public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AM

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup CFSG.Blueprint

variable {C : Type} [Group C] {g t : C} {P M : Subgroup C} [(zpowers g).Normal]

private lemma zpowers_eq_one_or_self_of_orderOf {G : Type*} [Group G] {u : G}
    (hu : orderOf u = 2) : ∀ x ∈ zpowers u, x = 1 ∨ x = u := by
  intro x hx
  rw [Subgroup.mem_zpowers_iff] at hx
  obtain ⟨k, rfl⟩ := hx
  rw [← zpow_mod_orderOf u k, hu, Nat.cast_ofNat]
  rcases Int.emod_two_eq_zero_or_one k with h | h
  · left; rw [h, zpow_zero]
  · right; rw [h, zpow_one]

private lemma y6f4a_closure_pair_isMulCommutative (hd : Y6CData g t P M) :
    IsMulCommutative ↥(closure ({g, t} : Set C)) := by
  refine Subgroup.isMulCommutative_closure ?_
  intro a ha b hb _
  rw [Set.mem_insert_iff] at ha hb
  rcases ha with ha | ha
  · subst a
    rcases hb with hb | hb
    · subst b
      exact Commute.refl g
    · rw [Set.mem_singleton_iff] at hb
      subst b
      exact (Subgroup.mem_center_iff.mp hd.g_central t).symm
  · rw [Set.mem_singleton_iff] at ha
    subst a
    rcases hb with hb | hb
    · subst b
      exact Subgroup.mem_center_iff.mp hd.g_central t
    · rw [Set.mem_singleton_iff] at hb
      subst b
      exact Commute.refl t

theorem y6f4a_P_normal_in_D (hd : Y6CData g t P M) :
    (P.subgroupOf (centralizer ({t} : Set C))).Normal := by
  refine ⟨fun n hn x => ?_⟩
  have hnP : (n : C) ∈ P := Subgroup.mem_subgroupOf.mp hn
  obtain ⟨p, hp, v, hv, hxv⟩ := y6f4a_decomp hd x.2
  have hvn : v * (n : C) * v⁻¹ = (n : C) := by
    have hcomm : (n : C) * v = v * (n : C) := y6f4a_V_comm_P hd hnP hv
    rw [← hcomm]
    group
  have hconj : (x : C) * (n : C) * (x : C)⁻¹ = p * (n : C) * p⁻¹ := by
    rw [hxv]
    calc (p * v) * (n : C) * (p * v)⁻¹ = p * (v * (n : C) * v⁻¹) * p⁻¹ := by group
      _ = p * (n : C) * p⁻¹ := by rw [hvn]
  rw [Subgroup.mem_subgroupOf]
  change (x : C) * (n : C) * (x : C)⁻¹ ∈ P
  rw [hconj]
  exact P.mul_mem (P.mul_mem hp hnP) (P.inv_mem hp)

theorem y6f4a_D_quot_solvable (hd : Y6CData g t P M)
    [(P.subgroupOf (centralizer ({t} : Set C))).Normal] :
    Group.IsSolvable (↥(centralizer ({t} : Set C)) ⧸
      P.subgroupOf (centralizer ({t} : Set C))) := by
  let D : Subgroup C := centralizer ({t} : Set C)
  let V : Subgroup C := closure ({g, t} : Set C)
  haveI hPn : (P.subgroupOf D).Normal := y6f4a_P_normal_in_D hd
  haveI hVc : IsMulCommutative ↥V := y6f4a_closure_pair_isMulCommutative hd
  have hstep : ∀ x : ↥D, ∃ v : ↥D, (v : C) ∈ V ∧
      (QuotientGroup.mk x : ↥D ⧸ P.subgroupOf D) = QuotientGroup.mk v := by
    intro x
    obtain ⟨p, hp, v, hv, hxv⟩ := y6f4a_decomp hd x.2
    have hpD : p ∈ D := by
      rw [show D = P ⊔ V from hd.D_eq]; exact Subgroup.mem_sup_left hp
    have hvD : v ∈ D := by
      rw [show D = P ⊔ V from hd.D_eq]; exact Subgroup.mem_sup_right hv
    refine ⟨⟨v, hvD⟩, hv, ?_⟩
    have hp_mem : (⟨p, hpD⟩ : ↥D) ∈ P.subgroupOf D := by
      rw [Subgroup.mem_subgroupOf]
      exact hp
    have hx_eq : x = ⟨p, hpD⟩ * ⟨v, hvD⟩ := by
      apply Subtype.ext
      rw [Subgroup.coe_mul]
      exact hxv
    have hp_one : (QuotientGroup.mk (⟨p, hpD⟩ : ↥D) : ↥D ⧸ P.subgroupOf D) = 1 :=
      (QuotientGroup.eq_one_iff (⟨p, hpD⟩ : ↥D)).mpr hp_mem
    rw [hx_eq, QuotientGroup.mk_mul, hp_one, one_mul]
  have hcomm : ∀ a b : ↥D ⧸ P.subgroupOf D, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    obtain ⟨v, hvV, hvx⟩ := hstep x
    obtain ⟨w, hwV, hwy⟩ := hstep y
    rw [hvx, hwy, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    have hvwC : (v : C) * (w : C) = (w : C) * (v : C) :=
      setLike_mul_comm (s := V) hvV hwV
    have hvw : v * w = w * v := Subtype.ext hvwC
    rw [hvw]
  exact Group.isSolvable_of_comm hcomm

theorem y6f4a_J_perf [Finite C] (hd : Y6CData g t P M) {J : Subgroup C}
    (hJP : J ≤ P) (hJperf : ∀ B : Subgroup C, B ≤ P → Group.IsPerfect ↥B → B ≤ J) :
    ∀ B : Subgroup (C ⧸ zpowers g),
      B ≤ centralizer ({(QuotientGroup.mk t : C ⧸ zpowers g)} : Set (C ⧸ zpowers g)) →
        Group.IsPerfect ↥B → B ≤ J.map (QuotientGroup.mk' (zpowers g)) := by
  intro B hBc hBperf
  let π : C →* C ⧸ zpowers g := QuotientGroup.mk' (zpowers g)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective (zpowers g)
  have hker : π.ker ≤ Subgroup.center C := by
    rw [show π.ker = zpowers g from QuotientGroup.ker_mk' (zpowers g)]
    exact Subgroup.zpowers_le.mpr hd.g_central
  have hlift := y6f4a_perfect_lift hπ hker hBperf
  haveI hPn : (P.subgroupOf (centralizer ({t} : Set C))).Normal := y6f4a_P_normal_in_D hd
  haveI hSol : Group.IsSolvable
      (↥(centralizer ({t} : Set C)) ⧸ P.subgroupOf (centralizer ({t} : Set C))) :=
    y6f4a_D_quot_solvable hd
  have hAD : P ≤ centralizer ({t} : Set C) := by
    rw [hd.D_eq]
    exact le_sup_left
  have hKD : ⁅B.comap π, B.comap π⁆ ≤ centralizer ({t} : Set C) := by
    intro x hx
    have hxcomap : x ∈ B.comap π := hlift.2.2 hx
    have hπx : π x ∈ B := Subgroup.mem_comap.mp hxcomap
    exact y6f4a_mem_cent_of_mk hd (by simpa [π] using hBc hπx)
  have hKP : ⁅B.comap π, B.comap π⁆ ≤ P :=
    y6f4a_perfect_le_of_solvable_sub (D := centralizer ({t} : Set C)) (A := P)
      hAD hKD hlift.1
  have hKJ : ⁅B.comap π, B.comap π⁆ ≤ J := hJperf _ hKP hlift.1
  rw [← hlift.2.1]
  exact Subgroup.map_mono hKJ

theorem y6f4a_yData_of_cData [Finite C]
    (hSch : CFSG.LocalAnalysis.ComponentInitial.SchreierFor Catalog) (hd : Y6CData g t P M) :
    ∃ J M' : Subgroup (C ⧸ zpowers g),
      Y6YData (QuotientGroup.mk t : C ⧸ zpowers g) J M' := by
  obtain ⟨e⟩ := hd.P_equiv
  obtain ⟨J, hJP, hJn, hJs, hJna, hJSL, hJc, hJperf, hJaut⟩ :=
    y6f4a_J_data (C := C) hSch P e hd.P_four
  obtain ⟨eJ⟩ := y6f4a_equiv_map_of_le_P hd hJP
  obtain ⟨eM⟩ := y6f4a_equiv_map_M hd
  refine ⟨J.map (QuotientGroup.mk' (zpowers g)),
    M.map (QuotientGroup.mk' (zpowers g)), ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have ht2C : t ^ 2 = 1 := by
      have h := pow_orderOf_eq_one t
      rwa [hd.t_order] at h
    have ht2 : (QuotientGroup.mk t : C ⧸ zpowers g) ^ 2 = 1 := by
      rw [← QuotientGroup.mk_pow, ht2C]
      rfl
    have htne : (QuotientGroup.mk t : C ⧸ zpowers g) ≠ 1 := by
      intro h
      have hmem : t ∈ zpowers g := (QuotientGroup.eq_one_iff t).mp h
      rcases zpowers_eq_one_or_self_of_orderOf hd.g_order t hmem with h1 | hg
      · have h2 : orderOf (1 : C) = 2 := by simpa [h1] using hd.t_order
        rw [orderOf_one] at h2
        exact absurd h2 (by norm_num)
      · exact hd.t_ne_g hg
    exact orderOf_eq_prime ht2 htne
  · exact (MulEquiv.isSimpleGroup_congr eJ).mp hJs
  · intro hc
    apply hJna
    rw [isMulCommutative_iff] at hc ⊢
    intro a b
    exact eJ.injective (by rw [map_mul, map_mul]; exact hc (eJ a) (eJ b))
  · exact y6f4a_J_norm hd hJP hJn
  · exact y6f4a_J_cent hd hJP hJn hJc
  · exact y6f4a_J_perf hd hJP hJperf
  · obtain ⟨k, hF, hFin, hk, ⟨eSL⟩⟩ := hJSL
    exact ⟨k, hF, hFin, hk, ⟨eJ.symm.trans eSL⟩⟩
  · intro α hα
    let β : MulAut ↥J := (MulAut.congr eJ).symm α
    have hβ4 : β ^ 4 = 1 := by
      apply (MulAut.congr eJ).injective
      rw [map_pow, show (MulAut.congr eJ) β = α from (MulAut.congr eJ).apply_symm_apply α,
        hα, map_one]
    have hβ2 : β ^ 2 = 1 := hJaut β hβ4
    have h := congrArg (MulAut.congr eJ) hβ2
    have h2 : ((MulAut.congr eJ) β) ^ 2 = 1 := by simpa only [map_pow, map_one] using h
    rw [show (MulAut.congr eJ) β = α from (MulAut.congr eJ).apply_symm_apply α] at h2
    exact h2
  · exact ⟨eM.symm.trans hd.M_equiv.some⟩
  · intro m hm
    obtain ⟨m0, hm0, rfl⟩ := Subgroup.mem_map.mp hm
    simp only [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv,
      hd.M_inv m0 hm0]

end CFSG.OddStandard.HigherRank.YamadaG23
