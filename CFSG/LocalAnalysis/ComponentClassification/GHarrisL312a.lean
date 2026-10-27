module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisFusExt2
public import Certificates.Certificate22609
public import Certificates.Certificate22608

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

namespace GHSylow

variable (D : GHSylow G)

omit [Finite G] in
theorem zword_B : Fus.yIX.words.getD 30 [] = [1, 2, 1, 2] ∧
    Fus.yIIX.words.getD 30 [] = [1, 2, 1, 2] ∧
    Fus.bIIA34.words.getD 30 [] = [1, 2, 1, 2] ∧ Fus.bIZ.words.getD 30 [] = [1, 2, 1, 2] ∧
    Fus.yIX.zIdx = 30 ∧ Fus.yIIX.zIdx = 30 ∧ Fus.bIIA34.zIdx = 30 ∧ Fus.bIZ.zIdx = 30 := by
  decide

theorem y_fusion_A
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hE : ∀ {g u : G}, g ∈ D.M → u ∈ D.E → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ D.E)
    (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i)) :
    ∃ g ∈ D.M, g⁻¹ * D.y * g = D.x := by
  obtain ⟨hcls, -⟩ := Certificates.certificate22608
  obtain ⟨hyZ, hyX, -⟩ := Certificates.certificate22609
  obtain ⟨j, g, hjext, hj, hgu, hC⟩ := D.exists_extremal_rep_S2 hidx (i := 6) (by decide)
  have hx := D.not_fusN_x_32
  have huj : D.FusN (6 : Fin 9) j := D.fusN_of_conj_rep (i := 6) hgu
  have hP' : ∀ i < [0, 0, 0, 0, 0, 5, 6, 0, 5].length,
      D.FusN i ([0, 0, 0, 0, 0, 5, 6, 0, 5].getD i i) := fun i hi => hP i hi
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exfalso
    rw [show SE.invRep 0 = SE.gen 0 by decide] at hgu hC
    have h := D.good_of_rep' (Fus.checkList_sound hyZ (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.yIZ.source = SE.invRep 6))
      (by decide : Fus.yIZ.target = SE.gen 0) hgu hC
      (D.not_fusN_of_case _ hP' huj [(5, 0)] (by simpa using (hx 0 (by simp)).1) _ (by decide))
      (fun _ => hE) (fun h => absurd h (by decide))
    have e : Fus.yIZ.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h
  · exact (D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 1 (by norm_num))).elim
  · exact (D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 2 (by norm_num))).elim
  · exact (D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 3 (by norm_num))).elim
  · rw [show SE.invRep 5 = SE.gen 6 by decide] at hgu hC
    have hA := Fus.checkList_sound hyX (List.mem_singleton_self _)
    have hsrc : Fus.yIX.source = SE.invRep 6 := by decide
    have htgt : Fus.yIX.target = SE.gen 6 := by decide
    have h := D.good_of_rep' hA hcls (congrArg D.toG hsrc) htgt hgu hC
      (D.not_fusN_of_case _ hP' huj [(5, 0), (5, 1), (5, 2)]
        (by simpa using ⟨(hx 0 (by simp)).1, (hx 1 (by simp)).1, (hx 2 (by simp)).1⟩) _
        (by decide))
      (fun _ => hE) (fun h => absurd h (by decide))
    have e : Fus.yIX.good = fun mul q => Fus.evalW mul q ([1, 2, 1, 2]) == SE.gen 0 := rfl
    rw [e] at h
    have hz : Fus.yIX.img (· * ·) (D.fusQ Fus.yIX g) 30 = SE.gen 0 := by
      have : Fus.yIX.img (· * ·) (D.fusQ Fus.yIX g) 30 =
          Fus.evalW (· * ·) (D.fusQ Fus.yIX g) [1, 2, 1, 2] := by
        unfold Fus.Data.img; rw [zword_B.1]
      rw [this]
      exact beq_iff_eq.mp h
    have hgC : ∀ s : SE, s * Fus.yIX.source = Fus.yIX.source * s →
        g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G) := by
      intro s hs
      refine (mem_inf.mp (hC _ (mem_inf.mpr ⟨D.toG_mem s,
        mem_centralizer_singleton_iff.mpr ?_⟩))).1
      rw [hsrc] at hs
      rw [← map_mul, ← map_mul, hs]
    have h30 := D.img_conj hA (by rw [hsrc, htgt]; exact hgu) hgC (k := 30) (by norm_num)
    rw [hz, show Fus.yIX.elt (· * ·) 30 = SE.gen 0 by decide] at h30
    refine ⟨g, mem_centralizer_singleton_iff.mpr ?_, hgu⟩
    calc g * D.z = g * (g⁻¹ * D.toG (SE.gen 0) * g) := by rw [← h30]
      _ = D.z * g := by group


theorem false_of_aZ_B
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hE : ∀ {g u : G}, g ∈ D.M → u ∈ D.E → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ D.E)
    (hF : ∀ {g u : G}, g ∈ D.M → u ∈ D.F → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ D.F)
    (hP : ∀ i < 9, D.FusN i ([0, 0, 2, 0, 4, 5, 6, 0, 5].getD i i)) : False := by
  obtain ⟨hcls, -⟩ := Certificates.certificate22608
  obtain ⟨-, -, hbZ, hbA1L, hbX, -⟩ := Certificates.certificate22609
  obtain ⟨j, g, hjext, hj, hgu, hC⟩ := D.exists_extremal_rep_S2 hidx (i := 4) (by decide)
  have hx := D.not_fusN_x_32
  have huj : D.FusN (4 : Fin 9) j := D.fusN_of_conj_rep (i := 4) hgu
  have hP' : ∀ i < [0, 0, 2, 0, 4, 5, 6, 0, 5].length,
      D.FusN i ([0, 0, 2, 0, 4, 5, 6, 0, 5].getD i i) := fun i hi => hP i hi
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · rw [show SE.invRep 0 = SE.gen 0 by decide] at hgu hC
    have hA := Fus.checkList_sound hbZ (List.mem_singleton_self _)
    have hsrc : Fus.bIZ.source = SE.invRep 4 := by decide
    have htgt : Fus.bIZ.target = SE.gen 0 := by decide
    have h := D.good_of_rep' hA hcls (congrArg D.toG hsrc) htgt hgu hC
      (D.not_fusN_of_case _ hP' huj [(5, 0)] (by simpa using (hx 0 (by simp)).1) _ (by decide))
      (fun _ => hE) (fun _ => hF)
    have e : Fus.bIZ.good = fun mul q => SE.clsTab (Fus.evalW mul q ([1, 2, 1, 2])) == 1 := rfl
    rw [e] at h
    have hgC : ∀ s : SE, s * Fus.bIZ.source = Fus.bIZ.source * s →
        g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G) := by
      intro s hs
      refine (mem_inf.mp (hC _ (mem_inf.mpr ⟨D.toG_mem s,
        mem_centralizer_singleton_iff.mpr ?_⟩))).1
      rw [hsrc] at hs
      rw [← map_mul, ← map_mul, hs]
    have hz : Fus.bIZ.img (· * ·) (D.fusQ Fus.bIZ g) 30 =
        Fus.evalW (· * ·) (D.fusQ Fus.bIZ g) [1, 2, 1, 2] := by
      unfold Fus.Data.img; rw [zword_B.2.2.2.1]
    have h30 := D.img_conj hA (by rw [hsrc, htgt]; exact hgu) hgC (k := 30) (by norm_num)
    rw [show Fus.bIZ.elt (· * ·) 30 = SE.gen 0 by decide] at h30
    have hzinv : SE.isInvB (Fus.bIZ.img (· * ·) (D.fusQ Fus.bIZ g) 30) = true := by
      rw [← (D.fus_img hA (by rw [hsrc, htgt]; exact hgu) hgC 30 (by norm_num)).2]
      rw [show Fus.bIZ.elt (· * ·) 30 = SE.gen 0 by decide]
      exact D.isInv_conjM hgC (by rw [hsrc]; decide) (by decide)
    rw [hz] at hzinv h30
    have hcl1 : SE.clsTab (Fus.evalW (· * ·) (D.fusQ Fus.bIZ g) [1, 2, 1, 2]) = 1 :=
      beq_iff_eq.mp h
    obtain ⟨-, c, hc⟩ := SE.cls_spec hcls hzinv
    rw [hcl1, show Fin.ofNat 9 1 = 1 by decide] at hc
    set h' := g * D.toG c with hh'
    have hzt : h'⁻¹ * D.z * h' = D.t := by
      rw [hh', show (g * D.toG c)⁻¹ * D.z * (g * D.toG c) =
        (D.toG c)⁻¹ * (g⁻¹ * D.toG (SE.gen 0) * g) * D.toG c by group, ← h30, ← map_inv,
        ← map_mul, ← map_mul, hc]
    have ha : h'⁻¹ * D.a1a4 * h' = D.z := by
      rw [hh', show (g * D.toG c)⁻¹ * D.a1a4 * (g * D.toG c) =
        (D.toG c)⁻¹ * (g⁻¹ * D.a1a4 * g) * D.toG c by group, hgu, ← map_inv, ← map_mul,
        ← map_mul, SE.gen0_central c]
    obtain ⟨n, -, hnz, hnt⟩ := D.exists_swap_z_t ⟨h', hzt⟩
    have hm : h' * n ∈ D.M := mem_centralizer_singleton_iff.mpr (by
      calc h' * n * D.z = h' * n * (n⁻¹ * D.t * n) := by rw [hnt]
        _ = h' * D.t * n := by group
        _ = h' * (h'⁻¹ * D.z * h') * n := by rw [hzt]
        _ = D.z * (h' * n) := by group)
    have hat : (h' * n)⁻¹ * D.a1a4 * (h' * n) = D.t := by
      rw [show (h' * n)⁻¹ * D.a1a4 * (h' * n) = n⁻¹ * (h'⁻¹ * D.a1a4 * h') * n by group, ha, hnz]
    have htF : D.t ∈ D.F := D.toG_mem_F_iff.mpr (by decide)
    have := hF (inv_mem hm) htF (by
      rw [inv_inv, ← hat, show h' * n * ((h' * n)⁻¹ * D.a1a4 * (h' * n)) * (h' * n)⁻¹ = D.a1a4 by
        group]
      exact D.toG_mem _)
    rw [inv_inv, ← hat, show h' * n * ((h' * n)⁻¹ * D.a1a4 * (h' * n)) * (h' * n)⁻¹ = D.a1a4 by
      group] at this
    exact absurd (D.toG_mem_F_iff.mp this) (by decide)
  · exact D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 1 (by norm_num))
  · have h := D.good_of_rep' (Fus.checkList_sound hbA1L (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.bIA1L.source = SE.invRep 4))
      (by decide : Fus.bIA1L.target = SE.invRep 2) hgu hC
      (D.not_fusN_of_case _ hP' huj [(2, 0), (2, 1), (5, 0)]
        (by simpa using ⟨(D.not_fusN_of_lt hjext (j := 0) (by decide)).1,
          (D.not_fusN_of_lt hjext (j := 1) (by decide)).1, (hx 0 (by simp)).1⟩) _ (by decide))
      (fun _ => hE) (fun _ => hF)
    have e : Fus.bIA1L.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h
  · exact D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 3 (by norm_num))
  · rw [show SE.invRep 5 = SE.gen 6 by decide] at hgu hC
    have h := D.good_of_rep' (Fus.checkList_sound hbX (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.bIX.source = SE.invRep 4))
      (by decide : Fus.bIX.target = SE.gen 6) hgu hC
      (D.not_fusN_of_case _ hP' huj [(5, 0), (5, 1), (5, 2)]
        (by simpa using ⟨(hx 0 (by simp)).1, (hx 1 (by simp)).1, (hx 2 (by simp)).1⟩) _
        (by decide))
      (fun _ => hE) (fun _ => hF)
    have e : Fus.bIX.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h


theorem a1a4_fusion_B
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hE : ∀ {g u : G}, g ∈ D.M → u ∈ D.E → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ D.E)
    (hF : ∀ {g u : G}, g ∈ D.M → u ∈ D.F → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ D.F)
    (hP : ∀ i < 9, D.FusN i ([0, 0, 2, 3, 4, 5, 6, 3, 5].getD i i))
    (h30 : ¬ D.FusN 3 0) (h32 : ¬ D.FusN 3 2) :
    ∃ g ∈ D.M, g⁻¹ * D.a1a4 * g = D.a3a4 := by
  obtain ⟨hcls, -⟩ := Certificates.certificate22608
  obtain ⟨-, -, -, -, -, hZ, hA1L, hX, hA34, -⟩ := Certificates.certificate22609
  obtain ⟨j, g, hjext, hj, hgu, hC⟩ := D.exists_extremal_rep_S2 hidx (i := 4) (by decide)
  have hx := D.not_fusN_x_32
  have huj : D.FusN (4 : Fin 9) j := D.fusN_of_conj_rep (i := 4) hgu
  have hP' : ∀ i < [0, 0, 2, 3, 4, 5, 6, 3, 5].length,
      D.FusN i ([0, 0, 2, 3, 4, 5, 6, 3, 5].getD i i) := fun i hi => hP i hi
  have hbase : ∀ p ∈ [(3, 0), (3, 2), (5, 0), (5, 2), (5, 3)], ¬ D.FusN p.1 p.2 := by
    simpa using ⟨h30, h32, (hx 0 (by simp)).1, (hx 2 (by simp)).1, (hx 3 (by simp)).1⟩
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exfalso
    rw [show SE.invRep 0 = SE.gen 0 by decide] at hgu hC
    have h := D.good_of_rep' (Fus.checkList_sound hZ (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.bIIZ.source = SE.invRep 4))
      (by decide : Fus.bIIZ.target = SE.gen 0) hgu hC
      (D.not_fusN_of_case _ hP' huj _ hbase _ (by decide)) (fun _ => hE) (fun _ => hF)
    have e : Fus.bIIZ.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h
  · exact (D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 1 (by norm_num))).elim
  · exfalso
    have h := D.good_of_rep' (Fus.checkList_sound hA1L (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.bIIA1L.source = SE.invRep 4))
      (by decide : Fus.bIIA1L.target = SE.invRep 2) hgu hC
      (D.not_fusN_of_case _ hP' huj ([(2, 0), (2, 1)] ++ [(3, 0), (3, 2), (5, 0), (5, 2), (5, 3)])
        (by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            rcases hp with rfl | rfl
            · exact (D.not_fusN_of_lt hjext (j := 0) (by decide)).1
            · exact (D.not_fusN_of_lt hjext (j := 1) (by decide)).1
          · exact hbase p hp) _ (by decide)) (fun _ => hE) (fun _ => hF)
    have e : Fus.bIIA1L.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h
  · have hA := Fus.checkList_sound hA34 (List.mem_singleton_self _)
    have hsrc : D.toG Fus.bIIA34.source = D.a1a4 := congrArg D.toG (by decide)
    have htgt : Fus.bIIA34.target = SE.invRep 3 := by decide
    have h := D.good_of_rep' hA hcls hsrc htgt hgu hC
      (D.not_fusN_of_case _ hP' huj ([(3, 1)] ++ [(3, 0), (3, 2), (5, 0), (5, 2), (5, 3)])
        (by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            subst hp
            exact (D.not_fusN_of_lt hjext (j := 1) (by decide)).1
          · exact hbase p hp) _ (by decide)) (fun _ => hE) (fun _ => hF)
    have e : Fus.bIIA34.good = fun mul q => Fus.evalW mul q ([1, 2, 1, 2]) == SE.gen 0 := rfl
    rw [e] at h
    have hz : Fus.bIIA34.img (· * ·) (D.fusQ Fus.bIIA34 g) 30 = SE.gen 0 := by
      have : Fus.bIIA34.img (· * ·) (D.fusQ Fus.bIIA34 g) 30 =
          Fus.evalW (· * ·) (D.fusQ Fus.bIIA34 g) [1, 2, 1, 2] := by
        unfold Fus.Data.img; rw [zword_B.2.2.1]
      rw [this]
      exact beq_iff_eq.mp h
    exact ⟨g, D.mem_M_of_fixz hA hsrc htgt hgu hC (by norm_num) (by decide) hz, hgu⟩
  · exfalso
    rw [show SE.invRep 5 = SE.gen 6 by decide] at hgu hC
    have h := D.good_of_rep' (Fus.checkList_sound hX (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.bIIX.source = SE.invRep 4))
      (by decide : Fus.bIIX.target = SE.gen 6) hgu hC
      (D.not_fusN_of_case _ hP' huj ([(5, 1)] ++ [(3, 0), (3, 2), (5, 0), (5, 2), (5, 3)])
        (by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            subst hp
            exact (hx 1 (by simp)).1
          · exact hbase p hp) _ (by decide)) (fun _ => hE) (fun _ => hF)
    have e : Fus.bIIX.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h


theorem y_fusion_B
    (hidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (hE : ∀ {g u : G}, g ∈ D.M → u ∈ D.E → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ D.E)
    (hF : ∀ {g u : G}, g ∈ D.M → u ∈ D.F → g⁻¹ * u * g ∈ (D.S : Subgroup G) → g⁻¹ * u * g ∈ D.F)
    (hP : ∀ i < 9, D.FusN i ([0, 0, 0, 3, 3, 5, 6, 3, 5].getD i i))
    (h30 : ¬ D.FusN 3 0) (h32 : ¬ D.FusN 3 2) :
    ∃ g ∈ D.M, g⁻¹ * D.y * g = D.x := by
  obtain ⟨hcls, -⟩ := Certificates.certificate22608
  obtain ⟨-, -, -, -, -, -, -, -, -, hZ, hA34, hX⟩ := Certificates.certificate22609
  obtain ⟨j, g, hjext, hj, hgu, hC⟩ := D.exists_extremal_rep_S2 hidx (i := 6) (by decide)
  have hx := D.not_fusN_x_32
  have huj : D.FusN (6 : Fin 9) j := D.fusN_of_conj_rep (i := 6) hgu
  have hP' : ∀ i < [0, 0, 0, 3, 3, 5, 6, 3, 5].length,
      D.FusN i ([0, 0, 0, 3, 3, 5, 6, 3, 5].getD i i) := fun i hi => hP i hi
  have hbase : ∀ p ∈ [(3, 0), (3, 2), (5, 0), (5, 2), (5, 3)], ¬ D.FusN p.1 p.2 := by
    simpa using ⟨h30, h32, (hx 0 (by simp)).1, (hx 2 (by simp)).1, (hx 3 (by simp)).1⟩
  rcases hj with rfl | rfl | rfl | rfl | rfl
  · exfalso
    rw [show SE.invRep 0 = SE.gen 0 by decide] at hgu hC
    have h := D.good_of_rep' (Fus.checkList_sound hZ (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.yIIZ.source = SE.invRep 6))
      (by decide : Fus.yIIZ.target = SE.gen 0) hgu hC
      (D.not_fusN_of_case _ hP' huj _ hbase _ (by decide)) (fun _ => hE) (fun _ => hF)
    have e : Fus.yIIZ.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h
  · exact (D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 1 (by norm_num))).elim
  · exact (D.false_of_extremal_fused hjext (k := 0) (by decide) (hP 2 (by norm_num))).elim
  · exfalso
    have h := D.good_of_rep' (Fus.checkList_sound hA34 (List.mem_singleton_self _)) hcls
      (congrArg D.toG (by decide : Fus.yIIA34.source = SE.invRep 6))
      (by decide : Fus.yIIA34.target = SE.invRep 3) hgu hC
      (D.not_fusN_of_case _ hP' huj ([(3, 1)] ++ [(3, 0), (3, 2), (5, 0), (5, 2), (5, 3)])
        (by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            subst hp
            exact (D.not_fusN_of_lt hjext (j := 1) (by decide)).1
          · exact hbase p hp) _ (by decide)) (fun _ => hE) (fun _ => hF)
    have e : Fus.yIIA34.good = fun _ _ => false := rfl
    rw [e] at h
    exact Bool.false_ne_true h
  · rw [show SE.invRep 5 = SE.gen 6 by decide] at hgu hC
    have hA := Fus.checkList_sound hX (List.mem_singleton_self _)
    have hsrc : D.toG Fus.yIIX.source = D.y := congrArg D.toG (by decide)
    have htgt : Fus.yIIX.target = SE.gen 6 := by decide
    have h := D.good_of_rep' hA hcls hsrc htgt hgu hC
      (D.not_fusN_of_case _ hP' huj ([(5, 1)] ++ [(3, 0), (3, 2), (5, 0), (5, 2), (5, 3)])
        (by
          intro p hp
          rcases List.mem_append.mp hp with hp | hp
          · simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
            subst hp
            exact (hx 1 (by simp)).1
          · exact hbase p hp) _ (by decide)) (fun _ => hE) (fun _ => hF)
    have e : Fus.yIIX.good = fun mul q => Fus.evalW mul q ([1, 2, 1, 2]) == SE.gen 0 := rfl
    rw [e] at h
    have hz : Fus.yIIX.img (· * ·) (D.fusQ Fus.yIIX g) 30 = SE.gen 0 := by
      have : Fus.yIIX.img (· * ·) (D.fusQ Fus.yIIX g) 30 =
          Fus.evalW (· * ·) (D.fusQ Fus.yIIX g) [1, 2, 1, 2] := by
        unfold Fus.Data.img; rw [zword_B.2.1]
      rw [this]
      exact beq_iff_eq.mp h
    exact ⟨g, D.mem_M_of_fixz hA hsrc htgt hgu hC (by norm_num) (by decide) hz, hgu⟩


end GHSylow

end CFSG.ComponentClassification.GHarris
