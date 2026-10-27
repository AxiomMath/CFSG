module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.R6Lem65
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Final
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65AStr
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Syl
public import CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65Ext5

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec6 CFSG.GH74.GLS.IVK

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ : Subgroup G}

theorem caseA_false (h : Std4 G z S K₁ K₂) (hII : II4_4_4_center)
    (hrec : Bg.B_reciprocity) (hq : II4_4_quat) (hd : IsDoubleCoverOfAlt (HatT K₁) 7)
    (hA : ∀ u ∈ Pz S z, orderOf u = 2 → IsConj z u) : False := by
  have hM := m4_of_std hII h
  have e1 : M.Pm S K₁ K₂ ⊓ K₁ = Pof S K₁ := by
    unfold M.Pm Pof
    rw [inf_assoc, inf_eq_right.2 (le_sup_left : K₁ ≤ K₁ ⊔ K₂)]
  have hP : M.Syl2In (S ⊓ K₁) K₁ := by
    have := hM.Pi_syl (K := K₁) (Or.inl rfl)
    rw [e1] at this
    exact this
  obtain ⟨a, haSK, ha8⟩ := exists_order_eight hP hd
  obtain ⟨u, huS, huK, hu2, hu1, huz, hau⟩ := exists_u h hII hq haSK.2 haSK.1 ha8
  have huP : u ∈ Pz S z := by
    rw [Pz_eq h]
    exact ⟨huS, huK⟩
  have hu2' : orderOf u = 2 := orderOf_eq_prime (by rw [sq]; exact hu2) hu1
  have huC : u ∈ centralizer ({z} : Set G) := hM.S_syl.1 huS
  have huN : u ∈ normalizer (K₁ : Set G) :=
    (sup_le Subgroup.le_normalizer hM.n₂₁ : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G)) huK
  exact not_isConj_of_order_eight h hII hrec hd haSK.2 ha8 huz huC huN hau (hA u huP hu2')

theorem caseB_false {t : G} (h : Cfg65 G z S K₁ K₂ t)
    (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) (h4hij : IVK_1_4hij_outer) (hFS : FStar_C)
    (h327 : IG_3_27) (hB2 : B_B2_g4) (h714 : IVK_7_14_g4) (hkgh : KGH G) : False := by
  obtain ⟨a, b, haP, hbP, ha8, hconj, hcent, hbinv, hbsq⟩ := h.exists_a₁ hII
  have hAB : AB65 S K₁ a b := ⟨haP, hbP, ha8, hconj, hcent, hbinv, hbsq⟩
  have hzw := h.z_mem_cent_tz hII
  have hI := h.I_isPCompIn hII h327
  have hAc := ABar_isComponent h.std.simple h.std.gen4 hB2 h.std.orderOf_z (h.orderOf_tz hII) hzw hI
  have hAle := ABar_le_centralizer h.std.orderOf_z hzw hI
  obtain ⟨hA7, hZodd⟩ := h.ABar_a7 hII h327 hB2 h.d₁
  obtain ⟨L, hL, hcases⟩ := pump_dichotomy h.std.orderOf_z hzw hI
  obtain ⟨T, hT, ⟨φ⟩, h8⟩ := h.exists_T hAB hII h4hij hrec
  have hC := h.fourth_power_centre hAB hII h4hij
  have hX4 := CFSG.GH74.L5U5.gen4_centralizerBar h.std.gen4 (t * z)
  have hGH : ∀ L : Subgroup (barQ ↥(centralizer ({t * z} : Set G))), CFSG.IsComponent L →
      GHList (↥L ⧸ center ↥L) := fun L hL =>
    Generic.ghList_of_quasisimple h.std.simple.1 h.std.simple.2.1 hkgh (h.orderOf_tz hII) hL.1
  have hs : sBar z (t * z) hzw * sBar z (t * z) hzw = 1 :=
    mul_self_eq_one_of_orderOf_eq_two (orderOf_sBar h.std.orderOf_z hzw)
  exact abstract_final h714 hX4 hGH hs (CFSG.GH74.L5U5.xbar_mem_center (t * z))
    (CFSG.GH74.L5U5.orderOf_xbar (h.orderOf_tz hII)) h8 hAle hAc
    (fun B hBle hB => h.ABar_unique hII hFS h327 hBle hB) hA7 hZodd hL hcases hT φ hC

theorem lem65_core_of_714
    (hII : II4_4_4_center) (hrec : Bg.B_reciprocity) (h41 : Prop4_1) (hFS : FStar_C)
    (h4hij : IVK_1_4hij_outer) (hq : II4_4_quat) (h327 : IG_3_27) (hB2 : B_B2_g4)
    (h714 : IVK_7_14_g4)
    (hkgh : ∀ (G : Type) [Group G] [Finite G] (z : G) (S K₁ K₂ : Subgroup G),
      Std4 G z S K₁ K₂ → KGH G) : Lem65_core := by
  intro G _ _ z S K₁ K₂ h hQ ha₁ ha₂ hd
  obtain ⟨-, hcase, -⟩ := h41 G z S K₁ K₂ h
  rcases hcase with hA | ⟨t, htS, htc, htne, htint, htfus, htz⟩
  · exact caseA_false h hII hrec hq hd hA
  · exact caseB_false ⟨h, hQ, ha₁, hd, htS, htc, htne, htint, htfus, htz⟩ hII hrec h4hij hFS h327 hB2
      h714 (hkgh G z S K₁ K₂ h)

end CFSG.GH74.GLS.Stage1.Thm3.Sec6.L65
