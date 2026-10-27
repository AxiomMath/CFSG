module

public import CFSG.GH74.Generic.BProg.B3.DictS1Three

public section

namespace CFSG.GH74.Generic.BProg.B3

open CFSG CFSG.GH74 CFSG.GH74.L5U5 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg
  CFSG.Assembly.LowTwoRank Subgroup DictS1Three

theorem dictS1Q3J_proved : DictS1Q3J := by
  intro G _ _ x K hset hmax _hthin hfront u hu hf F _ _ hF3 hlin Fr hFr
  have hx4 : Fr.X 4 = x := by
    rw [hFr]
    rfl
  subst hx4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hx : orderOf (Fr.X 4) = 2 := hset.inv
  have hF4 : Nat.card F % 4 = 3 := by rw [hF3]
  have h2 : (2 : F) ≠ 0 := S1.q3_two_ne_zero hF3
  have hg2 : GLS.InG2 ↥K := hmax.1.2.2
  have hmin : ∀ (z : G) (L : Subgroup (CentralizerBar z)), G2Pair z L → d2 ↥K ≤ d2 ↥L :=
    fun z L hp => (hmax.2 z L hp).1
  have hNo : NoAltJ2 G :=
    noAltJ2_of_minDepth hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hg2 hmin
      (Or.inl (d2_eq_six_of_shapeS1 hset.comp hg2 hset.shape))
  have cfg := Fr.cfg hF3
  set D4 := Fr.D 4 with hD4
  have hDK4 : D4.K = K := by
    obtain ⟨K', -, -, hfront', -, e', -⟩ := hlin 4
    have hK'K : K' = K := hfront'.layer_eq.symm.trans hfront.layer_eq
    have hcK : Nat.card ↥K' = Nat.card ↥(StatedSL 4 F) := Nat.card_congr e'.toEquiv
    rw [hK'K] at hcK
    have hcK' : Nat.card ↥K = Nat.card ↥(StatedSL 4 F) := hcK
    have hKperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hset.comp.1.1
    have hle : K ≤ D4.K := D4.perf_le K hKperf
    have hcard : Nat.card ↥D4.K ≤ Nat.card ↥K :=
      ((Nat.card_congr D4.iso.toEquiv).trans hcK'.symm).le
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  obtain ⟨s, hsb, hsmat, hss, hs1, -⟩ := S1.exists_zblk h2 (c := 2) (d := 3) (by decide)
  have hc : Fr.X 2 * Fr.X 3 = D4.ι s := Fr.X23_eq_ι hF3 hsmat hss hs1 hsb
  have hcJ3 : Fr.X 2 * Fr.X 3 ∈ (S1.blkLin (F := F) 2 3).map D4.ι := ⟨s, hsb, hc.symm⟩
  obtain ⟨hxι, hxcι, -, hy2, hyne, hJle, hS⟩ :=
    frame_split_core hF4 hx D4 (Fr.xK 4) hcJ3 cfg.c2
  rw [hDK4] at hS
  set Iw : Subgroup G := (⊤ : Subgroup ↥(StatedSL 4 F)).map D4.ι with hIw
  have hKq : IsQuasisimple ↥D4.K := by
    rw [hDK4]
    exact hset.comp.1
  have hIwP : IsPCompIn 2 (centralizer ({Fr.X 4} : Set G)) Iw := isPCompIn_range_ι D4 hKq
  have himg : S3.imgBar (Fr.X 4) Iw = K := (imgBar_range_ι D4).trans hDK4
  have hOnly : S3.OnlyInvX (Fr.X 4) K := by
    intro w hw' hw2
    rw [hfront.cent_eq] at hw'
    rcases B1.PilotS5.mem_zpowers_of_two (B1.PilotS5.orderOf_xbar hx) hw' with h | h
    · rw [h, orderOf_one] at hw2
      omega
    · exact h
  have hJ2 : IsJ2 (Fr.X 4) Iw :=
    isJ2_of_isPCompIn hset.simple hset.nonab hset.rank hset.kgh hx hset.comp hg2 hmin hOnly hIwP himg
  obtain ⟨E, hEel, hE8, hxE, hyE⟩ := exists_e8_lin hF4
  set A : Subgroup G := E.map D4.ι with hA
  have hAIw : A ≤ Iw := Subgroup.map_mono le_top
  have hAel : CFSG.IsElementaryAbelian 2 ↥A := IsElementaryAbelian.map _
  have hA8 : Nat.card ↥A = 8 := by
    rw [hA, Subgroup.card_map_of_injective D4.ι_injective, hE8]
  have hxA : Fr.X 4 ∈ A := by
    rw [hxι]
    exact ⟨_, hxE, rfl⟩
  have hyA : Fr.X 4 * (Fr.X 2 * Fr.X 3) ∈ A := by
    rw [hxcι]
    exact ⟨_, hyE, rfl⟩
  obtain ⟨eK⟩ := B1.PilotS5.hat_equiv_imgBar hIwP
  have eKK : (↥Iw ⧸ pPrimeCore 2 ↥Iw) ≃* ↥K := eK.trans (MulEquiv.subgroupCongr himg)
  have hQ1 : QShape1 (↥Iw ⧸ pPrimeCore 2 ↥Iw) := hset.shape.1.of_mulEquiv eKK.symm
  have hsrc : IsSource2 (Fr.X 4) Iw A := ⟨hAIw.trans hIwP.1, hAel, hA8, Or.inl ⟨hAIw, hQ1⟩⟩
  have eP : (↥Iw ⧸ pPrimeCore 2 ↥Iw) ≃* ↥(StatedSL 4 F) :=
    eKK.trans ((MulEquiv.subgroupCongr hDK4).symm.trans D4.iso)
  obtain ⟨z₀, hP⟩ := B1.PilotS1.grpS1_lin hF4
  obtain ⟨-, hSq, hSZ, hY, hCY, -⟩ := B1.PilotS1.shape1_data hset.gen4 hx hIwP eP hP hQ1
  have hS' : B1.PilotS1.SplitAt F (S3.imgBar (Fr.X 4) Iw) (xbar (Fr.X 4))
      (bar (Fr.X 4) (Fr.X 4 * (Fr.X 2 * Fr.X 3)))
      (S3.imgBar (Fr.X 4) ((S1.blkLin (F := F) 0 1).map D4.ι))
      (S3.imgBar (Fr.X 4) ((S1.blkLin (F := F) 2 3).map D4.ι)) := by
    rw [himg]
    exact hS
  have hadm := isAdmPair_of_splitAt_three hF3 hx hIwP hY hCY hSq hSZ hAIw hAel hA8 hxA hyA hy2 hyne hS'
  have hle01 : (S1.blkLin (F := F) 0 1).map D4.ι ≤ Fr.Ablk := by
    have hle : (S1.blkLin (F := F) 0 1).map (Fr.D 4).ι ≤ (S1.blkLin (F := F) 0 1).map (Fr.D 2).ι :=
      Fr.blk_le_of_layers hF3 (e := 2) (f := 4) (a := 0) (b := 1) (c := 3) (d := 2) (a' := 0)
        (b' := 1) (c' := 2) (d' := 3) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide) (by decide)
    exact hle.trans (Subgroup.map_mono le_sup_right)
  have hy01 : Fr.X 4 * (Fr.X 2 * Fr.X 3) ∈ (S1.blkLin (F := F) 0 1).map D4.ι := by
    rw [hxcι]
    exact ⟨_, (splitAt_xS_yS hF4).u_mem, rfl⟩
  refine nbhdDataJ_of_parts (B := oPrimeResidualOf 2 ((S1.blkLin (F := F) 0 1).map D4.ι)) hNo hJ2
    hsrc hadm ?_ ?_ ?_ ?_ ?_
  · have e : Fr.X 2 * Fr.X 3 = (Fr.X 4)⁻¹ * (Fr.X 4 * (Fr.X 2 * Fr.X 3)) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.subset_closure (by simp)))
      (Subgroup.subset_closure (by simp))
  · intro h1
    have h := cfg.c2
    rw [h1, orderOf_one] at h
    omega
  · exact fun a ha => (cfg.A_V ha).2
  · exact oPrimeResidual_le_liftAt (fun a ha => (hJle ha).1) (fun a ha => (hJle ha).2) le_rfl
  · refine le_iSup_conj_of_quasisimple cfg.A_quasi ((Subgroup.map_subtype_le _).trans hle01)
      ⟨Fr.X 4 * (Fr.X 2 * Fr.X 3), B1.PilotS1.mem_oPrimeResidualOf_of_two hy01 cfg.y_sq, ?_⟩
    by_contra hall
    push Not at hall
    exact cfg.y_ne (cfg.A_cen _ cfg.y_mem hall)

end CFSG.GH74.Generic.BProg.B3
