module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BNF
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.BRank0
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.F3Sylow
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.HeisAction
public import CFSG.HardMathSupport.Solomon.Coordinator.B3B.ExpVariant
public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporBMInvHat
public import CFSG.HardMathSupport.Solomon.Proving.AutSixBalance

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.B3B

open CFSG.Blueprint CFSG.Open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BThreeFi23
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance.BSevenLocal
open scoped Matrix

set_option linter.unusedSectionVars false

theorem nfProd_eq_heisNF {G : Type*} [Group G] (x y : Fin 4 → G) (z : G) (e : List ℕ)
    (he : ∀ i < 9, e.getD i 0 < 3) :
    nfProd x y z e = heisNF x y z (fun i => ((e.getD i.val 0 : ℕ) : ZMod 3))
      ((e.getD 8 0 : ℕ) : ZMod 3) := by
  unfold nfProd heisNF
  simp only [List.ofFn_succ, List.ofFn_zero, List.prod_cons, List.prod_nil, mul_one,
    Fin.coe_castAdd, Fin.coe_natAdd, Fin.val_zero, Fin.val_succ, Fin.succ_zero_eq_one,
    Fin.succ_one_eq_two]
  rw [ZMod.val_cast_of_lt (he 0 (by norm_num)), ZMod.val_cast_of_lt (he 1 (by norm_num)),
    ZMod.val_cast_of_lt (he 2 (by norm_num)), ZMod.val_cast_of_lt (he 3 (by norm_num)),
    ZMod.val_cast_of_lt (he 4 (by norm_num)), ZMod.val_cast_of_lt (he 5 (by norm_num)),
    ZMod.val_cast_of_lt (he 6 (by norm_num)), ZMod.val_cast_of_lt (he 7 (by norm_num)),
    ZMod.val_cast_of_lt (he 8 (by norm_num))]
  simp only [mul_assoc]
  rfl

theorem mem_normalizer_centralizer_of_conj_eq_sq {G : Type*} [Group G] {g z : G}
    (hz : z ^ 3 = 1) (h : g * z * g⁻¹ = z ^ 2) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer ({z} : Set G) : Set G) := by
  have hz4 : (z ^ 2) ^ 2 = z := by
    rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hz, one_mul]
  have key : ∀ b : G, Commute b z ↔ Commute b (z ^ 2) := fun b =>
    ⟨fun hb => hb.pow_right 2, fun hb => by rw [← hz4]; exact hb.pow_right 2⟩
  rw [Subgroup.mem_normalizer_iff]
  intro a
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  change Commute a z ↔ Commute (g * a * g⁻¹) z
  rw [← Commute.conj_iff g, h, ← key]


theorem exists_z_components_dvd :
    ∃ z : NativeSporadic.B, orderOf z = 3 ∧ rk z = 2916 ∧
      ∀ K : Subgroup NativeSporadic.B,
        IsComponentOf K (Subgroup.centralizer ({z} : Set NativeSporadic.B)) →
        9 ∣ (Subgroup.center ↥K).index → 3 ^ 8 ∣ Nat.card (MulAut ↥K) := by
  obtain ⟨x, y, z, g, hH, hy3, hgx, hgy, hgz, hrk⟩ := bNF_holds
  haveI : Finite NativeSporadic.B := CFSG.Monster.B.Pinned.finite_B
  have hn : 0 < 4 := by norm_num
  have hz3 : z ^ 3 = 1 := hH.zp
  refine ⟨z, orderOf_z hH, hrk, ?_⟩
  have hdX : ∀ (k : Fin 2) (j : Fin 4), ∀ i < 9,
      (nfXData.getD (4 * k.val + j.val) []).getD i 0 < 3 := by
    set_option maxRecDepth 100000 in decide
  have hdY : ∀ (k : Fin 2) (j : Fin 4), ∀ i < 9,
      (nfYData.getD (4 * k.val + j.val) []).getD i 0 < 3 := by
    set_option maxRecDepth 100000 in decide
  set Q := heisSub x y with hQ
  have hgxQ : ∀ k j, g k * x j * (g k)⁻¹ ∈ Q := fun k j => by
    rw [hgx k j, nfProd_eq_heisNF _ _ _ _ (hdX k j)]
    exact heisNF_mem hH hn _ _
  have hgyQ : ∀ k j, g k * y j * (g k)⁻¹ ∈ Q := fun k j => by
    rw [hgy k j, nfProd_eq_heisNF _ _ _ _ (hdY k j)]
    exact heisNF_mem hH hn _ _
  have hgN : ∀ k, g k ∈ Subgroup.normalizer (Q : Set NativeSporadic.B) := fun k =>
    mem_normalizer_of_conj_mem (hgxQ k) (hgyQ k)
  have hmat : ∀ k : Fin 2, heisMat hH hy3 (g k) = tMat k.val := fun k =>
    heisMat_eq_of_nf hH hy3 hn (tMat k.val)
      (fun j => ⟨_, by
        rw [hgx k j, nfProd_eq_heisNF _ _ _ _ (hdX k j)]
        congr 1
        funext i
        simp [tMat]⟩)
      (fun j => ⟨_, by
        rw [hgy k j, nfProd_eq_heisNF _ _ _ _ (hdY k j)]
        congr 1
        funext i
        simp [tMat]⟩)
  have hmat0 : heisMat hH hy3 (g 0) = tA := by
    have h0 := hmat 0
    simp only [Fin.val_zero] at h0
    rw [h0, tMat_zero]
  have hmat1 : heisMat hH hy3 (g 1) = tB := by
    have h1 := hmat 1
    simp only [Fin.val_one] at h1
    rw [h1, tMat_one]
  set L : Subgroup NativeSporadic.B :=
    Subgroup.closure (Set.range g ∪ (Set.range x ∪ Set.range y)) with hL
  have hQL : Q ≤ L := Subgroup.closure_mono Set.subset_union_right
  have hxQ : ∀ i, x i ∈ Q := fun i => Subgroup.subset_closure (Or.inl ⟨i, rfl⟩)
  have hyQ : ∀ i, y i ∈ Q := fun i => Subgroup.subset_closure (Or.inr ⟨i, rfl⟩)
  have hLN : L ≤ Subgroup.normalizer (Q : Set NativeSporadic.B) := by
    rw [hL, Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact hgN k
    · exact Subgroup.le_normalizer (hxQ i)
    · exact Subgroup.le_normalizer (hyQ i)
  set X := Subgroup.centralizer ({z} : Set NativeSporadic.B) with hX
  have hLX : L ≤ Subgroup.normalizer (X : Set NativeSporadic.B) := by
    rw [hL, Subgroup.closure_le]
    rintro _ (⟨k, rfl⟩ | ⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact mem_normalizer_centralizer_of_conj_eq_sq hz3 (hgz k)
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (hH.zx i))
    · exact Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.2 (hH.zy i))
  have hgL : ∀ k, g k ∈ L := fun k => Subgroup.subset_closure (Or.inl ⟨k, rfl⟩)
  have hHim : sylH ≤ (heisRepL hH hy3 hn L hLN).range := by
    refine sylH_le.trans ((Subgroup.closure_le _).2 ?_)
    rintro _ (rfl | rfl)
    · exact mem_range_heisRepL hH hy3 hn L hLN (hgL 0) (by rw [hmat0]; rfl)
    · exact mem_range_heisRepL hH hy3 hn L hLN (hgL 1) (by rw [hmat1]; rfl)
  have hG3 : (Nat.card NativeSporadic.B).factorization 3 ≤ 2 * 4 + 1 + 4 := by
    rw [factorization_card_B_three]
  have hCQ := hCQ_of_image hH hy3 hn L hQL hLN 4 sylH hHim card_sylH hG3
  have hhN : ∀ i : Fin 2, (![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] : Fin 2 → NativeSporadic.B) i ∈
      Subgroup.normalizer (Q : Set NativeSporadic.B) := by
    intro i
    fin_cases i
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hgN 0) (hgN 1)) 60
    · exact Subgroup.pow_mem _ (Subgroup.mul_mem _ (hgN 1) (hgN 0)) 60
  have hmat60 : ∀ i : Fin 2,
      heisMat hH hy3 ((![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] : Fin 2 → NativeSporadic.B) i) =
        hM i := by
    intro i
    fin_cases i
    · show heisMat hH hy3 ((g 0 * g 1) ^ 60) = hA
      rw [heisMat_pow hH hy3 (Subgroup.mul_mem _ (hgN 0) (hgN 1)),
        heisMat_mul hH hy3 (hgN 0) (hgN 1), hmat0, hmat1]
      exact pow_sixty_tA_tB
    · show heisMat hH hy3 ((g 1 * g 0) ^ 60) = hB
      rw [heisMat_pow hH hy3 (Subgroup.mul_mem _ (hgN 1) (hgN 0)),
        heisMat_mul hH hy3 (hgN 1) (hgN 0), hmat0, hmat1]
      exact pow_sixty_tB_tA
  have hdich : ∀ N : Subgroup NativeSporadic.B, N ≤ Q →
      (∀ a ∈ L, a ^ 60 ∈ Subgroup.normalizer (N : Set NativeSporadic.B)) →
        N ≤ Subgroup.zpowers z ∨ N = Q := by
    intro N hNQ hNn
    refine dich_of_irred hH hy3 hn ![(g 0 * g 1) ^ 60, (g 1 * g 0) ^ 60] hhN
      (fun U hU => irred_hAB U fun i v hv => by
        have := hU i v hv
        rwa [hmat60 i] at this) N hNQ (fun i => ?_)
    fin_cases i
    · exact hNn _ (Subgroup.mul_mem _ (hgL 0) (hgL 1))
    · exact hNn _ (Subgroup.mul_mem _ (hgL 1) (hgL 0))
  have hidx : ¬ (Subgroup.zpowers z).relIndex Q ∣ (6 : ℕ).factorial := by
    rw [hQ, relIndex_zpowers_heisSub hH hy3 hn]
    decide
  have hG : ¬ 9 ^ (6 + 1) ∣ Nat.card NativeSporadic.B := by
    intro hd
    have h14 : 3 ^ 14 ∣ Nat.card NativeSporadic.B := by
      have : (9 : ℕ) ^ (6 + 1) = 3 ^ 14 := by norm_num
      rwa [this] at hd
    have hpos : Nat.card NativeSporadic.B ≠ 0 := Nat.card_pos.ne'
    have := (Nat.prime_three.pow_dvd_iff_le_factorization hpos).1 h14
    rw [factorization_card_B_three] at this
    omega
  have hm : ∀ k, 0 < k → k ≤ 6 → k ∣ 60 := by
    intro k hk0 hk6
    interval_cases k <;> decide
  have main := component_relIndex_dvd_card_mulAut_exp z X Q L 6 60 hm hQL hLN hLX hCQ hdich hidx hG
  intro K hK h9
  have hdvd := main K hK h9
  rwa [hQ, relIndex_zpowers_heisSub hH hy3 hn] at hdvd

theorem exists_z_no_hatSix :
    ∃ z : NativeSporadic.B, orderOf z = 3 ∧ rk z = 2916 ∧
      ∀ K : Subgroup NativeSporadic.B,
        IsComponentOf K (Subgroup.centralizer ({z} : Set NativeSporadic.B)) →
        CFSG.HardMathSupport.Solomon.Coordinator.IsHatSix ↥K → False := by
  obtain ⟨z, hz3, hrk, main⟩ := exists_z_components_dvd
  refine ⟨z, hz3, hrk, ?_⟩
  intro K hK hK6
  obtain ⟨hperf, -, ⟨e⟩⟩ := hK6
  have hcardA6 : Nat.card (alternatingGroup (Fin 6)) = 360 := by
    rw [Nat.card_eq_fintype_card, card_alternatingGroup]
    decide
  have hidxK : (Subgroup.center ↥K).index = 360 := by
    rw [Subgroup.index, ← hcardA6]
    exact Nat.card_congr e.toEquiv
  have hdvd := main K hK (by rw [hidxK]; norm_num)
  have hinj := CFSG.HardMathSupport.Timmesfeld.Coordinator.autCenterQuot_injective_of_perfect hperf
  have h1 : Nat.card (MulAut ↥K) ∣ Nat.card (MulAut (↥K ⧸ Subgroup.center ↥K)) :=
    Subgroup.card_dvd_of_injective _ hinj
  have h2 : Nat.card (MulAut (↥K ⧸ Subgroup.center ↥K)) = 1440 := by
    rw [← CFSG.HardMathSupport.Solomon.Proving.AutSixBalance.card_mulAut_alt6]
    exact Nat.card_congr (MulAut.congr e).toEquiv
  rw [h2] at h1
  have := hdvd.trans h1
  revert this
  decide

theorem hUB_holds : ∀ s : NativeSporadic.B, orderOf s = 3 →
    (∀ d : NativeSporadic.B, CFSG.Monster.GMS.BabyInv 0 d → d * s * d⁻¹ ≠ s⁻¹) →
    ∀ K : Subgroup NativeSporadic.B,
      IsComponentOf K (Subgroup.centralizer ({s} : Set NativeSporadic.B)) →
      CFSG.HardMathSupport.Solomon.Coordinator.IsHatSix ↥K → False := by
  intro s hs hunv K hK hK6
  obtain ⟨z, hz3, hzrk, hzno⟩ := exists_z_no_hatSix
  have hzc : IsConj z (phiB (t3 1)) := isConj_phiB_t3_one_of_rk hz3 hzrk
  have hnot0 : ¬ IsConj s (phiB (t3 0)) := by
    intro hc
    obtain ⟨d, hd, hdr⟩ := phiB_t3_zero_inverted
    obtain ⟨c, hcx⟩ := isConj_iff.1 hc
    refine hunv (c⁻¹ * d * c) (CFSG.Monster.GMS.BabyInv.of_isConj hd
      (isConj_iff.2 ⟨c⁻¹, by simp⟩)) ?_
    have hx' : s = c⁻¹ * phiB (t3 0) * c := by rw [← hcx]; group
    calc c⁻¹ * d * c * s * (c⁻¹ * d * c)⁻¹
        = c⁻¹ * (d * phiB (t3 0) * d⁻¹) * c := by rw [hx']; group
      _ = s⁻¹ := by rw [hdr, hx']; group
  have hsc : IsConj s (phiB (t3 1)) := by
    obtain ⟨i, hi⟩ := bThree_classes s hs
    fin_cases i
    · exact absurd hi hnot0
    · exact hi
    · exact absurd (hi.trans bThreeRc_holds) hnot0
    · exact hi.trans bThreeRd_holds
  obtain ⟨c, hc⟩ := isConj_iff.1 (hsc.trans hzc.symm)
  refine bmInv_false_of_hatSix_of_mulEquiv (MulAut.conj c) hK hK6 ?_
  rw [MulAut.conj_apply, hc]
  exact hzno

end CFSG.HardMathSupport.Solomon.Coordinator.B3B
