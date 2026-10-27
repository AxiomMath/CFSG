module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8E8Levi

public section

namespace CFSG.ComponentClassification.RankTwoExceptional.E8

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.SeitzReduction (highRoot isRoot_highRoot)
open scoped Matrix

variable {K : Type} [Field K]

theorem iform_highRoot_single_e8 : ∀ j : Fin Tag.E8.rank,
    iform (highRoot .E8) (Pi.single j 1) = if j = e8Top then 1 else 0 := by
  decide +kernel

theorem iform_eq_sum_single {τ : Tag} (x y : Fin τ.rank → ℤ) :
    iform x y = ∑ j, iform x (Pi.single j 1) * y j := by
  simp only [iform, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true, Finset.sum_mul]
  rw [Finset.sum_comm]

theorem iform_highRoot_e8 (γ : Fin Tag.E8.rank → ℤ) : iform (highRoot .E8) γ = γ e8Top := by
  rw [iform_eq_sum_single]
  simp only [iform_highRoot_single_e8, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]

theorem rootChar_mulSingle_e8 (t : Kˣ) (γ : Fin Tag.E8.rank → ℤ) :
    rootChar (Pi.mulSingle e8Top t) γ = t ^ γ e8Top := by
  rw [rootChar, Finset.prod_eq_single e8Top (fun i _ hi => by simp [Pi.mulSingle_eq_of_ne hi])
    (fun h => absurd (Finset.mem_univ _) h), Pi.mulSingle_eq_same]

theorem rootTorusSL2_highRoot_e8
    (t : Kˣ) :
    rootTorusSL2 .E8 K (highRoot .E8) t = rootDiagUnit .E8 (Pi.mulSingle e8Top t) := by
  obtain ⟨-, -, -, -, h5, -⟩ :=
    exceptional_Lang_root_rank_one_torus_transport (τ := .E8) (K := K) (isRoot_highRoot .E8)
  obtain ⟨hh, hr⟩ := h5 t
  apply Units.ext
  refine end_ext_single fun b => ?_
  show _ = rootDiag (Pi.mulSingle e8Top t) (Finsupp.single b 1)
  rw [rootDiag_single]
  rcases b with i | ⟨γ, hγ⟩
  · have h := hh i
    rw [hVec] at h
    rw [h]
    simp [labelWt, rootChar_zero]
  · have h := hr γ hγ
    rw [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootVec_eq_single hγ] at h
    rw [h]
    have h2 : iform (highRoot .E8) (highRoot .E8) = 2 := by
      rw [iform_highRoot_e8]
      rfl
    rw [h2, iform_highRoot_e8, Int.mul_ediv_cancel_left _ (by norm_num : (2 : ℤ) ≠ 0)]
    simp [labelWt, rootChar_mulSingle_e8]

theorem coe_e8Rho_e8HSLHom
    (t : Kˣ) :
    ((e8Rho K (e8HSLHom K t) : adjointGroup .E8 K) : ModGL .E8 K) =
      rootDiagUnit .E8 (Pi.mulSingle e8Top t) :=
  rootTorusSL2_highRoot_e8 t

theorem torusGroup_le_adjointGroup_e8 :
    torusGroup .E8 K ≤ adjointGroup .E8 K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_adjointGroup i t

variable (K) in
@[expose] noncomputable def e8T :
    Subgroup (adjointGroup .E8 K) :=
  (torusGroup .E8 K).comap (adjointGroup .E8 K).subtype

theorem e8Q_le_e8T :
    e8Q K ≤ e8T K := by
  rintro _ ⟨t, rfl⟩
  exact (exceptional_Lang_root_rank_one_torus_transport (τ := .E8) (K := K)
    (isRoot_highRoot .E8)).2.1 t

theorem e8T_comm :
    ∀ a ∈ e8T K, ∀ b ∈ e8T K, a * b = b * a := by
  intro a ha b hb
  have h6 := (exceptional_Lang_root_rank_one_torus_transport (τ := .E8) (K := K)
    (isRoot_highRoot .E8)).2.2.2.2.2.1
  obtain ⟨x, hx, -⟩ := h6 _ ha
  obtain ⟨y, hy, -⟩ := h6 _ hb
  have hx' : ((a : adjointGroup .E8 K) : ModGL .E8 K) = rootDiagUnit .E8 x := hx
  have hy' : ((b : adjointGroup .E8 K) : ModGL .E8 K) = rootDiagUnit .E8 y := hy
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hx', hy', ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    mul_comm]

theorem e8T_le_normalizer_e8L :
    e8T K ≤ Subgroup.normalizer (e8L K : Set (adjointGroup .E8 K)) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  have hN := torusGroup_le_normalizer_rootSpan (K := K)
    (S := parabolicRoots .E8 e8LeviNodes) (fun α hα => hα.1) hh
  rw [Subgroup.mem_normalizer_iff] at hN
  have e := hN (g : ModGL .E8 K)
  rw [← subsystemGroup_eq_rootSpan] at e
  exact e

theorem e8L_le_centralizer_e8Q :
    e8L K ≤ Subgroup.centralizer (e8Q K : Set (adjointGroup .E8 K)) := by
  intro ℓ hℓ
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨t, rfl⟩
  have h7 := (exceptional_Lang_root_rank_one_torus_transport (τ := .E8) (K := K)
    (isRoot_highRoot .E8)).2.2.2.2.2.2.1 (Pi.mulSingle e8Top t)
  have hsub : subsystemGroup .E8 K e8LeviNodes ≤
      Subgroup.centralizer {rootDiagUnit .E8 (Pi.mulSingle e8Top t)} := by
    refine (Subgroup.closure_le _).2 ?_
    have hfix : ∀ γ : Fin Tag.E8.rank → ℤ, IsRoot .E8 γ → γ e8Top = 0 → ∀ c : K,
        pinnedX .E8 K γ c ∈ Subgroup.centralizer {rootDiagUnit .E8 (Pi.mulSingle e8Top t)} := by
      intro γ hγ h0 c
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e := h7 γ hγ c
      have hc : ((∏ i, (Pi.mulSingle e8Top t : Fin Tag.E8.rank → Kˣ) i ^ γ i : Kˣ) : K) = 1 := by
        have := rootChar_mulSingle_e8 t γ
        rw [rootChar] at this
        rw [this, h0, zpow_zero, Units.val_one]
      rw [hc, one_mul] at e
      have key : rootDiagUnit .E8 (Pi.mulSingle e8Top t) * pinnedX .E8 K γ c =
          pinnedX .E8 K γ c * rootDiagUnit .E8 (Pi.mulSingle e8Top t) := by
        calc _ = rootDiagUnit .E8 (Pi.mulSingle e8Top t) * pinnedX .E8 K γ c *
              (rootDiagUnit .E8 (Pi.mulSingle e8Top t))⁻¹ *
                rootDiagUnit .E8 (Pi.mulSingle e8Top t) := by group
          _ = _ := by rw [e]
      exact key.symm
    rintro _ ⟨i, hi, c, rfl | rfl⟩
    · have hi' : e8Top ≠ i := fun h => hi h.symm
      rw [← pinnedX_single]
      exact hfix _ (isRoot_single .E8 i) (by simp [hi']) c
    · have hi' : e8Top ≠ i := fun h => hi h.symm
      rw [← pinnedX_neg_single]
      exact hfix _ (IsRoot.neg (isRoot_single .E8 i)) (by simp [hi']) c
  have h := hsub hℓ
  rw [Subgroup.mem_centralizer_singleton_iff] at h
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, MonoidHom.comp_apply, coe_e8Rho_e8HSLHom]
  exact h.symm

theorem coeff_top_mem_Icc_of_isRoot {γ : Fin Tag.E8.rank → ℤ}
    (hγ : IsRoot .E8 γ) :
    -2 ≤ γ e8Top ∧ γ e8Top ≤ 2 := by
  have h : ∀ l ∈ Tag.artifactRoots .E8, -2 ≤ l.getD 7 0 ∧ l.getD 7 0 ≤ 2 := by
    decide +kernel
  have h1 := h _ (isRoot_iff_mem_artifactRoots.1 hγ)
  have h2 : (List.ofFn γ).getD 7 0 = γ e8Top := by
    rw [List.getD_eq_getElem _ _ (by rw [List.length_ofFn]; decide), List.getElem_ofFn]
    rfl
  rwa [h2] at h1

theorem three_le_card_units_e8 [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m) :
    (3 : ℤ) ≤ (Nat.card Kˣ : ℤ) := by
  have hm2 : 2 ≤ m := by
    by_contra h
    have h1 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  rw [Nat.card_units, hK]
  have : (4 : ℕ) ≤ 2 ^ m := by simpa using h4
  omega

theorem exists_mem_e8T_inv_mul_mem_e8L
    [Finite K]
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m) :
    ∀ c ∈ Subgroup.centralizer (e8Q K : Set (adjointGroup .E8 K)),
      ∃ h ∈ e8T K, h⁻¹ * c ∈ e8L K := by
  intro c hc
  obtain ⟨t, ht⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf t = Nat.card Kˣ := orderOf_eq_card_of_forall_mem_zpowers ht
  have hN := three_le_card_units_e8 hK hq
  set a : Fin Tag.E8.rank → Kˣ := Pi.mulSingle e8Top t with ha
  have hdvd : ∀ n : ℤ, t ^ n = 1 ↔ (Nat.card Kˣ : ℤ) ∣ n := fun n => by
    rw [← hord, orderOf_dvd_iff_zpow_eq_one]
  have hsmall : ∀ n : ℤ, (Nat.card Kˣ : ℤ) ∣ n → -2 ≤ n → n ≤ 2 → n = 0 := fun n h h1 h2 =>
    Int.eq_zero_of_abs_lt_dvd h (by rw [abs_lt]; omega)
  have hcT : (c : ModGL .E8 K) ∈ toralCentralizer .E8 K a := by
    refine Subgroup.mem_inf.2 ⟨c.2, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hc _ ⟨t, rfl⟩)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, MonoidHom.comp_apply, coe_e8Rho_e8HSLHom] at h1
    exact h1.symm
  obtain ⟨w, hw, h, hh, u, hu, v, hv, he⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors .E8 K a).1 _ hcT
  have hker : ∀ γ ∈ rootCharKernel a, γ ∈ parabolicRoots .E8 e8LeviNodes := by
    rintro γ ⟨hγ, h1⟩
    refine ⟨hγ, fun i hi => ?_⟩
    have hi7 : i = e8Top := by simpa [e8LeviNodes] using hi
    subst hi7
    rw [rootChar_mulSingle_e8, hdvd] at h1
    obtain ⟨hb1, hb2⟩ := coeff_top_mem_Icc_of_isRoot hγ
    exact hsmall _ h1 hb1 hb2
  have hcong : ∀ j : Fin Tag.E8.rank, (Nat.card Kˣ : ℤ) ∣
      (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) e8Top -
        (Pi.single j 1 : Fin Tag.E8.rank → ℤ) e8Top := by
    intro j
    have h1 := hw (Pi.single j 1)
    rw [rootChar_mulSingle_e8, rootChar_mulSingle_e8] at h1
    rw [← hdvd, zpow_sub, h1, mul_inv_cancel]
  have hne : ∀ j, j ≠ e8Top → (w • (Pi.single j 1 : Fin Tag.E8.rank → ℤ)) e8Top = 0 := by
    intro j hj
    have h1 := hcong j
    rw [Pi.single_eq_of_ne (Ne.symm hj), sub_zero] at h1
    obtain ⟨hb1, hb2⟩ := coeff_top_mem_Icc_of_isRoot (IsRoot.smul (isRoot_single .E8 j) w)
    exact hsmall _ h1 hb1 hb2
  have h7 : (w • (Pi.single e8Top 1 : Fin Tag.E8.rank → ℤ)) e8Top = 1 := by
    obtain ⟨hθ1, hθ2⟩ := coeff_top_mem_Icc_of_isRoot (IsRoot.smul (isRoot_highRoot .E8) w)
    have hsum := congrFun (smul_eq_sum_smul_single w (highRoot .E8)) e8Top
    rw [Finset.sum_apply, Finset.sum_eq_single e8Top
      (fun j _ hj => by rw [Pi.smul_apply, hne j hj, smul_zero])
      (fun h => absurd (Finset.mem_univ _) h), Pi.smul_apply, smul_eq_mul] at hsum
    have h2 : highRoot .E8 e8Top = 2 := rfl
    rw [h2] at hsum
    have h1 := hcong e8Top
    rw [Pi.single_eq_same] at h1
    have := hsmall _ h1 (by omega) (by omega)
    omega
  have hwJ : w ∈ parabolicWeylGroup .E8 e8LeviNodes := by
    refine (mem_parabolicWeylGroup_of_coord _ w rfl fun x i hi => ?_).1
    have hi7 : i = e8Top := by simpa [e8LeviNodes] using hi
    subst hi7
    rw [congrFun (smul_eq_sum_smul_single w x) e8Top, Finset.sum_apply,
      Finset.sum_eq_single e8Top (fun j _ hj => by rw [Pi.smul_apply, hne j hj, smul_zero])
        (fun h => absurd (Finset.mem_univ _) h), Pi.smul_apply, h7, smul_eq_mul, mul_one]
  have hTC := torusGroup_le_adjointGroup_e8 hh
  refine ⟨⟨h, hTC⟩, hh, ?_⟩
  have hpar : ∀ S : Set (Fin Tag.E8.rank → ℤ), S ⊆ rootCharKernel a →
      rootSpan .E8 K S ≤ subsystemGroup .E8 K e8LeviNodes := fun S hS => by
    rw [subsystemGroup_eq_rootSpan]
    exact rootSpan_mono fun γ hγ => hker γ (hS hγ)
  have hu' := hpar _ Set.inter_subset_left hu
  have hv' := hpar _ Set.inter_subset_left hv
  have hn := canonicalRep_mem_subsystemGroup (K := K) hwJ
  show ((⟨h, hTC⟩ : adjointGroup .E8 K)⁻¹ * c : adjointGroup .E8 K).1 ∈
    subsystemGroup .E8 K e8LeviNodes
  rw [Subgroup.coe_mul, Subgroup.coe_inv, he,
    show h⁻¹ * (h * u * canonicalRep (coxeterSystem .E8) K w * v) =
      u * canonicalRep (coxeterSystem .E8) K w * v by group]
  exact mul_mem (mul_mem hu' hn) hv'

theorem e8Q_ne_bot
    [Finite K]
    {m : ℕ} (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m) : e8Q K ≠ ⊥ := by
  have : Nontrivial Kˣ := Finite.one_lt_card_iff_nontrivial.1 (by
    have := three_le_card_units_e8 hK hq
    omega)
  obtain ⟨t, ht1⟩ := exists_ne (1 : Kˣ)
  intro hbot
  have hmem : e8Rho K (e8HSLHom K t) ∈ e8Q K := ⟨t, rfl⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  have h0 : rootDiagUnit .E8 (Pi.mulSingle e8Top t) = 1 := by
    rw [← coe_e8Rho_e8HSLHom, hmem]
    rfl
  set b : Label .E8 := Sum.inr ⟨Pi.single e8Top 1, isRoot_single .E8 e8Top⟩
  have h1 := congrArg
    (fun g : ModGL .E8 K => (g : Module.End K (RootModule .E8 K)) (Finsupp.single b 1)) h0
  change rootDiag (Pi.mulSingle e8Top t) (Finsupp.single b 1) = Finsupp.single b 1 at h1
  rw [rootDiag_single] at h1
  have h2 : ((rootChar (Pi.mulSingle e8Top t) (labelWt .E8 b) : Kˣ) : K) = t := by
    simp [b, labelWt, rootChar_mulSingle_e8]
  rw [h2, Finsupp.smul_single, smul_eq_mul, mul_one] at h1
  exact ht1 (Units.ext (Finsupp.single_injective _ h1))

theorem odd_card_e8Q
    [Finite K]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) : Odd (Nat.card (e8Q K)) :=
  (odd_card_units_e8 hm hK).of_dvd_nat (Subgroup.card_range_dvd _)

theorem zx_le_e8L
    [Finite K]
    {m : ℕ} (hm : 1 ≤ m) (hK : Nat.card K = 2 ^ m) (hq : 2 < 2 ^ m)
    {x : adjointGroup .E8 K} (hx : x ∈ e8L K) : Exc.zx x ≤ e8L K := by
  intro w hw
  obtain ⟨-, hwc, hw2⟩ := hw
  have hQx : ∀ y ∈ e8Q K, y ∈ Exc.cent x := fun y hy => by
    have h1 := Subgroup.mem_centralizer_iff.1 (e8L_le_centralizer_e8Q hx) y hy
    rw [Exc.cent, Subgroup.mem_centralizer_singleton_iff]
    exact h1
  have hwQ : w ∈ Subgroup.centralizer (e8Q K : Set (adjointGroup .E8 K)) :=
    Subgroup.mem_centralizer_iff.2 fun y hy => by
      have h1 := hwc y (hQx y hy)
      exact h1.symm
  obtain ⟨h, hh, hhw⟩ := exists_mem_e8T_inv_mul_mem_e8L hK hq w hwQ
  have hN : h⁻¹ ∈ Subgroup.normalizer (e8L K : Set (adjointGroup .E8 K)) :=
    inv_mem (e8T_le_normalizer_e8L hh)
  have hconj : h⁻¹ * (h⁻¹ * w) * h ∈ e8L K := by
    have := (Subgroup.mem_normalizer_iff.1 hN (h⁻¹ * w)).1 hhw
    rwa [inv_inv] at this
  have hh2 : h ^ 2 ∈ e8L K := by
    have e : (h ^ 2)⁻¹ = (h⁻¹ * (h⁻¹ * w) * h) * (h⁻¹ * w) := by
      calc (h ^ 2)⁻¹ = h⁻¹ * h⁻¹ * (w * w) := by rw [hw2]; group
        _ = _ := by group
    rw [← inv_mem_iff, e]
    exact mul_mem hconj hhw
  have hpow : h ^ Nat.card Kˣ = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact pow_card_units_eq_one_of_mem_torusGroup hh
  obtain ⟨k, hk⟩ := odd_card_units_e8 hm hK
  have hhL : h ∈ e8L K := by
    have e : h = (h ^ 2) ^ (k + 1) := by
      rw [← pow_mul, show 2 * (k + 1) = Nat.card Kˣ + 1 by omega, pow_succ, hpow, one_mul]
    rw [e]
    exact pow_mem hh2 _
  have e : w = h * (h⁻¹ * w) := by group
  rw [e]
  exact mul_mem hhL hhw

theorem rootForm_highRoot_single_e8 : ∀ i : Fin Tag.E8.rank, i ≠ e8Top →
    highRoot .E8 ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) = 0 ∧
    highRoot .E8 ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ (-Pi.single i 1 : Fin Tag.E8.rank → ℤ)) = 0 ∧
    (-highRoot .E8) ⬝ᵥ (Tag.E8.symmetrizedCartan *ᵥ (Pi.single i 1 : Fin Tag.E8.rank → ℤ)) = 0 ∧
    (-highRoot .E8) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ (-Pi.single i 1 : Fin Tag.E8.rank → ℤ)) = 0 := by
  decide +kernel

theorem e8D_le_centralizer_e8L :
    e8D K ≤ Subgroup.centralizer (e8L K : Set (adjointGroup .E8 K)) := by
  have hτ : Tag.E8 = .D4 ∨ Tag.E8 = .E6 ∨ Tag.E8 = .E7 ∨ Tag.E8 = .E8 :=
    Or.inr (Or.inr (Or.inr rfl))
  have hgen : ∀ σ : Fin Tag.E8.rank → ℤ, (σ = highRoot .E8 ∨ σ = -highRoot .E8) →
      ∀ γ : Fin Tag.E8.rank → ℤ, (∃ i ∈ e8LeviNodes, γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
        ∀ c d : K, Commute (pinnedX .E8 K σ c) (pinnedX .E8 K γ d) := by
    rintro σ hσ γ ⟨i, hi, hγ⟩ c d
    have hi' : i ≠ e8Top := hi
    have h0 := rootForm_highRoot_single_e8 i hi'
    have hσr : IsRoot .E8 σ := by
      rcases hσ with rfl | rfl
      exacts [isRoot_highRoot .E8, IsRoot.neg (isRoot_highRoot .E8)]
    have hγr : IsRoot .E8 γ := by
      rcases hγ with rfl | rfl
      exacts [isRoot_single .E8 i, IsRoot.neg (isRoot_single .E8 i)]
    refine pinnedX_commute_of_rootForm_nonneg hτ hσr hγr ?_ ?_ c d
    · intro he
      have h1 : σ e8Top = γ e8Top := congrFun he e8Top
      have h2 : γ e8Top = 0 := by
        rcases hγ with rfl | rfl
        · exact Pi.single_eq_of_ne hi'.symm _
        · rw [Pi.neg_apply, Pi.single_eq_of_ne hi'.symm, neg_zero]
      have h3 : σ e8Top ≠ 0 := by
        rcases hσ with rfl | rfl <;> decide
      exact h3 (h1.trans h2)
    · obtain ⟨h1, h2, h3, h4⟩ := h0
      rcases hσ with rfl | rfl <;> rcases hγ with rfl | rfl
      exacts [h1.ge, h2.ge, h3.ge, h4.ge]
  intro g hg
  rw [Subgroup.mem_centralizer_iff]
  intro ℓ hℓ
  obtain ⟨A, rfl⟩ := hg
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, coe_e8Rho]
  have hA : rootSL2 .E8 K (highRoot .E8) A ∈
      rootSubgroup .E8 K (highRoot .E8) ⊔ rootSubgroup .E8 K (-highRoot .E8) := by
    rw [← (exceptional_Lang_root_rank_one_torus_transport (τ := .E8) (K := K)
      (isRoot_highRoot .E8)).1]
    exact ⟨A, rfl⟩
  have hℓ' : (ℓ : ModGL .E8 K) ∈ subsystemGroup .E8 K e8LeviNodes := hℓ
  have hM : rootSubgroup .E8 K (highRoot .E8) ⊔ rootSubgroup .E8 K (-highRoot .E8) ≤
      Subgroup.centralizer (subsystemGroup .E8 K e8LeviNodes : Set (ModGL .E8 K)) := by
    rw [Subgroup.le_centralizer_iff]
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨i, hi, d, hx⟩
    have hgenM : ∀ γ : Fin Tag.E8.rank → ℤ, (γ = Pi.single i 1 ∨ γ = -Pi.single i 1) →
        pinnedX .E8 K γ d ∈ Subgroup.centralizer
          ((rootSubgroup .E8 K (highRoot .E8) ⊔ rootSubgroup .E8 K (-highRoot .E8) :
            Subgroup (ModGL .E8 K)) : Set (ModGL .E8 K)) := by
      intro γ hγ
      have hle : rootSubgroup .E8 K (highRoot .E8) ⊔ rootSubgroup .E8 K (-highRoot .E8) ≤
          Subgroup.centralizer {pinnedX .E8 K γ d} := by
        refine sup_le ((Subgroup.closure_le _).2 ?_) ((Subgroup.closure_le _).2 ?_) <;>
          rintro _ ⟨c, rfl⟩ <;> rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
        · exact (hgen _ (Or.inl rfl) γ ⟨i, hi, hγ⟩ c d).eq
        · exact (hgen _ (Or.inr rfl) γ ⟨i, hi, hγ⟩ c d).eq
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      exact Subgroup.mem_centralizer_singleton_iff.1 (hle hm)
    rcases hx with rfl | rfl
    · rw [SetLike.mem_coe, ← pinnedX_single]
      exact hgenM _ (Or.inl rfl)
    · rw [SetLike.mem_coe, ← pinnedX_neg_single]
      exact hgenM _ (Or.inr rfl)
  exact (Subgroup.mem_centralizer_iff.1 (hM hA) _ hℓ')

end CFSG.ComponentClassification.RankTwoExceptional.E8
