module

public import CFSG.Quasithin.H13.A5S1327w
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327o

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_s2a_F4 (h331 : Stmt3_3_1_F4) (h5172 : Stmt5_1_7_two_F4)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    (hO2 : pCoreOf 2 (S.H0 H) = ⊥) (hU : IsElemAbelian 2 (S.UH H)) :
    ∃ K₁ K₂, S2A S H hU K₁ K₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (L : Set G) with hM
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, -, hUred⟩ : S.UH H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (S.UH H) ∧ IsTwoReducedIn H (S.UH H) :=
    conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl

  have hZH' : ⁅quasithinOmegaOneCenter T, H⁆ ≠ ⊥ := by
    intro h
    apply hHZ
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact h)
  obtain ⟨-, -, hiii⟩ := h5172 G T M L V H 2 h501 S.isCh5Module hH hZH'
  have hZH : centerOf H = ⊥ := (hiii.resolve_left fun h => h hO2).2.2
  have hN := S.inf_centralizer_eq_bot_of_center hTH hZH

  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar_F4 h331 hH
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  have hJ := S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ
  obtain ⟨K₁, K₂, B⟩ := exists_twoBlocks hU hMP hsolv hSQT hUred hJ hS3

  have hfix : fixV (autI hU (twoResidual H)) = ⊥ := by
    rw [eq_bot_iff]
    intro u hu
    have hLN : twoResidual H ≤ Subgroup.normalizer (S.UH H : Set G) :=
      (twoResidual_le H).trans hUred.2.1
    have huT : u.val ∈ T ⊓ Subgroup.centralizer (oTwoUpper H : Set G) := by
      refine Subgroup.mem_inf.mpr
        ⟨(hUO.trans (inf_le_left.trans (pCoreOf_two_le_of_isSylowTwoOf hsyl))) u.val_mem, ?_⟩
      rw [← twoResidual_eq_oTwoUpper']
      exact (mem_fixV_autI hU hLN u).1 hu
    rw [hN, Subgroup.mem_bot] at huT
    exact Subgroup.mem_bot.mpr (IntMod.val_injective huT)
  have htop : commV K₁ ⊔ commV K₂ = ⊤ := by
    have := B.fix_sup
    rwa [hfix, bot_sup_eq] at this

  obtain ⟨-, hsylJ, -, hE, -⟩ := E2_3_two_of_isSolvable hU hMP hsolv hSQT hUred hJ
  rw [twoResidual_eq_oTwoUpper'] at hE
  have hEle : omegaOneCenterOf (thompsonJ T) ≤ T :=
    (A4.omegaOneCenterOf_le _).trans (thompsonJ_le_self T)
  have hEC : omegaOneCenterOf (thompsonJ T) ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ :=
    le_bot_iff.mp (hN ▸ inf_le_inf_right _ hEle)
  rw [hEC, sup_bot_eq] at hE

  rw [B.eqJ] at hsylJ
  obtain ⟨s₁, s₂, a₁, a₂, hd⟩ :=
    S1417.exists_sylowData hsylJ B.nat₁ B.nat₂ B.comm B.inf B.commV_inf htop
  have hJN : thompsonJ T ≤ Subgroup.normalizer (S.UH H : Set G) :=
    (thompsonJ_le_self T).trans (hTH.trans hUred.2.1)
  have hEfix : ∀ (u : G) (hu : u ∈ S.UH H), u ∈ Subgroup.centralizer (thompsonJ T : Set G) →
      (IntMod.mk hU ⟨u, hu⟩ = 1 ∨ IntMod.mk hU ⟨u, hu⟩ = a₁ ∨ IntMod.mk hU ⟨u, hu⟩ = a₂ ∨
        IntMod.mk hU ⟨u, hu⟩ = a₁ * a₂) := by
    intro u hu hC
    refine (hd.fixS _).1 ?_
    exact (mem_fixV_autI hU hJN (IntMod.mk hU ⟨u, hu⟩)).2 hC
  have hEU : omegaOneCenterOf (thompsonJ T) ≤ S.UH H := hE.le.trans inf_le_left

  have hEcard : Nat.card ↥(omegaOneCenterOf (thompsonJ T)) ≤ 4 := by
    refine card_le_four_of_injective
      (fun x : ↥(omegaOneCenterOf (thompsonJ T)) => IntMod.mk hU ⟨(x : G), hEU x.2⟩) ?_
      1 a₁ a₂ (a₁ * a₂) fun x => ?_
    · intro x y hxy
      apply Subtype.ext
      have h := congrArg IntMod.val hxy
      exact h
    · exact hEfix _ (hEU x.2) (hE.le x.2).2
  have hEV2 : omegaOneCenterOf (thompsonJ T) = S.V2 :=
    (Subgroup.eq_of_le_of_card_ge S.V2_le_omegaOneCenter_J
      (by rw [S.card_V2]; exact hEcard)).symm

  have hZE' : quasithinOmegaOneCenter T ≤ omegaOneCenterOf (thompsonJ T) := by
    obtain ⟨A₀, hA₀⟩ := exists_isMaxElemAbelian T
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨⟨hxT, hxC⟩, hx2⟩
    have hxA : x ∈ A₀ := by
      have hxCA : x ∈ T ⊓ Subgroup.centralizer (A₀ : Set G) :=
        ⟨hxT, Subgroup.centralizer_le hA₀.1 hxC⟩
      have : x ∈ omegaOneOf (T ⊓ Subgroup.centralizer (A₀ : Set G)) :=
        Subgroup.subset_closure ⟨hxCA, hx2⟩
      rwa [← eq_omegaOneOf_centralizer hA₀] at this
    have hxJ : x ∈ thompsonJ T := (le_iSup₂_of_le A₀ hA₀ le_rfl : A₀ ≤ thompsonJ T) hxA
    refine Subgroup.subset_closure ⟨⟨hxJ, ?_⟩, hx2⟩
    refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
    exact Subgroup.mem_centralizer_iff.1 hxC y (thompsonJ_le_self T hy)
  have hZE : quasithinOmegaOneCenter T ≤ S.V2 := hEV2 ▸ hZE'
  have hZV1 : quasithinOmegaOneCenter T = S.V1 := by
    apply le_antisymm
    · intro x hx
      refine S.mem_V1_of_fixed (S.V2_le_V3.trans S.V3_le_V (hZE hx)) fun t ht => ?_
      have := Subgroup.mem_centralizer_iff.mp (mem_quasithinOmegaOneCenter_iff.mp hx).2.1 t ht
      rw [this]; group
    · intro x hx
      rcases S.mem_V1.1 hx with rfl | rfl
      · exact Subgroup.one_mem _
      · exact S.z_mem_omegaOneCenter

  have hV2E : S.V2 ≤ S.UH H ⊓ Subgroup.centralizer (thompsonJ T : Set G) := by
    rw [← hEV2]; exact hE.le
  have he1U : S.e1 ∈ S.UH H := (hV2E S.e1_mem_V2).1
  have he2U : S.e2 ∈ S.UH H := (hV2E S.e2_mem_V2).1
  have hzU : S.z ∈ S.UH H := (hV2E S.z_mem_V2).1
  have hmk_ne : ∀ (u v : G) (hu : u ∈ S.UH H) (hv : v ∈ S.UH H), u ≠ v →
      IntMod.mk hU ⟨u, hu⟩ ≠ IntMod.mk hU ⟨v, hv⟩ := fun u v hu hv huv h =>
    huv (congrArg Subtype.val h)
  have hmk1 : ∀ (u : G) (hu : u ∈ S.UH H), u ≠ 1 → IntMod.mk hU ⟨u, hu⟩ ≠ 1 := fun u hu hu1 h =>
    hu1 (congrArg Subtype.val h)

  obtain ⟨t, htT, ht⟩ := B.swap
  obtain ⟨t₀, ht₀T, rfl⟩ := (mem_autI hU).1 htT
  have htz : convI hU t₀ (IntMod.mk hU ⟨S.z, hzU⟩) = IntMod.mk hU ⟨S.z, hzU⟩ := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    exact S.conj_z_of_mem_T ht₀T
  have htz' : (convI hU t₀)⁻¹ (IntMod.mk hU ⟨S.z, hzU⟩) = IntMod.mk hU ⟨S.z, hzU⟩ := by
    calc (convI hU t₀)⁻¹ (IntMod.mk hU ⟨S.z, hzU⟩) =
          (convI hU t₀)⁻¹ (convI hU t₀ (IntMod.mk hU ⟨S.z, hzU⟩)) := by rw [htz]
      _ = IntMod.mk hU ⟨S.z, hzU⟩ := by simp
  have hU12 : ∀ w : IntMod (S.UH H) hU, w ∈ commV K₁ → w ∈ commV K₂ → w = 1 := fun w h1 h2 => by
    have : w ∈ commV K₁ ⊓ commV K₂ := ⟨h1, h2⟩
    rwa [B.commV_inf, Subgroup.mem_bot] at this
  have hmap₁ : ∀ w ∈ commV K₁, convI hU t₀ w ∈ commV K₂ := fun w hw => by
    rw [← ht, ← commV_map_conjAut]
    exact ⟨w, hw, rfl⟩
  have ht' : B1.conjAut (convI hU t₀)⁻¹ K₂ = K₁ := by
    rw [← ht, ← S1417.conjAut_mul, inv_mul_cancel]
    exact S1417.conjAut_eq_of_mem (Subgroup.one_mem _)
  have hmap₂ : ∀ w ∈ commV K₂, (convI hU t₀)⁻¹ w ∈ commV K₁ := fun w hw => by
    rw [← ht', ← commV_map_conjAut]
    exact ⟨w, hw, rfl⟩
  have hz_val : IntMod.mk hU ⟨S.z, hzU⟩ = a₁ * a₂ := by
    rcases hEfix _ hzU (hV2E S.z_mem_V2).2 with h | h | h | h
    · exact absurd h (hmk1 _ hzU S.z_ne_one)
    · exfalso
      have h1 := hmap₁ (IntMod.mk hU ⟨S.z, hzU⟩) (by rw [h]; exact hd.a₁_mem)
      rw [htz, h] at h1
      exact hd.a₁_ne (hU12 _ hd.a₁_mem h1)
    · exfalso
      have h1 := hmap₂ (IntMod.mk hU ⟨S.z, hzU⟩) (by rw [h]; exact hd.a₂_mem)
      rw [htz', h] at h1
      exact hd.a₂_ne (hU12 _ h1 hd.a₂_mem)
    · exact h
  have hval : ∀ (u : G) (hu : u ∈ S.UH H), u ∈ S.V2 → u ≠ 1 → u ≠ S.z →
      IntMod.mk hU ⟨u, hu⟩ = a₁ ∨ IntMod.mk hU ⟨u, hu⟩ = a₂ := by
    intro u hu hu2 hu1 huz
    rcases hEfix _ hu (hV2E hu2).2 with h | h | h | h
    · exact absurd h (hmk1 _ hu hu1)
    · exact Or.inl h
    · exact Or.inr h
    · exact absurd (h.trans hz_val.symm) (hmk_ne _ _ hu hzU huz)

  have hCTL : T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
    set N := T ⊓ Subgroup.centralizer (L : Set G) with hNdef
    have hNT : N ≤ T := inf_le_left
    have hn : (N.subgroupOf T).Normal := by
      refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNT).mpr fun t ht => ?_
      refine B6.mem_normalizer_of_forall_mem (fun x hx => ?_) fun x hx => ?_
      · refine ⟨T.mul_mem (T.mul_mem ht hx.1) (T.inv_mem ht), ?_⟩
        exact conj_mem_centralizer_of_mem_normalizer (S.T_le_NL ht) hx.2
      · refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hx.1) ht, ?_⟩
        have := conj_mem_centralizer_of_mem_normalizer (Subgroup.inv_mem _ (S.T_le_NL ht)) hx.2
        rwa [inv_inv] at this
    by_contra hne
    have hne' : N.subgroupOf T ≠ ⊥ := by
      intro h
      apply hne
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hNT hx⟩ : ↥T) ∈ N.subgroupOf T := hx
      rw [h, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have : Group.IsNilpotent ↥T := S.isPGroup_T.isNilpotent
    have hW := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := N.subgroupOf T) hne'

    have hWp : IsPGroup 2 ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) :=
      S.isPGroup_T.to_subgroup _
    obtain ⟨w, hw2⟩ : ∃ w : ↥(N.subgroupOf T ⊓ Subgroup.center ↥T), orderOf w = 2 := by
      have h1 : 1 < Nat.card ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) :=
        (Subgroup.one_lt_card_iff_ne_bot _).mpr hW
      obtain ⟨k, hk⟩ := hWp.exists_card_eq
      have hk0 : k ≠ 0 := by
        rintro rfl
        rw [hk, pow_zero] at h1
        exact lt_irrefl _ h1
      exact exists_prime_orderOf_dvd_card' 2 (by rw [hk]; exact dvd_pow_self 2 hk0)
    have hw1 : ((w : ↥T) : G) ≠ 1 := by
      intro h
      have : w = 1 := Subtype.ext (Subtype.ext h)
      rw [this, orderOf_one] at hw2
      exact absurd hw2 (by norm_num)
    have hwsq : ((w : ↥T) : G) ^ 2 = 1 := by
      have h1 : w ^ 2 = 1 := hw2 ▸ pow_orderOf_eq_one w
      have h2 := congrArg (fun x : ↥(N.subgroupOf T ⊓ Subgroup.center ↥T) => ((x : ↥T) : G)) h1
      simpa using h2
    have hwN : ((w : ↥T) : G) ∈ N := Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp w.2).1
    have hwZ : ((w : ↥T) : G) ∈ quasithinOmegaOneCenter T := by
      refine mem_quasithinOmegaOneCenter_iff.mpr ⟨(w : ↥T).2, ?_, hwsq⟩
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp w.2).2 ⟨t, ht⟩)
    rw [hZV1, S.mem_V1] at hwZ
    rcases hwZ with h | h
    · exact hw1 h
    · have hzC : S.z ∈ V ⊓ Subgroup.centralizer (L : Set G) := ⟨S.z_mem_V, h ▸ hwN.2⟩
      rw [S.V_inf_centralizer_L, Subgroup.mem_bot] at hzC
      exact S.z_ne_one hzC

  have he12 : IntMod.mk hU ⟨S.e1, he1U⟩ ≠ IntMod.mk hU ⟨S.e2, he2U⟩ :=
    hmk_ne _ _ he1U he2U S.e1_ne_e2
  rcases hval _ he1U S.e1_mem_V2 S.e1_ne_one S.e1_ne_z with h1 | h1 <;>
    rcases hval _ he2U S.e2_mem_V2 S.e2_ne_one S.e2_ne_z with h2 | h2
  · exact absurd (h1.trans h2.symm) he12
  · exact ⟨K₁, K₂, ⟨B, hZH, hN, hfix, htop, hEV2, hE, hZV1, he1U, he2U,
      by rw [h1]; exact hd.a₁_mem, by rw [h2]; exact hd.a₂_mem, hCTL⟩⟩
  · exact ⟨K₂, K₁, ⟨B.symm, hZH, hN, hfix, by rw [sup_comm]; exact htop, hEV2, hE, hZV1, he1U,
      he2U, by rw [h1]; exact hd.a₂_mem, by rw [h2]; exact hd.a₁_mem, hCTL⟩⟩
  · exact absurd (h1.trans h2.symm) he12

end Setting

end CFSG.Quasithin.H13.A5
