module

public import CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.Leaf.ClosingE8TenAux27

public noncomputable section

namespace CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
open CFSG.LieType.Steinberg.Adjoint CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis
open CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.DetectE8
open scoped commutatorElement
open E8TenTwo

set_option linter.unusedSectionVars false


section Conj

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem conj_Q (hK : Nat.card K = 2) {y : ModGL Tag.E8 K} (hy : y ∈ TwClass.e8Ten.X₂ D)
    {T : Fn D.L →ₗ[D.L] Fn D.L} (hT : ActsBy (ΨE D y) T) {w : ModGL Tag.E8 K}
    (hwQ : w ∈ Qθ Tag.E8 K) :
    y * w * y⁻¹ ∈ Qθ Tag.E8 K ∧ κF D (y * w * y⁻¹) = T (κF D w) := by
  have hΨwQ : ΨE D w ∈ Qθ Tag.E8 D.L := ΨE_Qθ D hwQ
  obtain ⟨hcQ, hcc⟩ := hT _ hΨwQ
  have hΨ : ΨE D (y * w * y⁻¹) = ΨE D y * ΨE D w * (ΨE D y)⁻¹ := by
    rw [ΨE_mul, ΨE_mul, ΨE_inv]
  have hadj : y * w * y⁻¹ ∈ adjointGroup Tag.E8 K :=
    mul_mem (mul_mem (X₂_le_adjoint D hy) (Qθ_le_adjointGroup Tag.E8 K hwQ))
      (inv_mem (X₂_le_adjoint D hy))
  refine ⟨?_, ?_⟩
  · refine mem_Qθ_of_bc D hK hadj ?_
    rw [bc_eq_conj D, hΨ]
    exact Lθ_conj_mem_Qθ (gE_mem_Lθ D) hcQ
  · rw [κF_eq, κF_eq, hΨ, hcc]

theorem conj_B (hb : TwBasic (TwClass.e8Ten.X₁ D) (TwClass.e8Ten.X₂ D))
    {H : Subgroup (ModGL Tag.E8 K)} (hXH : TwClass.e8Ten.X₁ D ⊔ TwClass.e8Ten.X₂ D ≤ H)
    {y : ModGL Tag.E8 K} (hy : y ∈ TwClass.e8Ten.X₂ D) {w : ModGL Tag.E8 K}
    (hwB : conjSub w (Heis.Uneg Tag.E8 K) ≤ H) :
    conjSub (y * w * y⁻¹) (Heis.Uneg Tag.E8 K) ≤ H := by
  have hyH : y ∈ H := hXH (Subgroup.mem_sup_right hy)
  intro x hx
  obtain ⟨u, hu, hxu⟩ : ∃ u : ModGL Tag.E8 K, u ∈ Heis.Uneg Tag.E8 K ∧
      x = (y * w * y⁻¹) * u * (y * w * y⁻¹)⁻¹ :=
    ⟨(y * w * y⁻¹)⁻¹ * x * (y * w * y⁻¹), mem_conjSub_iff.1 hx, by group⟩
  have hc : u * y = y * u := hb.comm u (hb.Uneg_le hu) y hy
  have hyu : y⁻¹ * u * y = u := by
    calc y⁻¹ * u * y = y⁻¹ * (u * y) := by group
      _ = y⁻¹ * (y * u) := by rw [hc]
      _ = u := by group
  have hwu : w * u * w⁻¹ ∈ H := hwB (mem_conjSub_iff.2 (by
    have e : w⁻¹ * (w * u * w⁻¹) * w = u := by group
    rw [e]
    exact hu))
  have hx_eq : x = y * (w * u * w⁻¹) * y⁻¹ := by
    rw [hxu]
    calc (y * w * y⁻¹) * u * (y * w * y⁻¹)⁻¹ = y * w * (y⁻¹ * u * y) * w⁻¹ * y⁻¹ := by group
      _ = y * (w * u * w⁻¹) * y⁻¹ := by rw [hyu]; group
  rw [hx_eq]
  exact mul_mem (mul_mem hyH hwu) (inv_mem hyH)

end Conj

section Decode

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem decode (hK : Nat.card K = 2) {ω : D.L} (hω : ω ^ 2 + ω + 1 = 0) {v : ModGL Tag.E8 K}
    (hvQ : v ∈ Qθ Tag.E8 K)
    (hvM : ∀ β, κF D v β ≠ 0 → β ∈ mRoots ∧ (cls β = 1 ∨ cls β = 4)) :
    ∃ b, b < 2 ^ 20 ∧ κF D v = decv ω b := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set S := toSetup D ⊥ with hS
  have hq : v ∈ Qrat S.h := ΨE_Qθ D hvQ
  have hσ : S.sig (κF D v) = κF D v := S.sig_Cc hq
  have hrel : ∀ k, k < 10 → κF D v (nuW (2 * k + 1)) = κF D v (nuW (2 * k)) ^ 2 ∧
      κF D v (nuW (2 * k)) = κF D v (nuW (2 * k + 1)) ^ 2 := by
    intro k hk
    obtain ⟨hp1, hp2⟩ := nuW_pair k (List.mem_range.2 hk)
    have hroot1 : IsRoot Tag.E8 (nuW (2 * k)) := mem_rootFinset.1 (nuW_root (by omega))
    have hroot2 : IsRoot Tag.E8 (nuW (2 * k + 1)) := mem_rootFinset.1 (nuW_root (by omega))
    have hw1 : S.w • nuW (2 * k) = nuW (2 * k + 1) := by rw [toSetup_hw]; exact hp1
    have hw2 : S.w • nuW (2 * k + 1) = nuW (2 * k) := by rw [toSetup_hw]; exact hp2
    have hi1 : S.w⁻¹ • nuW (2 * k + 1) = nuW (2 * k) := by
      rw [inv_smul_eq_iff]
      exact hw1.symm
    have hi2 : S.w⁻¹ • nuW (2 * k) = nuW (2 * k + 1) := by
      rw [inv_smul_eq_iff]
      exact hw2.symm
    have e1 := congrFun hσ (nuW (2 * k + 1))
    have e2 := congrFun hσ (nuW (2 * k))
    simp only [Setup.sig, Mg_apply, Fv, hi1, hi2] at e1 e2
    have hFr : ∀ c : D.L, S.Fr c = c ^ 2 := fun c => Fr_sq D hK c
    rw [sg_eq_one D hK hroot1, one_mul, hFr] at e1
    rw [sg_eq_one D hK hroot2, one_mul, hFr] at e2
    exact ⟨e1.symm, e2.symm⟩
  have hcode : ∀ k, ∃ a : ℕ, a < 4 ∧ (k < 10 → κF D v (nuW (2 * k)) = emb ω a) := by
    intro k
    by_cases hk : k < 10
    · obtain ⟨h1, h2⟩ := hrel k hk
      have h4 : κF D v (nuW (2 * k)) ^ 4 = κF D v (nuW (2 * k)) := by
        calc κF D v (nuW (2 * k)) ^ 4 = (κF D v (nuW (2 * k)) ^ 2) ^ 2 := by ring
          _ = κF D v (nuW (2 * k + 1)) ^ 2 := by rw [← h1]
          _ = κF D v (nuW (2 * k)) := h2.symm
      obtain ⟨a, ha, hc⟩ := F4_cases hω h4
      exact ⟨a, ha, fun _ => hc⟩
    · exact ⟨0, by norm_num, fun h => absurd h hk⟩
  choose a ha hxa using hcode
  obtain ⟨b, hb, hdig⟩ := exists_pack a ha
  refine ⟨b, hb, ?_⟩
  funext μ
  by_cases hμ : ∃ i < 20, nuW i = μ
  · obtain ⟨i, hi, rfl⟩ := hμ
    rw [decv_apply_nuW ω hi, expandV_getD hi]
    have hk : i / 2 < 10 := by omega
    have hdig' := hdig (i / 2) hk
    by_cases he : i % 2 = 0
    · rw [if_pos he, hdig' ]
      have : i = 2 * (i / 2) := by omega
      rw [← hxa (i / 2) hk, ← this]
    · rw [if_neg he, hdig', emb_f4sq hω (ha _)]
      have : i = 2 * (i / 2) + 1 := by omega
      rw [← hxa (i / 2) hk, ← (hrel (i / 2) hk).1, ← this]
  · push Not at hμ
    rw [decv, decvX_apply_out ω _ hμ]
    by_contra hne
    obtain ⟨hm, hcls⟩ := hvM μ hne
    obtain ⟨i, hi, hie⟩ := nuW_complete μ hm hcls
    exact hμ i (List.mem_range.1 hi) hie

end Decode

section Std

variable {K : Type} [Field K] [Finite K] (D : LangLevi TwClass.e8Ten.tag K TwClass.e8Ten.w)

theorem AdjPair.of_P {β₀ β₁ : Fin Tag.E8.rank → ℤ} (h1 : AdjP1 β₀ β₁) (h2 : AdjP2 β₀ β₁)
    (h3 : AdjP3 β₀ β₁) : AdjPair β₀ β₁ := by
  obtain ⟨h₀, h₁, r₀, r₁, m₀, m₀', m₁, m₁'⟩ := h1
  obtain ⟨p₀, p₀', p₁, p₁'⟩ := h2
  obtain ⟨c₀, c₀', c₀s, c₁, c₁', c₁s⟩ := h3
  exact ⟨h₀, h₁, r₀, r₁, m₀, m₀', m₁, m₁', p₀, p₀', p₁, p₁', c₀, c₀', c₀s, c₁, c₁', c₁s⟩

theorem stdPair_adj {k : ℕ} (hk : k ∈ stdRep) : AdjPair (nuW (2 * k)) (nuW (2 * k + 1)) :=
  AdjPair.of_P (adjP1_std k hk) (adjP2_std k hk) (adjP3_std k hk)

theorem exists_u0 (hK : Nat.card K = 2) {ω : D.L} (hω : ω ^ 2 + ω + 1 = 0) {k : ℕ}
    (hk : k ∈ stdRep) {a : ℕ} (ha : a ∈ ([1, 2, 3] : List ℕ)) :
    ∃ u : ModGL Tag.E8 K, u ∈ Qθ Tag.E8 K ∧
      ΨE D u = pinnedX Tag.E8 D.L (nuW (2 * k)) (emb ω a) *
        pinnedX Tag.E8 D.L (nuW (2 * k + 1)) (emb ω a ^ 2) ∧
      κF D u = decv ω (a <<< (2 * k)) := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  haveI hAC : IsAlgClosed D.L := IsAlgClosure.isAlgClosed K
  set S := toSetup D ⊥ with hS
  have hk10 : k < 10 := stdRep_lt k hk
  have ha4 : a < 4 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    omega
  have hs : emb ω a ^ 4 = emb ω a := emb_pow4 hω ha4
  have hA4 := adjP4_std k hk
  have h1 : 2 * k < 20 := by omega
  have h2 : 2 * k + 1 < 20 := by omega
  have hr₀ : IsRoot Tag.E8 (nuW (2 * k)) := mem_rootFinset.1 (nuW_root h1)
  have hr₁ : IsRoot Tag.E8 (nuW (2 * k + 1)) := mem_rootFinset.1 (nuW_root h2)
  have hsg₀ : S.sg (nuW (2 * k)) = 1 := sg_eq_one D hK hr₀
  have hsg₁ : S.sg (nuW (2 * k + 1)) = 1 := sg_eq_one D hK hr₁
  have hFr : ∀ c : D.L, S.Fr c = c ^ 2 := fun c => Fr_sq D hK c
  obtain ⟨hp1, hp2⟩ := nuW_pair k (List.mem_range.2 hk10)
  have hcomm : ∀ x y : D.L, pinnedX Tag.E8 D.L (nuW (2 * k)) x * pinnedX Tag.E8 D.L (nuW (2 * k + 1)) y =
      pinnedX Tag.E8 D.L (nuW (2 * k + 1)) y * pinnedX Tag.E8 D.L (nuW (2 * k)) x := fun x y =>
    pinnedX_commute_of_not_root (nuW_root h1) (nuW_root h2) hA4.1 hA4.2.1 hA4.2.2 x y
  have hσ := S.pair_sfixed hr₀ hr₁ (by rw [toSetup_hw]; exact hp1) (by rw [toSetup_hw]; exact hp2)
    hcomm (s := emb ω a) (d := emb ω a ^ 2) (by rw [hsg₀, one_mul, hFr]) (by
      rw [hsg₁, one_mul, hFr, ← pow_mul]
      exact hs)
  have hxA : pinnedX Tag.E8 D.L (nuW (2 * k)) (emb ω a) *
      pinnedX Tag.E8 D.L (nuW (2 * k + 1)) (emb ω a ^ 2) ∈ adjointGroup Tag.E8 D.L :=
    mul_mem (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨_, rfl⟩))
      (rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨_, rfl⟩))
  obtain ⟨l, hlA, hl⟩ := S.rat_of_sfixed hxA hσ
  have hl' : baseChangeGL (algebraMap K D.L) l = gE D * (pinnedX Tag.E8 D.L (nuW (2 * k)) (emb ω a) *
      pinnedX Tag.E8 D.L (nuW (2 * k + 1)) (emb ω a ^ 2)) * (gE D)⁻¹ := hl
  have hΨ : ΨE D l = pinnedX Tag.E8 D.L (nuW (2 * k)) (emb ω a) *
      pinnedX Tag.E8 D.L (nuW (2 * k + 1)) (emb ω a ^ 2) := by
    unfold ΨE
    rw [hl']
    group
  have hβ₀D : nuW (2 * k) ∈ Deg1 Tag.E8 := mRoots_deg1 (nuW_data _ (List.mem_range.2 h1)).1
  have hβ₁D : nuW (2 * k + 1) ∈ Deg1 Tag.E8 := mRoots_deg1 (nuW_data _ (List.mem_range.2 h2)).1
  have hQ₀ := pinnedX_mem_Qθ_of_mem_Deg1 hβ₀D (emb ω a)
  have hQ₁ := pinnedX_mem_Qθ_of_mem_Deg1 hβ₁D (emb ω a ^ 2)
  have hlQ : l ∈ Qθ Tag.E8 K := by
    refine mem_Qθ_of_bc D hK hlA ?_
    rw [hl']
    exact Lθ_conj_mem_Qθ (gE_mem_Lθ D) (mul_mem hQ₀ hQ₁)
  refine ⟨l, hlQ, hΨ, ?_⟩
  rw [κF_eq, hΨ, (heisCoord_spec Tag.E8 D.L).mul _ hQ₀ _ hQ₁,
    (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 _ hβ₀D, (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 _ hβ₁D,
    decv_pair hω hk10 ha4]

theorem exists_apos :
    ∃ t : D.L, t ≠ 0 ∧ ΨE D (pinnedX Tag.E8 K (highRoot Tag.E8) 1) =
      pinnedX Tag.E8 D.L (highRoot Tag.E8) t := by
  set a := pinnedX Tag.E8 K (highRoot Tag.E8) 1 with ha
  have hbc : baseChangeGL (algebraMap K D.L) a = pinnedX Tag.E8 D.L (highRoot Tag.E8) 1 := by
    rw [ha, baseChangeGL_pinnedX, map_one]
  have hx : pinnedX Tag.E8 D.L (highRoot Tag.E8) 1 ∈ Uθ Tag.E8 D.L := mem_rootSubgroup.2 ⟨1, rfl⟩
  have hmem := Lθ_conj_mem_Uθ (inv_mem (gE_mem_Lθ D)) hx
  rw [inv_inv] at hmem
  obtain ⟨t, ht⟩ := mem_rootSubgroup.1 hmem
  have hΨ : ΨE D a = pinnedX Tag.E8 D.L (highRoot Tag.E8) t := by
    unfold ΨE
    rw [hbc, ht]
  refine ⟨t, ?_, hΨ⟩
  intro h0
  rw [h0, pinnedX_zero] at hΨ
  have h1 : a = 1 := ΨE_injective D (by rw [hΨ, ΨE_one])
  exact one_ne_zero ((E8TwoD.pinnedX_eq_one_iff (τ := Tag.E8) (highRoot Tag.E8) (1 : K)).1 h1)

theorem N_rat (hK : Nat.card K = 2) {ω : D.L} (hω : ω ^ 2 + ω + 1 = 0) {k : ℕ} (hk : k ∈ stdRep)
    {a : ℕ} (ha : a ∈ ([1, 2, 3] : List ℕ)) {u₀ : ModGL Tag.E8 K} (hu₀Q : u₀ ∈ Qθ Tag.E8 K)
    (hΨu : ΨE D u₀ = pinnedX Tag.E8 D.L (nuW (2 * k)) (emb ω a) *
      pinnedX Tag.E8 D.L (nuW (2 * k + 1)) (emb ω a ^ 2))
    {t₁ t₂ : D.L} (ha₁ : ΨE D (pinnedX Tag.E8 K (highRoot Tag.E8) 1) = pinnedX Tag.E8 D.L (highRoot Tag.E8) t₁)
    (ha₂ : ΨE D (pinnedX Tag.E8 K (-highRoot Tag.E8) 1) = pinnedX Tag.E8 D.L (-highRoot Tag.E8) t₂) :
    ⁅pinnedX Tag.E8 K (highRoot Tag.E8) 1, ⁅pinnedX Tag.E8 K (-highRoot Tag.E8) 1, u₀⁆⁆ ∈ Qθ Tag.E8 K ∧
      κF D ⁅pinnedX Tag.E8 K (highRoot Tag.E8) 1, ⁅pinnedX Tag.E8 K (-highRoot Tag.E8) 1, u₀⁆⁆ =
        (t₁ * t₂) • decv ω (a <<< (2 * k)) := by
  haveI hcL : CharP D.L 2 := charP_L D hK
  have hk10 : k < 10 := stdRep_lt k hk
  have ha4 : a < 4 := by
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
    omega
  have h1 : 2 * k < 20 := by omega
  have h2 : 2 * k + 1 < 20 := by omega
  have hβ₀D : nuW (2 * k) ∈ Deg1 Tag.E8 := mRoots_deg1 (nuW_data _ (List.mem_range.2 h1)).1
  have hβ₁D : nuW (2 * k + 1) ∈ Deg1 Tag.E8 := mRoots_deg1 (nuW_data _ (List.mem_range.2 h2)).1
  set N := ⁅pinnedX Tag.E8 K (highRoot Tag.E8) 1, ⁅pinnedX Tag.E8 K (-highRoot Tag.E8) 1, u₀⁆⁆ with hN
  have hΨN : ΨE D N = ⁅pinnedX Tag.E8 D.L (highRoot Tag.E8) t₁, ⁅pinnedX Tag.E8 D.L (-highRoot Tag.E8) t₂,
      pinnedX Tag.E8 D.L (nuW (2 * k)) (emb ω a) *
        pinnedX Tag.E8 D.L (nuW (2 * k + 1)) (emb ω a ^ 2)⁆⁆ := by
    rw [hN, ΨE_comm, ΨE_comm, ha₁, ha₂, hΨu]
  obtain ⟨ε₀, ε₁, hε₀, hε₁, hNc⟩ := N_calc (L := D.L) (stdPair_adj hk) (emb ω a) (emb ω a ^ 2) t₁ t₂
  rw [sign_eq_one hε₀, sign_eq_one hε₁] at hNc
  simp only [one_mul] at hNc
  rw [hNc] at hΨN
  have hQ₀ := pinnedX_mem_Qθ_of_mem_Deg1 hβ₀D (t₁ * t₂ * emb ω a)
  have hQ₁ := pinnedX_mem_Qθ_of_mem_Deg1 hβ₁D (t₁ * t₂ * emb ω a ^ 2)
  have hNadj : N ∈ adjointGroup Tag.E8 K := by
    have h1' : pinnedX Tag.E8 K (highRoot Tag.E8) 1 ∈ adjointGroup Tag.E8 K :=
      rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨1, rfl⟩)
    have h2' : pinnedX Tag.E8 K (-highRoot Tag.E8) 1 ∈ adjointGroup Tag.E8 K :=
      rootSubgroup_le_adjointGroup _ (mem_rootSubgroup.2 ⟨1, rfl⟩)
    have h3' := Qθ_le_adjointGroup Tag.E8 K hu₀Q
    rw [hN]
    simp only [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem h1' (mul_mem (mul_mem (mul_mem h2' h3') (inv_mem h2')) (inv_mem h3')))
      (inv_mem h1')) (inv_mem (mul_mem (mul_mem (mul_mem h2' h3') (inv_mem h2')) (inv_mem h3')))
  have hNQ : N ∈ Qθ Tag.E8 K := by
    refine mem_Qθ_of_bc D hK hNadj ?_
    rw [bc_eq_conj D, hΨN]
    exact Lθ_conj_mem_Qθ (gE_mem_Lθ D) (mul_mem hQ₀ hQ₁)
  refine ⟨hNQ, ?_⟩
  rw [κF_eq, hΨN, (heisCoord_spec Tag.E8 D.L).mul _ hQ₀ _ hQ₁,
    (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 _ hβ₀D, (heisCoord_spec Tag.E8 D.L).pinnedX_deg1 _ hβ₁D,
    decv_pair hω hk10 ha4]
  funext ν
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
  split_ifs <;> ring

end Std

end CFSG.HardMathSupport.Foote.Coordinator.TwistedFrame.E8TenAux
