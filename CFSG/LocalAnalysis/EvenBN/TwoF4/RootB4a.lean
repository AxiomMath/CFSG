module

public import CFSG.LocalAnalysis.EvenBN.TwoF4.RootB3

public noncomputable section

namespace CFSG.LocalAnalysis.EvenBN.TwoF4

open Subgroup
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution
open CFSG.LieType.Ree.LargeReeCover (torusPair)
open scoped commutatorElement

section Model

variable {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}

theorem reeGamma_inf_centralizer_S2_le (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    F4.reeGamma K a ⊓ centralizer (S2 K a : Set (ModGL F4.tag K)) ≤ S4 K a := by
  rintro y ⟨hyΓ, hyc⟩
  have hfS2 : invF K a ∈ S2 K a := rootV_le_rootJoin (i := .i10) (by decide)
    (rootElt_mem_rootV _ _)
  have hyD : y ∈ F4.reeGamma K a ⊓ centralizer {invF K a} :=
    mem_inf.2 ⟨hyΓ, mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 hyc _ hfS2).symm⟩
  rw [(reeGamma_inf_centralizer_invE_invF ha hK).2.2.1, sup_comm] at hyD
  have hN4 : leviN K a .i3 ≤ normalizer (S4 K a : Set (ModGL F4.tag K)) := by
    rw [S4_eq_tKernel hK]
    exact rankOneGroupOne_le_normalizer_tKernel hK
  have hyD' : y ∈ ((leviN K a .i3 ⊔ S4 K a : Subgroup (ModGL F4.tag K)) :
      Set (ModGL F4.tag K)) := hyD
  rw [coe_mul_of_left_le_normalizer_right _ _ hN4, Set.mem_mul] at hyD'
  obtain ⟨n, hn, q, hq, rfl⟩ := hyD'
  have hN2 : leviN K a .i3 ≤ normalizer (S2 K a : Set (ModGL F4.tag K)) :=
    leviN_three_le_normalizer_rootJoin ha hK (by decide) (by decide) (S2_spec hK).2.2.2
  have hqc : ∀ v ∈ S2 K a, q * v = v * q := fun v hv =>
    mem_centralizer_iff.1 (S2_le_centralizer_S4 ha hK hv) q hq
  have hnc : ∀ v ∈ S2 K a, n * v = v * n := by
    intro v hv
    have h1 := mem_centralizer_iff.1 hyc v hv
    have h2 : n * v * q = v * n * q := by
      calc n * v * q = n * (v * q) := by group
        _ = n * (q * v) := by rw [hqc v hv]
        _ = v * (n * q) := by rw [← mul_assoc, h1]
        _ = v * n * q := by group
    exact mul_right_cancel h2
  let D : Subgroup (leviN K a .i3) :=
    (centralizer (S2 K a : Set (ModGL F4.tag K))).subgroupOf (leviN K a .i3)
  have hDn : D.Normal := ⟨fun m hm k => by
    rw [mem_subgroupOf] at hm ⊢
    refine mem_centralizer_iff.2 fun v hv => ?_
    have hw : (k : ModGL F4.tag K)⁻¹ * v * k ∈ S2 K a := by
      have := (mem_normalizer_iff.1 (hN2 (inv_mem k.2)) v).1 hv
      rwa [inv_inv] at this
    have h1 := mem_centralizer_iff.1 hm _ hw
    simp only [Subgroup.coe_mul, InvMemClass.coe_inv]
    calc v * (↑k * ↑m * (↑k)⁻¹) = ↑k * ((↑k)⁻¹ * v * ↑k * ↑m) * (↑k)⁻¹ := by group
      _ = ↑k * (↑m * ((↑k)⁻¹ * v * ↑k)) * (↑k)⁻¹ := by rw [h1]
      _ = ↑k * ↑m * (↑k)⁻¹ * v := by group⟩
  obtain ⟨hs, -⟩ := isSimpleGroup_leviN ha hK .i3
  have h3 : (⟨rootElt K a .i3 1, rootV_le_leviN hK .i3 (rootElt_mem_rootV _ _)⟩ :
      leviN K a .i3) ∉ D := by
    intro hmem
    rw [mem_subgroupOf] at hmem
    have h11 : rootElt K a .i11 1 ∈ S2 K a := rootV_le_rootJoin (i := .i11) (by decide)
      (rootElt_mem_rootV _ _)
    have hc := mem_centralizer_iff.1 hmem _ h11
    have h1 : ⁅rootElt K a .i3 1, rootElt K a .i11 1⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.2 hc.symm
    rw [rootElt_comm_3_11 hK, one_mul, ← rootElt_zero (K := K) (a := a) .i12] at h1
    exact one_ne_zero (rootElt_injective hK _ h1)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs D hDn with hD | hD
  · have hnD : (⟨n, hn⟩ : leviN K a .i3) ∈ D := by
      rw [mem_subgroupOf]
      exact mem_centralizer_iff.2 fun v hv => (hnc v hv).symm
    have hn1 : n = 1 := by
      have hmem : (⟨n, hn⟩ : leviN K a .i3) ∈ (⊥ : Subgroup (leviN K a .i3)) := hD ▸ hnD
      exact congrArg Subtype.val ((mem_bot).1 hmem)
    rw [hn1, one_mul]
    exact hq
  · exact (h3 (by rw [hD]; exact mem_top _)).elim

theorem commutator_S4_S4_le (hK : Nat.card K = 2 ^ (2 * a + 1)) : ⁅S4 K a, S4 K a⁆ ≤ S2 K a := by
  have hlev := commutator_rootSpan_levelSet_le (K := K) (ℓ := ![0, 10, 7, 0])
    (fun k => by fin_cases k <;> decide) (t := 17) (t' := 17) (by norm_num) (by norm_num)
  rw [show (17 : ℤ) + 17 = 34 by norm_num] at hlev
  rw [(S4_spec hK).1, (S2_spec hK).1]
  exact le_inf ((commutator_mono inf_le_left inf_le_left).trans hlev)
    ((commutator_mono inf_le_right inf_le_right).trans commutator_reeGamma_le)

theorem rootElt_mul_rootElt_of_isSz (hK : Nat.card K = 2 ^ (2 * a + 1)) {k : Idx}
    (hk : k.isSz = true) (c e : K) :
    rootElt K a k c * rootElt K a k e =
      rootElt K a k (c + e) * rootElt K a k.center (largeReeSigma a c * e) := by
  have hcz : k.center.isCenter = true ∧ k.center.fourIdx = k.fourIdx := by
    cases k <;> simp_all [Idx.isSz, Idx.center, Idx.isCenter, Idx.fourIdx]
  rw [(rootElt_eq_coord k c).1 hk, (rootElt_eq_coord k e).1 hk, (rootElt_eq_coord k _).1 hk,
    (rootElt_eq_coord _ _).2.1 hcz.1, hcz.2, fourCoordG_mul_fourCoordG hK,
    ← fourCoordG_eq_mul hK, zero_add, zero_add]

theorem S4_le_of_rootV_five (hK : Nat.card K = 2 ^ (2 * a + 1)) {N : Subgroup (ModGL F4.tag K)}
    (hS2 : S2 K a ≤ N) (h5 : rootV K a .i5 ≤ N)
    (h3 : ∀ c : K, rootElt K a .i3 c ∈ normalizer (N : Set (ModGL F4.tag K)))
    (hs : weylS K ∈ normalizer (N : Set (ModGL F4.tag K))) : S4 K a ≤ N := by
  have hconj : ∀ {g x : ModGL F4.tag K}, g ∈ normalizer (N : Set (ModGL F4.tag K)) → x ∈ N →
      g * x * g⁻¹ ∈ N := fun hg hx => (mem_normalizer_iff.1 hg _).1 hx
  have hcomm : ∀ {g x : ModGL F4.tag K}, g ∈ normalizer (N : Set (ModGL F4.tag K)) → x ∈ N →
      ⁅g, x⁆ ∈ N := fun hg hx => by
    rw [commutatorElement_def]
    exact mul_mem (hconj hg hx) (inv_mem hx)
  have hV : ∀ i : Idx, (∀ c, rootElt K a i c ∈ N) → rootV K a i ≤ N := fun i hi =>
    (closure_le _).2 (by rintro _ ⟨c, rfl⟩; exact hi c)
  have hsV : ∀ i : Idx, i ≠ .i3 → rootV K a i ≤ N → rootV K a i.sPerm ≤ N := fun i hi hiN =>
    hV _ fun c => by
      rw [← weylS_conj_rootElt hi]
      exact hconj hs (hiN (rootElt_mem_rootV _ _))
  have hS2' : ∀ i ∈ ({.i10, .i11, .i12} : Finset Idx), rootV K a i ≤ N := fun i hi =>
    (rootV_le_rootJoin hi).trans hS2
  have h8 : rootV K a .i8 ≤ N := hV _ fun c => by
    have := hcomm (h3 1) (h5 (rootElt_mem_rootV (a := a) .i5 c))
    rwa [rootElt_comm_3_5 hK, one_mul] at this
  have h6 : rootV K a .i6 ≤ N := hsV .i5 (by decide) h5
  have h9 : rootV K a .i9 ≤ N := hV _ fun c => by
    have hc := hcomm (h3 c) (h6 (rootElt_mem_rootV (a := a) .i6 1))
    simp only [rootElt_comm_3_6 hK, largeReeSigma_one, one_mul, mul_one] at hc
    have h8' := h8 (rootElt_mem_rootV (a := a) .i8 (largeReeSigma a c))
    have h12' := hS2' .i12 (by decide) (rootElt_mem_rootV (a := a) .i12 c)
    have e : rootElt K a .i9 c = (rootElt K a .i8 (largeReeSigma a c))⁻¹ *
        (rootElt K a .i8 (largeReeSigma a c) * rootElt K a .i9 c * rootElt K a .i12 c) *
          (rootElt K a .i12 c)⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem (inv_mem h8') hc) (inv_mem h12')
  have h2 : rootV K a .i2 ≤ N := hsV .i8 (by decide) h8
  have h7 : rootV K a .i7 ≤ N := hsV .i9 (by decide) h9
  refine iSup₂_le fun i hi => ?_
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h2
  · exact h5
  · exact h6
  · exact h8
  · exact h7
  · exact h9
  · exact hS2' _ (by decide)
  · exact hS2' _ (by decide)
  · exact hS2' _ (by decide)

theorem S4_le_of_rootV_eight_nine (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {N : Subgroup (ModGL F4.tag K)} (hS2 : S2 K a ≤ N) (h8 : rootV K a .i8 ≤ N)
    (h9 : rootV K a .i9 ≤ N)
    (h3 : ∀ c : K, rootElt K a .i3 c ∈ normalizer (N : Set (ModGL F4.tag K)))
    (hs : weylS K ∈ normalizer (N : Set (ModGL F4.tag K)))
    (hH : ∀ τ : Kˣ × Kˣ, torusPair a τ ∈ normalizer (N : Set (ModGL F4.tag K))) :
    S4 K a ≤ N := by
  have hconj : ∀ {g x : ModGL F4.tag K}, g ∈ normalizer (N : Set (ModGL F4.tag K)) → x ∈ N →
      g * x * g⁻¹ ∈ N := fun hg hx => (mem_normalizer_iff.1 hg _).1 hx
  have hcomm : ∀ {g x : ModGL F4.tag K}, g ∈ normalizer (N : Set (ModGL F4.tag K)) → x ∈ N →
      ⁅g, x⁆ ∈ N := fun hg hx => by
    rw [commutatorElement_def]
    exact mul_mem (hconj hg hx) (inv_mem hx)
  have hV : ∀ i : Idx, (∀ c, rootElt K a i c ∈ N) → rootV K a i ≤ N := fun i hi =>
    (closure_le _).2 (by rintro _ ⟨c, rfl⟩; exact hi c)
  have hsV : ∀ i : Idx, i ≠ .i3 → rootV K a i ≤ N → rootV K a i.sPerm ≤ N := fun i hi hiN =>
    hV _ fun c => by
      rw [← weylS_conj_rootElt hi]
      exact hconj hs (hiN (rootElt_mem_rootV _ _))
  have h2 : rootV K a .i2 ≤ N := hsV .i8 (by decide) h8
  have h7 : rootV K a .i7 ≤ N := hsV .i9 (by decide) h9
  have h11 : ∀ e : K, rootElt K a .i11 e ∈ N := fun e =>
    hS2 (rootV_le_rootJoin (i := .i11) (by decide) (rootElt_mem_rootV _ _))
  have hz : ∀ c : K, rootElt K a .i6 c * rootElt K a .i5 (largeReeSigma a c) ∈ N := by
    intro c
    have hc := hcomm (h3 c) (h2 (rootElt_mem_rootV (a := a) .i2 1))
    simp only [rootElt_comm_3_2 hK, largeReeSigma_one, mul_one, one_mul] at hc
    have h67 : rootElt K a .i6 c * rootElt K a .i7 c = rootElt K a .i7 c * rootElt K a .i6 c :=
      commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_6_7 hK c c)
    have e : rootElt K a .i6 c * rootElt K a .i5 (largeReeSigma a c) =
        (rootElt K a .i7 c)⁻¹ * (rootElt K a .i6 c * rootElt K a .i7 c *
          rootElt K a .i5 (largeReeSigma a c) * rootElt K a .i8 (c * largeReeSigma a c) *
            rootElt K a .i9 (c * largeReeSigma a c)) *
          (rootElt K a .i9 (c * largeReeSigma a c))⁻¹ *
            (rootElt K a .i8 (c * largeReeSigma a c))⁻¹ := by
      rw [h67]
      group
    rw [e]
    exact mul_mem (mul_mem (mul_mem (inv_mem (h7 (rootElt_mem_rootV _ _))) hc)
      (inv_mem (h9 (rootElt_mem_rootV _ _)))) (inv_mem (h8 (rootElt_mem_rootV _ _)))
  obtain ⟨l, hl⟩ := exists_largeReeSigma_ne ha hK
  have hl0 : l ≠ 0 := fun h0 => hl (by rw [h0, largeReeSigma_zero])
  have hl1 : l - 1 ≠ 0 := fun h1 => hl (by rw [sub_eq_zero.1 h1, largeReeSigma_one])
  obtain ⟨τ, hτ5, hτ6⟩ := exists_rootChar_mul_eq hK (i := .i5) rfl (j := .i6) (by decide)
    one_ne_zero hl0
  rw [mul_one] at hτ6
  have h6 : rootV K a .i6 ≤ N := hV _ fun d => by
    set c := d * (l - 1)⁻¹ with hcdef
    have hlc : l * c = d + c := by
      rw [hcdef]
      field_simp
      ring
    have hw := hz c
    have hw' := hconj (hH τ) hw
    have e1 : torusPair a τ * (rootElt K a .i6 c * rootElt K a .i5 (largeReeSigma a c)) *
        (torusPair a τ)⁻¹ = rootElt K a .i6 (d + c) * rootElt K a .i5 (largeReeSigma a c) := by
      rw [show torusPair a τ * (rootElt K a .i6 c * rootElt K a .i5 (largeReeSigma a c)) *
          (torusPair a τ)⁻¹ = (torusPair a τ * rootElt K a .i6 c * (torusPair a τ)⁻¹) *
            (torusPair a τ * rootElt K a .i5 (largeReeSigma a c) * (torusPair a τ)⁻¹) by group,
        torusPair_conj_rootElt hK, torusPair_conj_rootElt hK, hτ6, hτ5, Units.val_one, one_mul,
        hlc]
    rw [e1] at hw'
    have hm := rootElt_mul_rootElt_of_isSz (a := a) hK (k := .i6) rfl d c
    have h611 : rootElt K a .i6 c * rootElt K a .i11 (largeReeSigma a d * c) =
        rootElt K a .i11 (largeReeSigma a d * c) * rootElt K a .i6 c :=
      commutatorElement_eq_one_iff_mul_comm.1 (rootElt_comm_6_11 hK _ _)
    have e2 : rootElt K a .i6 d =
        (rootElt K a .i6 (d + c) * rootElt K a .i5 (largeReeSigma a c) *
          (rootElt K a .i6 c * rootElt K a .i5 (largeReeSigma a c))⁻¹) *
        (rootElt K a .i6 c * rootElt K a .i11 (largeReeSigma a d * c) *
          (rootElt K a .i6 c)⁻¹) := by
      calc rootElt K a .i6 d = rootElt K a .i6 d * rootElt K a .i6 c * (rootElt K a .i6 c)⁻¹ := by
            group
        _ = rootElt K a .i6 (d + c) * rootElt K a .i11 (largeReeSigma a d * c) *
            (rootElt K a .i6 c)⁻¹ := by
          rw [hm]
          rfl
        _ = _ := by group
    rw [e2, h611, mul_inv_cancel_right]
    exact mul_mem (mul_mem hw' (inv_mem hw)) (h11 _)
  have h5 : rootV K a .i5 ≤ N := hsV .i6 (by decide) h6
  exact S4_le_of_rootV_five hK hS2 h5 h3 hs

end Model

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable (h : Setup G)

theorem S2_S4_le_reeGamma :
    S2 h.K h.a ≤ F4.reeGamma h.K h.a ∧ S4 h.K h.a ≤ F4.reeGamma h.K h.a :=
  ⟨(rootJoin_le_sylowP h.card_K _).trans inf_le_right,
    (rootJoin_le_sylowP h.card_K _).trans inf_le_right⟩

theorem L_inf_centralizer_S₂_le : h.L ⊓ centralizer (h.S₂ : Set G) ≤ h.S₄ := by
  rw [S₂, ← h.pull_centralizer_subgroup h.S2_S4_le_reeGamma.1]
  intro x hx
  obtain ⟨g, hg, hgΓ, rfl⟩ := h.mem_pull_iff_elt.1 hx
  exact (h.elt_mem_pull hgΓ).2
    (reeGamma_inf_centralizer_S2_le h.one_le_a h.card_K (mem_inf.2 ⟨hgΓ, hg⟩))

theorem C_inf_centralizer_S₂_le : h.C ⊓ centralizer (h.S₂ : Set G) ≤ h.S₄ ⊔ zpowers h.t := by
  intro x hx
  obtain ⟨hxC, hxS⟩ := mem_inf.1 hx
  have hV12 : h.V .i12 ≤ h.S₂ := h.pull_mono (rootV_le_rootJoin (by decide))
  have hxV : x ∈ h.CE := mem_inf.2 ⟨hxC, centralizer_le (SetLike.coe_subset_coe.2 hV12) hxS⟩
  have htS : h.t ∈ centralizer (h.S₂ : Set G) :=
    centralizer_le (SetLike.coe_subset_coe.2 (h.pull_le_L _)) h.htL
  obtain ⟨r, hr, m, hm, hxe | hxe⟩ := h.exists_of_mem_CE hxV
  · have hlS : r * m ∈ centralizer (h.S₂ : Set G) := by rw [← hxe]; exact hxS
    have hl : r * m ∈ h.S₄ := h.L_inf_centralizer_S₂_le
      (mem_inf.2 ⟨mul_mem (h.R_le_L hr) (h.N_le_L _ hm), hlS⟩)
    rw [hxe]
    exact mem_sup_left hl
  · have hlS : r * m ∈ centralizer (h.S₂ : Set G) := by
      have := mul_mem hxS (inv_mem htS)
      rwa [hxe, mul_inv_cancel_right] at this
    have hl : r * m ∈ h.S₄ := h.L_inf_centralizer_S₂_le
      (mem_inf.2 ⟨mul_mem (h.R_le_L hr) (h.N_le_L _ hm), hlS⟩)
    rw [hxe]
    exact mul_mem (mem_sup_left hl) (mem_sup_right (mem_zpowers _))

theorem comm_S₄_S₄_mem {u v : G} (hu : u ∈ h.S₄) (hv : v ∈ h.S₄) : ⁅u, v⁆ ∈ h.S₂ := by
  have e := h.pull_mono (commutator_S4_S4_le h.card_K)
  rw [h.pull_commutator h.S2_S4_le_reeGamma.2 h.S2_S4_le_reeGamma.2] at e
  exact e (commutator_mem_commutator hu hv)

theorem S₂_le_centralizer_S₄ : h.S₂ ≤ centralizer (h.S₄ : Set G) :=
  h.pull_le_centralizer (S2_le_centralizer_S4 h.one_le_a h.card_K)

theorem elt_rootElt_three_mem_Kp (c : h.K) : h.elt (rootElt h.K h.a .i3 c) ∈ h.Kp := by
  have hΓ : rootElt h.K h.a .i3 c ∈ F4.reeGamma h.K h.a :=
    rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _)
  have hN : rootElt h.K h.a .i3 c ∈ normalizer (radS h.K h.a : Set (ModGL F4.tag h.K)) := by
    have hmem : rootElt h.K h.a .i3 c ∈ F4.reeGamma h.K h.a ⊓
        normalizer (radS h.K h.a : Set (ModGL F4.tag h.K)) := by
      rw [(miyamoto_2_3 h.one_le_a h.card_K).2.1]
      exact mem_sup_left (mem_sup_right (rootV_le_leviN h.card_K .i3 (rootElt_mem_rootV _ _)))
    exact hmem.2
  refine mem_inf.2 ⟨h.L_le_C (h.elt_mem hΓ), ?_⟩
  have hle := h.pull_le_normalizer (M := normalizer (radS h.K h.a : Set (ModGL F4.tag h.K)))
    (M' := radS h.K h.a) le_rfl
  exact hle ((h.elt_mem_pull hΓ).2 hN)

theorem mem_normalizer_unpull_inf {N : Subgroup G} {g : ModGL F4.tag h.K}
    (hg : g ∈ F4.reeGamma h.K h.a) (hgN : h.elt g ∈ normalizer (N : Set G)) :
    g ∈ normalizer (h.unpull (N ⊓ h.L) : Set (ModGL F4.tag h.K)) := by
  have hgL : h.elt g ∈ normalizer ((N ⊓ h.L : Subgroup G) : Set G) :=
    mem_normalizer_inf hgN (le_normalizer (h.elt_mem hg))
  have hgL' : h.elt g⁻¹ ∈ normalizer ((N ⊓ h.L : Subgroup G) : Set G) := by
    rw [h.elt_inv' hg]
    exact inv_mem hgL
  refine mem_normalizer_of_conj_mem (fun x hx => h.conj_mem_unpull hg hgL hx) (fun x hx => ?_)
  have := h.conj_mem_unpull (inv_mem hg) hgL' hx
  rwa [inv_inv] at this

theorem le_unpull_inf {N : Subgroup G} {M : Subgroup (ModGL F4.tag h.K)}
    (hMΓ : M ≤ F4.reeGamma h.K h.a) (hM : h.pull M ≤ N) : M ≤ h.unpull (N ⊓ h.L) := by
  intro g hg
  have hgΓ := hMΓ hg
  rw [h.mem_unpull hgΓ]
  exact ⟨hM ((h.elt_mem_pull hgΓ).2 hg), h.elt_mem hgΓ⟩

theorem S₄_le_of_V5 {N : Subgroup G} (hS2 : h.S₂ ≤ N) (h5 : h.V .i5 ≤ N)
    (h3 : ∀ c : h.K, h.elt (rootElt h.K h.a .i3 c) ∈ normalizer (N : Set G))
    (hs : h.s ∈ normalizer (N : Set G)) : h.S₄ ≤ N := by
  have key := S4_le_of_rootV_five h.card_K (N := h.unpull (N ⊓ h.L))
    (h.le_unpull_inf h.S2_S4_le_reeGamma.1 hS2)
    (h.le_unpull_inf (rootV_le_reeGamma h.card_K _) h5)
    (fun c => h.mem_normalizer_unpull_inf (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _))
      (h3 c))
    (h.mem_normalizer_unpull_inf weylS_mem_reeGamma (by rw [h.elt_weylS]; exact hs))
  have := h.pull_mono key
  rw [h.pull_unpull inf_le_right] at this
  exact this.trans inf_le_left

theorem S₄_le_of_V8_V9 {N : Subgroup G} (hS2 : h.S₂ ≤ N) (h8 : h.V .i8 ≤ N) (h9 : h.V .i9 ≤ N)
    (h3 : ∀ c : h.K, h.elt (rootElt h.K h.a .i3 c) ∈ normalizer (N : Set G))
    (hs : h.s ∈ normalizer (N : Set G)) (hH : h.H ≤ normalizer (N : Set G)) : h.S₄ ≤ N := by
  have key := S4_le_of_rootV_eight_nine h.one_le_a h.card_K (N := h.unpull (N ⊓ h.L))
    (h.le_unpull_inf h.S2_S4_le_reeGamma.1 hS2)
    (h.le_unpull_inf (rootV_le_reeGamma h.card_K _) h8)
    (h.le_unpull_inf (rootV_le_reeGamma h.card_K _) h9)
    (fun c => h.mem_normalizer_unpull_inf (rootV_le_reeGamma h.card_K _ (rootElt_mem_rootV _ _))
      (h3 c))
    (h.mem_normalizer_unpull_inf weylS_mem_reeGamma (by rw [h.elt_weylS]; exact hs))
    (fun τ => h.mem_normalizer_unpull_inf (h.torusPair_mem_reeGamma τ)
      (hH (h.elt_torusPair_mem_H τ)))
  have := h.pull_mono key
  rw [h.pull_unpull inf_le_right] at this
  exact this.trans inf_le_left

end Setup

namespace LevelOneData

variable {h : Setup G} (d : LevelOneData h)

theorem B2_le_centralizer_B2 : d.B2 ≤ centralizer (d.B2 : Set G) := by
  have h10 : ∀ x ∈ d.WA .i10, ∀ y ∈ d.WA .i10, x * y = y * x := fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.1 (d.sec3_7_two.2.2.2.2.2.1 x hx y hy)
  have h10B : ∀ x ∈ d.WA .i10, ∀ y ∈ d.B1, x * y = y * x := fun x hx y hy =>
    commutatorElement_eq_one_iff_mul_comm.1 (d.sec3_7_two.2.2.2.2.2.2 x
      (d.WA_le_B3 (Or.inr rfl) hx) y hy)
  have hc : ∀ x ∈ d.WA .i10 ⊔ d.B1, ∀ y ∈ d.WA .i10, y * x = x * y := by
    intro x hx
    have hle : d.WA .i10 ⊔ d.B1 ≤ centralizer (d.WA .i10 : Set G) :=
      sup_le (fun z hz => mem_centralizer_iff.2 fun y hy => h10 y hy z hz)
        (fun z hz => mem_centralizer_iff.2 fun y hy => h10B y hy z hz)
    exact fun y hy => mem_centralizer_iff.1 (hle hx) y hy
  have hc' : ∀ x ∈ d.WA .i10 ⊔ d.B1, ∀ y ∈ d.B1, y * x = x * y := by
    intro x hx
    have hle : d.WA .i10 ⊔ d.B1 ≤ centralizer (d.B1 : Set G) :=
      sup_le (fun z hz => mem_centralizer_iff.2 fun y hy => (h10B z hz y hy).symm)
        (fun z hz => mem_centralizer_iff.2 fun y hy => d.B1_comm hy hz)
    exact fun y hy => mem_centralizer_iff.1 (hle hx) y hy
  intro x hx
  have hle : d.WA .i10 ⊔ d.B1 ≤ centralizer ({x} : Set G) :=
    sup_le (fun y hy => mem_centralizer_singleton_iff.2 (hc x hx y hy))
      (fun y hy => mem_centralizer_singleton_iff.2 (hc' x hx y hy))
  exact mem_centralizer_iff.2 fun y hy => mem_centralizer_singleton_iff.1 (hle hy)

theorem B2_comm {x y : G} (hx : x ∈ d.B2) (hy : y ∈ d.B2) : x * y = y * x :=
  (mem_centralizer_iff.1 (d.B2_le_centralizer_B2 hy) x hx)

@[expose] def sqIn (N : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ d.B2 ∧ x * x ∈ N}
  mul_mem' := fun {x y} hx hy => ⟨mul_mem hx.1 hy.1, by
    have e : x * y * (x * y) = x * x * (y * y) := by
      rw [show x * y * (x * y) = x * (y * x) * y by group, ← d.B2_comm hx.1 hy.1]
      group
    rw [e]
    exact mul_mem hx.2 hy.2⟩
  one_mem' := ⟨one_mem _, by rw [mul_one]; exact one_mem _⟩
  inv_mem' := fun {x} hx => ⟨inv_mem hx.1, by
    rw [← mul_inv_rev]
    exact inv_mem hx.2⟩

theorem WA10_sq_mem {x : G} (hx : x ∈ d.WA .i10) : x * x ∈ h.V .i10 := by
  refine d.mem_V_of_mem_WA (i := .i10) rfl (by decide) (mul_mem hx hx) ?_
  rw [d.comm_t_mul_A1 hx.1 hx.1]
  exact h.R₁_mul_self hx.1.2.2

theorem B2_sq_mem {x : G} (hx : x ∈ d.B2) : x * x ∈ h.V .i10 := by
  have hle : d.B2 ≤ d.sqIn (h.V .i10) :=
    sup_le (fun y hy => ⟨mem_sup_left hy, d.WA10_sq_mem hy⟩)
      (fun y hy => ⟨mem_sup_right hy, by rw [d.B1_mul_self hy]; exact one_mem _⟩)
  exact (hle hx).2

theorem WA10_mul_self {x : G} (hx : x ∈ d.WA .i10) : x * x = 1 := by
  obtain ⟨c, hc⟩ := h.exists_eq_elt_rootElt (i := .i10) rfl (d.WA10_sq_mem hx)
  set y := h.elt (rootElt h.K h.a .i1 1) with hy
  have hyK : y ∈ h.Kp := h.S₂_le_S₃_le_S₄_le_S.2.2.2.2
    (h.S₂_le_S₃_le_S₄_le_S.2.2.2.1 (h.V_le_S (k := .i1) (by decide) (h.elt_rootElt_mem_V _ _)))
  have hyB : y * x * y⁻¹ ∈ d.B2 :=
    (mem_normalizer_iff.1 (d.Kp_le_normalizer_B2 hyK) x).1 (mem_sup_left hx)
  have hsq := d.B2_sq_mem hyB
  have hΓ : ∀ k c, rootElt h.K h.a k c ∈ F4.reeGamma h.K h.a := fun k c =>
    rootV_le_reeGamma h.card_K k (rootElt_mem_rootV _ _)
  have h1 : ⁅y, h.elt (rootElt h.K h.a .i10 c)⁆ = h.elt (rootElt h.K h.a .i11 c) := by
    rw [hy, ← h.elt_commutator (hΓ _ _) (hΓ _ _), rootElt_comm_1_10 h.card_K, one_mul]
  have e : y * x * y⁻¹ * (y * x * y⁻¹) =
      h.elt (rootElt h.K h.a .i11 c) * h.elt (rootElt h.K h.a .i10 c) := by
    rw [← h1, commutatorElement_def,
      show y * x * y⁻¹ * (y * x * y⁻¹) = y * (x * x) * y⁻¹ by group, ← hc]
    group
  rw [e] at hsq
  have h11 : h.elt (rootElt h.K h.a .i11 c) ∈ h.V .i10 := by
    have := mul_mem hsq (inv_mem (h.elt_rootElt_mem_V .i10 c))
    rwa [mul_inv_cancel_right] at this
  have hr := h.r1c_eq_zero_of_mem (S := {.i10}) (by decide)
    (by rw [h.pull_rootJoin_singleton]; exact h11) (k := .i11) rfl (by decide)
  rw [h.r1c_elt_rootElt rfl c rfl, Pi.single_eq_same] at hr
  rw [hc, hr, rootElt_zero, h.elt_one']

theorem B2_mul_self {x : G} (hx : x ∈ d.B2) : x * x = 1 := by
  have hle : d.B2 ≤ d.sqIn ⊥ :=
    sup_le (fun y hy => ⟨mem_sup_left hy, by rw [d.WA10_mul_self hy]; exact one_mem _⟩)
      (fun y hy => ⟨mem_sup_right hy, by rw [d.B1_mul_self hy]; exact one_mem _⟩)
  exact (mem_bot).1 (hle hx).2

theorem mem_S₂_of_mem_B2 {x : G} (hx : x ∈ d.B2) (hxt : ⁅x, h.t⁆ = 1) : x ∈ h.S₂ :=
  h.mem_S₂_of_commute (h.S₂_le_S₃_le_S₄_le_S.2.1 (d.mem_S₃_of_mem_B3 (d.B2_le_B3 hx) hxt))
    fun w hw => mem_centralizer_iff.1 (d.B2_le_centralizer_S₄ hx) w hw

theorem exists_B2_comm_t {v : G} (hv : v ∈ h.S₂) : ∃ x ∈ d.B2, ⁅x, h.t⁆ = v := by
  obtain ⟨v₁₁, hv11, v₁₂, hv12, v₁₀, hv10, rfl⟩ := h.exists_mul_of_mem_S₂ hv
  obtain ⟨w₁₁, hw11, e11⟩ := d.exists_W11_comm_t hv11
  obtain ⟨w₁₂, hw12, e12⟩ := d.exists_W12_conj hv12
  obtain ⟨w₁₀, hw10, e10⟩ := d.exists_WA_comm_t (h.V_le_R₁ (by decide))
    (h.V_le_CH rfl (Or.inl rfl)) hv10
  have e12' : ⁅w₁₂, h.t⁆ = v₁₂ := by
    rw [commutatorElement_def, e12, ← h.mul_t_comm (h.V12_le_L hv12), mul_inv_cancel_right]
  have h11B : w₁₁ ∈ d.B2 := mem_sup_right (d.W11_le_B1 hw11)
  have h12B : w₁₂ ∈ d.B2 := mem_sup_right (d.W12_le_B1 hw12)
  have h10B : w₁₀ ∈ d.B2 := mem_sup_left hw10
  have hB := fun {z} (hz : z ∈ d.B2) => d.B2_le_B3 hz
  refine ⟨w₁₁ * w₁₂ * w₁₀, mul_mem (mul_mem h11B h12B) h10B, ?_⟩
  rw [d.comm_t_mul_B3 (hB (mul_mem h11B h12B)) (hB h10B), d.comm_t_mul_B3 (hB h11B) (hB h12B),
    e11, e12', e10]

theorem exists_B2_conj_eq {x : G} (hxt : ⁅x, h.t⁆ ∈ d.B2) :
    ∃ b ∈ d.B2, b * h.t * b⁻¹ = x * h.t * x⁻¹ := by
  set b₀ := ⁅x, h.t⁆ with hb₀
  have htt := h.t_mul_t
  have hinv : b₀ * h.t * (b₀ * h.t) = 1 := by
    rw [hb₀, commutatorElement_def]
    calc x * h.t * x⁻¹ * h.t⁻¹ * h.t * (x * h.t * x⁻¹ * h.t⁻¹ * h.t) =
        x * (h.t * h.t) * x⁻¹ := by group
      _ = 1 := by rw [htt]; group
  have hb₀t : ⁅b₀, h.t⁆ = 1 := by
    have hb₀i : b₀⁻¹ = b₀ := inv_eq_of_mul_eq_one_right (d.B2_mul_self hxt)
    rw [commutatorElement_def, hb₀i]
    calc b₀ * h.t * b₀ * h.t⁻¹ = b₀ * h.t * (b₀ * h.t) * (h.t * h.t)⁻¹ := by group
      _ = 1 := by rw [hinv, htt]; group
  obtain ⟨b, hb, hbt⟩ := d.exists_B2_comm_t (d.mem_S₂_of_mem_B2 hxt hb₀t)
  refine ⟨b, hb, ?_⟩
  rw [commutatorElement_def, hb₀, commutatorElement_def] at hbt
  exact mul_right_cancel hbt

theorem exists_B2_mul_mem_C {x : G} (hxt : ⁅x, h.t⁆ ∈ d.B2) :
    ∃ b ∈ d.B2, b⁻¹ * x ∈ h.C := by
  obtain ⟨b, hb, e⟩ := d.exists_B2_conj_eq hxt
  refine ⟨b, hb, mem_centralizer_singleton_iff.2 ?_⟩
  calc b⁻¹ * x * h.t = b⁻¹ * (x * h.t * x⁻¹) * x := by group
    _ = b⁻¹ * (b * h.t * b⁻¹) * x := by rw [e]
    _ = h.t * (b⁻¹ * x) := by group

end LevelOneData

end CFSG.LocalAnalysis.EvenBN.TwoF4
