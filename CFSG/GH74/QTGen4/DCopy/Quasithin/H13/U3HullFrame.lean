module

public import CFSG.Quasithin.H13.U3HullFrame
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3Local1332

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative

variable {G : Type} [Group G]

structure HullSetting_F4
    (G : Type) [Group G] [CFSG.GH74.QTGen4.Finite4 G] (T L V : Subgroup G)
    [IsElementaryAbelian 2 V] (z : G) where

  h1332 : Stmt13_3_2_F4

  hH : QTH13 G T L

  hU3 : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSU 3 3 1

  hF : QTU3InternalFrame T L V z

  Φ : Additive V ≃ₗ[ZMod 2] W6

  hL : ∀ (l : G) (hl : l ∈ L), ∃ j ∈ J6, linConj Φ
    (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j

  hLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), linConj Φ
    (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hF.2.2.2.2.2.2.1 hl⟩) = glLin j

  hN : ∀ n : normalizer (V : Set G), ∃ k ∈ N6,
    linConj Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin k

  hT : ∀ (t : G) (ht : t ∈ T), ∃ s ∈ S0, linConj Φ
    (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨t, hF.2.2.2.2.2.2.2.1 ht⟩) = glLin s

namespace HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting_F4

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}
variable
  (S : HullSetting_F4 G T L V z)
include S

theorem hLV_F4 : L ≤ normalizer (V : Set G) := S.hF.2.2.2.2.2.2.1

theorem hTV_F4 : T ≤ normalizer (V : Set G) := S.hF.2.2.2.2.2.2.2.1

theorem hVT_F4 : V ≤ T := S.hF.2.1

theorem hV64_F4 : Nat.card V = 64 := S.hF.2.2.2.1

theorem hTL_F4 : T ≤ normalizer (L : Set G) := S.hF.1

theorem hz2_F4 : orderOf z = 2 := S.hF.2.2.2.2.2.2.2.2.2.2.2.2

theorem hVz_F4 : V ⊓ centralizer (T : Set G) = zpowers z := S.hF.2.2.2.2.2.2.2.2.2.2.2.1

theorem hzVT_F4 : z ∈ V ⊓ centralizer (T : Set G) := by
  rw [S.hVz_F4]
  exact mem_zpowers z

theorem hzV_F4 : z ∈ V := S.hzVT_F4.1

theorem hz1_F4 : z ≠ 1 := by
  intro h
  have := S.hz2_F4
  rw [h, orderOf_one] at this
  exact absurd this (by norm_num)

noncomputable def rho_F4 : normalizer (V : Set G) →* GL (Fin 6) (ZMod 2) :=
  glLin.symm.toMonoidHom.comp
    ((linConj S.Φ).toMonoidHom.comp (u3ConjLin V (normalizer (V : Set G)) le_rfl))

theorem rho_spec_F4 (n : normalizer (V : Set G)) :
    linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl n) = glLin (S.rho_F4 n) := by
  simp only [rho_F4, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply,
    MulEquiv.apply_symm_apply]

theorem rho_mem_N6_F4 (n : normalizer (V : Set G)) : S.rho_F4 n ∈ N6 := by
  obtain ⟨k, hk, hkn⟩ := S.hN n
  rw [show S.rho_F4 n = k from glLin.injective (by rw [← S.rho_spec_F4, hkn])]
  exact hk

theorem phi_z_F4
    : S.Φ (Additive.ofMul (⟨z, S.hzV_F4⟩ : V)) = vecOf 15 := by
  classical
  set g15 := elOf S.Φ (vecOf 15) with hg15
  have hg15V : g15 ∈ V := elOf_mem _
  have hg : S.Φ (Additive.ofMul (⟨g15, hg15V⟩ : V)) = vecOf 15 := phi_elOf _
  have hg15C : g15 ∈ V ⊓ centralizer (T : Set G) := by
    refine ⟨hg15V, mem_centralizer_iff.2 fun t ht => ?_⟩
    obtain ⟨s, hs, hst⟩ := S.hT t ht
    obtain ⟨i, hi, rfl⟩ := eq_s0GL hs
    have h2 : S.Φ (Additive.ofMul ⟨t * g15 * t⁻¹,
        (mem_normalizer_iff.1 (S.hTV_F4 ht) g15).1 hg15V⟩) = vecOf 15 := by
      rw [phi_conj (S.hTV_F4 ht) hst hg15V, hg, glLin_apply, coe_s0GL hi, colMat_mulVec_vecOf,
        s0c_fix_fifteen _ (by
          rw [s0m, List.getD_eq_getElem _ _ (by rw [s0c_spec.1]; exact hi)]
          exact List.getElem_mem _)]
    have h4 : t * g15 * t⁻¹ = g15 := phi_injective' _ hg15V (h2.trans hg.symm)
    calc t * g15 = t * g15 * t⁻¹ * t := by group
      _ = g15 * t := by rw [h4]
  rw [S.hVz_F4] at hg15C
  have hg151 : g15 ≠ 1 := by
    intro h
    have h1 : S.Φ (Additive.ofMul (⟨g15, hg15V⟩ : V)) = 0 := by
      rw [show (⟨g15, hg15V⟩ : V) = 1 from Subtype.ext h]
      exact map_zero _
    rw [hg] at h1
    exact absurd (vecOf_injective (by norm_num : 15 < 64) (by norm_num : 0 < 64)
      (h1.trans vecOf_zero.symm)) (by norm_num)
  have hgz : g15 = z := by
    rw [mem_zpowers_iff_mem_range_orderOf, S.hz2_F4, Finset.mem_image] at hg15C
    obtain ⟨k, hk, hkz⟩ := hg15C
    rw [Finset.mem_range] at hk
    interval_cases k
    · rw [pow_zero] at hkz
      exact absurd hkz.symm hg151
    · rw [pow_one] at hkz
      exact hkz.symm
  have : (⟨z, S.hzV_F4⟩ : V) = ⟨g15, hg15V⟩ := Subtype.ext hgz.symm
  rw [this, hg]

noncomputable def V₁_F4 : Subgroup G := pullSub S.Φ V1sub

noncomputable def V₂_F4 : Subgroup G := pullSub S.Φ V2sub

noncomputable def V₃_F4 : Subgroup G := pullSub S.Φ V3sub

theorem card_V₁_F4 : Nat.card S.V₁_F4 = 2 := by rw [V₁_F4, card_pullSub, card_V1sub]

theorem card_V₂_F4 : Nat.card S.V₂_F4 = 4 := by rw [V₂_F4, card_pullSub, card_V2sub]

theorem card_V₃_F4 : Nat.card S.V₃_F4 = 8 := by rw [V₃_F4, card_pullSub, card_V3sub]

theorem z_mem_V₁_F4
    : z ∈ S.V₁_F4 := mem_pullSub.2 ⟨S.hzV_F4, by rw [S.phi_z_F4]; exact vecOf_fifteen_mem_V1sub⟩

theorem V₁_eq_F4 :
    S.V₁_F4 = zpowers z := by
  refine (Subgroup.eq_of_le_of_card_ge (zpowers_le.2 S.z_mem_V₁_F4) ?_).symm
  rw [S.card_V₁_F4, Nat.card_zpowers, S.hz2_F4]

theorem le12_F4 : S.V₁_F4 ≤ S.V₂_F4 := pullSub_mono V1sub_le_V2sub

theorem le23_F4 : S.V₂_F4 ≤ S.V₃_F4 := pullSub_mono V2sub_le_V3sub

theorem le3_F4 : S.V₃_F4 ≤ V := pullSub_le _

noncomputable def H_F4 : Subgroup G := centralizer (S.V₁_F4 : Set G)

theorem H_eq_F4 :
    S.H_F4 = centralizer ({z} : Set G) := by
  rw [H_F4, V₁_eq_F4, zpowers_eq_closure, centralizer_closure]

theorem mem_H_iff_F4
    {n : G} (hn : n ∈ normalizer (V : Set G)) {k : GL (Fin 6) (ZMod 2)}
    (hk : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨n, hn⟩) = glLin k) :
    n ∈ S.H_F4 ↔ glLin k (vecOf 15) = vecOf 15 := by
  rw [H_eq_F4, mem_centralizer_singleton_iff]
  have h1 := phi_conj' hn hk S.hzV_F4
  rw [S.phi_z_F4] at h1
  constructor
  · intro h
    have h2 : n * z * n⁻¹ = z := by rw [h, mul_inv_cancel_right]
    rw [← h1, ← S.phi_z_F4]
    congr 2
    exact Subtype.ext h2
  · intro h
    have h2 := phi_injective' _ S.hzV_F4 (h1.trans (h.trans S.phi_z_F4.symm))
    calc n * z = n * z * n⁻¹ * n := by group
      _ = z * n := by rw [h2]

theorem V₁_le_V₃_F4 : S.V₁_F4 ≤ S.V₃_F4 := S.le12_F4.trans S.le23_F4

theorem exists_lift_F4 {j : GL (Fin 6) (ZMod 2)} (hj : j ∈ J6) :
    ∃ l ∈ L, ∃ hl : l ∈ normalizer (V : Set G),
      linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l, hl⟩) = glLin j := by
  obtain ⟨l, hl, hlj⟩ := S.hLs j hj
  exact ⟨l, hl, S.hLV_F4 hl, hlj⟩

noncomputable def l₁ : G := (S.exists_lift_F4 xGL_mem).choose

theorem l₁_mem_F4 : S.l₁ ∈ L := (S.exists_lift_F4 xGL_mem).choose_spec.1

theorem l₁_N_F4 : S.l₁ ∈ normalizer (V : Set G) := (S.exists_lift_F4 xGL_mem).choose_spec.2.choose

theorem l₁_spec_F4 : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨S.l₁, S.l₁_N_F4⟩) =
    glLin xGL := (S.exists_lift_F4 xGL_mem).choose_spec.2.choose_spec

theorem l₁_H_F4
    : S.l₁ ∈ S.H_F4 := (S.mem_H_iff_F4 S.l₁_N_F4 S.l₁_spec_F4).2 xGL_fix

theorem normalizer_V₁_F4 : normalizer (S.V₁_F4 : Set G) = S.H_F4 :=
  normalizer_eq_centralizer_of_card_eq_two S.card_V₁_F4

theorem T_le_H_F4 : T ≤ S.H_F4 := by
  rw [H_eq_F4]
  intro t ht
  exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 S.hzVT_F4.2) t ht)

theorem T_le_N_V₁_F4 :
    T ≤ normalizer (S.V₁_F4 : Set G) := by
  rw [S.normalizer_V₁_F4]
  exact S.T_le_H_F4

theorem L₁T_le_H_F4 :
    L₁Of L S.V₁_F4 ⊔ T ≤ S.H_F4 := by
  refine sup_le ((oTwoRes_le (L ⊓ normalizer (S.V₁_F4 : Set G))).trans ?_) S.T_le_H_F4
  rw [← S.normalizer_V₁_F4]
  exact inf_le_right

theorem uniqueM_F4 : IsUniqueM (L ⊔ T) (normalizer (L : Set G)) := by
  obtain ⟨-, -, -, ⟨hMmax, hLT, huniq⟩, -⟩ :=
    u3_original_local_maximality_and_unique_normalizer_of_1332_F4 S.h1332 S.hH
  exact ⟨⟨hMmax, hLT⟩, fun M' hM' => huniq M' hM'.1 hM'.2⟩

theorem pCoreOf_L_le_F4 : pCoreOf 2 L ≤ T ⊓ centralizer (V : Set G) := by
  rw [S.hF.2.2.2.2.2.2.2.2.2.2.1]
  exact A6.pCoreOf_le_pCoreOf_sup S.hTL_F4

theorem isSimple_quot_F4 : IsSimpleGroup (↥L ⧸ CFSG.pCore 2 ↥L) := by
  obtain ⟨e1⟩ := CFSG.Timmesfeld.nonempty_mulEquiv_PSU3_of_lieModel S.hU3
  obtain ⟨e2⟩ := u33Pres_mulEquiv_PSU3
  have : IsSimpleGroup U33G := isSimpleGroup_u33Pres
  exact (MulEquiv.isSimpleGroup_congr (e1.trans e2.symm)).2 this

theorem inf_centralizer_le_F4 : L ⊓ centralizer (V : Set G) ≤ pCoreOf 2 L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsimp := S.isSimple_quot_F4
  set K : Subgroup ↥L := (centralizer (V : Set G)).subgroupOf L with hK
  have hKn : K.Normal := by
    constructor
    intro k hk l
    rw [mem_subgroupOf] at hk ⊢
    exact (mem_normalizer_iff.1 (normalizer_le_normalizer_centralizer V (S.hLV_F4 l.2)) k).1 hk
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  have hmapn : (K.map π).Normal := hKn.map π (QuotientGroup.mk'_surjective _)
  have hO2C : ∀ o : ↥L, o ∈ CFSG.pCore 2 ↥L → (o : G) ∈ centralizer (V : Set G) := fun o ho =>
    (S.pCoreOf_L_le_F4 ⟨o, mem_open_pCore_of_mem_pCore ho, rfl⟩).2
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.map π) with h | h
  · rintro x ⟨hxL, hxC⟩
    have hxK : (⟨x, hxL⟩ : ↥L) ∈ K := hxC
    have h1 : π ⟨x, hxL⟩ ∈ K.map π := ⟨_, hxK, rfl⟩
    rw [h, mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨⟨x, hxL⟩, mem_open_pCore_of_mem_pCore h1, rfl⟩
  · exfalso
    obtain ⟨l, hl, v, hv, hlv⟩ := S.hF.2.2.2.2.2.2.2.2.2.1
    have h1 : π ⟨l, hl⟩ ∈ K.map π := h ▸ mem_top _
    obtain ⟨k, hk, hkl⟩ := h1
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkl
    have hkC : (k : G) ∈ centralizer (V : Set G) := hk
    have hoC := hO2C _ hkl
    have hlC : l ∈ centralizer (V : Set G) := by
      have := mul_mem hkC hoC
      rwa [show (k : G) * ((k⁻¹ * ⟨l, hl⟩ : ↥L) : G) = l by simp] at this
    exact hlv (by rw [← (mem_centralizer_iff.1 hlC) v hv, mul_inv_cancel_right])

theorem L₁T_normalizes_V₃_F4
    : L₁Of L S.V₁_F4 ⊔ T ≤ normalizer (S.V₃_F4 : Set G) := by
  refine sup_le ((oTwoRes_le (L ⊓ normalizer (S.V₁_F4 : Set G))).trans fun l ⟨hl, hlN⟩ => ?_)
    fun t ht => ?_
  · obtain ⟨j, hj, hlj⟩ := S.hL l hl
    rw [S.normalizer_V₁_F4] at hlN
    have hfix := (S.mem_H_iff_F4 (S.hLV_F4 hl) hlj).1 hlN
    exact mem_normalizer_pullSub (S.hLV_F4 hl) hlj (map_V3sub_of_fix (J6_le_N6 hj) hfix)
  · obtain ⟨s, hs, hst⟩ := S.hT t ht
    exact mem_normalizer_pullSub (S.hTV_F4 ht) hst (map_V3sub_of_mem_S0 hs)

theorem T_normalizes_V₂_F4 : T ≤ normalizer (S.V₂_F4 : Set G) := fun t ht => by
  obtain ⟨s, hs, hst⟩ := S.hT t ht
  exact mem_normalizer_pullSub (S.hTV_F4 ht) hst (map_V2sub_of_mem_S0 hs)

theorem T_normalizes_V₃_F4 :
    T ≤ normalizer (S.V₃_F4 : Set G) :=
  le_sup_right.trans S.L₁T_normalizes_V₃_F4

theorem irred_F4 :
    ∀ W : Subgroup G, S.V₁_F4 ≤ W → W ≤ S.V₃_F4 →
    L₁Of L S.V₁_F4 ⊔ T ≤ normalizer (W : Set G) → W = S.V₁_F4 ∨ W = S.V₃_F4 := by
  intro W h1 h3 hW
  have hWV : W ≤ V := h3.trans S.le3_F4

  have h0 : orderOf S.l₁ ≠ 0 := (orderOf_pos S.l₁).ne'
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd h0
  set l₀ := S.l₁ ^ 2 ^ a with hl₀
  have hl₀N : l₀ ∈ normalizer (V : Set G) := pow_mem S.l₁_N_F4 _
  have hl₀L : l₀ ∈ L ⊓ normalizer (S.V₁_F4 : Set G) := by
    rw [S.normalizer_V₁_F4]
    exact ⟨pow_mem S.l₁_mem_F4 _, pow_mem S.l₁_H_F4 _⟩
  have hl₀m : l₀ ^ m = 1 := by
    rw [hl₀, ← pow_mul, ← ham, pow_orderOf_eq_one]
  have hl₀W : l₀ ∈ normalizer (W : Set G) :=
    hW (le_sup_left (a := L₁Of L S.V₁_F4) (Subgroup.subset_closure ⟨hl₀L, m, hm, hl₀m⟩))
  have hspec : linConj S.Φ (u3ConjLin V (normalizer (V : Set G)) le_rfl ⟨l₀, hl₀N⟩) =
      glLin (xGL ^ 2 ^ a) := by
    rw [show (⟨l₀, hl₀N⟩ : normalizer (V : Set G)) = ⟨S.l₁, S.l₁_N_F4⟩ ^ 2 ^ a from rfl,
      map_pow (u3ConjLin V (normalizer (V : Set G)) le_rfl), map_pow (linConj S.Φ), S.l₁_spec_F4,
      map_pow glLin]
  have hinv := subSpace_invariant hl₀N hspec hl₀W
  have hx : ∀ w ∈ subSpace S.Φ W, glLin xGL w ∈ subSpace S.Φ W := by
    rcases xGL_pow_two_pow a with h | h
    · rw [h] at hinv
      exact hinv
    · rw [h] at hinv
      intro w hw
      have := hinv _ (hinv w hw)
      rwa [← LinearEquiv.mul_apply, ← map_mul, xGL_pow_four] at this
  have hX := pullSub_subSpace (Φ := S.Φ) hWV
  have hP1 : V1sub ≤ subSpace S.Φ W := pullSub_le_iff.1 (by rw [hX]; exact h1)
  have hP3 : subSpace S.Φ W ≤ V3sub := pullSub_le_iff.1 (by rw [hX]; exact h3)
  rcases eq_of_V1_le_le_V3 hP1 hP3 hx with h | h
  · left
    rw [← hX, h]
    rfl
  · right
    rw [← hX, h]
    rfl

theorem V₁_lt_V₃_F4 : S.V₁_F4 < S.V₃_F4 := by
  refine lt_of_le_of_ne S.V₁_le_V₃_F4 fun h => ?_
  have := S.card_V₁_F4
  rw [h, S.card_V₃_F4] at this
  norm_num at this

theorem isTwoReducedIn_F4 : IsTwoReducedIn (L ⊔ T) V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hLTN : L ⊔ T ≤ normalizer (V : Set G) := sup_le S.hLV_F4 S.hTV_F4
  have hLTL : L ⊔ T ≤ normalizer (L : Set G) := sup_le le_normalizer S.hTL_F4
  refine ⟨S.hVT_F4.trans le_sup_right, hLTN, isElemAbelian_of_isElementaryAbelian' V,
    fun D hD hDn hD2 => ?_⟩
  have hrhoL : ∀ {l : G} (hl : l ∈ L), S.rho_F4 ⟨l, S.hLV_F4 hl⟩ ∈ J6 := by
    intro l hl
    obtain ⟨j, hj, hlj⟩ := S.hL l hl
    rw [show S.rho_F4 ⟨l, S.hLV_F4 hl⟩ = j from glLin.injective (by rw [← S.rho_spec_F4, hlj])]
    exact hj
  have hrhoLs : ∀ j ∈ J6, ∃ (l : G) (hl : l ∈ L), S.rho_F4 ⟨l, S.hLV_F4 hl⟩ = j := by
    intro j hj
    obtain ⟨l, hl, hlj⟩ := S.hLs j hj
    exact ⟨l, hl, glLin.injective (by rw [← S.rho_spec_F4, hlj])⟩
  set N : Subgroup (GL (Fin 6) (ZMod 2)) :=
    (D.subgroupOf (normalizer (V : Set G))).map S.rho_F4 ⊓ J6 with hNdef
  have hN : N = ⊥ := by
    refine eq_bot_of_isPGroup_of_normal_J6 inf_le_right ?_ ?_
    · rintro ⟨n, ⟨d, hd, rfl⟩, -⟩
      obtain ⟨k, hk⟩ := hD2 d hd
      refine ⟨k, Subtype.ext ?_⟩
      have h1 := (mem_centralizer_V_iff (d ^ 2 ^ k).2 (S.rho_spec_F4 (d ^ 2 ^ k))).1 hk
      rw [map_pow] at h1
      simpa using h1
    · intro σ hσ n hn
      obtain ⟨⟨d, hd, rfl⟩, hnJ⟩ := mem_inf.1 hn
      obtain ⟨l, hl, rfl⟩ := hrhoLs σ hσ
      rw [SetLike.mem_coe, mem_subgroupOf] at hd
      refine mem_inf.2 ⟨⟨⟨l, S.hLV_F4 hl⟩ * d * ⟨l, S.hLV_F4 hl⟩⁻¹, ?_, by rw [map_mul, map_mul,
        map_inv]⟩, mul_mem (mul_mem (hrhoL hl) hnJ) (inv_mem (hrhoL hl))⟩
      rw [SetLike.mem_coe, mem_subgroupOf]
      exact (mem_normalizer_iff.1 (hDn (le_sup_left (b := T) hl)) d).1 hd
  intro d hd
  have hdN : d ∈ normalizer (V : Set G) := hLTN (hD hd)
  rw [mem_centralizer_V_iff hdN (S.rho_spec_F4 ⟨d, hdN⟩)]
  refine eq_one_of_commute_J6 fun j hj => ?_
  obtain ⟨l, hl, rfl⟩ := hrhoLs j hj
  set c : normalizer (V : Set G) :=
    ⟨d, hdN⟩ * ⟨l, S.hLV_F4 hl⟩ * ⟨d, hdN⟩⁻¹ * ⟨l, S.hLV_F4 hl⟩⁻¹ with hc
  have hcD : (c : G) ∈ D := by
    rw [hc]
    show d * l * d⁻¹ * l⁻¹ ∈ D
    rw [show d * l * d⁻¹ * l⁻¹ = d * (l * d⁻¹ * l⁻¹) by group]
    exact D.mul_mem hd ((mem_normalizer_iff.1 (hDn (le_sup_left (b := T) hl)) _).1
      (D.inv_mem hd))
  have hcL : (c : G) ∈ L := by
    rw [hc]
    show d * l * d⁻¹ * l⁻¹ ∈ L
    exact L.mul_mem ((mem_normalizer_iff.1 (hLTL (hD hd)) l).1 hl) (L.inv_mem hl)
  have hcN : S.rho_F4 c ∈ N := by
    refine mem_inf.2 ⟨⟨c, hcD, rfl⟩, ?_⟩
    have := hrhoL hcL
    exact this
  rw [hN, mem_bot, hc, map_mul, map_mul, map_mul, map_inv, map_inv] at hcN
  calc S.rho_F4 ⟨l, S.hLV_F4 hl⟩ * S.rho_F4 ⟨d, hdN⟩ =
      (S.rho_F4 ⟨d, hdN⟩ * S.rho_F4 ⟨l, S.hLV_F4 hl⟩ * (S.rho_F4 ⟨d, hdN⟩)⁻¹ *
        (S.rho_F4 ⟨l, S.hLV_F4 hl⟩)⁻¹)⁻¹ * (S.rho_F4 ⟨d, hdN⟩ * S.rho_F4 ⟨l, S.hLV_F4 hl⟩) := by group
    _ = S.rho_F4 ⟨d, hdN⟩ * S.rho_F4 ⟨l, S.hLV_F4 hl⟩ := by rw [hcN, inv_one, one_mul]

end HullSetting_F4

end CFSG.Quasithin.H13.U3
