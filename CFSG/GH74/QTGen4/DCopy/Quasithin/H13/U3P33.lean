module

public import CFSG.Quasithin.H13.U3P33
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3Hull
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L14Producers
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.U3L15U

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Quasithin.SteinbergCB
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G]

namespace HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting_F4
open CFSG.Quasithin.H13.U3.HullSetting

variable [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} [IsElementaryAbelian 2 V] {z : G}

theorem V₁_eq_pullSub_F4
    (S : HullSetting_F4 G T L V z) : S.V₁_F4 = pullSub S.Φ V1sub := by
  rw [S.V₁_eq_F4]
  refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 (mem_pullSub.2 ⟨S.hzV_F4, ?_⟩)) ?_
  · rw [S.phi_z_F4]
    exact vecOf_fifteen_mem_V1sub
  · rw [card_pullSub, card_V1sub, Nat.card_zpowers, S.hz2_F4]

theorem V₂_eq_pullSub_F4
    (S : HullSetting_F4 G T L V z) : S.V₂_F4 = pullSub S.Φ V2sub :=
  S.V2_eq_F4 S.isV2_F4

theorem V₃_eq_pullSub_F4
    (S : HullSetting_F4 G T L V z) : S.V₃_F4 = pullSub S.Φ V3sub :=
  S.V3_eq_F4 (by rw [← S.V₂_eq_pullSub_F4]; exact S.le23_F4) S.le3_F4 S.T_normalizes_V₃_F4 S.card_V₃_F4

theorem e18_mem_F4
    (S : HullSetting_F4 G T L V z) : elOf S.Φ (vecOf 18) ∈ S.V₃_F4 := by
  rw [S.V₃_eq_pullSub_F4]
  exact elOf_mem_pullSub.2 ((hasMask_V3sub' 18 (by norm_num)).2 (by decide))

theorem e53_mem_F4
    (S : HullSetting_F4 G T L V z) : elOf S.Φ (vecOf 53) ∈ S.V₂_F4 := by
  rw [S.V₂_eq_pullSub_F4]
  exact elOf_mem_pullSub.2 ((hasMask_V2sub 53 (by norm_num)).2 (by decide))

theorem isElemAbelian_V₃_F4
    (S : HullSetting_F4 G T L V z) : IsElemAbelian 2 S.V₃_F4 :=
  elemAb_of_le (isElemAbelian_of_isElementaryAbelian' V) S.le3_F4

theorem inf_le_nX_F4
    (S : HullSetting_F4 G T L V z) : L ⊓ normalizer (S.V₁_F4 : Set G) ≤ U3P33.nX S.V₃_F4 S.V₁_F4 := by
  rintro l ⟨hl, hlN⟩
  refine ⟨?_, hlN⟩
  obtain ⟨j, hj, hlj⟩ := S.hL l hl
  have hlH : l ∈ S.H_F4 := by
    rw [← S.normalizer_V₁_F4]
    exact hlN
  have hfix := (S.mem_H_iff_F4 (S.hLV_F4 hl) hlj).1 hlH
  rw [S.V₃_eq_pullSub_F4]
  exact mem_normalizer_pullSub (S.hLV_F4 hl) hlj (map_V3sub_of_fix (J6_le_N6 hj) hfix)

theorem T_le_nX_F4
    (S : HullSetting_F4 G T L V z) : T ≤ U3P33.nX S.V₃_F4 S.V₁_F4 := fun _ ht =>
  ⟨S.T_normalizes_V₃_F4 ht, S.T_le_N_V₁_F4 ht⟩

theorem T_le_N_L₁_F4
    (S : HullSetting_F4 G T L V z) : T ≤ normalizer (L₁Of L S.V₁_F4 : Set G) := by
  rw [← lOne_eq_L₁Of]
  exact le_normalizer_lOne S.hTL_F4 S.T_le_N_V₁_F4

theorem isPGroup_sup_inf_centralizer_F4
    (S : HullSetting_F4 G T L V z) : IsPGroup 2 ↥((L ⊔ T) ⊓ centralizer (S.V₃_F4 : Set G)) := by
  have h23 : pullSub S.Φ V2sub ≤ S.V₃_F4 := by
    rw [← S.V₂_eq_pullSub_F4]
    exact S.le23_F4
  refine isPGroup_two_of_forall' fun c hc => ?_
  obtain ⟨k, hk⟩ := exists_pow_two_pow_mem_of_mem_sup S.hH.sylow.1 S.hTL_F4 hc.1
  have hmem : c ^ 2 ^ k ∈ L ⊓ centralizer (pullSub S.Φ V2sub : Set G) :=
    ⟨hk, Subgroup.centralizer_le h23 (pow_mem hc.2 _)⟩
  obtain ⟨m, hm⟩ := exists_two_pow_eq_one S.isPGroup_CL_V2_F4 hmem
  exact ⟨k + m, by rw [pow_add, pow_mul, hm]⟩

theorem isPGroup_L₁_sup_inf_F4
    (S : HullSetting_F4 G T L V z) :
    IsPGroup 2 ↥((L₁Of L S.V₁_F4 ⊔ T) ⊓ centralizer (S.V₃_F4 : Set G)) :=
  S.isPGroup_sup_inf_centralizer_F4.to_le
    (inf_le_inf_right _ (sup_le_sup_right ((oTwoRes_le _).trans inf_le_left) T))

theorem isPGroup_L₁_inf_F4
    (S : HullSetting_F4 G T L V z) : IsPGroup 2 ↥(L₁Of L S.V₁_F4 ⊓ centralizer (S.V₃_F4 : Set G)) :=
  S.isPGroup_L₁_sup_inf_F4.to_le (inf_le_inf_right _ le_sup_left)

theorem exists_c_F4
    (S : HullSetting_F4 G T L V z) :
    ∃ c ∈ L₁Of L S.V₁_F4, ∃ hc : c ∈ normalizer (V : Set G), ∃ e ∈ xCodes,
      ((S.rho_F4 ⟨c, hc⟩ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e.1 ∧
        (((S.rho_F4 ⟨c, hc⟩)⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
          colMat e.2 := by
  obtain ⟨a, m, hm, ham⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos S.l₁).ne'
  have hl₀L : S.l₁ ^ 2 ^ a ∈ L ⊓ normalizer (S.V₁_F4 : Set G) := by
    rw [S.normalizer_V₁_F4]
    exact ⟨pow_mem S.l₁_mem_F4 _, pow_mem S.l₁_H_F4 _⟩
  have hl₀m : (S.l₁ ^ 2 ^ a) ^ m = 1 := by
    rw [← pow_mul, ← ham, pow_orderOf_eq_one]
  have hX : S.rho_F4 ⟨S.l₁ ^ 2 ^ a, pow_mem S.l₁_N_F4 _⟩ = xGL ∨
      S.rho_F4 ⟨S.l₁ ^ 2 ^ a, pow_mem S.l₁_N_F4 _⟩ = xGL * xGL := by
    rw [S.rho_pow_F4 S.l₁_N_F4, S.rho_eq_of_spec_F4 _ S.l₁_spec_F4]
    exact xGL_pow_two_pow a
  obtain ⟨e, he, h1, h2⟩ := exists_xCode hX
  exact ⟨S.l₁ ^ 2 ^ a, subset_closure ⟨hl₀L, m, hm, hl₀m⟩, pow_mem S.l₁_N_F4 _, e, he, h1, h2⟩

theorem not_mem_trivSub_F4
    (S : HullSetting_F4 G T L V z) {n : G} (hn : n ∈ normalizer (V : Set G)) {e : List ℕ}
    (he : ((S.rho_F4 ⟨n, hn⟩ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat e)
    (hlt : vapp e 18 < 64) (hbit : v1mask.testBit (vapp e 18 ^^^ 18) = false) :
    n ∉ L32NSet14.trivSub S.V₃_F4 S.V₁_F4 := by
  intro h
  have h1 := h.2.2 _ S.e18_mem_F4
  rw [S.V₁_eq_pullSub_F4, conj_comm_mem_pullSub hn (S.rho_spec_F4 ⟨n, hn⟩) (elOf_mem (Φ := S.Φ) _),
    phi_elOf, glLin_vecOf_sub he,
    hasMask_V1sub _ (Nat.xor_lt_two_pow (n := 6) hlt (by norm_num)), hbit] at h1
  exact Bool.false_ne_true h1

theorem exists_T_not_triv_F4
    (S : HullSetting_F4 G T L V z) : ∃ t ∈ T, t ∉ L32NSet14.trivSub S.V₃_F4 S.V₁_F4 := by
  obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho_F4 (u6GL_mem_rhoT (i := 2) (by simp))
  have hu : ((u6GL 2 : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) = colMat (u6c 2) :=
    rfl
  exact ⟨t, htTL.1, S.not_mem_trivSub_F4 ht (hrho ▸ hu) (vapp_u6c_lt 2 18) sy_codes.1⟩

theorem gen3_F4
    (S : HullSetting_F4 G T L V z) : conjClosure S.V₂_F4 (L₁Of L S.V₁_F4) = S.V₃_F4 := by
  obtain ⟨c, hcL, hc, e, he, hX, -⟩ := S.exists_c_F4
  obtain ⟨-, h53, -, hb53, -⟩ := xCodes_spec e he
  have hLN : L₁Of L S.V₁_F4 ≤ normalizer (S.V₃_F4 : Set G) := le_sup_left.trans S.L₁T_normalizes_V₃_F4
  have hV₂W : S.V₂_F4 ≤ conjClosure S.V₂_F4 (L₁Of L S.V₁_F4) := le_conjClosure _ _
  have hWV : conjClosure S.V₂_F4 (L₁Of L S.V₁_F4) ≤ S.V₃_F4 := conjClosure_le fun h hh v hv =>
    (mem_normalizer_iff.mp (hLN hh) v).mp (S.le23_F4 hv)
  have hbW : c * elOf S.Φ (vecOf 53) * c⁻¹ ∈ conjClosure S.V₂_F4 (L₁Of L S.V₁_F4) :=
    mem_conjClosure hcL S.e53_mem_F4
  have hbV : c * elOf S.Φ (vecOf 53) * c⁻¹ ∉ S.V₂_F4 := by
    rw [S.V₂_eq_pullSub_F4, conj_mem_pullSub hc (S.rho_spec_F4 ⟨c, hc⟩) (elOf_mem (Φ := S.Φ) _),
      phi_elOf, glLin_vecOf hX, hasMask_V2sub _ h53, hb53]
    exact Bool.false_ne_true
  have h1 := Subgroup.card_dvd_of_le hV₂W
  have h2 := Subgroup.card_dvd_of_le hWV
  rw [S.card_V₂_F4] at h1
  rw [S.card_V₃_F4] at h2
  have hne : Nat.card (conjClosure S.V₂_F4 (L₁Of L S.V₁_F4)) ≠ 4 := fun h => hbV (by
    rw [Subgroup.eq_of_le_of_card_ge hV₂W (by rw [h, S.card_V₂_F4])]
    exact hbW)
  have h8 : Nat.card (conjClosure S.V₂_F4 (L₁Of L S.V₁_F4)) = 8 := by
    have hpos : 0 < Nat.card (conjClosure S.V₂_F4 (L₁Of L S.V₁_F4)) := Nat.card_pos
    have hle : Nat.card (conjClosure S.V₂_F4 (L₁Of L S.V₁_F4)) ≤ 8 := Nat.le_of_dvd (by norm_num) h2
    obtain ⟨d, hd⟩ := h1
    rw [hd] at hle hpos hne ⊢
    have hd2 : d ≤ 2 := by omega
    have hd0 : 0 < d := by omega
    interval_cases d <;> omega
  exact Subgroup.eq_of_le_of_card_ge hWV (by rw [S.card_V₃_F4, h8])

theorem comm3_F4
    (S : HullSetting_F4 G T L V z) : ⁅S.V₃_F4, pCoreOf 2 (L₁Of L S.V₁_F4)⁆ = S.V₁_F4 := by
  have hW := S.isElemAbelian_V₃_F4
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro v hv q hq
    have hq' := (U3P33.pCoreOf_le_trivSub hW S.card_V₃_F4 S.card_V₁_F4 S.V₁_le_V₃_F4 S.inf_le_nX_F4 hq).2.2
      v hv
    have e : ⁅v, q⁆ = (q * v * q⁻¹ * v⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact inv_mem hq'
  · obtain ⟨c, hcL, hc, e, he, hX, hXi⟩ := S.exists_c_F4
    obtain ⟨-, -, -, -, h29⟩ := xCodes_spec e he
    obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho_F4 (u6GL_mem_rhoT (i := 0) (by simp))
    have hct : t * c * t⁻¹ ∈ L₁Of L S.V₁_F4 :=
      (mem_normalizer_iff.mp (S.T_le_N_L₁_F4 htTL.1) c).mp hcL
    set k := c * (t * c * t⁻¹) * c⁻¹ * (t * c * t⁻¹)⁻¹ with hk
    have hkQ : k ∈ pCoreOf 2 (L₁Of L S.V₁_F4) :=
      U3P33.commutator_mem_pCoreOf hW S.card_V₃_F4 S.card_V₁_F4 S.V₁_le_V₃_F4 S.inf_le_nX_F4
        S.isPGroup_L₁_inf_F4 hcL hct
    have hkN : k ∈ normalizer (V : Set G) :=
      mul_mem (mul_mem (mul_mem hc (mul_mem (mul_mem ht hc) (inv_mem ht))) (inv_mem hc))
        (inv_mem (mul_mem (mul_mem ht hc) (inv_mem ht)))

    have hA : ((u6GL 0 : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        colMat (u6c 0) := rfl
    have hAi : (((u6GL 0)⁻¹ : GL (Fin 6) (ZMod 2)) : Matrix (Fin 6) (Fin 6) (ZMod 2)) =
        colMat (u6ci 0) := rfl
    have e1 : (⟨k, hkN⟩ : normalizer (V : Set G)) = ⟨c, hc⟩ * (⟨t, ht⟩ * ⟨c, hc⟩ * ⟨t, ht⟩⁻¹) *
        ⟨c, hc⟩⁻¹ * (⟨t, ht⟩ * ⟨c, hc⟩ * ⟨t, ht⟩⁻¹)⁻¹ := rfl
    have e2 : S.rho_F4 ⟨k, hkN⟩ = S.rho_F4 ⟨c, hc⟩ * u6GL 0 * S.rho_F4 ⟨c, hc⟩ * (u6GL 0)⁻¹ *
        (S.rho_F4 ⟨c, hc⟩)⁻¹ * u6GL 0 * (S.rho_F4 ⟨c, hc⟩)⁻¹ * (u6GL 0)⁻¹ := by
      rw [e1]
      simp only [map_mul, map_inv, hrho]
      group
    have hk18 : glLin (S.rho_F4 ⟨k, hkN⟩) (vecOf 18) = vecOf 29 := by
      rw [e2]
      simp only [map_mul, LinearEquiv.mul_apply]
      rw [glLin_vecOf hAi, glLin_vecOf hXi, glLin_vecOf hA, glLin_vecOf hXi, glLin_vecOf hAi,
        glLin_vecOf hX, glLin_vecOf hA, glLin_vecOf hX, h29]
    have h15 : (18 : ℕ) ^^^ 15 = 29 := by decide
    have hkv : k * elOf S.Φ (vecOf 18) * k⁻¹ = elOf S.Φ (vecOf 18) * z := by
      refine phi_injective' (Φ := S.Φ) ((mem_normalizer_iff.1 hkN _).1 (elOf_mem _))
        (mul_mem (elOf_mem _) S.hzV_F4) ?_
      rw [phi_conj' hkN (S.rho_spec_F4 ⟨k, hkN⟩) (elOf_mem _), phi_elOf, hk18,
        phi_mul' (elOf_mem _) S.hzV_F4, phi_elOf, S.phi_z_F4, ← vecOf_xor, h15]
    have hcomm : ⁅k, elOf S.Φ (vecOf 18)⁆ = z := by
      rw [commutatorElement_def, hkv,
        elemAb_comm (isElemAbelian_of_isElementaryAbelian' V) (elOf_mem _) S.hzV_F4]
      group
    have hz : z ∈ ⁅S.V₃_F4, pCoreOf 2 (L₁Of L S.V₁_F4)⁆ := by
      have h1 := Subgroup.commutator_mem_commutator hkQ S.e18_mem_F4
      rw [Subgroup.commutator_comm, hcomm] at h1
      exact h1
    calc S.V₁_F4 = zpowers z := S.V₁_eq_F4
      _ ≤ ⁅S.V₃_F4, pCoreOf 2 (L₁Of L S.V₁_F4)⁆ := zpowers_le.2 hz

theorem Lp3_F4
    (S : HullSetting_F4 G T L V z) : (pCoreOf 2 (L₁Of L S.V₁_F4)).relIndex (L₁Of L S.V₁_F4) = 3 := by
  obtain ⟨c, hcL, hc, e, he, hX, -⟩ := S.exists_c_F4
  obtain ⟨h18, -, hb18, -, -⟩ := xCodes_spec e he
  exact U3P33.relIndex_eq_three S.isElemAbelian_V₃_F4 S.card_V₃_F4 S.card_V₁_F4 S.V₁_le_V₃_F4 S.inf_le_nX_F4
    S.isPGroup_L₁_inf_F4 hcL (S.not_mem_trivSub_F4 hc hX h18 hb18)

theorem index2_F4
    (S : HullSetting_F4 G T L V z) : (pCoreOf 2 (L₁Of L S.V₁_F4 ⊔ T)).relIndex T = 2 := by
  obtain ⟨c, hcL, hc, e, he, hX, -⟩ := S.exists_c_F4
  obtain ⟨h18, -, hb18, -, -⟩ := xCodes_spec e he
  obtain ⟨t, ht, htn⟩ := S.exists_T_not_triv_F4
  exact U3P33.relIndex_eq_two S.isElemAbelian_V₃_F4 S.card_V₃_F4 S.card_V₁_F4 S.V₁_le_V₃_F4 S.inf_le_nX_F4
    S.T_le_nX_F4 S.hH.sylow.1 S.isPGroup_L₁_sup_inf_F4 hcL (S.not_mem_trivSub_F4 hc hX h18 hb18) ht htn

theorem irredOn_F4
    (S : HullSetting_F4 G T L V z) : IsIrredOnSection (L₁Of L S.V₁_F4 ⊔ T) S.V₃_F4 S.V₁_F4 :=
  ⟨S.V₁_lt_V₃_F4, S.L₁T_normalizes_V₃_F4, sup_le ((oTwoRes_le _).trans inf_le_right) S.T_le_N_V₁_F4,
    S.irred_F4⟩

theorem cv3_F4
    (S : HullSetting_F4 G T L V z) : ∀ y ∈ normalizer (V : Set G) ⊓ centralizer (S.V₃_F4 : Set G),
      Odd (orderOf y) → y ∈ centralizer (V : Set G) := by
  rintro y ⟨hyN, hyC⟩ hodd
  have hk := S.rho_spec_F4 ⟨y, hyN⟩
  rw [S.V₃_eq_pullSub_F4] at hyC
  have hfix := (mem_centralizer_pullSub_iff hyN hk V3sub).1 hyC
  have hsq := sq_eq_one_of_fixes (S.rho_mem_N6_F4 _) hfix
  rw [mem_centralizer_V_iff hyN hk]
  have h1 : S.rho_F4 ⟨y, hyN⟩ ^ orderOf y = 1 := by
    rw [← map_pow]
    have : (⟨y, hyN⟩ : normalizer (V : Set G)) ^ orderOf y = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow]; exact pow_orderOf_eq_one y)
    rw [this, map_one]
  obtain ⟨j, hj⟩ := hodd
  rw [hj, pow_succ, pow_mul, pow_two, hsq, one_pow, one_mul] at h1
  exact h1

theorem bcase_F4
    (S : HullSetting_F4 G T L V z) (hNL : U3NondegLineCentralizer_F4) :
    ∃ g ∈ L ⊓ normalizer (S.V₂_F4 : Set G), g ^ 3 = 1 ∧ g ∉ normalizer (S.V₁_F4 : Set G) ∧
      centralizer ((S.V₃_F4 ⊔ S.V₃_F4.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ≤
        normalizer (L : Set G) := by
  obtain ⟨g, hgX, hg3, -, hgN, hρg⟩ := S.exists_X_elem_F4
  rw [← S.V₂_eq_pullSub_F4] at hgX
  refine ⟨g, oTwoRes_le _ hgX, hg3, ?_, ?_⟩
  · rw [S.normalizer_V₁_F4, S.mem_H_iff_F4 hgN (S.rho_spec_F4 ⟨g, hgN⟩)]
    rcases hρg with h | h
    · rw [h, glLin_vecOf coe_yGL]
      intro h'
      exact cert_y.2 (vecOf_injective (vapp_u6c_lt 4 15) (by norm_num) h')
    · rw [h, map_mul, LinearEquiv.mul_apply, glLin_vecOf coe_yGL, glLin_vecOf coe_yGL]
      intro h'
      exact sy_codes.2.1 (vecOf_injective (vapp_u6c_lt 4 _) (by norm_num) h')
  · set Γ := (u3ConjLin V (normalizer (V : Set G)) le_rfl).range
    have hle : Γ.map (linConj S.Φ).toMonoidHom ≤ N6L := by
      rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
      obtain ⟨k, hk, hkn⟩ := S.hN n
      exact ⟨k, hk, by rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, hkn]⟩
    have hprof := qtBinarySixProfile_of_map_linConj S.Φ b0 Γ (qtBinarySixProfile_of_le_N6L hle)
    have hu : elOf S.Φ (vecOf 18) ∈ V := elOf_mem _
    have hv : g * elOf S.Φ (vecOf 18) * g⁻¹ ∈ V := (mem_normalizer_iff.1 hgN _).1 hu
    have hC := hNL G T L V z S.hH S.hU3 S.hF _ hprof.2.1 hprof.2.2.1
      (fun n x y => hprof.2.2.2.1 _ ⟨n, rfl⟩ x y) _ _ hu hv (by
        rw [LinearMap.compl₁₂_apply]
        simp only [LinearEquiv.coe_coe]
        rw [phi_elOf, phi_conj' hgN (S.rho_spec_F4 ⟨g, hgN⟩) hu, phi_elOf]
        rcases hρg with h | h
        · rw [h, glLin_vecOf coe_yGL, b0_vecOf, sy_codes.2.2.1]
          decide
        · rw [h, map_mul, LinearEquiv.mul_apply, glLin_vecOf coe_yGL, glLin_vecOf coe_yGL,
            b0_vecOf, sy_codes.2.2.2]
          decide)
    refine le_trans (Subgroup.centralizer_le ?_) hC
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact mem_sup_left S.e18_mem_F4
    · exact mem_sup_right ⟨_, S.e18_mem_F4, rfl⟩

theorem exists_inv_mul_mem_centralizer_F4
    (S : HullSetting_F4 G T L V z) {A : Subgroup G}
    (hTA : T ⊓ L ≤ A) (h1 : S.l₁ ∈ A)
    (hyA : ∃ x ∈ A, ∃ hx : x ∈ normalizer (V : Set G),
      S.rho_F4 ⟨x, hx⟩ = yGL ∨ S.rho_F4 ⟨x, hx⟩ = yGL * yGL) :
    ∀ l ∈ L, ∃ a ∈ A, a⁻¹ * l ∈ centralizer (V : Set G) := by
  set Ab : Subgroup (GL (Fin 6) (ZMod 2)) := (A.subgroupOf (normalizer (V : Set G))).map S.rho_F4
  have hmem : ∀ {a : G} (ha : a ∈ A) (haN : a ∈ normalizer (V : Set G)),
      S.rho_F4 ⟨a, haN⟩ ∈ Ab := fun ha haN => mem_map_of_mem _ (mem_subgroupOf.2 ha)
  have h012 : ∀ i ∈ ([0, 1, 2] : List (Fin 5)), u6GL i ∈ Ab := by
    intro i hi
    obtain ⟨t, htTL, ht, hrho⟩ := S.exists_T_rho_F4 (u6GL_mem_rhoT hi)
    rw [← hrho]
    exact hmem (hTA htTL) ht
  have h3 : u6GL 3 ∈ Ab := by
    rw [← xGL_eq_u6GL, ← S.rho_eq_of_spec_F4 _ S.l₁_spec_F4]
    exact hmem h1 S.l₁_N_F4
  have h4 : u6GL 4 ∈ Ab := by
    obtain ⟨x, hxA, hx, hrho⟩ := hyA
    have hx' := hmem hxA hx
    rw [← yGL_eq_u6GL]
    rcases hrho with h | h
    · rw [← h]
      exact hx'
    · rw [h] at hx'
      rw [← yGL_pow_four]
      exact mul_mem hx' hx'
  have hJ : J6 ≤ Ab := by
    rintro _ ⟨g, rfl⟩
    have hle : (⊤ : Subgroup U33G) ≤ Ab.comap rho6 := by
      rw [← u33Data.gen, closure_le]
      obtain ⟨ha, hb, hs, hx, hy⟩ := rho6_abs
      intro w hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with rfl | rfl | rfl | rfl | rfl
      · show rho6 u33Data.a ∈ Ab
        rw [ha]
        exact h012 0 (by simp)
      · show rho6 u33Data.b ∈ Ab
        rw [hb]
        exact h012 1 (by simp)
      · show rho6 u33Data.s ∈ Ab
        rw [hs]
        exact h012 2 (by simp)
      · show rho6 u33Data.x ∈ Ab
        rw [hx]
        exact h3
      · show rho6 u33Data.y ∈ Ab
        rw [hy]
        exact h4
    exact hle (mem_top g)
  intro l hlL
  have hlJ : S.rho_F4 ⟨l, S.hLV_F4 hlL⟩ ∈ Ab := hJ (S.rho_L_mem_F4 hlL)
  obtain ⟨⟨a, haN⟩, ha, hae⟩ := mem_map.1 hlJ
  refine ⟨a, mem_subgroupOf.1 ha, ?_⟩
  have h1' : S.rho_F4 ((⟨a, haN⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV_F4 hlL⟩) = 1 := by
    rw [map_mul, map_inv, hae, inv_mul_cancel]
  have h2 : (((⟨a, haN⟩ : normalizer (V : Set G))⁻¹ * ⟨l, S.hLV_F4 hlL⟩ :
      normalizer (V : Set G)) : G) ∈ centralizer (V : Set G) :=
    (mem_centralizer_V_iff _ (S.rho_spec_F4 _)).2 h1'
  exact h2

theorem genL_F4
    (S : HullSetting_F4 G T L V z) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) :
    L ≤ A6.g1 T V ⊔ L₁Of L V₂ := by
  obtain ⟨x, hxX, -, -, hx, hrho⟩ := S.exists_X_elem_F4
  rw [← S.V2_eq_F4 hV2] at hxX
  have hg1 : A6.g1 T V = S.H_F4 := S.g1_eq_H_F4
  intro l hl
  obtain ⟨a, ha, hal⟩ := S.exists_inv_mul_mem_centralizer_F4 (A := L₁Of L V₂ ⊔ L ⊓ S.H_F4)
    (fun t ht => mem_sup_right ⟨ht.2, S.T_le_H_F4 ht.1⟩) (mem_sup_right ⟨S.l₁_mem_F4, S.l₁_H_F4⟩)
    ⟨x, mem_sup_left hxX, hx, hrho⟩ l hl
  have haH : L₁Of L V₂ ⊔ L ⊓ S.H_F4 ≤ A6.g1 T V ⊔ L₁Of L V₂ := by
    rw [hg1]
    exact sup_le le_sup_right (inf_le_right.trans le_sup_left)
  have hcH : a⁻¹ * l ∈ A6.g1 T V := by
    rw [hg1, S.H_eq_F4]
    exact mem_centralizer_singleton_iff.2 ((mem_centralizer_iff.1 hal) z S.hzV_F4).symm
  have := mul_mem (haH ha) (mem_sup_left hcH : a⁻¹ * l ∈ A6.g1 T V ⊔ L₁Of L V₂)
  rwa [mul_inv_cancel_left] at this

theorem set14_F4
    (S : HullSetting_F4 G T L V z) (hNL : U3NondegLineCentralizer_F4) {V₂ : Subgroup G}
    (hV : IsIrrPlusIn L (reducedAggregate (L ⊔ T)) T V)
    (hZV : V ⊓ centralizer (L : Set G) = ⊥) (hV2 : A6.IsV2 T V V₂) :
    Set14 G T L V V₂ S.V₃_F4 (L₁Of L S.V₁_F4) := by
  have h1 := S.fsuV1_eq_V₁_F4
  have h22 : V₂ = S.V₂_F4 := (S.V2_eq_F4 hV2).trans S.V₂_eq_pullSub_F4.symm
  have h1332 := S.h1332 G T L S.hH L S.hH.faithful
  obtain ⟨g, hg, hg3, hg1, hgC⟩ := S.bcase_F4 hNL
  exact
  { h13 := S.hH
    irr := hV
    zv := hZV
    v2 := hV2
    card1 := by rw [h1]; exact S.card_V₁_F4
    le23 := by rw [h22]; exact S.le23_F4
    le3V := S.le3_F4
    T_V3 := S.T_normalizes_V₃_F4
    card3 := S.card_V₃_F4
    Lp_eq := (L32NSet14.oTwoUpper_oTwoRes _).symm
    Lp_L := (oTwoRes_le _).trans inf_le_left
    Lp_V1 := by rw [h1]; exact (oTwoRes_le _).trans inf_le_right
    T_Lp := S.T_le_N_L₁_F4
    gen := by rw [h22]; exact S.gen3_F4
    irred := by rw [h1]; exact S.irredOn_F4
    comm3 := by rw [h1]; exact S.comm3_F4
    index2 := S.index2_F4
    Lp3 := S.Lp3_F4
    Lp_def := ⟨fun h => absurd h (not_isHatA6_of_psu S.hU3), fun _ => by rw [h1]⟩
    cv3 := S.cv3_F4
    clv := S.inf_centralizer_le_F4.trans (pCoreOf_le_o2Z L)
    bcase := Or.inr ⟨g, by rw [h22]; exact hg, hg3, by rw [h1]; exact hg1, hgC⟩
    genL := S.genL_F4 hV2
    fsu := (h1332.2.2.1.2 V hV).2.2.1
    T_L := S.hTL_F4
    V_T := S.hVT_F4
    T_V := S.hTV_F4
    Mmax := h1332.2.1.2.2.1
    uniq := h1332.2.1.2.2.2
    ti := fun U H hU hUV hHU =>
      (u3_selected_local_normalizer_and_TI_of_1332_F4 S.h1332 S.hH S.hF).2.2.2.1 U hU hUV H hHU }

end HullSetting_F4

theorem set14ProducerU33_of_F4
    (h1332 : Stmt13_3_2_F4) (hNL : U3NondegLineCentralizer_F4) : Set14ProducerU33_F4 := by
  intro G _ _ T L V V₂ _ hH hV hZV hV2 hU3 _
  obtain ⟨z, hF⟩ := u3_frame_of_irrPlus_F4 h1332 hH hU3 hV
  have : IsElementaryAbelian 2 V := hF.2.2.1
  obtain ⟨Φ, hL, hLs, hN, hT⟩ := u3_six_module_transport_adapted_F4 h1332 hH hU3 hF
  let S : HullSetting_F4 G T L V z := ⟨h1332, hH, hU3, hF, Φ, hL, hLs, hN, hT⟩
  exact ⟨_, _, S.set14_F4 hNL hV hZV hV2⟩

end CFSG.Quasithin.H13.U3
