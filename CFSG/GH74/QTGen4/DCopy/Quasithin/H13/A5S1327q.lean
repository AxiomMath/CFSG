module

public import CFSG.Quasithin.H13.A5S1327q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327p

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem isXi_oTwoUpper_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    IsXi T (oTwoUpper H) ∧
      pCoreOf 2 (oTwoUpper H) = oTwoUpper H ⊓ Subgroup.centralizer (S.UH H : Set G) ∧
      (pCoreOf 2 (oTwoUpper H)).relIndex (oTwoUpper H) = 9 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h501 := S.hyp501
  have hTH : T ≤ H := hH.1.1
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hTH
  obtain ⟨hMP, -⟩ := h501.minParabolic_of_isHStar_F4 h331 hH
  have hF : CharTwo H := S.charTwo_of_inH hH.1
  obtain ⟨hUO, hUel, hUred⟩ : S.UH H ≤ pCoreOf 2 H ⊓ Subgroup.centralizer (pCoreOf 2 H : Set G) ∧
      IsElemAbelian 2 (S.UH H) ∧ IsTwoReducedIn H (S.UH H) :=
    conjClosure_isTwoReducedIn_of_charTwo hsyl hF le_rfl
  have hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p H ≤ 2 := by
    obtain ⟨-, hq⟩ := isSQTKSub_of_inH S.h13.qtke S.h13.simple S.h13.nonabelian hH.1
    intro p hp hp2
    have : Fact p.Prime := ⟨hp⟩
    have h1 := hq p hp hp2
    rwa [← pRank_top_subtype]
  have hJT := S.thompsonJ_not_le_centralizer_UH_F4 h331 h5172 hH hHZ
  have hC := S.centralizer_UH_le_pCoreOf_all_F4 h331 h1222 h5172 hH hHZ hsolv
  set U := S.UH H with hUdef
  set X := oTwoUpper H with hXdef
  have hHN : H ≤ Subgroup.normalizer (U : Set G) := hUred.2.1
  have hXH : X ≤ H := oTwoUpper_le H
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (U : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)

  obtain ⟨K₁, K₂, B⟩ := exists_twoBlocks hUel hMP hsolv hSQT hUred hJT hS3
  obtain ⟨y₁, hy₁, hy₁3, hy₁1⟩ := S1417.exists_orderThree B.nat₁
  obtain ⟨t, htT, ht⟩ := B.swap
  have hy₂ : t * y₁ * t⁻¹ ∈ K₂ := by
    rw [← ht, B1.mem_conjAut]
    simpa [mul_assoc] using hy₁
  have hy₂3 : (t * y₁ * t⁻¹) ^ 3 = 1 := by rw [conj_pow, hy₁3]; group
  have hy₂1 : t * y₁ * t⁻¹ ≠ 1 := fun h => hy₁1 (by
    have e : y₁ = t⁻¹ * (t * y₁ * t⁻¹) * t := by group
    rw [e, h]; group)
  obtain ⟨-, hsylJ⟩ := E2_3_two_sylow_of_isSolvable hUel hMP hsolv hSQT hUred hJT
  obtain ⟨s, hsT, hsK, hs2, hs1⟩ := B.exists_inv_mem_K1 hsylJ
  have hcard9 := B.card_autI_twoResidual hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  obtain ⟨hLcomm, hLcube⟩ := B.autI_twoResidual_comm_cube hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1
  rw [twoResidual_eq_oTwoUpper'] at hcard9 hLcomm hLcube

  have hO2X : pCoreOf 2 X = X ⊓ Subgroup.centralizer (U : Set G) := by
    apply le_antisymm
    · refine le_inf (pCoreOf_le 2 X) ?_
      refine le_trans ?_ hO2U
      exact le_pCoreOf_of_le_normalizer ((pCoreOf_le 2 X).trans hXH)
        ((le_normalizer_oTwoUpper H).trans (normalizer_le_normalizer_pCoreOf 2 X))
        (pCoreOf_isPGroup 2 X)
    · refine le_pCoreOf_of_le_normalizer inf_le_left ?_
        ((pCoreOf_isPGroup 2 H).to_le (le_trans (inf_le_inf_left _ le_rfl) ?_))
      · intro x hx
        exact Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, B6.le_normalizer_centralizer hHN (hXH hx)⟩
      · exact fun g hg => hC ⟨hXH hg.1, hg.2⟩
  have hXN : X ≤ Subgroup.normalizer (U : Set G) := hXH.trans hHN
  have hidx : (pCoreOf 2 X).relIndex X = 9 := by
    rw [hO2X, ← hcard9]
    exact (card_autI_eq hUel hXN).symm
  refine ⟨⟨(oTwoUpper_oTwoUpper H).symm, hTH.trans (le_normalizer_oTwoUpper H), ?_, 3,
    Nat.prime_three, by norm_num, ?_, Or.inl ?_, ?_⟩, hO2X, hidx⟩
  ·
    rw [hXdef, ← eq_oTwoUpper_sup_of_isSylowTwoOf' hsyl]
    exact hH.1.2
  ·
    intro x hx
    rw [hO2X]
    refine ⟨X.pow_mem hx 3, ?_⟩
    have h1 : convI hUel ⟨x ^ 3, hXN (X.pow_mem hx 3)⟩ = 1 := by
      have e : (⟨x ^ 3, hXN (X.pow_mem hx 3)⟩ : ↥(Subgroup.normalizer (U : Set G))) =
          ⟨x, hXN hx⟩ ^ 3 := rfl
      rw [e, map_pow]
      exact hLcube _ (convI_mem_autI hUel hx (hXN hx))
    exact (convI_eq_one_iff hUel _).1 h1
  · exact hidx
  ·
    intro Y hY1 hY2 hTY

    have hcomm : ⁅X, X⁆ ≤ pCoreOf 2 X := by
      rw [hO2X, Subgroup.commutator_le]
      intro u hu v hv
      refine ⟨X.mul_mem (X.mul_mem (X.mul_mem hu hv) (X.inv_mem hu)) (X.inv_mem hv), ?_⟩
      have h1 : convI hUel (⟨u, hXN hu⟩ * ⟨v, hXN hv⟩ * (⟨u, hXN hu⟩)⁻¹ * (⟨v, hXN hv⟩)⁻¹) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv,
          hLcomm _ (convI_mem_autI hUel hu (hXN hu)) _ (convI_mem_autI hUel hv (hXN hv))]
        group
      exact (convI_eq_one_iff hUel _).1 h1
    rw [sup_eq_right.mpr hcomm] at hY1 ⊢

    have hYs : autI hUel Y ≤ autI hUel X := autI_mono hUel hY2
    have hTYs : autI hUel T ≤
        Subgroup.normalizer ((autI hUel Y : Subgroup _) : Set (MulAut (IntMod U hUel))) :=
      autI_le_normalizer hUel hTY
    by_cases hY : autI hUel Y = ⊥
    · left
      refine le_antisymm ?_ hY1
      rw [hO2X]
      exact le_inf hY2 ((autI_eq_bot_iff hUel (hY2.trans hXN)).1 hY)
    · right
      have hX' : autI hUel (twoResidual H) = autI hUel X := by rw [twoResidual_eq_oTwoUpper']
      have hYeq := B.eq_of_normalized hy₁ hy₁3 hy₁1 hy₂ hy₂3 hy₂1 hsT hsK hs2 hs1 htT ht
        (hX' ▸ hYs) hY hTYs
      rw [hX'] at hYeq
      refine le_antisymm hY2 fun x hx => ?_
      have h1 : convI hUel ⟨x, hXN hx⟩ ∈ autI hUel Y := by
        rw [hYeq]; exact convI_mem_autI hUel hx (hXN hx)
      obtain ⟨y, hyY, hy⟩ := (mem_autI hUel).1 h1
      have h2 : (y : G)⁻¹ * x ∈ pCoreOf 2 X := by
        rw [hO2X]
        refine ⟨X.mul_mem (X.inv_mem (hY2 hyY)) hx, ?_⟩
        have h3 : convI hUel (y⁻¹ * ⟨x, hXN hx⟩) = 1 := by
          rw [map_mul, map_inv, hy, inv_mul_cancel]
        exact (convI_eq_one_iff hUel _).1 h3
      have := Y.mul_mem hyY (hY1 h2)
      simpa using this

theorem isXiStar_oTwoUpper_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    (h5172 : Stmt5_1_7_two_F4) (h1332 : Stmt13_3_2_F4) {H : Subgroup G}
    (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : ¬ Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    IsXiStar T (oTwoUpper H) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hXi, -, hidx⟩ := S.isXi_oTwoUpper_F4 h331 h1222 h5172 hH hHZ hsolv hS3
  refine ⟨hXi, fun L' hL' _ hle => ?_⟩
  have hTH : T ≤ H := hH.1.1
  set X := oTwoUpper H with hXdef

  have hZL' : ⁅quasithinOmegaOneCenter T, L'⁆ ≠ ⊥ := by
    intro hbot
    apply hHZ
    rw [eq_oTwoUpper_sup_of_isSylowTwoOf' (isSylowTwoOf_of_le S.h13.sylow hTH)]
    refine (sup_le le_sup_left le_sup_right).trans (hle.trans (sup_le ?_ ?_))
    · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact hbot)
    · exact T_le_centralizer_omegaOneCenter T
  have hf := Vol2.Ch11.SecS.isFaithfulLocal_of_omegaOneCenter S.h13.qtke S.h13.sylow hL' hZL'
  have hTL' : T ≤ Subgroup.normalizer (L' : Set G) := (h1332 G T L S.h13 L' hf).2.1.1
  have h60 := relIndex_pCoreOf_of_A5 (S.h13.a5 S.a5 L' hf)

  have hXL' : X ≤ L' := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    have hxLT : x ∈ L' ⊔ T := hle (Subgroup.mem_sup_left (Subgroup.subset_closure hx))
    have hxLT' : x ∈ ((L' ⊔ T : Subgroup G) : Set G) := hxLT
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L' T hTL'] at hxLT'
    obtain ⟨l, hl, t, ht, hlt⟩ := hxLT'
    obtain ⟨k, hk⟩ := S.isPGroup_T ⟨t, ht⟩
    have hk' : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨l', hl', he⟩ := pow_mem_mul_of_normalizes hl (hTL' ht) (2 ^ k)
    rw [hk', mul_one] at he
    have hx2 : x ^ 2 ^ k ∈ L' := by rw [← hlt, he]; exact hl'
    have hcop : Nat.Coprime (orderOf x) (2 ^ k) :=
      Nat.Coprime.pow_right k (Nat.coprime_two_right.mpr hx.2)
    exact B6.mem_of_pow_mem_of_coprime hx2 hcop

  have hdvd1 : (pCoreOf 2 X).relIndex X ∣ (X ⊓ pCoreOf 2 L').relIndex X := by
    refine Subgroup.relIndex_dvd_of_le_left X ?_
    refine le_pCoreOf_of_le_normalizer inf_le_left ?_
      ((pCoreOf_isPGroup 2 L').to_le inf_le_right)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, le_normalizer_pCoreOf 2 L' (hXL' hx)⟩
  have hdvd2 : (X ⊓ pCoreOf 2 L').relIndex X ∣ (pCoreOf 2 L').relIndex L' := by
    have hXN : X ≤ Subgroup.normalizer (pCoreOf 2 L' : Set G) :=
      hXL'.trans (le_normalizer_pCoreOf 2 L')
    have e1 : (X ⊓ pCoreOf 2 L').relIndex X = (pCoreOf 2 L').relIndex X := by
      rw [Subgroup.relIndex, Subgroup.relIndex]
      congr 1
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e1, ← B2F.relIndex_sup_eq_of_le_normalizer' hXN]
    have hle2 : X ⊔ pCoreOf 2 L' ≤ L' := sup_le hXL' (pCoreOf_le 2 L')
    rw [← Subgroup.relIndex_mul_relIndex (pCoreOf 2 L') (X ⊔ pCoreOf 2 L') L' le_sup_right hle2]
    exact Dvd.intro _ rfl
  have h9 := hdvd1.trans hdvd2
  rw [hidx, h60] at h9
  omega

end Setting

end CFSG.Quasithin.H13.A5
