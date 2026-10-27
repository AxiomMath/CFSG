module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch12Sec2Setting
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListA7IsoBase
public import CFSG.Quasithin.H13.L1332Inputs
public import CFSG.Quasithin.H13.VolIAltCoverSix
public import CFSG.Quasithin.Vol2.Ch12Sec2Action

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem modules13_3_2_of_modules12_2_2_F4 [CFSG.GH74.QTGen4.Finite4 G] (h1242 : Stmt12_4_2_F4) (h1271 : Stmt12_7_1_F4)
    (hL32 : L32NoIrrFour) {T K V : Subgroup G} (hH : Hyp1223 G T K V) (hexcl : ¬ QT13Excluded G)
    (h5K : QT13Five (↥K ⧸ CFSG.pCore 2 ↥K)) [IsMulCommutative ↥V]
    (hred : IsPrimeReduced 2 (V.subgroupOf (K ⊔ T))) (hVT : V ≤ T)
    (hmod : Modules12_2_2 K V) : Modules13_3_2 K V := by
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := hH.irrPlus.2.2.1
  have hc : ⁅V, K⁆ = V := hH.irrPlus.2.2.2.1
  have hV1 : V ≠ ⊥ := hH.irrPlus.2.1
  have hVLT : V ≤ K ⊔ T := hVT.trans le_sup_right
  have hsq : ∀ v : ↥V, v ^ 2 = 1 := by
    intro v
    have := hred.isElementaryAbelian
    have h2 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := V.subgroupOf (K ⊔ T))
      (⟨v, hVLT v.2⟩ : ↥(K ⊔ T)) (Subgroup.mem_subgroupOf.mpr v.2)
    exact Subtype.ext (by simpa using congrArg Subtype.val h2)
  have hcomm' : commV (autOn K V) = ⊤ := commV_autOn_eq_top hKV hc
  have hfix := fixV_autOn_eq hKV
  have h1242' := (stmt12_4_2_iff_F4.mp h1242) G T K V hH
  have hnc : ¬ K ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    apply hV1
    rw [← hc]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G) := by
    have hE : K ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      (sup_le Subgroup.le_normalizer hH.normalizes).trans
        (LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
    have hle : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
      LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((Subgroup.map_subtype_le _).trans le_sup_left) hE (LieType.BorelTits.pCoreOf_isPGroup 2 K)
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hle hx
    have hy' : y ∈ CFSG.pCore 2 ↥(K ⊔ T) := by assumption
    have hyc := pCore_le_centralizer_of_isPrimeReduced hred hy'
    rw [Subgroup.mem_centralizer_iff] at hyc ⊢
    intro v hv
    exact congrArg Subtype.val (hyc ⟨v, hVLT hv⟩ hv)
  have hsurj7 : ∀ {n : ℕ}, (n = 7 ∨ n = 8) → ∀ φ : ↥K →* ↥(alternatingGroup (Fin n)),
      Function.Surjective φ → False := by
    intro n hn φ hφ
    have hle := pCore_le_ker_of_surjective_alternating (by omega) φ hφ
    exact not_surjective_alternating_of_qt13Five h5K hn (QuotientGroup.lift _ φ hle)
      (QuotientGroup.lift_surjective_of_surjective _ φ hφ hle)
  rcases hmod with ⟨n, hn, ⟨e⟩, hnat⟩ | ⟨⟨e⟩, hcard, -⟩ | ⟨⟨e⟩, -, -⟩ |
      ⟨n, hn5, hn8, ⟨φ, hφ, -⟩, halt⟩ | ⟨-, φ, hφ, -⟩ | ⟨hU, hG2⟩ | ⟨hqs, hZ, hA6', hCV, -, -⟩
  · rcases hn with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨lieModel_psl_of_mulEquiv_sl_zmod_two le_rfl e, hnat,
        h1242'.1 (Or.inl ⟨e⟩)⟩)))
    · exact absurd ⟨e⟩ (not_mulEquiv_sl_of_qt13Five h5K (Or.inl rfl))
    · exact absurd ⟨e⟩ (not_mulEquiv_sl_of_qt13Five h5K (Or.inr rfl))
  · exfalso
    have hC := h1242'.1 (Or.inl ⟨e⟩)
    have := Vol2Native.A312L.Seven.slThree_isSimple
    obtain ⟨eA⟩ := nonempty_autOn_mulEquiv_of_simple hKV hO2 hnc e
    obtain ⟨W, hW1, hWtop, hWinv⟩ := hL32 ↥V hsq hcard (autOn K V) ⟨eA⟩
    have hKW := le_normalizer_map_of_invariant hKV hWinv
    have hirr := hH.irrPlus.2.2.2.2.2.1 (W.map V.subtype)
    rw [hC] at hirr
    rcases hirr bot_le (Subgroup.map_subtype_le W) hKW with h | h
    · exact hW1 ((Subgroup.map_eq_bot_iff_of_injective W V.subtype_injective).mp h)
    · apply hWtop
      apply Subgroup.map_injective V.subtype_injective
      rw [h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  · exact absurd ⟨e⟩ (not_mulEquiv_sl_of_qt13Five h5K (Or.inr rfl))
  · have hn' : n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 := by omega
    rcases hn' with rfl | rfl | h78
    · have hZ := VolI.altNaturalCoverFive_holds ↥V hsq (autOn K V) _ hfix.symm.le hcomm' halt
      rw [hZ] at halt
      exact Or.inl ⟨halt, (fixV_autOn_eq_bot_iff hKV).mp (hfix.trans hZ)⟩
    · rcases VolI.altNaturalCoverSix_holds ↥V hsq (autOn K V) _ hfix.symm.le hcomm' halt with
        hZ | ⟨hZ2, hV5, hreal⟩
      · rw [hZ] at halt
        exact Or.inr (Or.inl ⟨halt, (fixV_autOn_eq_bot_iff hKV).mp (hfix.trans hZ)⟩)
      · refine Or.inr (Or.inr (Or.inl ⟨hV5, ?_, hreal⟩))
        rw [← hZ2, ← Subgroup.card_map_of_injective V.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_comm]
    · exact (hsurj7 (by omega) φ hφ).elim
  · exact (hsurj7 (Or.inl rfl) φ hφ).elim
  · have hC := h1242'.1 (Or.inr hU)
    have hZ : (Subgroup.centralizer (K : Set G)).subgroupOf V = ⊥ :=
      hfix.symm.trans ((fixV_autOn_eq_bot_iff hKV).mpr hC)
    rw [hZ] at hG2
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hU, hG2, hC⟩)))
  · exfalso
    have hsub : (Subgroup.centralizer (V : Set G)).subgroupOf K = CFSG.pCore 2 ↥K := by
      rw [← Subgroup.inf_subgroupOf_left, hCV, pCoreOf]
      exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).trans
        (CFSG.pCore_eq_open (↥K) 2).symm
    have hin : ∃ _ : ((Subgroup.centralizer (V : Set G)).subgroupOf K).Normal,
        CFSG.IsQuasisimple (↥K ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf K) ∧
        Nat.card (Subgroup.center (↥K ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf K)) = 3 ∧
        Nonempty ((↥K ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf K) ⧸
            Subgroup.center (↥K ⧸ (Subgroup.centralizer (V : Set G)).subgroupOf K) ≃*
          alternatingGroup (Fin 6)) := by
      rw [hsub]
      exact ⟨inferInstance, hqs, hZ, hA6'⟩
    rcases (stmt12_7_1_iff_F4.mp h1271) G T K V hH hin with h | h
    · exact hexcl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact hexcl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))

end CFSG.Quasithin.H13
