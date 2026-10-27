module

public import CFSG.Quasithin.H13.NQS1345
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS1345A
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.NQS134Defs

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G}

theorem vk_facts_F4 (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (S : A6.Setting134 G T L V)
    {K : Subgroup G} (hKf : quasithinIsFaithfulLocal T K)
    (hnU : ¬ LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSU 3 3 1)
    {VK : Subgroup G} (hV : IsIrrPlusIn K (reducedAggregate (K ⊔ T)) T VK) :
    T ≤ normalizer (VK : Set G) ∧ FSU G T K VK ∧
      VK = conjClosure (quasithinOmegaOneCenter T ⊓ VK) K ∧
      (∃ _ : IsMulCommutative ↥VK,
        (AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 5 ∧
            VK ⊓ centralizer (K : Set G) = ⊥) ∨
          (AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 6 ∧
            VK ⊓ centralizer (K : Set G) = ⊥) ∨
          (Nat.card VK = 2 ^ 5 ∧ Nat.card ↥(VK ⊓ centralizer (K : Set G)) = 2 ∧
            FFModel.Realizes (V := ↥VK) (altCoreModel 6) (autOn K VK) ⊤ ⊥) ∨
          (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
            BinaryNaturalSL (V := ↥VK) (autOn K VK) ⊤ ⊥ 3 1 ∧
            VK ⊓ centralizer (K : Set G) = ⊥)) ∧
      A6.o2Z K = K ⊓ centralizer (VK : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨hTK, -, -, -⟩, ⟨-, hall⟩, h4⟩ := h1332 G T L S.h13 K hKf
  obtain ⟨hVT, hTV, hfsu, hab, hmod⟩ := hall VK hV
  have hKV : K ≤ normalizer (VK : Set G) := hV.2.2.1
  have hne : ¬ K ≤ centralizer (VK : Set G) := fun hle => hV.2.1 (hV.2.2.2.1.symm.trans
    (commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp hle)))

  have hmod4 : (AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 5 ∧
        VK ⊓ centralizer (K : Set G) = ⊥) ∨
      (AlternatingNatural (V := ↥VK) (autOn K VK) ⊤ ⊥ 6 ∧
        VK ⊓ centralizer (K : Set G) = ⊥) ∨
      (Nat.card VK = 2 ^ 5 ∧ Nat.card ↥(VK ⊓ centralizer (K : Set G)) = 2 ∧
        FFModel.Realizes (V := ↥VK) (altCoreModel 6) (autOn K VK) ⊤ ⊥) ∨
      (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
        BinaryNaturalSL (V := ↥VK) (autOn K VK) ⊤ ⊥ 3 1 ∧
        VK ⊓ centralizer (K : Set G) = ⊥) := by
    rcases hmod with ha | hb | hc | hd | he
    · exact Or.inl ha
    · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr hd))
    · exact absurd he.1 hnU

  have hOKT : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      (sup_le (le_normalizer_pCoreOf 2 K) (hTK.trans (normalizer_le_normalizer_pCoreOf 2 K)))
      (pCoreOf_isPGroup 2 K)
  have hO : pCoreOf 2 K ≤ centralizer (VK : Set G) :=
    (hOKT.trans (pCoreOf_le_centralizer_R2 (K ⊔ T))).trans
      (centralizer_le (SetLike.coe_subset_coe.mpr hV.1))

  have hnt : Nontrivial ↥(autOn K VK) :=
    (nontrivial_iff_ne_bot _).mpr (autOn_ne_bot_of_not_le_centralizer hKV hne)
  have hcen : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥ ∨ center ↥(autOn K VK) = ⊥ := by
    rcases hmod4 with ⟨⟨π, hπ⟩, -⟩ | ⟨⟨π, hπ⟩, -⟩ | ⟨-, -, ⟨π, hπ⟩⟩ | ⟨hd, -, -⟩
    · exact Or.inr (center_eq_bot_of_alt (n := 5) (by norm_num) π hπ.1)
    · exact Or.inr (center_eq_bot_of_alt (n := 6) (by norm_num) π hπ.1)
    · exact Or.inr (center_eq_bot_of_alt (n := 6) (by norm_num) π hπ.1)
    · exact Or.inl (center_eq_bot_of_simple_types (Or.inr (Or.inl hd)))

  have hVZ : VK = conjClosure (quasithinOmegaOneCenter T ⊓ VK) K := by
    by_cases hA5 : quasithinO2QuotientIso K (alternatingGroup (Fin 5))
    · have hC : VK ⊓ centralizer (K : Set G) = ⊥ :=
        (A5.modules13_3_2_of_A5 ((quasithinO2QuotientIso_iff K _).1 hA5) hKV hne hmod).2
      obtain ⟨hVR, hV1, -, -, -, hirr, -⟩ := hV
      have hJV : conjClosure (quasithinOmegaOneCenter T ⊓ VK) K ≤ VK :=
        conjClosure_le fun k hk z hz => (mem_normalizer_iff.mp (hKV hk) z).mp hz.2
      rcases hirr _ (hC ▸ bot_le) hJV (le_normalizer_conjClosure _ _) with h | h
      · exfalso
        rw [hC] at h
        obtain ⟨v, hv1⟩ := ne_bot_iff_exists_ne_one.mp
          (inf_centralizer_ne_bot_of_two S.h13.sylow.1 hVT hTV hV1)
        have hv2 : (v : G) ^ 2 = 1 := (twoReduced_R2 (K ⊔ T)).2.2.1.2 _ (hVR (mem_inf.1 v.2).1)
        have hvZ : (v : G) ∈ quasithinOmegaOneCenter T ⊓ VK :=
          ⟨mem_quasithinOmegaOneCenter_iff.2 ⟨hVT (mem_inf.1 v.2).1, (mem_inf.1 v.2).2, hv2⟩,
            (mem_inf.1 v.2).1⟩
        have h1 := le_conjClosure (quasithinOmegaOneCenter T ⊓ VK) K hvZ
        rw [h, mem_bot] at h1
        exact hv1 (Subtype.ext h1)
      · exact h.symm
    · have h1 := (h1334 G T K VK (h4 (Or.inl hA5)) hV).2.1
      rw [inf_comm]
      exact h1.symm
  exact ⟨hTV, hfsu, hVZ, ⟨hab, hmod4⟩, o2Z_eq_inf_centralizer hKV hO hne hfsu.quasisimple hcen⟩

theorem stmt13_4_5_of_F4 (h1332 : Stmt13_3_2_F4) (h13316 : Stmt13_3_16_F4) (h1334 : A6.Stmt13_3_4_F4)
    (h1338 : A6.Stmt13_3_8_F4) : Stmt13_4_5_F4 := by
  intro G _ _ T L V S H hH hHM hnsolv
  refine ⟨exists_mem_cComp hnsolv, fun K hK => ?_⟩
  obtain ⟨⟨hKmax, hKf⟩, hHK, hlist, hKM, hLK, hKZ⟩ := one_two_F4 h1332 h13316 h1338 S hH hHM hK
  have hnU := not_lieModel_PSU_F4 h1332 h13316 S hKf
  obtain ⟨-, -, ⟨hex, -⟩, -⟩ := h1332 G T L S.h13 K hKf
  obtain ⟨P, rfl⟩ := exists_sylow_of_quasithinIsSylowTwo S.h13.sylow
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hchar : CharTwo H := charTwo_of_inH S.h13.qtke.2.1 P hH
  have hTsyl : IsSylowTwoOf (P : Subgroup G) H := isSylowTwoOf_of_sylow_le P hH.1
  have hTKsyl : IsSylowTwoOf (P : Subgroup G) (K ⊔ P) := isSylowTwoOf_of_sylow_le P le_sup_right
  have hcharKT : CharTwo (K ⊔ (P : Subgroup G)) :=
    charTwo_of_inH S.h13.qtke.2.1 P ⟨le_sup_right, hKf.1.2.2.2⟩
  have hR : reducedAggregate (K ⊔ (P : Subgroup G)) ≤ reducedAggregate H :=
    R2_le_of_le hTsyl hchar le_sup_right (sup_le hKH hH.1)
  have hirr : ∀ W : Subgroup G, IsIrrPlusIn K (reducedAggregate (K ⊔ (P : Subgroup G))) P W →
      A6.o2Z K ≤ centralizer (W : Set G) := fun W hW =>
    (vk_facts_F4 h1332 h1334 S hKf hnU hW).2.2.2.2.le.trans inf_le_right
  have hRH := o2Z_le_centralizer_R2 hTsyl hKH hHK hTKsyl hcharKT
    (cube_mem_pCoreOf_of_o2Z hlist) hirr
  refine ⟨⟨hKmax, hKf⟩, hHK, hlist, hKM, hLK, hKZ, fun W hW => isIrrPlusIn_self_mono hR hW, hex,
    fun VK hVK => ?_⟩
  obtain ⟨hTV, hfsu, hVZ, hmod, ho2Z⟩ := vk_facts_F4 h1332 h1334 S hKf hnU hVK
  refine ⟨hTV, hfsu, hVZ, hmod, ho2Z, le_antisymm ?_ (le_inf A6.o2Z_le_L hRH)⟩
  rw [ho2Z]
  exact inf_le_inf_left K (centralizer_le (SetLike.coe_subset_coe.mpr (hVK.1.trans hR)))

end CFSG.Quasithin.H13.NQS134
