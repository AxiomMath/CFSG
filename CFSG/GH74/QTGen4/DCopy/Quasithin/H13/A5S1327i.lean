module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327e

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem exists_T_F0_ne_one_F4 (h331 : Stmt3_3_1_F4) (h1222 : Stmt12_2_2_F4)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3)))
    {F : ↥(S.H0 H) →* Equiv.Perm (Fin 3)}
    (hF1 : ∀ g : ↥(S.H0 H), F g = 1 ↔ (g : G) ∈ Subgroup.centralizer (S.UH H : Set G)) :
    ∃ t₀ : ↥(S.H0 H), (t₀ : G) ∈ T ∧ F t₀ ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := hH.1.1
  by_contra hall
  push Not at hall
  obtain ⟨hMP, -⟩ := S.hyp501.minParabolic_of_isHStar_F4 h331 hH
  apply hMP.not_normal
  have hTO : T ≤ pCoreOf 2 H := by
    intro t ht
    refine S.centralizer_UH_le_pCoreOf_F4 h331 h1222 hH hHZ hsolv hS3 ⟨hTH ht, ?_⟩
    exact (hF1 ⟨t, Subgroup.mem_sup_right (hTH ht)⟩).1 (hall _ ht)
  have heq : pCoreOf 2 H = T :=
    le_antisymm (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_le S.h13.sylow hTH)) hTO
  rw [← heq]
  exact le_normalizer_pCoreOf 2 H

end Setting

end CFSG.Quasithin.H13.A5
