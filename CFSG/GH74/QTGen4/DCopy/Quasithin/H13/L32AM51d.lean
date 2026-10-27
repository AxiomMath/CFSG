module

public import CFSG.Quasithin.H13.L32AM51d
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AC51g

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open CFSG.Quasithin.H13.L32A.C.Alt6 (conjK conjK_apply)
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open Equiv Equiv.Perm

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem exists_coords51_F4 (h1222 : Stmt12_2_2_F4) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hL1K : l1 T L V ≤ K)
    (hP : IsPSL 4 2 1 (cStar K)) {π : ↥H →* Perm (Fin 8)} (hsurj : Function.Surjective π)
    (hker : π.ker = CFSG.Open.pCore 2 ↥H)
    (hπK : (π.comp (Subgroup.inclusion (le_of_mem_cComp hK))).range = alternatingGroup (Fin 8)) :
    ∃ πK : ↥K →* Lin.SLn 4, Function.Surjective πK ∧
      (∀ k : ↥K, πK k = 1 ↔ (k : G) ∈ pCoreOf 2 K) ∧
      (T.subgroupOf K).map πK = unitriangular 4 (ZMod 2) ∧
      unitriangular 4 (ZMod 2) ⊔ ((l1 T L V).subgroupOf K).map πK = Lin.par 4 2 := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hTsylH : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  obtain ⟨πK, hπs, hkerK, hD⟩ := exists_pi_sln hP hKH hKn hTsylH
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hKn.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  obtain ⟨i₀, hi₀, hi₀n, hPi⟩ := exists_node_F4 h1222 h1332 h1334 S (by norm_num) hL1K hkerK hD
  obtain ⟨t₀, ht₀T, hodd⟩ := exists_odd_T S hsurj
  obtain ⟨hU, hPst⟩ := T_maps_F4 h1332 S hKn hHN hπs hkerK hD t₀ (hTH ht₀T) ht₀T
  refine ⟨πK, hπs, hkerK, hD, ?_⟩
  rcases Lin.aut_dichotomy (by norm_num) (indHom πK hπs hkerK hKn hHN ⟨t₀, hTH ht₀T⟩) hU with
    ⟨g, hg⟩ | hswap
  · exact absurd ⟨g, hg.symm⟩ (not_inner_of_odd hKH hKn hHN hker hπK hπs hkerK (hTH ht₀T) hodd)
  · have hP' : ∀ g ∈ Lin.par 4 i₀, indHom πK hπs hkerK hKn hHN ⟨t₀, hTH ht₀T⟩ g ∈
        Lin.par 4 i₀ := by
      rw [← hPi]
      exact hPst
    have hni := Lin.eq_of_swap hswap hi₀ hi₀n hP'
    obtain rfl : i₀ = 2 := by omega
    exact hPi

end CFSG.Quasithin.H13.L32A.C
