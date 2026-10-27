module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Act
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Fac
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Zero
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Fix
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1P

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G] {u x : G} {K I : Subgroup G} {𝒪 : Set (Subgroup G)}

theorem l34g_commute_core [Finite G] (hO3 : Asc82FactO3Cent) (hC3 : Asc82FactCent3)
    (hNF : Asc82FactNoncentralFixed) (hO : L34GOrb u x K 𝒪) (hI : I ∈ 𝒪)
    (hK3 : ∀ g ∈ K, ∃ n : ℕ, ∀ e ∈ sSup 𝒪, g ^ 3 ^ n * e = e * g ^ 3 ^ n)
    (hsub : (K.subgroupOf (K ⊔ (sSup 𝒪 ⊓ centralizer ({x} : Set G)))).IsSubnormal) :
    ⁅K, I⁆ = ⊥ := by
  have hxN : x ∈ normalizer ((sSup 𝒪 : Subgroup G) : Set G) :=
    hO.T_normalizes (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
  have hKN : K ≤ normalizer ((sSup 𝒪 : Subgroup G) : Set G) :=
    fun k hk => hO.T_normalizes (Subgroup.mem_sup_left hk)
  have hCN : sSup 𝒪 ⊓ centralizer ({x} : Set G) ≤ normalizer ((sSup 𝒪 : Subgroup G) : Set G) :=
    inf_le_left.trans Subgroup.le_normalizer
  have hx : x * x = 1 := sec63P_mul_self hO.invol
  have hP : l34gImg (sSup 𝒪) K = ⊥ :=
    l34g_act hO3 hC3 (hO.fac hxN) (l34g_c0_le hxN) (l34g_c0_normal hxN) (l34g_c0_odd hx hxN)
      (hO.c0_fixed hNF hxN) (hO.c0_swap hxN) (l34g_p_pGroup hKN hK3)
      (l34g_p_commute hKN hxN hO.xK) hO.p_perm (l34g_p_normalizes hKN hO.xK)
      (l34g_p_subnormal hKN hCN hsub)
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro i hi
  have h1 : (sSup 𝒪).normalizerMonoidHom ⟨k, hKN hk⟩ = 1 := by
    have hmem : (sSup 𝒪).normalizerMonoidHom ⟨k, hKN hk⟩ ∈ l34gImg (sSup 𝒪) K :=
      mem_l34gImg.2 ⟨k, hKN hk, hk, rfl⟩
    rw [hP] at hmem
    exact Subgroup.mem_bot.1 hmem
  exact ((l34gAct_eq_one_iff (hKN hk)).1 h1 i (le_sSup hI hi)).symm

end CFSG.OddStandard.SmallF3.Omega
