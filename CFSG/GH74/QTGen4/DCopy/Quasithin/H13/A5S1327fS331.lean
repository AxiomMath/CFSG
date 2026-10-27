module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1327eS331

public section
namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Setting

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V : Subgroup G} (S : Setting G T L V)
include S

theorem pow_three_pow_mem_F4 (h331 : Stmt3_3_1_F4)
    {H : Subgroup G} (hH : IsHStar T (Subgroup.normalizer (L : Set G)) H)
    (hHZ : ¬ H ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G))
    (hsolv : Group.IsSolvable ↥H) (hS3 : Nonempty (↥(S.HStar H) ≃* Equiv.Perm (Fin 3))) :
    ∀ k ∈ oTwoUpper H, ∃ a : ℕ, k ^ 3 ^ a ∈ pCoreOf 2 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hMP, -⟩ := S.hyp501.minParabolic_of_isHStar_F4 h331 hH
  obtain ⟨p, hp, -, hpow⟩ := hMP.exists_prime_pow_mem_pCoreOf hsolv
  rw [twoResidual_eq_oTwoUpper'] at hpow
  obtain ⟨F, hF1, hFsurj, hFT, hFL⟩ := S.exists_F_F4 h331 hH hsolv hS3
  obtain ⟨y, hyL, -, hFy, -⟩ := S.exists_gen_F4 h331 hH hHZ hsolv hF1 hFsurj hFT hFL
  have hsyl : IsSylowTwoOf T H := isSylowTwoOf_of_le S.h13.sylow hH.1.1
  obtain ⟨hUO, -, -⟩ := conjClosure_isTwoReducedIn_of_charTwo hsyl (S.charTwo_of_inH hH.1) le_rfl
  have hO2U : pCoreOf 2 H ≤ Subgroup.centralizer (S.UH H : Set G) :=
    Subgroup.le_centralizer_iff.mp (hUO.trans inf_le_right)
  have hFy3 : orderOf (F ⟨y, oTwoUpper_le H hyL⟩) = 3 := orderOf_eq_prime (hFL y hyL) hFy
  have hp3 : p = 3 := by
    obtain ⟨a, ha⟩ := hpow y hyL
    have h1 : F ⟨y, oTwoUpper_le H hyL⟩ ^ p ^ a = 1 := by
      rw [← map_pow]
      exact (hF1 _).2 (hO2U ha)
    have h3 : 3 ∣ p ^ a := by
      rw [← hFy3]
      exact orderOf_dvd_of_pow_eq_one h1
    exact ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)).symm
  rw [hp3] at hpow
  exact hpow

end Setting

end CFSG.Quasithin.H13.A5
