module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.A5S1328Sym1

public section
namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.A5Model

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G]

namespace Setting

variable {T L V : Subgroup G} (S : Setting G T L V)
include S

omit S in
theorem mem_V1_of_F4 (h512 : Stmt5_1_2_F4) {K VH : Subgroup G}
    (S' : Setting G T K VH)
    (hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G))
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) {y : G}
    (hy : y ∈ quasithinOmegaOneCenter T) : y = 1 ∨ y = S'.z := by
  obtain ⟨v, hv, c, hc, rfl⟩ := S'.Z_decomp_F4 h512 hJK hy
  have hvZ : v ∈ quasithinOmegaOneCenter T := by
    rcases S'.mem_V1.1 hv with rfl | rfl
    · exact Subgroup.one_mem _
    · exact S'.z_mem_omegaOneCenter
  have hcZ : c ∈ quasithinOmegaOneCenter T := by
    have e : c = v⁻¹ * (v * c) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hvZ) hy
  have hcK : c ∈ Subgroup.centralizer (K : Set G) :=
    Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr le_sup_left) hc
  have hc1 : c = 1 := by
    have : c ∈ quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) := ⟨hcZ, hcK⟩
    rwa [hZK, Subgroup.mem_bot] at this
  rw [hc1, mul_one]
  exact S'.mem_V1.1 hv

theorem z_eq_of_F4 (h512 : Stmt5_1_2_F4) {K VH : Subgroup G}
    (S' : Setting G T K VH)
    (hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G))
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) : S.z = S'.z :=
  (mem_V1_of_F4 h512 S' hJK hZK S.z_mem_omegaOneCenter).resolve_left S.z_ne_one

theorem mem_omegaOneCenter_of_F4 (h512 : Stmt5_1_2_F4) {K VH : Subgroup G}
    (S' : Setting G T K VH)
    (hJK : ¬ thompsonJ T ≤ Subgroup.centralizer
      (conjClosure (quasithinOmegaOneCenter T) (K ⊔ T) : Set G))
    (hZK : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (K : Set G) = ⊥) {x : G}
    (hx : x ∈ quasithinOmegaOneCenter T) : x = 1 ∨ x = S.z := by
  rw [S.z_eq_of_F4 h512 S' hJK hZK]
  exact mem_V1_of_F4 h512 S' hJK hZK hx

end Setting

end CFSG.Quasithin.H13.A5
