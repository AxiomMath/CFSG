module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.Vol2.Ch6Sec1Basic
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5DN

public section
namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T M L V H : Subgroup G} {n : ℕ}

namespace Cx615C

theorem false_of_centralizes_ch615_F4 (h432 : Stmt4_3_2_F4) (c : Cx615C G T M L V H n) {z : G}
    (hzZ : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1)
    (hKz : oTwoUpper H ≤ Subgroup.centralizer ({z} : Set G)) {d : G} (hdB : d ∈ borelL T L)
    (hdodd : Odd (orderOf d)) (hd1 : d ≠ 1) (hdz : d * z * d⁻¹ = z) : False := by
  have h := c.hyp
  have hz := mem_quasithinOmegaOneCenter_iff.mp hzZ
  have hzd : z ∈ Subgroup.centralizer ({d} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.mp hg]
    calc d * z = d * z * d⁻¹ * d := by group
      _ = z * d := by rw [hdz]
  have hzL : z ∈ Subgroup.centralizer (L : Set G) := c.CZd d hdB hdodd hd1 ⟨hzZ, hzd⟩
  have hord : orderOf z = 2 := orderOf_eq_prime hz.2.2 hz1
  have hP2 : IsPGroup 2 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hord, pow_one])
  have hPne : Subgroup.zpowers z ≠ ⊥ := fun h0 => hz1 (by
    have := Subgroup.mem_zpowers z
    rw [h0] at this
    exact Subgroup.mem_bot.mp this)
  have hloc : IsTwoLocal (Subgroup.normalizer (Subgroup.zpowers z : Set G)) :=
    ⟨_, hPne, hP2, rfl⟩
  have hTz : ∀ t ∈ T, t ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := fun t ht =>
    mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hz.2.1 t ht)
  have hLT : L ⊔ T ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    sup_le (fun l hl => mem_normalizer_zpowers_ch615 (Subgroup.mem_centralizer_iff.mp hzL l hl))
      hTz
  have hNM := le_of_isUniqueM_of_le_twoLocal (h.isUniqueM_F4 h432) hLT hloc
  have hsup : T ⊔ twoResidual H = H := sup_twoResidual_eq c.toCx615.isSylowTwoOf
  rw [twoResidual_eq_oTwoUpper'] at hsup
  apply c.hH.2.1
  rw [← hsup]
  refine sup_le (fun t ht => hNM (hTz t ht)) (fun k hk => hNM ?_)
  have hkz := Subgroup.mem_centralizer_iff.mp (hKz hk) z rfl
  exact mem_normalizer_zpowers_ch615 hkz.symm

end Cx615C

end CFSG.Quasithin.H13
