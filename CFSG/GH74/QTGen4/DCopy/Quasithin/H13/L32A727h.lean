module

public import CFSG.Quasithin.H13.L32A727h
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A727f
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A727g

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem false_of_card_three_F4 (S : Setting147 G T L V H) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (h76 : Lemma14_7_6_F4)
    (hs : Group.IsSolvable (↥H ⧸ CFSG.pCore 2 ↥H))
    {X : Subgroup ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H))}
    (hXf : ∀ α : MulAut ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)), (orderOf α).Coprime 3 →
      (∀ x ∈ X, x⁻¹ * α x ∈ frattiniIn X) → α = 1)
    (hK3 : Nat.card ↥(X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype) = 3)
    (hKn : (X.map (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).subtype).Normal)
    (hL3 : ¬ IsPGroup 3 ↥(modO2Image H (l1 T L V))) : False := by
  have : (CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)).Normal := CFSG.pCore_normal
  obtain ⟨j, hjL, hj2⟩ := exists_involution_l1_star_F4 S h1222 h1332 h1334 hL3
  have hj1 : j ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hj2
    norm_num at hj2
  have hjj : j ^ 2 ^ 1 = 1 := by
    rw [pow_one]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq hj2)
  obtain ⟨x, hx, hxF⟩ := not_fix_frattini_F4 S h76 hs hXf hjj hj1
  apply hxF
  have hjC := l1_star_le_centralizer hK3 (le_sup_left.trans S.hz.1.1) hjL
  have hc : (x : ↥H ⧸ CFSG.pCore 2 ↥H) * j = j * x := by
    simpa using Subgroup.mem_centralizer_iff.mp hjC _ ⟨x, hx, rfl⟩
  have e : MulAut.conjNormal j x = x := by
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    calc j * (x : ↥H ⧸ CFSG.pCore 2 ↥H) * j⁻¹ = (x : ↥H ⧸ CFSG.pCore 2 ↥H) * j * j⁻¹ := by
          rw [hc]
      _ = x := by group
  rw [e, inv_mul_cancel]
  exact Subgroup.one_mem _

end CFSG.Quasithin.H13.L32A.R727
