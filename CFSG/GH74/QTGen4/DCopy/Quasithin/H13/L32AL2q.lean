module

public import CFSG.Quasithin.H13.L32AL2q
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2m
public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32AL2p

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V K H : Subgroup G}

theorem L2Red.irred_F4 (hD36 : D36) (hD37 : D37)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6_F4) (h33 : Lemma14_7_33_F4)
    (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29_F4) (h1222 : Stmt12_2_2_F4)
    (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4) (R : L2Red G T L V K)
    (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) (hcase : L2CaseOne G T L V) {W' : Subgroup G}
    (hV₁W : fsuV1 T V ≤ W') (hWU : W' ≤ conjClosure V (A6.g1 T V))
    (hHW : A6.g1 T V ≤ Subgroup.normalizer (W' : Set G)) :
    W' = fsuV1 T V ∨ W' = conjClosure V (A6.g1 T V) := by
  by_cases hU : W' = conjClosure V (A6.g1 T V)
  · exact Or.inr hU
  left
  have : IsMulCommutative ↥(conjClosure V (A6.g1 T V)) := hF.F911_3.1
  obtain ⟨W, hW'W, hW⟩ := exists_topW_of_le R.S hF hV₁W (lt_of_le_of_ne hWU hU) hHW
  obtain ⟨t₀, C⟩ := exists_ctxL2_of_red hA37 hA38 R
  have X : TopCtx T L V K W t₀ := ⟨R, C, hW⟩
  obtain ⟨F, _, _, π, β, Y⟩ :=
    X.exists_model_F4 hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334
  have Wd := Y.wrData_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334

  obtain ⟨-, γ, γ', g, s, hcard, hH2, -, -⟩ := hcase
  obtain ⟨x, hx, hx1⟩ : ∃ x ∈ modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G)), x ≠ 1 := by
    by_contra hall
    push Not at hall
    have : modO2Image (A6.g1 T V) (F8.Uγ V (A6.g1 T V) (g : G)) = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      exact Subgroup.mem_bot.mpr (hall y hy)
    rw [this, Subgroup.card_bot] at hcard
    exact absurd hcard (by norm_num)
  obtain ⟨t, htU, rfl⟩ := mem_modO2Image'.mp hx
  have ht2 : t * t = 1 := Subtype.ext (by
    have := hF.isElemAbelian_Uγ.2 _ htU
    simpa [pow_two] using this)
  have ht1 : X.top.act t ≠ 1 := fun h1 => hx1 (by
    apply X.actDot_injective_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334
    rw [X.actDot_mk t, h1, map_one])
  have hidx := relIndex_centralizer_le hH2 hF.card_A₁ htU
  have hWV := X.eq_fsuV1_F4 hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 Wd ht2 ht1 hidx
  exact le_antisymm (hW'W.trans hWV.le) hV₁W

end CFSG.Quasithin.H13.L32A.L2
