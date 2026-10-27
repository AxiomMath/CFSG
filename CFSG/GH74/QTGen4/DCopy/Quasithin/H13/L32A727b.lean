module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32A727a

public section

namespace CFSG.Quasithin.H13.L32A.R727

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem pre_le_M_of_le_l1_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hK : K ≤ modO2Image H (l1 T L V)) :
    pre H K ≤ Subgroup.normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 H ≤ T := pCoreOf_le_of_le S.hyp (le_sup_right.trans S.hz.1.1)
  have hLM := l1T_le_M_F4 S.hyp h1332
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨a, ha, hae⟩ := mem_modO2Image'.mp (hK hx)
  have h1 : a⁻¹ * x ∈ CFSG.pCore 2 ↥H := by
    rw [← QuotientGroup.eq]
    exact hae
  rw [← mem_pCoreOf_iff] at h1
  have e : (x : G) = (a : G) * ((a⁻¹ * x : ↥H) : G) := by simp
  rw [Subgroup.coe_subtype, e]
  exact Subgroup.mul_mem _ (le_sup_left.trans hLM ha) (le_sup_right.trans hLM (hOT h1))

theorem eq_sup_of_not_le_F4 (S : Setting147 G T L V H) (h1332 : Stmt13_3_2_F4) (h1334 : A6.Stmt13_3_4_F4)
    (ih : ∀ H₀ : Subgroup G, H₀ < H → Setting147 G T L V H₀ → Concl T L V H₀)
    {K : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)} (hKn : K.Normal) (hK : IsPGroup 3 ↥K)
    (hKM : ¬ pre H K ≤ Subgroup.normalizer (L : Set G)) : H = pre H K ⊔ (l1 T L V ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := pre H K ⊔ (l1 T L V ⊔ T) with hX
  have hXH : X ≤ H := sup_le (pre_le K) S.hz.1.1
  refine (lt_or_eq_of_le hXH).elim (fun hlt => ?_) fun h => h.symm
  exfalso
  have hXM : ¬ X ≤ Subgroup.normalizer (L : Set G) := fun h => hKM (le_sup_left.trans h)
  have S' := setting_of_le_F4 S h1332 h1334 le_sup_right hXH hXM
  refine hKM (le_M_of_concl_F4 S' h1332 (ih X hlt S') le_sup_left
    ((hXH.trans (le_normalizer_pre hKn))) ((pCoreOf_le_pre K).trans le_sup_left)
    (hXH.trans (le_normalizer_pCoreOf 2 H)) (pCoreOf_isPGroup 2 H)
    fun n hn => pow_mem_of_isPGroup hK hn)

end CFSG.Quasithin.H13.L32A.R727
