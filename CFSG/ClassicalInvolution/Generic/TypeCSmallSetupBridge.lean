module

public import CFSG.ClassicalInvolution.Generic.TypeCSmallSetupInputs
public import CFSG.ClassicalInvolution.Balance.StrongLocalBalanceSmallC

public section

namespace CFSG.ClassicalInvolution.Generic.TypeCSetup

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {p f : ℕ} [Fact p.Prime]

theorem typeCAxisWeakS_of_baseS (h : SmallTypeCBaseS p f) : TypeCAxisWeakS p f := by
  intro G _ _ _ K z hbr K₁ K₂ K₃ z₁ z₂ z₃ t₁ t₂ t₃ w hd a ha ha1 b hb hbB
  obtain ⟨-, -, -, -, -, hA, hcard⟩ :=
    hd.triple.axis_eight hd.ht₁ hd.ht₂ hd.ht₃ hd.sq₁ hd.sq₂ hd.sq₃ hd.hw hd.inv
  have T := hd.triple
  have hcls : ∀ i : Fin 3, ![K₁, K₂, K₃] i ∈ CoreAssembly.conjClass K ∧
      IsClassicalMember p f (![K₁, K₂, K₃] i) (![z₁, z₂, z₃] i) := by
    intro i
    fin_cases i
    · exact ⟨hd.mem₁, T.cls₁⟩
    · exact ⟨hd.mem₂, T.cls₂⟩
    · exact ⟨hd.mem₃, T.cls₃⟩
  have hcomm : ∀ i j : Fin 3, i ≠ j → Commutes (![K₁, K₂, K₃] i) (![K₁, K₂, K₃] j) := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact T.comm₁₂
    · exact T.comm₁₃
    · exact T.comm₁₂.symm
    · exact absurd rfl hij
    · exact T.comm₂₃
    · exact T.comm₁₃.symm
    · exact T.comm₂₃.symm
    · exact absurd rfl hij
  have hprod : ![z₁, z₂, z₃] 0 * ![z₁, z₂, z₃] 1 * ![z₁, z₂, z₃] 2 = 1 := by
    show z₁ * z₂ * z₃ = 1
    rw [← T.prod]
    calc z₁ * z₂ * (z₁ * z₂) = z₁ * (z₂ * z₁) * z₂ := by group
      _ = z₁ * (z₁ * z₂) * z₂ := by rw [← T.comm_z₁₂]
      _ = (z₁ * z₁) * (z₂ * z₂) := by group
      _ = 1 := by rw [T.sq₁, T.sq₂, one_mul]
  have hord : ∀ {t zz : G}, t * t = zz → zz * zz = 1 → zz ≠ 1 → orderOf t = 4 := by
    intro t zz htt hzz hz1
    have h2 : t ^ 2 = zz := by rw [pow_two, htt]
    refine orderOf_eq_prime_pow (p := 2) (n := 1) ?_ ?_
    · rw [pow_one, h2]
      exact hz1
    · calc t ^ (2 ^ (1 + 1)) = (t ^ 2) ^ 2 := by rw [← pow_mul]; norm_num
        _ = 1 := by rw [h2, pow_two, hzz]
  have ht : ∀ i : Fin 3, ![t₁, t₂, t₃] i ∈ ![K₁, K₂, K₃] i ∧
      ![t₁, t₂, t₃] i * ![t₁, t₂, t₃] i = ![z₁, z₂, z₃] i ∧ orderOf (![t₁, t₂, t₃] i) = 4 := by
    intro i
    fin_cases i
    · exact ⟨hd.ht₁, hd.sq₁, hord hd.sq₁ T.sq₁ T.cls₁.ne_one⟩
    · exact ⟨hd.ht₂, hd.sq₂, hord hd.sq₂ T.sq₂ T.cls₂.ne_one⟩
    · exact ⟨hd.ht₃, hd.sq₃, hord hd.sq₃ T.sq₃ T.cls₃.ne_one⟩
  exact h G hbr.nonabelian hbr.odd hbr.five hbr.below K z hbr.cls hbr.rank hbr.fiveGenerated
    hbr.conn hbr.noBoot hbr.noA2 ![K₁, K₂, K₃] ![z₁, z₂, z₃] ![t₁, t₂, t₃] hcls hcomm hprod ht
    (axis z₁ z₂ t₁ t₂ t₃) rfl hA hcard a ha ha1 b hb hbB

theorem smallTypeCSetup_of_baseS (hexotic : ExoticLeviBlock p f) (h1 : TypeCEdgeTriangle p f)
    (h2a : TypeCAxisWeakClassical p f) (h2b : SmallTypeCBaseS p f) (h2c : TypeCAxisTwo p f)
    (h3 : TypeCFrameSide p f) (hp1 : TypeCP1Step p f) : SmallTypeCSetup p f :=
  smallTypeCSetup_of_parts hexotic h1 h2a (typeCAxisWeakS_of_baseS h2b) h2c h3 hp1

end CFSG.ClassicalInvolution.Generic.TypeCSetup
