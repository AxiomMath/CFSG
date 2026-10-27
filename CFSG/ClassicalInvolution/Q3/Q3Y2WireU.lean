module

public import CFSG.ClassicalInvolution.Q3.Q3Y2Wire
public import CFSG.ClassicalInvolution.ModelFacts.TG3SmallSU
public import CFSG.ClassicalInvolution.ModelFacts.TG3VacPSU

public section

namespace CFSG.ClassicalInvolution.Q3.Q3Y2

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models CFSG.ClassicalInvolution.Phan
  CFSG.LieType.BorelTits CFSG.LieType.Universal.Unitary CFSG.LocalAnalysis.ComponentInitial Module
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD
  CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.TG3
open scoped MatrixGroups Matrix

local notation "𝔽₃" => GaloisField 3 1

section WireU

theorem twinStrong3_psu_four (hadm : StatedLieAdmissible .PSU 4 3 1) :
    TwinStrong3 (Generic.fundamentalSubgroups .PSU
      (Generic.modelUniv .PSU 4 3 1 Nat.prime_three).D) := by
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  obtain ⟨e, hfund⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨c, hcsq, hσc⟩ := exists_sq_eq_neg_one_unitary_three (K := GaloisField 3 (2 * 1)) (p := 3)
    (f := 1) hK (by norm_num)
  intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hc _ r₁ hr₁ r₂ hr₂ hrr₁ hrr₂
  obtain ⟨i₁, hi₁⟩ := (hfund R₁).mp hR₁
  obtain ⟨i₂, hi₂⟩ := (hfund R₂).mp hR₂
  have hord : ∀ {R : Subgroup (Generic.modelUniv .PSU 4 3 1 Nat.prime_three).K}
      (eR : R ≃* SL(2, 𝔽₃)), orderOf (e (sl2Inv eR)) = 2 := by
    intro R eR
    rw [MulEquiv.orderOf_eq e]
    exact orderOf_eq_prime (by rw [pow_two]; exact sl2Inv_mul_self hodd eR)
      (sl2Inv_ne_one hodd eR)
  have hi₁e : e (sl2Inv e₁) = i₁ := hi₁.eq_of_orderOf_eq_two hK hp2
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₁)) (hord e₁)
  have hi₂e : e (sl2Inv e₂) = i₂ := hi₂.eq_of_orderOf_eq_two hK hp2
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₂)) (hord e₂)
  have hne' : R₁.map e.toMonoidHom ≠ R₂.map e.toMonoidHom := by
    intro h
    exact hne (by rw [Subgroup.map_injective e.injective h])
  have hc' : i₂ * i₁⁻¹ ∈ Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 4) := by
    rw [← hi₁e, ← hi₂e]
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc x]
  obtain ⟨-, -, -, hgen⟩ := su4_twin_gen hK hp2 le_rfl hcsq hσc hi₁ hi₂ hne' hc'
  refine top_le_sup_sup_of_sup_eq_top (centralizer_sup_eq_top_of_equiv e _ _ ?_)
  rw [map_mul, hi₁e]
  exact hgen (e r₁) (Subgroup.mem_map_of_mem _ hr₁) (e r₂) (Subgroup.mem_map_of_mem _ hr₂)
    (by rw [← map_mul, hrr₁, hi₁e]) (by rw [← map_mul, hrr₂, hi₂e])

theorem twinStrong3_psu_ne_four {k : ℕ} (hadm : StatedLieAdmissible .PSU k 3 1) (hk : k ≠ 4) :
    TwinStrong3 (Generic.fundamentalSubgroups .PSU
      (Generic.modelUniv .PSU k 3 1 Nat.prime_three).D) := by
  have hk3 : 3 ≤ k := hadm.2.2.1
  have hp2 : (3 : ℕ) ≠ 2 := by norm_num
  have hodd := odd_natCard_galoisField_three
  obtain ⟨e, hfund⟩ := psu_model_equiv (p := 3) (f := 1) hp2 hadm
  have hK : Nat.card (GaloisField 3 (2 * 1)) = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  intro R₁ hR₁ R₂ hR₂ e₁ e₂ hne _ hcen _
  exfalso
  have hsq₁ := sl2Inv_mul_self hodd e₁
  have hsq₂ := sl2Inv_mul_self hodd e₂
  have hcen' : sl2Inv e₁ * sl2Inv e₂ ∈
      Subgroup.center (Generic.modelUniv .PSU k 3 1 Nat.prime_three).K := by
    have h1 : sl2Inv e₁ * sl2Inv e₂ = sl2Inv e₂ * (sl2Inv e₁)⁻¹ := by
      have hc := Subgroup.mem_center_iff.mp hcen (sl2Inv e₁)
      have hinv : (sl2Inv e₁)⁻¹ = sl2Inv e₁ := inv_eq_of_mul_eq_one_right hsq₁
      rw [hinv] at hc ⊢
      have h3 := congrArg (fun x => x * sl2Inv e₁) hc
      simp only [mul_assoc, hsq₁, mul_one] at h3
      exact h3
    rw [h1]
    exact hcen
  have hne' : R₁.map e.toMonoidHom ≠ R₂.map e.toMonoidHom := by
    intro h
    exact hne (by rw [Subgroup.map_injective e.injective h])
  have hcenE : e (sl2Inv e₁) * e (sl2Inv e₂) ∈
      Subgroup.center (Su (GaloisField 3 (2 * 1)) 3 1 k) := by
    refine Subgroup.mem_center_iff.mpr fun y => ?_
    obtain ⟨x, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hcen' x]
  have hres := rank_eq_four_of_central_pair_su3 (K := GaloisField 3 (2 * 1)) (p := 3) (f := 1) hK
    hp2 le_rfl hk3 ((hfund R₁).mp hR₁) ((hfund R₂).mp hR₂) hne'
    (r₁ := e (sl2Inv e₁)) (r₂ := e (sl2Inv e₂))
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₁))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      change e (sl2Inv e₁) * e s₀ = e s₀ * e (sl2Inv e₁)
      rw [← map_mul, ← map_mul, sl2Inv_commute e₁ hs₀])
    (fun h => sl2Inv_ne_one hodd e₁ (e.injective (by rw [h, map_one])))
    (Subgroup.mem_map_of_mem _ (sl2Inv_mem e₂))
    (fun s hs => by
      obtain ⟨s₀, hs₀, rfl⟩ := hs
      change e (sl2Inv e₂) * e s₀ = e s₀ * e (sl2Inv e₂)
      rw [← map_mul, ← map_mul, sl2Inv_commute e₂ hs₀])
    (fun h => sl2Inv_ne_one hodd e₂ (e.injective (by rw [h, map_one])))
    hcenE
  exact hk hres

end WireU

end CFSG.ClassicalInvolution.Q3.Q3Y2
