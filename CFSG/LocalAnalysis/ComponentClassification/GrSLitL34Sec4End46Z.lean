module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4InputsEnd46Z

public section

namespace CFSG.ComponentClassification.GrSLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr

theorem l34Lemma46ClosedStep_of_inputs (hZst : L34Lemma46ZStep) (hStr : L34Lemma46StrongStep) :
    L34Lemma46ClosedStep := by
  intro G _ _ a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl
  have hZS := hZst G a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl
  have hprod := hStr G a x J S A hset hcent hZ hrun hn3 hexp hnc W hW hWodd hWx hNJ hMO hNS hSyl
    hZS
  obtain ⟨-, hU3, -, -, -, haS, -⟩ := id hset
  have ha2 : orderOf a = 2 := hU3.1
  have haa : a * a = 1 := by rw [← pow_two, ← ha2, pow_orderOf_eq_one]
  have ha1 : a ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ha2
    exact absurd ha2 (by norm_num)
  have hinvol : ∀ g : G, g⁻¹ * a * g * (g⁻¹ * a * g) = 1 := fun g => by
    rw [show g⁻¹ * a * g * (g⁻¹ * a * g) = g⁻¹ * (a * a) * g by group, haa]
    group
  let B : Subgroup G :=
    { carrier := {y | y = 1 ∨ (y ∈ S ∧ ∃ g : G, y = g⁻¹ * a * g)}
      one_mem' := Or.inl rfl
      mul_mem' := by
        rintro y z (rfl | ⟨hyS, hy⟩) (rfl | ⟨hzS, hz⟩)
        · exact Or.inl (one_mul 1)
        · exact Or.inr ⟨by simpa using hzS, by simpa using hz⟩
        · exact Or.inr ⟨by simpa using hyS, by simpa using hy⟩
        · by_cases hyz : y = z
          · left
            obtain ⟨g, rfl⟩ := hz
            rw [hyz]
            exact hinvol g
          · exact Or.inr ⟨mul_mem hyS hzS, hprod y hyS z hzS hy hz hyz⟩
      inv_mem' := by
        rintro y (rfl | ⟨hyS, g, rfl⟩)
        · exact Or.inl inv_one
        · right
          rw [inv_eq_of_mul_eq_one_right (hinvol g)]
          exact ⟨hyS, g, rfl⟩ }
  have hmemB : ∀ y : G, y ∈ B ↔ y = 1 ∨ (y ∈ S ∧ ∃ g : G, y = g⁻¹ * a * g) := fun _ => Iff.rfl
  refine ⟨B, ?_, ?_, ?_⟩
  · intro y hy
    rcases (hmemB y).mp hy with rfl | ⟨hyS, hy'⟩
    · exact one_mem _
    · exact mem_inf.mpr ⟨hyS, hZS y hyS hy'⟩
  · intro hbot
    have haB : a ∈ B := (hmemB a).mpr (Or.inr ⟨haS, 1, by group⟩)
    rw [hbot, mem_bot] at haB
    exact ha1 haB
  · intro y hy g hgS
    rcases (hmemB y).mp hy with rfl | ⟨-, h, rfl⟩
    · rw [show g⁻¹ * 1 * g = 1 by group]
      exact one_mem _
    · exact (hmemB _).mpr (Or.inr ⟨hgS, h * g, by group⟩)

end CFSG.ComponentClassification.GrSLit
