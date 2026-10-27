module

public import CFSG.LieType.SeitzGeneration.ExtSeitzFamily
public import CFSG.LieType.SeitzGeneration.ExcCatModels
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Phi2
public import CFSG.LieType.SeitzGeneration.ExtSeitzReeF4Cyclic

public section

namespace CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP TauCeti

section Proved


theorem seitzExcAnisotropicForAt_reeF4_geFive :
    SeitzExcAnisotropicForAt IsReeF4Index PrimeRange.geFive := by
  have hfs := fun (m : ℕ) (hv : (LieTypeIndex.reeF4 m).Valid) =>
    finite_isSimpleGroup_cat_reeF4 (m := m) hv
  have hA := seitzExcAnisotropicForAt_of_family (c := LieTypeIndex.reeF4)
    (P := fun m p => p ∣ 2 ^ (2 * m + 1) - 1) (F := IsReeF4Index)
    (Q := fun d p => 5 ≤ p ∧ ∃ m : ℕ, d = .reeF4 m ∧ p ∣ 2 ^ (2 * m + 1) - 1) hfs
    SEITZX.extSeitzAtInnerFor_reeF4_split
    (fun d p _ hQ => by
      obtain ⟨hp5, m, rfl, h⟩ := hQ
      exact ⟨m, rfl, hp5, h⟩)
  have hB := seitzExcAnisotropicForAt_of_family (c := LieTypeIndex.reeF4)
    (P := fun m p => p ∣ 2 ^ (2 * m + 1) + 1) (F := IsReeF4Index)
    (Q := fun d p => 5 ≤ p ∧ ∃ m : ℕ, d = .reeF4 m ∧ p ∣ 2 ^ (2 * m + 1) + 1) hfs
    extSeitzAtInnerFor_reeF4_phi2
    (fun d p _ hQ => by
      obtain ⟨hp5, m, rfl, h⟩ := hQ
      exact ⟨m, rfl, hp5, h⟩)
  have hC := seitzExcAnisotropicForAt_of_family (c := LieTypeIndex.reeF4)
    (P := fun m p => p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) (F := IsReeF4Index)
    (Q := fun d p => 5 ≤ p ∧ ∃ m : ℕ, d = .reeF4 m ∧ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) hfs
    extSeitzAtInnerFor_reeF4_phi4
    (fun d p _ hQ => by
      obtain ⟨hp5, m, rfl, h⟩ := hQ
      exact ⟨m, rfl, hp5, h⟩)
  have hD := seitzExcAnisotropicForAt_of_family (c := LieTypeIndex.reeF4)
    (P := fun m p => ¬ p ∣ 2 ^ (2 * m + 1) - 1 ∧ ¬ p ∣ 2 ^ (2 * m + 1) + 1 ∧
      ¬ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) (F := IsReeF4Index)
    (Q := fun d p => 5 ≤ p ∧ ∃ m : ℕ, d = .reeF4 m ∧ ¬ p ∣ 2 ^ (2 * m + 1) - 1 ∧
      ¬ p ∣ 2 ^ (2 * m + 1) + 1 ∧ ¬ p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1) hfs
    extSeitzAtInnerFor_reeF4_cyclic
    (fun d p _ hQ => by
      obtain ⟨hp5, m, rfl, h⟩ := hQ
      exact ⟨m, rfl, hp5, h⟩)
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, ⟨m, rfl⟩, hQ, hr, hn⟩
  have hF : IsReeF4Index (LieTypeIndex.reeF4 m) := ⟨m, rfl⟩
  by_cases h1 : p ∣ 2 ^ (2 * m + 1) - 1
  · exact hA ⟨_, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hQ, m, rfl, h1⟩, hr, hn⟩
  by_cases h2 : p ∣ 2 ^ (2 * m + 1) + 1
  · exact hB ⟨_, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hQ, m, rfl, h2⟩, hr, hn⟩
  by_cases h4 : p ∣ (2 ^ (2 * m + 1)) ^ 2 + 1
  · exact hC ⟨_, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hQ, m, rfl, h4⟩, hr, hn⟩
  · exact hD ⟨_, hv⟩ p hp hp2 hpd hex E hE hc ⟨hin, hF, ⟨hQ, m, rfl, h1, h2, h4⟩, hr, hn⟩

end Proved

@[expose] def SeitzExcAnisotropicReeF4Three : Prop :=
  SeitzExcAnisotropicForAt IsReeF4Index PrimeRange.three

section Assembly


theorem seitzExcAnisotropicFor_reeF4_of_three (h3 : SeitzExcAnisotropicReeF4Three) :
    SeitzExcAnisotropicReeF4 :=
  SeitzExcAnisotropicFor.of_three_geFive h3 seitzExcAnisotropicForAt_reeF4_geFive

end Assembly

end CFSG.LieType.SeitzGeneration
