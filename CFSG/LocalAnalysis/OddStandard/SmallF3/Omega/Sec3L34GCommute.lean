module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Core
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GC1Q
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GStruct
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec3L34GBase

public section

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup

variable {G : Type} [Group G]

theorem l34g_isSubnormal_of_le {H A B : Subgroup G} (hAB : A ≤ B)
    (h : (H.subgroupOf B).IsSubnormal) : (H.subgroupOf A).IsSubnormal := by
  have h' := h.comap (Subgroup.inclusion hAB)
  have e : (H.subgroupOf B).comap (Subgroup.inclusion hAB) = H.subgroupOf A := by
    ext a
    simp [Subgroup.mem_subgroupOf]
  rwa [e] at h'

theorem asc82CommuteStep_of_facts (hO3 : Asc82FactO3Cent) (hC3 : Asc82FactCent3)
    (hM3 : Asc82SchurOdd3) (hNF : Asc82FactNoncentralFixed) : Asc82CommuteStep := by
  intro G _ _ t L hSet x X y K u I hData hQI
  have hD := hData.pocket
  obtain ⟨-, hKcc, hKsub, -⟩ := hD.pocket
  have hxK : ∀ k ∈ K, x * k = k * x := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.1 (hKcc hk).1).symm
  obtain ⟨c, hc, huc⟩ := hData.mem
  have hKu : ∀ k ∈ K, k * u = u * k := by
    intro k hk
    have hkc : k * c = c * k :=
      Subgroup.mem_centralizer_iff.mp hc k (Subgroup.mem_sup_left (hD.le hk))
    have hky : k * y = y * k := Subgroup.mem_centralizer_singleton_iff.1 (hKcc hk).2
    rw [huc]
    calc k * (c * y) = (k * c) * y := (mul_assoc _ _ _).symm
      _ = (c * k) * y := by rw [hkc]
      _ = c * (k * y) := mul_assoc _ _ _
      _ = c * (y * k) := by rw [hky]
      _ = (c * y) * k := (mul_assoc _ _ _).symm
  have hxu : x * u = u * x := by
    have hxc : x * c = c * x :=
      Subgroup.mem_centralizer_iff.mp hc x (Subgroup.mem_sup_right (Subgroup.mem_zpowers x))
    have hxy : x * y = y * x :=
      (Subgroup.mem_centralizer_singleton_iff.1 (hD.component.1 hD.mem)).symm
    rw [huc]
    calc x * (c * y) = (x * c) * y := (mul_assoc _ _ _).symm
      _ = (c * x) * y := by rw [hxc]
      _ = c * (x * y) := mul_assoc _ _ _
      _ = c * (y * x) := by rw [hxy]
      _ = (c * y) * x := (mul_assoc _ _ _).symm
  have hO := l34g_orb_of_component hData.component hData.inFStar hD.involution_x hxu hKu hxK
  set 𝒪 : Set (Subgroup G) := {J | ∃ t ∈ K ⊔ zpowers x, J = CFSG.conjugate I t} with h𝒪
  have hIO : I ∈ 𝒪 := ⟨1, one_mem _, by ext g; rw [sec63P_mem_conjugate_iff]; simp⟩
  have hQE : ∀ q ∈ CFSG.inSubgroup (CFSG.pCore 2) K, ∀ e ∈ sSup 𝒪, q * e = e * q :=
    l34g_Q_centralizes (l34g_T_normalizes_Q hxK) (fun J hJ => hJ) hQI
  have hK3 : ∀ g ∈ K, ∃ n : ℕ, ∀ e ∈ sSup 𝒪, g ^ 3 ^ n * e = e * g ^ 3 ^ n := by
    intro g hg
    obtain ⟨n, hn⟩ := (sec3_pocket_structure hM3 hD).2 g hg
    exact ⟨n, fun e he => hQE _ hn e he⟩
  have hyQ := l34g_mem_pCore_of_pocketData asc82NoQ8InL2_holds asc82OddCoreCentralizerQ8_holds hD
  have hle : K ⊔ (sSup 𝒪 ⊓ centralizer ({x} : Set G)) ≤
      centralizer ({x} : Set G) ⊓ centralizer ({y} : Set G) := by
    refine sup_le hKcc fun e he => ⟨he.2, ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hQE y hyQ e he.1).symm
  exact l34g_commute_core hO3 hC3 hNF hO hIO hK3 (l34g_isSubnormal_of_le hle hKsub)

end CFSG.OddStandard.SmallF3.Omega
