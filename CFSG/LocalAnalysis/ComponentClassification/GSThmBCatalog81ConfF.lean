module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfK
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3Conf
public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog81ConfB

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup

namespace Conf81

variable {K₀ : Type} [Group K₀] [Finite K₀]

omit [Finite K₀] in
theorem isPGroup_sup {Q : Subgroup (MulAut K₀)} {g : MulAut K₀} (hQ : IsPGroup 2 Q)
    (hgN : g ∈ normalizer (Q : Set (MulAut K₀))) (hg2 : g * g ∈ Q) :
    IsPGroup 2 ↥(zpowers g ⊔ Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := hQ ⟨g * g, hg2⟩
  have hgn : g ^ 2 ^ (n + 1) = 1 := by
    have h1 := congrArg Subtype.val hn
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h1
    rw [pow_succ', pow_mul, pow_two]
    exact h1
  have hp : IsPGroup 2 (zpowers g) := by
    rintro ⟨y, hy⟩
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hy
    refine ⟨n + 1, Subtype.ext ?_⟩
    change (g ^ i) ^ 2 ^ (n + 1) = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hgn, one_zpow]
  exact hp.to_sup_of_normal_right' hQ (zpowers_le.mpr hgN)

theorem exists_q3Conf (c : Cat8.QConf K₀ (3 ^ 1))
    (htop : Cat8.Inn K₀ ⊔ zpowers c.a = ⊤) :
    ∃ c' : Cat8.Q3Conf K₀, c'.a = c.a ∧ c'.Q = c.Q ∧ c'.g = c.g ∧ c'.z = c.z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (MulAut K₀) := Finite.of_injective (fun φ : MulAut K₀ => (φ : K₀ → K₀))
    (fun φ ψ h => MulEquiv.ext (congrFun h))
  have hC : Cat8.innA K₀ c.a ⊓ centralizer ({c.a} : Set (MulAut K₀)) =
      centralizer ({c.a} : Set (MulAut K₀)) := by
    rw [show Cat8.innA K₀ c.a = ⊤ from htop, top_inf_eq]
  have hQS := c.Q_sylow
  rw [hC] at hQS
  have hQ2 : IsPGroup 2 c.Q := by
    obtain ⟨T, hT⟩ := hQS
    have h := T.isPGroup'
    rw [hT] at h
    exact h.of_equiv (subgroupOfEquivOfLe (c.Q_le.trans inf_le_right))
  obtain ⟨R, hR⟩ := (isPGroup_sup hQ2 c.g_norm c.g_sq).exists_le_sylow
  have hadm : Cat8.IsAdm K₀ c.a :=
    ⟨c.adm.sq, c.adm.out, by simpa [Cat8.ordL2] using c.adm.dvd⟩
  exact ⟨⟨c.a, c.Q, c.g, R, c.z, hadm, c.Q_le.trans inf_le_right, hQS, c.g_inn, c.g_norm,
    c.g_not_mem, c.g_sq, c.tau_inn, le_sup_right.trans hR, hR (mem_sup_left (mem_zpowers c.g)),
    ⟨R, rfl⟩, c.z_mem, c.z_comm, c.z_sq, c.z_ne⟩, rfl, rfl, rfl, rfl⟩

end Conf81

theorem cf81Conf :
    CF81Conf := by
  intro K₀ _ _ p f hp hp2 hf hK c
  rcases hK with hK | ⟨rfl, rfl, hA8⟩
  · exact ConfA.props_of_facts ((hp.odd_of_ne_two hp2).pow) c
      (ConfK.facts_psp hp hp2 hf hK c.a c.adm)
  · have hK' : IsSec8Socle K₀ 3 1 := Or.inr ⟨rfl, rfl, hA8⟩
    have hadm : Cat8.IsAdm K₀ c.a :=
      ⟨c.adm.sq, c.adm.out, by simpa [Cat8.ordL2] using c.adm.dvd⟩
    obtain ⟨c', ha, hQ, hg, hz⟩ := Conf81.exists_q3Conf c (CatFactsSmall.cfQ3Out K₀ hK' c.a hadm)
    have hP := CatFactsSmall.cfQ3Conf K₀ hK' c'
    obtain ⟨hD8, hQ32, -⟩ := hP.card_D
    have hQeq := hP.Q_eq
    have htau := hP.tau_comm
    have hgz := hP.g_z
    have hzt := hP.z_tau
    have hD : c'.D = c.D := by
      show c'.Q ⊓ Cat8.L0 K₀ c'.a = c.Q ⊓ Cat8.L0 K₀ c.a
      rw [ha, hQ]
    have hτ : c'.tau = c.tau := by
      show c'.a * (c'.g⁻¹ * c'.a * c'.g) = c.a * (c.g⁻¹ * c.a * c.g)
      rw [ha, hg]
    rw [hD] at hD8
    rw [hQ] at hQ32
    refine ⟨?_, by rw [hQ32, hD8], by rw [hD8], ?_, ?_, ?_⟩
    · rw [← hQ, hQeq, hD, hτ, ha]
    · rw [← hτ, ← hQ]
      exact htau
    · rw [← hg, ← hz]
      exact hgz
    · rw [← hτ, ← hz]
      exact hzt

end CFSG.ComponentClassification.GSThmB
