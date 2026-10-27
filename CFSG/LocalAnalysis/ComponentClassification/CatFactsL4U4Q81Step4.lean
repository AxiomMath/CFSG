module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Graph
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndTransfer

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Setting46e

variable {S : Subgroup X} {w z : X} {V : Subgroup X} {i₀ j₀ : ℕ}

theorem not_isSylowOf_top [IsSimpleGroup X] (hnab : ∃ a b : X, a * b ≠ b * a)
    (hs : Setting46e t L 3 4 S w z V i₀ j₀)
    (hQ : ∀ i j : ℕ, IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
      (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∨
        Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1) →
      hs.setup.Q81Data i j)
    {i j : ℕ} (hD : hs.setup.Q81Data i j)
    (hβt : ∀ c : X, c * t * c⁻¹ ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j) {W : Subgroup X}
    (hWM : W ≤ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) (hWp : IsPGroup 2 W)
    (htW : t ∈ W) : ¬ IsSylowOf 2 W ⊤ := by
  intro hWS
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨I, hI⟩ := Q81.exists_isInnDiag hD.quasisimple hD.center_cases
  have hEn : (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).Normal := by
    have := LocalCores.layer_characteristic (G := MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))
    infer_instance
  have hN : ∀ y : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j), y ∈ normalizer
      ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) : Subgroup _) : Set _) := by
    intro y
    rw [normalizer_eq_top_iff.mpr hEn]
    exact mem_top _
  set P : Subgroup X := (I.comap (QuotientGroup.mk' (pPrimeCore 2 ↥(centralizer
    ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))))).map (centralizer
      ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)).subtype with hP
  have hmemP : ∀ x : X, ∀ hx : x ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X),
      x ∈ P ↔ (QuotientGroup.mk ⟨x, hx⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∈ I := by
    intro x hx
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro h1
      exact ⟨⟨x, hx⟩, h1, rfl⟩
  have htM := hWM htW
  have htP : t ∉ P := by
    rw [hmemP t htM]
    exact hD.graph I hI
  have hrel : (W ⊓ P).relIndex W = 2 := by
    rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
    refine ⟨⟨t, htW⟩, fun b => ?_⟩
    simp only [mem_subgroupOf, Subgroup.coe_mul, mem_inf]
    have hbM := hWM b.2
    by_cases hb : (b : X) ∈ P
    · right
      refine ⟨⟨b.2, hb⟩, fun ⟨_, hbt⟩ => htP ?_⟩
      have h1 : t = (b : X)⁻¹ * (b * t) := by group
      rw [h1]
      exact mul_mem (inv_mem hb) hbt
    · left
      refine ⟨⟨mul_mem b.2 htW, ?_⟩, fun ⟨_, h1⟩ => hb h1⟩
      rw [hmemP _ (mul_mem hbM htM)]
      have h2 := hI.mul_mem _ (hN _) _ (hN _) ((hmemP _ hbM).not.mp hb) (hD.graph I hI)
      exact h2
  have hWidx : ¬ 2 ∣ W.index := by
    have h1 := ((isSylowOf_iff (p := 2)).mp hWS).2.2
    rwa [Subgroup.relIndex_top_right] at h1
  have ht2 : t ^ 2 = 1 := by rw [← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  obtain ⟨g, hgX₀, -, -⟩ := HarrisEnd.exists_extremal_conj_of_relIndex_two hnab hWp hWidx
    inf_le_left hrel htW (fun h1 => htP (mem_inf.mp h1).2) ht2
  have hgM : g⁻¹ * t * g⁻¹⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) := by
    rw [inv_inv]
    exact hWM (mem_inf.mp hgX₀).1
  have hgP : g⁻¹ * t * g⁻¹⁻¹ ∈ P := by
    rw [inv_inv]
    exact (mem_inf.mp hgX₀).2
  exact hs.mk_conj_t_not_mem hQ hD hβt hgM hI ((hmemP _ hgM).mp hgP)

end Setting46e

end CFSG.ComponentClassification.HarrisLit
