module

public import CFSG.LocalAnalysis.ComponentClassification.GHarrisEF
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisL31b
public import CFSG.LocalAnalysis.ComponentClassification.GHarrisSTransport

public noncomputable section

namespace CFSG.ComponentClassification.GHarris

open CFSG Subgroup SCert CFSG.ABGLocalTools

variable {G : Type} [Group G]

namespace GHSylow

variable (D : GHSylow G)

abbrev M : Subgroup G := centralizer ({D.z} : Set G)

abbrev E : Subgroup G := SE.Esub.map D.toG

abbrev F : Subgroup G := SE.Fsub.map D.toG

theorem toG_mem_E_iff {s : SE} : D.toG s ∈ D.E ↔ SE.predE s := D.mem_map_toG

theorem toG_mem_F_iff {s : SE} : D.toG s ∈ D.F ↔ SE.predF s := D.mem_map_toG

theorem E_le_S : D.E ≤ (D.S : Subgroup G) := by
  rintro _ ⟨s, -, rfl⟩
  exact D.toG_mem s

theorem F_le_S : D.F ≤ (D.S : Subgroup G) := by
  rintro _ ⟨s, -, rfl⟩
  exact D.toG_mem s

theorem S_le_M : (D.S : Subgroup G) ≤ D.M := D.S_le_centralizer_z

theorem conj_mem_E {s e : G} (hs : s ∈ (D.S : Subgroup G)) (he : e ∈ D.E) : s⁻¹ * e * s ∈ D.E := by
  obtain ⟨s₀, rfl⟩ := D.exists_toG hs
  obtain ⟨e₀, he₀, rfl⟩ := he
  refine ⟨s₀⁻¹ * e₀ * s₀, ?_, by simp only [map_mul, map_inv]⟩
  have := SE.Esub_normal.conj_mem e₀ he₀ s₀⁻¹
  rwa [inv_inv] at this

theorem conj_mem_F {s f : G} (hs : s ∈ (D.S : Subgroup G)) (hf : f ∈ D.F) : s⁻¹ * f * s ∈ D.F := by
  obtain ⟨s₀, rfl⟩ := D.exists_toG hs
  obtain ⟨f₀, hf₀, rfl⟩ := hf
  refine ⟨s₀⁻¹ * f₀ * s₀, ?_, by simp only [map_mul, map_inv]⟩
  have := SE.Fsub_normal.conj_mem f₀ hf₀ s₀⁻¹
  rwa [inv_inv] at this

theorem mem_E_or_F {w : G} (hw : w ∈ (D.S : Subgroup G)) (hw2 : w * w = D.z) :
    w ∈ D.E ∨ w ∈ D.F := by
  obtain ⟨w₀, rfl⟩ := D.exists_toG hw
  have h : w₀ * w₀ = SE.gen 0 := D.toG_injective (by rw [map_mul, hw2])
  rcases SE.sq_eq_z_cases w₀ h with h' | h'
  · exact Or.inl ((D.toG_mem_E_iff).mpr h')
  · exact Or.inr ((D.toG_mem_F_iff).mpr h')

theorem exists_conj_fun {g : G} {p : SE → Prop}
    (hS : ∀ s : SE, p s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G)) :
    ∃ f : SE → SE, ∀ s : SE, p s → D.toG (f s) = g⁻¹ * D.toG s * g := by
  choose f hf using fun s => (Classical.em (p s)).elim
    (fun hs => (D.exists_toG (hS s hs)).imp fun s' h' _ => h') fun hs => ⟨s, fun h => absurd h hs⟩
  exact ⟨f, hf⟩

theorem conj_le_E_or_F {g : G} (hg : g ∈ D.M) {p q : SE → Prop}
    (hpq : ∀ s, q s → p s) (hq2 : ∀ s, q s → s * s = SE.gen 0)
    (hcomm : ∀ u v, q u → q v → SE.commZ u v)
    (hcov : ∀ s, p s → q s ∨ ∃ u v, q u ∧ q v ∧ s = u * v)
    (hS : ∀ s : SE, p s → g⁻¹ * D.toG s * g ∈ (D.S : Subgroup G)) :
    (∀ s : SE, p s → g⁻¹ * D.toG s * g ∈ D.E) ∨ ∀ s : SE, p s → g⁻¹ * D.toG s * g ∈ D.F := by
  obtain ⟨f, hf⟩ := D.exists_conj_fun hS
  have hgz : g⁻¹ * D.z * g = D.z := by
    have := mem_centralizer_singleton_iff.mp hg
    calc g⁻¹ * D.z * g = g⁻¹ * (D.z * g) := by group
      _ = g⁻¹ * (g * D.z) := by rw [this]
      _ = D.z := by group
  have hsq : ∀ u, q u → f u * f u = SE.gen 0 := by
    intro u hu
    apply D.toG_injective
    rw [map_mul, hf u (hpq u hu)]
    calc g⁻¹ * D.toG u * g * (g⁻¹ * D.toG u * g) = g⁻¹ * D.toG (u * u) * g := by
          rw [map_mul]; group
      _ = D.toG (SE.gen 0) := by rw [hq2 u hu]; exact hgz
  have hEF : ∀ u, q u → SE.predE (f u) ∨ SE.predF (f u) := fun u hu =>
    SE.sq_eq_z_cases _ (hsq u hu)
  have hcz : ∀ u v, q u → q v → SE.commZ (f u) (f v) := by
    intro u v hu hv
    have hc := hcomm u v hu hv
    have key : D.toG (SE.comm (f u) (f v)) = g⁻¹ * D.toG (SE.comm u v) * g := by
      simp only [SE.comm, map_mul, map_inv]
      rw [hf u (hpq u hu), hf v (hpq v hv)]
      group
    rcases hc with h | h
    · left
      apply D.toG_injective
      rw [key, h, map_one]
      group
    · right
      apply D.toG_injective
      rw [key, h]
      exact hgz
  have hmul : ∀ s u v, p s → q u → q v → s = u * v → f s = f u * f v := by
    intro s u v hs hu hv hsuv
    apply D.toG_injective
    rw [map_mul, hf s hs, hf u (hpq u hu), hf v (hpq v hv), hsuv, map_mul]
    group
  by_cases hall : ∀ u, q u → SE.predE (f u)
  · left
    intro s hs
    rw [← hf s hs, D.toG_mem_E_iff]
    rcases hcov s hs with h | ⟨u, v, hu, hv, rfl⟩
    · exact hall s h
    · rw [hmul _ u v hs hu hv rfl]
      exact SE.Esub.mul_mem (hall u hu) (hall v hv)
  · right
    push Not at hall
    obtain ⟨u, hu, huE⟩ := hall
    have huF : SE.predF (f u) := (hEF u hu).resolve_left huE
    have hallF : ∀ v, q v → SE.predF (f v) := by
      intro v hv
      by_contra hvF
      have hvE : SE.predE (f v) := (hEF v hv).resolve_right hvF
      exact SE.not_commZ_mixed (f v) (f u) ⟨hvE, hsq v hv⟩ hvF ⟨huF, hsq u hu⟩ huE
        (hcz v u hv hu)
    intro s hs
    rw [← hf s hs, D.toG_mem_F_iff]
    rcases hcov s hs with h | ⟨u, v, hu, hv, rfl⟩
    · exact hallF s h
    · rw [hmul _ u v hs hu hv rfl]
      exact SE.Fsub.mul_mem (hallF u hu) (hallF v hv)

theorem conj_E_le_E_or_F {g : G} (hg : g ∈ D.M)
    (hS : ∀ e ∈ D.E, g⁻¹ * e * g ∈ (D.S : Subgroup G)) :
    (∀ e ∈ D.E, g⁻¹ * e * g ∈ D.E) ∨ ∀ e ∈ D.E, g⁻¹ * e * g ∈ D.F := by
  rcases D.conj_le_E_or_F hg (p := SE.predE) (q := SE.O4E) (fun s h => h.1) (fun s h => h.2)
      (fun u v hu hv => SE.commZ_E u v hu.1 hv.1) SE.gen_E
      (fun s hs => hS _ ⟨s, hs, rfl⟩) with h | h
  · left
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  · right
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs

theorem conj_F_le_E_or_F {g : G} (hg : g ∈ D.M)
    (hS : ∀ f ∈ D.F, g⁻¹ * f * g ∈ (D.S : Subgroup G)) :
    (∀ f ∈ D.F, g⁻¹ * f * g ∈ D.E) ∨ ∀ f ∈ D.F, g⁻¹ * f * g ∈ D.F := by
  rcases D.conj_le_E_or_F hg (p := SE.predF) (q := SE.O4F) (fun s h => h.1) (fun s h => h.2)
      (fun u v hu hv => SE.commZ_F u v hu.1 hv.1) SE.gen_F
      (fun s hs => hS _ ⟨s, hs, rfl⟩) with h | h
  · left
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs
  · right
    rintro _ ⟨s, hs, rfl⟩
    exact h s hs

end GHSylow

end CFSG.ComponentClassification.GHarris
