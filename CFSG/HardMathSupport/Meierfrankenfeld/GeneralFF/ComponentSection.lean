module

public import CFSG.HardMathSupport.Meierfrankenfeld.Coordinator.Interfaces
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Section
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.JNormalizesComponents

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules CFSG.Quasithin CFSG.QuasithinUnique.Setup
open CFSG.HardMathSupport.Meierfrankenfeld
open scoped commutatorElement

variable {X : Type*} [Group X]

theorem commutator_eq_of_ne_bot {K A : Subgroup X} (hK : CFSG.IsQuasisimple K)
    (hAK : A ≤ Subgroup.normalizer (K : Set X)) (h : ⁅K, A⁆ ≠ ⊥) : ⁅K, A⁆ = K := by
  have hle : ⁅K, A⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk a ha
    have h3 : a * k⁻¹ * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAK ha) k⁻¹).mp (K.inv_mem hk)
    have : ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact K.mul_mem hk h3
  have hnorm : ∀ k ∈ K, ∀ y ∈ ⁅K, A⁆, k * y * k⁻¹ ∈ ⁅K, A⁆ := by
    intro k hk y hy
    rw [Subgroup.commutator_comm] at hy ⊢
    exact commutator_conj_mem hk hy
  let N : Subgroup K := (⁅K, A⁆).subgroupOf K
  have hNn : N.Normal := ⟨fun n hn g => by
    change ((g : X) * (n : X) * (g : X)⁻¹ ∈ ⁅K, A⁆)
    exact hnorm g g.2 n hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hK hNn with hN | hN
  · refine le_antisymm hle fun k hk => ?_
    have : (⟨k, hk⟩ : K) ∈ N := by rw [hN]; trivial
    exact this
  · exfalso
    apply h
    have hKK : ⁅K, K⁆ = K := by
      have h1 := Subgroup.map_commutator (⊤ : Subgroup K) (⊤ : Subgroup K) K.subtype
      have h2 : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
        have := hK.1.commutator_eq_top
        rwa [commutator_def] at this
      rw [h2] at h1
      simpa [Subgroup.map_top, Subgroup.range_subtype] using h1.symm
    have hc : ⁅K, A⁆ ≤ Subgroup.centralizer (K : Set X) := by
      intro y hy k hk
      have hyK : y ∈ K := hle hy
      have hyN : (⟨y, hyK⟩ : K) ∈ N := hy
      have hz := Subgroup.mem_center_iff.mp (hN hyN) ⟨k, hk⟩
      exact congrArg Subtype.val hz
    have h1 : ⁅⁅K, A⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hc
    have h2 : ⁅⁅A, K⁆, K⁆ = ⊥ := by rw [Subgroup.commutator_comm A K]; exact h1
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hKK] at h3


theorem componentSectionProp : Coordinator.ComponentSectionProp := by
  intro X _ _ W _ _ _ ρ hρ _ A hAel hAbest K hK hKA
  have hKc : CFSG.IsComponent K := (CFSG.isComponent_iff_open K).mpr hK
  have hKq : CFSG.IsQuasisimple ↥K := hKc.1
  have hAn : A ≤ Subgroup.normalizer (K : Set X) := fun a ha =>
    bestOffenderSub_le_normalizer_component ρ hρ hKc (le_bestOffenderSub hAel hAbest ha)
  have hKA' : ⁅K, A⁆ = K := commutator_eq_of_ne_bot hKq hAn hKA
  have hfaith : ∀ x : X, (∀ w, ρ x w = w) → x = 1 := fun x hx =>
    hρ (by ext w; simp [hx w])
  have hK0 : K ≠ ⊥ := fun h => hKA (by rw [h]; simp)
  have hKnt : ¬ K ≤ cenOn ρ K ⊤ := fun h => hK0 (eq_bot_iff.mpr fun k hk =>
    (Subgroup.mem_bot).mpr (hfaith k fun w => (h hk).2 w Submodule.mem_top))
  have hb : IsBestOffenderOn ρ A ⊤ :=
    (isBestOffender_iff_on ρ A (fun a _ ha => hfaith a ha)).mp ⟨hAel, hAbest⟩
  obtain ⟨W', hW'1, hW'2, Lb, Eb, hsq, hirr, hq, hE0, hEel, hEq, hEN, hoff, ψ, hψ⟩ :=
    exists_irrSection ρ K A hKq hAel hAn hKA' hKnt hb
  have hrange : (Lb.subtype.comp ψ).range = Lb := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, Subgroup.map_top,
      Subgroup.range_subtype]
  refine ⟨W', hW'1, hW'2, Lb.subtype.comp ψ, Eb, hsq, ?_, ?_, ?_, hE0, hEel, hEq, hoff⟩
  · rw [hrange]
    have := CFSG.LocalCores.isQuasisimple_nontrivial hq
    exact (Subgroup.nontrivial_iff_ne_bot Lb).mp inferInstance
  · rw [hrange]; exact hirr
  · rw [hrange]; exact hEN

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
