module

public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.StrictMin
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Replacement

public section

namespace CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

open CFSG.RankThree.FFModules
open scoped commutatorElement

variable {G : Type*} [Group G] {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
variable {ρ : Representation (ZMod 2) G V}

theorem commOn_eq_bot_iff {A : Subgroup G} {U : Submodule (ZMod 2) V} :
    commOn ρ A U = ⊥ ↔ ∀ a ∈ A, ∀ u ∈ U, ρ a u = u := by
  constructor
  · intro h a ha u hu
    have : ρ a u - u ∈ commOn ρ A U := Submodule.subset_span ⟨a, ha, u, hu, rfl⟩
    rw [h, Submodule.mem_bot, sub_eq_zero] at this
    exact this
  · intro h
    rw [eq_bot_iff, commOn, Submodule.span_le]
    rintro w ⟨a, ha, u, hu, rfl⟩
    simp [h a ha u hu]

theorem le_cenOn_iff_commOn_eq_bot {A : Subgroup G} {U : Submodule (ZMod 2) V} :
    A ≤ cenOn ρ A U ↔ commOn ρ A U = ⊥ := by
  rw [commOn_eq_bot_iff]
  exact ⟨fun h a ha u hu => (h ha).2 u hu, fun h a ha => ⟨ha, h a ha⟩⟩

theorem commOn_top_mapsTo {K : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (K : Set G))
    {w : V} (hw : w ∈ commOn ρ K ⊤) : ρ g w ∈ commOn ρ K ⊤ := by
  refine Submodule.span_induction (p := fun w _ => ρ g w ∈ commOn ρ K ⊤) ?_ ?_ ?_ ?_ hw
  · rintro _ ⟨k, hk, u, -, rfl⟩
    have hk' : g * k * g⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hg k).mp hk
    have : ρ g (ρ k u - u) = ρ (g * k * g⁻¹) (ρ g u) - ρ g u := by
      rw [map_sub, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      have : ρ g⁻¹ (ρ g u) = u := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]; rfl
      rw [this]
    rw [this]
    exact Submodule.subset_span ⟨_, hk', _, Submodule.mem_top, rfl⟩
  · simp
  · intro x y _ _ hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy
  · intro c x _ hx
    rw [map_smul]
    exact Submodule.smul_mem _ _ hx

theorem isInvariant_commOn_top {K H : Subgroup G} (h : H ≤ Subgroup.normalizer (K : Set G)) :
    IsInvariant ρ H (commOn ρ K ⊤) := fun _ hg _ hu => commOn_top_mapsTo (h hg) hu


theorem exists_strictMin_moving [Finite G] [Finite V] (K A : Subgroup G)
    (hA2 : CFSG.IsElementaryAbelian 2 A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKA : ⁅K, A⁆ = K) (hKnt : ¬ K ≤ cenOn ρ K ⊤) (hb : IsBestOffenderOn ρ A ⊤) :
    ∃ B : Subgroup G, B ≤ A ∧
      IsInvariant ρ (K ⊔ B) (commOn ρ K ⊤) ∧
      ¬ K ≤ cenOn ρ K (commOn ρ K ⊤) ∧
      ¬ B ≤ cenOn ρ B (commOn ρ K ⊤) ∧
      IsBestOffenderOn ρ B (commOn ρ K ⊤) ∧ IsQuadraticOn ρ B (commOn ρ K ⊤) ∧
      (∀ b ∈ B, b ∉ cenOn ρ B (commOn ρ K ⊤) →
        ∃ k ∈ K, ∃ u ∈ commOn ρ K ⊤, ρ b (ρ k u) ≠ ρ k (ρ b u)) ∧
      (∀ B' : Subgroup G, cenOn ρ B (commOn ρ K ⊤) ≤ B' → B' < B →
        ¬ B' ≤ cenOn ρ B (commOn ρ K ⊤) →
          Nat.card B' * Nat.card (fixOn ρ B' (commOn ρ K ⊤)) <
            Nat.card B * Nat.card (fixOn ρ B (commOn ρ K ⊤))) := by
  classical
  set U := commOn ρ K ⊤ with hU
  have hKn : K ≤ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer
  have hAU : IsInvariant ρ A U := isInvariant_commOn_top hAK
  have hbU : IsBestOffenderOn ρ A U := hb.restrict le_top
  have hKU : ¬ K ≤ cenOn ρ K U := by
    intro hle
    apply hKnt
    have h1 : commOn ρ K U = ⊥ := le_cenOn_iff_commOn_eq_bot.mp hle
    have h2 := commOn_commOn_eq (ρ := ρ) hA2 hAK hKA
    rw [← hU, h1] at h2
    exact le_cenOn_iff_commOn_eq_bot.mpr h2.symm
  have hUK : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ u ∈ U, ρ g u ∈ U :=
    fun g hg u hu => commOn_top_mapsTo hg hu
  have hAnt : commOn ρ A U ≠ ⊥ := by
    intro h
    apply hKU
    have hA : ∀ a ∈ A, ∀ u ∈ U, ρ a u = u := commOn_eq_bot_iff.mp h
    have hcomm : ∀ k ∈ K, ∀ a ∈ A, ∀ u ∈ U, ρ (k * a * k⁻¹ * a⁻¹) u = u := by
      intro k hk a ha u hu
      have h1 : ρ a⁻¹ u = u := hA a⁻¹ (A.inv_mem ha) u hu
      have hu' : ρ k⁻¹ u ∈ U := hUK k⁻¹ (hKn (K.inv_mem hk)) u hu
      have h2 : ρ a (ρ k⁻¹ u) = ρ k⁻¹ u := hA a ha _ hu'
      simp only [map_mul, Module.End.mul_apply, h1, h2]
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    have hle : ⁅K, A⁆ ≤ cenOn ρ K U := by
      rw [Subgroup.commutator_le]
      intro k hk a ha
      refine ⟨?_, fun u hu => hcomm k hk a ha u hu⟩
      have h3 : a * k⁻¹ * a⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAK ha) k⁻¹).mp (K.inv_mem hk)
      have : ⁅k, a⁆ = k * (a * k⁻¹ * a⁻¹) := by simp only [commutatorElement_def]; group
      rw [this]
      exact K.mul_mem hk h3
    rw [hKA] at hle
    exact hle
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := timmesfeld_replacement_on ρ A U hAU hbU
  set A' : Subgroup G := cenOn ρ A (commOn ρ A U) with hA'
  have hA'A : A' ≤ A := cenOn_le ρ A _
  have hA'nt : commOn ρ A' U ≠ ⊥ := h5 hAnt
  have hne : ¬ A' ≤ cenOn ρ A' U := fun h => hA'nt (le_cenOn_iff_commOn_eq_bot.mp h)
  obtain ⟨B, hBA', hCB, hBC, hBw, hBbest, hBcen, hstrict⟩ := exists_strictMin_offender h4 hne
  have hBA : B ≤ A := hBA'.trans hA'A
  refine ⟨B, hBA, ?_, hKU, ?_, hBbest, ?_, ?_, ?_⟩
  · exact isInvariant_commOn_top (sup_le hKn (hBA.trans hAK))
  · rwa [hBcen]
  · intro w hw b hb
    have hw' : w ∈ commOn ρ A' U := commOn_mono_left hBA' hw
    exact (h6 b (hBA hb) w hw')
  · intro b hb hbc
    by_contra hcon
    push Not at hcon
    have hbcent : ∀ k ∈ K, ∀ w ∈ commOn ρ K ⊤, ρ b (ρ k w) = ρ k (ρ b w) := hcon
    have hbA' : b ∈ A' := hBA' hb
    have hbcen : b ∈ cenOn ρ A (commOn ρ A (commOn ρ K ⊤)) := hbA'
    have hbA : b ∈ A := hBA hb
    have := ms1_two_nine (ρ := ρ) hA2 hAK hKA b hbA hbcent hbcen
    exact hbc ⟨hb, fun u hu => this u hu⟩
  · intro B' hCB' hB'B hB'C
    rw [hBcen] at hCB' hB'C
    have := hstrict B' hCB' hB'B hB'C
    rw [← hBw] at this
    exact this

end CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
