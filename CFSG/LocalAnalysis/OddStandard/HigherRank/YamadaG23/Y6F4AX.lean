module

public import CFSG.LocalAnalysis.OddStandard.HigherRank.YamadaG23.Y6F4AQ
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.ProdAut
public import Mathlib.GroupTheory.Subgroup.Simple

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

open Subgroup

open CFSG.EvenSporadicStandard.M24Std.ProdAut

private def Pres {A : Type*} [Group A] (α : MulAut (A × A)) : Prop :=
  (∀ x : A, (α (x, 1)).2 = 1) ∧ ∀ x : A, (α (1, x)).1 = 1

private def Swap {A : Type*} [Group A] (α : MulAut (A × A)) : Prop :=
  (∀ x : A, (α (x, 1)).1 = 1) ∧ ∀ x : A, (α (1, x)).2 = 1

private lemma pres_one {A : Type*} [Group A] : Pres (1 : MulAut (A × A)) := by
  constructor <;> intro x <;> rfl

private lemma pres_mul_pres {A : Type*} [Group A] {α β : MulAut (A × A)}
    (hα : Pres α) (hβ : Pres β) : Pres (α * β) := by
  constructor
  · intro x
    rw [MulAut.mul_apply]
    have hb : (β (x, 1)).2 = 1 := hβ.1 x
    have key : β (x, 1) = ((β (x, 1)).1, 1) := by ext <;> simp [hb]
    rw [key]
    exact hα.1 _
  · intro x
    rw [MulAut.mul_apply]
    have hb : (β (1, x)).1 = 1 := hβ.2 x
    have key : β (1, x) = (1, (β (1, x)).2) := by ext <;> simp [hb]
    rw [key]
    exact hα.2 _

private lemma swap_mul_swap {A : Type*} [Group A] {α β : MulAut (A × A)}
    (hα : Swap α) (hβ : Swap β) : Pres (α * β) := by
  constructor
  · intro x
    rw [MulAut.mul_apply]
    have hb : (β (x, 1)).1 = 1 := hβ.1 x
    have key : β (x, 1) = (1, (β (x, 1)).2) := by ext <;> simp [hb]
    rw [key]
    exact hα.2 _
  · intro x
    rw [MulAut.mul_apply]
    have hb : (β (1, x)).2 = 1 := hβ.2 x
    have key : β (1, x) = ((β (1, x)).1, 1) := by ext <;> simp [hb]
    rw [key]
    exact hα.1 _

private lemma pres_inv {A : Type*} [Group A] {α : MulAut (A × A)} (hα : Pres α) :
    Pres α⁻¹ := by
  obtain ⟨f₁, f₂, hf⟩ := exists_prod_preserve α hα.1 hα.2
  constructor
  · intro x
    obtain ⟨a, b, hab⟩ : ∃ a b, α⁻¹ (x, 1) = (a, b) :=
      ⟨(α⁻¹ (x, 1)).1, (α⁻¹ (x, 1)).2, by ext <;> rfl⟩
    rw [hab]
    have h1 : α (a, b) = (x, 1) := by rw [← hab]; simp
    rw [hf a b] at h1
    have h2 : f₂ b = 1 := (Prod.ext_iff.1 h1).2
    exact f₂.injective (by rw [h2, map_one])
  · intro x
    obtain ⟨a, b, hab⟩ : ∃ a b, α⁻¹ (1, x) = (a, b) :=
      ⟨(α⁻¹ (1, x)).1, (α⁻¹ (1, x)).2, by ext <;> rfl⟩
    rw [hab]
    have h1 : α (a, b) = (1, x) := by rw [← hab]; simp
    rw [hf a b] at h1
    have h2 : f₁ a = 1 := (Prod.ext_iff.1 h1).1
    exact f₁.injective (by rw [h2, map_one])

private lemma pow_apply_pres {A : Type*} [Group A] {α : MulAut (A × A)} {f₁ f₂ : MulAut A}
    (hf : ∀ a b : A, α (a, b) = (f₁ a, f₂ b)) :
    ∀ n : ℕ, ∀ a b : A, (α ^ n) (a, b) = ((f₁ ^ n) a, (f₂ ^ n) b) := by
  intro n
  induction n with
  | zero => intro a b; simp
  | succ n ih =>
      intro a b
      simp only [pow_succ, MulAut.mul_apply, hf, ih]

private lemma central_eq_one {A : Type*} [Group A] [IsSimpleGroup A]
    (hna : ¬ IsMulCommutative A) : ∀ a : A, (∀ c, a * c = c * a) → a = 1 := by
  intro a ha
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center A) with h | h
  · have hmem : a ∈ Subgroup.center A :=
      Subgroup.mem_center_iff.mpr fun c => (ha c).symm
    rw [h] at hmem
    exact Subgroup.mem_bot.mp hmem
  · exact absurd (Subgroup.center_eq_top_iff.mp h) hna

theorem y6f4a_no_z4cube_aut_prod {A : Type} [Group A] [Finite A] [IsSimpleGroup A]
    (hna : ¬ IsMulCommutative A) (h4 : ∀ α : MulAut A, α ^ 4 = 1 → α ^ 2 = 1) {M : Type}
    [Group M] (hM : Nonempty (M ≃* (Fin 3 → Multiplicative (ZMod 4)))) (ρ : M →* MulAut (A × A))
    (hρ : Function.Injective ρ) : False := by
  have hsimple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    haveI := hN
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
  have hcentral : ∀ a : A, (∀ c, a * c = c * a) → a = 1 := central_eq_one hna
  have hnt : ∃ s : A, s ≠ 1 := exists_ne (1 : A)
  have hcases : ∀ α : MulAut (A × A), Pres α ∨ Swap α :=
    fun α => mulAut_prod_cases hsimple hcentral hnt α
  let K : Subgroup M :=
    { carrier := {x | Pres (ρ x)}
      one_mem' := by
        show Pres (ρ 1)
        rw [map_one]
        exact pres_one
      mul_mem' := by
        intro a b ha hb
        show Pres (ρ (a * b))
        rw [map_mul]
        exact pres_mul_pres ha hb
      inv_mem' := by
        intro a ha
        show Pres (ρ a⁻¹)
        rw [map_inv]
        exact pres_inv ha }
  have hKmem : ∀ x : M, x ∈ K ↔ Pres (ρ x) := fun x => Iff.rfl
  have hKindex : K.index ≤ 2 := by
    by_cases htop : K = ⊤
    · rw [Subgroup.index_eq_one.mpr htop]
      norm_num
    · have hex : ∃ s : M, s ∉ K := by
        by_contra h
        push_neg at h
        exact htop (le_antisymm le_top fun x _ => h x)
      obtain ⟨s, hs⟩ := hex
      have hns : ¬ Pres (ρ s) := fun hp => hs ((hKmem s).mpr hp)
      have hidx2 : K.index = 2 := by
        rw [Subgroup.index_eq_two_iff_exists_notMem_and]
        refine ⟨s, hs, fun b => ?_⟩
        by_cases hb : b ∈ K
        · exact Or.inr hb
        · refine Or.inl ?_
          have hnb : ¬ Pres (ρ b) := fun hp => hb ((hKmem b).mpr hp)
          show Pres (ρ (b * s))
          rw [map_mul]
          rcases hcases (ρ b) with hpb | hpb
          · exact absurd hpb hnb
          · rcases hcases (ρ s) with hps | hps
            · exact absurd hps hns
            · exact swap_mul_swap hpb hps
      exact le_of_eq hidx2
  obtain ⟨e⟩ := hM
  have hMtop : Nonempty (↥(⊤ : Subgroup M) ≃* (Fin 3 → Multiplicative (ZMod 4))) :=
    ⟨Subgroup.topEquiv.trans e⟩
  have hidxrel : K.relIndex (⊤ : Subgroup M) ≤ 2 := by
    rw [Subgroup.relIndex_top_right]
    exact hKindex
  obtain ⟨x, hxK, -, hxord⟩ :=
    @y6f4a_exists_order_four M _ (⊤ : Subgroup M) K hMtop hidxrel
  have hpres : Pres (ρ x) := (hKmem x).mp hxK
  obtain ⟨f₁, f₂, hf⟩ := exists_prod_preserve (ρ x) hpres.1 hpres.2
  have hx4 : x ^ 4 = 1 := by
    rw [← hxord]
    exact pow_orderOf_eq_one x
  have hpx4 : ρ x ^ 4 = 1 := by
    rw [← map_pow, hx4, map_one]
  have hf1 : f₁ ^ 4 = 1 := by
    ext a
    have h1 : (ρ x ^ 4) (a, 1) = (a, 1) := by rw [hpx4]; rfl
    rw [pow_apply_pres hf 4 a 1] at h1
    simpa using (Prod.ext_iff.1 h1).1
  have hf2 : f₂ ^ 4 = 1 := by
    ext b
    have h1 : (ρ x ^ 4) (1, b) = (1, b) := by rw [hpx4]; rfl
    rw [pow_apply_pres hf 4 1 b] at h1
    simpa using (Prod.ext_iff.1 h1).2
  have hf1sq : f₁ ^ 2 = 1 := h4 f₁ hf1
  have hf2sq : f₂ ^ 2 = 1 := h4 f₂ hf2
  have hpx2 : ρ x ^ 2 = 1 := by
    apply MulEquiv.ext
    intro p
    rcases p with ⟨a, b⟩
    rw [pow_apply_pres hf 2 a b, hf1sq, hf2sq]
    rfl
  have hx2 : x ^ 2 = 1 := hρ (by rw [map_pow, hpx2, map_one])
  have hdvd : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one hx2
  rw [hxord] at hdvd
  exact absurd hdvd (by decide)

end CFSG.OddStandard.HigherRank.YamadaG23
