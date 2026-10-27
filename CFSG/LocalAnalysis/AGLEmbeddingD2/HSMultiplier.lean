module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.RankThree.PartTwo.Sec4.Census

theorem card_ker_inf_commutator_dvd_hopfMultiplier {Γ T : Type} [Group Γ] [Finite Γ] [Group T]
    (hT : Group.IsPerfect T) (φ : Γ →* T) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Γ) :
    Nat.card ↥(φ.ker ⊓ commutator Γ) ∣
      Nat.card (CFSG.RankThree.PerfectCover.hopfMultiplier T) := by
  set E := commutator Γ with hE
  have hmapE : E.map φ = ⊤ := by
    rw [hE, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective φ hφ,
      ← commutator_def]
    exact hT.commutator_eq_top
  have hsup : E ⊔ φ.ker = ⊤ := by
    have h := Subgroup.comap_map_eq φ E
    rw [hmapE, Subgroup.comap_top] at h
    exact h.symm
  have hcen : ∀ A : Subgroup Γ, ⁅φ.ker, A⁆ = ⊥ := fun A =>
    le_bot_iff.mp ((Subgroup.commutator_mono hker le_rfl).trans
      (Subgroup.commutator_center_left A).le)
  have hcen' : ∀ A : Subgroup Γ, ⁅A, φ.ker⁆ = ⊥ := fun A =>
    (Subgroup.commutator_comm A φ.ker).trans (hcen A)
  have hEE : ⁅E, E⁆ = E := by
    have h1 : ⁅E ⊔ φ.ker, E ⊔ φ.ker⁆ = E := by
      rw [hsup]
      exact (commutator_def Γ).symm
    simpa only [Subgroup.commutator_sup_right, Subgroup.commutator_sup_left, hcen, hcen',
      sup_bot_eq] using h1
  have hEp : Group.IsPerfect E := Subgroup.isPerfect_iff.mpr hEE
  let q : E →* T := φ.comp E.subtype
  have hq : Function.Surjective q := by
    intro t
    have ht : t ∈ E.map φ := hmapE ▸ Subgroup.mem_top t
    obtain ⟨g, hg, rfl⟩ := ht
    exact ⟨⟨g, hg⟩, rfl⟩
  have hqker : q.ker ≤ Subgroup.center E := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hx' : (x : Γ) ∈ Subgroup.center Γ := hker hx
    exact Subtype.ext ((Subgroup.mem_center_iff.mp hx') y)
  have hdvd := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hEp q hq hqker
  have hcard : Nat.card q.ker = Nat.card ↥(φ.ker ⊓ E) := by
    refine Nat.card_congr
      { toFun := fun x => ⟨(x : E), x.2, (x : E).2⟩
        invFun := fun y => ⟨⟨y, y.2.2⟩, y.2.1⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rwa [hcard] at hdvd

theorem isPerfect_of_isSimpleGroup_of_not_prime {B : Type} [Group B] [IsSimpleGroup B]
    (hB : ¬ (Nat.card B).Prime) : Group.IsPerfect B := by
  have hnab : ∃ a b : B, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup B := { (inferInstance : Group B) with mul_comm := hc }
    exact hB (IsSimpleGroup.prime_card (α := B))
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator B) with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ commutator B := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h1, Subgroup.mem_bot] at h2
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · exact h1

end CFSG.AGLEmbeddingD2
