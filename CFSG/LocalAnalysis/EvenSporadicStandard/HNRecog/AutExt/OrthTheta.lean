module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HNRecog.AutExt.OrthFin

public section

namespace CFSG.EvenSporadicStandard.HNRecog.Section4

open Equiv Equiv.Perm

private lemma zmod2_eq_one_of_ne_zero (a : ZMod 2) (ha : a ≠ 0) : a = 1 := by
  revert a
  decide +kernel

private lemma sum_one_fin5 : (∑ _i : Fin 5, (1 : ZMod 2)) = 1 := by
  decide +kernel

private lemma fv5Even_add_one {f : Fv5} (hf : ¬ Fv5Even f) : Fv5Even (f + fv5One) := by
  have hf' : (∑ i, f i) ≠ 0 := hf
  have h1 : (∑ i, f i) = 1 := zmod2_eq_one_of_ne_zero _ hf'
  have hsum : (∑ i, (f + fv5One) i) = 1 + 1 := by
    simp only [Pi.add_apply, fv5One]
    rw [Finset.sum_add_distrib, sum_one_fin5, h1]
  change (∑ i, (f + fv5One) i) = 0
  rw [hsum]
  decide +kernel

private lemma exists_even_preimage {G : Type} [Group G] {M : Subgroup G} {π : Fv5 → G}
    (hπadd : ∀ f g, π (f + g) = π f * π g) (hπone : π fv5One = 1)
    (hπsurj : ∀ x ∈ M, ∃ f, π f = x) (x : G) (hx : x ∈ M) :
    ∃ f, Fv5Even f ∧ π f = x := by
  obtain ⟨f, hf⟩ := hπsurj x hx
  by_cases hfe : Fv5Even f
  · exact ⟨f, hfe, hf⟩
  · exact ⟨f + fv5One, fv5Even_add_one hfe, by rw [hπadd, hπone, mul_one, hf]⟩

private lemma natCard_even : Nat.card {f : Fv5 // Fv5Even f} = 16 := by
  calc Nat.card {f : Fv5 // Fv5Even f}
      = Fintype.card {f : Fv5 // Fv5Even f} := Nat.card_eq_fintype_card
    _ = (Finset.univ.filter fun e : Fv5 => Fv5Even e).card :=
        Fintype.card_of_subtype _ (fun x => by simp)
    _ = 16 := card_fv5Even

private lemma even_injective {G : Type} [Group G] {M : Subgroup G} {π : Fv5 → G}
    (hM16 : Nat.card ↥M = 16) (hπM : ∀ f, π f ∈ M)
    (hπadd : ∀ f g, π (f + g) = π f * π g) (hπone : π fv5One = 1)
    (hπsurj : ∀ x ∈ M, ∃ f, π f = x) :
    ∀ f g : Fv5, Fv5Even f → Fv5Even g → π f = π g → f = g := by
  classical
  let F : {f : Fv5 // Fv5Even f} → ↥M := fun f => ⟨π f.1, hπM f.1⟩
  have hFsurj : Function.Surjective F := by
    intro y
    obtain ⟨f, hf, hfx⟩ := exists_even_preimage hπadd hπone hπsurj y.1 y.2
    exact ⟨⟨f, hf⟩, Subtype.ext hfx⟩
  have hcard : Nat.card {f : Fv5 // Fv5Even f} = Nat.card ↥M := by
    rw [natCard_even, hM16]
  have hbij : Function.Bijective F :=
    hFsurj.bijective_of_nat_card_le (le_of_eq hcard)
  intro f g hf hg hfg
  have hFfg : F ⟨f, hf⟩ = F ⟨g, hg⟩ := Subtype.ext hfg
  exact congrArg Subtype.val (hbij.1 hFfg)

theorem exists_orthTheta {G : Type} [Group G] {K M : Subgroup G} {ρ : ↥K →* Perm (Fin 5)}
    {π : Fv5 → G} (hM16 : Nat.card ↥M = 16) (hπM : ∀ f, π f ∈ M)
    (hπadd : ∀ f g, π (f + g) = π f * π g) (hπone : π fv5One = 1)
    (hπsurj : ∀ x ∈ M, ∃ f, π f = x)
    (hπconj : ∀ (l : ↥K) (f : Fv5), (l : G) * π f * (l : G)⁻¹ = π (fv5Act (ρ l) f)) :
    ∃ θ : G → Fv5, (∀ x ∈ M, ∀ y ∈ M, θ (x * y) = θ x + θ y) ∧ (∀ x ∈ M, Fv5Even (θ x)) ∧
      (∀ x ∈ M, ∀ y ∈ M, θ x = θ y → x = y) ∧ (∀ e : Fv5, Fv5Even e → ∃ x ∈ M, θ x = e) ∧
      ∀ (l : ↥K) (x : G), x ∈ M → θ ((l : G) * x * (l : G)⁻¹) = fv5Act (ρ l) (θ x) := by
  classical
  haveI : Nonempty Fv5 := ⟨(0 : Fv5)⟩
  let θ : G → Fv5 := Function.invFunOn π {f | Fv5Even f}
  have hex : ∀ x ∈ M, ∃ f, f ∈ {f | Fv5Even f} ∧ π f = x := by
    intro x hx
    obtain ⟨f, hf, hfx⟩ := exists_even_preimage hπadd hπone hπsurj x hx
    exact ⟨f, hf, hfx⟩
  have hθeven : ∀ x ∈ M, Fv5Even (θ x) := by
    intro x hx
    exact Function.invFunOn_mem (hex x hx)
  have hθπ : ∀ x ∈ M, π (θ x) = x := by
    intro x hx
    exact Function.invFunOn_eq (hex x hx)
  have hθuniq : ∀ x ∈ M, ∀ f : Fv5, Fv5Even f → π f = x → θ x = f := by
    intro x hx f hf hfx
    exact even_injective hM16 hπM hπadd hπone hπsurj (θ x) f (hθeven x hx) hf
      ((hθπ x hx).trans hfx.symm)
  refine ⟨θ, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx y hy
    exact hθuniq (x * y) (M.mul_mem hx hy) (θ x + θ y)
      (fv5Even_add (hθeven x hx) (hθeven y hy))
      (by rw [hπadd, hθπ x hx, hθπ y hy])
  · intro x hx
    exact hθeven x hx
  · intro x hx y hy hxy
    rw [← hθπ x hx, ← hθπ y hy, hxy]
  · intro e he
    exact ⟨π e, hπM e, hθuniq (π e) (hπM e) e he rfl⟩
  · intro l x hx
    have hmem : (l : G) * x * (l : G)⁻¹ ∈ M := by
      obtain ⟨f, hf⟩ := hπsurj x hx
      rw [← hf, hπconj l f]
      exact hπM (fv5Act (ρ l) f)
    exact hθuniq ((l : G) * x * (l : G)⁻¹) hmem (fv5Act (ρ l) (θ x))
      (fv5Act_even (hθeven x hx))
      (by rw [← hπconj l (θ x), hθπ x hx])

end CFSG.EvenSporadicStandard.HNRecog.Section4
