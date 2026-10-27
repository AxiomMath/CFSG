module

public import Mathlib.GroupTheory.Solvable
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic.Group

public section

namespace CFSG.EvenSporadicStandard.Induction.AutBound

open Subgroup

variable {P : Type*} [Group P] (X : Subgroup P)

theorem normalizerMonoidHom_injective
    (hC : ∀ c : P, (∀ x ∈ X, c * x = x * c) → c = 1) :
    Function.Injective (X.normalizerMonoidHom) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro n hn
  rw [normalizerMonoidHom_ker] at hn
  have h : (n : P) = 1 := hC _ fun x hx => (mem_centralizer_iff.1 (mem_subgroupOf.1 hn) x hx).symm
  exact Subtype.ext h

theorem normalizerMonoidHom_bijective [Finite P]
    (hC : ∀ c : P, (∀ x ∈ X, c * x = x * c) → c = 1)
    (hcard : Nat.card (MulAut X) ≤ Nat.card (normalizer (X : Set P))) :
    Function.Bijective (X.normalizerMonoidHom) := by
  have : Finite (MulAut X) :=
    Finite.of_injective (fun α : MulAut X => α.toEquiv) fun α β h => MulEquiv.ext fun x =>
      congrFun (congrArg DFunLike.coe h) x
  exact (Function.Injective.bijective_of_nat_card_le (normalizerMonoidHom_injective X hC)
    hcard)

theorem exists_conj_of_mulAut [Finite P] (hC : ∀ c : P, (∀ x ∈ X, c * x = x * c) → c = 1)
    (hcard : Nat.card (MulAut X) ≤ Nat.card (normalizer (X : Set P))) (α : MulAut X) :
    ∃ n : normalizer (X : Set P), X.normalizerMonoidHom n = α := by
  obtain ⟨n, hn⟩ := (normalizerMonoidHom_bijective X hC hcard).2 α
  exact ⟨n, hn⟩

theorem sq_eq_one_of_aut_sq_eq_one (hC : ∀ c : P, (∀ x ∈ X, c * x = x * c) → c = 1)
    {n : normalizer (X : Set P)} (h : X.normalizerMonoidHom n * X.normalizerMonoidHom n = 1) :
    n * n = 1 :=
  normalizerMonoidHom_injective X hC (by rw [map_mul, h, map_one])

theorem ne_one_of_aut_ne_one {n : normalizer (X : Set P)} (h : X.normalizerMonoidHom n ≠ 1) :
    n ≠ 1 := fun hn => h (by rw [hn, map_one])

theorem mem_fixed_iff {σ : P} (hσ : σ ∈ normalizer (X : Set P)) (x : X) :
    X.normalizerMonoidHom ⟨σ, hσ⟩ x = x ↔ (x : P) ∈ centralizer ({σ} : Set P) := by
  rw [mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    change σ * (x : P) * σ⁻¹ = x at h1
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  · intro h
    apply Subtype.ext
    change σ * (x : P) * σ⁻¹ = x
    rw [mul_inv_eq_iff_eq_mul]
    exact h.symm

def conjInfCentralizer {s n : P} (hn : n ∈ normalizer (X : Set P)) :
    ↥(X ⊓ centralizer ({n * s * n⁻¹} : Set P)) →* ↥(X ⊓ centralizer ({s} : Set P)) where
  toFun y := ⟨n⁻¹ * (y : P) * n, by
    obtain ⟨hyX, hyC⟩ := mem_inf.1 y.2
    refine mem_inf.2 ⟨?_, ?_⟩
    · have := (mem_normalizer_iff.1 ((normalizer (X : Set P)).inv_mem hn) (y : P)).1 hyX
      simpa [mul_assoc] using this
    · rw [mem_centralizer_singleton_iff] at hyC ⊢
      have h2 : (y : P) * (n * s * n⁻¹) = (n * s * n⁻¹) * y := hyC
      calc n⁻¹ * (y : P) * n * s = n⁻¹ * ((y : P) * (n * s * n⁻¹)) * n := by group
        _ = n⁻¹ * ((n * s * n⁻¹) * y) * n := by rw [h2]
        _ = s * (n⁻¹ * y * n) := by group⟩
  map_one' := Subtype.ext (by simp)
  map_mul' a b := Subtype.ext (by simp [mul_assoc])

theorem conjInfCentralizer_surjective {s n : P} (hn : n ∈ normalizer (X : Set P)) :
    Function.Surjective (conjInfCentralizer X (s := s) hn) := by
  intro z
  obtain ⟨hzX, hzC⟩ := mem_inf.1 z.2
  refine ⟨⟨n * (z : P) * n⁻¹, mem_inf.2 ⟨?_, ?_⟩⟩, Subtype.ext ?_⟩
  · exact (mem_normalizer_iff.1 hn (z : P)).1 hzX
  · rw [mem_centralizer_singleton_iff] at hzC ⊢
    have h2 : (z : P) * s = s * z := hzC
    calc n * (z : P) * n⁻¹ * (n * s * n⁻¹) = n * ((z : P) * s) * n⁻¹ := by group
      _ = n * (s * z) * n⁻¹ := by rw [h2]
      _ = n * s * n⁻¹ * (n * z * n⁻¹) := by group
  · change n⁻¹ * (n * (z : P) * n⁻¹) * n = z
    group

theorem not_isSolvable_inf_centralizer_conj {s n : P} (hn : n ∈ normalizer (X : Set P))
    (hs : ¬ Group.IsSolvable ↥(X ⊓ centralizer ({s} : Set P))) :
    ¬ Group.IsSolvable ↥(X ⊓ centralizer ({n * s * n⁻¹} : Set P)) := fun hsolv => by
  have := hsolv
  exact hs (Group.isSolvable_of_surjective (f := conjInfCentralizer X hn)
    (conjInfCentralizer_surjective X hn))

def fixedToInfCentralizer {σ : P} (hσ : σ ∈ normalizer (X : Set P)) (F : Subgroup X)
    (hF : ∀ x, x ∈ F ↔ X.normalizerMonoidHom ⟨σ, hσ⟩ x = x) :
    ↥F →* ↥(X ⊓ centralizer ({σ} : Set P)) where
  toFun z := ⟨(z : X), mem_inf.2 ⟨(z : X).2, (mem_fixed_iff X hσ _).1 ((hF _).1 z.2)⟩⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem fixedToInfCentralizer_surjective {σ : P} (hσ : σ ∈ normalizer (X : Set P))
    (F : Subgroup X) (hF : ∀ x, x ∈ F ↔ X.normalizerMonoidHom ⟨σ, hσ⟩ x = x) :
    Function.Surjective (fixedToInfCentralizer X hσ F hF) := by
  intro z
  obtain ⟨hzX, hzC⟩ := mem_inf.1 z.2
  refine ⟨⟨⟨(z : P), hzX⟩, (hF _).2 ((mem_fixed_iff X hσ ⟨(z : P), hzX⟩).2 hzC)⟩, Subtype.ext rfl⟩

theorem not_isSolvable_fixed_of_classes [Finite P]
    (hC : ∀ c : P, (∀ x ∈ X, c * x = x * c) → c = 1)
    (hcard : Nat.card (MulAut X) ≤ Nat.card (normalizer (X : Set P))) (R : Set P)
    (hR : ∀ s ∈ R, ¬ Group.IsSolvable ↥(X ⊓ centralizer ({s} : Set P)))
    (hcover : ∀ σ ∈ normalizer (X : Set P), σ * σ = 1 → σ ≠ 1 →
      ∃ s ∈ R, ∃ n ∈ normalizer (X : Set P), σ = n * s * n⁻¹)
    (α : MulAut X) (h1 : α ≠ 1) (h2 : α * α = 1) (F : Subgroup X) (hF : ∀ x, x ∈ F ↔ α x = x) :
    ¬ Group.IsSolvable ↥F := by
  obtain ⟨n, hn⟩ := exists_conj_of_mulAut X hC hcard α
  subst hn
  have hsq : n * n = 1 := sq_eq_one_of_aut_sq_eq_one X hC h2
  have hne : n ≠ 1 := ne_one_of_aut_ne_one X h1
  have hsq' : (n : P) * n = 1 := congrArg Subtype.val hsq
  have hne' : (n : P) ≠ 1 := fun h => hne (Subtype.ext h)
  obtain ⟨s, hsR, m, hm, hms⟩ := hcover n n.2 hsq' hne'
  have hnon := not_isSolvable_inf_centralizer_conj X hm (hR s hsR)
  rw [← hms] at hnon
  intro hsolv
  exact hnon (Group.isSolvable_of_surjective (f := fixedToInfCentralizer X n.2 F hF)
    (fixedToInfCentralizer_surjective X n.2 F hF))

end CFSG.EvenSporadicStandard.Induction.AutBound
