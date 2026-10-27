module

public import CFSG.GroupTheory.HallHigmanPiCore
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
public import Mathlib.CategoryTheory.Category.Init
public import Mathlib.Combinatorics.Matroid.Init
public import Mathlib.NumberTheory.ArithmeticFunction.Misc

public section

namespace CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs

open Subgroup
open scoped commutatorElement

theorem card_prime_of_isSimpleGroup_isSolvable (S : Type*) [Group S] [Finite S] [IsSimpleGroup S]
    (hS : Group.IsSolvable S) : (Nat.card S).Prime := by
  have hcomm : ∀ a b : S, a * b = b * a := IsSimpleGroup.comm_iff_isSolvable.mpr hS
  let _ : CommGroup S := { ‹Group S› with mul_comm := fun a b => hcomm a b }
  exact CommGroup.is_simple_iff_prime_card.mp inferInstance

theorem index_prime_alternative {p : ℕ} [hp : Fact p.Prime] {H : Type*} [Group H] (T : Subgroup H)
    (hq : (T.index).Prime) : T.index = p ∨ Nat.Coprime p T.index := by
  by_cases h : T.index = p
  · exact Or.inl h
  · exact Or.inr ((Nat.coprime_primes hp.out hq).2 (Ne.symm h))

theorem isPSolvable_of_normal_coprime_quotient_solvable {p : ℕ} [hp : Fact p.Prime]
    {X : Type*} [Group X] [Finite X] (N : Subgroup X) [N.Normal]
    (hN : Nat.Coprime p (Nat.card N)) (hsol : Group.IsSolvable (X ⧸ N)) :
    CFSG.HallHigman.IsPSolvable p X := by
  intro H _ T _ hs
  classical
  set K : Subgroup H := N.subgroupOf H with hKdef
  have hKle : K.map H.subtype ≤ N := by
    rintro _ ⟨h, hh, rfl⟩
    exact hh
  have hKcard : Nat.card K ∣ Nat.card N := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective]
    exact Subgroup.card_dvd_of_le hKle
  have hcopK : Nat.Coprime p (Nat.card K) := Nat.Coprime.coprime_dvd_right hKcard hN
  by_cases hKT : K ≤ T
  ·
    have hsolS : Group.IsSolvable (H ⧸ T) := by
      let g : H →* X ⧸ N := (QuotientGroup.mk' N).comp H.subtype
      have hgk : g.ker = K := by
        ext h
        simp [g, hKdef, MonoidHom.mem_ker, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      have hkerT : g.ker ≤ T := by rw [hgk]; exact hKT
      have : Group.IsSolvable g.range := inferInstance
      have hq : Group.IsSolvable (H ⧸ g.ker) :=
        Group.isSolvable_of_surjective (f := (QuotientGroup.quotientKerEquivRange g).symm.toMonoidHom)
          (QuotientGroup.quotientKerEquivRange g).symm.surjective
      have hmapsurj : Function.Surjective (QuotientGroup.map g.ker T (MonoidHom.id H)
          (by simpa using hkerT)) := by
        intro x
        obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
        exact ⟨QuotientGroup.mk h, rfl⟩
      exact Group.isSolvable_of_surjective hmapsurj
    have hprime := card_prime_of_isSimpleGroup_isSolvable (H ⧸ T) hsolS
    exact index_prime_alternative T hprime
  ·
    right
    have hsurj : Function.Surjective ((QuotientGroup.mk' T).comp K.subtype) := by
      have hMtop : K.map (QuotientGroup.mk' T : H →* H ⧸ T) = ⊤ := by
        rcases hs.eq_bot_or_eq_top_of_normal (K.map (QuotientGroup.mk' T : H →* H ⧸ T)) with h | h
        · exfalso
          obtain ⟨k, hk, hkT⟩ := IsConcreteLE.not_le_iff_exists.mp hKT
          have h1 : (QuotientGroup.mk' T k : H ⧸ T) ∈ K.map (QuotientGroup.mk' T : H →* H ⧸ T) :=
            Subgroup.mem_map_of_mem _ hk
          rw [h, Subgroup.mem_bot] at h1
          exact hkT ((QuotientGroup.eq_one_iff k).mp h1)
        · exact h
      intro y
      have hy : y ∈ K.map (QuotientGroup.mk' T : H →* H ⧸ T) := by
        rw [hMtop]; exact Subgroup.mem_top y
      obtain ⟨k, hk, hky⟩ := Subgroup.mem_map.mp hy
      exact ⟨⟨k, hk⟩, hky⟩
    have hdvd : Nat.card (H ⧸ T) ∣ Nat.card K :=
      Subgroup.card_dvd_of_surjective hsurj
    have hdvd' : T.index ∣ Nat.card K := hdvd
    exact (Nat.Coprime.coprime_dvd_left hdvd' hcopK.symm).symm

theorem commutator_centralizes_cyclic {G : Type*} [Group G] (R : Subgroup G) [IsCyclic R]
    {a b : G} (ha : ∀ r ∈ R, a * r * a⁻¹ ∈ R) (hb : ∀ r ∈ R, b * r * b⁻¹ ∈ R) :
    ∀ r ∈ R, a⁻¹ * b⁻¹ * a * b * r = r * (a⁻¹ * b⁻¹ * a * b) := by
  obtain ⟨g, hg⟩ : ∃ g : R, ∀ x : R, x ∈ Subgroup.zpowers g := IsCyclic.exists_generator
  have hpow : ∀ r ∈ R, ∃ n : ℤ, (g : G) ^ n = r := by
    intro r hr
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨r, hr⟩)
    exact ⟨n, by simpa using congrArg Subtype.val hn⟩
  have hgR : (g : G) ∈ R := g.2
  obtain ⟨i, hiE⟩ : ∃ i : ℤ, a * (g : G) * a⁻¹ = (g : G) ^ i := by
    obtain ⟨i, hi⟩ := hpow _ (ha _ hgR)
    exact ⟨i, hi.symm⟩
  obtain ⟨j, hjE⟩ : ∃ j : ℤ, b * (g : G) * b⁻¹ = (g : G) ^ j := by
    obtain ⟨j, hj⟩ := hpow _ (hb _ hgR)
    exact ⟨j, hj.symm⟩
  have h1 : a * (g : G) ^ j * a⁻¹ = (g : G) ^ (i * j) := by
    rw [← conj_zpow, hiE, ← zpow_mul]
  have h2 : b * (g : G) ^ i * b⁻¹ = (g : G) ^ (j * i) := by
    rw [← conj_zpow, hjE, ← zpow_mul]
  have h3 : a * b * (g : G) * (a * b)⁻¹ = (g : G) ^ (i * j) := by
    rw [show a * b * (g : G) * (a * b)⁻¹ = a * (b * (g : G) * b⁻¹) * a⁻¹ by group, hjE, h1]
  have h4 : b * a * (g : G) * (b * a)⁻¹ = (g : G) ^ (j * i) := by
    rw [show b * a * (g : G) * (b * a)⁻¹ = b * (a * (g : G) * a⁻¹) * b⁻¹ by group, hiE, h2]
  have hxy : a * b * (g : G) * (a * b)⁻¹ = b * a * (g : G) * (b * a)⁻¹ := by
    rw [h3, h4, mul_comm i j]
  have hcomm : Commute (a⁻¹ * b⁻¹ * a * b) (g : G) := by
    show a⁻¹ * b⁻¹ * a * b * (g : G) = (g : G) * (a⁻¹ * b⁻¹ * a * b)
    calc a⁻¹ * b⁻¹ * a * b * (g : G) = (b * a)⁻¹ * (a * b * (g : G) * (a * b)⁻¹) * (a * b) := by
          group
      _ = (b * a)⁻¹ * (b * a * (g : G) * (b * a)⁻¹) * (a * b) := by rw [hxy]
      _ = (g : G) * (a⁻¹ * b⁻¹ * a * b) := by group
  intro r hr
  obtain ⟨n, rfl⟩ := hpow r hr
  exact hcomm.zpow_right n

theorem isSolvable_of_commutatorElement_mem {G : Type*} [Group G] (D : Subgroup G)
    [Group.IsSolvable D] (hD : ∀ a b : G, ⁅a, b⁆ ∈ D) : Group.IsSolvable G := by
  obtain ⟨N, hNdef⟩ : ∃ N : Subgroup G, N = ⁅(⊤ : Subgroup G), ⊤⁆ := ⟨_, rfl⟩
  have :N.Normal := by rw [hNdef]; infer_instance
  have hND : N ≤ D := by
    rw [hNdef, commutator_le]
    intro g₁ _ g₂ _
    exact hD g₁ g₂
  have hcomm : ∀ x y : G ⧸ N, x * y = y * x := by
    intro x y
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [e, hNdef]
    exact commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
  have :Group.IsSolvable (G ⧸ N) := Group.isSolvable_of_comm hcomm
  have hle : (QuotientGroup.mk' N).ker ≤ D.subtype.range := by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype]
    exact hND
  exact Group.isSolvable_of_ker_le_range D.subtype (QuotientGroup.mk' N) hle

end CFSG.AGLEmbeddingD2.Tits.OrdinaryProofs
