module

public import CFSG.ClassicalInvolution.Q3.Q3TJExc

public section

namespace CFSG.ClassicalInvolution.Q3.Q3T

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
open CFSG.ComponentClassification CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint

variable {X : Type} [Group X]

theorem mem_inner_of_odd_twistedE6 (K : Type) [Field K] [Finite K] (hK : Nat.card K = (3 ^ 1) ^ 2)
    (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (3 ^ 1)) (α : MulAut (twistedE6RootGroup K σ))
    (hodd : Odd (orderOf α)) : α ∈ OuterAutomorphisms.inner (twistedE6RootGroup K σ) := by
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hkerΘ, -, hexp, -⟩, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form Nat.prime_three (by norm_num) le_rfl K hK σ hσ
  have hcard : Nat.card (K ≃+* K) = 2 := by
    obtain ⟨-, -, -, -, h, -⟩ := finite_field_automorphism_fixed_field_cardinality (F := K)
      Nat.prime_three (n := 2) (by norm_num) (by rw [hK]; norm_num)
    exact h
  have hΘ : Θ α = 1 := by
    have h1 : orderOf (Θ α) ∣ 2 := by
      have h := orderOf_dvd_natCard (Θ α)
      rwa [show Nat.card (RingAut K) = 2 from hcard] at h
    have hodd' : Odd (orderOf (Θ α)) := hodd.of_dvd_nat (orderOf_map_dvd Θ α)
    rcases (Nat.dvd_prime Nat.prime_two).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · rw [h] at hodd'
      exact absurd hodd' (by decide)
  set S := twistedE6Inn K σ ⊔ twistedE6Diag K σ with hS
  have hmem : α ∈ S := by
    rw [← hkerΘ]
    exact hΘ
  obtain ⟨i, hi, d, hd, hid⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  obtain ⟨u, rfl⟩ := hd
  have hiS : i ∈ S := Subgroup.mem_sup_left hi
  have hdS : compatDiagAutHom TwistTag.E6 K σ.toRingHom u ∈ S := Subgroup.mem_sup_right ⟨u, rfl⟩
  have hsplit : (⟨α, hmem⟩ : S) = ⟨i, hiS⟩ * ⟨_, hdS⟩ := Subtype.ext hid.symm
  have hi1 : ((⟨i, hiS⟩ : S) : ↥S ⧸ (twistedE6Inn K σ).subgroupOf S) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hi)
  set a : ↥S ⧸ (twistedE6Inn K σ).subgroupOf S := QuotientGroup.mk (⟨α, hmem⟩ : S) with ha_def
  have ha : a = QuotientGroup.mk (s := (twistedE6Inn K σ).subgroupOf S) (⟨_, hdS⟩ : S) := by
    rw [ha_def, hsplit, QuotientGroup.mk_mul, hi1, one_mul]
  have hu8 : u ^ 8 = 1 := by
    have : Fintype K := Fintype.ofFinite K
    have hq : Fintype.card K - 1 = 8 := by
      rw [← Nat.card_eq_fintype_card, hK]
      norm_num
    funext b
    rw [Pi.pow_apply, Pi.one_apply]
    have hne : ((u b : orbitField TwistTag.E6 K σ.toRingHom b) : K) ≠ 0 := fun h0 =>
      (u b).ne_zero (Subtype.ext h0)
    have h := FiniteField.pow_card_sub_one_eq_one
      ((u b : orbitField TwistTag.E6 K σ.toRingHom b) : K) hne
    rw [hq] at h
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one]
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    exact h
  have hd8 : (⟨_, hdS⟩ : S) ^ 8 = 1 := by
    apply Subtype.ext
    show (compatDiagAutHom TwistTag.E6 K σ.toRingHom u) ^ 8 = 1
    rw [← map_pow, hu8, map_one]
  have ha8 : a ^ 8 = 1 := by
    rw [ha, ← QuotientGroup.mk_pow, hd8, QuotientGroup.mk_one]
  have ha3 : a ^ 3 = 1 := hexp a
  have ha1 : a = 1 := by
    calc a = (a ^ 3) ^ 3 * (a ^ 8)⁻¹ := by group
      _ = 1 := by rw [ha3, ha8]; group
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp ha1)

abbrev F9 : Type := GaloisField 3 (2 * 1)

theorem exists_eq_conj_twistedE6 (hZ : Subgroup.center X = ⊥)
    (f : (Generic.modelUniv .twistedE6 0 3 1 Nat.prime_three).K →* X) (hf : Function.Surjective f)
    (hker : f.ker ≤ Subgroup.center (Generic.modelUniv .twistedE6 0 3 1 Nat.prime_three).K)
    (α : MulAut X) (hodd : Odd (orderOf α)) : ∃ g : X, α = MulAut.conj g := by
  have hσ : ∀ c, iterateFrobeniusEquiv F9 3 1 c = c ^ (3 ^ 1) := fun c =>
    iterateFrobeniusEquiv_def F9 3 1 c
  have hσθ : (iterateFrobeniusEquiv F9 3 1).toRingHom = LieType.Steinberg.Exceptional.frobQ 3 1 :=
    RingHom.ext fun c => by
      rw [LieType.Steinberg.Exceptional.frobQ_apply]
      exact hσ c
  have hK : Nat.card F9 = (3 ^ 1) ^ 2 := by
    rw [GaloisField.card 3 (2 * 1) (by norm_num)]
    norm_num
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hder, hZ0, -⟩ :=
    twisted_E6_odd_exact_automorphism_normal_form Nat.prime_three (by norm_num) le_rfl F9 hK
      (iterateFrobeniusEquiv F9 3 1) hσ
  have hH : ⁅twistedFixedGroup .E6 F9 (LieType.Steinberg.Exceptional.frobQ 3 1),
      twistedFixedGroup .E6 F9 (LieType.Steinberg.Exceptional.frobQ 3 1)⁆ =
      twistedE6RootGroup F9 (iterateFrobeniusEquiv F9 3 1) := by
    rw [← hσθ]
    exact hder
  let π := (MulEquiv.subgroupCongr hH).toMonoidHom.comp
    (LieType.Steinberg.Isogeny.twistedE6Isogeny 3 1 le_rfl)
  have hπ : Function.Surjective π := (MulEquiv.subgroupCongr hH).surjective.comp
    (LieType.Steinberg.Isogeny.twistedE6Isogeny_surjective 3 1 le_rfl)
  have hπk : π.ker ≤ Subgroup.center (LieType.Steinberg.Exceptional.twistedE6Group 3 1) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : LieType.Steinberg.Isogeny.twistedE6Isogeny 3 1 le_rfl x = 1 :=
      (MulEquiv.subgroupCongr hH).map_eq_one_iff.mp hx
    have h2 : (x : ↥(e6Data_valid.minGroup F9)) ∈
        (LieType.Steinberg.Isogeny.e6IsogenyT F9).ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have h3 := congrArg
        (fun y : ↥⁅twistedFixedGroup .E6 F9 (LieType.Steinberg.Exceptional.frobQ 3 1),
          twistedFixedGroup .E6 F9 (LieType.Steinberg.Exceptional.frobQ 3 1)⁆ =>
            (y : ModGL TwistTag.E6.tag F9)) h1
      rw [LieType.Steinberg.Isogeny.coe_twistedE6Isogeny] at h3
      exact h3
    have hc := LieType.Steinberg.Isogeny.ker_e6IsogenyT_le_center F9 h2
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro y
    exact Subtype.ext (hc y)
  let f' : LieType.Steinberg.Exceptional.twistedE6Group 3 1 →* X := f
  have hker' : f'.ker ≤ Subgroup.center (LieType.Steinberg.Exceptional.twistedE6Group 3 1) := hker
  obtain ⟨e⟩ := nonempty_mulEquiv_of_central f' hf hker' hZ π hπ hπk hZ0
  exact exists_eq_conj_of_mulEquiv e
    (fun β hβ => mem_inner_of_odd_twistedE6 F9 hK _ hσ β hβ) α hodd

end CFSG.ClassicalInvolution.Q3.Q3T
