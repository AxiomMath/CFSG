module

public import CFSG.Quasithin.Background.F6ResL28
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.CaseTwoLocalL28Group
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.AGLEmbedding.KFactProofs.L28Local

open CFSG.Quasithin.F6.L28Res

theorem frob_pow_three : (frob : MulAut G8) ^ 3 = 1 := by
  apply MulEquiv.ext
  intro x
  have h : (frob ^ 3 : MulAut G8) x = frob (frob (frob x)) := by
    simp [pow_succ, MulAut.mul_apply]
  rw [h]
  exact Subtype.ext (congrArg Subtype.val (frobF_frobF_frobF x))

theorem conj_injective_G8 : Function.Injective (MulAut.conj : G8 →* MulAut G8) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro g hg
  have hc : ∀ h : G8, g * h * g⁻¹ = h := fun h => by
    have := congrArg (fun α : MulAut G8 => α h) (MonoidHom.mem_ker.mp hg)
    simpa using this
  have hc' : ∀ h : G8, g * h = h * g := fun h => by
    calc g * h = g * h * g⁻¹ * g := by group
      _ = h * g := by rw [hc h]
  exact Subgroup.mem_bot.mpr (eq_one_of_commute g (hc' ga) (hc' gb))

theorem frob_not_mem_range : ∀ g : G8, MulAut.conj g ≠ frob ∧ MulAut.conj g ≠ frob ^ 2 := by
  intro g
  obtain ⟨h1, h2⟩ := frob_not_inner g
  refine ⟨fun h => h1 ⟨?_, ?_⟩, fun h => h2 ⟨?_, ?_⟩⟩
  · rw [← MulAut.conj_apply, h]
    rfl
  · rw [← MulAut.conj_apply, h]
    rfl
  · rw [← MulAut.conj_apply, h]
    rfl
  · rw [← MulAut.conj_apply, h]
    rfl

theorem exists_conj_mul_frob_pow (f : MulAut G8) :
    ∃ (g : G8) (i : ℕ), i < 3 ∧ f = MulAut.conj g * frob ^ i := by
  set I := (MulAut.conj : G8 →* MulAut G8).range with hI
  have := L28Data.normal_range_conj G8
  let ψ : MulAut G8 →* MulAut G8 ⧸ I := QuotientGroup.mk' I
  have hψ : ∀ a, ψ a = 1 ↔ a ∈ I := fun a => QuotientGroup.eq_one_iff a
  have h1 : ψ frob ≠ 1 := fun h => by
    obtain ⟨g, hg⟩ := (hψ _).1 h
    exact (frob_not_mem_range g).1 hg
  have h3 : (ψ frob) ^ 3 = 1 := by rw [← map_pow, frob_pow_three, map_one]
  have hord : orderOf (ψ frob) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h3 h1
  let Θ : G8 × Fin 3 → MulAut G8 := fun p => MulAut.conj p.1 * frob ^ (p.2 : ℕ)
  have hΘ : Function.Injective Θ := by
    rintro ⟨g, i⟩ ⟨g', j⟩ h
    simp only [Θ] at h
    have hi : ψ frob ^ (i : ℕ) = ψ frob ^ (j : ℕ) := by
      have := congrArg ψ h
      rw [map_mul, map_mul, map_pow, map_pow] at this
      have hc : ∀ a : G8, ψ (MulAut.conj a) = 1 := fun a => (hψ _).2 ⟨a, rfl⟩
      rwa [hc, hc, one_mul, one_mul] at this
    have hij : (i : ℕ) = j := by
      have := (pow_eq_pow_iff_modEq).1 hi
      rw [hord] at this
      exact Nat.ModEq.eq_of_lt_of_lt this i.2 j.2
    have hij' : i = j := Fin.ext hij
    subst hij'
    have := mul_right_cancel h
    exact Prod.ext (conj_injective_G8 this) rfl
  have hbij : Function.Bijective Θ := by
    refine hΘ.bijective_of_nat_card_le ?_
    rw [card_mulAut, Nat.card_prod, card_G8, Nat.card_eq_fintype_card (α := Fin 3)]
    simp
  obtain ⟨⟨g, i⟩, hgi⟩ := hbij.2 f
  exact ⟨g, i, i.2, hgi.symm⟩

@[expose] def T0 : Subgroup G8 := Subgroup.zpowers g9

@[expose] def T0list : List G8 := (List.range 9).map fun k => g9 ^ k

theorem orderOf_g9 : orderOf g9 = 9 := by
  obtain ⟨-, -, h93, h99⟩ := gen_facts_prod
  have := orderOf_eq_prime_pow (n := 1) (p := 3) (x := g9) (by simpa using h93)
    (by simpa using h99)
  simpa using this

theorem card_T0 : Nat.card T0 = 9 := by
  rw [T0, Nat.card_zpowers, orderOf_g9]

theorem mem_T0_iff {x : G8} : x ∈ T0 ↔ x ∈ T0list := by
  classical
  rw [T0, mem_zpowers_iff_mem_range_orderOf, orderOf_g9, T0list]
  simp [Finset.mem_image, Finset.mem_range, List.mem_map, List.mem_range]

theorem mem_normalizer_T0_iff {g : G8} :
    g ∈ Subgroup.normalizer (T0 : Set G8) ↔ g * g9 * g⁻¹ ∈ T0list := by
  rw [← mem_T0_iff]
  constructor
  · intro hg
    exact (Subgroup.mem_normalizer_iff.1 hg g9).1 (Subgroup.mem_zpowers g9)
  · intro hg
    refine Subgroup.mem_normalizer_fintype fun n hn => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hn
    have : g * g9 ^ k * g⁻¹ = (g * g9 * g⁻¹) ^ k := by simp
    rw [this]
    exact Subgroup.zpow_mem _ hg k

set_option synthInstance.maxSize 1024

theorem card_conj_mem : Fintype.card {g : G8 // g * g9 * g⁻¹ ∈ T0list} = 18 := by
  decide +kernel

theorem exists_inv : ∃ s : G8, s * g9 * s⁻¹ ∈ T0list ∧
    ∀ x ∈ T0list, s * x * s⁻¹ = x → x = 1 := by
  decide +kernel

theorem centralizer_T0 : ∀ t ∈ T0list, t ≠ 1 → ∀ g : G8, g * t = t * g → g ∈ T0list := by
  decide +kernel

theorem conj_frob_zero : ∀ g : G8, g * g9 * g⁻¹ = g9 → g ∈ T0list := by
  decide +kernel

theorem conj_frob_one : ∀ g : G8, g * frobF g9 * g⁻¹ ≠ g9 := by
  decide +kernel

theorem conj_frob_two : ∀ g : G8, g * frobF (frobF g9) * g⁻¹ ≠ g9 := by
  decide +kernel

theorem l28Data_T0 : L28Data G8 T0 where
  card_group := card_G8
  card_eq := card_T0
  card_normalizer := by
    rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_normalizer_T0_iff (g := g)),
      Nat.card_eq_fintype_card]
    exact card_conj_mem
  centralizer_le := fun t ht ht1 g hg =>
    mem_T0_iff.2 (centralizer_T0 t (mem_T0_iff.1 ht) ht1 g hg)
  inv := by
    obtain ⟨s, hs, hsx⟩ := exists_inv
    exact ⟨s, mem_normalizer_T0_iff.2 hs, fun x hx => hsx x (mem_T0_iff.1 hx)⟩
  aut := by
    intro f hf
    obtain ⟨g, i, hi, rfl⟩ := exists_conj_mul_frob_pow f
    have h9 : (MulAut.conj g * frob ^ i) g9 = g9 := hf g9 (Subgroup.mem_zpowers g9)
    interval_cases i
    · have h0 : g * g9 * g⁻¹ = g9 := by simpa [MulAut.conj_apply] using h9
      exact ⟨g, mem_T0_iff.2 (conj_frob_zero g h0), by simp⟩
    · have h1 : g * frobF g9 * g⁻¹ = g9 := by
        have := h9
        simp only [pow_one, MulAut.mul_apply, MulAut.conj_apply] at this
        exact this
      exact absurd h1 (conj_frob_one g)
    · have h2 : g * frobF (frobF g9) * g⁻¹ = g9 := by
        have := h9
        simp only [pow_two, MulAut.mul_apply, MulAut.conj_apply] at this
        exact this
      exact absurd h2 (conj_frob_two g)

end CFSG.AGLEmbedding.KFactProofs.L28Local
