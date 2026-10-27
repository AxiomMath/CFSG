module

public import Mathlib.GroupTheory.Transfer

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP

open Subgroup

theorem exists_burnside_complement {X : Type*} [Group X] [Finite X] {f : ℕ} [Fact f.Prime]
    {N₀ ZE : Subgroup X} (hZEp : IsPGroup f ZE) (hZE : ZE ≤ N₀)
    (hZEc : ∀ z ∈ ZE, ∀ n ∈ N₀, n * z = z * n)
    (hmax : ∀ S : Subgroup X, S ≤ N₀ → IsPGroup f S → S ≤ ZE) :
    ∃ T : Subgroup X, T ≤ N₀ ∧ ¬ f ∣ Nat.card T ∧
      (∀ n ∈ N₀, ∃ t ∈ T, ∃ z ∈ ZE, n = t * z) ∧
      ∀ h : X, (∀ n ∈ N₀, h * n * h⁻¹ ∈ N₀) → ∀ t ∈ T, h * t * h⁻¹ ∈ T := by
  let P : Sylow f N₀ :=
    ⟨ZE.subgroupOf N₀, hZEp.comap_of_injective N₀.subtype N₀.subtype_injective,
      fun {Q} hQ hle => by
        have h2 := hmax _ (Subgroup.map_subtype_le Q) (hQ.map _)
        exact le_antisymm (fun q hq => h2 ⟨q, hq, rfl⟩) hle⟩
  have hP : Subgroup.normalizer (P : Set N₀) ≤ Subgroup.centralizer (P : Set N₀) := fun g _ =>
    Subgroup.mem_centralizer_iff.mpr fun z hz =>
      Subtype.ext (hZEc (z : X) hz g g.2).symm
  let θ : N₀ →* P := MonoidHom.transferSylow P hP
  have hnd : ¬ f ∣ Nat.card θ.ker := MonoidHom.not_dvd_card_ker_transferSylow P hP
  have hcompl := MonoidHom.ker_transferSylow_isComplement' P hP
  have hTcard : Nat.card (θ.ker.map N₀.subtype) = Nat.card θ.ker :=
    Subgroup.card_map_of_injective N₀.subtype_injective
  refine ⟨θ.ker.map N₀.subtype, Subgroup.map_subtype_le _, by rwa [hTcard], ?_, ?_⟩
  · intro n hn
    obtain ⟨⟨t, z⟩, htz⟩ := hcompl.2 ⟨n, hn⟩
    refine ⟨(t.1 : X), ⟨t.1, t.2, rfl⟩, (z.1 : X), z.2, ?_⟩
    exact (congrArg Subtype.val htz).symm
  · intro h hh t ht
    obtain ⟨t₀, ht₀, rfl⟩ := ht
    have hn : h * (t₀ : X) * h⁻¹ ∈ N₀ := hh t₀ t₀.2
    let n' : N₀ := ⟨h * (t₀ : X) * h⁻¹, hn⟩
    have hpow : n' ^ Nat.card θ.ker = 1 := by
      apply Subtype.ext
      have h1 : t₀ ^ Nat.card θ.ker = 1 := by
        have : (⟨t₀, ht₀⟩ : θ.ker) ^ Nat.card θ.ker = 1 := pow_card_eq_one'
        exact congrArg Subtype.val this
      have h2 : (t₀ : X) ^ Nat.card θ.ker = 1 := by
        have := congrArg Subtype.val h1
        simpa using this
      show (h * (t₀ : X) * h⁻¹) ^ Nat.card θ.ker = 1
      rw [show (h * (t₀ : X) * h⁻¹) ^ Nat.card θ.ker = h * (t₀ : X) ^ Nat.card θ.ker * h⁻¹ from by
        simpa using (conj_pow (a := h) (b := (t₀ : X)) (i := Nat.card θ.ker)), h2]
      simp
    obtain ⟨k, hk⟩ := P.isPGroup' (θ n')
    have h3 : (θ n') ^ Nat.card θ.ker = 1 := by rw [← map_pow, hpow, map_one]
    have hcop : Nat.Coprime (Nat.card θ.ker) (f ^ k) :=
      Nat.Coprime.pow_right k (((Fact.out : f.Prime).coprime_iff_not_dvd.mpr hnd).symm)
    have h4 : θ n' = 1 := by
      have o1 : orderOf (θ n') ∣ Nat.card θ.ker := orderOf_dvd_of_pow_eq_one h3
      have o2 : orderOf (θ n') ∣ f ^ k := orderOf_dvd_of_pow_eq_one hk
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop o1 o2)
    exact ⟨n', h4, rfl⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.RankP
