module

public import CFSG.ClassicalInvolution.Phan.Defs
public import CFSG.ClassicalInvolution.Phan.CenterScalars
public import CFSG.Blueprint.Catalog

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.Assembly.LowTwoRank


theorem unitary_simple_central_quotient_native_model
    (K : Type) [Field K] [Finite K] (p f : ℕ) [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = (p ^ f) ^ 2) (hp : p ≠ 2) {n : ℕ} (hn : 3 ≤ n)
    {X : Type} [Group X] [IsSimpleGroup X] (hX : ∃ a b : X, a * b ≠ b * a)
    (θ : Su K p f (n + 1) →* X) (hθ : Function.Surjective θ)
    (hker : θ.ker ≤ Subgroup.center (Su K p f (n + 1))) :
    θ.ker = Subgroup.center (Su K p f (n + 1)) ∧
      Nonempty (StatedProj (StatedSU (n + 1) (p ^ f) K) ≃* X) ∧
      Blueprint.LieModel X .PSU (n + 1) p f ∧ Blueprint.OddLieType X := by
  have hσ := isUnitaryInvolution_unitaryInvolution (K := K) (p := p) (f := f) hK
  have hf : 1 ≤ f := by
    rcases Nat.eq_zero_or_pos f with rfl | hf
    · have h1 : Nat.card K = 1 := by simpa using hK
      have : (1 : ℕ) < Nat.card K := Finite.one_lt_card
      omega
    · exact hf
  have hZX : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hX
      exact hab (Subgroup.mem_center_iff.1 (h ▸ Subgroup.mem_top b) a)
  have hkerEq : θ.ker = Subgroup.center (Su K p f (n + 1)) := by
    refine le_antisymm hker fun z hz => ?_
    have : θ z ∈ Subgroup.center X := Subgroup.mem_center_iff.2 fun x => by
      obtain ⟨y, rfl⟩ := hθ x
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz y)]
    rw [hZX, Subgroup.mem_bot] at this
    exact this
  have hcenter := center_SUid_eq hσ (m := n + 1) (by omega)
  have hSU : SUid (unitaryInvolution K p f) (n + 1) = StatedSU (n + 1) (p ^ f) K :=
    SUid_eq_statedSU hK (n + 1)
  let e₁ : Su K p f (n + 1) ⧸ θ.ker ≃* X := QuotientGroup.quotientKerEquivOfSurjective θ hθ
  let e₂ : StatedProj (SUid (unitaryInvolution K p f) (n + 1)) ≃*
      StatedProj (StatedSU (n + 1) (p ^ f) K) :=
    QuotientGroup.congr _ _ (MulEquiv.subgroupCongr hSU) (by
      ext x
      simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact hy
      · intro hx
        exact ⟨(MulEquiv.subgroupCongr hSU).symm x, by simpa using hx, by simp⟩)
  let e₃ : Su K p f (n + 1) ⧸ θ.ker ≃* StatedProj (SUid (unitaryInvolution K p f) (n + 1)) :=
    QuotientGroup.quotientMulEquivOfEq (hkerEq.trans hcenter)
  have hiso : Nonempty (StatedProj (StatedSU (n + 1) (p ^ f) K) ≃* X) :=
    ⟨e₂.symm.trans (e₃.symm.trans e₁)⟩
  have hadm : StatedLieAdmissible .PSU (n + 1) p f := by
    refine ⟨Fact.out, hf, by omega, ?_⟩
    intro h
    have h2 : p ^ f = 2 := (Prod.mk.inj h).2
    have : p ∣ 2 := by
      rw [← h2]
      exact dvd_pow_self p (by omega)
    rcases (Nat.dvd_prime Nat.prime_two).mp this with h' | h'
    · exact (Fact.out : p.Prime).one_lt.ne' h'
    · exact hp h'
  have hmodel : Blueprint.LieModel X .PSU (n + 1) p f := by
    obtain ⟨e⟩ := hiso
    exact Or.inl ⟨by decide, hadm, K, inferInstance, inferInstance, hK, ⟨e.symm⟩⟩
  exact ⟨hkerEq, hiso, hmodel, ⟨.PSU, n + 1, p, f, Fact.out, hp, hadm, hmodel⟩⟩

end CFSG.ClassicalInvolution.Phan
