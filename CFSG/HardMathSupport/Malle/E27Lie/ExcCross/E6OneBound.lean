module

public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TorsionTorus
public import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.WeylE6Sylow

public noncomputable section

namespace CFSG.HardMathSupport.Malle.E27Lie.ExcCross

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

set_option linter.unusedSectionVars false

theorem kerC_E6_card : (kerC Tag.E6).card ≤ 3 := by
  decide +kernel

section E6One


theorem E6_exists_cube_root (K : Type) [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1) :
    ∃ ζ : rootsOfUnity 3 K, orderOf ζ = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hdvd : 3 ∣ Nat.card Kˣ := by rwa [Nat.card_units]
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) 3 hdvd
  have hx3 : x ∈ rootsOfUnity 3 K := (mem_rootsOfUnity 3 x).2 (by rw [← hx]; exact pow_orderOf_eq_one x)
  refine ⟨⟨x, hx3⟩, ?_⟩
  rw [← Subgroup.orderOf_coe]
  exact hx


instance finite_Tor3_of_finite (τ : Tag) (K : Type) [Field K] [Finite K] :
    Finite (Tor3 τ K) := by
  have : Finite (adjointGroup τ K) := generated_group_finite τ K
  refine Finite.of_injective (fun x : Tor3 τ K => (⟨(x : ModGL τ K),
    (le_sup_left : torusGroup τ K ≤ monomialSubgroup τ K).trans monomialSubgroup_le_adjointGroup'
      x.2.1⟩ : adjointGroup τ K)) ?_
  intro x y h
  apply Subtype.ext
  have := congrArg Subtype.val h
  exact this

theorem eightyOne_dvd_centralizer_E6 (K : Type) [Field K] [Finite K] (h3 : 3 ∣ Nat.card K - 1)
    (n : ↥(monomialSub Tag.E6 K)) (hn : orderOf n = 3) :
    81 ∣ Nat.card (Subgroup.centralizer ({n} : Set ↥(monomialSub Tag.E6 K))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨ζ, hζ⟩ := E6_exists_cube_root K h3
  let ι : ↥(monomialSub Tag.E6 K) →* ModGL Tag.E6 K :=
    (adjointGroup Tag.E6 K).subtype.comp (monomialSub Tag.E6 K).subtype
  have hι : Function.Injective ι :=
    Subtype.val_injective.comp (Subtype.val_injective)
  have hn3 : n ^ 3 = 1 := by rw [← hn]; exact pow_orderOf_eq_one n
  set s : ModGL Tag.E6 K := ι n with hs
  have hsm : s ∈ monomialSubgroup Tag.E6 K := n.2
  have hs3 : s ^ 3 = 1 := by rw [hs, ← map_pow, hn3, map_one]
  obtain ⟨B, hB1, hB2, hBfin, hB3, hB4⟩ := exists_three_subgroup_Tor3 (τ := Tag.E6) (L := K)
    kerC_E6_card (by decide) (fun p hp => exists_conj_fixed3_E6 p hp) hζ hsm hs3
  have hrange : B ≤ ι.range := by
    refine hB1.trans (sup_le ?_ ?_)
    · intro x hx
      have hxt : x ∈ torusGroup Tag.E6 K := hx.1
      have hxm : x ∈ monomialSubgroup Tag.E6 K := (le_sup_left : torusGroup Tag.E6 K ≤
        monomialSubgroup Tag.E6 K) hxt
      have hxa : x ∈ adjointGroup Tag.E6 K := monomialSubgroup_le_adjointGroup' hxm
      exact ⟨⟨⟨x, hxa⟩, hxm⟩, rfl⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨n, rfl⟩
  set B' : Subgroup ↥(monomialSub Tag.E6 K) := B.comap ι with hB'
  have hcard : Nat.card B' = Nat.card B := by
    rw [← Subgroup.card_map_of_injective hι, hB', Subgroup.map_comap_eq, inf_of_le_right hrange]
  have hB'C : B' ≤ Subgroup.centralizer ({n} : Set ↥(monomialSub Tag.E6 K)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply hι
    rw [map_mul, map_mul]
    have := Subgroup.mem_centralizer_singleton_iff.1 (hB2 hx)
    exact this
  have hB'3 : IsPGroup 3 B' := by
    intro x
    refine ⟨1, ?_⟩
    apply Subtype.ext
    apply hι
    have := hB3 (ι x.1) x.2
    simpa using this
  have hfin' : Finite B' := Finite.of_injective _ (Subgroup.inclusion_injective hB'C)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 hB'3
  have hk4 : 4 ≤ k := by
    by_contra hlt
    rw [not_le] at hlt
    have h1 : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [← hk, hcard] at h1
    omega
  have h81 : 81 ∣ Nat.card B' := by
    rw [hk]
    exact (pow_dvd_pow 3 hk4 : 3 ^ 4 ∣ 3 ^ k)
  exact h81.trans (Subgroup.card_dvd_of_le hB'C)

end E6One

end CFSG.HardMathSupport.Malle.E27Lie.ExcCross
