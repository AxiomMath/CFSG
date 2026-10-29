module

public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDDefs
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKDOrbit

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3

open CFSG CFSG.Open Subgroup
open CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6KD

variable {G : Type} [Group G]

theorem p622_le_of_orbit_length_one [Finite G] (z : G) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hzp : z ^ p = 1) (L : Subgroup G) (hLz : ∀ g : G, g ∈ L ↔ z * g * z⁻¹ ∈ L)
    (hsimp : IsSimpleGroup ↥L) (hnab : ¬ ∀ a b : ↥L, a * b = b * a)
    (hK : CFSG.Open.IsKGroup ↥L) (hpL : ¬ p ∣ Nat.card ↥L)
    (T : Subgroup G) (hTL : CFSG.ABGLocalTools.IsSylowOf 2 T L)
    (hTz : ∀ g ∈ T, z * g * z⁻¹ ∈ T) (M : Subgroup G)
    (hC : ∀ g ∈ L, z * g = g * z → g ∈ M)
    (hN1 : ∀ U : Subgroup G, U ≤ T → U ≠ ⊥ → (∀ g ∈ U, z * g * z⁻¹ ∈ U) →
      Subgroup.normalizer (U : Set G) ⊓ L ≤ M)
    (hN3 : ∀ U : Subgroup G, U ≤ L → IsPGroup 2 U → U ≠ ⊥ → (∀ g ∈ U, z * g = g * z) →
      Subgroup.normalizer (U : Set G) ⊓ L ≤ M)
    (hEven : KFactFieldAutEvenAt p) (hOdd : KFactFieldAutOddAt p) : L ≤ M := by
  by_cases hcent : ∀ g ∈ L, z * g = g * z
  · intro x hx
    exact hC x hx (hcent x hx)
  obtain ⟨g₀, hg₀, hg₀z⟩ : ∃ g ∈ L, z * g ≠ g * z := by
    by_contra h
    push Not at h
    exact hcent h
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hαord : orderOf (conjAutOf z L hLz) = p :=
    orderOf_eq_prime (conjAutOf_pow_eq_one z p hzp L hLz)
      (conjAutOf_ne_one z L hLz g₀ hg₀ hg₀z)
  have key : (⊤ : Subgroup ↥L) ≤ M.subgroupOf L := by
    by_cases hodd : ∃ U : Subgroup ↥L, CFSG.ABGLocalTools.IsSylowOf 2 U ⊤ ∧
        ∀ g ∈ U, conjAutOf z L hLz g = g
    ·
      obtain ⟨U, hU, hUc⟩ := hodd
      have hgen := hOdd ↥L (conjAutOf z L hLz) U hp hαord hpL hsimp hnab hK hU hUc
      rw [← hgen]
      apply (Subgroup.closure_le _).mpr
      intro x hx
      simp only [Set.mem_iUnion] at hx
      obtain ⟨U₀, ⟨hU₀U, hU₀⟩, hxN⟩ := hx
      rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
      have hU2 : IsPGroup 2 ↥U := hU.isPGroup
      have hU₀2 : IsPGroup 2 ↥U₀ := hU2.to_le hU₀U
      have hU₀'2 : IsPGroup 2 ↥(U₀.map L.subtype) := hU₀2.map L.subtype
      have hle : U₀.map L.subtype ≤ L := Subgroup.map_subtype_le U₀
      have hne : U₀.map L.subtype ≠ ⊥ := by
        intro hbot
        apply hU₀
        rw [Subgroup.eq_bot_iff_forall]
        intro u hu
        have hmem : (u : G) ∈ U₀.map L.subtype := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
        rw [hbot, Subgroup.mem_bot] at hmem
        exact Subtype.ext hmem
      have hcent : ∀ g ∈ U₀.map L.subtype, z * g = g * z := by
        intro g hg
        obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hg
        have h1 : conjAutOf z L hLz u = u := hUc u (hU₀U hu)
        have h2 : z * (u : G) * z⁻¹ = (u : G) := congrArg Subtype.val h1
        exact mul_inv_eq_iff_eq_mul.mp h2
      exact hN3 (U₀.map L.subtype) hle hU₀'2 hne hcent
        (Subgroup.mem_inf.mpr ⟨normalizer_map_mem hxN, x.2⟩)
    ·
      have hT' : CFSG.ABGLocalTools.IsSylowOf 2 (T.subgroupOf L) ⊤ := by
        apply (CFSG.ABGLocalTools.isSylowOf_map_subtype_iff L).mp
        have htop : (⊤ : Subgroup ↥L).map L.subtype = L := by
          rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        rw [Subgroup.subgroupOf_map_subtype, htop, inf_eq_left.mpr hTL.le]
        exact hTL
      have hgen := hEven ↥L (conjAutOf z L hLz) (T.subgroupOf L) hp hαord hpL hsimp
        hnab hK hT' hodd
      have hTM : T ≤ M := by
        by_cases hT0 : T = ⊥
        · rw [hT0]
          exact bot_le
        · intro t ht
          exact (hN1 T le_rfl hT0 hTz)
            (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer ht, hTL.le ht⟩)
      rw [← hgen]
      apply (Subgroup.closure_le _).mpr
      rintro x (hx | hx)
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        apply hC x.1 x.2
        have h2 : z * (x : G) * z⁻¹ = (x : G) := congrArg Subtype.val hx
        exact mul_inv_eq_iff_eq_mul.mp h2
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        exact hTM (Subgroup.mem_subgroupOf.mp hx)
  intro x hx
  exact Subgroup.mem_subgroupOf.mp (key (Subgroup.mem_top (⟨x, hx⟩ : ↥L)))

end CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3
