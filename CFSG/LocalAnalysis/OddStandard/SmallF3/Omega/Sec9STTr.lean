module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9STModel
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec9SEFin1
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7EndM
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.FFModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec9t_cent_B_i3 (hT6 : Asc82Tab6M) :
    ∀ (G : Type) [Group G] [Finite G] (L : Subgroup G), IsOm6M L →
      ∀ P : Subgroup G, IsSylow2Of P L → ∀ B : Subgroup G, B ≤ P → IsElemAb2 B 4 →
        ∀ y : G, y ∈ normalizer (L : Set G) → (∀ b ∈ B, y * b = b * y) → ¬ InnerOn L y →
          ∀ x : G, x ∈ normalizer (L : Set G) → (∀ b ∈ B, x * b = b * x) →
            ∃ b ∈ B, ∃ c ∈ centralizer (L : Set G), x = b * c ∨ x = b * y * c := by
  intro G _ _ L hL P hP B hBP hB y hyN hyB hyout x hxN hxB
  obtain ⟨V, _, _, _, Q, hQ, hd, hs, ⟨e⟩⟩ := ff_isOmegaStar_center_six_minus hL
  have hm : Module.finrank (ZMod 3) V = 6 ∧ quadSign Q = -1 := ⟨hd, hs⟩
  have hLperf : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  have hBN : B ≤ Subgroup.normalizer (L : Set G) :=
    hBP.trans (hP.1.trans Subgroup.le_normalizer)
  let Φ : ↥(Subgroup.normalizer (L : Set G)) →* ProjSim Q := ffInducesHom hm e
  let ψ : ↥B →* ProjSim Q := Φ.comp (Subgroup.inclusion hBN)
  let F : Subgroup (ProjSim Q) := ψ.range
  have hψ : ∀ b : ↥B, ψ b = Φ ⟨(b : G), hBN b.2⟩ := fun b => rfl
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hb1 : Φ ⟨(b : G), hBN b.2⟩ = 1 := by
      rw [← hψ b]; exact hb
    have hcent : (b : G) ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hLperf ⟨(b : G), hBN b.2⟩).mp hb1
    by_contra hne
    have hbne : (b : G) ≠ 1 := fun h => hne (Subtype.ext h)
    have hbL : (b : G) ∈ L := (hBP.trans hP.1) b.2
    have hb2 : orderOf (b : G) = 2 := orderOf_eq_prime (hB.1.2 (b : G) b.2) hbne
    exact sec711M_not_central hL hbL hb2 hcent
  have hF16 : Nat.card F = 2 ^ 4 := by
    have hcard : Nat.card F = Nat.card ↥B :=
      (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
    rw [hcard, hB.2]
  have hlift : ∀ f ∈ F, f ≠ 1 → ∃ t : OGroup Q, t * t = 1 ∧ phiSim Q t = f ∧
      2 ≤ invDim t ∧ invDim t ≤ 4 := by
    intro f hf hfne
    obtain ⟨b, hb_eq⟩ := MonoidHom.mem_range.mp hf
    have hbne : b ≠ 1 := by
      intro hb1
      exact hfne (by rw [← hb_eq, hb1, map_one])
    have hbne' : (b : G) ≠ 1 := fun h => hbne (Subtype.ext h)
    have hbL : (b : G) ∈ L := (hBP.trans hP.1) b.2
    have hb2 : orderOf (b : G) = 2 := orderOf_eq_prime (hB.1.2 (b : G) b.2) hbne'
    have hnot : (b : G) ∉ Subgroup.centralizer (L : Set G) :=
      sec711M_not_central hL hbL hb2
    have hin : InnerOn L (b : G) := Subgroup.mem_sup_left hbL
    have htype : InducesTypeSome L (b : G) 6 (-1) 4 1 :=
      (hT6.inner_iff G L hL (b : G) hb2 (hBN b.2)).mp ⟨hin, hnot⟩
    have hsim := simHasDim_of_inducesTypeSome hm e (hBN b.2) htype
    obtain ⟨t, htt, ht, htx⟩ := hsim
    refine ⟨t, htt, ?_, by omega, by omega⟩
    rw [← hb_eq]
    exact htx
  have hu : ∀ f ∈ F, Φ ⟨x, hxN⟩ * f = f * Φ ⟨x, hxN⟩ := by
    intro f hf
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hf
    show Φ ⟨x, hxN⟩ * Φ (Subgroup.inclusion hBN b) =
      Φ (Subgroup.inclusion hBN b) * Φ ⟨x, hxN⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hxB (b : G) b.2
  have hv : ∀ f ∈ F, Φ ⟨y, hyN⟩ * f = f * Φ ⟨y, hyN⟩ := by
    intro f hf
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp hf
    show Φ ⟨y, hyN⟩ * Φ (Subgroup.inclusion hBN b) =
      Φ (Subgroup.inclusion hBN b) * Φ ⟨y, hyN⟩
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    exact hyB (b : G) b.2
  have hcos := sec9t_cosets hQ hd F hF16 hlift hu hv
  rcases hcos with hxmem | hymem | hxymem
  · obtain ⟨b, hb_eq⟩ := MonoidHom.mem_range.mp hxmem
    have hbΦ : Φ ⟨(b : G), hBN b.2⟩ = Φ ⟨x, hxN⟩ := by
      rw [← hψ b]; exact hb_eq
    have hΦ1 : Φ (⟨(b : G), hBN b.2⟩⁻¹ * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, map_inv, hbΦ, inv_mul_cancel]
    have hcent : ((b : G)⁻¹ * x) ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hLperf _).mp hΦ1
    exact ⟨(b : G), b.2, (b : G)⁻¹ * x, hcent, Or.inl (by group)⟩
  · obtain ⟨b, hb_eq⟩ := MonoidHom.mem_range.mp hymem
    have hbΦ : Φ ⟨(b : G), hBN b.2⟩ = Φ ⟨y, hyN⟩ := by
      rw [← hψ b]; exact hb_eq
    have hbL : (b : G) ∈ L := (hBP.trans hP.1) b.2
    have hΦ1 : Φ (⟨(b : G), hBN b.2⟩⁻¹ * ⟨y, hyN⟩) = 1 := by
      rw [map_mul, map_inv, hbΦ, inv_mul_cancel]
    have hcent : ((b : G)⁻¹ * y) ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hLperf _).mp hΦ1
    exact (hyout (by
      rw [InnerOn, show y = (b : G) * ((b : G)⁻¹ * y) from by group]
      exact Subgroup.mul_mem_sup hbL hcent)).elim
  · obtain ⟨b, hb_eq⟩ := MonoidHom.mem_range.mp hxymem
    have hbΦ : Φ ⟨(b : G), hBN b.2⟩ = (Φ ⟨y, hyN⟩)⁻¹ * Φ ⟨x, hxN⟩ := by
      rw [← hψ b]; exact hb_eq
    have hΦ1 : Φ ((⟨y, hyN⟩ * ⟨(b : G), hBN b.2⟩)⁻¹ * ⟨x, hxN⟩) = 1 := by
      rw [map_mul, map_inv, map_mul, hbΦ]
      group
    have hcent : ((y * (b : G))⁻¹ * x) ∈ Subgroup.centralizer (L : Set G) :=
      (ffInducesHom_eq_one_iff hm e hLperf _).mp hΦ1
    refine ⟨(b : G), b.2, (y * (b : G))⁻¹ * x, hcent, Or.inr ?_⟩
    rw [hyB (b : G) b.2]
    group

end CFSG.OddStandard.SmallF3.Omega
