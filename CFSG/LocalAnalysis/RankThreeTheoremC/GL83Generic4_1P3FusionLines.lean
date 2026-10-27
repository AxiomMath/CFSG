module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3PlaneLines
import CFSG.LocalAnalysis.RankThreeTheoremC.FusionControl
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3R1P34f

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.ABGLocalTools Subgroup

variable {G : Type} [Group G] [Finite G]

theorem isLargeObstruction_conj_of_map_le (hS : Setting G) (hU0 : FullCoreLocal G) {p : ℕ}
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G} (hM : IsCoreMaxLocal p P M)
    {x : G} (hxP : x ∈ (P : Subgroup G)) (hx : IsLargeObstruction p M x) {g : G}
    (hg : (zpowers x).map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G)) :
    IsLargeObstruction p M (g * x * g⁻¹) := by
  have hfact : Fact p.Prime := ⟨sigmaA_prime p hp⟩
  have hg' : (zpowers x).map (MulAut.conj g⁻¹⁻¹).toMonoidHom ≤ (P : Subgroup G) := by
    rwa [inv_inv]
  obtain ⟨c, hcM, hc⟩ := exists_mem_conj_eq_of_map_le hS hU0 hp hM (zpowers_le.mpr hxP) hg'
  have hxc : c⁻¹ * x * c = g * x * g⁻¹ := by
    simpa using hc x (mem_zpowers x)
  have h := hx.conj (M.inv_mem hcM)
  rwa [MulAut.conj_apply, inv_inv, hxc] at h

theorem mem_zpowers_of_isCyclic_of_pow_three {Z : Subgroup G} (hZ : IsCyclic Z) {x z : G}
    (hxZ : x ∈ Z) (hzZ : z ∈ Z) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1) (hz3 : z ^ 3 = 1) :
    z ∈ zpowers x := by
  by_cases hz1 : z = 1
  · rw [hz1]
    exact one_mem _
  have hxo : orderOf x = 3 := orderOf_eq_prime hx3 hx1
  have hzo : orderOf z = 3 := orderOf_eq_prime hz3 hz1
  have h := (IsCyclic.subgroup_eq_iff_card_eq (G := Z) (H := zpowers (⟨x, hxZ⟩ : Z))
    (K := zpowers (⟨z, hzZ⟩ : Z))).2 (by
      rw [Nat.card_zpowers, Nat.card_zpowers, Subgroup.orderOf_mk, Subgroup.orderOf_mk, hxo, hzo])
  have hz' : (⟨z, hzZ⟩ : Z) ∈ zpowers (⟨x, hxZ⟩ : Z) := by
    rw [h]
    exact mem_zpowers _
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hz'
  exact mem_zpowers_iff.mpr ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem false_of_coset_lines (hS : Setting G) (hU0 : FullCoreLocal G) (hD1 : TheoremD1 G)
    (K1 : StronglyEmbeddedRankTwoKFactNoBM) (K2 : StronglyEmbeddedCyclicOuterKFact)
    (K3 : KFactOutCyclic) (K4 : KFactComponentPCoreThree) (hno : NoExcludedSection3 G)
    (hKM : CFSG.AGLEmbeddingD2.KFactM11Three) (hKA : KFactM11TwoSignalizer)
    (hL : KFactsL34Full) (hA1 : A6SylowData) (hA3 : A6BorelCore) (hE1 : KFactL28Three)
    (hE3 : KFactL28BorelCore) (hp : 3 ∈ rankThreeSigmaA G) {P : Sylow 3 G} {M : Subgroup G}
    (hM : IsCoreMaxLocal 3 P M) {y z₀ w : G} (hy : IsLargeObstruction 3 M y) (hz₀M : z₀ ∈ M)
    (hz₀1 : z₀ ≠ 1) (hz₀3 : z₀ ^ 3 = 1) (hyz : y ∉ zpowers z₀) (hcomm : z₀ * y = y * z₀)
    (hwM : w ∈ M) (hwy : w * y * w⁻¹ = z₀ * y) (hwz : w * z₀ * w⁻¹ = z₀) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hyM, hy1, hy3, -, -⟩ := id hy
  obtain ⟨hDel, hDc⟩ := plane_zpowers_sup hy3 hz₀1 hz₀3 hyz hcomm
  have hDM : zpowers z₀ ⊔ zpowers y ≤ M := sup_le (zpowers_le.mpr hz₀M) (zpowers_le.mpr hyM)
  have hz₀D : z₀ ∈ zpowers z₀ ⊔ zpowers y := mem_sup_left (mem_zpowers z₀)
  have hyD : y ∈ zpowers z₀ ⊔ zpowers y := mem_sup_right (mem_zpowers y)
  have hbD : z₀ * y ∈ zpowers z₀ ⊔ zpowers y := Subgroup.mul_mem _ hz₀D hyD
  have hcD : z₀ * (z₀ * y) ∈ zpowers z₀ ⊔ zpowers y := Subgroup.mul_mem _ hz₀D hbD
  have hbLO : IsLargeObstruction 3 M (z₀ * y) := by
    have h := hy.conj hwM
    rwa [MulAut.conj_apply, hwy] at h
  have hcLO : IsLargeObstruction 3 M (z₀ * (z₀ * y)) := by
    have h := hbLO.conj hwM
    rwa [MulAut.conj_apply,
      show w * (z₀ * y) * w⁻¹ = (w * z₀ * w⁻¹) * (w * y * w⁻¹) by group, hwz, hwy] at h
  have hb3 : (z₀ * y) ^ 3 = 1 := hDel.2 _ hbD
  have hc3 : (z₀ * (z₀ * y)) ^ 3 = 1 := hDel.2 _ hcD
  have hb1 : z₀ * y ≠ 1 := hbLO.2.1
  have hc1 : z₀ * (z₀ * y) ≠ 1 := hcLO.2.1
  have hz₀o : orderOf z₀ = 3 := orderOf_eq_prime hz₀3 hz₀1
  have key : ∀ u : G, u ^ 3 = 1 → u ≠ 1 → u ∉ zpowers z₀ → z₀ * u ∉ zpowers u := by
    intro u hu3 hu1 huz h
    have hz : z₀ ∈ zpowers u := (Subgroup.mul_mem_cancel_right _ (mem_zpowers u)).mp h
    have := p34_zpowers_eq_of_mem (orderOf_eq_prime hu3 hu1) hz hz₀1
    exact huz (this ▸ mem_zpowers u)
  have hbz : z₀ * y ∉ zpowers z₀ := fun h =>
    hyz ((Subgroup.mul_mem_cancel_left _ (mem_zpowers z₀)).mp h)
  have hcz : z₀ * (z₀ * y) ∉ zpowers z₀ := fun h =>
    hbz ((Subgroup.mul_mem_cancel_left _ (mem_zpowers z₀)).mp h)
  have hba : z₀ * y ∉ zpowers y := key y hy3 hy1 hyz
  have hcb : z₀ * (z₀ * y) ∉ zpowers (z₀ * y) := key _ hb3 hb1 hbz
  have hay : z₀ * (z₀ * (z₀ * y)) = y := by
    calc z₀ * (z₀ * (z₀ * y)) = (z₀ * z₀ * z₀) * y := by group
      _ = z₀ ^ 3 * y := by rw [pow_three']
      _ = y := by rw [hz₀3, one_mul]
  have hac : y ∉ zpowers (z₀ * (z₀ * y)) := by
    have h := key _ hc3 hc1 hcz
    rwa [hay] at h
  exact false_of_three_lines hS hU0 hD1 K1 K2 K3 K4 hno hKM hKA hL hA1 hA3 hE1 hE3 hp hM hDM hDel
    hDc hyD hbD hcD hy1 hb1 hc1 (zpowers_ne_of_not_mem hba) (zpowers_ne_of_not_mem hac).symm
    (zpowers_ne_of_not_mem hcb) hy hbLO hcLO

end CFSG.LocalAnalysis.RankThreeTheoremC
