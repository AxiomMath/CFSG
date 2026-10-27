module

public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBKGF2CriticalQuotientWidth
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergCCTICommutingCenterWidth

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GorensteinLyons

open Subgroup CFSG.Open
open CFSG.SectionRank.Ccomm (ThompsonCritical)
open CFSG.LocalAnalysis.ComponentInitial (bilinIsometryGroup)
open scoped IsMulCommutative commutatorElement

namespace SteinbergBQ.HigherCenter

variable {G : Type*} [Group G]

theorem critical_form_data
    [Finite G] (hchar : IsCharacteristicPType G 2)
    (he : 4 ≤ CFSG.twoLocalOddRank G) {M B : Subgroup G} (hM : GLAIsMaxTwoLocal M)
    (hsym : GLASymplecticType (pCoreOf 2 M)) (hB : GLAIsBmax 3 B) (hBM : B ≤ M) {Q : Subgroup G}
    (hQ : Q = CFSG.inSubgroup (CFSG.pCore 2) M) {z : G} (hzQ : z ∈ (center Q).map Q.subtype)
    (hz : orderOf z = 2) {D : Subgroup Q} (hD : ThompsonCritical D) {u : ℕ}
    (hu : Nat.card (D ⧸ center D) = 2 ^ (2 * u)) {D' : Subgroup M}
    (hD' : D' = (D.map Q.subtype).subgroupOf M) :
    ∃ _ : IsElementaryAbelian 2 (D' ⧸ center D'),
    ∃ b : LinearMap.BilinForm (ZMod 2) (Additive (D' ⧸ center D')),
      (∀ x y : D', (((⁅x, y⁆ : D') : M) : G) = z ^ (b (Additive.ofMul (x : D' ⧸ center D'))
        (Additive.ofMul (y : D' ⧸ center D'))).val) ∧
      (∀ b' : LinearMap.BilinForm (ZMod 2) (Additive (D' ⧸ center D')),
        (∀ x y : D', (((⁅x, y⁆ : D') : M) : G) = z ^ (b' (Additive.ofMul (x : D' ⧸ center D'))
          (Additive.ofMul (y : D' ⧸ center D'))).val) → b' = b) ∧
      b.IsAlt ∧ b.Nondegenerate ∧
      Module.finrank (ZMod 2) (Additive (D' ⧸ center D')) = 2 * u ∧
      ∃ ι : M ⧸ CFSG.pCore 2 M →* bilinIsometryGroup b, Function.Injective ι ∧
        ∀ (m : M) (x y : D'), (y : M) = m * x * m⁻¹ →
          (((ι (m : M ⧸ CFSG.pCore 2 M) : bilinIsometryGroup b) :
            LinearMap.GeneralLinearGroup (ZMod 2) (Additive (D' ⧸ center D'))) :
              Module.End (ZMod 2) (Additive (D' ⧸ center D')))
            (Additive.ofMul (x : D' ⧸ center D')) = Additive.ofMul (y : D' ⧸ center D') := by
  classical
  have hQM : Q ≤ M := hQ ▸ map_subtype_le _
  obtain ⟨-, -, z', -, -, hz'u, hEA, b, hb, hbu, hbalt, hbnd, w, -, hw, -,
    ⟨ρ, hρ, -, -, ⟨ι, hι, hιρ⟩, -⟩, -⟩ :=
    (gf2_critical_quotient_and_width_at_rank_four hchar he hM hsym hB hBM hQ rfl).2 D hD D' hD'
  obtain ⟨zq, hzqc, hzq⟩ := hzQ
  have hzq' : (zq : G) = z := hzq
  have hzqD : zq ∈ D := by
    have h1 : zq ∈ centralizer (D : Set Q) :=
      mem_centralizer_iff.2 fun d _ => mem_center_iff.1 hzqc d
    rw [hD.2.2.2] at h1
    exact h1.1
  have hzM : z ∈ M := hzq' ▸ hQM zq.2
  have hzD' : (⟨z, hzM⟩ : M) ∈ D' := by
    rw [hD', mem_subgroupOf]
    exact ⟨zq, hzqD, hzq⟩
  have hzc : (⟨⟨z, hzM⟩, hzD'⟩ : D') ∈ center D' := by
    rw [mem_center_iff]
    intro x
    have hx : ((x : M) : G) ∈ D.map Q.subtype := by
      have h1 : ∀ m : M, m ∈ D' → (m : G) ∈ D.map Q.subtype := fun m hm => by
        rw [hD', mem_subgroupOf] at hm
        exact hm
      exact h1 x x.2
    obtain ⟨d, -, hd⟩ := hx
    apply Subtype.ext
    apply Subtype.ext
    change ((x : M) : G) * z = z * ((x : M) : G)
    rw [← hd, ← hzq']
    exact congrArg Subtype.val (mem_center_iff.1 hzqc d)
  have hz2 : orderOf (⟨⟨z, hzM⟩, hzD'⟩ : D') = 2 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    exact hz
  have hzz' : ((z' : M) : G) = z := by
    rw [← hz'u _ hzc hz2]
  have hpow : ∀ n : ℕ, (((z' ^ n : D') : M) : G) = z ^ n := fun n => by
    rw [Subgroup.coe_pow, Subgroup.coe_pow, hzz']
  have hDM : D.map Q.subtype ≤ M := (map_subtype_le D).trans hQM
  let e : D ≃* D' := ((D.equivMapOfInjective Q.subtype Q.subtype_injective).trans
    (subgroupOfEquivOfLe hDM).symm).trans (MulEquiv.subgroupCongr hD'.symm)
  have hcard : Nat.card (D ⧸ center D) = Nat.card (Additive (D' ⧸ center D')) :=
    Nat.card_congr
      ((QuotientGroup.congr _ _ e (TICommutingCenters.center_map_equiv e)).toEquiv.trans
        Additive.ofMul)
  have h2 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (D' ⧸ center D'))
  rw [Nat.card_zmod, hw, ← hcard, hu] at h2
  have hwu : w = u := by
    have h3 := Nat.pow_right_injective (le_refl 2) h2
    omega
  subst hwu
  refine ⟨hEA, b, fun x y => ?_, fun b' hb' => hbu b' fun x y => ?_, hbalt, hbnd, hw, ι, hι,
    fun m x y hxy => ?_⟩
  · rw [hb x y, hpow]
  · apply Subtype.ext
    apply Subtype.ext
    rw [hb' x y, hpow]
  · rw [hιρ m]
    exact hρ m x y hxy

end SteinbergBQ.HigherCenter

end CFSG.LocalAnalysis.GorensteinLyons
