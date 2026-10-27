module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKPocket
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5PKOdd
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OPDefs
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec5OStep1

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

theorem sec5op_lemmaK {G : Type} [Group G] [Finite G] {t : G} {L S : Subgroup G} {z r ρ : G}
    {B A : Subgroup G} {φ : (Fin 6 → ZMod 2) → G} {K₁ K₂ : Subgroup G} {a b : G}
    (hy : Sec5B59Hyp) (hD : Asc82FactQCentOrd6) (hK : Asc82FactQCentTwo6)
    (hO3 : IsPGroup 3 (oddCoreIn L)) (h : Sec510Ctx G t L S z r ρ B A φ)
    (hs : Sec510Stage1 G t L S z φ A K₁ K₂ a b) {K : Subgroup G} (hKi : K = K₁ ∨ K = K₂) :
    ∃ K' : Subgroup G, Sl23PocketIn L z K' ∧ twoCoreIn K' = twoCoreIn K ∧
      K' ≤ centralizer ((sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) : Subgroup G) : Set G) ∧
      oddCoreIn K' = oddCoreIn L ⊓
        centralizer ((sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂) : Subgroup G) : Set G) ∧
      (∀ k ∈ K', Odd (orderOf k) → ∃ n : ℕ, orderOf k = 3 ^ n) ∧ twoRes K' = K' := by
  let R : Subgroup G := sec5p510_R S (twoCoreIn K₁) (twoCoreIn K₂)
  let K' : Subgroup G := (K ⊔ oddCoreIn L) ⊓ centralizer (R : Set G)
  have hOc : ∀ o ∈ oddCoreIn L, ∀ l ∈ L, l * o * l⁻¹ = o := by
    intro o ho l hl
    have hZ : oddCoreIn L ≤ centerIn L :=
      sec5o_oddCoreIn_le_centerIn h.toSec5Setting.isOm6Z2
    have hcomm : o * l = l * o := (sec5_mem_centerIn_iff.mp (hZ ho)).2 l hl
    rw [← hcomm]
    group
  have hpocket : Sl23PocketIn L z K := by
    rcases hKi with rfl | rfl
    · exact hs.pk.pocket₁
    · exact hs.pk.pocket₂
  have hOK : oddCoreIn K ≤ oddCoreIn L :=
    sec5pk_oddCoreIn_pocket_le hD h.toSec5Ctx hs.pk hKi
  have hR2 : IsPGroup 2 R := h.syl.2.1.to_le inf_le_left
  have hRz : ∀ x ∈ R, x * z = z * x := by
    intro x hx
    have hx' : x ∈ S ⊓ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) := by
      simpa only [R, sec5p510_R] using hx
    exact h.central x hx'.1
  have hRN : R ≤ normalizer (L : Set G) := sec5p510_R_le_normalizer hy h.toSec5Ctx
  have hRQ : ∀ x ∈ R, ∀ q ∈ twoCoreIn K, x * q = q * x := by
    intro x hx q hq
    have hx' : x ∈ S ⊓ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) := by
      simpa only [R, sec5p510_R] using hx
    have hqQ : q ∈ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
      have hle : twoCoreIn K ≤ twoCoreIn K₁ ⊔ twoCoreIn K₂ := by
        rcases hKi with hK₁ | hK₂
        · rw [hK₁]; exact le_sup_left
        · rw [hK₂]; exact le_sup_right
      exact hle hq
    exact (Subgroup.mem_centralizer_iff.mp hx'.2 q hqQ).symm
  have hQ : Nonempty (↥(twoCoreIn K) ≃* QuaternionGroup 2) := by
    rcases hKi with rfl | rfl
    · exact hs.pk.q.iso₁
    · exact hs.pk.q.iso₂
  have hFF4 : ∀ x ∈ R, ∀ n ∈ twoRes (L ⊓ centralizer ({z} : Set G)),
      x * n * x⁻¹ * n⁻¹ ∈ oddCoreIn L := by
    intro x hx n hn
    have hx' : x ∈ S ⊓ centralizer ((twoCoreIn K₁ ⊔ twoCoreIn K₂ : Subgroup G) : Set G) := by
      simpa only [R, sec5p510_R] using hx
    have hxN : x ∈ normalizer (L : Set G) := sec5p510_R_le_normalizer hy h.toSec5Ctx hx
    have hxz : x ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr (h.central x hx'.1)
    exact hK G L z h.toSec5Setting.isOm6Z2 h.pocket K₁ K₂ hs.pk.pocket₁ hs.pk.pocket₂ hs.pk.ne
      hs.pk.q.iso₁ hs.pk.q.iso₂ hs.pk.q.comm hs.pk.q.card hs.pk.q.center
      x hxN hxz hx'.2 n hn
  obtain ⟨h1, h2, h3, h4, h5⟩ :=
    sec5pk_pocket (L := L) (K := K) (R := R) (K' := K') (z := z)
      rfl hpocket hOc hOK hO3 hR2 hRz hRN hRQ hQ hFF4
  exact ⟨K', h1, h2, inf_le_right, h3, h4, h5⟩

end CFSG.OddStandard.SmallF3.Omega
