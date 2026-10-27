module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.Child8Tools
public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.GF2Type.Aschbacher1976Full.LeafDihedral

theorem dihedral_central_eq_r {m : ℕ} (hm : Even m) (hm2 : m ≠ 2)
    {c : DihedralGroup m} (hc : c ∈ Subgroup.center (DihedralGroup m)) (hc1 : c ≠ 1) :
    c = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) := by
  rw [DihedralGroup.center_eq_closure_of_even_ne_two hm hm2] at hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  have hsq : DihedralGroup.r ((m / 2 : ℕ) : ZMod m) ^ 2 = 1 := by
    have h2 : m / 2 * 2 = m := Nat.div_mul_cancel (even_iff_two_dvd.mp hm)
    rw [DihedralGroup.r_pow, DihedralGroup.one_def, ← Nat.cast_mul, h2, ZMod.natCast_self]
  have hk01 : k % ((2 : ℕ) : ℤ) = 0 ∨ k % ((2 : ℕ) : ℤ) = 1 := by omega
  rw [zpow_eq_zpow_emod' k hsq] at hk
  rcases hk01 with h | h
  · rw [h, zpow_zero] at hk
    exact absurd hk.symm hc1
  · rw [h, zpow_one] at hk
    exact hk.symm

theorem eq_of_central_involution {G : Type} [Group G] {H : Subgroup G} {m : ℕ} (hm : Even m)
    (hm2 : m ≠ 2) (e : ↥H ≃* DihedralGroup m) {a b : G} (ha : a ∈ H) (hb : b ∈ H)
    (hac : ∀ h ∈ H, h * a = a * h) (hbc : ∀ h ∈ H, h * b = b * h) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a = b := by
  have key : ∀ (x : G) (hx : x ∈ H), (∀ h ∈ H, h * x = x * h) → x ≠ 1 →
      e ⟨x, hx⟩ = DihedralGroup.r ((m / 2 : ℕ) : ZMod m) := by
    intro x hx hxc hx1
    refine dihedral_central_eq_r hm hm2 ?_ ?_
    · rw [Subgroup.mem_center_iff]
      intro d
      obtain ⟨h, rfl⟩ := e.surjective d
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hxc h.1 h.2)
    · intro h1
      apply hx1
      have h2 : (⟨x, hx⟩ : ↥H) = 1 := e.injective (by rw [h1, map_one])
      exact congrArg Subtype.val h2
  have h1 := key a ha hac ha1
  have h2 := key b hb hbc hb1
  exact congrArg Subtype.val (e.injective (h1.trans h2.symm))

theorem exists_sylow_two_centralizer {G : Type} [Group G] [Finite G] {z : G} (hz : orderOf z = 2)
    {m k : ℕ} (hm : Even m) (hm2 : m ≠ 2)
    (hcard : Nat.card (Subgroup.centralizer ({z} : Set G)) = 2 ^ k)
    (e : ↥(Subgroup.centralizer ({z} : Set G)) ≃* DihedralGroup m) :
    ∃ S : Sylow 2 G, (S : Subgroup G) = Subgroup.centralizer ({z} : Set G) := by
  have hz1 : z ≠ 1 := fun h => by simp [h] at hz
  have hzH : z ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr rfl
  refine CFSG.EvenSmallLie.OmegaEight.Child8.exists_sylow_eq_of_normalizer_le
    (IsPGroup.of_card hcard) (fun Q _ h1 h2 => le_antisymm h2 h1) ?_
  intro g hg
  have hnorm : ∀ h : G, h ∈ Subgroup.centralizer ({z} : Set G) ↔
      g * h * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) :=
    Subgroup.mem_normalizer_iff.mp hg
  have hbH : g * z * g⁻¹ ∈ Subgroup.centralizer ({z} : Set G) := (hnorm z).mp hzH
  have hbc : ∀ h ∈ Subgroup.centralizer ({z} : Set G),
      h * (g * z * g⁻¹) = (g * z * g⁻¹) * h := by
    intro h hh
    have hk : g⁻¹ * h * g ∈ Subgroup.centralizer ({z} : Set G) := by
      refine (hnorm _).mpr ?_
      have hconj : g * (g⁻¹ * h * g) * g⁻¹ = h := by group
      rw [hconj]
      exact hh
    have hkz := Subgroup.mem_centralizer_singleton_iff.mp hk
    calc h * (g * z * g⁻¹) = g * ((g⁻¹ * h * g) * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * h * g)) * g⁻¹ := by rw [hkz]
      _ = (g * z * g⁻¹) * h := by group
  have hb1 : g * z * g⁻¹ ≠ 1 := by
    intro h
    apply hz1
    calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hzc : ∀ h ∈ Subgroup.centralizer ({z} : Set G), h * z = z * h :=
    fun h hh => Subgroup.mem_centralizer_singleton_iff.mp hh
  have hzz : z = g * z * g⁻¹ := eq_of_central_involution hm hm2 e hzH hbH hzc hbc hz1 hb1
  apply Subgroup.mem_centralizer_singleton_iff.mpr
  calc g * z = (g * z * g⁻¹) * g := by group
    _ = z * g := by rw [← hzz]

theorem card_centralizer_transport {G H : Type} [Group G] [Group H] (e : G ≃* H) (x : G) :
    Nat.card (Subgroup.centralizer ({e x} : Set H)) =
      Nat.card (Subgroup.centralizer ({x} : Set G)) := by
  refine (Nat.card_congr (Equiv.subtypeEquiv e.toEquiv fun y => ?_)).symm
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff,
    MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, ← map_mul, ← map_mul, e.injective.eq_iff]

end CFSG.GF2Type.Aschbacher1976Full.LeafDihedral
