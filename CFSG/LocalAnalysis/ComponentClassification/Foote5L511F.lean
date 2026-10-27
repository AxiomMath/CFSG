module

public import CFSG.LocalAnalysis.ComponentClassification.Foote5L511D
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.Foote5L510G

public noncomputable section

namespace CFSG.ComponentClassification.Foote5

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.FooteLit
  CFSG.ABGLocalTools GorensteinWalter

variable {G : Type} [Group G] [Finite G] {𝕊 : Type} [Group 𝕊]

theorem exists_lift_of_fixed_pgroup {L P : Subgroup G} (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
    (hP : IsPGroup 2 P) (hPN : P ≤ normalizer (L : Set G)) {x : 𝕊}
    (hfix : ∀ p ∈ P, actG L ε p x = x) :
    ∃ k : G, ∃ hk : k ∈ L, k ∈ centralizer (P : Set G) ∧ psi L ε ⟨k, hk⟩ = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨y, hyL⟩, rfl⟩ := psi_surjective ε x
  obtain ⟨y', hy'N, hy'⟩ := exists_commute_of_coprime (P := P) (N := oddCoreIn L)
    hP (fun h2 => by have := Nat.odd_iff.mp (odd_card_oddCoreIn L); omega)
    (fun p hp n hn => conj_mem_oddCoreIn ε (hPN hp) hn) (y := y) (fun p hp => by
      have h1 := hfix p hp
      rw [actG_psi ε (hPN hp)] at h1
      exact (psi_eq_iff ε _ _).mp h1.symm)
  have hy'L : y' ∈ L := by
    rw [show y' = y * (y⁻¹ * y') by group]
    exact mul_mem hyL (mem_of_mem_oddCoreIn hy'N)
  refine ⟨y', hy'L, mem_centralizer_iff.mpr fun p hp => hy' p hp, ?_⟩
  exact (psi_eq_iff ε ⟨y, hyL⟩ ⟨y', hy'L⟩).mpr hy'N |>.symm

omit [Finite G] in
theorem mem_map_psi_iff {L N : Subgroup G} (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊) {a : 𝕊} :
    a ∈ (N.subgroupOf L).map (psi L ε) ↔
      ∃ k : G, ∃ hk : k ∈ L, k ∈ N ∧ psi L ε ⟨k, hk⟩ = a := by
  constructor
  · rintro ⟨⟨k, hkL⟩, hkN, rfl⟩
    exact ⟨k, hkL, mem_subgroupOf.mp hkN, rfl⟩
  · rintro ⟨k, hkL, hkN, rfl⟩
    exact ⟨⟨k, hkL⟩, mem_subgroupOf.mpr hkN, rfl⟩

theorem exists_commuting_involution_lifts {L N : Subgroup G} (ε : L ⧸ pPrimeCore 2 L ≃* 𝕊)
    {a b : 𝕊} (ha : a ∈ (N.subgroupOf L).map (psi L ε))
    (hb : b ∈ (N.subgroupOf L).map (psi L ε)) (ha2 : a * a = 1) (hb2 : b * b = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a * b = b * a) :
    ∃ u ∈ N, ∃ v ∈ N, ∃ (hu : u ∈ L) (hv : v ∈ L), psi L ε ⟨u, hu⟩ = a ∧
      psi L ε ⟨v, hv⟩ = b ∧ u * u = 1 ∧ v * v = 1 ∧ u * v = v * u := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hkL, hkN, hka⟩ := (mem_map_psi_iff ε).mp ha
  obtain ⟨u, huN, huL, hψu, hu2, -, -⟩ := exists_involution_lift ε hkN hkL hka ha2 ha1
  obtain ⟨k', hk'L, hk'N, hk'b⟩ := (mem_map_psi_iff ε).mp hb
  have hNodd : ¬ 2 ∣ Nat.card ↥(N ⊓ oddCoreIn L) := fun h2 => by
    have h3 := Subgroup.card_dvd_of_le (inf_le_right : N ⊓ oddCoreIn L ≤ oddCoreIn L)
    have h4 := Nat.odd_iff.mp (odd_card_oddCoreIn L)
    have h5 := dvd_trans h2 h3
    omega
  have hPN : ∀ x ∈ zpowers u, ∀ n ∈ N ⊓ oddCoreIn L, x * n * x⁻¹ ∈ N ⊓ oddCoreIn L := by
    intro x hx n hn
    have hxN : x ∈ N := (zpowers_le.mpr huN) hx
    have hxL : x ∈ L := (zpowers_le.mpr huL) hx
    exact mem_inf.mpr ⟨mul_mem (mul_mem hxN (mem_inf.mp hn).1) (inv_mem hxN),
      conj_mem_oddCoreIn ε (le_normalizer hxL) (mem_inf.mp hn).2⟩
  have hy : ∀ x ∈ zpowers u, k'⁻¹ * (x * k' * x⁻¹) ∈ N ⊓ oddCoreIn L := by
    intro x hx
    have hxN : x ∈ N := (zpowers_le.mpr huN) hx
    have hxL : x ∈ L := (zpowers_le.mpr huL) hx
    refine mem_inf.mpr ⟨mul_mem (inv_mem hk'N) (mul_mem (mul_mem hxN hk'N) (inv_mem hxN)), ?_⟩
    have hxk : x * k' * x⁻¹ ∈ L := mul_mem (mul_mem hxL hk'L) (inv_mem hxL)
    refine (psi_eq_iff ε ⟨k', hk'L⟩ ⟨_, hxk⟩).mp ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.mp hx
    rw [show (⟨u ^ i * k' * (u ^ i)⁻¹, hxk⟩ : L) =
      ⟨u, huL⟩ ^ i * ⟨k', hk'L⟩ * (⟨u, huL⟩ ^ i)⁻¹ from rfl, map_mul, map_mul, map_inv,
      map_zpow, hψu, hk'b, (Commute.zpow_left hab i).eq, mul_inv_cancel_right]
  obtain ⟨k₂, hk₂N, hk₂c⟩ := exists_commute_of_coprime (P := zpowers u)
    (isPGroup_zpowers_of_pow_two (k := 1) (by rw [pow_one, sq]; exact hu2)) hNodd hPN hy
  have hk₂M : k₂ ∈ N := by
    rw [show k₂ = k' * (k'⁻¹ * k₂) by group]
    exact mul_mem hk'N (mem_inf.mp hk₂N).1
  have hk₂L : k₂ ∈ L := by
    rw [show k₂ = k' * (k'⁻¹ * k₂) by group]
    exact mul_mem hk'L (mem_of_mem_oddCoreIn (mem_inf.mp hk₂N).2)
  have hψk₂ : psi L ε ⟨k₂, hk₂L⟩ = b :=
    ((psi_eq_iff ε ⟨k', hk'L⟩ ⟨k₂, hk₂L⟩).mpr (mem_inf.mp hk₂N).2).symm.trans hk'b
  obtain ⟨v, hvN, hvL, hψv, hv2, -, m, rfl⟩ :=
    exists_involution_lift ε hk₂M hk₂L hψk₂ hb2 hb1
  exact ⟨u, huN, k₂ ^ m, hvN, huL, hvL, hψu, hψv, hu2, hv2,
    (Commute.pow_right (hk₂c u (mem_zpowers u)) m).eq⟩

namespace Sec5

variable {L₀ L Q S T : Subgroup G} {z t : G} (h : Sec5 G L₀ L Q S T z t)
include h

theorem mem_coreActionKernel_footeF_iff {b : G} (hbC : b ∈ coreActionKernel L)
    (hb2 : orderOf b = 2) {y : G} (hyN : y ∈ normalizer (L : Set G))
    (hyb : y ∈ centralizer ({b} : Set G)) :
    y ∈ coreActionKernel (footeF L₀ b) ↔ y ∈ coreActionKernel L := by
  have h4 := h.sec4
  obtain ⟨hfix, hLb, hLbF⟩ := footeFixed_eq_footeF h4.hLB h4.hGA h4.hGC h4.hSA
    h4.footeFamilyType h4.huniq h4.hrank2 h.pmax h.memF hb2 hbC
  obtain ⟨εb, hεb⟩ := exists_actG_eq_of_footeFixed hfix h.zL hb2 hbC hLb
    (MulEquiv.refl (L ⧸ pPrimeCore 2 L))
  have hyNb := le_normalizer_of_mem_footeFamilyOf h4.huniq hLb hLbF hyb
  rw [← actG_eq_one_iff εb hyNb, ← actG_eq_one_iff (MulEquiv.refl _) hyN, hεb y hyN hyNb hyb]

end Sec5

end CFSG.ComponentClassification.Foote5
