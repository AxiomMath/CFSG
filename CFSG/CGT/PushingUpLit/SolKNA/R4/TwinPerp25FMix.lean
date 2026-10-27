module

public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FPsiC
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25FEC2
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinFusion
public import CFSG.ClassicalInvolution.Q3.TL4LinkZ2L2B4A
public import CFSG.CGT.PushingUpLit.SolKNA.R4.TwinPerp25F0

public section

set_option linter.unusedSectionVars false

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.C2516

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

section Mix


theorem mix14R_proof {r n : ℕ} (hr : 4 ≤ r) : Mix14R r n := by
  intro Y _ _ R S t hP K' W S₁ R₁ R₂ t₁ u₁ u₂ hyp h11 a haS ha2 hF
  classical
  obtain ⟨A, _, Ψ, hΨ1, hΨ2, hΨ3⟩ := exists_psi hr hP hyp
  by_cases hΨa : Ψ ⟨a, haS⟩ = 1
  · exact hΨ3 a haS ha2 hF hΨa
  exfalso
  have hs := hyp.std.setting
  have hΩ : HypOmegaGen (CoreAssembly.conjClass (tightCore R)) := hs.stand.hyp
  have hK : tightCore R ∈ CoreAssembly.conjClass (tightCore R) := hs.stand.mem
  have hzK : IsUniqueInvolution (tightCore R) t := hs.hz
  have hR₁ : IsSylow2In R₁ (tightCore R) :=
    T7F25.Asc77.T7C.isSylow2In_of_mem_RSet_of_le hΩ hK hyp.hR.1 hyp.hR.2.1
  let Nk : Subgroup Y := Ψ.ker.map (S₁ : Subgroup Y).subtype
  have hmemNk : ∀ (g : Y) (hg : g ∈ (S₁ : Subgroup Y)), Ψ ⟨g, hg⟩ = 1 → g ∈ Nk := fun g hg h =>
    Subgroup.mem_map.mpr ⟨⟨g, hg⟩, MonoidHom.mem_ker.mpr h, rfl⟩
  have hcomm : ∀ (y z : ↥(S₁ : Subgroup Y)), Ψ (y * z * y⁻¹ * z⁻¹) = 1 := by
    intro y z
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (Ψ y) (Ψ z)]
    group
  obtain ⟨t', hT⟩ := T7F25.Asc77.T7T.exists_hyp25T hyp
  have hR₁ord : ∀ y ∈ R₁, y ≠ 1 → y = t ∨ 4 ∣ orderOf y := by
    intro y hy hy1
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR₁.2.1) ⟨y, hy⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · exact absurd (orderOf_eq_one_iff.mp (by simpa using hk)) hy1
      · left
        have hy2 : y * y = 1 := by
          have h1 := pow_orderOf_eq_one y
          rw [hk] at h1
          have : y ^ 2 = 1 := by simpa using h1
          rwa [pow_two] at this
        exact (hT.hzR.unique y hy hy2).resolve_left hy1
    · right
      rw [hk]
      exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
  set C : Subgroup Y := Subgroup.centralizer ({t} : Set Y) with hC
  have hec := ec_twin hr hP hyp h11
  have hweak : ∀ y ∈ R₁, y ≠ 1 → ∀ g : Y, g⁻¹ * y * g ∈ (S₁ : Subgroup Y) →
      g⁻¹ * y * g ∈ Nk := by
    intro y hy hy1 g hg
    rcases hR₁ord y hy hy1 with rfl | h4
    · refine hmemNk _ hg (hΨ2 _ hg ?_ ⟨g⁻¹, by simp⟩)
      calc g⁻¹ * y * g * (g⁻¹ * y * g) = g⁻¹ * (y * y) * g := by group
        _ = 1 := by rw [hzK.sq]; group
    · obtain ⟨-, hR⟩ := conj_four_dvd hP hyp (Or.inl hy) h4 hg
      exact hmemNk _ hg (hΨ1 _ hg hR)
  have hfus : ∀ g : Y, (∀ y ∈ (S₁ : Subgroup Y) ⊓ Subgroup.centralizer ({a} : Set Y),
      g⁻¹ * y * g ∈ (S₁ : Subgroup Y)) → a⁻¹ * (g⁻¹ * a * g) ∈ Nk := by
    intro g hg
    obtain ⟨w, hwR₂, hwa, hw4⟩ := exists_order_four_of_isFAut hF
    have hwS : w ∈ (S₁ : Subgroup Y) := hyp.hR'.2.2 hwR₂
    have hwg := hg w ⟨hwS, Subgroup.mem_centralizer_singleton_iff.mpr hwa⟩
    obtain ⟨hgt, -⟩ := conj_four_dvd hP hyp (Or.inr hwR₂) (by rw [hw4]) hwg
    have hgC : g ∈ C := by
      rw [hC, Subgroup.mem_centralizer_singleton_iff]
      have : g * t * g⁻¹ = t := hgt
      calc g * t = (g * t * g⁻¹) * g := by group
        _ = t * g := by rw [this]
    have hagS := hg a ⟨haS, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    obtain ⟨s', hs', hs'e⟩ := exists_conj_eq_of_normal_complement (K := C)
      (O := Balance.oddCoreIn C) (P := (S₁ : Subgroup Y)) (Balance.oddCoreIn_le C)
      (fun k hk o ho => Balance.conj_mem_oddCoreIn hk ho) (Balance.odd_card_oddCoreIn C)
      S₁.isPGroup' (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr (hyp.hzS s hs))
      hec haS hgC hagS
    have hs'S : s' ∈ (S₁ : Subgroup Y) := hs'
    have hcom := hcomm ⟨a, haS⟩⁻¹ ⟨s', hs'S⟩⁻¹
    refine hmemNk _ ((S₁ : Subgroup Y).mul_mem ((S₁ : Subgroup Y).inv_mem haS) hagS) ?_
    have e : (⟨a⁻¹ * (g⁻¹ * a * g), (S₁ : Subgroup Y).mul_mem ((S₁ : Subgroup Y).inv_mem haS)
        hagS⟩ : ↥(S₁ : Subgroup Y)) = ⟨a, haS⟩⁻¹ * ⟨s', hs'S⟩⁻¹ * ⟨a, haS⟩⁻¹⁻¹ *
        ⟨s', hs'S⟩⁻¹⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      rw [hs'e]; group
    rw [e]
    exact hcom
  have hxN : a ∉ Nk := by
    intro h
    obtain ⟨g, hg, hga⟩ := Subgroup.mem_map.mp h
    have : g = ⟨a, haS⟩ := Subtype.ext hga
    rw [this] at hg
    exact hΨa (MonoidHom.mem_ker.mp hg)
  exact TL4.LinkZ2B.false_of_transfer_of_hom (R₀ := R₁)
    (fun A' _ f hf => hP.hom_eq_one hK hR₁ f hf) S₁ (N := Nk)
    (fun y hy z hz => hmemNk _ ((S₁ : Subgroup Y).mul_mem ((S₁ : Subgroup Y).mul_mem
      ((S₁ : Subgroup Y).mul_mem hy hz) ((S₁ : Subgroup Y).inv_mem hy)) ((S₁ : Subgroup Y).inv_mem hz))
      (hcomm ⟨y, hy⟩ ⟨z, hz⟩)) haS hxN (by rw [sq]; exact ha2) hfus hweak

end Mix

end CFSG.CGT.PushingUpLit.SolKNA.R4.C2516
