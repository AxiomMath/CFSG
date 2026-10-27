module

public import CFSG.LocalAnalysis.OddStandard.GH71.CUFacts
public import CFSG.LocalAnalysis.OddStandard.GH71.UFrame2

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_isPGroup_two_of_odd {X : Type*} [Group X] {A B : Subgroup X}
    (hA : IsPGroup 2 ↥A) (hB : Odd (Nat.card B)) {w : X} (hwA : w ∈ A) (hwB : w ∈ B) : w = 1 := by
  obtain ⟨k, hk⟩ := hA ⟨w, hwA⟩
  have h1 : orderOf w ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val hk)
  have h2 : orderOf w ∣ Nat.card B := by
    have := orderOf_dvd_natCard (⟨w, hwB⟩ : B)
    rwa [Subgroup.orderOf_mk] at this
  have hc : Nat.Coprime (2 ^ k) (Nat.card B) := (Nat.coprime_two_left.mpr hB).pow_left k
  exact orderOf_eq_one_iff.mp ((Nat.Coprime.coprime_dvd_left h1 hc).eq_one_of_dvd h2)

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem le_pPrimeCoreOf_centralizer_U (h : Ctx71 G z S U u) (hB1 : SpecB1) (hB2 : SpecB2)
    {W : Subgroup G} (hWC : W ≤ centralizer (U : Set G)) (hW3 : IsPGroup 3 ↥W)
    (hWS : S ≤ normalizer (W : Set G)) : W ≤ pPrimeCoreOf 2 (centralizer (U : Set G)) := by
  have hfr := h.frame
  obtain ⟨X, hX3, hXS, hXall⟩ := hB1 _ _ hfr.cover hfr.sylow hfr.card
  have hCM : centralizer (U : Set G) ≤ Cen z := by rw [h.centralizer_U]; exact inf_le_left
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) with hπ
  set Y := (X.comap π).map (Cen z).subtype ⊓ centralizer (U : Set G) with hY
  have huC : u ∈ Cen z := h.U_le.trans h.S_le h.u_mem
  have hWX : barIn (Cen z) W ≤ X :=
    hXall _ (IVK812.isPGroup_barIn hW3) (IVK812.barIn_le_normalizer hWS)
  have hWY : W ≤ Y := fun w hw =>
    ⟨⟨⟨w, hCM (hWC hw)⟩, hWX ⟨⟨w, hCM (hWC hw)⟩, hw, rfl⟩, rfl⟩, hWC hw⟩
  have hYodd : Odd (Nat.card Y) := by
    have h1 : Nat.card ((X.comap π).map (Cen z).subtype) =
        3 * Nat.card (pPrimeCore 2 ↥(Cen z)) := by
      rw [card_map_of_injective (Cen z).subtype_injective, L121.card_comap_mk', hX3]
    have h2 : Odd (3 * Nat.card (pPrimeCore 2 ↥(Cen z))) :=
      (by norm_num : Odd 3).mul (L121.odd_card_pPrimeCore' ↥(Cen z))
    exact odd_card_of_le inf_le_left (h1 ▸ h2)
  have hYn : centralizer (U : Set G) ≤ normalizer (Y : Set G) := by
    intro c hc
    have hcM : c ∈ Cen z := hCM hc
    have hcu : π ⟨c, hcM⟩ ∈ centralizer ({π ⟨u, huC⟩} : Set (HBar (Cen z))) := by
      rw [mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      exact (mem_centralizer_iff.mp hc u h.u_mem).symm
    have hcX : π ⟨c, hcM⟩ ∈ normalizer (X : Set (HBar (Cen z))) :=
      hB2 _ _ _ hfr X hX3 hXS (π ⟨u, huC⟩) ⟨⟨u, huC⟩, h.u_mem, rfl⟩
        (h.not_mem_center h.u_mem h.u_ne_one h.u_ne_z) hcu
    refine inf_normalizer_le_normalizer_inf ⟨?_, le_normalizer hc⟩
    show c ∈ normalizer (((X.comap π).map (Cen z).subtype : Subgroup G) : Set G)
    rw [mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨⟨c, hcM⟩ * y' * ⟨c, hcM⟩⁻¹, ?_, rfl⟩
      show π (⟨c, hcM⟩ * y' * ⟨c, hcM⟩⁻¹) ∈ X
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hcX _).mp hy'
    · rintro ⟨y', hy', hy'e⟩
      have hy'e' : (y' : G) = c * y * c⁻¹ := hy'e
      have hyM : y ∈ Cen z := by
        have : y = c⁻¹ * (c * y * c⁻¹) * c := by group
        rw [this, ← hy'e']
        exact (Cen z).mul_mem ((Cen z).mul_mem ((Cen z).inv_mem hcM) y'.2) hcM
      refine ⟨⟨y, hyM⟩, ?_, rfl⟩
      have e : (⟨y, hyM⟩ : ↥(Cen z)) = ⟨c, hcM⟩⁻¹ * y' * ⟨c, hcM⟩ := by
        apply Subtype.ext
        show y = c⁻¹ * (y' : G) * c
        rw [hy'e']; group
      show π ⟨y, hyM⟩ ∈ X
      rw [e, map_mul, map_mul, map_inv]
      have := (mem_normalizer_iff.mp (inv_mem hcX) (π y')).mp hy'
      simpa [mul_assoc] using this
  exact hWY.trans (le_pPrimeCoreOf_of_odd inf_le_right hYodd hYn)

theorem U_le_commutator (h : Ctx71 G z S U u) (hB0 : SpecB0) : U ≤ ⁅S, S⁆ := by
  have h0 := hB0 _ _ _ h.frame
  have hSC : S ≤ Cen z := h.S_le
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) with hπ
  set S' := S.subgroupOf (Cen z) with hS'
  have hS'2 : IsPGroup 2 ↥S' := h.S2.comap_subtype
  have hle : ⁅S', S'⁆ ≤ S' := Subgroup.commutator_le.mpr fun a ha b hb => by
    rw [commutatorElement_def]
    exact S'.mul_mem (S'.mul_mem (S'.mul_mem ha hb) (S'.inv_mem ha)) (S'.inv_mem hb)
  have e : (⁅S', S'⁆).map (Cen z).subtype = ⁅S, S⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSC]
  intro x hx
  have hxC : x ∈ Cen z := h.U_le.trans hSC hx
  have hbar : π ⟨x, hxC⟩ ∈ ⁅S'.map π, S'.map π⁆ := h0 ⟨⟨x, hxC⟩, hx, rfl⟩
  rw [← Subgroup.map_commutator] at hbar
  obtain ⟨y, hy, hyx⟩ := hbar
  have hxS' : (⟨x, hxC⟩ : ↥(Cen z)) ∈ S' := h.U_le hx
  have hmem : y⁻¹ * ⟨x, hxC⟩ ∈ pPrimeCore 2 ↥(Cen z) := by
    rw [← QuotientGroup.eq_one_iff]
    show π (y⁻¹ * ⟨x, hxC⟩) = 1
    rw [map_mul, map_inv, hyx, inv_mul_cancel]
  have h1 := eq_one_of_isPGroup_two_of_odd hS'2 (L121.odd_card_pPrimeCore' ↥(Cen z))
    (S'.mul_mem (S'.inv_mem (hle hy)) hxS') hmem
  have hyx' : y = ⟨x, hxC⟩ := inv_mul_eq_one.mp h1
  rw [← e]
  exact ⟨y, hy, by rw [hyx']; rfl⟩

theorem exists_conj_of_covers_N (h : Ctx71 G z S U u) {K : Subgroup G}
    (hcov : Covers K (normalizer (U : Set G)) (pPrimeCoreOf 2 (normalizer (U : Set G)))) :
    ∃ k ∈ K, k * z * k⁻¹ = u := by
  obtain ⟨g, ⟨hgU, -⟩, hgz⟩ := h.exists_conj_u
  have hON : K ⊓ normalizer (U : Set G) ≤
      normalizer (pPrimeCoreOf 2 (normalizer (U : Set G)) : Set G) :=
    fun y hy => le_normalizer_pPrimeCoreOf' _ hy.2
  obtain ⟨a, ha, c, hc, rfl⟩ := (covers_iff hON).mp hcov g hgU
  have hcC : c ∈ centralizer (U : Set G) := by
    rw [h.pPrimeCoreOf_normalizer_U] at hc
    exact pPrimeCoreOf_le' _ hc
  have hcz : c * z * c⁻¹ = z := by
    rw [mem_centralizer_iff.mp hcC z h.z_mem |>.symm]; group
  refine ⟨a, ha.1, ?_⟩
  rw [← hgz]
  calc a * z * a⁻¹ = a * (c * z * c⁻¹) * a⁻¹ := by rw [hcz]
    _ = a * c * z * (a * c)⁻¹ := by group

end Ctx71

end CFSG.OddStandard.GH71
