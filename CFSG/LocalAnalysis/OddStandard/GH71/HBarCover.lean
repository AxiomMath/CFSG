module

public import CFSG.LocalAnalysis.OddStandard.GH71.Frame
public import CFSG.LocalAnalysis.OddStandard.GH71.Covers

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2

variable {G : Type} [Group G] [Finite G] {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem exists_sylow_barIn (h : Ctx71 G z S U u) {H : Subgroup G} (hSH : S ≤ H) :
    ∃ Q : Sylow 2 (HBar H), (Q : Subgroup (HBar H)) = barIn H S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := Stage2.Final.sylow_of_sylowTop h.ctx.sylow_top
  have hPH : (P : Subgroup G) ≤ H := hP ▸ hSH
  refine ⟨(P.subtype hPH).mapSurjective (QuotientGroup.mk'_surjective (pPrimeCore 2 ↥H)), ?_⟩
  rw [Sylow.coe_mapSurjective, Sylow.coe_subtype, hP]
  rfl

theorem exists_maxSInv_not_le (h : Ctx71 G z S U u) (hB1 : SpecB1) {H : Subgroup G}
    (hSH : S ≤ H) (hcov : Covers H (Cen z) (pPrimeCoreOf 2 (Cen z))) :
    ∃ V, MaxSInv 3 S H V ∧ ¬ V ≤ pPrimeCoreOf 2 H := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfr := h.frame
  obtain ⟨X, hX3, hXS, -⟩ := hB1 _ _ hfr.cover hfr.sylow hfr.card
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥(Cen z)) with hπ
  set O := pPrimeCoreOf 2 (Cen z) with hO
  set W := (X.comap π).map (Cen z).subtype ⊓ H with hW
  have hWM : W ≤ Cen z := inf_le_left.trans (map_subtype_le _)
  have hWH : W ≤ H := inf_le_right
  have hWodd : Odd (Nat.card W) := by
    have h1 : Nat.card ((X.comap π).map (Cen z).subtype) =
        3 * Nat.card (pPrimeCore 2 ↥(Cen z)) := by
      rw [card_map_of_injective (Cen z).subtype_injective, L121.card_comap_mk', hX3]
    have h2 : Odd (3 * Nat.card (pPrimeCore 2 ↥(Cen z))) :=
      (by norm_num : Odd 3).mul (L121.odd_card_pPrimeCore' ↥(Cen z))
    exact odd_card_of_le inf_le_left (h1 ▸ h2)
  have hSW : S ≤ normalizer (W : Set G) := by
    intro s hs
    have hsM : s ∈ Cen z := h.S_le hs
    refine inf_normalizer_le_normalizer_inf ⟨?_, le_normalizer (hSH hs)⟩
    show s ∈ normalizer (((X.comap π).map (Cen z).subtype : Subgroup G) : Set G)
    rw [mem_normalizer_iff]
    have hsX : π ⟨s, hsM⟩ ∈ normalizer (X : Set (HBar (Cen z))) :=
      hXS ⟨⟨s, hsM⟩, hs, rfl⟩
    intro y
    constructor
    · rintro ⟨y', hy', rfl⟩
      refine ⟨⟨s, hsM⟩ * y' * ⟨s, hsM⟩⁻¹, ?_, rfl⟩
      show π (⟨s, hsM⟩ * y' * ⟨s, hsM⟩⁻¹) ∈ X
      rw [map_mul, map_mul, map_inv]
      exact (mem_normalizer_iff.mp hsX _).mp hy'
    · rintro ⟨y', hy', hy'e⟩
      have hyM : y ∈ Cen z := by
        have : y = s⁻¹ * (s * y * s⁻¹) * s := by group
        rw [this, ← hy'e]
        exact (Cen z).mul_mem ((Cen z).mul_mem ((Cen z).inv_mem hsM) y'.2) hsM
      refine ⟨⟨y, hyM⟩, ?_, rfl⟩
      have e : (⟨y, hyM⟩ : ↥(Cen z)) = ⟨s, hsM⟩⁻¹ * y' * ⟨s, hsM⟩ := by
        apply Subtype.ext
        show y = s⁻¹ * (y' : G) * s
        have hy'e' : (y' : G) = s * y * s⁻¹ := hy'e
        rw [hy'e']; group
      show π ⟨y, hyM⟩ ∈ X
      rw [e, map_mul, map_mul, map_inv]
      have := (mem_normalizer_iff.mp (inv_mem hsX) (π y')).mp hy'
      simpa [mul_assoc] using this
  obtain ⟨V₀, hV₀, -, hSV₀⟩ := Goldschmidt.G310.exists_invariant_sylow_containing Nat.prime_two
    Nat.prime_three h.S2 (not_two_dvd_of_odd hWodd) hSW bot_le IsPGroup.of_bot
    (fun s _ => by
      rw [mem_normalizer_iff]
      intro x
      simp only [mem_bot]
      constructor
      · intro hx; rw [hx]; group
      · intro hx
        have : x = s⁻¹ * (s * x * s⁻¹) * s := by group
        rw [this, hx]; group)
  have hWbar : barIn (Cen z) W = X := by
    apply le_antisymm
    · rintro _ ⟨w, hw, rfl⟩
      obtain ⟨⟨w', hw'⟩, hx, hwe⟩ := (Subgroup.mem_subgroupOf.mp hw).1
      have : w = ⟨w', hw'⟩ := Subtype.ext hwe.symm
      rw [this]; exact hx
    · intro x hx
      obtain ⟨⟨m, hm⟩, rfl⟩ := QuotientGroup.mk'_surjective _ x
      have hOM : H ⊓ Cen z ≤ normalizer (O : Set G) := fun y hy =>
        le_normalizer_pPrimeCoreOf' _ hy.2
      obtain ⟨a, ha, c, hc, hac⟩ := (covers_iff hOM).mp hcov m hm
      have hcM : c ∈ Cen z := pPrimeCoreOf_le' _ hc
      have hπa : π ⟨a, ha.2⟩ = π ⟨m, hm⟩ := by
        have e : (⟨m, hm⟩ : ↥(Cen z)) = ⟨a, ha.2⟩ * ⟨c, hcM⟩ := Subtype.ext hac
        rw [e, map_mul]
        obtain ⟨c', hc', hc'e⟩ := hc
        have : (⟨c, hcM⟩ : ↥(Cen z)) = c' := Subtype.ext hc'e.symm
        have h1 : π c' = 1 := (QuotientGroup.eq_one_iff _).mpr hc'
        rw [this, h1, mul_one]
      refine ⟨⟨a, ha.2⟩, ⟨⟨⟨a, ha.2⟩, ?_, rfl⟩, ha.1⟩, hπa⟩
      show π ⟨a, ha.2⟩ ∈ X
      rw [hπa]; exact hx
  have hrel : (W ⊓ O).relIndex W = 3 := by
    rw [IVK812.relIndex_eq_card_barIn hWM, hWbar, hX3]
  have hV₀O : ¬ V₀ ≤ pPrimeCoreOf 2 H := by
    intro hle
    have hOHM : pPrimeCoreOf 2 H ⊓ Cen z ≤ O := by
      refine le_pPrimeCoreOf_of_covers hcov inf_le_right
        (odd_card_of_le inf_le_left (odd_card_pPrimeCoreOf' H)) ?_
      intro y hy
      exact inf_normalizer_le_normalizer_inf
        ⟨le_normalizer_pPrimeCoreOf' H hy.1, le_normalizer hy.2⟩
    have hsub : V₀ ≤ W ⊓ O := le_inf hV₀.1 (le_inf hle (hV₀.1.trans hWM) |>.trans hOHM)
    have hdvd := relIndex_dvd_of_le_left W hsub
    rw [hrel] at hdvd
    obtain ⟨Q, hQ⟩ := Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hV₀
    have hidx : ¬ 3 ∣ V₀.relIndex W := by
      have heq : V₀.subgroupOf W = (Q : Subgroup ↥W) := by
        rw [← hQ]; exact Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
      rw [Subgroup.relIndex, heq]
      exact Sylow.not_dvd_index Q
    exact hidx hdvd
  obtain ⟨V, hV, hV₀V⟩ := exists_maxSInv_above (hV₀.1.trans hWH) hV₀.2.1 hSV₀
  exact ⟨V, hV, fun hle => hV₀O (hV₀V.trans hle)⟩

theorem hbar_of_covers (h : Ctx71 G z S U u) (hB1 : SpecB1) (h812 : IVK_8_12_ly)
    {H : Subgroup G} (hH : H ≠ ⊤) (hSH : S ≤ H)
    (hcov : Covers H (Cen z) (pPrimeCoreOf 2 (Cen z))) :
    IsDoubleCoverOfAlt (HBar H) 11 ∨ Blueprint.NativeSporadic.IsSporadic (HBar H) .Ly := by
  obtain ⟨V, hV, hVO⟩ := h.exists_maxSInv_not_le hB1 hSH hcov
  exact (h812 G z S h.ctx H hH hSH V hV hVO).1

end Ctx71

end CFSG.OddStandard.GH71
