module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.Thm4TwinDefs
public import CFSG.ClassicalInvolution.Q3.TL4SepCent

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
  CFSG.ClassicalInvolution.Q3

namespace Thm4Twin

variable {r : ℕ} {G : Type} [Group G] [Finite G] {Δ : Set (Subgroup G)}

omit [Finite G] in
theorem TwinT4Hyp.gen (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) :
    Subgroup.closure {x : G | x ∈ J ∧ IsPGroup 2 (Subgroup.zpowers x)} = J := by
  rcases h.hyp.omega2 J hJ with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨e⟩ := h1
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp ((h.twoGroup J hJ).of_equiv e)
    rw [natCard_sl2Three] at hk
    have h3 : 3 ∣ 2 ^ k := hk ▸ (by norm_num : 3 ∣ 24)
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)

theorem TwinT4Hyp.le_centralizer_of_not_mem (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ)
    {u : G} (hu : IsUniqueInvolution J u) {X : Subgroup G} (hX : X.Normal) (huX : u ∉ X) :
    J ≤ Subgroup.centralizer (X : Set G) := by
  have hOX : oddCoreOf X = ⊥ := by
    rw [oddCoreOf, TL4.oddCore_eq_bot_of_normal h.odd hX, Subgroup.map_bot]
  rw [← h.gen hJ, Subgroup.closure_le]
  rintro x ⟨hxJ, hx2⟩
  obtain ⟨T, hT, hTJ, hxT⟩ := exists_mem_RSet_ge hJ hx2 (Subgroup.zpowers_le.mpr hxJ)
  have hTX : T ⊓ X = ⊥ := by
    by_contra hne
    exact huX (TL4.mem_of_isPGroup_of_ne_bot hu (inf_le_left.trans hTJ.1)
      (hTJ.2.1.to_le inf_le_left) hne).2
  have hc := comm613Gen_normal h.hyp hT hX hTX
  rw [hOX, le_bot_iff, Subgroup.commutator_eq_bot_iff_le_centralizer] at hc
  exact hc (hxT (Subgroup.mem_zpowers x))

variable {J L : Subgroup G}

theorem TwinT4Hyp.le_center_of_normal_two (h : TwinT4Hyp r G Δ) (hgen : omegaGen Δ = ⊤)
    (hno : TL4.NoInvO2 Δ) {P : Subgroup G} (hP : P.Normal) (hP2 : IsPGroup 2 P) :
    P ≤ Subgroup.center G := by
  have hle : omegaGen Δ ≤ Subgroup.centralizer (P : Set G) := by
    refine iSup₂_le fun J hJ => ?_
    obtain ⟨u, hu⟩ := (h.hyp.omega1 J hJ).1
    exact h.le_centralizer_of_not_mem hJ hu hP fun huP => hno J hJ u hu ⟨P, hP, hP2, huP⟩
  rw [hgen] at hle
  intro p hp
  refine Subgroup.mem_center_iff.mpr fun g => ?_
  exact ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top g))) p hp).symm

theorem TwinT4Hyp.mem_layer (h : TwinT4Hyp r G Δ) {J : Subgroup G} (hJ : J ∈ Δ) {u : G}
    (hu : IsUniqueInvolution J u) (hno : ¬ TightInO2 u) : u ∈ layer G := by
  by_contra huE
  have hEn : (layer G).Normal := by
    have := CFSG.LocalCores.layer_characteristic (G := G)
    infer_instance
  have hE := h.le_centralizer_of_not_mem hJ hu hEn huE
  have hF := h.le_centralizer_of_not_mem hJ hu fittingSubgroup_normal fun huF =>
    hno ⟨_, fittingSubgroup_normal, TL4.isPGroup_fittingSubgroup h.odd, huF⟩
  have hC : J ≤ Subgroup.centralizer (generalizedFitting G : Set G) :=
    TL4.le_centralizer_sup hF hE
  have hJF : J ≤ generalizedFitting G := hC.trans (centralizer_generalizedFitting_le G)
  obtain ⟨-, P, hP, hPnc⟩ := h.hyp.omega1 J hJ
  refine hPnc ⟨⟨fun a b => Subtype.ext ?_⟩⟩
  have hb := Subgroup.mem_centralizer_iff.mp (hC (hP.1 a.2)) b (hJF (hP.1 b.2))
  exact hb.symm

end Thm4Twin

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
