module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12Coprime
public import CFSG.ClassicalInvolution.Asc77.WP2Defs
public import CFSG.ClassicalInvolution.Asc77.WP3Layer
public import CFSG.GroupTheory.SteinbergBSQuotientLifting

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinExitPf12

section Pair

variable {G : Type} [Group G] [Finite G]

@[expose] def InO2C (z u : G) : Prop :=
  ∃ P : Subgroup G, P ≤ Subgroup.centralizer ({u} : Set G) ∧
    (P.subgroupOf (Subgroup.centralizer ({u} : Set G))).Normal ∧ IsPGroup 2 P ∧ z ∈ P

theorem oddCoreIn_le_centralizer_of_inO2 {z u : G} (h : InO2C u z) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ Subgroup.centralizer ({u} : Set G) := by
  obtain ⟨P, hPC, hPn, hP2, huP⟩ := h
  set C : Subgroup G := Subgroup.centralizer ({z} : Set G) with hC
  intro n hn
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hnC : n ∈ C := oddCoreIn_le C hn
  have key : n * u * n⁻¹ * u⁻¹ = 1 := by
    set c := n * u * n⁻¹ * u⁻¹ with hc
    have hcP : c ∈ P := by
      have h1 : (⟨n, hnC⟩ : ↥C) * ⟨u, hPC huP⟩ * (⟨n, hnC⟩ : ↥C)⁻¹ ∈ P.subgroupOf C :=
        hPn.conj_mem ⟨u, hPC huP⟩ (Subgroup.mem_subgroupOf.mpr huP) ⟨n, hnC⟩
      have h2 : n * u * n⁻¹ ∈ P := Subgroup.mem_subgroupOf.mp h1
      exact P.mul_mem h2 (P.inv_mem huP)
    have hcN : c ∈ oddCoreIn C := by
      have h3 : u * n⁻¹ * u⁻¹ ∈ oddCoreIn C := conj_mem_oddCoreIn (hPC huP) ((oddCoreIn C).inv_mem hn)
      have : c = n * (u * n⁻¹ * u⁻¹) := by rw [hc]; group
      rw [this]
      exact (oddCoreIn C).mul_mem hn h3
    exact eq_one_of_odd_orderOf_of_pGroup hP2 hcP
      (odd_orderOf_of_mem_odd (odd_card_oddCoreIn C) hcN)
  calc n * u = (n * u * n⁻¹ * u⁻¹) * u * n := by group
    _ = u * n := by rw [key]; group

omit [Finite G] in
theorem centralizer_zpowers_eq {K : Type} [Group K] (x : K) :
    Subgroup.centralizer (Subgroup.zpowers x : Set K) = Subgroup.centralizer ({x} : Set K) := by
  ext g
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    exact h x (Subgroup.mem_zpowers x)
  · intro h y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact (Commute.zpow_left (show Commute x g from h) k).eq

theorem oddCoreIn_le_oddCoreIn_of_inO2 {z u : G} (hz2 : IsPGroup 2 (Subgroup.zpowers z))
    (hzu : z * u = u * z) (hA : InO2C u z) (hB : InO2C z u) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) ≤ oddCoreIn (Subgroup.centralizer ({u} : Set G)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup G := Subgroup.centralizer ({u} : Set G) with hH
  set N : Subgroup G := oddCoreIn (Subgroup.centralizer ({z} : Set G)) with hN
  have hNH : N ≤ H := oddCoreIn_le_centralizer_of_inO2 hA
  have hzH : z ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr hzu
  set zH : ↥H := ⟨z, hzH⟩ with hzHdef
  obtain ⟨P, hPH, hPn, hP2, hzP⟩ := hB
  set O : Subgroup ↥H := classicalInvolutionOddCore ↥H with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  have hOodd : Odd (Nat.card O) := CFSG.ComponentClassification.OddCore.odd_card ↥H
  have hOnd : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  have hOq : classicalInvolutionOddCore (↥H ⧸ O) = ⊥ :=
    CFSG.ComponentClassification.OddCore.quotient_corefree ↥H
  set Pb : Subgroup (↥H ⧸ O) := (P.subgroupOf H).map π with hPb
  have hPbn : Pb.Normal := hPn.map π (QuotientGroup.mk'_surjective O)
  have hPb2 : IsPGroup 2 Pb :=
    (hP2.comap_subtype).of_surjective (π.subgroupMap (P.subgroupOf H)) (π.subgroupMap_surjective _)
  have hzPb : π zH ∈ Pb := ⟨zH, Subgroup.mem_subgroupOf.mpr hzP, rfl⟩
  have h35 := oddCoreIn_centralizer_eq_bot_of_mem_normal hOq hPbn hPb2 hzPb
  have hQ : IsPGroup 2 (Subgroup.zpowers zH) := by
    refine hz2.of_injective
      ((H.subtype.comp (Subgroup.zpowers zH).subtype).codRestrict (Subgroup.zpowers z) ?_) ?_
    · rintro ⟨x, hx⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, rfl⟩
    · intro x y hxy
      exact Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hxy))
  have hcent := GroupTheory.SteinbergBS.centralizer_map_mk'_eq (p := 2) (N := O) hOnd hQ
  rw [MonoidHom.map_zpowers, centralizer_zpowers_eq, centralizer_zpowers_eq] at hcent
  set N' : Subgroup ↥H := N.subgroupOf H with hN'
  set Nb : Subgroup (↥H ⧸ O) := N'.map π with hNb
  have hNbC : Nb ≤ Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)) := by
    rintro _ ⟨n', hn', rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hn : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have hc : (n' : G) * z = z * n' := Subgroup.mem_centralizer_singleton_iff.mp (oddCoreIn_le _ hn)
    have : n' * zH = zH * n' := Subtype.ext hc
    rw [← map_mul, ← map_mul, this]
  have hfwd : ∀ g ∈ Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)), ∀ x ∈ Nb, g * x * g⁻¹ ∈ Nb := by
    intro g hg x hx
    rw [hcent] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨n', hn', rfl⟩ := hx
    have hhC : (h : G) ∈ Subgroup.centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hh))
    have hn : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have h1 : (h : G) * n' * (h : G)⁻¹ ∈ N := conj_mem_oddCoreIn hhC hn
    refine ⟨h * n' * h⁻¹, Subgroup.mem_subgroupOf.mpr h1, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hNbN : Subgroup.centralizer ({π zH} : Set (↥H ⧸ O)) ≤ Subgroup.normalizer (Nb : Set (↥H ⧸ O)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨fun hx => hfwd g hg x hx, fun hx => ?_⟩
    have := hfwd g⁻¹ (Subgroup.inv_mem _ hg) _ hx
    simpa [mul_assoc] using this
  have hN'odd : Odd (Nat.card N') := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv]
    exact odd_card_oddCoreIn _
  have hNbodd : Odd (Nat.card Nb) :=
    Odd.of_dvd_nat hN'odd (CFSG.card_dvd_of_surjective (π.subgroupMap N') (π.subgroupMap_surjective _))
  have hNbO := le_oddCoreIn_of_normalizes hNbC hNbN hNbodd
  rw [h35, le_bot_iff] at hNbO
  intro n hn
  have hn' : (⟨n, hNH hn⟩ : ↥H) ∈ N' := Subgroup.mem_subgroupOf.mpr hn
  have h1 : π ⟨n, hNH hn⟩ ∈ Nb := ⟨_, hn', rfl⟩
  rw [hNbO, Subgroup.mem_bot] at h1
  exact ⟨⟨n, hNH hn⟩, (QuotientGroup.eq_one_iff _).mp h1, rfl⟩

open CFSG.ClassicalInvolution.Asc77 in
theorem oddCoreIn_eq_bot_of_inO2_triple {z u : G} (hz2 : z * z = 1) (hu2 : u * u = 1)
    (hzu : z * u = u * z) (hA : InO2C u z) (hB : InO2C z u) (hA' : InO2C (z * u) z)
    (hB' : InO2C z (z * u))
    (hα : alphaOf (Subgroup.closure ({z, u} : Set G)) = ⊥) :
    oddCoreIn (Subgroup.centralizer ({z} : Set G)) = ⊥ := by
  have hzp := ExactLayer.isPGroup_zpowers_of_sq_eq_one hz2
  have hup := ExactLayer.isPGroup_zpowers_of_sq_eq_one hu2
  have hzuz : z * (z * u) = (z * u) * z := by
    calc z * (z * u) = z * (u * z) := by rw [hzu]
      _ = (z * u) * z := by group
  have h1 := oddCoreIn_le_oddCoreIn_of_inO2 hzp hzu hA hB
  have h2 := oddCoreIn_le_oddCoreIn_of_inO2 hzp hzuz hA' hB'
  rw [← le_bot_iff, ← hα]
  refine le_sup_of_le_right ?_
  refine le_iInf₂ fun a ha => le_iInf fun ha1 => ?_
  have hu2' : u * u = u * u := rfl
  rcases Bootstrap.mem_closure_pair_cases hz2 hu2 hzu ha with rfl | rfl | rfl | rfl
  · exact absurd rfl ha1
  · exact le_rfl
  · exact h1
  · exact h2

end Pair

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
