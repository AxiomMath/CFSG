module

public import CFSG.LocalAnalysis.OddStandard.GH71.CUFacts2
public import CFSG.LocalAnalysis.OddStandard.GH71.CosetFix
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.IVK812LyAux

public section

namespace CFSG.OddStandard.GH71

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer CFSG.GH74.GLS.Stage2.Bender.Thm2 CFSG.OddStandard.Solomon75

variable {G : Type} [Group G] [Finite G]

theorem odd_card_of_isPGroup_three {Q : Subgroup G} (hQ : IsPGroup 3 ↥Q) : Odd (Nat.card Q) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

omit [Finite G] in
theorem mem_commutator_barIn {S H : Subgroup G} (hSH : S ≤ H) {a : G} (ha : a ∈ ⁅S, S⁆)
    (haH : a ∈ H) :
    QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨a, haH⟩ ∈ ⁅barIn H S, barIn H S⁆ := by
  have e : (⁅S.subgroupOf H, S.subgroupOf H⁆).map H.subtype = ⁅S, S⁆ := by
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, inf_of_le_left hSH]
  rw [← e] at ha
  obtain ⟨b, hb, hbe⟩ := ha
  have hb' : b = ⟨a, haH⟩ := Subtype.ext hbe
  rw [← hb']
  unfold barIn
  rw [← Subgroup.map_commutator]
  exact ⟨b, hb, rfl⟩

theorem exists_gen_of_card_three {X : Type*} [Group X] [Finite X] {P : Subgroup X}
    (hP : Nat.card P = 3) : ∃ x ∈ P, orderOf x = 3 ∧ zpowers x = P := by
  have hne : P ≠ ⊥ := fun hb => by rw [hb, Subgroup.card_bot] at hP; omega
  obtain ⟨⟨x, hx⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hx1' : x ≠ 1 := fun e => hx1 (Subtype.ext e)
  have hdvd : orderOf x ∣ 3 := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : P)
    rwa [Subgroup.orderOf_mk, hP] at this
  have hord : orderOf x = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with e | e
    · exact absurd (orderOf_eq_one_iff.mp e) hx1'
    · exact e
  exact ⟨x, hx, hord, eq_of_le_of_card_ge (zpowers_le.mpr hx) (by rw [hP, Nat.card_zpowers, hord])⟩

variable {z : G} {S U : Subgroup G} {u : G}

namespace Ctx71

theorem card_barIn_of_ivk (h812 : IVK_8_12_ly) (h : Ctx71 G z S U u) {H P : Subgroup G}
    (hH : H ≠ ⊤) (hSH : S ≤ H) (hP : MaxSInv 3 S H P) (hPO : ¬ P ≤ pPrimeCoreOf 2 H) :
    Nat.card (barIn H P) = 3 := by
  rw [← IVK812.relIndex_eq_card_barIn hP.1]
  exact (h812 G z S h.ctx H hH hSH P hP hPO).2.2

theorem exists_gen_bar (h : Ctx71 G z S U u) (hB0 : SpecB0) {H P : Subgroup G} (hSH : S ≤ H)
    (hSP : S ≤ normalizer (P : Set G)) (hcard : Nat.card (barIn H P) = 3) :
    ∃ x ∈ barIn H P, orderOf x = 3 ∧ zpowers x = barIn H P ∧
      barIn H S ≤ normalizer ((zpowers x : Subgroup (HBar H)) : Set (HBar H)) ∧
      ∀ a ∈ U, ∀ haH : a ∈ H,
        QuotientGroup.mk' (pPrimeCore 2 ↥H) ⟨a, haH⟩ ∈ centralizer ({x} : Set (HBar H)) := by
  obtain ⟨x, hx, hx3, hxP⟩ := exists_gen_of_card_three hcard
  have hSx : barIn H S ≤ normalizer ((zpowers x : Subgroup (HBar H)) : Set (HBar H)) := by
    rw [hxP]; exact IVK812.barIn_le_normalizer hSP
  refine ⟨x, hx, hx3, hxP, hSx, fun a ha haH => ?_⟩
  exact IVK812.commutator_le_centralizer_of_le_normalizer_zpowers hx3 hSx
    (mem_commutator_barIn hSH (h.U_le_commutator hB0 ha) haH)

theorem not_inf_centralizer_U_le (h : Ctx71 G z S U u) (hB0 : SpecB0) {H P : Subgroup G}
    (hSH : S ≤ H) (hPH : P ≤ H) (hSP : S ≤ normalizer (P : Set G))
    (hcard : Nat.card (barIn H P) = 3) : ¬ P ⊓ centralizer (U : Set G) ≤ pPrimeCoreOf 2 H := by
  intro hle
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥H) with hπ
  obtain ⟨x, -, -, hxP, -, hUx⟩ := h.exists_gen_bar hB0 hSH hSP hcard
  set N₀ := P ⊓ pPrimeCoreOf 2 H with hN₀
  have hUH : U ≤ H := h.U_le.trans hSH
  have hU2 : IsPGroup 2 ↥U := h.S2.to_le h.U_le
  have hN₀odd : Odd (Nat.card N₀) := odd_card_of_le inf_le_right (odd_card_pPrimeCoreOf' H)
  have hUN : U ≤ normalizer (N₀ : Set G) := fun a ha =>
    inf_normalizer_le_normalizer_inf
      ⟨hSP (h.U_le ha), le_normalizer_pPrimeCoreOf' H (hUH ha)⟩
  have htriv : ∀ a ∈ U, ∀ k ∈ P, k⁻¹ * (a * k * a⁻¹) ∈ N₀ := by
    intro a ha k hk
    refine ⟨P.mul_mem (P.inv_mem hk) ((mem_normalizer_iff.mp (hSP (h.U_le ha)) k).mp hk), ?_⟩
    have hkH := hPH hk
    have haH := hUH ha
    have hkx : π ⟨k, hkH⟩ ∈ zpowers x := hxP ▸ ⟨⟨k, hkH⟩, hk, rfl⟩
    obtain ⟨n, hn⟩ := mem_zpowers_iff.mp hkx
    have hax : Commute (π ⟨a, haH⟩) x := mem_centralizer_singleton_iff.mp (hUx a ha haH)
    have hc : π ⟨a, haH⟩ * π ⟨k, hkH⟩ = π ⟨k, hkH⟩ * π ⟨a, haH⟩ := by
      rw [← hn]; exact hax.zpow_right n
    have hmem : (⟨k, hkH⟩ : ↥H)⁻¹ * (⟨a, haH⟩ * ⟨k, hkH⟩ * ⟨a, haH⟩⁻¹) ∈ pPrimeCore 2 ↥H := by
      rw [← QuotientGroup.eq_one_iff]
      show π _ = 1
      simp only [map_mul, map_inv]
      rw [hc]
      group
    exact ⟨_, hmem, rfl⟩
  have hne : barIn H P ≠ ⊥ := fun hb => by rw [hb, Subgroup.card_bot] at hcard; omega
  have hPO : ¬ P ≤ pPrimeCoreOf 2 H := fun hPO => hne ((IVK812.barIn_eq_bot_iff hPH).mpr hPO)
  obtain ⟨k, hk, hkO⟩ := IsConcreteLE.not_le_iff_exists.mp hPO
  obtain ⟨n, hn, hkn⟩ := exists_centralized_in_coset hU2 hN₀odd hUN htriv hk
  apply hkO
  have h1 : k * n ∈ pPrimeCoreOf 2 H := hle ⟨P.mul_mem hk hn.1, hkn⟩
  have e : k = k * n * n⁻¹ := by group
  rw [e]
  exact (pPrimeCoreOf 2 H).mul_mem h1 ((pPrimeCoreOf 2 H).inv_mem hn.2)

end Ctx71

end CFSG.OddStandard.GH71
