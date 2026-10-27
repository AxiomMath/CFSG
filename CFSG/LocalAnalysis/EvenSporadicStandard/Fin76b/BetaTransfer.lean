module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma65R1
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Sylow3

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open

theorem BetaFor.inv {X : Type*} [Group X] {β : X} (h : BetaFor X β) : BetaFor X β⁻¹ := by
  have hc : centralizer ({β⁻¹} : Set X) = centralizer ({β} : Set X) := by
    ext g
    simp only [mem_centralizer_singleton_iff]
    constructor
    · intro hg
      exact ((Commute.inv_right_iff).1 (show Commute g β⁻¹ from hg)).eq
    · intro hg
      exact (Commute.inv_right (show Commute g β from hg)).eq
  have key : ∀ A B : Subgroup X, A = B →
      Nonempty (↥A ⧸ fusionOddCore ↥A ≃* alternatingGroup (Fin 6)) →
      Nonempty (↥B ⧸ fusionOddCore ↥B ≃* alternatingGroup (Fin 6)) := by
    rintro A B rfl hA
    exact hA
  obtain ⟨h3, hD, hO⟩ := h
  refine ⟨by rw [orderOf_inv]; exact h3, key _ _ hc.symm hD, ?_⟩
  rw [hc, zpowers_inv]
  exact hO

theorem betaFor_of_order_three {X : Type*} [Group X] [Finite X] {t β₀ β : X}
    (hcard : Nat.card ↥(centralizer ({t} : Set X)) = 1920) (hβ₀t : β₀ * t = t * β₀)
    (hβ₀ : BetaFor X β₀) (hβt : β * t = t * β) (hβ3 : orderOf β = 3) : BetaFor X β := by
  obtain ⟨w, -, hw | hw⟩ := exists_conj_of_order_three (W := centralizer ({t} : Set X)) hcard
    (mem_centralizer_singleton_iff.2 hβ₀t) (mem_centralizer_singleton_iff.2 hβt) hβ₀.1 hβ3
  · have := hβ₀.conj w
    rwa [hw] at this
  · have := (hβ₀.conj w).inv
    rwa [hw, inv_inv] at this

theorem mem_commutator_of_a6 {C : Type*} [Group C] [Finite C]
    (hA6 : Nonempty (C ⧸ fusionOddCore C ≃* alternatingGroup (Fin 6))) {x : C} {k : ℕ}
    (hx : x ^ (2 ^ k) = 1) : x ∈ _root_.commutator C := by
  obtain ⟨e⟩ := hA6
  let π : C →* alternatingGroup (Fin 6) := e.toMonoidHom.comp (QuotientGroup.mk' (fusionOddCore C))
  have hπ : Function.Surjective π :=
    e.surjective.comp (QuotientGroup.mk'_surjective (fusionOddCore C))
  have hker : ∀ y, π y = 1 ↔ y ∈ fusionOddCore C := by
    intro y
    simp only [π, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [e.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hperf : derivedSeries (alternatingGroup (Fin 6)) 1 = ⊤ := by
    rw [derivedSeries_one]
    exact commutator_alternatingGroup_eq_top (by simp)
  have h2 := map_derivedSeries_eq hπ 1
  rw [hperf] at h2
  have hxm : π x ∈ (derivedSeries C 1).map π := by rw [h2]; trivial
  obtain ⟨c, hc, hcx⟩ := hxm
  rw [derivedSeries_one] at hc
  have hn : c⁻¹ * x ∈ fusionOddCore C := by
    rw [← hker, map_mul, map_inv, hcx, inv_mul_cancel]
  let p := QuotientGroup.mk' (_root_.commutator C)
  have hpc : p c = 1 := (QuotientGroup.eq_one_iff c).2 hc
  have hpx : p x = p (c⁻¹ * x) := by
    rw [map_mul, map_inv, hpc, inv_one, one_mul]
  have hd1 : orderOf (p x) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hx, map_one])
  have hd2 : orderOf (p x) ∣ Nat.card (fusionOddCore C) := by
    rw [hpx]
    exact (orderOf_map_dvd p _).trans (Subgroup.orderOf_dvd_natCard _ hn)
  have hcop : Nat.gcd (2 ^ k) (Nat.card (fusionOddCore C)) = 1 :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.2 (odd_natCard_fusionOddCore C))
  have hone : orderOf (p x) = 1 := Nat.dvd_one.1 (hcop ▸ Nat.dvd_gcd hd1 hd2)
  exact (QuotientGroup.eq_one_iff x).1 (orderOf_eq_one_iff.1 hone)

theorem subgroupOf_le_commutator_of_a6 {G : Type*} [Group G] [Finite G] {K C D : Subgroup G}
    (hCK : C ≤ K) (hDC : D ≤ C) (hD2 : IsPGroup 2 D)
    (hA6 : Nonempty (↥C ⧸ fusionOddCore ↥C ≃* alternatingGroup (Fin 6))) :
    D.subgroupOf K ≤ _root_.commutator ↥K := by
  intro d hd
  have hdD : (d : G) ∈ D := mem_subgroupOf.1 hd
  obtain ⟨k, hk⟩ := hD2 ⟨(d : G), hdD⟩
  have hk' : (⟨(d : G), hDC hdD⟩ : C) ^ (2 ^ k) = 1 := by
    apply Subtype.ext
    have := congrArg Subtype.val hk
    simpa using this
  have hc := mem_commutator_of_a6 hA6 hk'
  have h1 := map_derivedSeries_le_derivedSeries (Subgroup.inclusion hCK) 1
  rw [derivedSeries_one, derivedSeries_one] at h1
  exact h1 ⟨_, hc, rfl⟩

theorem map_conj_inf_centralizer {G : Type*} [Group G] {L : Subgroup G} {t : G} {E : Subgroup G}
    (hW : WFacts L t E) {w : G} (hwL : w ∈ L) (hwt : w * t = t * w) (β₁ : G) :
    (E ⊓ centralizer ({β₁} : Set G)).map (MulAut.conj w).toMonoidHom =
      E ⊓ centralizer ({w * β₁ * w⁻¹} : Set G) := by
  ext g
  constructor
  · rintro ⟨d, ⟨hdE, hd⟩, rfl⟩
    refine ⟨hW.normal w hwL hwt d hdE, mem_centralizer_singleton_iff.2 ?_⟩
    have hd' := mem_centralizer_singleton_iff.1 hd
    show w * d * w⁻¹ * (w * β₁ * w⁻¹) = w * β₁ * w⁻¹ * (w * d * w⁻¹)
    calc w * d * w⁻¹ * (w * β₁ * w⁻¹) = w * (d * β₁) * w⁻¹ := by group
      _ = w * (β₁ * d) * w⁻¹ := by rw [hd']
      _ = w * β₁ * w⁻¹ * (w * d * w⁻¹) := by group
  · rintro ⟨hgE, hg⟩
    have hwt' : w⁻¹ * t = t * w⁻¹ := by
      calc w⁻¹ * t = w⁻¹ * (t * w) * w⁻¹ := by group
        _ = w⁻¹ * (w * t) * w⁻¹ := by rw [hwt]
        _ = t * w⁻¹ := by group
    have hdE : w⁻¹ * g * w ∈ E := by
      have := hW.normal w⁻¹ (L.inv_mem hwL) hwt' g hgE
      simpa using this
    refine ⟨w⁻¹ * g * w, ⟨hdE, mem_centralizer_singleton_iff.2 ?_⟩, ?_⟩
    · have hg' := mem_centralizer_singleton_iff.1 hg
      calc w⁻¹ * g * w * β₁ = w⁻¹ * (g * (w * β₁ * w⁻¹)) * w := by group
        _ = w⁻¹ * ((w * β₁ * w⁻¹) * g) * w := by rw [hg']
        _ = β₁ * (w⁻¹ * g * w) := by group
    · show w * (w⁻¹ * g * w) * w⁻¹ = g
      group

theorem card_inf_centralizer_eq_eight {G : Type*} [Group G] [Finite G] {L : Subgroup G} {t : G}
    {E : Subgroup G} (hW : WFacts L t E) {β : G} (hβL : β ∈ L) (hβt : β * t = t * β)
    (hβ3 : orderOf β = 3) : Nat.card ↥(E ⊓ centralizer ({β} : Set G)) = 8 := by
  obtain ⟨β₁, hβ₁L, hβ₁t, hβ₁3, hcard, -⟩ := hW.beta
  have hmem : ∀ y ∈ L, y * t = t * y → y ∈ L ⊓ centralizer ({t} : Set G) := fun y hy hyt =>
    ⟨hy, mem_centralizer_singleton_iff.2 hyt⟩
  obtain ⟨w, hwW, hw⟩ := exists_conj_of_order_three (W := L ⊓ centralizer ({t} : Set G))
    hW.card_cent (hmem β₁ hβ₁L hβ₁t) (hmem β hβL hβt) hβ₁3 hβ3
  have hwL : w ∈ L := hwW.1
  have hwt : w * t = t * w := mem_centralizer_singleton_iff.1 hwW.2
  have hc : centralizer ({w * β₁ * w⁻¹} : Set G) = centralizer ({β} : Set G) := by
    rcases hw with hw | hw
    · rw [hw]
    · rw [hw]
      ext g
      simp only [mem_centralizer_singleton_iff]
      constructor
      · intro hg
        exact ((Commute.inv_right_iff).1 (show Commute g β⁻¹ from hg)).eq
      · intro hg
        exact (Commute.inv_right (show Commute g β from hg)).eq
  have himg := map_conj_inf_centralizer hW hwL hwt β₁
  rw [hc] at himg
  rw [← himg, Subgroup.card_map_of_injective (MulAut.conj w).injective]
  exact hcard

theorem betaData65_of_wFacts {G : Type*} [Group G] [Finite G] {L : Subgroup G} {t : G}
    {E : Subgroup G} (hW : WFacts L t E) (hE2 : IsPGroup 2 E) {β : G} (hβL : β ∈ L)
    (hβt : β * t = t * β) (hβ3 : orderOf β = 3)
    (hA6 : Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6))) :
    BetaData65 E β :=
  ⟨card_inf_centralizer_eq_eight hW hβL hβt hβ3,
    subgroupOf_le_commutator_of_a6 (K := centralizer ({β} : Set G))
      (C := L ⊓ centralizer ({β} : Set G)) (D := E ⊓ centralizer ({β} : Set G)) inf_le_right
      (inf_le_inf_right _ hW.E_le) (hE2.to_le inf_le_left) hA6⟩

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ : Subgroup G}

theorem a6_quotient_of_model (h : InnerConfig G L z t T₀) {X : Type*} [Group X] [Finite X]
    (φ : X ≃* L) (hB : BetaDataSq X) (hR : RootFactsClass X) {β : G} (hβL : β ∈ L)
    (hβt : β * t = t * β) (hβ3 : orderOf β = 3) :
    Nonempty (↥(L ⊓ centralizer ({β} : Set G)) ⧸
      fusionOddCore ↥(L ⊓ centralizer ({β} : Set G)) ≃* alternatingGroup (Fin 6)) := by
  let tL : ↥L := ⟨t, h.t_mem_A⟩
  have htL2 : orderOf tL = 2 := by rw [← Subgroup.orderOf_coe]; exact h.t_order
  obtain ⟨g, hgA, hg⟩ := h.t_square
  have hsq : ∃ g' : X, g' * g' = φ.symm tL :=
    ⟨φ.symm ⟨g, hgA⟩, by rw [← map_mul]; congr 1; exact Subtype.ext hg⟩
  have ht2 : orderOf (φ.symm tL) = 2 := by rw [MulEquiv.orderOf_eq]; exact htL2
  obtain ⟨β₀, hcomm, hβ₀⟩ := hB (φ.symm tL) ht2 hsq
  let βL : ↥L := ⟨β, hβL⟩
  have hβ'3 : orderOf (φ.symm βL) = 3 := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
    exact hβ3
  have hβ't : φ.symm βL * φ.symm tL = φ.symm tL * φ.symm βL := by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hβt
  have hF : BetaFor X (φ.symm βL) :=
    betaFor_of_order_three (hR _ ht2 hsq).card_cent hcomm.symm hβ₀ hβ't hβ'3
  obtain ⟨-, hD, -⟩ := hF.transport φ
  have hβeq : ((φ (φ.symm βL) : L) : G) = β := by simp [βL]
  have key : ∀ x y : G, x = y →
      Nonempty (↥(L ⊓ centralizer ({x} : Set G)) ⧸
        fusionOddCore ↥(L ⊓ centralizer ({x} : Set G)) ≃* alternatingGroup (Fin 6)) →
      Nonempty (↥(L ⊓ centralizer ({y} : Set G)) ⧸
        fusionOddCore ↥(L ⊓ centralizer ({y} : Set G)) ≃* alternatingGroup (Fin 6)) := by
    rintro x y rfl hx
    exact hx
  exact key _ _ hβeq hD

end CFSG.EvenSporadicStandard.Fin76b
