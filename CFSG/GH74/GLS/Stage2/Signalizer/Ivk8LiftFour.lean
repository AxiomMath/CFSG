module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8LiftCbar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Four
public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87L31Hat

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local
  CFSG.GH74.GLS.Stage2.Signalizer.Odd87

section RLift

theorem exists_rpow_lift {X Y : Type} [Group X] [Group Y] [Finite X] (f : X →* Y) {r : ℕ}
    (hr : r.Prime) {x : Y} (hxr : orderOf x = r) {d : X} (hd : f d = x) :
    ∃ k j : ℕ, (d ^ j) ^ (r ^ k) = 1 ∧ f (d ^ j) = x := by
  have hm0 : orderOf d ≠ 0 := (orderOf_pos d).ne'
  obtain ⟨a, m', hm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm0 r hr.ne_one
  have hcop : Nat.Coprime m' r := ((Nat.Prime.coprime_iff_not_dvd hr).2 hm').symm
  obtain ⟨i, -, hi⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hr.one_lt
  refine ⟨a, m' * i, ?_, ?_⟩
  · calc (d ^ (m' * i)) ^ (r ^ a) = (d ^ (r ^ a * m')) ^ i := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          ring
      _ = 1 := by rw [← hm, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, hd, ← pow_mod_orderOf, hxr, hi, pow_one]

end RLift

section Four

variable {G : Type} [Group G]

theorem pPrimeCoreOf_conj_mem [Finite G] {X : Subgroup G} {g y : G} (hg : g ∈ X)
    (hy : y ∈ pPrimeCoreOf 2 X) : g * y * g⁻¹ ∈ pPrimeCoreOf 2 X := by
  obtain ⟨m, hm, rfl⟩ := hy
  exact ⟨⟨g, hg⟩ * m * ⟨g, hg⟩⁻¹,
    (pPrimeCore_normal (G := ↥X)).conj_mem m hm ⟨g, hg⟩, rfl⟩

theorem odd_card_pPrimeCoreOf [Finite G] (X : Subgroup G) :
    Odd (Nat.card ↥(pPrimeCoreOf 2 X)) := by
  have h : Nat.card ↥(pPrimeCoreOf 2 X) = Nat.card ↥(pPrimeCore 2 ↥X) :=
    Subgroup.card_map_of_injective X.subtype_injective
  rw [h, ← Nat.coprime_two_left]
  exact pPrimeCore_coprime_card

theorem lift_four {H : Subgroup G} (hlift : LiftTwo H) {U : Subgroup (HBar H)}
    (hU : IVK.IsFourSubgroup U) :
    ∃ Ũ : Subgroup G, Ũ ≤ H ∧ IVK.IsFourSubgroup Ũ ∧ barIn H Ũ = U ∧
      ∀ c ∈ centralizer (U : Set (HBar H)),
        ∃ d : ↥H, (∀ u ∈ Ũ, (d : G) * u = u * d) ∧ mkH H d = c := by
  obtain ⟨hUe, hU4⟩ := hU
  have hUsq : ∀ u ∈ U, u * u = 1 := fun u hu => by
    have := elemPow_eq_one_of_isElementaryAbelian (p := 2) (A := U) u hu
    simpa [sq] using this
  have hU2 : IsPGroup 2 ↥U := by
    have := hUe
    exact IsElementaryAbelian.isPGroup 2 ↥U
  obtain ⟨W', hW'2, hW'U, hW'N, hW'C⟩ := hlift U hU2
  have hinj : Function.Injective ((mkH H).comp W'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    have h1 : (y : ↥H) ∈ W' ⊓ pPrimeCore 2 ↥H :=
      ⟨y.2, (QuotientGroup.eq_one_iff _).1 hy⟩
    rw [hW'N, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hmemU : ∀ y : ↥W', mkH H y ∈ U := fun y => hW'U ▸ ⟨y, y.2, rfl⟩
  let φ : ↥W' →* ↥U := ((mkH H).comp W'.subtype).codRestrict U hmemU
  have hφ : Function.Bijective φ := by
    refine ⟨fun a b hab => hinj ?_, ?_⟩
    · exact congrArg Subtype.val hab
    · rintro ⟨u, hu⟩
      rw [← hW'U] at hu
      obtain ⟨y, hy, rfl⟩ := hu
      exact ⟨⟨y, hy⟩, rfl⟩
  have hcard : Nat.card ↥W' = 4 := by
    rw [Nat.card_eq_of_bijective φ hφ, hU4]
  have hsq : ∀ y ∈ W', y * y = 1 := by
    intro y hy
    have h1 : mkH H y * mkH H y = 1 := hUsq _ (hW'U ▸ ⟨y, hy, rfl⟩)
    have h1' : mkH H (y * y) = 1 := by rw [map_mul]; exact h1
    have h2 : y * y ∈ pPrimeCore 2 ↥H := (QuotientGroup.eq_one_iff (y * y)).1 h1'
    have h3 : y * y ∈ W' ⊓ pPrimeCore 2 ↥H := ⟨W'.mul_mem hy hy, h2⟩
    rw [hW'N, Subgroup.mem_bot] at h3
    exact h3
  refine ⟨W'.map H.subtype, Subgroup.map_subtype_le W', ?_, ?_, ?_⟩
  · refine hat_isFourSubgroup_of_card_sq _ ?_ ?_
    · rw [Subgroup.card_map_of_injective H.subtype_injective, hcard]
    · rintro _ ⟨y, hy, rfl⟩
      have := congrArg (fun t : ↥H => (t : G)) (hsq y hy)
      simpa using this
  · have h5 : (W'.map H.subtype).subgroupOf H = W' := by
      ext y
      constructor
      · rintro ⟨w, hw, hwy⟩
        have := Subtype.ext hwy
        subst this
        exact hw
      · intro hy
        exact ⟨y, hy, rfl⟩
    unfold barIn
    rw [h5]
    exact hW'U
  · intro c hc
    rw [hW'C] at hc
    obtain ⟨d, hd, hdc⟩ := hc
    refine ⟨d, ?_, hdc⟩
    rintro _ ⟨y, hy, rfl⟩
    exact (congrArg (fun t : ↥H => (t : G)) ((Subgroup.mem_centralizer_iff.1 hd y hy))).symm

theorem hbar_four [Finite G] {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.ly S)
    {H : Subgroup G} (hlift : LiftTwo H) {U : Subgroup (HBar H)} (hU : IVK.IsFourSubgroup U)
    {r : ℕ} (hr : r.Prime) (h5 : 5 ≤ r) {x : HBar H} (hx : x ∈ centralizer (U : Set (HBar H)))
    (hxr : orderOf x = r) : x ∈ pPrimeCoreOf 2 (centralizer (U : Set (HBar H))) := by
  obtain ⟨Ũ, hŨH, hŨ4, hŨU, hcent⟩ := lift_four hlift hU
  obtain ⟨d, hd, hdx⟩ := hcent x hx
  obtain ⟨k, j, hdr, hfj⟩ := exists_rpow_lift (mkH H) hr hxr hdx
  have hd₁c : ∀ u ∈ Ũ, ((d ^ j : ↥H) : G) * u = u * ((d ^ j : ↥H) : G) := by
    intro u hu
    rw [Subgroup.coe_pow]
    exact ((show Commute (d : G) u from hd u hu).pow_left j).eq
  have hd₁G : ((d ^ j : ↥H) : G) ∈ centralizer (Ũ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (hd₁c u hu).symm
  have hd₁r : ((d ^ j : ↥H) : G) ^ (r ^ k) = 1 := by
    have := congrArg (fun t : ↥H => (t : G)) hdr
    simpa using this
  have hmem := four_cent_pow hctx hŨ4 hr h5 hd₁G hd₁r
  let D : Subgroup G := H ⊓ centralizer (Ũ : Set G)
  let M : Subgroup G := pPrimeCoreOf 2 (centralizer (Ũ : Set G))
  have hMle : M ≤ centralizer (Ũ : Set G) := Subgroup.map_subtype_le _
  have hN₁ : H ⊓ M ≤ pPrimeCoreOf 2 D := by
    refine CFSG.GH74.GLS.Stage1.Thm3.Sec4.le_pPrimeCoreOf' (X := D) (N := H ⊓ M)
      (fun y hy => ⟨hy.1, hMle hy.2⟩) ?_ ?_
    · intro g hg y hy
      exact ⟨H.mul_mem (H.mul_mem hg.1 hy.1) (H.inv_mem hg.1),
        pPrimeCoreOf_conj_mem hg.2 hy.2⟩
    · exact (odd_card_pPrimeCoreOf (centralizer (Ũ : Set G))).of_dvd_nat
        (Subgroup.card_dvd_of_le inf_le_right)
  have hd₁P : ((d ^ j : ↥H) : G) ∈ pPrimeCoreOf 2 D := hN₁ ⟨(d ^ j).2, hmem⟩
  let P₂ : Subgroup G := pPrimeCoreOf 2 D
  have hP₂D : P₂ ≤ D := Subgroup.map_subtype_le _
  have hP₂H : P₂ ≤ H := hP₂D.trans inf_le_left
  have hN₂ : barIn H P₂ ≤ pPrimeCoreOf 2 (centralizer (U : Set (HBar H))) := by
    refine CFSG.GH74.GLS.Stage1.Thm3.Sec4.le_pPrimeCoreOf' (X := centralizer (U : Set (HBar H)))
      (N := barIn H P₂) ?_ ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      rw [← hŨU] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      have hyD : (y : G) ∈ D := hP₂D (Subgroup.mem_subgroupOf.1 hy)
      have hc : (w : G) * (y : G) = (y : G) * (w : G) :=
        (Subgroup.mem_centralizer_iff.1 hyD.2 (w : G) (Subgroup.mem_subgroupOf.1 hw))
      show mkH H w * mkH H y = mkH H y * mkH H w
      rw [← map_mul, ← map_mul]
      exact congrArg (mkH H) (Subtype.ext hc)
    · intro a ha n hn
      obtain ⟨d', hd', rfl⟩ := hcent a ha
      obtain ⟨y, hy, rfl⟩ := hn
      refine ⟨d' * y * d'⁻¹, Subgroup.mem_subgroupOf.2 ?_, by simp⟩
      have hd'D : (d' : G) ∈ D :=
        ⟨d'.2, Subgroup.mem_centralizer_iff.2 (fun u hu => (hd' u hu).symm)⟩
      exact pPrimeCoreOf_conj_mem hd'D (Subgroup.mem_subgroupOf.1 hy)
    · have h1 : Nat.card ↥(barIn H P₂) ∣ Nat.card ↥(P₂.subgroupOf H) :=
        Subgroup.card_map_dvd _ _
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₂H).toEquiv] at h1
      exact (odd_card_pPrimeCoreOf D).of_dvd_nat h1
  rw [← hfj]
  exact hN₂ ⟨d ^ j, Subgroup.mem_subgroupOf.2 hd₁P, rfl⟩

theorem aframe_four_field [Finite G] {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.ly S)
    (H : Subgroup G) :
    ∀ U : Subgroup (HBar H), IVK.IsFourSubgroup U → ∀ r : ℕ, r.Prime → 5 ≤ r →
      ∀ x ∈ centralizer (U : Set (HBar H)), orderOf x = r →
        x ∈ pPrimeCoreOf 2 (centralizer (U : Set (HBar H))) :=
  fun _ hU _ hr h5 _ hx hxr => hbar_four hctx (liftTwo H) hU hr h5 hx hxr

end Four

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
