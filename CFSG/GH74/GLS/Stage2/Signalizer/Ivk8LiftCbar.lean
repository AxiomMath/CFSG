module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8Cbar
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8LiftGen

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local

abbrev mkH {G : Type} [Group G] (H : Subgroup G) : ↥H →* HBar H :=
  QuotientGroup.mk' (pPrimeCore 2 ↥H)

@[expose] def LiftTwo {G : Type} [Group G] (H : Subgroup G) : Prop :=
  ∀ W : Subgroup (HBar H), IsPGroup 2 ↥W → ∃ W' : Subgroup ↥H, IsPGroup 2 ↥W' ∧
    W'.map (mkH H) = W ∧ W' ⊓ pPrimeCore 2 ↥H = ⊥ ∧
    centralizer (W : Set (HBar H)) = (centralizer (W' : Set ↥H)).map (mkH H)

theorem quotPCore_equiv_of_surjective_odd {X Y : Type} [Group X] [Group Y] [Finite X] [Finite Y]
    (f : X →* Y) (hf : Function.Surjective f) (hker : ¬ 2 ∣ Nat.card f.ker) :
    Nonempty ((X ⧸ pPrimeCore 2 X) ≃* (Y ⧸ pPrimeCore 2 Y)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcomap, -⟩ := CFSG.prime_complement_kernel_core_preimage (p := 2) f hf hker
  let h : X →* (Y ⧸ pPrimeCore 2 Y) := (QuotientGroup.mk' _).comp f
  have hh : Function.Surjective h := (QuotientGroup.mk'_surjective _).comp hf
  have hhk : h.ker = pPrimeCore 2 X := by
    rw [← hcomap]
    ext x
    simp [h, QuotientGroup.eq_one_iff]
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hhk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective h hh)⟩

section Lift

variable {G : Type} [Group G] [Finite G]

theorem lift_quot {H X : Subgroup G} (hXH : X ≤ H) {R : Subgroup (HBar H)} (hR : barIn H X = R) :
    Nonempty ((↥X ⧸ pPrimeCore 2 ↥X) ≃* (↥R ⧸ pPrimeCore 2 ↥R)) := by
  subst hR
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let g : ↥X →* HBar H := (mkH H).comp (Subgroup.inclusion hXH)
  have hrange : ∀ x : ↥X, g x ∈ barIn H X := fun x =>
    ⟨⟨x, hXH x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  let f : ↥X →* ↥(barIn H X) := g.codRestrict (barIn H X) hrange
  have hf : Function.Surjective f := by
    rintro ⟨_, ⟨y, hy, rfl⟩⟩
    exact ⟨⟨(y : G), Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext rfl⟩
  have hker : ¬ 2 ∣ Nat.card f.ker := by
    have hle : f.ker ≤ (pPrimeCore 2 ↥H).comap (Subgroup.inclusion hXH) := by
      intro x hx
      have h1 : mkH H (Subgroup.inclusion hXH x) = 1 :=
        congrArg Subtype.val ((MonoidHom.mem_ker).1 hx)
      exact (QuotientGroup.eq_one_iff (Subgroup.inclusion hXH x)).1 h1
    have h2 := Subgroup.card_dvd_of_le hle
    have h3 := Subgroup.card_comap_dvd_of_injective (pPrimeCore 2 ↥H) (Subgroup.inclusion hXH)
      (Subgroup.inclusion_injective hXH)
    intro h
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).1 pPrimeCore_coprime_card
      (h.trans (h2.trans h3))
  exact quotPCore_equiv_of_surjective_odd f hf hker

theorem hbar_cbar {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.ly S) {H : Subgroup G}
    {t' : G} (ht'2 : orderOf t' = 2) {R : Subgroup (HBar H)}
    (hcent : ∀ c ∈ R, ∃ d : ↥H, (d : G) * t' = t' * (d : G) ∧ mkH H d = c) :
    ∃ (n : ℕ) (K : Type) (_ : Group K) (R' : Subgroup K), (n = 10 ∨ n = 11) ∧
      IsDoubleCoverOfAlt K n ∧
      Nonempty ((↥R ⧸ pPrimeCore 2 ↥R) ≃* (↥R' ⧸ pPrimeCore 2 ↥R')) := by
  let R₀ : Subgroup ↥H := (centralizer ({t'} : Set G)).comap H.subtype ⊓ R.comap (mkH H)
  let Rt : Subgroup G := R₀.map H.subtype
  have hRtH : Rt ≤ H := Subgroup.map_subtype_le R₀
  have hRtc : Rt ≤ centralizer ({t'} : Set G) := by
    rintro _ ⟨d, hd, rfl⟩
    exact hd.1
  have hbar : barIn H Rt = R := by
    ext c
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨d, hd, hdy⟩ := (Subgroup.mem_subgroupOf.1 hy)
      have : y = d := Subtype.ext hdy.symm
      rw [this]
      exact hd.2
    · intro hc
      obtain ⟨d, hd, hdc⟩ := hcent c hc
      refine ⟨d, Subgroup.mem_subgroupOf.2 ⟨d, ⟨?_, ?_⟩, rfl⟩, hdc⟩
      · exact Subgroup.mem_centralizer_singleton_iff.2 hd
      · show mkH H d ∈ R
        rw [hdc]
        exact hc
  obtain ⟨e1⟩ := lift_quot hRtH hbar
  obtain ⟨n, K, _, R', hn, hK, ⟨e2⟩⟩ := cbar_G hctx t' ht'2 Rt hRtc
  exact ⟨n, K, inferInstance, R', hn, hK, ⟨e1.symm.trans e2⟩⟩

theorem hbar_cbar_field {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.ly S) {H : Subgroup G}
    (hlift : LiftTwo H) :
    ∀ t : HBar H, orderOf t = 2 → ∀ R : Subgroup (HBar H), R ≤ centralizer ({t} : Set (HBar H)) →
      ∃ (n : ℕ) (K : Type) (_ : Group K) (R' : Subgroup K), (n = 10 ∨ n = 11) ∧
        IsDoubleCoverOfAlt K n ∧
        Nonempty ((↥R ⧸ pPrimeCore 2 ↥R) ≃* (↥R' ⧸ pPrimeCore 2 ↥R')) := by
  intro t ht R hR
  have hW2 : IsPGroup 2 ↥(zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨W', -, hW'U, hW'N, hW'C⟩ := hlift (zpowers t) hW2
  obtain ⟨y, hy, hyt⟩ : ∃ y ∈ W', mkH H y = t := by
    have : t ∈ W'.map (mkH H) := hW'U ▸ mem_zpowers t
    obtain ⟨y, hy, hyt⟩ := this
    exact ⟨y, hy, hyt⟩
  have hy2 : y ^ 2 = 1 := by
    have ht2 : t ^ 2 = 1 := by
      have := pow_orderOf_eq_one t
      rwa [ht] at this
    have h1 : mkH H (y ^ 2) = 1 := by rw [map_pow, hyt, ht2]
    have h2 : y ^ 2 ∈ W' ⊓ pPrimeCore 2 ↥H :=
      ⟨W'.pow_mem hy 2, (QuotientGroup.eq_one_iff (y ^ 2)).1 h1⟩
    rw [hW'N, Subgroup.mem_bot] at h2
    exact h2
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [map_one] at hyt
    rw [← hyt, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have hyord : orderOf y = 2 := orderOf_eq_prime hy2 hy1
  have hcent : ∀ c ∈ R, ∃ d : ↥H, (d : G) * (y : G) = (y : G) * (d : G) ∧ mkH H d = c := by
    intro c hc
    have hct : c ∈ centralizer (zpowers t : Set (HBar H)) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨m, rfl⟩
      have h : Commute t c := (Subgroup.mem_centralizer_singleton_iff.1 (hR hc)).symm
      exact (h.zpow_left m).eq
    rw [hW'C] at hct
    obtain ⟨d, hd, hdc⟩ := hct
    refine ⟨d, ?_, hdc⟩
    exact (congrArg (fun t : ↥H => (t : G)) (Subgroup.mem_centralizer_iff.1 hd y hy)).symm
  exact hbar_cbar hctx ((Subgroup.orderOf_coe y).trans hyord) hcent

theorem liftTwo (H : Subgroup G) : LiftTwo H :=
  fun W hW => exists_lift_two_centralizer_bar H W hW

theorem aframe_cbar_field {z : G} {S : Subgroup G} (hctx : Stage2Ctx G z Kind.ly S)
    (H : Subgroup G) :
    ∀ t : HBar H, orderOf t = 2 → ∀ R : Subgroup (HBar H), R ≤ centralizer ({t} : Set (HBar H)) →
      ∃ (n : ℕ) (K : Type) (_ : Group K) (R' : Subgroup K), (n = 10 ∨ n = 11) ∧
        IsDoubleCoverOfAlt K n ∧
        Nonempty ((↥R ⧸ pPrimeCore 2 ↥R) ≃* (↥R' ⧸ pPrimeCore 2 ↥R')) :=
  hbar_cbar_field hctx (liftTwo H)

end Lift

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
