module

public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreInvol
public import CFSG.LocalAnalysis.OddStandard.Solomon75CoreShape

public section

namespace CFSG.OddStandard.Solomon75

open Subgroup CFSG CFSG.GH74.GLS

namespace CoreAux

section Equivariance

variable {G G' : Type} [Group G] [Group G']

theorem oddCoreOf_map_equiv (f : G ≃* G') (H : Subgroup G) :
    oddCoreOf (H.map f.toMonoidHom) = (oddCoreOf H).map f.toMonoidHom := by
  have h : pPrimeCore 2 ↥(H.map f.toMonoidHom) =
      (pPrimeCore 2 ↥H).map
        (Subgroup.equivMapOfInjective H f.toMonoidHom f.injective).toMonoidHom :=
    (pPrimeCore_map_iso 2 (Subgroup.equivMapOfInjective H f.toMonoidHom f.injective)).symm
  have hcomp : (H.map f.toMonoidHom).subtype.comp
      (Subgroup.equivMapOfInjective H f.toMonoidHom f.injective).toMonoidHom =
      f.toMonoidHom.comp H.subtype := MonoidHom.ext fun x => rfl
  unfold oddCoreOf
  rw [h, Subgroup.map_map, Subgroup.map_map, hcomp]

theorem balance_conj {x y : G} (h : G)
    (hxy : oddCoreOf (cen x) ⊓ cen y ≤ oddCoreOf (cen y)) :
    oddCoreOf (cen (h * x * h⁻¹)) ⊓ cen (h * y * h⁻¹) ≤ oddCoreOf (cen (h * y * h⁻¹)) := by
  rw [cen_conj, cen_conj, oddCoreOf_map_equiv (MulAut.conj h) (cen x),
    oddCoreOf_map_equiv (MulAut.conj h) (cen y),
    ← Subgroup.map_inf_eq _ _ _ (MulAut.conj h).injective]
  exact Subgroup.map_mono hxy

end Equivariance

section OddCore

theorem eq_one_of_mem_pPrimeCore_of_two_pow {C : Type} [Group C] [Finite C] {x : C}
    (hx : x ∈ pPrimeCore 2 C) (h2 : ∃ m : ℕ, orderOf x = 2 ^ m) : x = 1 := by
  obtain ⟨m, hm⟩ := h2
  have h1 : orderOf x ∣ Nat.card (pPrimeCore 2 C) := by
    have := orderOf_dvd_natCard (⟨x, hx⟩ : pPrimeCore 2 C)
    rwa [Subgroup.orderOf_mk] at this
  have hodd := odd_card_pPrimeCore C
  rw [hm] at h1
  have hm0 : m = 0 := by
    by_contra hm0
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 ((dvd_pow_self 2 hm0).trans h1))
  rw [hm0, pow_zero, orderOf_eq_one_iff] at hm
  exact hm

end OddCore

end CoreAux

open CoreAux

section Core

variable {G : Type} [Group G] [Finite G]

theorem balance_core {t z : G} (adm : ℕ → Prop) (hadm : ∀ a b : ℕ, a ∣ b → adm b → adm a)
    {k : ℕ} (R : Subgroup G) (hRz : R ≤ cen z) (hRt : R ≤ cen t) (hR : Nat.card R = 2 ^ k)
    (hno : ∀ X : Subgroup (CentQuot z), IsPGroup 2 X → Nat.card X = 2 ^ k →
      ∀ P : Subgroup (CentQuot z), adm (Nat.card P) → X ≤ normalizer (P : Set (CentQuot z)) →
        P = ⊥)
    (hO : adm (Nat.card (oddCoreOf (cen t)))) :
    oddCoreOf (cen t) ⊓ cen z ≤ oddCoreOf (cen z) := by
  set N : Subgroup ↥(cen z) := pPrimeCore 2 ↥(cen z) with hN
  set π : ↥(cen z) →* CentQuot z := QuotientGroup.mk' N with hπ
  set D : Subgroup G := oddCoreOf (cen t) ⊓ cen z with hD
  set RC : Subgroup ↥(cen z) := R.subgroupOf (cen z) with hRC
  set DC : Subgroup ↥(cen z) := D.subgroupOf (cen z) with hDC
  have hRCcard : Nat.card RC = 2 ^ k := by
    rw [← hR]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRz).toEquiv
  have hRC2 : IsPGroup 2 RC := IsPGroup.of_card hRCcard
  have hinj : Function.Injective (π.comp RC.subtype) := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : ((a : RC) : ↥(cen z)) ∈ N := (QuotientGroup.eq_one_iff _).1 ha
    obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.1 hRC2) a
    have h1 : orderOf ((a : RC) : ↥(cen z)) = 2 ^ m := by rw [Subgroup.orderOf_coe]; exact hm
    have := eq_one_of_mem_pPrimeCore_of_two_pow hmem ⟨m, h1⟩
    exact Subtype.ext this
  set X : Subgroup (CentQuot z) := RC.map π with hX
  have hXcard : Nat.card X = 2 ^ k := by
    rw [← hRCcard]
    refine (Nat.card_congr (Equiv.ofBijective
      (fun x : RC => (⟨π x, Subgroup.mem_map_of_mem π x.2⟩ : X)) ⟨?_, ?_⟩)).symm
    · intro a b hab
      exact hinj (congrArg Subtype.val hab)
    · rintro ⟨_, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hXp : IsPGroup 2 X := IsPGroup.of_card hXcard
  set Pq : Subgroup (CentQuot z) := DC.map π with hPq
  have hDcard : Nat.card DC = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : D ≤ cen z)).toEquiv
  have hadmP : adm (Nat.card Pq) :=
    hadm _ _ ((Subgroup.card_map_dvd DC π).trans
      (hDcard ▸ Subgroup.card_dvd_of_le (inf_le_left : D ≤ oddCoreOf (cen t)))) hO
  have hnorm : X ≤ normalizer (Pq : Set (CentQuot z)) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨r, hr, rfl⟩ _ ⟨d, hd, rfl⟩
    have hrR : (r : G) ∈ R := hr
    have hdD : (d : G) ∈ D := hd
    have hr' : (r : G) ∈ normalizer (D : Set G) :=
      mem_normalizer_inf (le_normalizer_oddCoreOf (cen t) (hRt hrR))
        (Subgroup.le_normalizer (hRz hrR))
    have hconj : (r : G) * (d : G) * (r : G)⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hr' _).mp hdD
    refine ⟨r * d * r⁻¹, ?_, by simp [hπ]⟩
    exact hconj
  have hbot := hno X hXp hXcard Pq hadmP hnorm
  intro d hd
  have hdc : d ∈ cen z := hd.2
  have hmem : (⟨d, hdc⟩ : ↥(cen z)) ∈ DC := hd
  have h1 : π ⟨d, hdc⟩ ∈ Pq := Subgroup.mem_map_of_mem π hmem
  rw [hbot, Subgroup.mem_bot] at h1
  have h2 : (⟨d, hdc⟩ : ↥(cen z)) ∈ N := (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨⟨d, hdc⟩, h2, rfl⟩

end Core

section Balanced

variable {G : Type} [Group G] [Finite G] [IsSimpleGroup G]

theorem isDoubleCoverOfAlt_centQuot_of_involution (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) {n : ℕ} (hn : 8 ≤ n) (hcov : IsDoubleCoverOfAlt (CentQuot t) n)
    (hB : AlternatingBalanceData n) {u : G} (hu : orderOf u = 2) :
    IsDoubleCoverOfAlt (CentQuot u) n := by
  obtain ⟨g, rfl⟩ := exists_conj_of_involution hnonab ht hn hcov hB u hu
  exact isDoubleCoverOfAlt_centQuot_conj g hcov

theorem balanced_of_adm {n : ℕ} (hn : 8 ≤ n) (hD : CoverSylowData n)
    (hB : AlternatingBalanceData n) (adm : ℕ → Prop) (hadm : ∀ a b : ℕ, a ∣ b → adm b → adm a)
    (hno : ∀ (K : Type) [Group K] [Finite K], IsDoubleCoverOfAlt K n →
      ∀ X : Subgroup K, IsPGroup 2 X → Nat.card X = 2 ^ (if n ≤ 9 then 6 else 7) →
        ∀ P : Subgroup K, adm (Nat.card P) → X ≤ normalizer (P : Set K) → P = ⊥)
    (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G} (ht : orderOf t = 2)
    (hcov : IsDoubleCoverOfAlt (CentQuot t) n) (hO : adm (Nat.card (oddCoreOf (cen t)))) :
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x * y = y * x → x ≠ y →
      oddCoreOf (cen x) ⊓ cen y ≤ oddCoreOf (cen y) := by
  obtain ⟨P, htP, hPC⟩ := exists_sylow_central ht hn hcov
  have hshape := sylowShape_of_hasSylowTwoTypeAhat hn hD
    (hasSylowTwoTypeAhat_of_centralizer_cover ht hn hcov) P
  obtain ⟨z, hzP, hz2, hznc, R, hRP, hRz, hRcard⟩ := hshape.half
  have hzt : z ≠ t := fun h => hznc fun s hs => by
    rw [h]
    exact mem_centralizer_singleton_iff.1 (hPC hs)
  have hcovz := isDoubleCoverOfAlt_centQuot_of_involution hnonab ht hn hcov hB hz2
  have hRk : Nat.card R = 2 ^ (if n ≤ 9 then 6 else 7) := by
    have := hshape.card
    split_ifs at this ⊢ <;> omega
  have hcore : oddCoreOf (cen t) ⊓ cen z ≤ oddCoreOf (cen z) :=
    balance_core adm hadm R (fun r hr => mem_centralizer_singleton_iff.2 (hRz r hr))
      (hRP.trans hPC) hRk (hno _ hcovz) hO
  intro x y hx hy hxy hne
  obtain ⟨g, hg⟩ := exists_conj_of_involution hnonab ht hn hcov hB x hx
  set y' := g⁻¹ * y * g with hy'
  have hy'2 : orderOf y' = 2 := by
    rw [hy', ← hy]
    simpa using orderOf_conj_eq' g⁻¹ y
  have hy'C : y' ∈ cen t := by
    rw [mem_centralizer_singleton_iff]
    have h1 : x * y = y * x := hxy
    rw [hg] at h1
    calc y' * t = g⁻¹ * (y * (g * t * g⁻¹)) * g := by rw [hy']; group
      _ = g⁻¹ * ((g * t * g⁻¹) * y) * g := by rw [← h1]
      _ = t * y' := by rw [hy']; group
  have hy't : y' ≠ t := by
    intro h
    apply hne
    rw [hg, ← h, hy']
    group
  obtain ⟨m, hm, hmy⟩ := exists_conj_in_cen ht hcov (hB.one_class (CentQuot t) hcov) hy'C
    (hPC hzP) hy'2 hz2 hy't hzt
  have hmt : m * t = t * m := mem_centralizer_singleton_iff.mp hm
  have hmt' : m⁻¹ * t * m = t := by
    calc m⁻¹ * t * m = m⁻¹ * (t * m) := by group
      _ = m⁻¹ * (m * t) := by rw [hmt]
      _ = t := by group
  have hx' : x = (g * m⁻¹) * t * (g * m⁻¹)⁻¹ := by
    calc x = g * t * g⁻¹ := hg
      _ = g * (m⁻¹ * t * m) * g⁻¹ := by rw [hmt']
      _ = (g * m⁻¹) * t * (g * m⁻¹)⁻¹ := by group
  have hy'' : y = (g * m⁻¹) * z * (g * m⁻¹)⁻¹ := by
    have h1 : y' = m⁻¹ * z * m := by rw [← hmy]; group
    calc y = g * y' * g⁻¹ := by rw [hy']; group
      _ = (g * m⁻¹) * z * (g * m⁻¹)⁻¹ := by rw [h1]; group
  rw [hx', hy'']
  exact balance_conj (g * m⁻¹) hcore

theorem balanced {n : ℕ} (hn : 8 ≤ n) (hn10 : n ≤ 10) (hD : CoverSylowData n)
    (hB : AlternatingBalanceData n) (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) (hcov : IsDoubleCoverOfAlt (CentQuot t) n) :
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x * y = y * x → x ≠ y →
      oddCoreOf (cen x) ⊓ cen y ≤ oddCoreOf (cen y) :=
  balanced_of_adm hn hD hB Odd (fun _ _ hab hb => hb.of_dvd_nat hab)
    (fun K _ _ hK X hX hXc P hP hXP => hB.no_odd hn10 K hK X hX hXc P hP hXP) hnonab ht hcov
    (odd_card_oddCoreOf _)

theorem balanced_of_not_three_dvd {n : ℕ} (hn : 8 ≤ n) (hD : CoverSylowData n)
    (hB : AlternatingBalanceData n) (hnonab : ∃ a b : G, a * b ≠ b * a) {t : G}
    (ht : orderOf t = 2) (hcov : IsDoubleCoverOfAlt (CentQuot t) n)
    (h3 : ¬ 3 ∣ Nat.card (pPrimeCore 2 ↥(cen t))) :
    ∀ x y : G, orderOf x = 2 → orderOf y = 2 → x * y = y * x → x ≠ y →
      oddCoreOf (cen x) ⊓ cen y ≤ oddCoreOf (cen y) := by
  refine balanced_of_adm hn hD hB (fun m => Nat.Coprime m 6)
    (fun a b hab hb => Nat.Coprime.coprime_dvd_left hab hb)
    (fun K _ _ hK X hX hXc P hP hXP => hB.no_odd' K hK X hX hXc P hP hXP) hnonab ht hcov ?_
  have hodd : Odd (Nat.card (oddCoreOf (cen t))) := odd_card_oddCoreOf _
  have hcard : Nat.card (oddCoreOf (cen t)) = Nat.card (pPrimeCore 2 ↥(cen t)) :=
    Subgroup.card_map_of_injective (cen t).subtype_injective
  have h3' : ¬ 3 ∣ Nat.card (oddCoreOf (cen t)) := hcard ▸ h3
  show Nat.Coprime _ (2 * 3)
  exact Nat.Coprime.mul_right (Nat.coprime_two_right.mpr hodd)
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3' |>.symm)

end Balanced

end CFSG.OddStandard.Solomon75
