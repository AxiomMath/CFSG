module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.H35Comp

public section

namespace CFSG.EvenSporadicStandard.Induction.Balance

open Subgroup

theorem eq_of_card_two {P : Type*} [Group P] (hP : Nat.card P = 2) {a b : P} (ha : a ≠ 1)
    (hb : b ≠ 1) : a = b := by
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : P)).1 hP
  exact (hy a ha).trans (hy b hb).symm

theorem normalizer_le_centralizer_of_card_two {G : Type*} [Group G] (P : Sylow 2 G)
    (hP : Nat.card (P : Subgroup G) = 2) :
    normalizer (P : Set G) ≤ centralizer (P : Set G) := by
  intro g hg
  rw [mem_centralizer_iff]
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1, one_mul, mul_one]
  have hmem : g * x * g⁻¹ ∈ (P : Subgroup G) := (mem_normalizer_iff.1 hg x).1 hx
  have h1 : (⟨g * x * g⁻¹, hmem⟩ : (P : Subgroup G)) ≠ 1 := by
    intro h
    apply hx1
    have := congrArg Subtype.val h
    simp only [OneMemClass.coe_one] at this
    simpa using this
  have h2 : (⟨x, hx⟩ : (P : Subgroup G)) ≠ 1 := by
    intro h
    exact hx1 (congrArg Subtype.val h)
  have := congrArg Subtype.val (eq_of_card_two hP h1 h2)
  simp only at this
  calc x * g = (g * x * g⁻¹) * g := by rw [this]
    _ = g * x := by group

theorem exists_sylow_card_two {G : Type*} [Group G] [Finite G] (h2 : 2 ∣ Nat.card G)
    (h4 : ¬ 4 ∣ Nat.card G) : ∃ P : Sylow 2 G, Nat.card (P : Subgroup G) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := G)
  refine ⟨P, ?_⟩
  rw [P.card_eq_multiplicity]
  have hn : Nat.card G ≠ 0 := Nat.card_pos.ne'
  have hge : 1 ≤ (Nat.card G).factorization 2 :=
    (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hn).1 h2
  have hle : (Nat.card G).factorization 2 ≤ 1 := by
    by_contra hlt
    push Not at hlt
    apply h4
    have h22 : 2 ^ 2 ∣ 2 ^ (Nat.card G).factorization 2 := pow_dvd_pow 2 hlt
    exact h22.trans (Nat.ordProj_dvd _ _)
  rw [le_antisymm hle hge]
  norm_num

theorem not_four_dvd_card_of_sylow {A : Type*} [Group A] [Finite A]
    (h : ∀ P : Sylow 2 A, Nat.card (P : Subgroup A) = 2) : ¬ 4 ∣ Nat.card A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ := Sylow.nonempty (p := 2) (G := A)
  have h1 := h P
  rw [P.card_eq_multiplicity] at h1
  intro h4
  have hn : Nat.card A ≠ 0 := Nat.card_pos.ne'
  have h2 : 2 ≤ (Nat.card A).factorization 2 :=
    (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two hn).1 (by simpa using h4)
  have h3 : 2 ^ 2 ≤ 2 ^ (Nat.card A).factorization 2 := Nat.pow_le_pow_right (by norm_num) h2
  omega

theorem eq_zpowers_of_oddCore_eq_bot {G : Type} [Group G] [Finite G] (hO : CFSG.oddCore G = ⊥)
    (D : Subgroup G) [D.Normal] {t : G} (ht : t ∈ D) (ht2 : orderOf t = 2)
    (h4 : ¬ 4 ∣ Nat.card D) : D = zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ∣ Nat.card D := by
    have := Subgroup.orderOf_dvd_natCard D ht
    rwa [ht2] at this
  obtain ⟨P, hP⟩ := exists_sylow_card_two h2 h4
  have hN := normalizer_le_centralizer_of_card_two P hP
  set K := (MonoidHom.transferSylow P hN).ker with hK
  have hcompl : K.IsComplement' (P : Subgroup D) :=
    MonoidHom.ker_transferSylow_isComplement' P hN
  have hodd : Odd (Nat.card K) :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 (MonoidHom.not_dvd_card_ker_transferSylow P hN))
  have hKle : K ≤ CFSG.pPrimeCore 2 D := by
    rw [← EvenSporadicStandard.Solomon78.oddCore_eq_pPrimeCore_two']
    exact le_sSup ⟨inferInstance, hodd⟩
  have hKbot : K = ⊥ := by
    have h1 := CFSG.Walter.map_pPrimeCore_le_of_isSubnormal
      (Subgroup.Normal.isSubnormal ‹D.Normal›)
    have h2' : K.map D.subtype ≤ CFSG.pPrimeCore 2 G := (Subgroup.map_mono hKle).trans h1
    rw [← EvenSporadicStandard.Solomon78.oddCore_eq_pPrimeCore_two', hO, le_bot_iff] at h2'
    exact (Subgroup.map_eq_bot_iff_of_injective _ D.subtype_injective).1 h2'
  rw [hKbot] at hcompl
  have hPtop : (P : Subgroup D) = ⊤ := isComplement'_bot_left.1 hcompl
  have hcard : Nat.card D = 2 := by
    rw [← hP, hPtop, Subgroup.card_top]
  have hle : zpowers t ≤ D := Subgroup.zpowers_le.2 ht
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [Nat.card_zpowers, ht2, hcard]

theorem centralizer_inf_eq_zpowers {H : Type} [Group H] [Finite H] {C L : Subgroup H} {t : H}
    (hO : CFSG.oddCore ↥C = ⊥) (htC : t ∈ C) (ht2 : orderOf t = 2)
    (hL : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L) (htL : t ∈ centralizer (L : Set H))
    (h4 : ¬ 4 ∣ Nat.card (centralizer (L : Set H))) :
    centralizer (L : Set H) ⊓ C = zpowers t := by
  set D : Subgroup H := centralizer (L : Set H) ⊓ C with hD
  have hDC : D ≤ C := inf_le_right
  have hDn : (D.subgroupOf C).Normal := by
    refine ⟨fun d hd g => ?_⟩
    have hdL : (d : H) ∈ centralizer (L : Set H) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hd)).1
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, (g * d * g⁻¹ : ↥C).2⟩)
    rw [mem_centralizer_iff]
    intro l hl
    have hl' : (g : H)⁻¹ * l * (g : H) ∈ L := by
      simpa using hL _ (C.inv_mem g.2) l hl
    have h1 := mem_centralizer_iff.1 hdL _ hl'
    change l * ((g : H) * d * (g : H)⁻¹) = (g : H) * d * (g : H)⁻¹ * l
    calc l * ((g : H) * d * (g : H)⁻¹)
        = (g : H) * (((g : H)⁻¹ * l * g) * d) * (g : H)⁻¹ := by group
      _ = (g : H) * (d * ((g : H)⁻¹ * l * g)) * (g : H)⁻¹ := by rw [h1]
      _ = (g : H) * d * (g : H)⁻¹ * l := by group
  let t' : ↥C := ⟨t, htC⟩
  have ht'D : t' ∈ D.subgroupOf C := Subgroup.mem_subgroupOf.2 ⟨htL, htC⟩
  have ht'2 : orderOf t' = 2 := by rw [← ht2]; exact Subgroup.orderOf_mk _ _
  have h4' : ¬ 4 ∣ Nat.card (D.subgroupOf C) := by
    intro h
    apply h4
    refine h.trans ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDC).toEquiv]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hzp := eq_zpowers_of_oddCore_eq_bot hO (D.subgroupOf C) ht'D ht'2 h4'
  apply le_antisymm
  · intro d hd
    have hd' : (⟨d, hd.2⟩ : ↥C) ∈ D.subgroupOf C := hd
    rw [hzp, Subgroup.mem_zpowers_iff] at hd'
    obtain ⟨k, hk⟩ := hd'
    exact Subgroup.mem_zpowers_iff.2 ⟨k, congrArg Subtype.val hk⟩
  · exact Subgroup.zpowers_le.2 ⟨htL, htC⟩

theorem exists_conj_of_quotient_inner {X : Type*} [Group X] [Group.IsPerfect X]
    (hOut : ∀ φ : MulAut (X ⧸ center X), ∃ y, φ = MulAut.conj y) (α : MulAut X) :
    ∃ x : X, α = MulAut.conj x := by
  obtain ⟨y, hy⟩ := hOut (ComponentClassification.PerfectAutomorphisms.onCenterQuotient α)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  refine ⟨x, ComponentClassification.PerfectAutomorphisms.centerQuotientHom_injective X ?_⟩
  ext z
  obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
  show ComponentClassification.PerfectAutomorphisms.onCenterQuotient α
      (QuotientGroup.mk' (center X) z) =
    ComponentClassification.PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)
      (QuotientGroup.mk' (center X) z)
  rw [hy, ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk]
  simp [MulAut.conj_apply]

theorem centralizer_le_sup_zpowers {H : Type} [Group H] {C L : Subgroup H} {t : H}
    (hLC : L ≤ C) (hL : ∀ c ∈ C, ∀ l ∈ L, c * l * c⁻¹ ∈ L) [Group.IsPerfect ↥L]
    (hOut : ∀ φ : MulAut (↥L ⧸ center ↥L), ∃ y, φ = MulAut.conj y)
    (hD : centralizer (L : Set H) ⊓ C = zpowers t) : C ≤ L ⊔ zpowers t := by
  intro c hc
  have hcN : c ∈ normalizer (L : Set H) := by
    rw [mem_normalizer_iff]
    intro l
    refine ⟨hL c hc l, fun hl => ?_⟩
    have h := hL c⁻¹ (C.inv_mem hc) _ hl
    have e : c⁻¹ * (c * l * c⁻¹) * c⁻¹⁻¹ = l := by group
    rwa [e] at h
  obtain ⟨x, hx⟩ := exists_conj_of_quotient_inner hOut (L.normalizerMonoidHom ⟨c, hcN⟩)
  have hxc : (x : H)⁻¹ * c ∈ centralizer (L : Set H) ⊓ C := by
    refine Subgroup.mem_inf.2 ⟨?_, C.mul_mem (C.inv_mem (hLC x.2)) hc⟩
    rw [mem_centralizer_iff]
    intro m hm
    have h1 := congrArg (fun φ : MulAut L => (φ ⟨m, hm⟩ : H)) hx
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply,
      Subgroup.coe_mul, Subgroup.coe_inv] at h1
    have h2 : c * m = (x : H) * m * (x : H)⁻¹ * c := by rw [← h1]; group
    calc m * ((x : H)⁻¹ * c) = (x : H)⁻¹ * ((x : H) * m * (x : H)⁻¹ * c) := by group
      _ = (x : H)⁻¹ * (c * m) := by rw [h2]
      _ = (x : H)⁻¹ * c * m := by group
  rw [hD] at hxc
  have : c = (x : H) * ((x : H)⁻¹ * c) := by group
  rw [this]
  exact mul_mem_sup x.2 hxc

end CFSG.EvenSporadicStandard.Induction.Balance
