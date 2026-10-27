module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Facts
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Closing.Data
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.LocMFacts
public import CFSG.Monster.Existence.Simple

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup CFSG CFSG.Monster.Existence CFSG.Monster.Existence.Compat CFSG.Open
  CFSG.Blueprint CFSG.EvenSporadicStandard.Solomon78

@[expose] def InvolutionOddCoreTrivial (Y : Type) [Group Y] : Prop :=
  ∀ t : Y, orderOf t = 2 → ∀ P : Subgroup Y, P ≤ centralizer ({t} : Set Y) →
    (P.subgroupOf (centralizer ({t} : Set Y))).Normal → Odd (Nat.card P) → P = ⊥

theorem eq_bot_of_le_zpowers_of_odd {X : Type} [Group X] {t : X} (ht : orderOf t = 2)
    {P : Subgroup X} (hle : P ≤ zpowers t) (hodd : Odd (Nat.card P)) : P = ⊥ := by
  have hdvd : Nat.card P ∣ 2 := by
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, ht] at this
  rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
  · exact Subgroup.eq_bot_of_card_eq P h
  · rw [h] at hodd
    exact absurd hodd (by decide)

theorem InvolutionOddCoreTrivial.of_mulEquiv {Y X : Type} [Group Y] [Group X] (φ : Y ≃* X)
    (h : InvolutionOddCoreTrivial X) : InvolutionOddCoreTrivial Y := by
  intro t ht P hP hPn hodd
  have ht' : orderOf (φ t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hmap := map_centralizer_equiv φ t
  have hle : P.map (φ : Y →* X) ≤ centralizer ({φ t} : Set X) := by
    rw [← hmap]
    exact Subgroup.map_mono hP
  have hPn' : ((P.map (φ : Y →* X)).subgroupOf (centralizer ({φ t} : Set X))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨p, hp, hpn⟩ := mem_subgroupOf.1 hn
    obtain ⟨g0, hg0, hgg⟩ : ∃ g0 ∈ centralizer ({t} : Set Y), φ g0 = (g : X) := by
      have : (g : X) ∈ (centralizer ({t} : Set Y)).map (φ : Y →* X) := by
        rw [hmap]
        exact g.2
      exact this
    have hconj : g0 * p * g0⁻¹ ∈ P := by
      have := hPn.conj_mem ⟨p, hP hp⟩ (mem_subgroupOf.2 hp) ⟨g0, hg0⟩
      exact mem_subgroupOf.1 this
    rw [mem_subgroupOf]
    refine ⟨g0 * p * g0⁻¹, hconj, ?_⟩
    have e1 : (φ : Y →* X) g0 = (g : X) := hgg
    have e2 : (φ : Y →* X) p = (n : X) := hpn
    rw [map_mul, map_mul, map_inv, e1, e2]
    rfl
  have hodd' : Odd (Nat.card (P.map (φ : Y →* X))) := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hodd
  have hbot := h (φ t) ht' _ hle hPn' hodd'
  rw [eq_bot_iff]
  intro x hx
  have hx' : φ x ∈ P.map (φ : Y →* X) := ⟨x, hx, rfl⟩
  rw [hbot, mem_bot] at hx'
  exact mem_bot.2 (φ.injective (hx'.trans (map_one φ).symm))

theorem centralizes_of_odd_normal {X : Type} [Group X] {C P Q : Subgroup X}
    (hP : (P.subgroupOf C).Normal) (hQ : (Q.subgroupOf C).Normal) (hPC : P ≤ C) (hQC : Q ≤ C)
    (hPodd : Odd (Nat.card P)) (hQ2 : IsPGroup 2 Q) : P ≤ centralizer (Q : Set X) := by
  intro p hp
  rw [mem_centralizer_iff]
  intro q hq
  have hpq : p * q * p⁻¹ * q⁻¹ ∈ P := by
    have h1 : q * p⁻¹ * q⁻¹ ∈ P := by
      have := hP.conj_mem ⟨p⁻¹, hPC (P.inv_mem hp)⟩ (mem_subgroupOf.2 (P.inv_mem hp)) ⟨q, hQC hq⟩
      exact mem_subgroupOf.1 this
    have := P.mul_mem hp h1
    simpa [mul_assoc] using this
  have hpq' : p * q * p⁻¹ * q⁻¹ ∈ Q := by
    have h1 : p * q * p⁻¹ ∈ Q := by
      have := hQ.conj_mem ⟨q, hQC hq⟩ (mem_subgroupOf.2 hq) ⟨p, hPC hp⟩
      exact mem_subgroupOf.1 this
    exact Q.mul_mem h1 (Q.inv_mem hq)
  have h2 : orderOf (⟨p * q * p⁻¹ * q⁻¹, hpq⟩ : P) ∣ Nat.card P := orderOf_dvd_natCard _
  obtain ⟨k, hk⟩ := hQ2 ⟨p * q * p⁻¹ * q⁻¹, hpq'⟩
  have h3 : orderOf (⟨p * q * p⁻¹ * q⁻¹, hpq'⟩ : Q) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h4 : orderOf (p * q * p⁻¹ * q⁻¹) = orderOf (⟨p * q * p⁻¹ * q⁻¹, hpq⟩ : P) := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mk]
  have h5 : orderOf (p * q * p⁻¹ * q⁻¹) = orderOf (⟨p * q * p⁻¹ * q⁻¹, hpq'⟩ : Q) := by
    rw [← Subgroup.orderOf_coe, Subgroup.coe_mk]
  have h6 : orderOf (p * q * p⁻¹ * q⁻¹) ∣ 2 ^ k := h5 ▸ h3
  have h7 : orderOf (p * q * p⁻¹ * q⁻¹) ∣ Nat.card P := h4 ▸ h2
  have h8 : Nat.Coprime (2 ^ k) (Nat.card P) := by
    apply Nat.Coprime.pow_left
    exact Nat.coprime_two_left.2 hPodd
  have h9 : orderOf (p * q * p⁻¹ * q⁻¹) = 1 :=
    Nat.eq_one_of_dvd_coprimes h8 h6 h7
  have h10 : p * q * p⁻¹ * q⁻¹ = 1 := orderOf_eq_one_iff.1 h9
  calc q * p = (p * q * p⁻¹ * q⁻¹) * q * p := by rw [h10, one_mul]
    _ = p * q := by group

theorem monsterOddCore_of_existence {X : Type} [Group X] (h : MonsterExistenceStatement X)
    (F : TwoAFacts) : InvolutionOddCoreTrivial X := by
  obtain ⟨⟨hfin, -, -, -⟩, a, z, -, -, -, hinv, hA, hBz, -⟩ := h
  have := hfin
  intro t ht P hP hPn hodd
  rcases hinv t ht with h1 | h1
  · obtain ⟨-, hzc, ⟨e⟩⟩ := hA t h1
    set C : Subgroup X := centralizer ({t} : Set X) with hC
    have hsimple : IsSimpleGroup (↥C ⧸ center ↥C) :=
      @MulEquiv.isSimpleGroup _ _ _ _ F.b_simple e
    set Q1 : Subgroup (↥C ⧸ center ↥C) :=
      (P.subgroupOf C).map (QuotientGroup.mk' (center ↥C)) with hQ1
    have hQ1n : Q1.Normal := hPn.map _ QuotientGroup.mk_surjective
    have hP'card : Nat.card (P.subgroupOf C) = Nat.card P :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP).toEquiv
    have hQ1dvd : Nat.card Q1 ∣ Nat.card P := hP'card ▸ Subgroup.card_map_dvd _ _
    rcases hsimple.eq_bot_or_eq_top_of_normal Q1 with hbot | htop
    · have hle : P.subgroupOf C ≤ center ↥C := by
        intro x hx
        have : QuotientGroup.mk' (center ↥C) x ∈ Q1 := mem_map_of_mem _ hx
        rw [hbot, mem_bot] at this
        exact (QuotientGroup.eq_one_iff x).1 this
      have hPle : P ≤ zpowers t := by
        intro x hx
        have hx' : (⟨x, hP hx⟩ : ↥C) ∈ center ↥C := hle (mem_subgroupOf.2 hx)
        rw [← hzc]
        exact ⟨⟨x, hP hx⟩, hx', rfl⟩
      exact eq_bot_of_le_zpowers_of_odd ht hPle hodd
    · exfalso
      rw [htop, Subgroup.card_top, Nat.card_congr e.toEquiv, F.b_card] at hQ1dvd
      have hev : Even monsterBabyOrder := by
        unfold monsterBabyOrder
        norm_num
      exact (Nat.not_even_iff_odd.2 (hodd.of_dvd_nat hQ1dvd)) hev
  · have hB := hBz t h1
    have hQn : ((twoCore t).subgroupOf (cent t)).Normal := by
      rw [twoCore, inSubgroup, ← comap_subtype,
        comap_map_eq_self_of_injective (cent t).subtype_injective]
      exact pCore_normal
    have hQp : IsPGroup 2 (twoCore t) := pCore_isPGroup.map _
    have hPc : P ≤ centralizer (twoCore t : Set X) :=
      centralizes_of_odd_normal hPn hQn hP (twoCore_le t) hodd hQp
    have hle : P ≤ zpowers t := by
      rw [← IsTwoBCentralizer.inf_centralizer_eq ht hB]
      exact le_inf hP hPc
    exact eq_bot_of_le_zpowers_of_odd ht hle hodd

theorem autOddCoreTrivial_of_allInner {Y : Type} [Group Y] (hinn : AllInner Y)
    (hZ : center Y = ⊥) (h : InvolutionOddCoreTrivial Y) : AutOddCoreTrivial Y := by
  intro ν hν1 hνν P hP hPn hodd
  obtain ⟨g, rfl⟩ := hinn ν
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hν1 (map_one _)
  have hg2 : g ^ 2 = 1 := by
    have hc : g * g ∈ center Y := by
      rw [Subgroup.mem_center_iff]
      intro y
      have := congrArg (fun f : MulAut Y => f y) hνν
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.one_apply] at this
      calc y * (g * g) = (g * (g * y * g⁻¹) * g⁻¹) * (g * g) := by rw [this]
        _ = g * g * y := by group
    rw [hZ, Subgroup.mem_bot] at hc
    rw [pow_two]
    exact hc
  have hord : orderOf g = 2 := orderOf_eq_prime hg2 hg1
  have hfix := fixSubgroup_conj g
  rw [hfix] at hP hPn
  exact h g hord P hP hPn hodd

theorem AutOddCoreTrivial.of_mulEquiv {Y X : Type} [Group Y] [Group X] (φ : Y ≃* X)
    (h : AutOddCoreTrivial X) : AutOddCoreTrivial Y := by
  intro ν hν1 hνν P hP hPn hodd
  set ν' : MulAut X := MulAut.congr φ ν with hν'
  have hν'app : ∀ y : Y, ν' (φ y) = φ (ν y) := fun y => by
    rw [hν', MulAut.congr_apply]
    simp
  have hfix : ∀ y : Y, y ∈ fixSubgroup ν ↔ φ y ∈ fixSubgroup ν' := fun y => by
    show ν y = y ↔ ν' (φ y) = φ y
    rw [hν'app]
    exact ⟨fun h' => by rw [h'], fun h' => φ.injective h'⟩
  have hν'1 : ν' ≠ 1 := by
    intro h1
    apply hν1
    ext y
    have := hν'app y
    rw [h1, MulAut.one_apply] at this
    exact φ.injective this.symm
  have hν'ν' : ν' * ν' = 1 := by
    ext x
    obtain ⟨y, rfl⟩ := φ.surjective x
    rw [MulAut.mul_apply, hν'app, hν'app]
    have := congrArg (fun f : MulAut Y => φ (f y)) hνν
    simpa using this
  have hle : P.map (φ : Y →* X) ≤ fixSubgroup ν' := by
    rintro _ ⟨p, hp, rfl⟩
    exact (hfix p).1 (hP hp)
  have hPn' : ((P.map (φ : Y →* X)).subgroupOf (fixSubgroup ν')).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨p, hp, hpn⟩ := mem_subgroupOf.1 hn
    obtain ⟨g0, hg0⟩ := φ.surjective (g : X)
    have hg0f : g0 ∈ fixSubgroup ν := (hfix g0).2 (by rw [hg0]; exact g.2)
    have hconj : g0 * p * g0⁻¹ ∈ P := by
      have := hPn.conj_mem ⟨p, hP hp⟩ (mem_subgroupOf.2 hp) ⟨g0, hg0f⟩
      exact mem_subgroupOf.1 this
    rw [mem_subgroupOf]
    refine ⟨g0 * p * g0⁻¹, hconj, ?_⟩
    have e1 : (φ : Y →* X) g0 = (g : X) := hg0
    have e2 : (φ : Y →* X) p = (n : X) := hpn
    rw [map_mul, map_mul, map_inv, e1, e2]
    rfl
  have hodd' : Odd (Nat.card (P.map (φ : Y →* X))) := by
    rw [Subgroup.card_map_of_injective φ.injective]
    exact hodd
  have hbot := h ν' hν'1 hν'ν' _ hle hPn' hodd'
  rw [eq_bot_iff]
  intro x hx
  have hx' : φ x ∈ P.map (φ : Y →* X) := ⟨x, hx, rfl⟩
  rw [hbot, mem_bot] at hx'
  exact mem_bot.2 (φ.injective (hx'.trans (map_one φ).symm))

end CFSG.EvenSporadicStandard.Induction
