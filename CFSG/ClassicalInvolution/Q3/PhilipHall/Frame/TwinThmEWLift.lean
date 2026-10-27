module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf3OddStand
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmEPf8Cls
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

namespace TwinThmEW
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinThmE

section LiftF

variable {Y : Type} [Group Y] [Finite Y] {Λ : Set (Subgroup Y)}
  {N : Subgroup Y} [N.Normal]

theorem orderOf_mk_of_isPGroup (hN : Odd (Nat.card N)) {P : Subgroup Y} (hP : IsPGroup 2 ↥P)
    {a : Y} (ha : a ∈ P) : orderOf (QuotientGroup.mk' N a) = orderOf a := by
  apply Nat.dvd_antisymm
  · exact orderOf_map_dvd _ a
  · set m := orderOf (QuotientGroup.mk' N a) with hm
    have h1 : QuotientGroup.mk' N (a ^ m) = 1 := by
      rw [map_pow, hm]; exact pow_orderOf_eq_one _
    have hmem : a ^ m ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    have hdvd : orderOf (a ^ m) ∣ orderOf a := orderOf_pow_dvd m
    have hodd : Odd (orderOf (a ^ m)) := hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hmem)
    have h2 : IsPGroup 2 (Subgroup.zpowers a) := hP.to_le (Subgroup.zpowers_le.mpr ha)
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    rw [Nat.card_zpowers] at hk
    have hdvd2 : orderOf (a ^ m) ∣ 2 ^ k := hk ▸ hdvd
    have hcop : Nat.Coprime (orderOf (a ^ m)) 2 := Odd.coprime_two_right hodd
    have h3 : orderOf (a ^ m) = 1 := (hcop.pow_right k).eq_one_of_dvd hdvd2
    rw [orderOf_eq_one_iff] at h3
    rw [← orderOf_dvd_iff_pow_eq_one] at h3
    exact h3

theorem e189_lift_a_F (hΛ : HypOmegaGen Λ) (hN : Odd (Nat.card N)) {K : Subgroup Y} {z t : Y} (hK : K ∈
    Λ) (hz : IsUniqueInvolution K z)
    (ht2 : t * t = 1) (hzt : z * t = t * z) {K'' : Subgroup (Y ⧸ N)}
    (hK'' : K'' ∈ twinSet (quotFamily Λ N) (K.map (QuotientGroup.mk' N)))
    (hne : K'' ≠ K.map (QuotientGroup.mk' N)) {Rb₁ Rb₂ : Subgroup (Y ⧸ N)}
    (hRb₁ : IsSylow2In Rb₁ (K.map (QuotientGroup.mk' N))) (hRb₂ : IsSylow2In Rb₂ K'')
    (hRbc : Commutes Rb₁ Rb₂) {ub xb : Y ⧸ N} (hu : ub ∈ Rb₁ ⊔ Rb₂) (hu1 : ub ≠ 1)
    (hu2 : ub * ub = 1) (hux : xb * ub * xb⁻¹ = QuotientGroup.mk' N z * QuotientGroup.mk' N t)
    (hFb : (∃ eb : Y ⧸ N, eb * ub * eb⁻¹ = QuotientGroup.mk' N z) ∨
      ∀ a ∈ Rb₁, ∀ b ∈ Rb₂, orderOf a = 4 → orderOf b = 4 → ∃ eb : Y ⧸ N, eb * ub * eb⁻¹ = a * b) :
    ∃ K₃ ∈ twinSet Λ K, K₃ ≠ K ∧ ∃ R₁ R₃ : Subgroup Y, IsSylow2In R₁ K ∧ IsSylow2In R₃ K₃ ∧
      Commutes R₁ R₃ ∧ ∃ u x : Y, u ∈ R₁ ⊔ R₃ ∧ u ≠ 1 ∧ u * u = 1 ∧
        x * u * x⁻¹ = z * t ∧ ((∃ e : Y, e * u * e⁻¹ = z) ∨
          ∀ a ∈ R₁, ∀ b ∈ R₃, orderOf a = 4 → orderOf b = 4 → ∃ e : Y, e * u * e⁻¹ = a * b) := by
  set mk := QuotientGroup.mk' N with hmk
  
  obtain ⟨L, hLtw, hLmap⟩ := exists_lift_twin hΛ hN hK hK''
  obtain ⟨hLΛ, z₀, hz₀K, hz₀L⟩ := hLtw
  have hz₀ : z₀ = z := hz₀K.eq hz
  have hzL : IsUniqueInvolution L z := hz₀ ▸ hz₀L
  obtain ⟨R₁, hR₁, hR₁map⟩ := exists_lift_sylow hN hRb₁
  have hRb₂' : IsSylow2In Rb₂ (L.map mk) := by
    rw [hLmap]
    exact hRb₂
  obtain ⟨R₂, hR₂, hR₂map⟩ := exists_lift_sylow hN hRb₂'
  have hR₁2 : IsPGroup 2 R₁ := hR₁.2.1
  have hR₂2 : IsPGroup 2 R₂ := hR₂.2.1
  obtain ⟨m, hm, hP⟩ := exists_conj_isPGroup_sup hN hR₁2 hR₂2 (by rw [hR₁map, hR₂map]; exact hRbc)
  have hmk1 : mk m = 1 := (QuotientGroup.eq_one_iff _).mpr hm
  set L' : Subgroup Y := conjSub m L with hL'
  set R₃ : Subgroup Y := conjSub m R₂ with hR₃
  have hL'Λ : L' ∈ Λ := hΛ.conjInvariant m L hLΛ
  have hL'img : L'.map mk = K'' := by
    rw [hL', AscQuot.map_conjSub, hmk1, conjSub_one, hLmap]
  have hR₃syl : IsSylow2In R₃ L' := hR₂.conj m
  have hR₃img : R₃.map mk = Rb₂ := by
    rw [hR₃, AscQuot.map_conjSub, hmk1, conjSub_one, hR₂map]
  have hL'ne : L' ≠ K := by
    intro h
    apply hne
    rw [← hL'img, h]
  
  have hR₁Ω : R₁ ∈ RSet Λ := mem_RSet_of_isSylow2In hK hR₁
  have hR₃Ω : R₃ ∈ RSet Λ := mem_RSet_of_isSylow2In hL'Λ hR₃syl
  have h8₁ := hΛ.eight_le_of_mem_RSet hR₁Ω
  have h8₃ := hΛ.eight_le_of_mem_RSet hR₃Ω
  have hRne : R₁ ≠ R₃ := by
    intro h
    exact hL'ne (hΛ.eq_of_le_of_le hL'Λ hK hR₃syl.2.1 (by omega) hR₃syl.1 (h ▸ hR₁.1))
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  have hcomm : Commutes R₁ R₃ :=
    Q3CP.l67Gen Y Λ hΛ S R₁ hR₁Ω R₃ hR₃Ω (le_sup_left.trans hS) (le_sup_right.trans hS)
      hRne
  
  have hzR₁ : z ∈ R₁ := AscL62.mem_of_uniqueInvolution_of_pGroup hz hR₁.1 hR₁2 (by omega)
  have hz'L' : IsUniqueInvolution L' (m * z * m⁻¹) := hzL.conj m
  have hz'R₃ : m * z * m⁻¹ ∈ R₃ :=
    AscL62.mem_of_uniqueInvolution_of_pGroup hz'L' hR₃syl.1 hR₃syl.2.1 (by omega)
  have hzz' : z * (m * z * m⁻¹) = (m * z * m⁻¹) * z := hcomm z hzR₁ _ hz'R₃
  have hzz'1 : z * (m * z * m⁻¹) = 1 := by
    have hsq : (z * (m * z * m⁻¹)) * (z * (m * z * m⁻¹)) = 1 := by
      calc (z * (m * z * m⁻¹)) * (z * (m * z * m⁻¹))
          = z * ((m * z * m⁻¹) * z) * (m * z * m⁻¹) := by group
        _ = z * (z * (m * z * m⁻¹)) * (m * z * m⁻¹) := by rw [← hzz']
        _ = (z * z) * ((m * z * m⁻¹) * (m * z * m⁻¹)) := by group
        _ = 1 := by rw [hz.sq, hz'L'.sq, one_mul]
    have hmem : z * (m * z * m⁻¹) ∈ N := by
      refine (QuotientGroup.eq_one_iff _).mp ?_
      show mk _ = 1
      rw [map_mul, map_mul, map_mul, map_inv, hmk1, one_mul, inv_one, mul_one, ← map_mul, hz.sq,
        map_one]
    have hdvd : orderOf (z * (m * z * m⁻¹)) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hsq)
    have hodd : Odd (orderOf (z * (m * z * m⁻¹))) :=
      hN.of_dvd_nat (Subgroup.orderOf_dvd_natCard N hmem)
    have h1 : orderOf (z * (m * z * m⁻¹)) = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.mp h1
  have hz'z : m * z * m⁻¹ = z := by
    have := eq_inv_of_mul_eq_one_right hzz'1
    rw [this, inv_eq_of_mul_eq_one_right hz.sq]
  have hL'tw : L' ∈ twinSet Λ K := ⟨hL'Λ, z, hz, hz'z ▸ hz'L'⟩
  refine ⟨L', hL'tw, hL'ne, R₁, R₃, hR₁, hR₃syl, hcomm, ?_⟩
  
  have haP : ub ∈ (R₁ ⊔ R₃).map mk := by
    rw [Subgroup.map_sup, hR₁map, hR₃img]
    exact hu
  obtain ⟨u, huP, hu1', hu2', hmku⟩ := exists_involution_lift_of_isPGroup hN hP haP hu1 hu2
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective N xb
  have hw2 : (x₀ * u * x₀⁻¹) * (x₀ * u * x₀⁻¹) = 1 := by
    calc (x₀ * u * x₀⁻¹) * (x₀ * u * x₀⁻¹) = x₀ * (u * u) * x₀⁻¹ := by group
      _ = 1 := by rw [hu2']; group
  have hzt2 : (z * t) * (z * t) = 1 := mul_involution_of_commute hz.sq ht2 hzt
  have hmkw : mk (z * t) = mk (x₀ * u * x₀⁻¹) := by
    rw [map_mul, map_mul, map_mul, map_inv, hmku, hx₀, ← hux]
  obtain ⟨m', hm', hmw⟩ := exists_conj_eq_of_map_eq hN hzt2 hw2 hmkw
  refine ⟨u, m' * x₀, huP, hu1', hu2', ?_, ?_⟩
  · calc (m' * x₀) * u * (m' * x₀)⁻¹ = m' * (x₀ * u * x₀⁻¹) * m'⁻¹ := by group
      _ = z * t := hmw
  · have hord : ∀ (P : Subgroup Y), IsPGroup 2 ↥P → ∀ a ∈ P, orderOf (mk a) = orderOf a :=
      fun P hP a ha => orderOf_mk_of_isPGroup hN hP ha
    rcases hFb with ⟨eb, heb⟩ | hFb
    · left
      obtain ⟨e₀, he₀⟩ := QuotientGroup.mk'_surjective N eb
      have hw2' : (e₀ * u * e₀⁻¹) * (e₀ * u * e₀⁻¹) = 1 := by
        calc (e₀ * u * e₀⁻¹) * (e₀ * u * e₀⁻¹) = e₀ * (u * u) * e₀⁻¹ := by group
          _ = 1 := by rw [hu2']; group
      have himg : mk z = mk (e₀ * u * e₀⁻¹) := by
        rw [map_mul, map_mul, map_inv, he₀, hmku, heb]
      obtain ⟨m'', hm'', hmz⟩ := exists_conj_eq_of_map_eq hN hz.sq hw2' himg
      exact ⟨m'' * e₀, by rw [← hmz]; group⟩
    · right
      intro a ha b hb ha4 hb4
      have hma : mk a ∈ Rb₁ := by rw [← hR₁map]; exact Subgroup.mem_map_of_mem _ ha
      have hmb : mk b ∈ Rb₂ := by rw [← hR₃img]; exact Subgroup.mem_map_of_mem _ hb
      have ha4' : orderOf (mk a) = 4 := (hord R₁ hR₁2 a ha).trans ha4
      have hb4' : orderOf (mk b) = 4 := (hord R₃ hR₃syl.2.1 b hb).trans hb4
      obtain ⟨eb, heb⟩ := hFb _ hma _ hmb ha4' hb4'
      obtain ⟨e₀, he₀⟩ := QuotientGroup.mk'_surjective N eb
      have haK : a ∈ K := hR₁.1 ha
      have hbL : b ∈ L' := hR₃syl.1 hb
      have hsq : ∀ {M : Subgroup Y} {w c : Y}, IsUniqueInvolution M w → c ∈ M → orderOf c = 4 →
          c * c = w := by
        intro M w c hw hc h4
        have h1 : (c * c) * (c * c) = 1 := by
          have := pow_orderOf_eq_one c
          rw [h4] at this
          calc (c * c) * (c * c) = c ^ 4 := by simp [pow_succ, mul_assoc]
            _ = 1 := this
        rcases hw.unique (c * c) (M.mul_mem hc hc) h1 with h | h
        · exfalso
          have : orderOf c ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h)
          rw [h4] at this
          omega
        · exact h
      have ha2 : a * a = z := hsq hz haK ha4
      have hb2 : b * b = z := hsq (hz'z ▸ hz'L') hbL hb4
      have hab : a * b = b * a := hcomm a ha b hb
      have hab2 : (a * b) * (a * b) = 1 := by
        calc (a * b) * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [← hab]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, hz.sq]
      have hw2' : (e₀ * u * e₀⁻¹) * (e₀ * u * e₀⁻¹) = 1 := by
        calc (e₀ * u * e₀⁻¹) * (e₀ * u * e₀⁻¹) = e₀ * (u * u) * e₀⁻¹ := by group
          _ = 1 := by rw [hu2']; group
      have himg : mk (a * b) = mk (e₀ * u * e₀⁻¹) := by
        rw [map_mul, map_mul, map_mul, map_inv, he₀, hmku, heb]
      obtain ⟨n, hn, hnab⟩ := exists_conj_eq_of_map_eq hN hab2 hw2' himg
      exact ⟨n * e₀, by rw [← hnab]; group⟩

end LiftF

end TwinThmEW

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
