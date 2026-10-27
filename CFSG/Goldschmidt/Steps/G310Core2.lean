module

public import CFSG.Goldschmidt.Steps.G310Core1
public import CFSG.Goldschmidt.Steps.G310Trans

public section

namespace CFSG.Goldschmidt.G310

open CFSG.Open
open scoped commutatorElement

section SylowIndex

variable {X : Type*} [Group X] [Finite X]

theorem fusionIsSylowIn_of_relIndex {p : ℕ} [Fact p.Prime] {S N Y : Subgroup X} [N.Normal]
    (hS : fusionIsSylowIn p S N) (hNY : N ≤ Y) (hidx : ¬ p ∣ N.relIndex Y) :
    fusionIsSylowIn p S Y := by
  refine ⟨hS.1.trans hNY, hS.2.1, fun Q hQY hQ hSQ => hS.2.2 Q ?_ hQ hSQ⟩
  have h1 : N.relIndex (N ⊔ Q) = N.relIndex Q := Subgroup.relIndex_sup_left Q N
  have h2 := Subgroup.relIndex_mul_relIndex (H := N) (K := N ⊔ Q) (L := Y) le_sup_left
    (sup_le hNY hQY)
  have hdvd : N.relIndex Q ∣ N.relIndex Y := by
    rw [← h1]
    exact Dvd.intro _ h2
  obtain ⟨a, ha⟩ := hQ.exists_card_eq
  have hdvd' : N.relIndex Q ∣ p ^ a := ha ▸ Subgroup.relIndex_dvd_card _ _
  obtain ⟨b, -, hb⟩ := (Nat.dvd_prime_pow Fact.out).mp hdvd'
  have hb0 : b = 0 := by
    by_contra hb0
    apply hidx
    rw [hb] at hdvd
    exact (dvd_pow_self p hb0).trans hdvd
  rw [hb0, pow_zero] at hb
  exact Subgroup.relIndex_eq_one.mp hb

omit [Finite X] in
theorem fusionIsSylowIn_of_le {p : ℕ} {S Y Z : Subgroup X} (hS : fusionIsSylowIn p S Y)
    (hSZ : S ≤ Z) (hZY : Z ≤ Y) : fusionIsSylowIn p S Z :=
  ⟨hSZ, hS.2.1, fun Q hQZ hQ hSQ => hS.2.2 Q (hQZ.trans hZY) hQ hSQ⟩

end SylowIndex

section A0

variable {M : Type} [Group M] [Finite M]

theorem isSylow_h0
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    fusionIsSylowIn 2 (A ⊓ layerII A) (h0 A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := layerII_normal A
  refine fusionIsSylowIn_of_relIndex (isSylow_layerII hO hS) le_sup_left ?_
  have h3 : (layerII A).relIndex (h0 A) = (layerII A).relIndex (oddCent A) :=
    Subgroup.relIndex_sup_left (oddCent A) (layerII A)
  rw [h3]
  intro h2
  exact (Nat.not_even_iff_odd.mpr (odd_card_oddCent A))
    (even_iff_two_dvd.mpr (h2.trans (Subgroup.relIndex_dvd_card _ _)))

omit [Finite M] in
theorem isMulCommutative_inf {A : Subgroup M} (hS : IsSStarIn ⊤ A) :
    IsMulCommutative ↥(A ⊓ layerII A) :=
  ⟨⟨fun a b => Subtype.ext (mul_comm_of_isMulCommutative hS.2.1 a.2.1 b.2.1)⟩⟩

omit [Finite M] in
theorem h0_le_centralizer (A : Subgroup M) :
    h0 A ≤ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (layerII A : Set M) : Subgroup M) : Set M) := by
  refine sup_le (fun l hl => ?_) (fun d hd => ?_)
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp ha.2 l hl).symm
  · rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (oddCent_le A hd) a ha.1

theorem le_normalizer_of_inf
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {R : Subgroup M} (hRH : R ≤ h0 A)
    (hAR : A ⊓ layerII A ≤ Subgroup.normalizer (R : Set M)) :
    A ≤ Subgroup.normalizer (R : Set M) := by
  rw [split_layerII hO hS]
  refine sup_le hAR ?_
  intro c hc
  apply Subgroup.centralizer_le_normalizer
  rw [Subgroup.mem_centralizer_iff]
  intro r hr
  exact (Subgroup.mem_centralizer_iff.mp (h0_le_centralizer A (hRH hr)) c hc).symm

end A0

section Burnside

variable {M : Type} [Group M] [Finite M]

theorem inf_centralizer_le_oddCent
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Subgroup M}
    (hRH : R ≤ h0 A) (hR : IsPGroup p R) :
    R ⊓ Subgroup.centralizer (A : Set M) ≤ oddCent A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact p.Prime := ⟨hp⟩
  set C₁ := h0 A ⊓ Subgroup.centralizer (A : Set M) with hC₁
  set A₀ := A ⊓ layerII A with hA₀
  have hA₀C : A₀ ≤ C₁ := fun a ha =>
    ⟨Subgroup.mem_sup_left ha.2, Subgroup.mem_centralizer_iff.mpr fun b hb =>
      mul_comm_of_isMulCommutative hS.2.1 hb ha.1⟩
  have hsyl : fusionIsSylowIn 2 A₀ C₁ := fusionIsSylowIn_of_le (isSylow_h0 hO hS) hA₀C inf_le_left
  obtain ⟨S, hSdef⟩ := G3a.exists_sylow_of_fusionIsSylowIn hsyl
  have hScen : Subgroup.centralizer ((S : Subgroup C₁) : Set C₁) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    rw [hSdef] at hs
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp x.2.2 _ hs.1)
  have hP : Subgroup.normalizer ((S : Subgroup C₁) : Set C₁) ≤
      Subgroup.centralizer ((S : Subgroup C₁) : Set C₁) := by
    rw [hScen]
    exact le_top
  set τ := MonoidHom.transferSylow S hP with hτ
  have hcomp := MonoidHom.ker_transferSylow_isComplement' S hP
  have hkerodd : Odd (Nat.card τ.ker) := by
    have h1 := hcomp.card_mul_card
    have h2 := (S : Subgroup C₁).card_mul_index
    have h3 : Nat.card τ.ker = (S : Subgroup C₁).index := by
      have hpos : 0 < Nat.card (S : Subgroup C₁) := Nat.card_pos
      rw [← h2] at h1
      rw [mul_comm (Nat.card (S : Subgroup C₁))] at h1
      exact Nat.eq_of_mul_eq_mul_right hpos h1
    rw [h3]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp S.not_dvd_index)
  have hker : τ.ker ≤ goldschmidtOddCore C₁ := le_sSup ⟨inferInstance, hkerodd⟩
  have hOC : oddCoreOf C₁ ≤ oddCent A := by
    refine le_oddCoreOf_of_normalizer ((oddCoreOf_le C₁).trans (le_inf le_top inf_le_right))
      ?_ (not_two_dvd_card_oddCoreOf C₁)
    intro c hc
    have hcN : c ∈ Subgroup.normalizer (C₁ : Set M) := by
      refine le_normalizer_inf (A := Subgroup.centralizer (A : Set M)) ?_ Subgroup.le_normalizer
        hc.2
      intro y _
      rw [Subgroup.normalizer_eq_top_iff.mpr (h0_normal hO hS)]
      exact Subgroup.mem_top y
    apply mem_normalizer_of_map_le
    rintro _ ⟨d, hd, rfl⟩
    have hd' : d ∈ (pPrimeCore 2 C₁).map C₁.subtype := by
      rw [← goldschmidtOddCore_eq_pPrimeCore]
      exact hd
    have := CFSG.Walter.conj_mem_map_of_characteristic hcN hd'
    rw [← goldschmidtOddCore_eq_pPrimeCore] at this
    exact this
  intro x hx
  have hxC : x ∈ C₁ := ⟨hRH hx.1, hx.2⟩
  have hτx : τ ⟨x, hxC⟩ = 1 := by
    obtain ⟨n, hn⟩ := hR ⟨x, hx.1⟩
    have hxn : (⟨x, hxC⟩ : C₁) ^ p ^ n = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hn
    have h1 : orderOf (τ ⟨x, hxC⟩) ∣ p ^ n :=
      (orderOf_map_dvd τ _).trans (orderOf_dvd_of_pow_eq_one hxn)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') (τ ⟨x, hxC⟩)
    rw [hk] at h1
    have h2 : 2 ^ k ∣ 1 := by
      have hcop : Nat.Coprime (2 ^ k) (p ^ n) :=
        Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
      exact Nat.Coprime.eq_one_of_dvd hcop h1 ▸ dvd_refl _
    rw [Nat.dvd_one] at h2
    rw [← orderOf_eq_one_iff, hk, h2]
  have hmem : (⟨x, hxC⟩ : C₁) ∈ goldschmidtOddCore C₁ := hker hτx
  exact hOC ⟨⟨x, hxC⟩, hmem, rfl⟩

end Burnside

section MaxInv

variable {X : Type*} [Group X]

theorem IsMaxInvIn.conjSub' {Y B P : Subgroup X} {p : ℕ} (hP : IsMaxInvIn Y B p P) {n : X}
    (hnB : n ∈ Subgroup.normalizer (B : Set X)) (hnY : n ∈ Subgroup.normalizer (Y : Set X)) :
    IsMaxInvIn Y B p (conjSub n P) := by
  have hnY' : conjSub n Y = Y := conjSub_eq_of_mem_normalizer hnY
  have hnY'' : conjSub n⁻¹ Y = Y := conjSub_eq_of_mem_normalizer (Subgroup.inv_mem _ hnY)
  refine ⟨⟨?_, hP.prop.2.conjSub hnB⟩, fun Q hQ hle => ?_⟩
  · rw [← hnY']
    exact conjSub_mono hP.prop.1
  · have h1 : P ≤ conjSub n⁻¹ Q := by
      have := conjSub_mono (g := n⁻¹) hle
      rwa [conjSub_inv_conjSub] at this
    have h2 : conjSub n⁻¹ Q ≤ Y := by
      rw [← hnY'']
      exact conjSub_mono hQ.1
    have h3 := hP.2 ⟨h2, hQ.2.conjSub (Subgroup.inv_mem _ hnB)⟩ h1
    have := conjSub_mono (g := n) h3
    rwa [conjSub_conjSub_inv] at this

theorem mem_sup_of_conjSub_eq {P Y : Subgroup X} {n y : X} (hy : y ∈ Y)
    (h : conjSub n P = conjSub y P) : n ∈ Y ⊔ Subgroup.normalizer (P : Set X) := by
  have h1 : conjSub (n * y⁻¹) P = P := by
    rw [conjSub_mul, h, conjSub_inv_conjSub]
  have h2 := mem_normalizer_of_conjSub_eq h1
  have e : n = (n * y⁻¹) * y := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_right h2) (Subgroup.mem_sup_left hy)

theorem top_le_sup_normalizer_of_normal [Finite X] {p : ℕ} [Fact p.Prime] {S N : Subgroup X}
    [N.Normal] (hS : fusionIsSylowIn p S N) :
    (⊤ : Subgroup X) ≤ N ⊔ Subgroup.normalizer (S : Set X) := by
  obtain ⟨P, hP⟩ := exists_sylow_of_fusionIsSylowIn hS
  have h := Sylow.normalizer_sup_eq_top P
  rw [hP, sup_comm] at h
  rw [h]

end MaxInv

section Main

variable {M : Type} [Group M] [Finite M]

theorem isMaxInvIn_h0
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M} (hS : IsSStarIn ⊤ A)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup M}
    (hP : Maximal (· ∈ sigN ⊤ A p) P) : IsMaxInvIn (h0 A) (A ⊓ layerII A) p P := by
  obtain ⟨-, hPp, hAP, -⟩ := hP.prop
  refine ⟨⟨(le_h0 hO hS hp hp2 hP.prop).1, hPp, inf_le_left.trans hAP⟩, fun Q hQ hle => ?_⟩
  have hAQ := le_normalizer_of_inf hO hS hQ.1 hQ.2.2
  exact hP.2 ⟨le_top, hQ.2.1, hAQ, inf_centralizer_le_oddCent hO hS hp hp2 hQ.1 hQ.2.1⟩ hle

theorem h0_le_normalizer_sup
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {P : Subgroup M} (hPH : P ≤ h0 A) :
    h0 A ≤ Subgroup.normalizer ((layerII A ⊔ P : Subgroup M) : Set M) := by
  apply le_normalizer_of_conj_mem
  intro h hh y hy
  have hyH : y ∈ h0 A := sup_le le_sup_left hPH hy
  have hc : ⁅y⁻¹, h⁆ ∈ layerII A :=
    commutator_h0_le hO hS (Subgroup.commutator_mem_commutator ((h0 A).inv_mem hyH) hh)
  have e : h * y * h⁻¹ = y * ⁅y⁻¹, h⁆ := by
    rw [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ hy (Subgroup.mem_sup_left hc)

theorem top_le_layerII_sup_normalizer
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup M}
    (hP : Maximal (· ∈ sigN ⊤ A p) P) :
    (⊤ : Subgroup M) ≤ layerII A ⊔ Subgroup.normalizer (P : Set M) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A₀ := A ⊓ layerII A with hA₀
  have hHn := h0_normal hO hS
  have hmax := isMaxInvIn_h0 hO hS hp hp2 hP
  have hsyl := isSylow_h0 hO hS
  have hab := isMulCommutative_inf hS
  have hPH := (le_h0 hO hS hp hp2 hP.prop).1
  have hA₀H : A₀ ≤ h0 A := inf_le_right.trans le_sup_left
  have hN : Subgroup.normalizer (A₀ : Set M) ≤ h0 A ⊔ Subgroup.normalizer (P : Set M) := by
    intro n hn
    have hnH : n ∈ Subgroup.normalizer (h0 A : Set M) := by
      rw [Subgroup.normalizer_eq_top_iff.mpr hHn]
      exact Subgroup.mem_top n
    obtain ⟨y, hy, hyP⟩ := exists_conj_of_isMaxInvIn hA₀H hab hsyl hp2 hmax
      (hmax.conjSub' hn hnH)
    exact mem_sup_of_conjSub_eq hy.1 hyP
  have h1 : (⊤ : Subgroup M) ≤ h0 A ⊔ Subgroup.normalizer (P : Set M) :=
    (top_le_sup_normalizer_of_normal hsyl).trans (sup_le le_sup_left hN)
  set Y := layerII A ⊔ P with hY
  have hYH : Y ≤ h0 A := sup_le le_sup_left hPH
  have hHY := h0_le_normalizer_sup hO hS hPH
  have hmaxY : IsMaxInvIn Y A₀ p P :=
    ⟨⟨le_sup_right, hmax.prop.2⟩, fun Q hQ hle => hmax.2 ⟨hQ.1.trans hYH, hQ.2⟩ hle⟩
  have hsylY : fusionIsSylowIn 2 A₀ Y :=
    fusionIsSylowIn_of_le hsyl (inf_le_right.trans le_sup_left) hYH
  have hD : oddCent A ≤ layerII A ⊔ Subgroup.normalizer (P : Set M) := by
    intro d hd
    have hdA : d ∈ Subgroup.normalizer (A₀ : Set M) := by
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact Subgroup.mem_centralizer_iff.mp (oddCent_le A hd) a ha.1
    obtain ⟨y, hy, hyP⟩ := exists_conj_of_isMaxInvIn (inf_le_right.trans le_sup_left) hab hsylY
      hp2 hmaxY (hmaxY.conjSub' hdA (hHY (Subgroup.mem_sup_right hd)))
    have h2 := mem_sup_of_conjSub_eq hy.1 hyP
    exact (sup_le (sup_le le_sup_left (Subgroup.le_normalizer.trans le_sup_right))
      le_sup_right) h2
  exact h1.trans (sup_le (sup_le le_sup_left hD) le_sup_right)

theorem eq_of_le_layerII_sup
    (hO : goldschmidtOddCore M = ⊥) {A : Subgroup M}
    (hS : IsSStarIn ⊤ A) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {P : Subgroup M}
    (hP : Maximal (· ∈ sigN ⊤ A p) P) {R : Subgroup M} (hRle : R ≤ layerII A ⊔ P)
    (hR : IsPGroup p R) (hAR : A ≤ Subgroup.normalizer (R : Set M)) (hPR : P ≤ R) : R = P := by
  have hPH := (le_h0 hO hS hp hp2 hP.prop).1
  have hRH : R ≤ h0 A := hRle.trans (sup_le le_sup_left hPH)
  exact le_antisymm (hP.2 ⟨le_top, hR, hAR, inf_centralizer_le_oddCent hO hS hp hp2 hRH hR⟩ hPR)
    hPR

end Main

end CFSG.Goldschmidt.G310
