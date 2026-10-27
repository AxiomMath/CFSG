module

public import CFSG.Walter.Cited.SuzukiCases
public import CFSG.CharacterTheory.Semidihedral.Principal.CyclicTorusNormalizerQuotientsSupport
public import Certificates.Data.A5

public section

open scoped Classical

namespace CFSG.BrauerLinearThree

namespace TenFourGroup

@[expose] def a5CentralizerCard (x : alternatingGroup (Fin 5)) : ℕ :=
  ((Finset.univ : Finset (alternatingGroup (Fin 5))).filter fun y => y * x = x * y).card

theorem a5CentralizerCard_eq_four :
    ∀ x : alternatingGroup (Fin 5), x ≠ 1 → x ^ 2 = 1 → a5CentralizerCard x = 4 := by
  decide

theorem card_centralizer_alternatingGroup_five {x : alternatingGroup (Fin 5)} (hx1 : x ≠ 1)
    (hx2 : x ^ 2 = 1) :
    Nat.card (Subgroup.centralizer ({x} : Set (alternatingGroup (Fin 5)))) = 4 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have h := a5CentralizerCard_eq_four x hx1 hx2
  rw [a5CentralizerCard] at h
  rw [← h]
  congr 1
  ext y
  simp [Subgroup.mem_centralizer_singleton_iff]

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem commute_of_mem_sup {V W : Subgroup A} (hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v)
    {x y : A} (hx : x ∈ V ⊔ W) (hy : y ∈ V ⊔ W) : x * y = y * x := by
  have hVc : V ≤ Subgroup.centralizer (W : Set A) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => (hVW v hv w hw).symm
  obtain ⟨v₁, hv₁, w₁, hw₁, rfl⟩ :=
    CFSG.Semidihedral.Principal.exists_mul_eq_of_mem_sup_of_le_centralizer hVc hx
  obtain ⟨v₂, hv₂, w₂, hw₂, rfl⟩ :=
    CFSG.Semidihedral.Principal.exists_mul_eq_of_mem_sup_of_le_centralizer hVc hy
  calc v₁ * w₁ * (v₂ * w₂) = (v₁ * v₂) * (w₁ * w₂) := by
        rw [mul_assoc, ← mul_assoc w₁, ← hVW v₂ hv₂ w₁ hw₁, mul_assoc, mul_assoc]
    _ = (v₂ * v₁) * (w₂ * w₁) := by rw [hVab v₁ hv₁ v₂ hv₂, hWab w₁ hw₁ w₂ hw₂]
    _ = v₂ * w₂ * (v₁ * w₁) := by
        rw [mul_assoc, ← mul_assoc v₁, hVW v₁ hv₁ w₂ hw₂, mul_assoc, mul_assoc]

theorem exists_preimage_centralizer {O : Subgroup A} [O.Normal] (hOodd : Odd (Nat.card O))
    {t : A} (ht : orderOf t = 2) (q : A ⧸ O)
    (hq : q * (QuotientGroup.mk' O t) = (QuotientGroup.mk' O t) * q) :
    ∃ c : A, c * t = t * c ∧ QuotientGroup.mk' O c = q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective O q
  have hA : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  let α : Subgroup.zpowers t →* MulAut A := MulAut.conj.comp (Subgroup.zpowers t).subtype
  have hcop : ¬ 2 ∣ Nat.card O := fun h => (Nat.not_even_iff_odd.mpr hOodd) (even_iff_two_dvd.mpr h)
  obtain ⟨c, hc, hfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 2 hA α O
    hcop g).2 (by
      intro a x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hcomm : Commute (QuotientGroup.mk' O g) (QuotientGroup.mk' O t) := hq
      have hxg : QuotientGroup.mk' O x = QuotientGroup.mk' O g := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
        exact hx
      rw [← QuotientGroup.eq_one_iff]
      change QuotientGroup.mk' O (g⁻¹ * ((a : A) * x * (a : A)⁻¹)) = 1
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxg, ← hk, map_zpow,
        ← (hcomm.zpow_right k).eq]
      group)
  have hct := hfix ⟨t, Subgroup.mem_zpowers t⟩
  change t * c * t⁻¹ = c at hct
  refine ⟨c, ?_, ?_⟩
  · calc c * t = t * c * t⁻¹ * t := by rw [hct]
      _ = t * c := by group
  · rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, eq_comm, QuotientGroup.eq]
    exact hc

theorem le_pPrimeCore_of_kleinFour_sylow
    (V W : Subgroup A) (P : Sylow 2 A)
    (hPV : (P : Subgroup A) = V) (hV : IsKleinFour V) (t : A) (htV : t ∈ V)
    (ht : orderOf t = 2) (hC : Subgroup.centralizer ({t} : Set A) = V ⊔ W)
    (hVW : ∀ v ∈ V, ∀ w ∈ W, v * w = w * v) (hWab : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a)
    (hWodd : Odd (Nat.card W)) (htrans : ∀ v ∈ V, v ≠ 1 → ∃ a : A, a * t * a⁻¹ = v) :
    W ≤ CFSG.pPrimeCore 2 A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hVab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (mul_comm_of_exponent_two hV.exponent_two ⟨a, ha⟩ ⟨b, hb⟩)
  have hVc : V ≤ Subgroup.centralizer (W : Set A) := fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw => (hVW v hv w hw).symm
  have hconj : ∀ x : A, orderOf x = 2 → IsConj x t := by
    intro x hx
    have hxp : IsPGroup 2 (Subgroup.zpowers x) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
    obtain ⟨y, hxy⟩ :=
      CFSG.Semidihedral.InvolutionFusion.exists_ambient_conjugate_mem_sylow P x hxp
    have hyV : (y : A) ∈ V := hPV ▸ y.2
    have hy1 : (y : A) ≠ 1 := by
      intro h1
      rw [h1, isConj_one_left] at hxy
      rw [hxy, orderOf_one] at hx
      exact absurd hx (by norm_num)
    obtain ⟨a, ha⟩ := htrans y hyV hy1
    exact hxy.trans (isConj_iff.mpr ⟨a, ha⟩).symm
  have hyp : CFSG.Walter.Suzuki.Hyp A := by
    refine ⟨fun Q => ?_, fun x y hx hy => (hconj x hx).trans (hconj y hy).symm, fun x hx => ?_⟩
    · let e : (Q : Subgroup A) ≃* V := (Sylow.equiv Q P).trans (MulEquiv.subgroupCongr hPV)
      exact ⟨by rw [Nat.card_congr e.toEquiv, hV.card_four],
        by rw [Monoid.exponent_eq_of_mulEquiv e, hV.exponent_two]⟩
    · obtain ⟨c, hc⟩ := isConj_iff.mp (hconj x hx)
      have hmem : ∀ a : Subgroup.centralizer ({x} : Set A), c * (a : A) * c⁻¹ ∈ V ⊔ W := by
        intro a
        rw [← hC, Subgroup.mem_centralizer_singleton_iff, ← hc]
        have ha := Subgroup.mem_centralizer_singleton_iff.mp a.2
        calc c * (a : A) * c⁻¹ * (c * x * c⁻¹) = c * ((a : A) * x) * c⁻¹ := by group
          _ = c * (x * a) * c⁻¹ := by rw [ha]
          _ = c * x * c⁻¹ * (c * a * c⁻¹) := by group
      refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
      have h := commute_of_mem_sup hVab hWab hVW (hmem a) (hmem b)
      have h' : c * ((a : A) * b) * c⁻¹ = c * ((b : A) * a) * c⁻¹ := by
        calc c * ((a : A) * b) * c⁻¹ = c * a * c⁻¹ * (c * b * c⁻¹) := by group
          _ = c * b * c⁻¹ * (c * a * c⁻¹) := h
          _ = c * ((b : A) * a) * c⁻¹ := by group
      simpa using h'
  set O := CFSG.pPrimeCore 2 A with hOdef
  have hOodd : Odd (Nat.card O) := CFSG.Walter.Suzuki.odd_card_pPrimeCore
  set π := QuotientGroup.mk' O with hπ
  have hCX : ∀ q : A ⧸ O, q * π t = π t * q → q ∈ (V ⊔ W).map π := by
    intro q hq
    obtain ⟨c, hct, rfl⟩ := exists_preimage_centralizer hOodd ht q hq
    exact ⟨c, by rw [← hC]; exact Subgroup.mem_centralizer_singleton_iff.mpr hct, rfl⟩
  have hoddmem : ∀ z ∈ (V ⊔ W).map π, Odd (orderOf z) → z ∈ W.map π := by
    rintro z ⟨d, hd, rfl⟩ hzodd
    obtain ⟨v, hv, w, hw, rfl⟩ :=
      CFSG.Semidihedral.Principal.exists_mul_eq_of_mem_sup_of_le_centralizer hVc hd
    set m := orderOf (π (v * w)) with hm
    have hvw : Commute (π v) (π w) := by
      change π v * π w = π w * π v
      rw [← map_mul, ← map_mul, hVW v hv w hw]
    have hv2 : (π v) ^ 2 = 1 := by
      have : v ^ 2 = 1 := by
        have h := Monoid.pow_exponent_eq_one (⟨v, hv⟩ : V)
        rw [hV.exponent_two] at h
        exact congrArg Subtype.val h
      rw [← map_pow, this, map_one]
    have hpow : (π v) ^ m * (π w) ^ m = 1 := by
      rw [← hvw.mul_pow, ← map_mul, hm, pow_orderOf_eq_one]
    have hvm : (π v) ^ m = π v := by
      obtain ⟨k, hk⟩ := hzodd
      rw [hk, pow_succ, pow_mul, hv2, one_pow, one_mul]
    rw [hvm] at hpow
    have hvW : π v ∈ W.map π := by
      rw [eq_inv_of_mul_eq_one_left hpow]
      exact Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_map_of_mem π hw) _)
    rw [map_mul]
    exact Subgroup.mul_mem _ hvW ⟨w, hw, rfl⟩
  have hπWodd : Odd (Nat.card (W.map π)) := Odd.of_dvd_nat hWodd (Subgroup.card_map_dvd W π)
  have hπWelt : ∀ y ∈ W.map π, Odd (orderOf y) := fun y hy =>
    Odd.of_dvd_nat hπWodd (Subgroup.orderOf_dvd_natCard _ hy)
  have hWle : W.map π ≤ Subgroup.centralizer ({π t} : Set (A ⧸ O)) := by
    rintro _ ⟨w, hw, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hVW t htV w hw]
  suffices hbot : W.map π = ⊥ by
    rwa [Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hbot
  rcases hyp.quotient_cases with ⟨T, hTn, hT4⟩ | ⟨hsimple, h60⟩
  ·
    have hX2 := hyp.factorization_two_quotient
    have hV4 : Nat.card (V.map π) = 4 := by
      have h := hyp.card_map_sylow P
      rwa [hPV] at h
    let PT : Sylow 2 (A ⧸ O) := Sylow.ofCard T (by rw [hT4, hX2]; norm_num)
    let PV : Sylow 2 (A ⧸ O) := Sylow.ofCard (V.map π) (by rw [hV4, hX2]; norm_num)
    have hPTn : (PT : Subgroup (A ⧸ O)).Normal := by
      rw [Sylow.coe_ofCard]
      exact hTn
    have : Unique (Sylow 2 (A ⧸ O)) := Sylow.unique_of_normal PT hPTn
    have hVT : V.map π = T := by
      have h := congrArg (fun Q : Sylow 2 (A ⧸ O) => (Q : Subgroup (A ⧸ O)))
        (Subsingleton.elim PV PT)
      simpa [PV, PT, Sylow.coe_ofCard] using h
    have hVn : (V.map π).Normal := hVT ▸ hTn
    have hWn : (W.map π).Normal := by
      constructor
      intro y hy x
      apply hoddmem
      · apply hCX
        have htx : x⁻¹ * π t * x⁻¹⁻¹ ∈ V.map π := hVn.conj_mem (π t) ⟨t, htV, rfl⟩ x⁻¹
        rw [inv_inv] at htx
        obtain ⟨v, hv, hvx⟩ := htx
        obtain ⟨w, hw, rfl⟩ := hy
        have hcomm : π w * π v = π v * π w := by rw [← map_mul, ← map_mul, hVW v hv w hw]
        have hpt : π t = x * π v * x⁻¹ := by rw [hvx]; group
        rw [hpt]
        calc x * π w * x⁻¹ * (x * π v * x⁻¹) = x * (π w * π v) * x⁻¹ := by group
          _ = x * (π v * π w) * x⁻¹ := by rw [hcomm]
          _ = x * π v * x⁻¹ * (x * π w * x⁻¹) := by group
      · rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
        exact hπWelt y hy
    exact CFSG.Walter.Suzuki.eq_bot_of_odd_quotient hWn hπWodd
  ·
    obtain ⟨e⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five h60
    have ht1 : π t ≠ 1 := by
      intro h1
      have htO : t ∈ O := (QuotientGroup.eq_one_iff t).mp h1
      have h2 := Odd.of_dvd_nat hOodd (Subgroup.orderOf_dvd_natCard O htO)
      rw [ht] at h2
      exact absurd h2 (by decide)
    have ht2' : t ^ 2 = 1 := by
      rw [← ht]
      exact pow_orderOf_eq_one t
    have ht2 : (π t) ^ 2 = 1 := by rw [← map_pow, ht2', map_one]
    have hC4 : Nat.card (Subgroup.centralizer ({π t} : Set (A ⧸ O))) = 4 := by
      have hmap := CFSG.centralizer_singleton_map e (π t)
      have h := card_centralizer_alternatingGroup_five (x := e (π t))
        (fun h => ht1 (e.injective (by rw [h, map_one])))
        (by rw [← map_pow, ht2, map_one])
      rw [← hmap, Subgroup.card_map_of_injective e.injective] at h
      exact h
    have hdvd : Nat.card (W.map π) ∣ 4 := hC4 ▸ Subgroup.card_dvd_of_le hWle
    have h1 : Nat.card (W.map π) = 1 := by
      have h4 : Nat.card (W.map π) ∣ 2 ^ 2 := by norm_num; exact hdvd
      obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h4
      rw [hk'] at hπWodd
      rcases k with _ | k
      · rw [hk', pow_zero]
      · exact absurd (Nat.even_pow.mpr ⟨even_two, k.succ_ne_zero⟩)
          (Nat.not_even_iff_odd.mpr hπWodd)
    exact Subgroup.card_eq_one.mp h1

end TenFourGroup

end CFSG.BrauerLinearThree
