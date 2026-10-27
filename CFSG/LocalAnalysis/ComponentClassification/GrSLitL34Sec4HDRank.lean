module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeModel
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCorrDihedralWitness

public section

namespace CFSG.ComponentClassification.GrSLit.HeDiag

open CFSG Subgroup CFSG.Sporadic.HeldB CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

section Rank

variable {X : Type} [Group X] [Finite X] {K : Subgroup X}
variable (e : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He)

include e in
theorem inf_sup_coreActionKernel_le' {S : Subgroup X} (hSN : S ≤ normalizer (K : Set X))
    (hS2 : IsPGroup 2 S) (h1024 : Nat.card ↥(S ⊓ K) = 1024) :
    S ⊓ (K ⊔ coreActionKernel K) ≤ S ⊓ K ⊔ S ⊓ coreActionKernel K := by
  intro s hs
  obtain ⟨hsS, hsLK⟩ := mem_inf.mp hs
  have hsN : s ∈ normalizer (K : Set X) := hSN hsS
  have hsP : heN e s ∈ heP := (heN_mem_heP_iff hsN).mpr hsLK
  have h2 : IsPGroup 2 ↥(S ⊓ K) := hS2.to_le inf_le_left
  have hle : imL e (S ⊓ K) ≤ imN e S ⊓ heP := by
    intro y hy
    obtain ⟨t, ht, rfl⟩ := (mem_imL inf_le_right).mp hy
    exact mem_inf.mpr ⟨(mem_imN hSN).mpr ⟨t, (mem_inf.mp ht).1, heN_eq_heL (mem_inf.mp ht).2⟩,
      heL_mem_heP (mem_inf.mp ht).2⟩
  have heq : imL e (S ⊓ K) = imN e S ⊓ heP := by
    refine eq_of_le_of_card_ge hle ?_
    rw [card_imL inf_le_right h2, h1024]
    exact card_le_of_le_heP inf_le_right ((isPGroup_imN hSN hS2).to_le inf_le_left)
  have hs' : heN e s ∈ imL e (S ⊓ K) := by
    rw [heq]
    exact mem_inf.mpr ⟨(mem_imN hSN).mpr ⟨s, hsS, rfl⟩, hsP⟩
  obtain ⟨t, ht, hteq⟩ := (mem_imL inf_le_right).mp hs'
  obtain ⟨htS, htL⟩ := mem_inf.mp ht
  have htN : t ∈ normalizer (K : Set X) := le_normalizer htL
  have h1 : heN e (t⁻¹ * s) = 1 := by
    rw [heN_mul (inv_mem htN) hsN, heN_inv htN, heN_eq_heL htL, hteq, inv_mul_cancel]
  rw [heN_eq_one_iff (mul_mem (inv_mem htN) hsN)] at h1
  have : s = t * (t⁻¹ * s) := by group
  rw [this]
  exact mul_mem (mem_sup_left ht) (mem_sup_right (mem_inf.mpr ⟨mul_mem (inv_mem htS) hsS, h1⟩))

include e in
theorem eq_one_of_mem_coreActionKernel {S : Subgroup X} (hS2 : IsPGroup 2 S) {x : X}
    (hxS : x ∈ S) (hxK : x ∈ K) (hxk : x ∈ coreActionKernel K) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : heL e x = 1 := by
    rw [← heN_eq_heL hxK]
    exact (heN_eq_one_iff (le_normalizer hxK)).mpr hxk
  have hxO := (heL_eq_one_iff hxK).mp h1
  have hodd : Odd (orderOf x) :=
    (UnbalancedCorr.odd_card_map_pPrimeCore K).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hxO)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨x, hxS⟩
  rw [Subgroup.orderOf_mk] at hk
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact hk
  · rw [hk, pow_succ] at hodd
    exact absurd (even_iff_two_dvd.mpr (dvd_mul_left 2 _)) (Nat.not_even_iff_odd.mpr hodd)

end Rank

theorem commute_of_mem_coreActionKernel {X : Type} [Group X] [Finite X] {K S : Subgroup X}
    (hS2 : IsPGroup 2 S) {p r : X} (hpS : p ∈ S) (hpk : p ∈ coreActionKernel K) (hrS : r ∈ S)
    (hrK : r ∈ K) :
    r * p = p * r := by
  have hc : r⁻¹ * p⁻¹ * r * p ∈ (pPrimeCore 2 ↥K).map K.subtype :=
    (mem_coreActionKernel.mp hpk).2 r hrK
  have hcS : r⁻¹ * p⁻¹ * r * p ∈ S :=
    mul_mem (mul_mem (mul_mem (inv_mem hrS) (inv_mem hpS)) hrS) hpS
  have h1 : r⁻¹ * p⁻¹ * r * p = 1 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hodd : Odd (orderOf (r⁻¹ * p⁻¹ * r * p)) :=
      (UnbalancedCorr.odd_card_map_pPrimeCore K).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hc)
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hS2) ⟨_, hcS⟩
    rw [Subgroup.orderOf_mk] at hk
    rcases k with _ | k
    · rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hk
    · rw [hk, pow_succ] at hodd
      exact absurd (even_iff_two_dvd.mpr (dvd_mul_left 2 _)) (Nat.not_even_iff_odd.mpr hodd)
  calc r * p = p * r * (r⁻¹ * p⁻¹ * r * p) := by group
    _ = p * r := by rw [h1, mul_one]

theorem eight_le_card_inf_centralizer {X : Type} [Group X] [Finite X] {E : Subgroup X}
    (hE : IsElemTwo E) (h64 : Nat.card E = 64) {t : X} (htN : t ∈ normalizer (E : Set X))
    (htt : t * t = 1) : 8 ≤ Nat.card ↥(E ⊓ centralizer ({t} : Set X)) := by
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hconj : ∀ x ∈ E, t * x * t⁻¹ ∈ E := fun x hx => (mem_normalizer_iff.mp htN x).mp hx
  let φ : ↥E →* ↥E :=
    { toFun := fun x => ⟨x * (t * x * t⁻¹), mul_mem x.2 (hconj x x.2)⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun x y => Subtype.ext (by
        change (x : X) * y * (t * (x * y) * t⁻¹) = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹))
        have h1 := hE.1 _ y.2 _ (hconj x x.2)
        calc (x : X) * y * (t * (x * y) * t⁻¹) = x * (y * (t * x * t⁻¹)) * (t * y * t⁻¹) := by
              group
          _ = x * ((t * x * t⁻¹) * y) * (t * y * t⁻¹) := by rw [h1]
          _ = x * (t * x * t⁻¹) * (y * (t * y * t⁻¹)) := by group) }
  set C := E ⊓ centralizer ({t} : Set X) with hC
  have hfix : ∀ x : ↥E, (t * x * t⁻¹ = x) → (x : X) ∈ C := fun x hx =>
    mem_inf.mpr ⟨x.2, mem_centralizer_singleton_iff.mpr (by
      calc (x : X) * t = t * x * t⁻¹ * t := by rw [hx]
        _ = t * x := by group)⟩
  have hker : φ.ker.map E.subtype ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    have h1 : (x : X) * (t * x * t⁻¹) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    refine hfix x ?_
    have h2 : (x : X) * x = 1 := hE.2 _ x.2
    calc t * (x : X) * t⁻¹ = x * (x * (t * x * t⁻¹)) := by rw [← mul_assoc, h2, one_mul]
      _ = x := by rw [h1, mul_one]
  have hrange : φ.range.map E.subtype ≤ C := by
    rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
    refine hfix (φ x) ?_
    change t * ((x : X) * (t * x * t⁻¹)) * t⁻¹ = x * (t * x * t⁻¹)
    have h1 := hE.1 _ (hconj x x.2) _ x.2
    calc t * ((x : X) * (t * x * t⁻¹)) * t⁻¹ = (t * x * t⁻¹) * ((t * t) * x * (t⁻¹ * t⁻¹)) := by
          group
      _ = (t * x * t⁻¹) * x := by rw [htt, ← mul_inv_rev, htt, inv_one, one_mul, mul_one]
      _ = x * (t * x * t⁻¹) := h1
  have hcard : Nat.card ↥E = Nat.card φ.ker * Nat.card φ.range := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv, mul_comm]
  have h1 : Nat.card φ.ker ≤ Nat.card C := by
    rw [← card_map_of_injective E.subtype_injective]
    exact card_le_of_le hker
  have h2 : Nat.card φ.range ≤ Nat.card C := by
    rw [← card_map_of_injective E.subtype_injective]
    exact card_le_of_le hrange
  rw [h64] at hcard
  by_contra h
  push Not at h
  have h3 : Nat.card φ.ker * Nat.card φ.range ≤ 7 * 7 :=
    Nat.mul_le_mul (by omega) (by omega)
  omega

theorem exists_eight_fixed
    {X : Type} [Group X] [Finite X] {K : Subgroup X}
    (e : K ⧸ pPrimeCore 2 ↥K ≃* Blueprint.NativeSporadic.He) (h64 : HeldSylowElementarySixtyFour)
    (hOut : HeldOuterInvolutionRank) {S : Subgroup X} (hSN : S ≤ normalizer (K : Set X))
    (hS2 : IsPGroup 2 S) (h1024 : Nat.card ↥(S ⊓ K) = 1024) {y : X} (hyS : y ∈ S)
    (hyy : y * y = 1) :
    ∃ F : Subgroup X, F ≤ S ⊓ K ∧ F ≤ centralizer ({y} : Set X) ∧ IsElemTwo F ∧
      Nat.card F = 8 := by
  have hR2 : IsPGroup 2 ↥(S ⊓ K) := hS2.to_le inf_le_left
  have hyN : y ∈ normalizer (K : Set X) := hSN hyS
  have hyR : y ∈ normalizer ((S ⊓ K : Subgroup X) : Set X) :=
    mem_normalizer_inf (le_normalizer hyS) hyN
  by_cases hyLK : y ∈ K ⊔ coreActionKernel K
  ·
    have hyRP := inf_sup_coreActionKernel_le' e hSN hS2 h1024 (mem_inf.mpr ⟨hyS, hyLK⟩)
    have hPR : S ⊓ coreActionKernel K ≤ normalizer ((S ⊓ K : Subgroup X) : Set X) :=
      fun p hp => mem_normalizer_inf (le_normalizer (mem_inf.mp hp).1)
        (mem_coreActionKernel.mp (mem_inf.mp hp).2).1
    have hyset : y ∈ ((S ⊓ K : Subgroup X) : Set X) *
        ((S ⊓ coreActionKernel K : Subgroup X) : Set X) := by
      rw [← coe_mul_of_right_le_normalizer_left _ _ hPR]
      exact hyRP
    obtain ⟨t, ht, p, hp, rfl⟩ := hyset
    have hcomm : ∀ r ∈ S ⊓ K, r * p = p * r := fun r hr =>
      commute_of_mem_coreActionKernel hS2 (mem_inf.mp hp).1 (mem_inf.mp hp).2 (mem_inf.mp hr).1
        (mem_inf.mp hr).2
    have htt : t * t = 1 := by
      have htp := hcomm t ht
      have h1 : t * t = (p * p)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]
        calc t * t * (p * p) = t * (t * p) * p := by group
          _ = t * (p * t) * p := by rw [htp]
          _ = t * p * (t * p) := by group
          _ = 1 := hyy
      refine eq_one_of_mem_coreActionKernel e hS2 (mul_mem (mem_inf.mp ht).1 (mem_inf.mp ht).1)
        (mul_mem (mem_inf.mp ht).2 (mem_inf.mp ht).2) ?_
      rw [h1]
      exact inv_mem (mul_mem (mem_inf.mp hp).2 (mem_inf.mp hp).2)
    obtain ⟨E, hER, hRN, hEe, hE64⟩ := exists_elem_sixtyFour e h64 inf_le_right hR2 h1024
    have h8 := eight_le_card_inf_centralizer hEe hE64 (hRN ht) htt
    obtain ⟨F, hFC, hF8⟩ := exists_le_card_eight (hEe.isPGroup.to_le inf_le_left) h8
    refine ⟨F, hFC.trans (inf_le_left.trans hER), fun f hf => ?_,
      hEe.mono (hFC.trans inf_le_left), hF8⟩
    have hfR : f ∈ S ⊓ K := hER (mem_inf.mp (hFC hf)).1
    have hft := mem_centralizer_singleton_iff.mp (mem_inf.mp (hFC hf)).2
    rw [mem_centralizer_singleton_iff]
    calc f * (t * p) = f * t * p := by group
      _ = t * f * p := by rw [hft]
      _ = t * (f * p) := by group
      _ = t * (p * f) := by rw [hcomm f hfR]
      _ = t * p * f := by group
  · obtain ⟨F, hFR, hFy, -, hFe, hF8⟩ := exists_outer_eight e hOut inf_le_right hR2 h1024 hyN hyR
      hyLK (by rw [hyy]; exact one_mem _) (one_mem _) (mul_one 1) (by rw [one_mul, mul_one])
    exact ⟨F, hFR, hFy, hFe, hF8⟩

end CFSG.ComponentClassification.GrSLit.HeDiag
