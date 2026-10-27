module

public import CFSG.LocalAnalysis.ABGTheoremB.IV1
public import CFSG.LocalAnalysis.ABGTheoremB.V4Defs

public section

namespace CFSG.ABGTheoremB.V56

open CFSG.ABGLocalTools
open scoped Pointwise

variable {G : Type*} [Group G]

theorem coe_sup_of_permutable {A B : Subgroup G} (h : (A : Set G) * B = B * A) :
    ((A ⊔ B : Subgroup G) : Set G) = A * B := by
  let S : Subgroup G :=
    { carrier := (A : Set G) * B
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        have hba : b * a' ∈ (B : Set G) * A := ⟨b, hb, a', ha', rfl⟩
        rw [← h] at hba
        obtain ⟨a'', ha'', b'', hb'', he⟩ := hba
        refine ⟨a * a'', A.mul_mem ha ha'', b'' * b', B.mul_mem hb'' hb', ?_⟩
        change a * a'' * (b'' * b') = a * b * (a' * b')
        rw [show a * b * (a' * b') = a * (b * a') * b' by group, ← he]
        group
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, mul_one 1⟩
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        have hba : b⁻¹ * a⁻¹ ∈ (B : Set G) * A := ⟨b⁻¹, B.inv_mem hb, a⁻¹, A.inv_mem ha, rfl⟩
        rw [← h] at hba
        change (a * b)⁻¹ ∈ (A : Set G) * B
        rwa [mul_inv_rev] }
  have hAS : A ≤ S := fun a ha => ⟨a, ha, 1, B.one_mem, mul_one a⟩
  have hBS : B ≤ S := fun b hb => ⟨1, A.one_mem, b, hb, one_mul b⟩
  apply Set.Subset.antisymm
  · exact SetLike.coe_subset_coe.mpr (sup_le hAS hBS)
  · rintro _ ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem permutable_of_le_normalizer {A B : Subgroup G}
    (h : B ≤ Subgroup.normalizer (A : Set G)) : (A : Set G) * B = B * A := by
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B h,
    ← Subgroup.coe_mul_of_left_le_normalizer_right B A h, sup_comm]

theorem card_sup_of_permutable [Finite G] {A B : Subgroup G} (h : (A : Set G) * B = B * A)
    (hAB : A ⊓ B = ⊥) : Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  have hcoe := coe_sup_of_permutable h
  let f : A × B → (A ⊔ B : Subgroup G) := fun x =>
    ⟨(x.1 : G) * x.2, Subgroup.mul_mem_sup x.1.2 x.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ he
      have he' : (a : G) * b = a' * b' := congrArg Subtype.val he
      have hmem : (a' : G)⁻¹ * a ∈ A ⊓ B := by
        refine ⟨A.mul_mem (A.inv_mem a'.2) a.2, ?_⟩
        have e : (a' : G)⁻¹ * a = b' * (b : G)⁻¹ := by
          calc (a' : G)⁻¹ * a = (a' : G)⁻¹ * (a * b) * (b : G)⁻¹ := by group
            _ = (a' : G)⁻¹ * (a' * b') * (b : G)⁻¹ := by rw [he']
            _ = b' * (b : G)⁻¹ := by group
        rw [e]
        exact B.mul_mem b'.2 (B.inv_mem b.2)
      rw [hAB, Subgroup.mem_bot] at hmem
      have ha : (a : G) = a' := (inv_mul_eq_one.mp hmem).symm
      have hb : (b : G) = b' := by
        rw [ha] at he'
        exact mul_left_cancel he'
      rw [Subtype.ext ha, Subtype.ext hb]
    · rintro ⟨x, hx⟩
      have hx' : x ∈ (A : Set G) * B := by
        rw [← hcoe]
        exact hx
      obtain ⟨a, ha, b, hb, rfl⟩ := hx'
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

theorem mul_inter_of_le {A B K : Subgroup G} (hBK : B ≤ K) :
    ((A : Set G) * B) ∩ K = ((A ⊓ K : Subgroup G) : Set G) * B := by
  ext x
  constructor
  · rintro ⟨⟨a, ha, b, hb, rfl⟩, hx⟩
    refine ⟨a, ⟨ha, ?_⟩, b, hb, rfl⟩
    have := K.mul_mem hx (K.inv_mem (hBK hb))
    simpa using this
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact ⟨⟨a, ha.1, b, hb, rfl⟩, K.mul_mem ha.2 (hBK hb)⟩

theorem mul_inter_of_le' {A B K : Subgroup G} (hBK : B ≤ K) :
    ((B : Set G) * A) ∩ K = (B : Set G) * ((A ⊓ K : Subgroup G) : Set G) := by
  ext x
  constructor
  · rintro ⟨⟨b, hb, a, ha, rfl⟩, hx⟩
    refine ⟨b, hb, a, ⟨ha, ?_⟩, rfl⟩
    have := K.mul_mem (K.inv_mem (hBK hb)) hx
    simpa using this
  · rintro ⟨b, hb, a, ha, rfl⟩
    exact ⟨⟨b, hb, a, ha.1, rfl⟩, K.mul_mem (hBK hb) ha.2⟩

theorem permutable_inf_of_le {A B H : Subgroup G} (hBH : B ≤ H)
    (h : (A : Set G) * B = B * A) :
    ((A ⊓ H : Subgroup G) : Set G) * B = B * ((A ⊓ H : Subgroup G) : Set G) := by
  rw [← mul_inter_of_le hBH, ← mul_inter_of_le' hBH, h]

theorem permutable_sup_of_le_normalizer {P M B : Subgroup G}
    (hPM : P ≤ Subgroup.normalizer (M : Set G)) (hBM : B ≤ Subgroup.normalizer (M : Set G))
    (h : (P : Set G) * B = B * P) :
    ((P ⊔ M : Subgroup G) : Set G) * B = B * ((P ⊔ M : Subgroup G) : Set G) := by
  rw [Subgroup.coe_mul_of_left_le_normalizer_right P M hPM]
  have hMB : (M : Set G) * B = B * M := permutable_of_le_normalizer hBM
  rw [mul_assoc, hMB, ← mul_assoc, h, mul_assoc]

theorem inf_eq_bot_of_coprime {A B : Subgroup G} (h : Nat.Coprime (Nat.card A) (Nat.card B)) :
    A ⊓ B = ⊥ :=
  (Subgroup.disjoint_of_coprime_natCard h).eq_bot

theorem coprime_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) {A B : Subgroup G}
    (hA : IsPGroup p A) (hB : ¬ p ∣ Nat.card B) : Nat.Coprime (Nat.card A) (Nat.card B) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hA
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hB)

theorem card_dvd_of_isPGroup_of_dvd_mul [Finite G] {p : ℕ} (hp : p.Prime) {Y : Subgroup G}
    (hY : IsPGroup p Y) {n m : ℕ} (hm : ¬ p ∣ m) (h : Nat.card Y ∣ n * m) : Nat.card Y ∣ n := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
  rw [hk] at h ⊢
  exact (Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).mpr hm)).dvd_of_dvd_mul_right h

theorem odd_card_of_isPGroup [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup G}
    (hY : IsPGroup p Y) : Odd (Nat.card Y) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hY
  rw [hk]
  exact (hp.eq_two_or_odd'.resolve_left hp2).pow

theorem inf_eq_bot_of_two_of_odd [Finite G] {A B : Subgroup G} (hA : IsPGroup 2 A)
    (hB : Odd (Nat.card B)) : A ⊓ B = ⊥ :=
  inf_eq_bot_of_coprime (coprime_card_of_isPGroup Nat.prime_two hA hB.not_two_dvd_nat)

theorem inf_eq_bot_of_isPGroup_of_two [Finite G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {A B : Subgroup G} (hA : IsPGroup p A) (hB : IsPGroup 2 B) : A ⊓ B = ⊥ := by
  rw [inf_comm]
  exact inf_eq_bot_of_two_of_odd hB (odd_card_of_isPGroup hp hp2 hA)

theorem ne_bot_of_prime_dvd_card {p : ℕ} (hp : p.Prime) {K : Subgroup G}
    (h : p ∣ Nat.card K) : K ≠ ⊥ := by
  rintro rfl
  rw [Subgroup.card_bot] at h
  exact hp.one_lt.ne' (Nat.dvd_one.mp h)

theorem ne_bot_of_isSylowOf [Finite G] {p : ℕ} (hp : p.Prime) {P K : Subgroup G}
    (hP : IsSylowOf p P K) (hdvd : p ∣ Nat.card K) : P ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  intro h
  have hc := hP.card_eq
  rw [h, Subgroup.card_bot] at hc
  have hk : 1 ≤ (Nat.card K).factorization p :=
    (hp.dvd_iff_one_le_factorization Nat.card_pos.ne').mp hdvd
  have : 1 < p ^ (Nat.card K).factorization p := Nat.one_lt_pow (by omega) hp.one_lt
  omega

theorem le_centralizer_of_le_normalizer {A B : Subgroup G}
    (hAB : A ≤ Subgroup.normalizer (B : Set G)) (hBA : B ≤ Subgroup.normalizer (A : Set G))
    (h : A ⊓ B = ⊥) : A ≤ Subgroup.centralizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ B :=
    B.mul_mem ((Subgroup.mem_normalizer_iff.mp (hAB ha) b).mp hb) (B.inv_mem hb)
  have h2 : a * b * a⁻¹ * b⁻¹ ∈ A := by
    have := A.mul_mem ha ((Subgroup.mem_normalizer_iff.mp (hBA hb) a⁻¹).mp (A.inv_mem ha))
    simpa [mul_assoc] using this
  have h3 : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := ⟨h2, h1⟩
  rw [h, Subgroup.mem_bot] at h3
  have e : a * b = b * a := by
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  exact e.symm

section PPrime

variable [Finite G] {p : ℕ} {U W : Subgroup G}

theorem card_sup_pPrime (hp : p.Prime) (hU : IsPGroup p U) (hW : ¬ p ∣ Nat.card W)
    (hUW : (U : Set G) * W = W * U) : Nat.card (U ⊔ W : Subgroup G) = Nat.card U * Nat.card W :=
  card_sup_of_permutable hUW (inf_eq_bot_of_coprime (coprime_card_of_isPGroup hp hU hW))

theorem card_dvd_of_le_sup_pPrime (hp : p.Prime) (hU : IsPGroup p U) (hW : ¬ p ∣ Nat.card W)
    (hUW : (U : Set G) * W = W * U) {Y : Subgroup G} (hY : IsPGroup p Y) (hYX : Y ≤ U ⊔ W) :
    Nat.card Y ∣ Nat.card U := by
  apply card_dvd_of_isPGroup_of_dvd_mul hp hY hW
  rw [← card_sup_pPrime hp hU hW hUW]
  exact Subgroup.card_dvd_of_le hYX

theorem eq_of_le_sup_pPrime (hp : p.Prime) (hU : IsPGroup p U) (hW : ¬ p ∣ Nat.card W)
    (hUW : (U : Set G) * W = W * U) {Y : Subgroup G} (hY : IsPGroup p Y) (hUY : U ≤ Y)
    (hYX : Y ≤ U ⊔ W) : Y = U :=
  (Subgroup.eq_of_le_of_card_ge hUY
    (Nat.le_of_dvd Nat.card_pos (card_dvd_of_le_sup_pPrime hp hU hW hUW hY hYX))).symm

theorem isSylowOf_sup_pPrime (hp : p.Prime) (hU : IsPGroup p U) (hW : ¬ p ∣ Nat.card W)
    (hUW : (U : Set G) * W = W * U) : IsSylowOf p U (U ⊔ W) := by
  have : Fact p.Prime := ⟨hp⟩
  refine isSylowOf_iff.mpr ⟨le_sup_left, hU, ?_⟩
  have h := Subgroup.relIndex_mul_card U (U ⊔ W)
  rw [inf_eq_left.mpr le_sup_left, card_sup_pPrime hp hU hW hUW] at h
  have hU0 : 0 < Nat.card U := Nat.card_pos
  have : U.relIndex (U ⊔ W) = Nat.card W := by
    apply Nat.eq_of_mul_eq_mul_right hU0
    rw [h, mul_comm]
  rw [this]
  exact hW

end PPrime

theorem isPGroup_pCoreIn (p : ℕ) (H : Subgroup G) : IsPGroup p (pCoreIn p H) :=
  IsPGroup.map CFSG.pCore_isPGroup H.subtype

theorem le_normalizer_pCoreIn (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pCoreIn p H : Set G) :=
  le_normalizer_map_subtype H (CFSG.pCore p H)

theorem le_normalizer_pPrimeCoreIn (p : ℕ) (H : Subgroup G) :
    H ≤ Subgroup.normalizer (pPrimeCoreIn p H : Set G) :=
  le_normalizer_map_subtype H (CFSG.pPrimeCore p H)

theorem coprime_card_pPrimeCoreIn [Finite G] {p : ℕ} (hp : p.Prime) (H : Subgroup G) :
    Nat.Coprime p (Nat.card (pPrimeCoreIn p H)) := by
  have : Fact p.Prime := ⟨hp⟩
  rw [pPrimeCoreIn, Subgroup.card_map_of_injective H.subtype_injective]
  exact CFSG.pPrimeCore_coprime_card

theorem le_pCoreIn {p : ℕ} {X H : Subgroup G} (hXH : X ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (X : Set G)) (hX : IsPGroup p X) : X ≤ pCoreIn p H := by
  have hnormal : (X.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (Subgroup.mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hle : X.subgroupOf H ≤ CFSG.pCore p H :=
    le_sSup ⟨hnormal, hX.comap_subtype⟩
  intro x hx
  exact ⟨⟨x, hXH hx⟩, hle hx, rfl⟩

theorem le_pPrimeCoreIn {p : ℕ} {X H : Subgroup G} (hXH : X ≤ H)
    (hnorm : H ≤ Subgroup.normalizer (X : Set G)) (hX : Nat.Coprime p (Nat.card X)) :
    X ≤ pPrimeCoreIn p H := by
  have hnormal : (X.subgroupOf H).Normal := by
    constructor
    intro a ha h
    exact (Subgroup.mem_normalizer_iff.mp (hnorm h.property) a).mp ha
  have hcard : Nat.card (X.subgroupOf H) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv
  have hle : X.subgroupOf H ≤ CFSG.pPrimeCore p H :=
    le_sSup ⟨hnormal, by rw [hcard]; exact hX⟩
  intro x hx
  exact ⟨⟨x, hXH hx⟩, hle hx, rfl⟩

theorem pPrimeCoreIn_eq_bot_iff {p : ℕ} {H : Subgroup G} :
    pPrimeCoreIn p H = ⊥ ↔ CFSG.pPrimeCore p H = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective

theorem pPrimeCoreIn_le_oddCoreIn {p : ℕ} {K : Subgroup G}
    (h : PConstrainedWithin p K (CFSG.oddCore K)) : pPrimeCoreIn p K ≤ oddCoreIn K :=
  Subgroup.map_mono (pPrimeCore_le_Op_p'p.trans h.1)

theorem pPrimeCoreIn_le_solvRadIn {p : ℕ} {K : Subgroup G}
    (h : PConstrainedWithin p K (CFSG.solvableRadical K)) : pPrimeCoreIn p K ≤ solvRadIn K :=
  Subgroup.map_mono (pPrimeCore_le_Op_p'p.trans h.1)

theorem inf_pPrimeCoreIn_le_of_sup_eq [Finite G] {p : ℕ} (hp : p.Prime) {K H : Subgroup G}
    (hKH : pPrimeCoreIn p K ⊔ (K ⊓ H) = K) : K ⊓ pPrimeCoreIn p H ≤ pPrimeCoreIn p K := by
  set A := K ⊓ pPrimeCoreIn p H
  set B := pPrimeCoreIn p K
  have hBK : B ≤ K := pPrimeCoreIn_le p K
  have hKB : K ≤ Subgroup.normalizer (B : Set G) := le_normalizer_pPrimeCoreIn p K
  have hAK : A ≤ K := inf_le_left
  have hAB : A ≤ Subgroup.normalizer (B : Set G) := hAK.trans hKB
  have hsup : A ⊔ B ≤ K := sup_le hAK hBK
  have hnorm : K ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    rw [← hKH]
    refine sup_le (fun b hb => ?_) ?_
    · exact Subgroup.le_normalizer ((le_sup_right : B ≤ A ⊔ B) hb)
    · have h1 : K ⊓ H ≤ Subgroup.normalizer (A : Set G) := by
        refine (le_inf (inf_le_left.trans Subgroup.le_normalizer)
          (inf_le_right.trans (le_normalizer_pPrimeCoreIn p H))).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      exact (le_inf h1 (inf_le_left.trans hKB)).trans
        (normalizer_inf_normalizer_le_normalizer_sup A B)
  have hcop : Nat.Coprime p (Nat.card (A ⊔ B : Subgroup G)) := by
    have hcA : Nat.Coprime p (Nat.card A) :=
      Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
        (coprime_card_pPrimeCoreIn hp H)
    have hcB : Nat.Coprime p (Nat.card B) := coprime_card_pPrimeCoreIn hp K
    have h := card_sup_mul_card_inf_of_le_normalizer hAB
    rw [sup_comm] at h
    have hdvd : Nat.card (A ⊔ B : Subgroup G) ∣ Nat.card B * Nat.card A :=
      Dvd.intro _ h
    exact Nat.Coprime.coprime_dvd_right hdvd (Nat.Coprime.mul_right hcB hcA)
  exact le_sup_left.trans (le_pPrimeCoreIn hsup hnorm hcop)

section PPrimeCore

variable [Finite G] {p : ℕ} {U V W : Subgroup G}

theorem pPrimeCoreIn_sup_le (hp : p.Prime) (hU : IsPGroup p U) (hW : ¬ p ∣ Nat.card W)
    (hUW : (U : Set G) * W = W * U) : pPrimeCoreIn p (U ⊔ W) ≤ W := by
  set Y := pPrimeCoreIn p (U ⊔ W)
  have hYX : Y ≤ U ⊔ W := pPrimeCoreIn_le p _
  have hWY : W ≤ Subgroup.normalizer (Y : Set G) :=
    le_sup_right.trans (le_normalizer_pPrimeCoreIn p _)
  have hcY : Nat.Coprime p (Nat.card Y) := coprime_card_pPrimeCoreIn hp _
  have hcW : Nat.Coprime p (Nat.card W) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hW
  have h1 := card_sup_mul_card_inf_of_le_normalizer hWY
  have hcYW : Nat.Coprime p (Nat.card (Y ⊔ W : Subgroup G)) :=
    Nat.Coprime.coprime_dvd_right (Dvd.intro _ h1) (Nat.Coprime.mul_right hcY hcW)
  have hdvd : Nat.card (Y ⊔ W : Subgroup G) ∣ Nat.card U * Nat.card W := by
    rw [← card_sup_pPrime hp hU hW hUW]
    exact Subgroup.card_dvd_of_le (sup_le hYX le_sup_right)
  have hcU : Nat.Coprime (Nat.card (Y ⊔ W : Subgroup G)) (Nat.card U) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hU
    rw [hk]
    exact Nat.Coprime.pow_right k hcYW.symm
  have hdvd' : Nat.card (Y ⊔ W : Subgroup G) ∣ Nat.card W := hcU.dvd_of_dvd_mul_left hdvd
  have heq : Y ⊔ W = W :=
    (Subgroup.eq_of_le_of_card_ge le_sup_right (Nat.le_of_dvd Nat.card_pos hdvd')).symm
  rw [← heq]
  exact le_sup_left

theorem pPrimeCoreIn_sup_eq_bot_of_le (hp : p.Prime) (hU : IsPGroup p U)
    (hW : ¬ p ∣ Nat.card W) (hUW : (U : Set G) * W = W * U) (hVU : V ≤ U)
    (hV : pPrimeCoreIn p (V ⊔ W) = ⊥) : pPrimeCoreIn p (U ⊔ W) = ⊥ := by
  have hle := pPrimeCoreIn_sup_le hp hU hW hUW
  have h : pPrimeCoreIn p (U ⊔ W) ≤ pPrimeCoreIn p (V ⊔ W) :=
    le_pPrimeCoreIn (hle.trans le_sup_right)
      ((sup_le_sup_right hVU W).trans (le_normalizer_pPrimeCoreIn p _))
      (coprime_card_pPrimeCoreIn hp _)
  rw [hV] at h
  exact le_bot_iff.mp h

end PPrimeCore

private theorem pow_mul_mem {M : Subgroup G} {z : G} (hz : z ∈ Subgroup.normalizer (M : Set G))
    {m : G} (hm : m ∈ M) : ∀ k : ℕ, ∃ m' ∈ M, (m * z) ^ k = m' * z ^ k := by
  intro k
  induction k with
  | zero => exact ⟨1, M.one_mem, by simp⟩
  | succ k ih =>
    obtain ⟨m', hm', he⟩ := ih
    have hzk : z ^ k ∈ Subgroup.normalizer (M : Set G) := Subgroup.pow_mem _ hz k
    have hconj : z ^ k * m * (z ^ k)⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.mp hzk m).mp hm
    refine ⟨m' * (z ^ k * m * (z ^ k)⁻¹), M.mul_mem hm' hconj, ?_⟩
    rw [pow_succ, he, pow_succ]
    group

theorem le_normalizer_inf_of_permutable [Finite G] {X Y M : Subgroup G}
    (hXY : (X : Set G) * Y = Y * X) (hcop : Nat.Coprime (Nat.card X) (Nat.card Y))
    (hXM : X ≤ Subgroup.normalizer (M : Set G)) (hXM1 : X ⊓ M = ⊥) :
    X ≤ Subgroup.normalizer ((Y ⊓ M : Subgroup G) : Set G) := by
  have key : ∀ x ∈ X, ∀ y ∈ Y ⊓ M, x * y * x⁻¹ ∈ Y ⊓ M := by
    intro x hx y hy
    have hmem : x * y ∈ (Y : Set G) * X := by
      rw [← hXY]
      exact ⟨x, hx, y, hy.1, rfl⟩
    obtain ⟨y', hy', x', hx', hxy⟩ := hmem
    change y' * x' = x * y at hxy
    set z : G := x' * x⁻¹ with hz
    have hzX : z ∈ X := X.mul_mem hx' (X.inv_mem hx)
    set m : G := x * y * x⁻¹ with hm
    have hmM : m ∈ M := (Subgroup.mem_normalizer_iff.mp (hXM hx) y).mp hy.2
    have hy'e : y' = m * z⁻¹ := by
      rw [hm, hz]
      have : y' = x * y * x'⁻¹ := by rw [← hxy]; group
      rw [this]
      group
    have hzinvN : z⁻¹ ∈ Subgroup.normalizer (M : Set G) := hXM (X.inv_mem hzX)
    obtain ⟨m', hm', hpow⟩ := pow_mul_mem hzinvN hmM (Nat.card Y)
    have hy'pow : y' ^ Nat.card Y = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard Y hy')
    rw [hy'e, hpow] at hy'pow
    have hzpow : z⁻¹ ^ Nat.card Y ∈ X ⊓ M := by
      refine ⟨Subgroup.pow_mem _ (X.inv_mem hzX) _, ?_⟩
      rw [← mul_eq_one_iff_inv_eq.mp hy'pow]
      exact M.inv_mem hm'
    rw [hXM1, Subgroup.mem_bot] at hzpow
    have hz1 : z⁻¹ = 1 := by
      have h1 : orderOf z⁻¹ ∣ Nat.card Y := orderOf_dvd_of_pow_eq_one hzpow
      have h2 : orderOf z⁻¹ ∣ Nat.card X := Subgroup.orderOf_dvd_natCard X (X.inv_mem hzX)
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h2 h1)
    have hxx' : x' = x := by
      have h1 : z = 1 := inv_eq_one.mp hz1
      rw [hz] at h1
      exact mul_inv_eq_one.mp h1
    have hconj : m = y' := by
      rw [hm]
      rw [hxx'] at hxy
      rw [← hxy]
      group
    exact ⟨by rw [hconj]; exact hy', hmM⟩
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact key x hx y
  · intro hy
    have := key x⁻¹ (X.inv_mem hx) _ hy
    simpa [mul_assoc] using this

theorem lt_inf_normalizer_of_lt [Finite G] {p : ℕ} (hp : p.Prime) {U V : Subgroup G}
    (hV : IsPGroup p V) (hUV : U < V) : U < V ⊓ Subgroup.normalizer (U : Set G) := by
  have : Fact p.Prime := ⟨hp⟩
  have : Group.IsNilpotent V := hV.isNilpotent
  have hlt : U.subgroupOf V < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [Subgroup.subgroupOf_eq_top] at h
    exact hUV.ne (le_antisymm hUV.le h)
  obtain ⟨y, hyN, hyU⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  rw [← Subgroup.subgroupOf_normalizer_eq hUV.le, Subgroup.mem_subgroupOf] at hyN
  rw [Subgroup.mem_subgroupOf] at hyU
  exact IsConcreteLE.lt_iff_le_and_exists.mpr
    ⟨le_inf hUV.le Subgroup.le_normalizer, (y : G), Subgroup.mem_inf.mpr ⟨y.2, hyN⟩, hyU⟩

theorem exists_mem_maximals_ge [Finite G] {𝓢 : Set (Subgroup G)} {U : Subgroup G}
    (hU : U ∈ 𝓢) : ∃ M ∈ maximals 𝓢, U ≤ M := by
  obtain ⟨M, hUM, hM⟩ := Finite.exists_le_maximal (p := fun X => X ∈ 𝓢) hU
  exact ⟨M, ⟨hM.1, fun R hR hMR => le_antisymm (hM.2 hR hMR) hMR⟩, hUM⟩

theorem mem_map_conj_iff {K : Subgroup G} {g y : G} :
    y ∈ K.map (MulAut.conj g).toMonoidHom ↔ g⁻¹ * y * g ∈ K := by
  rw [Subgroup.mem_map_equiv, MulAut.conj_symm_apply]

theorem map_conj_mul (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext y
  simp

theorem map_conj_inv_map_conj (K : Subgroup G) (g : G) :
    (K.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = K := by
  rw [← map_conj_mul, inv_mul_cancel, map_conj_one]

theorem map_conj_le_map_conj_iff {A B : Subgroup G} (g : G) :
    A.map (MulAut.conj g).toMonoidHom ≤ B.map (MulAut.conj g).toMonoidHom ↔ A ≤ B :=
  Subgroup.map_le_map_iff_of_injective (MulAut.conj g).injective

theorem card_map_conj (A : Subgroup G) (g : G) :
    Nat.card (A.map (MulAut.conj g).toMonoidHom) = Nat.card A :=
  Subgroup.card_map_of_injective (MulAut.conj g).injective

theorem normalizer_map_conj (A : Subgroup G) (g : G) :
    Subgroup.normalizer ((A.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) =
      (Subgroup.normalizer (A : Set G)).map (MulAut.conj g).toMonoidHom :=
  (Subgroup.map_equiv_normalizer_eq A (MulAut.conj g)).symm

theorem map_conj_mem_signalizersPerm {D W : Subgroup G} {p : ℕ} {c : G}
    (hcD : c ∈ Subgroup.centralizer (D : Set G)) (hcW : c ∈ Subgroup.normalizer (W : Set G))
    {X : Subgroup G} (hX : X ∈ signalizersPerm ⊤ D W p) :
    X.map (MulAut.conj c).toMonoidHom ∈ signalizersPerm ⊤ D W p := by
  obtain ⟨⟨-, hXp, hDX, hXD⟩, hXW⟩ := hX
  have hcd : ∀ d ∈ D, c⁻¹ * d * c = d := by
    intro d hd
    have h := (Subgroup.mem_centralizer_iff.mp hcD) d hd
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  refine ⟨⟨le_top, hXp.map _, ?_, ?_⟩, ?_⟩
  · intro d hd
    rw [normalizer_map_conj, mem_map_conj_iff, hcd d hd]
    exact hDX hd
  · rw [eq_bot_iff]
    intro y hy
    obtain ⟨hyX, hyD⟩ := Subgroup.mem_inf.mp hy
    rw [mem_map_conj_iff, hcd y hyD] at hyX
    have : y ∈ X ⊓ D := ⟨hyX, hyD⟩
    rwa [hXD] at this
  · have hWc : W.map (MulAut.conj c).toMonoidHom = W := by
      ext y
      rw [mem_map_conj_iff]
      have := Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hcW) y
      rw [inv_inv] at this
      exact this.symm
    rw [← hWc]
    simp only [Subgroup.coe_map]
    rw [← Set.image_mul, hXW, Set.image_mul]

theorem map_conj_mem_maximals {D W : Subgroup G} {p : ℕ} {c : G}
    (hcD : c ∈ Subgroup.centralizer (D : Set G)) (hcW : c ∈ Subgroup.normalizer (W : Set G))
    {X : Subgroup G} (hX : X ∈ maximals (signalizersPerm ⊤ D W p)) :
    X.map (MulAut.conj c).toMonoidHom ∈ maximals (signalizersPerm ⊤ D W p) := by
  refine ⟨map_conj_mem_signalizersPerm hcD hcW hX.1, fun R hR hXR => ?_⟩
  have hR' := map_conj_mem_signalizersPerm (c := c⁻¹) (Subgroup.inv_mem _ hcD)
    (Subgroup.inv_mem _ hcW) hR
  have hle : X ≤ R.map (MulAut.conj c⁻¹).toMonoidHom := by
    rw [← map_conj_le_map_conj_iff c, ← map_conj_mul, mul_inv_cancel, map_conj_one]
    exact hXR
  have h := hX.2 _ hR' hle
  rw [← h, ← map_conj_mul, mul_inv_cancel, map_conj_one]

theorem le_normalizer_of_conj_mem {A X : Subgroup G}
    (h : ∀ a ∈ A, ∀ y ∈ X, a * y * a⁻¹ ∈ X) : A ≤ Subgroup.normalizer (X : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨h a ha y, fun hy => ?_⟩
  have := h a⁻¹ (A.inv_mem ha) _ hy
  simpa [mul_assoc] using this

theorem normalizer_le_normalizer_of_characteristic {P Q : Subgroup G} (hQP : Q ≤ P)
    (hQ : (Q.subgroupOf P).Characteristic) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (Q : Set G) := by
  apply le_normalizer_of_conj_mem
  intro g hg y hy
  let φ := Subgroup.normalizerMonoidHom P ⟨g, hg⟩
  have hfix := hQ.fixed φ
  have hmem : (⟨y, hQP hy⟩ : P) ∈ (Q.subgroupOf P).comap φ.toMonoidHom := by
    rw [hfix]
    exact hy
  exact hmem

section Constraint

variable [Finite G] {K Z : Subgroup G}

omit [Finite G] in
private theorem relIndex_dvd_card_of_le_solvRadIn (hS : solvRadIn K = oddCoreIn K ⊔ Z)
    (hZK : Z ≤ K) {Y : Subgroup G} (hY : Y ≤ solvRadIn K) :
    (oddCoreIn K).relIndex Y ∣ Nat.card Z := by
  set O := oddCoreIn K
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hYK : Y ≤ K := hY.trans (solvRadIn_le K)
  rw [← relIndex_sup_right_of_le_normalizer (hYK.trans hKO)]
  have hle : Y ⊔ O ≤ O ⊔ Z := sup_le (hS ▸ hY) le_sup_left
  have h1 := Subgroup.relIndex_mul_relIndex O (Y ⊔ O) (O ⊔ Z) le_sup_right hle
  have h2 : O.relIndex (O ⊔ Z) = O.relIndex Z := by
    rw [sup_comm]
    exact relIndex_sup_right_of_le_normalizer (hZK.trans hKO)
  rw [h2] at h1
  exact (Dvd.intro _ h1).trans (Subgroup.relIndex_dvd_card O Z)

theorem le_oddCoreIn_of_le_solvRadIn (hS : solvRadIn K = oddCoreIn K ⊔ Z)
    (hZ : IsPGroup 2 Z) (hZK : Z ≤ K) {Y : Subgroup G} (hY : Y ≤ solvRadIn K)
    (hYodd : Odd (Nat.card Y)) : Y ≤ oddCoreIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 := relIndex_dvd_card_of_le_solvRadIn hS hZK hY
  have h2 : (oddCoreIn K).relIndex Y ∣ Nat.card Y := Subgroup.relIndex_dvd_card _ _
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
  rw [hk] at h1
  have hcop : Nat.Coprime (2 ^ k) (Nat.card Y) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hYodd)
  exact Subgroup.relIndex_eq_one.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem inf_solvRadIn_eq_bot (hS : solvRadIn K = oddCoreIn K ⊔ Z) (hZ : IsPGroup 2 Z)
    (hZK : Z ≤ K) {W : Subgroup G} (hW : Odd (Nat.card W)) (hWO : W ⊓ oddCoreIn K = ⊥) :
    W ⊓ solvRadIn K = ⊥ := by
  have hodd : Odd (Nat.card (W ⊓ solvRadIn K : Subgroup G)) :=
    hW.of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  have hle := le_oddCoreIn_of_le_solvRadIn hS hZ hZK inf_le_right hodd
  rw [eq_bot_iff, ← hWO]
  exact le_inf inf_le_left hle

theorem inf_centralizer_le_solvRadIn {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {F : Subgroup G}
    (hcon : PConstrainedWithin p K (CFSG.solvableRadical K))
    (hS : solvRadIn K = oddCoreIn K ⊔ Z) (hZ : IsPGroup 2 Z) (hZK : Z ≤ K)
    (hF : IsSylowOf p F (oddCoreIn K)) :
    K ⊓ Subgroup.centralizer (F : Set G) ≤ solvRadIn K := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set E : Subgroup G := (CFSG.Op_p'p p K).map K.subtype with hE
  set O := oddCoreIn K
  have hEK : E ≤ K := Subgroup.map_subtype_le _
  have hES : E ≤ solvRadIn K := Subgroup.map_mono hcon.1
  have hKE : K ≤ Subgroup.normalizer (E : Set G) := le_normalizer_map_subtype K _
  have hKO : K ≤ Subgroup.normalizer (O : Set G) := le_normalizer_oddCoreIn K
  have hOK : O ≤ K := oddCoreIn_le K
  have hOE₀ : O ≤ Subgroup.normalizer ((E ⊓ O : Subgroup G) : Set G) :=
    (le_inf (hOK.trans hKE) (hOK.trans hKO)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hF₀ : IsSylowOf p (F ⊓ (E ⊓ O)) (E ⊓ O) := hF.inf_of_le_normalizer inf_le_right hOE₀
  have hidx : ¬ p ∣ (E ⊓ O).relIndex E := by
    rw [Subgroup.inf_relIndex_left]
    have h1 := relIndex_dvd_card_of_le_solvRadIn hS hZK hES
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ
    rw [hk] at h1
    intro hpd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (hpd.trans h1)))
  have hFE : IsSylowOf p (F ⊓ (E ⊓ O)) E := by
    rw [isSylowOf_iff] at hF₀ ⊢
    refine ⟨hF₀.1.trans inf_le_left, hF₀.2.1, ?_⟩
    rw [← Subgroup.relIndex_mul_relIndex (F ⊓ (E ⊓ O)) (E ⊓ O) E hF₀.1 inf_le_left]
    exact Nat.Prime.not_dvd_mul hp hF₀.2.2 hidx
  set A : Subgroup K := (F ⊓ (E ⊓ O)).subgroupOf K
  have hAmap : A.map K.subtype = F ⊓ (E ⊓ O) := by
    rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hF₀.le.trans (inf_le_left.trans hEK))]
  have hA : IsSylowOf p A (CFSG.Op_p'p p K) := by
    rw [← isSylowOf_map_subtype_iff K, hAmap]
    exact hFE
  have hC := hcon.2 A hA
  intro g hg
  obtain ⟨hgK, hgC⟩ := hg
  have hmem : (⟨g, hgK⟩ : K) ∈ Subgroup.centralizer (A : Set K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    apply Subtype.ext
    have ha' : (a : G) ∈ F := (Subgroup.mem_subgroupOf.mp ha).1
    exact (Subgroup.mem_centralizer_iff.mp hgC) a ha'
  exact hES ⟨⟨g, hgK⟩, hC hmem, rfl⟩

end Constraint

section FamilyW

variable [Finite G] {σ : Setting G} {J W : Subgroup G}

theorem le_N_of_mem_familyW (hσ : σ.IsValid) (hJ : σ.IsV21Layer J)
    (hW : W ∈ σ.familyW J) : W ≤ σ.N :=
  hW.1.trans (hJ.le.trans hσ.L₀_le_N)

theorem le_C_of_mem_familyW (hσ : σ.IsValid) (hJ : σ.IsV21Layer J)
    (hW : W ∈ σ.familyW J) : W ≤ σ.C := by
  have hWN := le_N_of_mem_familyW hσ hJ hW
  obtain ⟨-, hDW, hWP, hWsup⟩ := hW
  set Pn := pCoreIn σ.p σ.N
  have hNP : σ.N ≤ Subgroup.normalizer (Pn : Set G) := le_normalizer_pCoreIn σ.p σ.N
  have hBN : oddCoreIn σ.C ⊓ J ≤ σ.N := inf_le_left.trans ((oddCoreIn_le σ.C).trans σ.C_le_N)
  intro w hw
  rw [Setting.C, Subgroup.mem_centralizer_iff]
  intro t ht
  have htN : t ∈ σ.N := σ.T_le_N hσ ht
  have htW : t ∈ Subgroup.normalizer (W : Set G) := hDW (σ.T_le_D hσ ht)
  have hw' : w ∈ ((oddCoreIn σ.C ⊓ J ⊔ Pn : Subgroup G) : Set G) := by
    rw [← hWsup]
    exact (le_sup_left : W ≤ W ⊔ Pn) hw
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (hBN.trans hNP)] at hw'
  obtain ⟨c', hc', o', ho', rfl⟩ := hw'
  have hc'C : c' ∈ σ.C := (oddCoreIn_le σ.C) hc'.1
  have hc't : c' * t = t * c' :=
    ((Subgroup.mem_centralizer_iff.mp hc'C) t ht).symm
  have hcommW : c' * o' * t * (c' * o')⁻¹ * t⁻¹ ∈ W := by
    have h1 : t * (c' * o')⁻¹ * t⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp htW _).mp (W.inv_mem hw)
    have := W.mul_mem hw h1
    simpa [mul_assoc] using this
  have hcommP : c' * o' * t * (c' * o')⁻¹ * t⁻¹ ∈ Pn := by
    have h1 : t * o'⁻¹ * t⁻¹ ∈ Pn :=
      (Subgroup.mem_normalizer_iff.mp (hNP htN) _).mp (Pn.inv_mem ho')
    have h2 : o' * (t * o'⁻¹ * t⁻¹) ∈ Pn := Pn.mul_mem ho' h1
    have h3 : c' * (o' * (t * o'⁻¹ * t⁻¹)) * c'⁻¹ ∈ Pn :=
      (Subgroup.mem_normalizer_iff.mp (hNP (hBN hc')) _).mp h2
    have e : c' * o' * t * (c' * o')⁻¹ * t⁻¹ = c' * (o' * (t * o'⁻¹ * t⁻¹)) * c'⁻¹ := by
      have hct : t * c'⁻¹ * t⁻¹ = c'⁻¹ := by
        rw [show t * c'⁻¹ * t⁻¹ = (t * c' * t⁻¹)⁻¹ by group, ← hc't]
        group
      calc c' * o' * t * (c' * o')⁻¹ * t⁻¹ = c' * o' * t * o'⁻¹ * (t⁻¹ * t) * c'⁻¹ * t⁻¹ := by
            group
        _ = c' * o' * (t * o'⁻¹ * t⁻¹) * (t * c'⁻¹ * t⁻¹) := by group
        _ = c' * (o' * (t * o'⁻¹ * t⁻¹)) * c'⁻¹ := by rw [hct]; group
    rw [e]
    exact h3
  have hbot : c' * o' * t * (c' * o')⁻¹ * t⁻¹ ∈ W ⊓ Pn := ⟨hcommW, hcommP⟩
  rw [hWP, Subgroup.mem_bot] at hbot
  have : c' * o' * t = t * (c' * o') := by
    have h := mul_eq_one_iff_eq_inv.mp hbot
    rw [inv_inv] at h
    calc c' * o' * t = c' * o' * t * (c' * o')⁻¹ * (c' * o') := by group
      _ = t * (c' * o') := by rw [h]
  exact this.symm

theorem odd_card_of_mem_familyW (hσ : σ.IsValid) (hJ : σ.IsV21Layer J)
    (hW : W ∈ σ.familyW J) : Odd (Nat.card W) := by
  have hWN := le_N_of_mem_familyW hσ hJ hW
  obtain ⟨-, -, hWP, hWsup⟩ := hW
  set Pn := pCoreIn σ.p σ.N
  set B := oddCoreIn σ.C ⊓ J
  have hNP : σ.N ≤ Subgroup.normalizer (Pn : Set G) := le_normalizer_pCoreIn σ.p σ.N
  have hBN : B ≤ σ.N := inf_le_left.trans ((oddCoreIn_le σ.C).trans σ.C_le_N)
  have h1 := card_sup_mul_card_inf_of_le_normalizer (hWN.trans hNP)
  have h2 := card_sup_mul_card_inf_of_le_normalizer (hBN.trans hNP)
  rw [inf_comm, hWP, Subgroup.card_bot, mul_one, sup_comm, hWsup, sup_comm] at h1
  rw [h1] at h2
  have hP0 : 0 < Nat.card Pn := Nat.card_pos
  have h3 : Nat.card W * Nat.card (Pn ⊓ B : Subgroup G) = Nat.card B := by
    apply Nat.eq_of_mul_eq_mul_left hP0
    rw [← h2]
    ring
  have hBodd : Odd (Nat.card B) :=
    (odd_card_oddCoreIn σ.C).of_dvd_nat (Subgroup.card_dvd_of_le inf_le_left)
  exact hBodd.of_dvd_nat (Dvd.intro _ h3)

end FamilyW

end CFSG.ABGTheoremB.V56
