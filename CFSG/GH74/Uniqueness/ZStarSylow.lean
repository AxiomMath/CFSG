module

public import CFSG.GH74.Uniqueness.Lemma31gh
public import CFSG.GH74.Uniqueness.Prop35

public section

namespace CFSG.GH74.Uniqueness

open Subgroup

section PPrimeCoreIn

variable {X : Type*} [Group X]

@[expose] def pPrimeCoreIn (D : Subgroup X) : Subgroup X :=
  (pPrimeCore 2 ↥D).map D.subtype

theorem pPrimeCoreIn_le (D : Subgroup X) : pPrimeCoreIn D ≤ D := Subgroup.map_subtype_le _

theorem odd_card_pPrimeCoreIn [Finite X] (D : Subgroup X) : Odd (Nat.card (pPrimeCoreIn D)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := pPrimeCore_coprime_card (p := 2) (G := ↥D)
  rw [pPrimeCoreIn, Subgroup.card_map_of_injective D.subtype_injective]
  exact Nat.coprime_two_left.mp h

theorem le_pPrimeCoreIn [Finite X] {N D : Subgroup X} (hND : N ≤ D)
    (hnorm : D ≤ normalizer (N : Set X)) (hodd : Odd (Nat.card N)) : N ≤ pPrimeCoreIn D := by
  have hN : (N.subgroupOf D).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hND).mpr hnorm
  have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf D)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hND).toEquiv]
    exact Nat.coprime_two_left.mpr hodd
  have hle : N.subgroupOf D ≤ pPrimeCore 2 D := le_sSup ⟨hN, hcop⟩
  intro x hx
  exact ⟨⟨x, hND hx⟩, hle hx, rfl⟩

theorem pPrimeCoreIn_normalizes (D : Subgroup X) : D ≤ normalizer (pPrimeCoreIn D : Set X) := by
  intro d hd
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨d, hd⟩ * k * ⟨d, hd⟩⁻¹, (pPrimeCore_normal (p := 2) (G := ↥D)).conj_mem k hk ⟨d, hd⟩,
      rfl⟩
  · rintro ⟨k, hk, hkx⟩
    have hk' := (pPrimeCore_normal (p := 2) (G := ↥D)).conj_mem k hk ⟨d, hd⟩⁻¹
    rw [inv_inv] at hk'
    refine ⟨_, hk', ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hkx ⊢
    rw [hkx]
    group

theorem conjugate_pPrimeCoreIn_le [Finite X] {D : Subgroup X} {g : X}
    (hg : g ∈ normalizer (D : Set X)) : conjugate (pPrimeCoreIn D) g ≤ pPrimeCoreIn D := by
  have hD : ∀ x : X, x ∈ D ↔ g * x * g⁻¹ ∈ D := Subgroup.mem_normalizer_iff.mp hg
  have hcard : Nat.card (conjugate (pPrimeCoreIn D) g) = Nat.card (pPrimeCoreIn D) :=
    Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective
  apply le_pPrimeCoreIn (D := D)
  · intro x hx
    rw [mem_conjugate_iff] at hx
    have := pPrimeCoreIn_le D hx
    exact (hD x).mpr this
  · intro d hd
    rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have hgd : g * d * g⁻¹ ∈ D := (hD d).mp hd
    have hn := Subgroup.mem_normalizer_iff.mp (pPrimeCoreIn_normalizes D hgd) (g * x * g⁻¹)
    have e : g * (d * x * d⁻¹) * g⁻¹ = (g * d * g⁻¹) * (g * x * g⁻¹) * (g * d * g⁻¹)⁻¹ := by group
    rw [e]
    exact hn
  · rw [hcard]
    exact odd_card_pPrimeCoreIn D

theorem mem_normalizer_pPrimeCoreIn [Finite X] {D : Subgroup X} {t : X}
    (ht : t ∈ normalizer (D : Set X)) : t ∈ normalizer (pPrimeCoreIn D : Set X) := by
  have ht' : t⁻¹ ∈ normalizer (D : Set X) := (normalizer (D : Set X)).inv_mem ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    have := conjugate_pPrimeCoreIn_le ht' (x := t * x * t⁻¹)
    rw [mem_conjugate_iff] at this
    apply this
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rw [e]
    exact hx
  · intro hx
    have := conjugate_pPrimeCoreIn_le ht (x := x)
    rw [mem_conjugate_iff] at this
    exact this hx

end PPrimeCoreIn

section Involutions

variable {X : Type} [Group X]

theorem mul_self_of_orderOf_eq_two {t : X} (ht : orderOf t = 2) : t * t = 1 := by
  rw [← sq, ← ht, pow_orderOf_eq_one]

theorem mem_of_mul_self_mem_of_odd_orderOf {K : Subgroup X} {x : X} (hodd : Odd (orderOf x))
    (hx : x * x ∈ K) : x ∈ K := by
  obtain ⟨m, hm⟩ := hodd
  have : (x * x) ^ (m + 1) = x := by
    rw [← sq, ← pow_mul, show 2 * (m + 1) = (2 * m + 1) + 1 by ring, pow_succ, ← hm,
      pow_orderOf_eq_one, one_mul]
  rw [← this]
  exact K.pow_mem hx (m + 1)

theorem mem_normalizer_inf {A B : Subgroup X} {t : X} (hA : t ∈ normalizer (A : Set X))
    (hB : t ∈ normalizer (B : Set X)) : t ∈ normalizer ((A ⊓ B : Subgroup X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro x
  simp only [Subgroup.mem_inf]
  rw [hA x, hB x]

theorem orderOf_conj_eq {t : X} (ht : orderOf t = 2) (a : X) : orderOf (a * t * a⁻¹) = 2 := by
  have := orderOf_injective (MulAut.conj a).toMonoidHom (MulAut.conj a).injective t
  simpa [MulAut.conj_apply, ht] using this

theorem mul_self_mem_of_mem_sup_zpowers {W : Subgroup X} {t : X} (ht : t * t = 1)
    (htW : t ∈ normalizer (W : Set X)) {q : X} (hq : q ∈ W ⊔ zpowers t) : q * q ∈ W := by
  have hnormW : ∀ x ∈ W, t * x * t⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htW x).mp hx
  rcases mem_sup_zpowers_of_involution ht hnormW hq with hqW | hqtW
  · exact W.mul_mem hqW hqW
  · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, q = w * t⁻¹ := ⟨q * t, hqtW, by group⟩
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
    have e : w * t⁻¹ * (w * t⁻¹) = w * (t * w * t⁻¹) := by
      rw [hti]
      group
    rw [e]
    exact W.mul_mem hw (hnormW w hw)

end Involutions

section ZStar

variable {X : Type} [Group X]

theorem IsZStarIn.restrict {A W : Subgroup X} {t : X} (ht2 : t * t = 1) (h : IsZStarIn A t)
    (hWA : W ≤ A) (htW : t ∈ normalizer (W : Set X)) : IsZStarIn (W ⊔ zpowers t) t := by
  obtain ⟨htA, N, hNA, hNn, hNodd, hN⟩ := h
  have hAN : A ≤ normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mp hNn
  have hsupA : W ⊔ zpowers t ≤ A := sup_le hWA ((Subgroup.zpowers_le).mpr htA)
  have hsupW : W ⊔ zpowers t ≤ normalizer (W : Set X) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).mpr htW)
  have hnormW : ∀ x ∈ W, t * x * t⁻¹ ∈ W := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp htW x).mp hx
  have hN'le : N ⊓ W ≤ W ⊔ zpowers t := inf_le_right.trans le_sup_left
  refine ⟨Subgroup.mem_sup_right (Subgroup.mem_zpowers t), N ⊓ W, hN'le, ?_, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hN'le]
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hAN (hsupA ha)) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hsupW ha) x
    simp only [Subgroup.mem_inf]
    rw [h1, h2]
  · exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_left)
  · intro m hm
    refine Subgroup.mem_inf.mpr ⟨hN m (hsupA hm), ?_⟩
    rcases mem_sup_zpowers_of_involution ht2 hnormW hm with hmW | hmtW
    · have : m * t * m⁻¹ * t⁻¹ = m * (t * m⁻¹ * t⁻¹) := by group
      rw [this]
      exact W.mul_mem hmW (hnormW m⁻¹ (W.inv_mem hmW))
    · obtain ⟨w, hw, rfl⟩ : ∃ w ∈ W, m = w * t⁻¹ := ⟨m * t, hmtW, by group⟩
      have e : w * t⁻¹ * t * (w * t⁻¹)⁻¹ * t⁻¹ = w * (t * w⁻¹ * t⁻¹) := by group
      rw [e]
      exact W.mul_mem hw (hnormW w⁻¹ (W.inv_mem hw))

variable [Finite X]

theorem commutator_mem_pPrimeCoreIn {W : Subgroup X} {t : X}
    (hZ : IsZStarIn (W ⊔ zpowers t) t) (htW : t ∈ normalizer (W : Set X)) {d : X} (hd : d ∈ W) :
    d * t * d⁻¹ * t⁻¹ ∈ pPrimeCoreIn W := by
  obtain ⟨htA, N, hNA, hNn, hNodd, hN⟩ := hZ
  have hAN : W ⊔ zpowers t ≤ normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mp hNn
  have hdA : d ∈ W ⊔ zpowers t := Subgroup.mem_sup_left hd
  have hnW : d * t * d⁻¹ * t⁻¹ ∈ W := by
    have : d * t * d⁻¹ * t⁻¹ = d * (t * d⁻¹ * t⁻¹) := by group
    rw [this]
    exact W.mul_mem hd ((Subgroup.mem_normalizer_iff.mp htW d⁻¹).mp (W.inv_mem hd))
  have hle : N ⊓ W ≤ pPrimeCoreIn W := by
    apply le_pPrimeCoreIn inf_le_right
    · intro w hw
      exact mem_normalizer_inf (hAN (Subgroup.mem_sup_left hw)) (Subgroup.le_normalizer hw)
    · exact Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le inf_le_left)
  exact hle (Subgroup.mem_inf.mpr ⟨hN d hdA, hnW⟩)

omit [Finite X] in
theorem exists_mul_centralizer {A N : Subgroup X} {t : X} (ht : orderOf t = 2) (hNA : N ≤ A)
    (htN : t ∈ normalizer (N : Set X))
    (hNodd : Odd (Nat.card N)) (hcomm : ∀ a ∈ A, a * t * a⁻¹ * t⁻¹ ∈ N) {a : X} (ha : a ∈ A) :
    ∃ n ∈ N, ∃ c ∈ A ⊓ centralizer ({t} : Set X), a = n * c := by
  have hv2 := orderOf_conj_eq ht a
  have hvt : (a * t * a⁻¹) * t⁻¹ ∈ N := hcomm a ha
  have hcoset := (CFSG.OddInversion.odd_inversion_coset_count hNodd htN
    (CFSG.OddInversion.notMem_of_odd_card hNodd ht) ht).1
  have hmem : a * t * a⁻¹ ∈ {v : X | v * t⁻¹ ∈ N ∧ orderOf v = 2} := ⟨hvt, hv2⟩
  rw [hcoset] at hmem
  obtain ⟨b, hbN, hb⟩ := hmem
  refine ⟨b⁻¹, N.inv_mem hbN, b * a,
    Subgroup.mem_inf.mpr ⟨A.mul_mem (hNA hbN) ha, ?_⟩, by group⟩
  rw [Subgroup.mem_centralizer_singleton_iff]
  have : b * a * t * a⁻¹ * b⁻¹ = t := by
    have e : b * a * t * a⁻¹ * b⁻¹ = b * (a * t * a⁻¹) * b⁻¹ := by group
    rw [e, hb]
    group
  calc b * a * t = (b * a * t * a⁻¹ * b⁻¹) * (b * a) := by group
    _ = t * (b * a) := by rw [this]

theorem exists_mul_centralizer_pPrimeCoreIn {W : Subgroup X} {t : X} (ht : orderOf t = 2)
    (htW : t ∈ normalizer (W : Set X))
    (hcomm : ∀ d ∈ W, d * t * d⁻¹ * t⁻¹ ∈ pPrimeCoreIn W) {d : X} (hd : d ∈ W) :
    ∃ a ∈ pPrimeCoreIn W, ∃ c ∈ W ⊓ centralizer ({t} : Set X), d = a * c :=
  exists_mul_centralizer ht (pPrimeCoreIn_le W) (mem_normalizer_pPrimeCoreIn htW)
    (odd_card_pPrimeCoreIn W) hcomm hd

theorem exists_centralizer_conj {W P Q : Subgroup X} {t : X} (ht : orderOf t = 2)
    (htW : t ∈ normalizer (W : Set X))
    (hcomm : ∀ d ∈ W, d * t * d⁻¹ * t⁻¹ ∈ pPrimeCoreIn W)
    (htP : t ∈ normalizer (P : Set X)) (htQ : t ∈ normalizer (Q : Set X)) {w : X} (hw : w ∈ W)
    (hPQ : conjugate P w = Q) : ∃ c ∈ W ⊓ centralizer ({t} : Set X), conjugate P c = Q := by
  set K := pPrimeCoreIn W with hK
  have ht'P : w * t * w⁻¹ ∈ normalizer (P : Set X) := by
    rw [← conjugate_eq_iff_mem_normalizer]
    have h1 : conjugate Q t = Q := conjugate_eq_iff_mem_normalizer.mpr htQ
    rw [← hPQ, conjugate_conjugate] at h1
    calc conjugate P (w * t * w⁻¹) = conjugate (conjugate P (w * t)) w⁻¹ := by
          rw [conjugate_conjugate]
      _ = conjugate (conjugate P w) w⁻¹ := by rw [h1]
      _ = P := by rw [conjugate_conjugate, mul_inv_cancel, conjugate_one]
  have hn : w * t * w⁻¹ * t⁻¹ ∈ K := hcomm w hw
  have hnP : w * t * w⁻¹ * t⁻¹ ∈ normalizer (P : Set X) :=
    (normalizer (P : Set X)).mul_mem ht'P ((normalizer (P : Set X)).inv_mem htP)
  have hKodd : Odd (Nat.card K) := odd_card_pPrimeCoreIn W
  have htK : t ∈ normalizer (K : Set X) := mem_normalizer_pPrimeCoreIn htW
  have htE : t ∈ normalizer ((K ⊓ normalizer (P : Set X) : Subgroup X) : Set X) :=
    mem_normalizer_inf htK (Subgroup.le_normalizer htP)
  have hEodd : Odd (Nat.card (K ⊓ normalizer (P : Set X) : Subgroup X)) :=
    Odd.of_dvd_nat hKodd (Subgroup.card_dvd_of_le inf_le_left)
  have hcoset := (CFSG.OddInversion.odd_inversion_coset_count hEodd htE
    (CFSG.OddInversion.notMem_of_odd_card hEodd ht) ht).1
  have hmem : w * t * w⁻¹ ∈ {v : X | v * t⁻¹ ∈ (K ⊓ normalizer (P : Set X) : Subgroup X) ∧
      orderOf v = 2} := ⟨Subgroup.mem_inf.mpr ⟨hn, hnP⟩, orderOf_conj_eq ht w⟩
  rw [hcoset] at hmem
  obtain ⟨b, hbE, hb⟩ := hmem
  have hbK : b ∈ K := (Subgroup.mem_inf.mp hbE).1
  have hbP : b ∈ normalizer (P : Set X) := (Subgroup.mem_inf.mp hbE).2
  refine ⟨b * w, Subgroup.mem_inf.mpr ⟨W.mul_mem (pPrimeCoreIn_le W hbK) hw, ?_⟩, ?_⟩
  · rw [Subgroup.mem_centralizer_singleton_iff]
    have : b * w * t * w⁻¹ * b⁻¹ = t := by
      have e : b * w * t * w⁻¹ * b⁻¹ = b * (w * t * w⁻¹) * b⁻¹ := by group
      rw [e, hb]
      group
    calc b * w * t = (b * w * t * w⁻¹ * b⁻¹) * (b * w) := by group
      _ = t * (b * w) := by rw [this]
  · have hb' : conjugate P b = P := conjugate_eq_iff_mem_normalizer.mpr hbP
    rw [← conjugate_conjugate, hb', hPQ]

end ZStar

section Sylow

variable {X : Type} [Group X] [Finite X]

theorem exists_conj_of_isSylowOf {p : ℕ} [Fact p.Prime] {W P Q : Subgroup X}
    (hP : ABGLocalTools.IsSylowOf p P W) (hQ : ABGLocalTools.IsSylowOf p Q W) :
    ∃ w ∈ W, conjugate P w = Q := by
  obtain ⟨P', rfl⟩ := hP
  obtain ⟨Q', rfl⟩ := hQ
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W P' Q'
  refine ⟨(g : X)⁻¹, W.inv_mem g.2, ?_⟩
  have hc : ∀ s : W, s ∈ ((g • P' : Sylow p W) : Subgroup W) ↔
      g⁻¹ * s * g ∈ (P' : Subgroup W) := by
    intro s
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨s', hs', rfl⟩
      have e : g⁻¹ * (g * s' * g⁻¹) * g = s' := by group
      simp only [MulAut.smul_def, MulAut.conj_apply]
      rw [e]
      exact hs'
    · intro hs
      exact ⟨g⁻¹ * s * g, hs, by simp [MulAut.smul_def]; group⟩
  rw [← hg]
  ext x
  rw [mem_conjugate_iff]
  simp only [Subgroup.mem_map, Subgroup.coe_subtype]
  constructor
  · rintro ⟨y, hy, hyx⟩
    refine ⟨g * y * g⁻¹, (hc _).mpr (by
      have e : g⁻¹ * (g * y * g⁻¹) * g = y := by group
      rw [e]
      exact hy), ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hyx]
    group
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g⁻¹ * y * g, (hc y).mp hy, by simp⟩

theorem isSylowOf_conjugate_of_mem {p : ℕ} [Fact p.Prime] {S H : Subgroup X}
    (hS : ABGLocalTools.IsSylowOf p S H) {c : X} (hc : c ∈ H) :
    ABGLocalTools.IsSylowOf p (conjugate S c) H := by
  have hcH : conjugate H c = H :=
    conjugate_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hc)
  have hle : conjugate S c ≤ H := by
    rw [← hcH]
    intro x hx
    rw [mem_conjugate_iff] at hx ⊢
    exact hS.le hx
  apply ABGLocalTools.isSylowOf_of_card hle
  have hcard : Nat.card ↥(conjugate S c) = Nat.card S :=
    Subgroup.card_map_of_injective (MulAut.conj c⁻¹).injective
  rw [hcard]
  exact hS.card_eq

theorem exists_invariant_sylow {W P : Subgroup X} {t : X} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (ht : orderOf t = 2) (htW : t ∈ normalizer (W : Set X)) (hZ : IsZStarIn (W ⊔ zpowers t) t)
    (hPW : P ≤ W) (hPp : IsPGroup p P) (htP : t ∈ normalizer (P : Set X)) :
    ∃ Q : Subgroup X, ABGLocalTools.IsSylowOf p Q W ∧ P ≤ Q ∧ t ∈ normalizer (Q : Set X) := by
  have : Fact p.Prime := ⟨hp⟩
  set A : Subgroup X := W ⊔ zpowers t with hA
  have ht2 : t * t = 1 := mul_self_of_orderOf_eq_two ht
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    exact absurd ht (by norm_num)
  have htA : t ∈ A := Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have hWA : W ≤ A := le_sup_left
  let u : A := ⟨t, htA⟩
  have hu : CFSG.BenderSuzuki.PFAppendixIII.IsInvolution u := by
    refine ⟨fun h => ht1 (congrArg Subtype.val h), ?_⟩
    apply Subtype.ext
    simpa [pow_two] using ht2
  obtain ⟨-, N, hNA, hNn, hNodd, hN⟩ := hZ
  have hAN : A ≤ normalizer (N : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNA).mp hNn
  have htN : t ∈ normalizer (N : Set X) := hAN htA
  have hfactor : pPrimeCore 2 ↥A ⊔ centralizer ({u} : Set A) = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, ha⟩ -
    obtain ⟨n, hnN, c, hc, rfl⟩ := exists_mul_centralizer ht hNA htN hNodd hN ha
    have hcop : Nat.Coprime 2 (Nat.card (N.subgroupOf A)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNA).toEquiv]
      exact Nat.coprime_two_left.mpr hNodd
    have hle : N.subgroupOf A ≤ pPrimeCore 2 A := le_sSup ⟨hNn, hcop⟩
    have hn' : (⟨n, hNA hnN⟩ : A) ∈ pPrimeCore 2 A := hle hnN
    have hc' : (⟨c, (Subgroup.mem_inf.mp hc).1⟩ : A) ∈ centralizer ({u} : Set A) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      apply Subtype.ext
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hc).2
    exact Subgroup.mul_mem_sup hn' hc'
  have hP'p : IsPGroup p (P.subgroupOf A) := hPp.comap_subtype
  have huP' : u ∈ normalizer ((P.subgroupOf A : Subgroup A) : Set A) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    show (x : X) ∈ P ↔ ((u * x * u⁻¹ : A) : X) ∈ P
    simpa using Subgroup.mem_normalizer_iff.mp htP (x : X)
  obtain ⟨S, hPS, huS⟩ :=
    CFSG.BenderSuzuki.exists_invariant_sylow_containing_of_pPrimeCore_sup_centralizer_eq_top hu hp
      (hp.odd_of_ne_two hp2) hP'p huP' hfactor
  set Q : Subgroup X := (S : Subgroup A).map A.subtype with hQ
  have hQA : ABGLocalTools.IsSylowOf p Q A := ⟨S, rfl⟩
  have hQp : IsPGroup p Q := S.isPGroup'.map A.subtype
  have hQW : Q ≤ W := by
    intro q hq
    have hqA : q ∈ A := by
      obtain ⟨y, -, rfl⟩ := hq
      exact y.2
    have hodd : Odd (orderOf q) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQp ⟨q, hq⟩
      rw [Subgroup.orderOf_mk] at hk
      rw [hk]
      exact (hp.odd_of_ne_two hp2).pow
    exact mem_of_mul_self_mem_of_odd_orderOf hodd (mul_self_mem_of_mem_sup_zpowers ht2 htW hqA)
  refine ⟨Q, hQA.of_le hQW hWA, ?_, ?_⟩
  · intro x hx
    exact ⟨⟨x, hWA (hPW hx)⟩, hPS (show (⟨x, hWA (hPW hx)⟩ : A) ∈ P.subgroupOf A from hx), rfl⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    have hnorm := Subgroup.mem_normalizer_iff.mp huS
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨u * y * u⁻¹, (hnorm y).mp hy, by simp [u]⟩
    · rintro ⟨y, hy, hyx⟩
      refine ⟨u⁻¹ * y * u, ?_, ?_⟩
      · refine (hnorm (u⁻¹ * y * u)).mpr ?_
        have e : u * (u⁻¹ * y * u) * u⁻¹ = y := by group
        rw [e]
        exact hy
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hyx ⊢
        have hu' : (u : X) = t := rfl
        rw [hu', hyx]
        group

theorem exists_sylow_le_centralizer {W P : Subgroup X} {t : X} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ht : orderOf t = 2) (htW : t ∈ normalizer (W : Set X))
    (hZ : IsZStarIn (W ⊔ zpowers t) t) (hP : ABGLocalTools.IsSylowOf p P W)
    (htP : t ∈ normalizer (P : Set X)) :
    ∃ S : Subgroup X, S ≤ P ∧ ABGLocalTools.IsSylowOf p S (W ⊓ centralizer ({t} : Set X)) := by
  have : Fact p.Prime := ⟨hp⟩
  have hcomm := fun d hd => commutator_mem_pPrimeCoreIn hZ htW (d := d) hd
  obtain ⟨S₀, hS₀⟩ := ABGLocalTools.exists_isSylowOf p (W ⊓ centralizer ({t} : Set X))
  have hS₀le : S₀ ≤ W ⊓ centralizer ({t} : Set X) := hS₀.le
  have hS₀W : S₀ ≤ W := hS₀le.trans inf_le_left
  have htS₀ : t ∈ normalizer (S₀ : Set X) := by
    refine Subgroup.centralizer_le_normalizer (S₀ : Set X) ?_
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp (hS₀le hs)).2
  obtain ⟨Q, hQ, hS₀Q, htQ⟩ := exists_invariant_sylow hp hp2 ht htW hZ hS₀W hS₀.isPGroup htS₀
  obtain ⟨w, hw, hwQ⟩ := exists_conj_of_isSylowOf hQ hP
  obtain ⟨c, hc, hcQ⟩ := exists_centralizer_conj ht htW hcomm htQ htP hw hwQ
  refine ⟨conjugate S₀ c, ?_, ?_⟩
  · rw [← hcQ]
    intro x hx
    rw [mem_conjugate_iff] at hx ⊢
    exact hS₀Q hx
  · have hcC : c ∈ W ⊓ centralizer ({t} : Set X) := hc
    exact isSylowOf_conjugate_of_mem hS₀ hcC

end Sylow

section Counting

variable {X : Type*} [Group X]

theorem card_conj_orbit (D : Subgroup X) (z : X) :
    Nat.card {y : X // ∃ d ∈ D, y = d⁻¹ * z * d} = (centralizer ({z} : Set X)).relIndex D := by
  let f : D → {y : X // ∃ d ∈ D, y = d⁻¹ * z * d} := fun d =>
    ⟨(d : X) * z * (d : X)⁻¹, (d : X)⁻¹, D.inv_mem d.2, by group⟩
  have hf : Function.Surjective f := by
    rintro ⟨y, d, hd, rfl⟩
    exact ⟨⟨d⁻¹, D.inv_mem hd⟩, Subtype.ext (by simp [f])⟩
  have hfib : ∀ a b : D, f a = f b ↔ a⁻¹ * b ∈ (centralizer ({z} : Set X)).subgroupOf D := by
    intro a b
    simp only [f, Subtype.mk.injEq, Subgroup.mem_subgroupOf,
      Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_mul, Subgroup.coe_inv]
    constructor
    · intro h
      calc (a : X)⁻¹ * b * z = (a : X)⁻¹ * (b * z * (b : X)⁻¹) * b := by group
        _ = (a : X)⁻¹ * (a * z * (a : X)⁻¹) * b := by rw [h]
        _ = z * ((a : X)⁻¹ * b) := by group
    · intro h
      calc (a : X) * z * (a : X)⁻¹
          = (a : X) * ((a : X)⁻¹ * b * z * ((a : X)⁻¹ * b)⁻¹) * (a : X)⁻¹ := by
            rw [h]
            group
        _ = (b : X) * z * (b : X)⁻¹ := by group
  rw [Subgroup.relIndex, Subgroup.index]
  symm
  calc Nat.card (D ⧸ (centralizer ({z} : Set X)).subgroupOf D)
      = Nat.card (Quotient (Setoid.ker f)) :=
        Nat.card_congr (Quotient.congrRight fun a b => by
          rw [Setoid.ker_def, hfib]
          exact QuotientGroup.leftRel_apply)
    _ = Nat.card {y : X // ∃ d ∈ D, y = d⁻¹ * z * d} :=
        Nat.card_congr (Setoid.quotientKerEquivOfSurjective f hf)

end Counting

end CFSG.GH74.Uniqueness
