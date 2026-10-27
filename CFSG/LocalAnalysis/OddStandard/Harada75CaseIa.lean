module

public import CFSG.LocalAnalysis.OddStandard.Harada75Pres
public import CFSG.LocalAnalysis.OddStandard.Harada75Dual
public import CFSG.LocalAnalysis.OddStandard.Harada75Ord8
public import CFSG.LocalAnalysis.OddStandard.Harada75Normal

public section

namespace CFSG.OddStandard.Harada75

open Subgroup
open scoped commutatorElement

variable {S : Type} [Group S]

private theorem caseIa_card_le_finset {G : Type} [Group G] [Finite G] (U : Subgroup G)
    (F : Finset G) (h : ∀ x ∈ U, x ∈ F) : Nat.card U ≤ F.card := by
  have h1 : (U : Set G) ⊆ (F : Set G) := fun x hx => h x hx
  have h2 := Set.ncard_le_ncard h1 (Finset.finite_toSet F)
  rw [Set.ncard_coe_finset] at h2
  rwa [← Nat.card_coe_set_eq] at h2

private theorem caseIa_comm_of_eq_one {a b : S} (h : a * b * a⁻¹ * b⁻¹ = 1) : a * b = b * a := by
  have h1 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h1]

private theorem caseIa_sup_norm {X Y : Subgroup S} {n : S} (hX : ∀ x ∈ X, n * x * n⁻¹ ∈ X)
    (hY : ∀ y ∈ Y, n * y * n⁻¹ ∈ Y) : ∀ p ∈ X ⊔ Y, n * p * n⁻¹ ∈ X ⊔ Y := by
  have hX' : X ≤ (X ⊔ Y).comap (MulAut.conj n).toMonoidHom := fun x hx =>
    Subgroup.mem_sup_left (hX x hx)
  have hY' : Y ≤ (X ⊔ Y).comap (MulAut.conj n).toMonoidHom := fun y hy =>
    Subgroup.mem_sup_right (hY y hy)
  exact fun p hp => sup_le hX' hY' hp

private theorem caseIa_mem_sup {A E : Subgroup S} (hE : ∀ s : S, ∀ e ∈ E, s * e * s⁻¹ ∈ E)
    {x : S} (hx : x ∈ A ⊔ E) : ∃ a ∈ A, ∃ e ∈ E, a * e = x := by
  have : E.Normal := ⟨fun n hn g => hE g n hn⟩
  exact Subgroup.mem_sup_of_normal_right.mp hx

private theorem caseIa_card_sup [Finite S] {N H K : Subgroup S} (hH : H ≤ N) (hK : K ≤ N)
    (hKn : ∀ n ∈ N, ∀ k ∈ K, n * k * n⁻¹ ∈ K) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card H * Nat.card K := by
  have hKnorm : (K.subgroupOf N).Normal := ⟨fun a ha g => hKn g.1 g.2 a.1 ha⟩
  have hcard : ∀ {X : Subgroup S}, X ≤ N → Nat.card (X.subgroupOf N) = Nat.card X :=
    fun hX => Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  have h1 := Subgroup.relIndex_sup_right (H.subgroupOf N) (K.subgroupOf N)
  have h2 := Subgroup.relIndex_mul_card (H := K.subgroupOf N)
    (K := H.subgroupOf N ⊔ K.subgroupOf N)
  have h3 := Subgroup.relIndex_mul_card (H := K.subgroupOf N) (K := H.subgroupOf N)
  rw [inf_eq_left.mpr (le_sup_right : K.subgroupOf N ≤ H.subgroupOf N ⊔ K.subgroupOf N), h1,
    ← Subgroup.subgroupOf_sup hH hK, hcard (sup_le hH hK), hcard hK] at h2
  have e : K.subgroupOf N ⊓ H.subgroupOf N = (K ⊓ H).subgroupOf N := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  rw [e, hcard (inf_le_left.trans hK), hcard hH] at h3
  rw [← h2, ← h3, inf_comm H K]
  ring

private structure CaseIaConj (A E B : Subgroup S) : Prop where
  comm : ∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b
  sq : ∀ b ∈ B, b * b = 1
  card : Nat.card B = 8
  cent : ∀ x : S, (∀ b ∈ B, x * b = b * x) → x ∈ B
  inf_card : Nat.card ↥(B ⊓ E) = 4
  ne : B ≠ A
  le_norm : B ≤ Subgroup.normalizer (A : Set S)
  norm : ∀ n ∈ Subgroup.normalizer (A : Set S), ∀ b ∈ B, n * b * n⁻¹ ∈ B

private theorem caseIa_card_conj {X Y : Subgroup S} {t : S} (h : ∀ x, x ∈ Y ↔ t⁻¹ * x * t ∈ X) :
    Nat.card Y = Nat.card X :=
  Nat.card_congr
    { toFun := fun x => ⟨t⁻¹ * x.1 * t, (h x.1).mp x.2⟩
      invFun := fun y => ⟨t * y.1 * t⁻¹, (h _).mpr (by
        have e : t⁻¹ * (t * y.1 * t⁻¹) * t = y.1 := by group
        rw [e]
        exact y.2)⟩
      left_inv := fun x => Subtype.ext (by show t * (t⁻¹ * x.1 * t) * t⁻¹ = x.1; group)
      right_inv := fun y => Subtype.ext (by show t⁻¹ * (t * y.1 * t⁻¹) * t = y.1; group) }

private theorem caseIa_conj_abelian {A B : Subgroup S} (hA : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a * a = 1) {t : S} (hBmem : ∀ x, x ∈ B ↔ t⁻¹ * x * t ∈ A) :
    (∀ b ∈ B, ∀ b' ∈ B, b * b' = b' * b) ∧ (∀ b ∈ B, b * b = 1) := by
  refine ⟨fun b hb b' hb' => ?_, fun b hb => ?_⟩
  · have h1 := hA _ ((hBmem b).mp hb) _ ((hBmem b').mp hb')
    have e1 : t⁻¹ * (b * b') * t = (t⁻¹ * b * t) * (t⁻¹ * b' * t) := by group
    have e2 : t⁻¹ * (b' * b) * t = (t⁻¹ * b' * t) * (t⁻¹ * b * t) := by group
    have h2 : t⁻¹ * (b * b') * t = t⁻¹ * (b' * b) * t := by rw [e1, e2, h1]
    exact mul_left_cancel (mul_right_cancel h2)
  · have h1 := hA2 _ ((hBmem b).mp hb)
    have e : t⁻¹ * (b * b) * t = (t⁻¹ * b * t) * (t⁻¹ * b * t) := by group
    have h2 : t⁻¹ * (b * b) * t = 1 := by rw [e]; exact h1
    calc b * b = t * (t⁻¹ * (b * b) * t) * t⁻¹ := by group
      _ = 1 := by rw [h2]; group

private theorem caseIa_conj_cent {A B : Subgroup S} (hA : ∀ x : S, (∀ a ∈ A, x * a = a * x) → x ∈ A)
    {t : S} (hBmem : ∀ x, x ∈ B ↔ t⁻¹ * x * t ∈ A) :
    ∀ x : S, (∀ b ∈ B, x * b = b * x) → x ∈ B := by
  intro x hx
  rw [hBmem]
  apply hA
  intro a ha
  have hmem : t * a * t⁻¹ ∈ B := (hBmem _).mpr (by
    have e : t⁻¹ * (t * a * t⁻¹) * t = a := by group
    rw [e]
    exact ha)
  have h1 := hx _ hmem
  calc t⁻¹ * x * t * a = t⁻¹ * (x * (t * a * t⁻¹)) * t := by group
    _ = t⁻¹ * ((t * a * t⁻¹) * x) * t := by rw [h1]
    _ = a * (t⁻¹ * x * t) := by group

private theorem caseIa_exists_conj [Finite S] (hS : IsPGroup 2 S) {A E : Subgroup S}
    (h : Cfg S A E) (hcard : Nat.card ↥(A ⊓ E) = 4)
    (hNS : Subgroup.normalizer (A : Set S) ≠ ⊤) : ∃ B : Subgroup S, CaseIaConj A E B := by
  obtain ⟨t, -, htN, ht⟩ := exists_mem_normalizer_not_mem hS
    (W := Subgroup.normalizer (A : Set S)) (C := ⊤) le_top hNS
  have ht' : ∀ w, w ∈ Subgroup.normalizer (A : Set S) ↔
      t * w * t⁻¹ ∈ Subgroup.normalizer (A : Set S) := fun w => ht w (Subgroup.mem_top w)
  obtain ⟨B, hBmem⟩ : ∃ B : Subgroup S, ∀ x, x ∈ B ↔ t⁻¹ * x * t ∈ A :=
    ⟨{ carrier := {x | t⁻¹ * x * t ∈ A}
       one_mem' := by simp
       mul_mem' := fun {a b} ha hb => by
         have e : t⁻¹ * (a * b) * t = (t⁻¹ * a * t) * (t⁻¹ * b * t) := by group
         show t⁻¹ * (a * b) * t ∈ A
         rw [e]
         exact A.mul_mem ha hb
       inv_mem' := fun {a} ha => by
         have e : t⁻¹ * a⁻¹ * t = (t⁻¹ * a * t)⁻¹ := by group
         show t⁻¹ * a⁻¹ * t ∈ A
         rw [e]
         exact A.inv_mem ha }, fun x => Iff.rfl⟩
  have hEconj : ∀ x, x ∈ E ↔ t⁻¹ * x * t ∈ E := by
    intro x
    constructor
    · intro hx
      have := h.E_norm t⁻¹ x hx
      rwa [inv_inv] at this
    · intro hx
      have := h.E_norm t _ hx
      have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
      rwa [e] at this
  have hBN : B ≤ Subgroup.normalizer (A : Set S) := by
    intro x hx
    have h1 : t⁻¹ * x * t ∈ Subgroup.normalizer (A : Set S) :=
      Subgroup.le_normalizer ((hBmem x).mp hx)
    have h2 := (ht' _).mp h1
    have e : t * (t⁻¹ * x * t) * t⁻¹ = x := by group
    rwa [e] at h2
  obtain ⟨hBc, hB2⟩ := caseIa_conj_abelian h.A_comm h.A_sq hBmem
  refine ⟨B, ⟨hBc, hB2, ?_, caseIa_conj_cent h.A_cent hBmem, ?_, ?_, hBN, ?_⟩⟩
  · rw [caseIa_card_conj hBmem, h.A_card]
  · rw [caseIa_card_conj (X := A ⊓ E) (t := t) (fun x => ?_), hcard]
    constructor
    · rintro ⟨hxB, hxE⟩
      exact ⟨(hBmem x).mp hxB, (hEconj x).mp hxE⟩
    · rintro ⟨hxA, hxE⟩
      exact ⟨(hBmem x).mpr hxA, (hEconj x).mpr hxE⟩
  · intro hBA
    apply htN
    rw [hBA] at hBmem
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have h1 := hBmem (t * g * t⁻¹)
    have e : t⁻¹ * (t * g * t⁻¹) * t = g := by group
    rw [e] at h1
    exact h1.symm
  · intro n hn b hb
    rw [hBmem]
    have hm : t⁻¹ * n * t ∈ Subgroup.normalizer (A : Set S) := by
      rw [ht' (t⁻¹ * n * t)]
      have e : t * (t⁻¹ * n * t) * t⁻¹ = n := by group
      rwa [e]
    have h1 := (Subgroup.mem_normalizer_iff.mp hm _).mp ((hBmem b).mp hb)
    have e : (t⁻¹ * n * t) * (t⁻¹ * b * t) * (t⁻¹ * n * t)⁻¹ = t⁻¹ * (n * b * n⁻¹) * t := by
      group
    rwa [e] at h1

private theorem caseIa_comm_mem_inf {A E B : Subgroup S} (hB : CaseIaConj A E B) {a b : S}
    (ha : a ∈ A) (hb : b ∈ B) : a * b * a⁻¹ * b⁻¹ ∈ A ⊓ B := by
  have haN : a ∈ Subgroup.normalizer (A : Set S) := Subgroup.le_normalizer ha
  have hbN : b ∈ Subgroup.normalizer (A : Set S) := hB.le_norm hb
  refine ⟨?_, ?_⟩
  · have h1 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hbN _).mp (A.inv_mem ha)
    have h2 := A.mul_mem ha h1
    have e : a * (b * a⁻¹ * b⁻¹) = a * b * a⁻¹ * b⁻¹ := by group
    rwa [e] at h2
  · exact B.mul_mem (hB.norm a haN b hb) (B.inv_mem hb)

private theorem caseIa_inter_ne_one [Finite S] {A E B : Subgroup S} (h : Cfg S A E)
    (hB : CaseIaConj A E B) : Nat.card ↥(A ⊓ B) ≠ 1 := by
  intro h1
  apply hB.ne
  have hbot : A ⊓ B = ⊥ := Subgroup.eq_bot_of_card_eq _ h1
  have hBA : B ≤ A := by
    intro b hb
    apply h.A_cent
    intro a ha
    have hc := caseIa_comm_mem_inf hB ha hb
    rw [hbot, Subgroup.mem_bot] at hc
    exact (caseIa_comm_of_eq_one hc).symm
  exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hB.card, h.A_card])

private theorem caseIa_inter_ne_eight [Finite S] {A E B : Subgroup S} (h : Cfg S A E)
    (hB : CaseIaConj A E B) : Nat.card ↥(A ⊓ B) ≠ 8 := by
  intro h8
  apply hB.ne
  have h1 : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h8, h.A_card])
  have h2 : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h8, hB.card])
  exact h2.symm.trans h1

private theorem caseIa_sup_eq [Finite S] (hS : IsPGroup 2 S) {A E B : Subgroup S} (h : Cfg S A E)
    (hcard : Nat.card ↥(A ⊓ E) = 4) (hN : Nat.card ↥(Subgroup.normalizer (A : Set S)) = 64)
    (hB : CaseIaConj A E B) (h4 : Nat.card ↥(A ⊓ B) = 4) : A ⊔ E = A ⊔ B := by
  have hAN : A ≤ Subgroup.normalizer (A : Set S) := Subgroup.le_normalizer
  have hEN : E ≤ Subgroup.normalizer (A : Set S) := h.caseI_E_le_normalizer hcard
  have hBN : B ≤ Subgroup.normalizer (A : Set S) := hB.le_norm
  have hAnorm : ∀ n ∈ Subgroup.normalizer (A : Set S), ∀ a ∈ A, n * a * n⁻¹ ∈ A :=
    fun n hn a ha => (Subgroup.mem_normalizer_iff.mp hn a).mp ha
  have hEnorm : ∀ n ∈ Subgroup.normalizer (A : Set S), ∀ e ∈ E, n * e * n⁻¹ ∈ E :=
    fun n _ e he => h.E_norm n e he
  have hPcard : Nat.card ↥(A ⊔ E) = 16 := by
    have := caseIa_card_sup hAN hEN hEnorm
    rw [hcard, h.A_card, h.E_card] at this
    omega
  have hP'card : Nat.card ↥(A ⊔ B) = 16 := by
    have := caseIa_card_sup hAN hBN hB.norm
    rw [h4, h.A_card, hB.card] at this
    omega
  have hnc : ∃ x ∈ Subgroup.normalizer (A : Set S), ∃ y ∈ Subgroup.normalizer (A : Set S),
      ⁅x, y⁆ ∉ A := by
    have hX : IsPGroup 2 (Subgroup.normalizer (A : Set S)) := hS.to_subgroup _
    have h8 : Nat.card ↥(Subgroup.normalizer (A : Set S)) =
        8 * Nat.card ↥(Subgroup.normalizer (A : Set S) ⊓ Subgroup.centralizer (A : Set S)) := by
      rw [h.centralizer_eq, inf_eq_right.mpr hAN, hN, h.A_card]
    obtain ⟨x, hx, y, hy, hxy⟩ := exists_commutator_not_mem_centralizer h.A_comm
      (fun a ha => by rw [pow_two]; exact h.A_sq a ha) h.A_card hX hAnorm h8
    exact ⟨x, hx, y, hy, by rwa [h.centralizer_eq] at hxy⟩
  exact eq_of_card_sixteen_of_nonabelian hN h.A_card hAN hAnorm hnc le_sup_left
    (sup_le hAN hEN) (fun n hn => caseIa_sup_norm (hAnorm n hn) (hEnorm n hn)) hPcard
    le_sup_left (sup_le hAN hBN) (fun n hn => caseIa_sup_norm (hAnorm n hn) (hB.norm n hn))
    hP'card

private theorem caseIa_inf_le_conj [Finite S] {A E B : Subgroup S} (h : Cfg S A E)
    (hB : CaseIaConj A E B) (hle : B ≤ A ⊔ E) : A ⊓ E ≤ B := by
  intro x hx
  apply hB.cent
  intro b hb
  obtain ⟨a, ha, e, he, rfl⟩ := caseIa_mem_sup h.E_norm (hle hb)
  calc x * (a * e) = (x * a) * e := by group
    _ = (a * x) * e := by rw [h.A_comm x hx.1 a ha]
    _ = a * (x * e) := by group
    _ = a * (e * x) := by rw [h.E_comm x hx.2 e he]
    _ = a * e * x := by group

private theorem caseIa_not_le_sup [Finite S] {A E B : Subgroup S} (h : Cfg S A E)
    (hcard : Nat.card ↥(A ⊓ E) = 4) (hB : CaseIaConj A E B) (h4 : Nat.card ↥(A ⊓ B) = 4)
    (hle : B ≤ A ⊔ E) : False := by
  have hA₀B := caseIa_inf_le_conj h hB hle
  obtain ⟨b, hbB, hbn⟩ : ∃ b ∈ B, b ∉ A ⊓ E := by
    by_contra hno
    push Not at hno
    have := Subgroup.card_le_of_le (show B ≤ A ⊓ E from hno)
    rw [hB.card, hcard] at this
    omega
  obtain ⟨a', ha', e', he', rfl⟩ := caseIa_mem_sup h.E_norm (hle hbB)
  by_cases ha'E : a' ∈ E
  · have hBE : A ⊓ E = B ⊓ E :=
      Subgroup.eq_of_le_of_card_ge (le_inf hA₀B inf_le_right) (by rw [hB.inf_card, hcard])
    exact hbn (by rw [hBE]; exact ⟨hbB, E.mul_mem ha'E he'⟩)
  · by_cases he'A : e' ∈ A
    · have hAB : A ⊓ E = A ⊓ B :=
        Subgroup.eq_of_le_of_card_ge (le_inf inf_le_left hA₀B) (by rw [h4, hcard])
      exact hbn (by rw [hAB]; exact ⟨A.mul_mem ha' he'A, hbB⟩)
    · have hsq := hB.sq _ hbB
      have hcomm : a' * e' = e' * a' :=
        calc a' * e' = (a' * e')⁻¹ := eq_inv_of_mul_eq_one_left hsq
          _ = e'⁻¹ * a'⁻¹ := mul_inv_rev _ _
          _ = e' * a' := by rw [h.E_inv he', h.A_inv ha']
      exact he'A ((h.caseI_cent_iff hcard ha' ha'E he').mp hcomm)

private theorem caseIa_inter_ne_four [Finite S] (hS : IsPGroup 2 S) {A E B : Subgroup S}
    (h : Cfg S A E) (hcard : Nat.card ↥(A ⊓ E) = 4)
    (hN : Nat.card ↥(Subgroup.normalizer (A : Set S)) = 64) (hB : CaseIaConj A E B) :
    Nat.card ↥(A ⊓ B) ≠ 4 := by
  intro h4
  have hEq := caseIa_sup_eq hS h hcard hN hB h4
  exact caseIa_not_le_sup h hcard hB h4 (by rw [hEq]; exact le_sup_right)

private theorem caseIa_inter_eq_two [Finite S] (hS : IsPGroup 2 S) {A E B : Subgroup S}
    (h : Cfg S A E) (hcard : Nat.card ↥(A ⊓ E) = 4)
    (hN : Nat.card ↥(Subgroup.normalizer (A : Set S)) = 64) (hB : CaseIaConj A E B) :
    Nat.card ↥(A ⊓ B) = 2 := by
  have hd : Nat.card ↥(A ⊓ B) ∣ 8 := by
    have := Subgroup.card_dvd_of_le (inf_le_left : A ⊓ B ≤ A)
    rwa [h.A_card] at this
  have h1 := caseIa_inter_ne_one h hB
  have h8 := caseIa_inter_ne_eight h hB
  have h4 := caseIa_inter_ne_four hS h hcard hN hB
  have hle : Nat.card ↥(A ⊓ B) ≤ 8 := Nat.le_of_dvd (by norm_num) hd
  have hpos : 0 < Nat.card ↥(A ⊓ B) := Nat.card_pos
  generalize Nat.card ↥(A ⊓ B) = n at *
  interval_cases n <;> omega

private theorem caseIa_inf_eq {A E B : Subgroup S} [Finite S] (h : Cfg S A E)
    (hB : CaseIaConj A E B) (h2 : Nat.card ↥(A ⊓ B) = 2) {z : S} (hz1 : z ≠ 1)
    (hzc : ∀ s : S, s * z = z * s) : ∀ x : S, (x ∈ A ∧ x ∈ B) ↔ (x = 1 ∨ x = z) := by
  have hzA : z ∈ A := h.A_cent z fun a _ => (hzc a).symm
  have hzB : z ∈ B := hB.cent z fun b _ => (hzc b).symm
  intro x
  constructor
  · intro hx
    exact eq_one_or_eq_of_card_two h2 (u := z) ⟨hzA, hzB⟩ hz1 x hx
  · rintro (hx | hx)
    · rw [hx]
      exact ⟨A.one_mem, B.one_mem⟩
    · rw [hx]
      exact ⟨hzA, hzB⟩

private theorem caseIa_mem_E [Finite S] {A E B : Subgroup S} (h : Cfg S A E)
    (hB : CaseIaConj A E B) {f₁ f₂ e₁ e₂ z : S} (hf₁ : f₁ ∈ A ⊓ E) (he₁ : e₁ ∈ B) (he₂ : e₂ ∈ B)
    (P : Pres e₁ e₂ f₁ f₂ z) : e₂ ∈ E := by
  have hle : B ⊓ E ≤ B ⊓ Subgroup.centralizer ({f₁} : Set S) := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_singleton_iff.mpr (h.E_comm x hx.2 f₁ hf₁.2)⟩
  have hcent : Nat.card ↥(B ⊓ Subgroup.centralizer ({f₁} : Set S)) = 4 := by
    refine card_centralizer_involution hB.comm hB.sq hB.card (fun x hx => ?_)
      (h.A_sq f₁ hf₁.1) ⟨e₁, he₁, fun hc => P.z_ne ?_⟩
    · exact hB.norm f₁ (Subgroup.le_normalizer hf₁.1) x hx
    · have h1 := P.e₁f₁
      rw [hc] at h1
      exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
  have heq : B ⊓ E = B ⊓ Subgroup.centralizer ({f₁} : Set S) :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hcent, hB.inf_card])
  have : e₂ ∈ B ⊓ Subgroup.centralizer ({f₁} : Set S) :=
    ⟨he₂, Subgroup.mem_centralizer_singleton_iff.mpr P.e₂f₁⟩
  rw [← heq] at this
  exact this.2

private theorem caseIa_final [Finite S] (hS : IsPGroup 2 S) {A E B : Subgroup S} (h : Cfg S A E)
    (hcard : Nat.card ↥(A ⊓ E) = 4) (hB : CaseIaConj A E B) (h2 : Nat.card ↥(A ⊓ B) = 2) :
    NoE32 S := by
  classical
  obtain ⟨z, hzE, hz1, hzc⟩ := h.exists_z hS
  have hz2 : z * z = 1 := h.E_sq z hzE
  have hAB := caseIa_inf_eq h hB h2 hz1 hzc
  have hzA : z ∈ A := h.A_cent z fun a _ => (hzc a).symm
  have hzB : z ∈ B := hB.cent z fun b _ => (hzc b).symm
  obtain ⟨f₁, hf₁, hf₁1, hf₁z⟩ : ∃ f₁ ∈ A ⊓ E, f₁ ≠ 1 ∧ f₁ ≠ z := by
    by_contra hno
    push Not at hno
    have h1 := caseIa_card_le_finset (A ⊓ E) ({1, z} : Finset S) (by
      intro x hx
      by_cases h1 : x = 1
      · simp [h1]
      · simp [hno x hx h1])
    have h2' : ({1, z} : Finset S).card ≤ 2 := Finset.card_le_two
    omega
  obtain ⟨f₂, hf₂, hf₂E⟩ : ∃ f₂ ∈ A, f₂ ∉ E := by
    by_contra hno
    push Not at hno
    have hle : A ≤ E := hno
    rw [inf_eq_left.mpr hle, h.A_card] at hcard
    omega
  have hnE : ∀ x ∈ E, f₂ ≠ x := fun x hx hEq => hf₂E (by rw [hEq]; exact hx)
  have hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a ∨ a * b = b * a * z := by
    intro a ha b hb
    have hc := caseIa_comm_mem_inf hB ha hb
    rcases eq_one_or_eq_of_card_two h2 (u := z) ⟨hzA, hzB⟩ hz1 _ hc with h' | h'
    · exact Or.inl (caseIa_comm_of_eq_one h')
    · refine Or.inr ?_
      calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
        _ = z * (b * a) := by rw [h']
        _ = b * a * z := (hzc (b * a)).symm
  obtain ⟨e₁, e₂, he₁, he₂, P, hcl⟩ := exists_hyperbolic_dual h.A_comm h.A_sq h.A_card hB.comm
    hB.sq hB.card hzc hz1 hz2 hAB hcomm
    (fun a ha hab => (hAB a).mp ⟨ha, hB.cent a hab⟩)
    (fun b hb hba => (hAB b).mp ⟨h.A_cent b fun a ha => (hba a ha).symm, hb⟩)
    hf₁.1 hf₂ ⟨hf₁1, hf₁z⟩
    ⟨hnE 1 E.one_mem, hnE z hzE, hnE f₁ hf₁.2, hnE (f₁ * z) (E.mul_mem hf₁.2 hzE)⟩
  have he₂E : e₂ ∈ E := caseIa_mem_E h hB hf₁ he₁ he₂ P
  refine noE32_of_pres hS h P.swap₁ hf₁.2 he₂E hzE fun a ha => ?_
  refine Subgroup.closure_mono ?_ (hcl a ha)
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
  tauto

theorem noE32_of_caseIa {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S) {A E : Subgroup S}
    (h : Cfg S A E) (hcard : Nat.card ↥(A ⊓ E) = 4)
    (hN : Nat.card ↥(Subgroup.normalizer (A : Set S)) = 64)
    (hNS : Subgroup.normalizer (A : Set S) ≠ ⊤) : NoE32 S := by
  obtain ⟨B, hB⟩ := caseIa_exists_conj hS h hcard hNS
  exact caseIa_final hS h hcard hB (caseIa_inter_eq_two hS h hcard hN hB)

end CFSG.OddStandard.Harada75
