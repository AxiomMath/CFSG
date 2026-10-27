module

public import CFSG.LocalAnalysis.OddStandard.Harada75Basic
public import CFSG.LocalAnalysis.OddStandard.Harada75Rank

public section

namespace CFSG.OddStandard.Harada75

open Subgroup
open scoped commutatorElement

section CaseIc

variable {S : Type} [Group S]

private theorem caseIc_step_one [Finite S] {A E : Subgroup S} (h : Cfg S A E)
    {T U : Subgroup S}
    (hQ3 : Nat.card T * Nat.card ↥(U ⊓ E) ≤ 4 * Nat.card U * Nat.card ↥(T ⊓ E))
    (hT : Nat.card T = 32 * Nat.card U) : E ≤ T ∧ U ⊓ E = ⊥ := by
  have hU : 0 < Nat.card U := Nat.card_pos
  have hUE : 0 < Nat.card ↥(U ⊓ E) := Nat.card_pos
  have hTE : Nat.card ↥(T ⊓ E) ≤ 8 := by
    have := Subgroup.card_le_of_le (inf_le_right : T ⊓ E ≤ E)
    rwa [h.E_card] at this
  rw [hT] at hQ3
  have h1 : (4 * Nat.card U) * (8 * Nat.card ↥(U ⊓ E)) ≤
      (4 * Nat.card U) * Nat.card ↥(T ⊓ E) :=
    calc (4 * Nat.card U) * (8 * Nat.card ↥(U ⊓ E))
        = 32 * Nat.card U * Nat.card ↥(U ⊓ E) := by ring
      _ ≤ 4 * Nat.card U * Nat.card ↥(T ⊓ E) := hQ3
  have h2 := Nat.le_of_mul_le_mul_left h1 (by omega)
  have hUE1 : Nat.card ↥(U ⊓ E) = 1 := by omega
  have hTE8 : Nat.card ↥(T ⊓ E) = 8 := by omega
  refine ⟨?_, Subgroup.card_eq_one.mp hUE1⟩
  have h3 : T ⊓ E = E := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hTE8, h.E_card])
  calc E = T ⊓ E := h3.symm
    _ ≤ T := inf_le_left

private theorem caseIc_cent {A E : Subgroup S} (h : Cfg S A E) {T U : Subgroup S}
    (hET : E ≤ T) (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) (hUE : U ⊓ E = ⊥) :
    ∀ x ∈ T, ∀ e ∈ E, x * e = e * x := by
  intro x hx e he
  have h1 : ⁅x, e⁆ ∈ U := hcomm x hx e (hET he)
  have h2 : ⁅x, e⁆ ∈ E := by
    rw [commutatorElement_def]
    exact E.mul_mem (h.E_norm x e he) (E.inv_mem he)
  have h3 : ⁅x, e⁆ ∈ U ⊓ E := ⟨h1, h2⟩
  rw [hUE, Subgroup.mem_bot] at h3
  exact commutatorElement_eq_one_iff_mul_comm.mp h3

private theorem caseIc_K_elem {E K T U : Subgroup S} (hKT : K ≤ T)
    (hKsq : ∀ x ∈ K, x * x ∈ E) (hKcomm : ∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ E)
    (hsq : ∀ x ∈ T, x ^ 2 ∈ U) (hcomm : ∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) (hUE : U ⊓ E = ⊥) :
    (∀ x ∈ K, x * x = 1) ∧ (∀ x ∈ K, ∀ y ∈ K, x * y = y * x) := by
  refine ⟨fun x hx => ?_, fun x hx y hy => ?_⟩
  · have h1 : x * x ∈ U ⊓ E := ⟨by rw [← pow_two]; exact hsq x (hKT hx), hKsq x hx⟩
    rw [hUE, Subgroup.mem_bot] at h1
    exact h1
  · have h1 : ⁅x, y⁆ ∈ U ⊓ E := ⟨hcomm x (hKT hx) y (hKT hy), hKcomm x hx y hy⟩
    rw [hUE, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1

private structure CaseIcData (A E K : Subgroup S) (a : S) : Prop where
  cfg : Cfg S A E
  card : Nat.card ↥(A ⊓ E) = 4
  EK : E ≤ K
  Kn : K.Normal
  Kcard : Nat.card K = 2 * Nat.card E
  KE : ∀ k ∈ K, ∀ e ∈ E, k * e = e * k
  K2 : ∀ x ∈ K, x * x = 1
  Kc : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x
  a_mem : a ∈ A
  a_notE : a ∉ E
  a_notK : a ∉ K

section Data

variable [Finite S] {A E K : Subgroup S} {a : S}

private theorem caseIc_A_cases (D : CaseIcData A E K a) {a' : S} (ha' : a' ∈ A) :
    a' ∈ E ∨ ∃ e ∈ A ⊓ E, a' = a * e := by
  by_cases hE : a' ∈ E
  · exact Or.inl hE
  · refine Or.inr ⟨a⁻¹ * a', ?_, by group⟩
    exact inv_mul_mem_of_card (H := A ⊓ E) (K := A) inf_le_left
      (by rw [D.cfg.A_card, D.card]) D.a_mem ha' (fun h' => D.a_notE h'.2) (fun h' => hE h'.2)

private theorem caseIc_comm_all (D : CaseIcData A E K a) {x : S} (hxa : x * a = a * x)
    (hxE : ∀ e ∈ A ⊓ E, x * e = e * x) : ∀ a' ∈ A, x * a' = a' * x := by
  intro a' ha'
  rcases caseIc_A_cases D ha' with hE | ⟨e, he, rfl⟩
  · exact hxE a' ⟨ha', hE⟩
  · calc x * (a * e) = (x * a) * e := by group
      _ = (a * x) * e := by rw [hxa]
      _ = a * (x * e) := by group
      _ = a * (e * x) := by rw [hxE e he]
      _ = a * e * x := by group

private theorem caseIc_mem_of_comm (D : CaseIcData A E K a) {k : S} (hk : k ∈ K)
    (hka : a * k = k * a) : k ∈ A ⊓ E := by
  have hkA : k ∈ A :=
    D.cfg.A_cent k (caseIc_comm_all D hka.symm fun e he => D.KE k hk e he.2)
  refine ⟨hkA, ?_⟩
  by_contra hkE
  obtain ⟨x, hx, hne⟩ := D.cfg.caseI_noncomm D.card hkA hkE
  exact hne (D.KE k hk x hx)

private theorem caseIc_exists_y (D : CaseIcData A E K a) {k₁ : S} (hk₁ : k₁ ∈ A ⊓ E) :
    ∃ y ∈ K, y * (a * y * a⁻¹) = k₁ := by
  have hKa : ∀ x ∈ K, a * x * a⁻¹ ∈ K := fun x hx => D.Kn.conj_mem x hx a
  have ha2 : a * a = 1 := D.cfg.A_sq a D.a_mem
  have hker : Nat.card (invMap K a D.Kc hKa).ker = 4 := by
    refine Eq.trans (Nat.card_congr
      { toFun := fun x => ⟨x.1.1, caseIc_mem_of_comm D x.1.2
          ((mem_ker_invMap K a D.Kc D.K2 hKa x.1).mp x.2)⟩
        invFun := fun x => ⟨⟨x.1, D.EK x.2.2⟩,
          (mem_ker_invMap K a D.Kc D.K2 hKa ⟨x.1, D.EK x.2.2⟩).mpr
            (D.cfg.A_comm a D.a_mem x.1 x.2.1)⟩
        left_inv := fun x => rfl
        right_inv := fun x => rfl }) D.card
  have h1 := Subgroup.card_ker_mul_card_range (invMap K a D.Kc hKa)
  have hK16 : Nat.card K = 16 := by rw [D.Kcard, D.cfg.E_card]
  rw [hker, hK16] at h1
  have hrange : Nat.card (invMap K a D.Kc hKa).range = 4 := by omega
  have hle := range_invMap_le_ker K a D.Kc D.K2 ha2 hKa
  have heq : (invMap K a D.Kc hKa).range = (invMap K a D.Kc hKa).ker :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [hker, hrange])
  have hmem : (⟨k₁, D.EK hk₁.2⟩ : K) ∈ (invMap K a D.Kc hKa).ker :=
    (mem_ker_invMap K a D.Kc D.K2 hKa _).mpr (D.cfg.A_comm a D.a_mem k₁ hk₁.1)
  rw [← heq] at hmem
  obtain ⟨y, hy⟩ := hmem
  exact ⟨y.1, y.2, congrArg Subtype.val hy⟩

private theorem caseIc_W_cases (D : CaseIcData A E K a) {x : S} (hx : x ∈ K ⊔ A) :
    x ∈ K ∨ ∃ k₁ ∈ K, x = a * k₁ := by
  have := D.Kn
  have hx' : x ∈ (↑(K ⊔ A) : Set S) := hx
  rw [Subgroup.normal_mul K A] at hx'
  obtain ⟨k, hk, a', ha', rfl⟩ := hx'
  rcases caseIc_A_cases D ha' with hE | ⟨e, he, rfl⟩
  · exact Or.inl (K.mul_mem hk (D.EK hE))
  · exact Or.inr ⟨a⁻¹ * k * a * e, K.mul_mem (D.Kn.conj_mem' k hk a) (D.EK he.2), by group⟩

private theorem caseIc_sup_eq (hS : IsPGroup 2 S) (D : CaseIcData A E K a) :
    K ⊔ A = Subgroup.centralizer ((A ⊓ E : Subgroup S) : Set S) := by
  have hWC : K ⊔ A ≤ Subgroup.centralizer ((A ⊓ E : Subgroup S) : Set S) := by
    refine sup_le (fun k hk => ?_) (fun a' ha' => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      exact fun x hx => (D.KE k hk x hx.2).symm
    · rw [Subgroup.mem_centralizer_iff]
      exact fun x hx => D.cfg.A_comm x hx.1 a' ha'
  by_contra hne
  obtain ⟨t, htC, htW, hconj⟩ := exists_mem_normalizer_not_mem hS hWC hne
  have ha2 : a * a = 1 := D.cfg.A_sq a D.a_mem
  have haW : a ∈ K ⊔ A := Subgroup.mem_sup_right D.a_mem
  have h1 : t * a * t⁻¹ ∈ K ⊔ A := (hconj a (hWC haW)).mp haW
  have hnot : t * a * t⁻¹ ∉ K := by
    intro hK
    apply D.a_notK
    have h2 := D.Kn.conj_mem' _ hK t
    have e : t⁻¹ * (t * a * t⁻¹) * t = a := by group
    rwa [e] at h2
  obtain ⟨k₁, hk₁, hk₁eq⟩ : ∃ k₁ ∈ K, t * a * t⁻¹ = a * k₁ := by
    rcases caseIc_W_cases D h1 with hK | ⟨k₁, hk₁, he⟩
    · exact absurd hK hnot
    · exact ⟨k₁, hk₁, he⟩
  have hsq : a * k₁ * (a * k₁) = 1 := by
    rw [← hk₁eq]
    calc t * a * t⁻¹ * (t * a * t⁻¹) = t * (a * a) * t⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hk₁inv : k₁⁻¹ = k₁ := inv_eq_of_mul_eq_one_right (D.K2 k₁ hk₁)
  have hak : a * k₁ = k₁ * a := by
    have h3 : a * k₁ * a = k₁⁻¹ := eq_inv_of_mul_eq_one_left (by rw [← hsq]; group)
    calc a * k₁ = a * k₁ * a * a := by rw [mul_assoc (a * k₁) a a, ha2, mul_one]
      _ = k₁ * a := by rw [h3, hk₁inv]
  obtain ⟨y, hy, hyeq⟩ := caseIc_exists_y D (caseIc_mem_of_comm D hk₁ hak)
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right (D.K2 y hy)
  have h4 : t * a * t⁻¹ = y * a * y := by
    rw [hk₁eq, hak, ← hyeq]
    group
  have key : y⁻¹ * t * a = a * (y⁻¹ * t) := by
    have h5 : t * a = y * a * y * t := by
      calc t * a = (t * a * t⁻¹) * t := by group
        _ = y * a * y * t := by rw [h4]
    calc y⁻¹ * t * a = y⁻¹ * (t * a) := by group
      _ = y⁻¹ * (y * a * y * t) := by rw [h5]
      _ = a * y * t := by group
      _ = a * (y⁻¹ * t) := by rw [hyinv]; group
  have hE : ∀ e ∈ A ⊓ E, y⁻¹ * t * e = e * (y⁻¹ * t) := by
    intro e he
    have h6 : e * t = t * e := Subgroup.mem_centralizer_iff.mp htC e he
    have h7 : y⁻¹ * e = e * y⁻¹ := D.KE y⁻¹ (K.inv_mem hy) e he.2
    calc y⁻¹ * t * e = y⁻¹ * (t * e) := by group
      _ = y⁻¹ * (e * t) := by rw [h6]
      _ = (y⁻¹ * e) * t := by group
      _ = (e * y⁻¹) * t := by rw [h7]
      _ = e * (y⁻¹ * t) := by group
  have hA : y⁻¹ * t ∈ A := D.cfg.A_cent _ (caseIc_comm_all D key hE)
  apply htW
  have := Subgroup.mul_mem_sup hy hA
  rwa [mul_inv_cancel_left] at this

end Data

end CaseIc

theorem noE32_of_caseIc_aux {S : Type} [Group S] [Finite S] (hS : IsPGroup 2 S)
    {A E : Subgroup S} (h : Cfg S A E) (hcard : Nat.card ↥(A ⊓ E) = 4)
    (hsuz : ∃ K : Subgroup S, E ≤ K ∧ K.Normal ∧ Nat.card K = 2 * Nat.card E ∧
      (∀ x ∈ K, x * x ∈ E) ∧ (∀ x ∈ K, ∀ y ∈ K, ⁅x, y⁆ ∈ E) ∧
      (∀ T : Subgroup S, E ≤ T → 4 * Nat.card E ≤ Nat.card T → K ≤ T) ∧
      (∀ T U : Subgroup S, U ≤ T → (∀ x ∈ T, x ^ 2 ∈ U) →
        (∀ x ∈ T, ∀ y ∈ T, ⁅x, y⁆ ∈ U) →
        Nat.card T * Nat.card ↥(U ⊓ E) ≤ 4 * Nat.card U * Nat.card ↥(T ⊓ E))) :
    NoE32 S := by
  obtain ⟨K, hEK, hKn, hKcard, hKsq, hKcomm, hQ2, hQ3⟩ := hsuz
  intro T U hsec
  obtain ⟨hUT, hsq, hcomm, hT⟩ := hsec
  obtain ⟨hET, hUE⟩ := caseIc_step_one h (hQ3 T U hUT hsq hcomm) hT
  have hTE := caseIc_cent h hET hcomm hUE
  have hUpos : 0 < Nat.card U := Nat.card_pos
  have hKT : K ≤ T := hQ2 T hET (by rw [h.E_card, hT]; omega)
  obtain ⟨hK2, hKc⟩ := caseIc_K_elem hKT hKsq hKcomm hsq hcomm hUE
  obtain ⟨a, haA, haE⟩ : ∃ a ∈ A, a ∉ E := by
    by_contra hno
    push Not at hno
    have hAE : A ≤ E := hno
    have h1 : A ⊓ E = A := inf_eq_left.mpr hAE
    rw [h1, h.A_card] at hcard
    omega
  have haT : a ∉ T := by
    intro haT
    obtain ⟨x, hx, hne⟩ := h.caseI_noncomm hcard haA haE
    exact hne (hTE a haT x hx)
  have haK : a ∉ K := fun haK => haT (hKT haK)
  have D : CaseIcData A E K a :=
    ⟨h, hcard, hEK, hKn, hKcard, fun k hk e he => hTE k (hKT hk) e he, hK2, hKc, haA, haE, haK⟩
  have hsup := caseIc_sup_eq hS D
  have hTK : T ≤ K := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer ((A ⊓ E : Subgroup S) : Set S) :=
      Subgroup.mem_centralizer_iff.mpr fun e he => (hTE x hx e he.2).symm
    rw [← hsup] at hxC
    rcases caseIc_W_cases D hxC with hxK | ⟨k₁, hk₁, rfl⟩
    · exact hxK
    · exact absurd (by simpa using T.mul_mem hx (T.inv_mem (hKT hk₁))) haT
  have hle := Subgroup.card_le_of_le hTK
  rw [hT, hKcard, h.E_card] at hle
  omega

end CFSG.OddStandard.Harada75
