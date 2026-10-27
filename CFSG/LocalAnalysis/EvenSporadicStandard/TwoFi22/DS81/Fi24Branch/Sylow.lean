module

public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch.Facts

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch

open Subgroup CFSG.Blueprint.NativeSporadic

variable {G : Type} [Group G] [Finite G] {E : Subgroup G} {t : G}

theorem sq_eq_one_comm {H : Subgroup G} (hH : ∀ a ∈ H, a ^ 2 = 1) :
    ∀ a ∈ H, ∀ b ∈ H, a * b = b * a := by
  intro a ha b hb
  have ha' : a⁻¹ = a := by
    have h : a * a = 1 := by simpa [pow_two] using hH a ha
    exact (mul_eq_one_iff_eq_inv.mp h).symm
  have hb' : b⁻¹ = b := by
    have h : b * b = 1 := by simpa [pow_two] using hH b hb
    exact (mul_eq_one_iff_eq_inv.mp h).symm
  have hab : a * b = (a * b)⁻¹ := by
    have h : (a * b) * (a * b) = 1 := by simpa [pow_two] using hH (a * b) (mul_mem ha hb)
    exact mul_eq_one_iff_eq_inv.mp h
  rw [mul_inv_rev, ha', hb'] at hab
  exact hab

theorem card_Nrm (h : M24Out G E t) :
    Nat.card ↥(Nrm E) = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 := by
  have hquot : Nat.card (↥(Nrm E) ⧸ E.subgroupOf (Nrm E)) = 244823040 := by
    obtain ⟨e⟩ := h.quotient
    refine (Nat.card_congr e.toEquiv).trans ?_
    change Nat.card ↥CFSG.Blueprint.NativeSporadic.M24 = 244823040
    exact CFSG.Sporadic.Mathieu.card_M24
  have hsub : Nat.card (E.subgroupOf (Nrm E)) = 2 ^ 11 := by
    change Nat.card (E.subgroupOf (normalizer (E : Set G))) = 2 ^ 11
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe Subgroup.le_normalizer).toEquiv]
    exact h.card_E
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (E.subgroupOf (Nrm E)), hquot, hsub]
  norm_num

theorem eq_of_elementary (hC : CocodeFacts) (h : M24Out G E t) {A : Subgroup G}
    (hAN : A ≤ Nrm E) (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA : Nat.card ↥A = 2 ^ 11) : A = E := by
  by_cases hAE : A ≤ E
  · exact Subgroup.eq_of_le_of_card_ge hAE (by rw [hA, h.card_E])
  · exfalso
    have hno := hC.noOffender G E t h A hAN hA2 hAc hAE
    have hAle : A ≤ centralizer (A : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hAc a ha b hb).symm
    have hcard_le : Nat.card ↥(A ⊓ E) ≤ Nat.card ↥(E ⊓ centralizer (A : Set G)) :=
      Subgroup.card_le_of_le (by
        intro x hx
        exact ⟨hx.2, hAle hx.1⟩)
    have hmul := Subgroup.relIndex_mul_card (H := A ⊓ E) (K := A)
    rw [inf_eq_left.mpr inf_le_left] at hmul
    have hcardA : Nat.card ↥A ≤ 2 ^ 10 := by
      calc Nat.card ↥A = (A ⊓ E).relIndex A * Nat.card ↥(A ⊓ E) := hmul.symm
        _ ≤ (A ⊓ E).relIndex A * Nat.card ↥(E ⊓ centralizer (A : Set G)) :=
            Nat.mul_le_mul_left _ hcard_le
        _ ≤ 2 ^ 10 := hno
    have : (2 : ℕ) ^ 11 ≤ 2 ^ 10 := hA ▸ hcardA
    norm_num at this

theorem eq_of_sylow_le (hC : CocodeFacts) (h : M24Out G E t) (T : Sylow 2 ↥(Nrm E))
    {T₁ : Subgroup G} (hT₁ : IsPGroup 2 ↥T₁)
    (hle : (T : Subgroup ↥(Nrm E)).map (Nrm E).subtype ≤ T₁) :
    (T : Subgroup ↥(Nrm E)).map (Nrm E).subtype = T₁ := by
  set T' : Subgroup G := (T : Subgroup ↥(Nrm E)).map (Nrm E).subtype with hT'def
  have hle' : T' ≤ T₁ := by rw [hT'def]; exact hle
  have hT'_le_N : T' ≤ Nrm E := by
    rw [hT'def]; exact Subgroup.map_subtype_le (T : Subgroup ↥(Nrm E))
  have hE_le_T' : E ≤ T' := by
    have hp : IsPGroup 2 (E.subgroupOf (Nrm E)) := by
      have hE2 : IsPGroup 2 (E : Subgroup G) := IsPGroup.of_card h.card_E
      exact hE2.of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.le_normalizer : E ≤ Nrm E)).symm
    haveI hN : (E.subgroupOf (Nrm E)).Normal := by
      unfold Nrm
      infer_instance
    have h2 : E.subgroupOf (Nrm E) ≤ (T : Subgroup ↥(Nrm E)) :=
      IsPGroup.le_sylow_of_normal hp T
    calc E = (E.subgroupOf (Nrm E)).map (Nrm E).subtype :=
          (Subgroup.map_subgroupOf_eq_of_le Subgroup.le_normalizer).symm
      _ ≤ T' := by rw [hT'def]; exact Subgroup.map_mono h2
  by_contra hne
  have hlt : T'.subgroupOf T₁ < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne (le_antisymm hle' fun y hy => ?_)
    have : (⟨y, hy⟩ : ↥T₁) ∈ T'.subgroupOf T₁ := htop ▸ mem_top _
    exact this
  haveI : Finite ↥T₁ := inferInstance
  haveI : Group.IsNilpotent ↥T₁ := hT₁.isNilpotent
  obtain ⟨n, hnN, hnT'⟩ :=
    IsConcreteLE.exists_of_lt
      (Group.normalizerCondition_of_isNilpotent (G := ↥T₁) (T'.subgroupOf T₁) hlt)
  have hnT'g : (n : G) ∉ T' := fun h => hnT' (by simpa [Subgroup.mem_subgroupOf] using h)
  have hnorm : ∀ s : G, s ∈ T' ↔ (n : G) * s * (n : G)⁻¹ ∈ T' := by
    intro s
    constructor
    · intro hs
      have := (mem_normalizer_iff.mp hnN ⟨s, hle' hs⟩).mp hs
      simpa [Subgroup.mem_subgroupOf] using this
    · intro hs
      have hsT : s ∈ T₁ := by
        have h1 : (n : G) * s * (n : G)⁻¹ ∈ T₁ := hle' hs
        have := T₁.mul_mem (T₁.mul_mem (T₁.inv_mem n.2) h1) n.2
        simpa [mul_assoc] using this
      have := (mem_normalizer_iff.mp hnN ⟨s, hsT⟩).mpr (by simpa [Subgroup.mem_subgroupOf] using hs)
      simpa [Subgroup.mem_subgroupOf] using this
  have hA_le_T' : E.map (MulAut.conj (n : G)).toMonoidHom ≤ T' := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨e, he, rfl⟩
    show (n : G) * e * (n : G)⁻¹ ∈ T'
    exact (hnorm e).mp (hE_le_T' he)
  have hA2 : ∀ a ∈ E.map (MulAut.conj (n : G)).toMonoidHom, a ^ 2 = 1 := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨e, he, rfl⟩
    rw [← map_pow, h.E_sq e he, map_one]
  have hAc := sq_eq_one_comm hA2
  have hcardA : Nat.card ↥(E.map (MulAut.conj (n : G)).toMonoidHom) = 2 ^ 11 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (n : G)).injective, h.card_E]
  have hAeqE : E.map (MulAut.conj (n : G)).toMonoidHom = E :=
    eq_of_elementary hC h (hA_le_T'.trans hT'_le_N) hA2 hAc hcardA
  have hx_norm : (n : G) ∈ Nrm E := by
    rw [Nrm, Subgroup.mem_normalizer_iff_map_conj_eq]
    simpa using hAeqE
  have hK_eq : (T₁ ⊓ Nrm E).subgroupOf (Nrm E) = (T : Subgroup ↥(Nrm E)) := by
    refine T.is_maximal' ?_ ?_
    · have h1 : IsPGroup 2 (T₁ ⊓ Nrm E : Subgroup G) :=
        (hT₁ : IsPGroup 2 (T₁ : Subgroup G)).to_inf_left
      exact h1.of_equiv (Subgroup.subgroupOfEquivOfLe (inf_le_right : T₁ ⊓ Nrm E ≤ Nrm E)).symm
    · intro x hx
      rw [Subgroup.mem_subgroupOf]
      exact ⟨hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩), x.2⟩
  have hEq : T₁ ⊓ Nrm E = T' := by
    have h1 := congrArg (Subgroup.map (Nrm E).subtype) hK_eq
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right, ← hT'def] at h1
    exact h1
  exact hnT'g (by rw [← hEq]; exact ⟨n.2, hx_norm⟩)

theorem card_sylow (hC : CocodeFacts) (h : M24Out G E t)
    (S : Sylow 2 G) : Nat.card ↥S = 2 ^ 21 := by
  obtain ⟨T : Sylow 2 ↥(Nrm E)⟩ := (Sylow.nonempty : Nonempty (Sylow 2 ↥(Nrm E)))
  have hT'p : IsPGroup 2 ((T : Subgroup ↥(Nrm E)).map (Nrm E).subtype) :=
    T.isPGroup'.map (Nrm E).subtype
  obtain ⟨S', hS'le⟩ := hT'p.exists_le_sylow
  have heq : (T : Subgroup ↥(Nrm E)).map (Nrm E).subtype = (S' : Subgroup G) :=
    eq_of_sylow_le hC h T S'.isPGroup' hS'le
  have hfacN : (Nat.card ↥(Nrm E)).factorization 2 = 21 := by
    rw [card_Nrm h]
    rw [show 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 = 2 ^ 21 * (3 ^ 3 * 5 * 7 * 11 * 23) by ring]
    have hcop : Nat.Coprime (2 ^ 21) (3 ^ 3 * 5 * 7 * 11 * 23) := by norm_num
    rw [Nat.factorization_mul_apply_of_coprime hcop,
      Nat.factorization_pow_self (by norm_num : Nat.Prime 2),
      Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 3 ^ 3 * 5 * 7 * 11 * 23)]
  have hcardT : Nat.card ↥T = 2 ^ 21 :=
    (Sylow.card_eq_multiplicity T).trans (by rw [hfacN])
  have hcardS' : Nat.card ↥S' = 2 ^ 21 := by
    have h1 : Nat.card ↥((T : Subgroup ↥(Nrm E)).map (Nrm E).subtype) = 2 ^ 21 :=
      (Subgroup.card_map_of_injective (Nrm E).subtype_injective).trans hcardT
    exact (congrArg (fun H : Subgroup G => Nat.card ↥H) heq).symm.trans h1
  calc Nat.card ↥S = 2 ^ (Nat.card G).factorization 2 := Sylow.card_eq_multiplicity S
    _ = Nat.card ↥S' := (Sylow.card_eq_multiplicity S').symm
    _ = 2 ^ 21 := hcardS'

end CFSG.EvenSporadicStandard.TwoFi22.DS81.Fi24Branch
