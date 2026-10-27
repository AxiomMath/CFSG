module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7C2
public import CFSG.LocalAnalysis.ComponentClassification.HSFLitA7TFacts

public section

namespace CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv CFSG.ComponentClassification.UnbalancedLayer

namespace A7Base

variable {X : Type} [Group X] [Finite X] {S : A7Base X}

namespace Case2

variable (C : S.Case2)

theorem eq_E_of_le_centralizer {P : Subgroup X} (hP : IsPGroup 2 P) (hEP : S.E C.yb ≤ P)
    (hPC : P ≤ centralizer (S.E C.yb : Set X)) : P = S.E C.yb := by
  have hPt : P ≤ centralizer ({S.t} : Set X) := by
    intro p hp
    rw [mem_centralizer_singleton_iff]
    exact ((mem_centralizer_iff.mp (hPC hp)) S.t C.t_mem_E).symm
  obtain ⟨m, hm, hmP⟩ := S.data.exists_conj_le_T hP hPt
  set E' : Subgroup X := (S.E C.yb).map (MulAut.conj m).toMonoidHom with hE'
  have hE'T : E' ≤ S.data.T := fun a ha => hmP (Subgroup.map_mono hEP ha)
  have hE'el : ElemAbelianTwo E' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, C.comm ha hb]
    · rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_pow, S.E_sq C.yb_mem C.yb_sq ha, map_one]
  have hE'c : Nat.card E' = 16 := by
    rw [hE', card_map_of_injective (MulAut.conj m).injective, C.card_E]
  have hcases := S.eq_E_of_elem hE'T hE'el hE'c
  have hPm : P.map (MulAut.conj m).toMonoidHom ≤ E' := by
    rintro _ ⟨p, hp, rfl⟩
    have hpT := hmP ⟨p, hp, rfl⟩
    have hc : ∀ e ∈ E', (MulAut.conj m).toMonoidHom p * e = e * (MulAut.conj m).toMonoidHom p := by
      rintro _ ⟨a, ha, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul, (mem_centralizer_iff.mp (hPC hp)) a ha]
    rcases hcases with h | h
    · rw [h] at hc ⊢
      exact S.mem_E_of_commute (Or.inl rfl) hpT hc
    · rw [h] at hc ⊢
      exact S.mem_E_of_commute (Or.inr rfl) hpT hc
  apply le_antisymm _ hEP
  have hcard : Nat.card P ≤ Nat.card (S.E C.yb) := by
    have h1 : Nat.card (P.map (MulAut.conj m).toMonoidHom) = Nat.card P :=
      card_map_of_injective (MulAut.conj m).injective
    rw [← h1, C.card_E, ← hE'c]
    exact Subgroup.card_le_of_le hPm
  have := Subgroup.eq_of_le_of_card_ge hEP hcard
  rw [this]

theorem exists_V : ∃ V : Subgroup X, IsPGroup 2 V ∧ C.T₁ ≤ V ∧
    V ≤ normalizer (S.E C.yb : Set X) ∧ Nat.card V = 4 * Nat.card S.data.T ∧
    (∀ Q : Subgroup X, IsPGroup 2 Q → V ≤ Q → Q ≤ normalizer (S.E C.yb : Set X) → Q = V) ∧
    ∀ v ∈ V, (∀ e ∈ S.E C.yb, v * e = e * v) → v ∈ S.E C.yb := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (S.E C.yb : Set X) with hN
  have hT₁N : C.T₁ ≤ N := C.T₁_le_normalizer
  have hT₁' : IsPGroup 2 (C.T₁.subgroupOf N) := C.T₁_p.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hT₁'.exists_le_sylow
  set V : Subgroup X := (Q : Subgroup N).map N.subtype with hV
  have hVp : IsPGroup 2 V := Q.isPGroup'.map _
  have hVN : V ≤ N := map_subtype_le _
  have hT₁V : C.T₁ ≤ V := fun g hg => ⟨⟨g, hT₁N hg⟩, hQ hg, rfl⟩
  have hcardV : Nat.card V = 2 ^ (Nat.card N).factorization 2 := by
    rw [hV, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity]
  have hTN : S.data.T ≤ N ⊓ centralizer ({S.t} : Set X) :=
    le_inf (C.T_le.trans hT₁N) S.data.T_le_centralizer
  have hTC := S.card_T_eq_of_le hTN inf_le_right
  have hmul := card_eq_mul_two_pow (P := V) (Q := S.data.T) inf_le_left hcardV hTC
  rw [relIndex_inf_centralizer_eq_ncard, C.ncard_orbit,
    show (4 : ℕ).factorization 2 = 2 by
      rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp] at hmul
  refine ⟨V, hVp, hT₁V, hVN, by rw [hmul]; ring, fun Q' hQ' hle hQ'N => ?_, fun v hv hc => ?_⟩
  · refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    obtain ⟨m, hm⟩ := hQ'.exists_card_eq
    have hdvd : Nat.card Q' ∣ Nat.card N := Subgroup.card_dvd_of_le hQ'N
    rw [hm] at hdvd ⊢
    rw [hcardV]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd)
  · have hEV : S.E C.yb ≤ V := C.E_le_T.trans (C.T_le.trans hT₁V)
    have hEP : S.E C.yb ≤ V ⊓ centralizer (S.E C.yb : Set X) := le_inf hEV fun e he =>
      mem_centralizer_iff.mpr fun e' he' => C.comm he' he
    have hPeq := C.eq_E_of_le_centralizer (hVp.to_le inf_le_left) hEP inf_le_right
    have hvP : v ∈ V ⊓ centralizer (S.E C.yb : Set X) :=
      ⟨hv, mem_centralizer_iff.mpr fun e he => (hc e he).symm⟩
    rw [hPeq] at hvP
    exact hvP

end Case2

end A7Base

end CFSG.ComponentClassification.HSFLit
