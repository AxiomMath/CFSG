module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitConjOrbit
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46T
public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.SDSyl

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

@[expose] def cls (t b : X) : Set X := {a | ∃ g ∈ centralizer ({t} : Set X), g * b * g⁻¹ = a}

omit [Finite X] in
theorem mem_cls_self (b : X) : b ∈ cls t b := ⟨1, one_mem _, by group⟩

omit [Finite X] in
theorem cls_eq_of_mem {a b : X} (h : a ∈ cls t b) : cls t a = cls t b := by
  obtain ⟨g, hg, rfl⟩ := h
  ext c
  constructor
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g' * g, mul_mem hg' hg, by group⟩
  · rintro ⟨g', hg', rfl⟩
    exact ⟨g' * g⁻¹, mul_mem hg' (inv_mem hg), by group⟩

omit [Finite X] in
theorem cls_t_mul (b : X) : cls t (t * b) = (fun a => t * a) '' cls t b := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨g * b * g⁻¹, ⟨g, hg, rfl⟩, ?_⟩
    have := mem_centralizer_singleton_iff.mp hg
    calc t * (g * b * g⁻¹) = (t * g) * b * g⁻¹ := by group
      _ = g * t * b * g⁻¹ := by rw [← this]
      _ = g * (t * b) * g⁻¹ := by group
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨g, hg, ?_⟩
    have := mem_centralizer_singleton_iff.mp hg
    calc g * (t * b) * g⁻¹ = g * t * b * g⁻¹ := by group
      _ = t * g * b * g⁻¹ := by rw [this]
      _ = t * (g * b * g⁻¹) := by group

omit [Finite X] in
theorem ncard_cls_t_mul (b : X) : (cls t (t * b)).ncard = (cls t b).ncard := by
  rw [cls_t_mul, Set.ncard_image_of_injective _ (mul_right_injective t)]

omit [Finite X] in
theorem ncard_cls_eq (b : X) :
    (cls t b).ncard = (centralizer ({t} : Set X) ⊓ centralizer ({b} : Set X)).relIndex
      (centralizer ({t} : Set X)) :=
  (relIndex_inf_centralizer_eq_ncard _ b).symm

theorem odd_ncard_cls {b : X} (hTb : A.T ≤ centralizer ({b} : Set X)) : Odd (cls t b).ncard := by
  rw [ncard_cls_eq]
  set H := centralizer ({t} : Set X) ⊓ centralizer ({b} : Set X) with hH
  have hTH : A.T ≤ H := le_inf A.T_le_centralizer hTb
  have h1 := card_T_eq_two_pow (A := A)
  have h2 := card_T_eq_of_le (A := A) hTH inf_le_left
  have h3 := card_eq_mul_two_pow (P := A.T) (Q := A.T) (inf_le_left : H ≤ _) h1 h2
  have hpos : 0 < Nat.card A.T := Nat.card_pos
  have h4 : 2 ^ (H.relIndex (centralizer ({t} : Set X))).factorization 2 = 1 := by
    have : Nat.card A.T * 2 ^ (H.relIndex (centralizer ({t} : Set X))).factorization 2 =
        Nat.card A.T * 1 := by rw [mul_one]; exact h3.symm
    exact Nat.eq_of_mul_eq_mul_left hpos this
  have h5 : (H.relIndex (centralizer ({t} : Set X))).factorization 2 = 0 := by
    rcases Nat.eq_zero_or_pos ((H.relIndex (centralizer ({t} : Set X))).factorization 2) with h | h
    · exact h
    · exfalso
      have : 2 ≤ 2 ^ (H.relIndex (centralizer ({t} : Set X))).factorization 2 :=
        Nat.le_self_pow (by omega) 2
      omega
  have h6 : H.relIndex (centralizer ({t} : Set X)) ≠ 0 := by
    intro h0
    have := relIndex_mul_card H (centralizer ({t} : Set X))
    rw [h0, zero_mul] at this
    exact Nat.card_pos.ne' this.symm
  rw [Nat.odd_iff]
  by_contra hne
  have h2d : 2 ∣ H.relIndex (centralizer ({t} : Set X)) := by omega
  have := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two h6).mp h2d
  omega

theorem odd_ncard_cls_z : Odd (cls t S.z).ncard :=
  odd_ncard_cls fun _ hg => mem_centralizer_singleton_iff.mpr (z_comm S hg).symm

theorem odd_ncard_cls_tz : Odd (cls t (t * S.z)).ncard := by
  rw [ncard_cls_t_mul]
  exact odd_ncard_cls_z S

theorem ncard_cls_k : (cls t S.k).ncard ≡ 2 [MOD 4] := S.card_conj_k

theorem ncard_cls_tk : (cls t (t * S.k)).ncard ≡ 2 [MOD 4] := by
  rw [ncard_cls_t_mul]
  exact S.card_conj_k

end CFSG.OddStandard.SmallF3.L33.KD.KD46
