module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.L33.Fritz.KD46Fus

public section

namespace CFSG.OddStandard.SmallF3.L33.KD.KD46
open CFSG.ComponentClassification.HSFLit

open CFSG Subgroup Equiv SD SDKD

theorem word_ψ_inj : ∀ i l i' l' : Fin 2,
    z8 ^ (i : ℕ) * k8 ^ (l : ℕ) = z8 ^ (i' : ℕ) * k8 ^ (l' : ℕ) → i = i' ∧ l = l' := by decide

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {A : SDData t L}
  {C : A.CaseKD} (S : KDBase A C)

theorem B_word_inj {i j l i' j' l' : ℕ} (hi : i < 2) (hj : j < 2) (hl : l < 2) (hi' : i' < 2)
    (hj' : j' < 2) (hl' : l' < 2)
    (h : S.z ^ i * t ^ j * S.k ^ l = S.z ^ i' * t ^ j' * S.k ^ l') :
    i = i' ∧ j = j' ∧ l = l' := by
  have hψ := congrArg (ψX A) h
  have hw : ∀ a b e : ℕ, ψX A (S.z ^ a * t ^ b * S.k ^ e) = z8 ^ a * k8 ^ e := by
    intro a b e
    rw [ψX_mul (mul_mem (pow_mem (z_mem_T S) _) (pow_mem A.t_mem_T _)) (pow_mem (k_mem_T S) _),
      ψX_mul (pow_mem (z_mem_T S) _) (pow_mem A.t_mem_T _), ψX_pow (z_mem_T S),
      ψX_pow A.t_mem_T, ψX_pow (k_mem_T S), ψ_z, ψX_t, ψ_k, one_pow, mul_one]
  rw [hw, hw] at hψ
  obtain ⟨h1, h2⟩ := word_ψ_inj ⟨i, hi⟩ ⟨l, hl⟩ ⟨i', hi'⟩ ⟨l', hl'⟩ hψ
  have hi'' : i = i' := congrArg Fin.val h1
  have hl'' : l = l' := congrArg Fin.val h2
  subst hi'' hl''
  refine ⟨rfl, ?_, rfl⟩
  have ht : t ^ j = t ^ j' := by
    rw [mul_assoc, mul_assoc] at h
    exact mul_right_cancel (mul_left_cancel h)
  interval_cases j <;> interval_cases j'
  · rfl
  · exact absurd (by simpa using ht) (t_ne_one' (A := A)).symm
  · exact absurd (by simpa using ht) (t_ne_one' (A := A))
  · rfl

@[expose] def orbT : Set X := {b | ∃ n ∈ normalizer (S.TE : Set X), n * t * n⁻¹ = b}

theorem mem_orbT_iff {b : X} : b ∈ orbT S ↔ b ∈ S.B ∧ ConjTo t b := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨conj_mem_B_of_mem_normalizer S hn (mem_B_t S), ⟨n, rfl⟩⟩
  · rintro ⟨hb, hc⟩
    exact exists_normalizer_conj_eq S hb hc

omit [Finite X] in
include A in
theorem not_conjTo_one : ¬ ConjTo t (1 : X) := by
  rintro ⟨g, hg⟩
  apply t_ne_one' (A := A)
  calc t = g⁻¹ * (g * t * g⁻¹) * g := by group
    _ = 1 := by rw [hg]; group

theorem exists_T₁ (hnot : ¬ SectRank4 X) :
    ∃ T₁ : Subgroup X, IsPGroup 2 T₁ ∧ A.T ≤ T₁ ∧ T₁ ≤ normalizer (S.TE : Set X) ∧
      (∀ Q : Subgroup X, IsPGroup 2 Q → T₁ ≤ Q → Q ≤ normalizer (S.TE : Set X) → Q = T₁) ∧
      Nat.card T₁ = Nat.card A.T * 2 ^ (orbT S).ncard.factorization 2 ∧
      Nat.card A.T < Nat.card T₁ ∧
      Nat.card T₁ = 2 ^ (Nat.card (normalizer (S.TE : Set X))).factorization 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (S.TE : Set X) with hN
  have hTN : A.T ≤ N := T_le_normalizer_TE S
  have hTp : IsPGroup 2 (A.T.subgroupOf N) :=
    A.isPGroup_T.comap_of_injective _ (subtype_injective _)
  obtain ⟨Q, hQ⟩ := hTp.exists_le_sylow
  set T₁ : Subgroup X := (Q : Subgroup N).map N.subtype with hT₁
  have hT₁p : IsPGroup 2 T₁ := Q.isPGroup'.map _
  have hT₁N : T₁ ≤ N := map_subtype_le _
  have hTT₁ : A.T ≤ T₁ := fun g hg => ⟨⟨g, hTN hg⟩, hQ hg, rfl⟩
  have hcardT₁ : Nat.card T₁ = 2 ^ (Nat.card N).factorization 2 := by
    rw [hT₁, card_map_of_injective (subtype_injective _), Sylow.card_eq_multiplicity]
  have hmax : ∀ Q' : Subgroup X, IsPGroup 2 Q' → T₁ ≤ Q' → Q' ≤ N → Q' = T₁ := by
    intro Q' hQ' hle hQ'N
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    obtain ⟨m, hm⟩ := hQ'.exists_card_eq
    have hdvd : Nat.card Q' ∣ Nat.card N := Subgroup.card_dvd_of_le hQ'N
    rw [hm] at hdvd ⊢
    rw [hcardT₁]
    exact Nat.pow_le_pow_right (by norm_num)
      ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd)
  have hidx : (N ⊓ centralizer ({t} : Set X)).relIndex N = (orbT S).ncard :=
    relIndex_inf_centralizer_eq_ncard N t
  have hTC : Nat.card A.T =
      2 ^ (Nat.card (N ⊓ centralizer ({t} : Set X) : Subgroup X)).factorization 2 :=
    card_T_eq_of_le (A := A) (le_inf hTN A.T_le_centralizer) inf_le_right
  have hcard := card_eq_mul_two_pow (P := T₁) (Q := A.T) inf_le_left hcardT₁ hTC
  rw [hidx] at hcard
  have hlt : Nat.card A.T < Nat.card T₁ := by
    have hns : ∀ P : Sylow 2 X, (P : Subgroup X) ≠ A.T := fun P hP =>
      hnot fun Q' hQ' => A.gen4_of_coe_sylow_eq P hP Q' hQ'
    obtain ⟨w, hwN, hwT, hwp⟩ := exists_mem_normalizer_not_mem A.isPGroup_T hns
    have hwN' : w ∈ N := normalizer_T_le S hwN
    have hle : A.T ⊔ zpowers w ≤ N := sup_le hTN (zpowers_le.mpr hwN')
    have hlt' : A.T < A.T ⊔ zpowers w :=
      lt_of_le_of_ne le_sup_left fun h => hwT (h ▸ mem_sup_right (mem_zpowers w))
    have h1 := card_lt_of_lt hlt'
    obtain ⟨m, hm⟩ := hwp.exists_card_eq
    have hdvd : Nat.card (A.T ⊔ zpowers w : Subgroup X) ∣ Nat.card N :=
      Subgroup.card_dvd_of_le hle
    rw [hm] at hdvd h1
    have h2 : 2 ^ m ≤ Nat.card T₁ := by
      rw [hcardT₁]
      exact Nat.pow_le_pow_right (by norm_num)
        ((Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp hdvd)
    omega
  exact ⟨T₁, hT₁p, hTT₁, hT₁N, hmax, hcard, hlt, hcardT₁⟩

end CFSG.OddStandard.SmallF3.L33.KD.KD46
