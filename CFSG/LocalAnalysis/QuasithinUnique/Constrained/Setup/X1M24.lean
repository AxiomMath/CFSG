module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Inner
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M24Check
public import CFSG.Sporadic.Schreier.MathieuOddCoreM24

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family

abbrev S24 : Type := ↥NativeSporadic.M24

section Facts

theorem m24_card_eq : Nat.card S24 = 2 ^ 10 * 239085 := by
  rw [m24_card]
  norm_num

theorem m24_Rl_mem {x : S24} (hx : x ∈ m24rl) : x ∈ Subgroup.closure {g | g ∈ m24rg} := by
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  rw [evalN, normH_eq]
  exact evalG_mem _ (fun g hg => Subgroup.subset_closure hg) w

theorem m24_sylow :
    SylowData S24 10 239085 m24rl := by
  obtain ⟨hlen, hnd, h1, hgen, hpow⟩ := m24_sylow_check
  exact SylowData.of_gens m24rg hlen hnd h1 hgen (fun x hx => m24_Rl_mem hx) hpow m24_card_eq
    (by decide)

theorem m24_rank_le
    : ∀ B : Subgroup S24, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 6 :=
  m24_sylow.card_le_of_count 6 m24_count_check

theorem m24_conj_length (ws : List (List ℤ)) : (m24conj ws).length = ws.length := by
  simp [m24conj]

theorem m24_gen1
    (B : Subgroup S24) (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List S24, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S24)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hok, hcover⟩ := m24_G1_check
  obtain ⟨h1, h2⟩ := gen1_hyps m24rl m24conj m24G1 (p := 11) hok m24_conj_length hcover
  exact m24_sylow.gen1 _ h1 h2 B hsq hne

theorem m24_gen2_11
    (B : Subgroup S24) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (h3 : 2 < Nat.card B) :
    ∃ cs : List S24, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S24)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hok, hbad⟩ := m24_G2_11_check
  obtain ⟨h1, h2⟩ := gen2_hyps_fast m24key m24rl m24conj m24G2_11 (p := 11) hok m24_conj_length
  refine m24_sylow.gen2_of_count _ _ h1 h2 B hcomm hsq ?_
  rw [hbad]
  exact Nat.mul_pos (by omega) (by omega)

theorem m24_gen2_23
    (B : Subgroup S24) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (h32 : 32 ≤ Nat.card B) :
    ∃ cs : List S24, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S24)), orderOf x = 23 := by
  have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
  obtain ⟨hok, hbad⟩ := m24_G2_23_check
  obtain ⟨h1, h2⟩ := gen2_hyps_fast m24key m24rl m24conj m24G2_23 (p := 23) hok m24_conj_length
  refine m24_sylow.gen2_of_count _ _ h1 h2 B hcomm hsq ?_
  have h930 : 930 ≤ (Nat.card B - 1) * (Nat.card B - 2) := by
    calc 930 = (32 - 1) * (32 - 2) := by norm_num
      _ ≤ (Nat.card B - 1) * (Nat.card B - 2) := Nat.mul_le_mul (by omega) (by omega)
  omega

end Facts

theorem m24_weight_lt_or_tight
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* NativeSporadic.Carrier .M24)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W ∨
      (Nat.card E = 2 ^ 6 ∧ (fixV E).index = 2 ^ 6) := by
  have e' : CQ L ≃* S24 := e
  have hAut : ∀ φ : S24 ≃* S24, ∃ s : S24, ∀ x, φ x = s * x * s⁻¹ :=
    autInner_of_card_le m24_center_eq_bot' m24_mulAut_card
  have hEL : E ≤ L := le_of_autInner hW hq.1 hirr hE hEel e' hAut
  have hcard : Nat.card E ≤ 2 ^ 6 := card_le_two_pow_of_le hW hirr hEL hEel e' m24_rank_le
  have hBcomm := imgSub_comm (hEL := hEL) (e := e') hEel
  have hBsq := imgSub_sq (hEL := hEL) (e := e') hEel
  have hBcard := card_imgSub hW hirr hEL hEel e'
  have hidx := index_fixV_eq_two_pow hW E
  have hE2 : 2 ≤ Nat.card E := by
    by_contra h
    push Not at h
    have h1 : Nat.card E = 1 := by
      have := Nat.card_pos (α := E)
      omega
    exact hEne (Subgroup.card_eq_one.1 h1)
  by_cases h2 : Nat.card E ≤ 2
  · left
    apply weight_lt_of_lt_index
    have hne : imgSub L E hEL e' ≠ ⊥ := by
      intro h
      have h1 : Nat.card (imgSub L E hEL e') = 1 := by rw [h]; simp
      rw [hBcard] at h1
      omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨cs, hcs, hx⟩ := m24_gen1 _ hBsq hne
    have h := two_pow_le_of_inner_gen hW hEL e' (k := 3) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
    rw [orderOf_two_zmod_11] at h
    have h2' := two_pow_le_of_pow_le hidx h (ρ := 4) (by norm_num)
    omega
  by_cases h31 : Nat.card E < 32
  · left
    apply weight_lt_of_lt_index
    have h3 : 2 < Nat.card (imgSub L E hEL e') := by rw [hBcard]; omega
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    obtain ⟨cs, hcs, hx⟩ := m24_gen2_11 _ hBcomm hBsq h3
    have h := two_pow_le_of_inner_gen hW hEL e' (k := 2) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
    rw [orderOf_two_zmod_11] at h
    have h2' := two_pow_le_of_pow_le hidx h (ρ := 5) (by norm_num)
    omega
  · have h32 : 32 ≤ Nat.card (imgSub L E hEL e') := by rw [hBcard]; omega
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    obtain ⟨cs, hcs, hx⟩ := m24_gen2_23 _ hBcomm hBsq h32
    have h := two_pow_le_of_inner_gen hW hEL e' (k := 2) (p := 23) (by norm_num) ⟨cs, hcs, hx⟩
    rw [orderOf_two_zmod_23] at h
    have h2' := two_pow_le_of_pow_le hidx h (ρ := 6) (by norm_num)
    by_cases hlt : Nat.card E < (fixV E).index
    · left
      exact weight_lt_of_lt_index E hlt
    · right
      constructor <;> omega

end CFSG.QuasithinUnique.Setup.X1
