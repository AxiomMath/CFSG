module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Out2
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1OuterGen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Check
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1M22Outer

public section

namespace CFSG.QuasithinUnique.Setup.X1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Mathieu CFSG.Blueprint CFSG.Quasithin
  CFSG.QuasithinUnique.Setup.Family CFSG.Certificates CFSG.ComponentClassification.OuterAutomorphisms

abbrev S22 : Type := ↥NativeSporadic.M22

section Facts

theorem m22_card_eq : Nat.card S22 = 2 ^ 7 * 3465 := by
  rw [m22_card]
  norm_num

theorem m22_sylow :
    SylowData S22 7 3465 m22rl := by
  obtain ⟨hlen, hnd, h1, hmul, hpow⟩ := m22_sylow_check
  exact SylowData.of_mul_mem hlen hnd h1 hmul hpow m22_card_eq (by decide)

theorem m22_rank_le
    : ∀ B : Subgroup S22, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
    (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 4 :=
  m22_sylow.rank_le 4 m22_rank_check

theorem m22_gen1
    (B : Subgroup S22) (hsq : ∀ x ∈ B, x * x = 1) (hne : B ≠ ⊥) :
    ∃ cs : List S22, cs.length = 3 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S22)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hok, hcover⟩ := m22_G1_check
  obtain ⟨h1, h2⟩ := gen1_hyps m22rl m22conj m22G1 (p := 11) hok
    (fun ws => by simp [m22conj]) hcover
  exact m22_sylow.gen1 _ h1 h2 B hsq hne

theorem m22_gen2
    (B : Subgroup S22) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hsq : ∀ x ∈ B, x * x = 1) (h3 : 2 < Nat.card B) :
    ∃ cs : List S22, cs.length = 2 ∧
      ∃ x ∈ Subgroup.closure (conjSet cs (B : Set S22)), orderOf x = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  obtain ⟨hok, hcover⟩ := m22_G2_check
  obtain ⟨h1, h2⟩ := gen2_hyps m22rl m22conj m22G2 (p := 11) hok
    (fun ws => by simp [m22conj]) hcover
  exact m22_sylow.gen2 _ h1 h2 B hcomm hsq h3

theorem m22_outer_cover'
    : ∀ u : Equiv.Perm (Fin 22), m22Delta⁻¹ * u ∈ NativeSporadic.M22 →
    orderOf u = 2 → ∃ r ∈ m22OutReps, ∃ c ∈ NativeSporadic.M22, u = c * r * c⁻¹ := by
  have hn : (22 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m22Certificate := m22Certificate_check
  obtain ⟨hok, hsz, -⟩ := m22_outer_cover
  obtain ⟨hr1, hro1, -, -, -⟩ := m22_out_rep_data1
  obtain ⟨hr2, hro2, -, -, -⟩ := m22_out_rep_data2
  have hA : m22gA ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hB : m22gB ∈ m22Certificate.originalSubgroup := m22_gens_mem _ (by simp)
  have hg₀ : ∀ h ∈ m22Certificate.originalSubgroup,
      m22Delta⁻¹ * h * m22Delta ∈ m22Certificate.originalSubgroup := by
    rw [m22Certificate_originalSubgroup]
    exact inv_conj_mem _ m22_delta_normalizes m22_delta_sq
  rw [← m22Certificate_originalSubgroup]
  exact (exists_conj_of_repsOK hn m22Certificate hQ (pairTables_spec hn hA hB) m22Delta hg₀
    (by norm_num) m22OutReps (fun r hr => by
      rw [m22OutReps_eq] at hr
      rcases List.mem_pair.1 hr with rfl | rfl
      · exact ⟨hr1, hro1⟩
      · exact ⟨hr2, hro2⟩) 2000 hok).1

theorem m22_gens_mem_M22 : ∀ g ∈ [m22gA, m22gB], g ∈ NativeSporadic.M22 := by
  rw [← m22Certificate_originalSubgroup]
  exact m22_gens_mem

theorem outer_rep_ok (r : Equiv.Perm (Fin 22)) (e : List (List ℤ) × List ℤ)
    (h : m22outerOK r e = true) : ∃ ks : List (Equiv.Perm (Fin 22)), ks.length = 3 ∧
      (∀ x ∈ ks, x ∈ NativeSporadic.M22) ∧ ∃ w : List ℤ,
        orderOf (evalG (ks.map fun x => r * (x * r * x⁻¹)) w) = 11 := by
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  simp only [m22outerOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨hlen, hz1, hz2⟩ := h
  refine ⟨e.1.map (evalG [m22gA, m22gB]), by simpa using hlen, ?_, e.2, orderOf_eq_prime hz1 hz2⟩
  intro x hx
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hx
  exact evalG_mem NativeSporadic.M22 m22_gens_mem_M22 w

theorem m22_hrep
    : ∀ u : Equiv.Perm (Fin 22), m22Delta⁻¹ * u ∈ NativeSporadic.M22 →
    orderOf u = 2 → ∃ ks : List (Equiv.Perm (Fin 22)), ks.length = 3 ∧
      (∀ x ∈ ks, x ∈ NativeSporadic.M22) ∧ ∃ w : List ℤ,
        orderOf (evalG (ks.map fun x => u * (x * u * x⁻¹)) w) = 11 := by
  refine hrepGen_of_cover NativeSporadic.M22 m22OutReps m22_outer_cover' ?_
  intro r hr
  rw [m22OutReps_eq] at hr
  obtain ⟨h1, h2⟩ := m22_outer_check
  rcases List.mem_pair.1 hr with rfl | rfl
  · exact outer_rep_ok _ _ h1
  · exact outer_rep_ok _ _ h2

theorem m22_outer_gen
    : ∀ α : MulAut S22, α * α = 1 → α ∉ inner S22 →
    ∃ cs : List (MulAut S22), cs.length = 3 + 1 ∧ (∀ c ∈ cs, c ∈ inner S22) ∧
      ∃ y ∈ Subgroup.closure (conjSet cs {α}), orderOf y = 11 :=
  outer_gen_of_delta NativeSporadic.M22 m22Delta m22_delta_normalizes m22_delta_sq
    m22_center_eq_bot' m22_delta_outer m22_mulAut_card m22_hrep

end Facts

theorem m22_weight_lt_or_tight
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L E : Subgroup (MulAut W)} (hq : CFSG.IsQuasisimple ↥L) (hirr : IsIrrOn L)
    (e : CQ L ≃* NativeSporadic.Carrier .M22)
    (hE : E ≤ Subgroup.normalizer (L : Set (MulAut W))) (hEne : E ≠ ⊥) (hEel : IsElemAbelian2 E) :
    Nat.card E * Nat.card (fixV E) < Nat.card W ∨
      (¬ E ≤ L ∧ Nat.card E = 2 ^ 5 ∧ (fixV E).index = 2 ^ 5) := by
  have e' : CQ L ≃* S22 := e
  have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hidx := index_fixV_eq_two_pow hW E
  by_cases hEL : E ≤ L
  · left
    apply weight_lt_of_lt_index
    have hcard : Nat.card E ≤ 2 ^ 4 := card_le_two_pow_of_le hW hirr hEL hEel e' m22_rank_le
    have hBcomm := imgSub_comm (hEL := hEL) (e := e') hEel
    have hBsq := imgSub_sq (hEL := hEL) (e := e') hEel
    have hBcard := card_imgSub hW hirr hEL hEel e'
    by_cases h8 : Nat.card E ≤ 8
    · have hne : imgSub L E hEL e' ≠ ⊥ := by
        intro h
        have h1 : Nat.card (imgSub L E hEL e') = 1 := by rw [h]; simp
        rw [hBcard] at h1
        exact hEne (Subgroup.card_eq_one.1 h1)
      obtain ⟨cs, hcs, hx⟩ := m22_gen1 _ hBsq hne
      have h := two_pow_le_of_inner_gen hW hEL e' (k := 3) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
      rw [orderOf_two_zmod_11] at h
      have h2 := two_pow_le_of_pow_le hidx h (ρ := 4) (by norm_num)
      omega
    · have h3 : 2 < Nat.card (imgSub L E hEL e') := by rw [hBcard]; omega
      obtain ⟨cs, hcs, hx⟩ := m22_gen2 _ hBcomm hBsq h3
      have h := two_pow_le_of_inner_gen hW hEL e' (k := 2) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
      rw [orderOf_two_zmod_11] at h
      have h2 := two_pow_le_of_pow_le hidx h (ρ := 5) (by norm_num)
      omega
  · obtain ⟨hdisp, hcardE⟩ := (out2_dichotomy_gen hW hq.1 hirr hE hEel e' m22_center_eq_bot'
      m22_mulAut_card (k := 3 + 1) (p := 11) (by norm_num)
      (fun ψ hψ hψ2 => m22_outer_gen ψ hψ2 hψ)).resolve_left hEL
    rw [orderOf_two_zmod_11] at hdisp
    have h8 := two_pow_le_of_pow_le hidx hdisp (ρ := 3) (by norm_num)
    by_cases h4 : Nat.card E ≤ 4
    · left
      apply weight_lt_of_lt_index
      omega
    · have hE0L : E ⊓ L ≤ L := inf_le_right
      have hE0el : IsElemAbelian2 (E ⊓ L) :=
        ⟨fun a ha b hb => hEel.1 a ha.1 b hb.1, fun a ha => hEel.2 a ha.1⟩
      have hE0card : Nat.card ↥(E ⊓ L) ≤ 2 ^ 4 :=
        card_le_two_pow_of_le hW hirr hE0L hE0el e' m22_rank_le
      have hBcomm := imgSub_comm (hEL := hE0L) (e := e') hE0el
      have hBsq := imgSub_sq (hEL := hE0L) (e := e') hE0el
      have hBcard := card_imgSub hW hirr hE0L hE0el e'
      have h3 : 2 < Nat.card (imgSub L (E ⊓ L) hE0L e') := by rw [hBcard]; omega
      obtain ⟨cs, hcs, hx⟩ := m22_gen2 _ hBcomm hBsq h3
      have h := two_pow_le_of_inner_gen hW hE0L e' (k := 2) (p := 11) (by norm_num) ⟨cs, hcs, hx⟩
      rw [orderOf_two_zmod_11] at h
      have h5 := two_pow_le_of_pow_le (index_fixV_eq_two_pow hW (E ⊓ L)) h (ρ := 5) (by norm_num)
      have hmono : (fixV (E ⊓ L)).index ≤ (fixV E).index :=
        Subgroup.index_antitone (fixV_anti inf_le_left)
      by_cases hlt : Nat.card E < (fixV E).index
      · left
        exact weight_lt_of_lt_index E hlt
      · right
        refine ⟨hEL, ?_, ?_⟩ <;> omega

end CFSG.QuasithinUnique.Setup.X1
