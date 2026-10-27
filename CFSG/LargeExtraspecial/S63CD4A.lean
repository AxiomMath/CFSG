module

public import CFSG.LargeExtraspecial.S63CD4AData
public import CFSG.LargeExtraspecial.S63CD4At

public section

namespace CFSG.LargeExtraspecial.S63

open Subgroup CFSG.Quasithin CFSG.Sporadic.SmallF2.Native
open CFSG.Monster.B.Co2 (allLt_spec)


theorem d4L_core : ∀ K : Subgroup trialityGroup8, K ≤ d4L →
    (∀ l ∈ d4L, ∀ k ∈ K, l * k * l⁻¹ ∈ K) → IsPGroup 2 K → K = ⊥ := by
  intro K hKL hKn hK2
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, -, -, h5, h6, -, -, -, -, -, h12, -⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h5
  have hLEl : ∀ i < 504, ∃ a ∈ d4L, RepE d4E L.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (lGens_hyp k hk).1) h5.1 i (h5.2 ▸ hi)
  have hLv : ∀ i < 504, validR L.El[i]! = true := fun i hi =>
    ((enumOK_parts h5.1).2.2 i (h5.2 ▸ hi)).1
  by_contra hne
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial K := (nontrivial_iff_ne_bot K).2 hne
  obtain ⟨k, hk⟩ : ∃ k : K, orderOf k = 2 := by
    rcases hK2.card_eq_or_dvd with h1 | h1
    · exact absurd h1 Finite.one_lt_card.ne'
    · exact exists_prime_orderOf_dvd_card' 2 h1
  set x := k.1 with hxdef
  have hxK : x ∈ K := k.2
  have hx2 : orderOf x = 2 := by rw [hxdef, Subgroup.orderOf_coe, hk]
  have hxx : x * x = 1 := by rw [← pow_two, ← hx2, pow_orderOf_eq_one]
  have hx1 : x ≠ 1 := by
    rintro h0
    rw [h0, orderOf_one] at hx2
    exact absurd hx2 (by norm_num)
  obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK lGens_hyp h5.1 (hKL hxK)
  rw [h5.2] at hi
  have hvi := hLv i hi
  have hsq : mulR L.El[i]! L.El[i]! = oneR :=
    (eq_iff_of_repE (validR_mulR (size_of_validR hvi) hvi) validR_oneR (repE_mul hri hri)
      repE_one).2 hxx
  have hne1 : L.El[i]! ≠ oneR := fun h' =>
    hx1 ((eq_iff_of_repE hvi validR_oneR hri repE_one).1 h')
  have h12' := h12 i hi
  simp only [hsq, beq_self_eq_true, Bool.not_true, Bool.false_or, Bool.or_eq_true, beq_iff_eq,
    hne1, false_or, List.any_eq_true, List.mem_range, Bool.and_eq_true, Bool.not_eq_true',
    beq_eq_false_iff_ne] at h12'
  obtain ⟨c, hc, hm1, hm63⟩ := h12'
  obtain ⟨lc, hlc, hrc⟩ := hLEl c hc
  obtain ⟨hic, hrc'⟩ := repE_inv_of_invOK hLEl h6 hc hrc
  set μ := x * (lc * x * lc⁻¹) with hμ
  have hrm : RepE d4E (mulR L.El[i]! (conjI L.El[c]! L.El[L.inv[c]!]! L.El[i]!)) μ :=
    repE_mul hri (repE_mul (repE_mul hrc hri) hrc')
  have hvm : validR (mulR L.El[i]! (conjI L.El[c]! L.El[L.inv[c]!]! L.El[i]!)) = true :=
    validR_mulR (size_of_validR hvi) (validR_conjI (size_of_validR (hLv c hc)) (hLv _ hic))
  have hμK : μ ∈ K := K.mul_mem hxK (hKn lc hlc x hxK)
  have hμ63 : μ ^ 63 = 1 := by
    have := repE_powRows hrm 63
    rw [hm63] at this
    exact eq_of_repE d4E_injective this repE_one
  obtain ⟨a, ha⟩ := hK2 ⟨μ, hμK⟩
  have ha' : μ ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
  have hcop : Nat.Coprime (2 ^ a) 63 := Nat.Coprime.pow_left a (by norm_num)
  have hord : orderOf μ = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left (orderOf_dvd_of_pow_eq_one ha') hcop)
      (orderOf_dvd_of_pow_eq_one hμ63)
  rw [orderOf_eq_one_iff] at hord
  rw [hord] at hrm
  exact hm1 ((eq_iff_of_repE hvm validR_oneR hrm repE_one).2 rfl)

theorem d4Q_irred : ∀ M : Subgroup trialityGroup8, M ≤ d4Q →
    (∀ l ∈ d4L, ∀ m ∈ M, l * m * l⁻¹ ∈ M) → d4z ∈ M → (∃ m ∈ M, m ≠ 1 ∧ m ≠ d4z) →
      d4Q ≤ M := by
  rintro M hMQ hMn hzM ⟨m, hmM, hm1, hmz⟩
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, h3, -, h5, h6, -, -, -, -, -, -, h13, -⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3 h5
  have hLEl : ∀ i < 504, ∃ a ∈ d4L, RepE d4E L.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (lGens_hyp k hk).1) h5.1 i (h5.2 ▸ hi)
  obtain ⟨j, hj, hrj⟩ := exists_mem_of_enumOK qGens_hyp h3.1 (hMQ hmM)
  have hvj := ((enumOK_parts h3.1).2.2 j hj).1
  have hQj1 : Q.El[j]! ≠ oneR := fun h' =>
    hm1 ((eq_iff_of_repE hvj validR_oneR hrj repE_one).1 h')
  have hQjz : Q.El[j]! ≠ z0R := fun h' =>
    hmz ((eq_iff_of_repE hvj validR_z0R hrj repE_z0R).1 h')
  have h13' := h13 j (h3.2 ▸ hj)
  simp only [Bool.or_eq_true, beq_iff_eq, hQj1, hQjz, false_or, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq] at h13'
  obtain ⟨hls, hcov⟩ := h13'
  have hys : ∀ y ∈ irrList L (irr j) Q.El[j]!, ∃ a ∈ M, RepE d4E y a := by
    intro y hy
    simp only [irrList, List.mem_append, List.mem_map, List.mem_singleton] at hy
    rcases hy with ⟨c, hc, rfl⟩ | rfl
    · obtain ⟨lc, hlc, hrc⟩ := hLEl c (hls c hc)
      obtain ⟨-, hrc'⟩ := repE_inv_of_invOK hLEl h6 (hls c hc) hrc
      exact ⟨lc * m * lc⁻¹, hMn lc hlc m hmM, repE_mul (repE_mul hrc hrj) hrc'⟩
    · exact ⟨d4z, hzM, repE_z0R⟩
  have hps := exists_mem_of_mem_subProds hys
  intro q hq
  obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK qGens_hyp h3.1 hq
  obtain ⟨p, hp, hpi⟩ := exists_of_coverOK hcov i hi
  obtain ⟨a, ha, hra⟩ := hps p hp
  rw [← hpi] at hra
  rw [eq_of_repE d4E_injective hri hra]
  exact ha

theorem d4Q_le_comm : d4Q ≤ zpowers d4z ⊔ ⁅d4Q, d4L⁆ := by
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -, -, -, -, -, h14, h14', -⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3 h5
  have hLEl : ∀ i < 504, ∃ a ∈ d4L, RepE d4E L.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (lGens_hyp k hk).1) h5.1 i (h5.2 ▸ hi)
  have hQEl : ∀ i < 512, ∃ a ∈ d4Q, RepE d4E Q.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (qGens_hyp k hk).1) h3.1 i (h3.2 ▸ hi)
  have hys : ∀ y ∈ commList Q L comms, ∃ a ∈ zpowers d4z ⊔ ⁅d4Q, d4L⁆, RepE d4E y a := by
    intro y hy
    simp only [commList, List.mem_append, List.mem_map, List.mem_singleton] at hy
    rcases hy with ⟨p, hp, rfl⟩ | rfl
    · obtain ⟨hp1, hp2⟩ := h14 p hp
      obtain ⟨q, hq, hrq⟩ := hQEl p.1 hp1
      obtain ⟨-, hrq'⟩ := repE_inv_of_invOK hQEl h4 hp1 hrq
      obtain ⟨l, hl, hrl⟩ := hLEl p.2 hp2
      obtain ⟨-, hrl'⟩ := repE_inv_of_invOK hLEl h6 hp2 hrl
      refine ⟨q⁻¹ * l⁻¹ * (q * l), ?_, repE_mul (repE_mul hrq' hrl') (repE_mul hrq hrl)⟩
      apply mem_sup_right
      have hc := commutator_mem_commutator (d4Q.inv_mem hq) (d4L.inv_mem hl)
      rw [commutatorElement_def, inv_inv, inv_inv] at hc
      rw [← mul_assoc]
      exact hc
    · exact ⟨d4z, mem_sup_left (mem_zpowers d4z), repE_z0R⟩
  have hps := exists_mem_of_mem_subProds hys
  intro q hq
  obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK qGens_hyp h3.1 hq
  obtain ⟨p, hp, hpi⟩ := exists_of_coverOK h14' i hi
  obtain ⟨a, ha, hra⟩ := hps p hp
  rw [← hpi] at hra
  rw [eq_of_repE d4E_injective hri hra]
  exact ha

theorem d4L_faithful : ∀ q ∈ d4Q, ∀ l ∈ d4L, (∀ x ∈ d4Q, q * l * x = x * (q * l)) → l = 1 := by
  intro q hq l hl hcomm
  by_contra hl1
  obtain ⟨Q, L, irr, comms, h⟩ := exists_d4ACheckOn
  obtain ⟨-, -, h3, h4, h5, h6, -, -, -, -, -, -, -, -, -, h15, h16⟩ := parts_of_d4ACheckOn h
  simp only [EnumData.ok, Bool.and_eq_true, beq_iff_eq] at h3 h5
  have hLEl : ∀ i < 504, ∃ a ∈ d4L, RepE d4E L.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (lGens_hyp k hk).1) h5.1 i (h5.2 ▸ hi)
  have hQEl : ∀ i < 512, ∃ a ∈ d4Q, RepE d4E Q.El[i]! a := fun i hi =>
    exists_of_enumOK (fun k hk => (qGens_hyp k hk).1) h3.1 i (h3.2 ▸ hi)
  obtain ⟨i, hi, hri⟩ := exists_mem_of_enumOK lGens_hyp h5.1 hl
  rw [h5.2] at hi
  have hvi := ((enumOK_parts h5.1).2.2 i (h5.2 ▸ hi)).1
  have hne : L.El[i]! ≠ oneR := fun h' =>
    hl1 ((eq_iff_of_repE hvi validR_oneR hri repE_one).1 h')
  have h16' := h16 i hi
  simp only [Bool.or_eq_true, beq_iff_eq, hne, false_or, List.any_eq_true, List.mem_range,
    Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne] at h16'
  obtain ⟨k, hk, hA1, hA2⟩ := h16'
  have hxQ : qGH k ∈ d4Q := subset_closure ⟨k, hk, rfl⟩
  have hlx : l * qGH k * l⁻¹ = q⁻¹ * qGH k * q := by
    calc l * qGH k * l⁻¹ = q⁻¹ * (q * l * qGH k) * l⁻¹ := by group
      _ = q⁻¹ * (qGH k * (q * l)) * l⁻¹ := by rw [hcomm _ hxQ]
      _ = q⁻¹ * qGH k * q := by group
  obtain ⟨i', hi', hri'⟩ := exists_mem_of_enumOK qGens_hyp h3.1 (d4Q.inv_mem hq)
  rw [h3.2] at hi'
  obtain ⟨-, hri''⟩ := repE_inv_of_invOK hQEl h4 hi' hri'
  rw [inv_inv] at hri''
  have hrB : RepE d4E (conjI Q.El[i']! Q.El[Q.inv[i']!]! qGens[k]!) (q⁻¹ * qGH k * q) :=
    repE_mul (repE_mul hri' (qGens_hyp k hk).1) hri''
  obtain ⟨hii, hri_inv⟩ := repE_inv_of_invOK hLEl h6 hi hri
  have hrA : RepE d4E (conjI L.El[i]! L.El[L.inv[i]!]! qGens[k]!) (q⁻¹ * qGH k * q) := by
    rw [← hlx]
    exact repE_mul (repE_mul hri (qGens_hyp k hk).1) hri_inv
  have hvA : validR (conjI L.El[i]! L.El[L.inv[i]!]! qGens[k]!) = true :=
    validR_conjI (size_of_validR hvi) ((enumOK_parts h5.1).2.2 _ (h5.2 ▸ hii)).1
  rcases h15 i' hi' k hk with hB | hB
  · rw [hB] at hrB
    have := eq_of_repE d4E_injective hrB (qGens_hyp k hk).1
    rw [this] at hrA
    exact hA1 (arr_eq_of_repE hvA (validR_qGens hk) hrA (qGens_hyp k hk).1)
  · rw [hB] at hrB
    have := eq_of_repE d4E_injective hrB (repE_mul (qGens_hyp k hk).1 repE_z0R)
    rw [this] at hrA
    exact hA2 (arr_eq_of_repE hvA (validR_mulR (size_of_validR (validR_qGens hk)) validR_z0R)
      hrA (repE_mul (qGens_hyp k hk).1 repE_z0R))


theorem d42At_d4z : D42At trialityGroup8 d4z :=
  d42At_of_semidirect d4z_mem_d4Q d4L_le_centralizer (fun _ hc => exists_of_mem_centralizer_d4z hc)
    d4L_normalizes (fun _ hx hx' => eq_one_of_mem_d4Q_d4L hx hx') d4L_core d4Q_irred d4Q_le_comm
    d4L_faithful

end CFSG.LargeExtraspecial.S63
