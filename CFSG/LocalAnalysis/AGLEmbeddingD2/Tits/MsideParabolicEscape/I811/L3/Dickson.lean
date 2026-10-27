module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3.Parabolic
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2
public import CFSG.Dihedral.Glauberman.DicksonMaxTables

public section

namespace CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3

open CFSG.BenderSuzuki.MatrixGroups CFSG.Glauberman.Dickson
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupPSL2
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound.OvergroupA5

variable {F : Type} [Field F] [Finite F] {p f : ℕ} [Fact p.Prime]

theorem normalizer_nonsplit_maximal (hF : Nat.card F = p ^ f)
    (hq : Nat.card F % 3 = 2) (h5 : 5 ≤ Nat.card F) {S : Subgroup (PSL2MatrixGroup F)}
    (hS : IsCyclic S) (hSc : Nat.card S = (Nat.card F + 1) / Nat.gcd (Nat.card F - 1) 2)
    (hN : Nat.card (Subgroup.normalizer (S : Set (PSL2MatrixGroup F))) = 2 * Nat.card S)
    {w : PSL2MatrixGroup F} (hwN : w ∈ Subgroup.normalizer (S : Set (PSL2MatrixGroup F)))
    (hwinv : ∀ t ∈ S, w * t * w⁻¹ = t⁻¹) {H : Subgroup (PSL2MatrixGroup F)}
    (hH : Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ≤ H) :
    H = Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) ∨ H = ⊤ := by
  classical
  have hF' := hF
  obtain ⟨q, hqdef⟩ : ∃ q, Nat.card F = q := ⟨_, rfl⟩
  obtain ⟨n, hndef⟩ : ∃ n, Nat.card S = n := ⟨_, rfl⟩
  rw [hqdef] at hF hq h5
  rw [hqdef, hndef] at hSc
  rw [hndef] at hN
  set NS := Subgroup.normalizer (S : Set (PSL2MatrixGroup F)) with hNSdef
  have hp : p.Prime := Fact.out
  have hf0 : f ≠ 0 := CFSG.BenderSuzuki.External.huppert_II_8_27_field_exponent_ne_zero hF'
  have hp3 : p ≠ 3 := by
    rintro rfl
    have : 3 ∣ q := hF ▸ dvd_pow_self 3 hf0
    omega
  have hg : Nat.gcd (q - 1) 2 = 1 ∨ Nat.gcd (q - 1) 2 = 2 := by
    have h := Nat.gcd_dvd_right (q - 1) 2
    have h2 : Nat.gcd (q - 1) 2 ≤ 2 := Nat.le_of_dvd (by norm_num) h
    have h0 : 0 < Nat.gcd (q - 1) 2 := Nat.gcd_pos_of_pos_right _ (by norm_num)
    omega
  have hng : n * Nat.gcd (q - 1) 2 = q + 1 := by
    rw [hSc]
    refine Nat.div_mul_cancel ?_
    rcases hg with h | h
    · rw [h]; exact one_dvd _
    · rw [h]
      have h2 : 2 ∣ q - 1 := h ▸ Nat.gcd_dvd_left (q - 1) 2
      omega
  have hn3 : 3 ≤ n := by rcases hg with h | h <;> rw [h] at hng <;> omega
  have hqn : q ≤ 2 * n + 1 := by rcases hg with h | h <;> rw [h] at hng <;> omega
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := S)
  have hso : orderOf (s : PSL2MatrixGroup F) = n := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hs, hndef]
  have hsN : (s : PSL2MatrixGroup F) ∈ NS := Subgroup.le_normalizer s.2
  have hsH : (s : PSL2MatrixGroup F) ∈ H := hH hsN
  have hwH : w ∈ H := hH hwN
  have hnc : w * (s : PSL2MatrixGroup F) ≠ (s : PSL2MatrixGroup F) * w := by
    intro hc
    have h1 := hwinv s s.2
    rw [hc, mul_inv_cancel_right] at h1
    have h2 : (s : PSL2MatrixGroup F) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h1]
      exact inv_mul_cancel _
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hso] at this
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hNScard : Nat.card NS = 2 * n := hN
  have hNSH : Nat.card NS ≤ Nat.card H := Subgroup.card_le_of_le hH
  have hcardEq : Nat.card H ≤ Nat.card NS → H = NS := fun h =>
    (Subgroup.eq_of_le_of_card_ge hH h).symm
  have hsHo : orderOf (⟨s, hsH⟩ : H) = n := (Subgroup.orderOf_coe ⟨_, hsH⟩).symm.trans hso
  have hnp : Nat.Coprime n p := by
    have hdvd : n ∣ q + 1 := ⟨_, hng.symm⟩
    refine (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_))
    intro hpn
    have hpq : p ∣ q := hF ▸ dvd_pow_self p hf0
    have hp1 : p ∣ q + 1 := hpn.trans hdvd
    have : p ∣ 1 := (Nat.dvd_add_right hpq).mp hp1
    exact hp.one_lt.ne' (Nat.dvd_one.mp this)
  have hKW : Nat.card H ∣ Nat.card (PSL2MatrixGroup F) := Subgroup.card_subgroup_dvd_card H
  rcases huppert_II_8_27_dickson_psl2_subgroup_classification_with_subfield hF' H with
    hE | ⟨z', -, -, hC⟩ | ⟨z', hz', hcard, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨h16, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ |
    ⟨m, t, -, ht, N, C, hNn, hNe, hNc, hCc, hCt, hdisj, hsup⟩ | ⟨m, hm0, hmf, ⟨e⟩, -⟩ |
    ⟨m, hm0, hmf, ⟨e⟩, -⟩
  ·
    exfalso
    have := hE.is_comm.comm (⟨w, hwH⟩ : H) ⟨s, hsH⟩
    exact hnc (congrArg Subtype.val this)
  ·
    exfalso
    have := hC.commGroup.mul_comm (⟨w, hwH⟩ : H) ⟨s, hsH⟩
    exact hnc (congrArg Subtype.val this)
  ·
    left
    have hz'0 : z' ≠ 0 := by
      rintro rfl
      have := Nat.card_pos (α := H)
      omega
    have : NeZero z' := ⟨hz'0⟩
    have hrot : n ∣ z' := by
      have ho : orderOf (e ⟨s, hsH⟩) = n := by rw [MulEquiv.orderOf_eq, hsHo]
      rcases hes : e ⟨s, hsH⟩ with i | i
      · rw [hes, DihedralGroup.orderOf_r] at ho
        rw [← ho]
        exact Nat.div_dvd_of_dvd (Nat.gcd_dvd_left _ _)
      · rw [hes, DihedralGroup.orderOf_sr] at ho
        omega
    refine hcardEq ?_
    rw [hcard, hNScard]
    rw [hqdef] at hz'
    rcases hz' with h | h
    · exfalso
      have h1 := hrot.trans h
      have h2 : (q - 1) / Nat.gcd (q - 1) 2 < n := by
        rcases hg with hg | hg <;> rw [hg] at hng ⊢ <;> omega
      have h3 : 0 < (q - 1) / Nat.gcd (q - 1) 2 := by
        rcases hg with hg | hg <;> rw [hg] <;> omega
      have := Nat.le_of_dvd h3 h1
      omega
    · have h1 : z' ∣ n := by
        rw [hSc]
        exact h
      have := Nat.dvd_antisymm h1 hrot
      omega
  ·
    exfalso
    have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.orderOf_dvd_of_equiv_alternating_four
      e ⟨s, hsH⟩
    rw [hsHo] at hord
    have hn : n = 3 := by
      rcases hord with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    have hq5 : q = 5 := by rcases hg with h | h <;> rw [h, hn] at hng <;> omega
    have hH12 : Nat.card H = 12 := by
      rw [Nat.card_congr e.toEquiv]
      exact QuatTable.card_alternatingFour
    have hidx : ((NS.subgroupOf H).map (e : H →* alternatingGroup (Fin 4))).index = 2 := by
      rw [Subgroup.index_map_equiv]
      have h1 := Subgroup.relIndex_mul_card NS H
      rw [inf_of_le_left hH, hNScard, hn, hH12] at h1
      rw [← Subgroup.relIndex]
      omega
    exact QuatTable.alternatingFour_index_ne_two _ hidx
  ·
    exfalso
    have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.orderOf_dvd_of_equiv_perm_four
      e ⟨s, hsH⟩
    rw [hsHo] at hord
    have hn : n = 3 ∨ n = 4 := by
      rcases hord with h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
    have hq5 : q = 5 := by
      rcases hn with hn | hn <;> rcases hg with h | h <;> rw [h, hn] at hng <;> omega
    rw [pow_mul', ← hF, hq5] at h16
    norm_num at h16
  ·
    right
    have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.orderOf_dvd_of_equiv_alternating_five
      e ⟨s, hsH⟩
    rw [hsHo] at hord
    have hn : n = 3 ∨ n = 5 := by
      rcases hord with h | h | h
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h; omega
      · have := Nat.le_of_dvd (by norm_num) h
        rcases (show n = 3 ∨ n = 4 ∨ n = 5 by omega) with h' | h' | h'
        · exact Or.inl h'
        · rw [h'] at h; norm_num at h
        · exact Or.inr h'
    have hq5 : q = 5 := by
      rcases hn with hn | hn <;> rcases hg with h | h <;> rw [h, hn] at hng <;> omega
    have hp2 : p ≠ 2 := by
      rintro rfl
      have : 2 ∣ q := hF ▸ dvd_pow_self 2 hf0
      omega
    have h60 := MaxUp.card_psl2_odd hF' hp2
    rw [← hF', hqdef, hq5] at h60
    norm_num at h60
    refine Subgroup.eq_top_of_card_eq H ?_
    rw [h60, Nat.card_congr e.toEquiv]
    exact MaxUp.card_alternatingFive'
  ·
    exfalso
    have hNnorm : N.Normal := hNn
    have h1 := relIndex_sup_normal C N
    rw [hsup, Subgroup.relIndex_top_right,
      Subgroup.relIndex, Subgroup.subgroupOf_eq_bot.mpr hdisj.symm, Subgroup.index_bot] at h1
    have hHc : Nat.card H = Nat.card N * Nat.card C := by
      rw [← C.index_mul_card, h1]
    have hdvd : n ∣ Nat.card N * Nat.card C := by
      rw [← hHc, ← hsHo]
      exact orderOf_dvd_natCard _
    rw [hNc, hCt] at hdvd
    have hnt : n ∣ t := (Nat.Coprime.pow_right m hnp).dvd_of_dvd_mul_left hdvd
    have h2 := hnt.trans ht
    rw [← hF] at h2
    have h3 : (q - 1) / Nat.gcd (q - 1) 2 < n := by
      rcases hg with hg | hg <;> rw [hg] at hng ⊢ <;> omega
    have h4 : 0 < (q - 1) / Nat.gcd (q - 1) 2 := by
      rcases hg with hg | hg <;> rw [hg] <;> omega
    have := Nat.le_of_dvd h4 h2
    omega
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    by_cases h2 : p ^ m = 2
    · left
      refine hcardEq ?_
      have hdvd : Nat.card H ∣ 6 := by
        rw [Nat.card_congr e.toEquiv]
        have := card_psl2_dvd (GaloisField p m)
        rw [hGF, h2] at this
        simpa using this
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have ha := four_le_pow hp3 hm0 h2
    by_cases hmeq : m = f
    · right
      obtain ⟨φ⟩ := nonempty_galoisField_ringHom hF' hmf
      have hcardle : Nat.card F ≤ Nat.card (GaloisField p m) := by rw [hF', hGF, hmeq]
      have hbij := φ.injective.bijective_of_nat_card_le hcardle
      let ψ : F ≃+* GaloisField p m := (RingEquiv.ofBijective φ hbij).symm
      have hle : Nat.card (PSL2MatrixGroup F) ≤ Nat.card (PSL2MatrixGroup (GaloisField p m)) :=
        Nat.card_le_card_of_injective _ (psl2Map_injective ψ.toRingHom)
      refine Subgroup.eq_top_of_card_eq H ?_
      refine le_antisymm (Nat.le_of_dvd Nat.card_pos hKW) ?_
      rw [Nat.card_congr e.toEquiv]
      exact hle
    · exfalso
      obtain ⟨k, hk⟩ := hmf
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with h | h
        · interval_cases k <;> simp_all
        · exact h
      have hf2 : 2 * m ≤ f := by nlinarith
      have hpow : (p ^ m) ^ 2 ≤ q := by
        rw [hF, ← pow_mul, mul_comm]
        exact Nat.pow_le_pow_right hp.pos hf2
      have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.psl2_orderOf_le
        (GaloisField p m) (e ⟨s, hsH⟩)
      rw [MulEquiv.orderOf_eq, hsHo, hGF] at hord
      exact false_of_subfield_bound ha hord hpow hqn
  ·
    have hGF : Nat.card (GaloisField p m) = p ^ m := GaloisField.card p m hm0
    have hf2 : 2 * m ≤ f := Nat.le_of_dvd (Nat.pos_of_ne_zero hf0) hmf
    by_cases h2 : p ^ m = 2
    · left
      refine hcardEq ?_
      have hdvd : Nat.card H ∣ 6 := by
        rw [Nat.card_congr e.toEquiv, MaxUp.card_pgl2_galoisField hm0, pow_mul' p 2 m, h2]
        norm_num
      have := Nat.le_of_dvd (by norm_num) hdvd
      omega
    exfalso
    have ha := four_le_pow hp3 hm0 h2
    have hpow : (p ^ m) ^ 2 ≤ q := by
      rw [hF, ← pow_mul, mul_comm]
      exact Nat.pow_le_pow_right hp.pos hf2
    have hord := CFSG.ComponentClassification.AschbacherKnownGroup.FactsL2.pgl2_orderOf_le
      (GaloisField p m) (e ⟨s, hsH⟩)
    rw [MulEquiv.orderOf_eq, hsHo, hGF] at hord
    exact false_of_subfield_bound ha hord hpow hqn

end CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.I811.L3
