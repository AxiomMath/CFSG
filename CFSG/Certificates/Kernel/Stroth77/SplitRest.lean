module

public import CFSG.Certificates.Kernel.Stroth77.SplitGroups
public import Certificates.Data.Kernel.Stroth77.SplitW4
public import Certificates.Data.CFSGNative.Stroth15.GL5

public section

namespace CFSG.KC.Stroth77SP

open Equiv Equiv.Perm CFSG.CGT.Stroth77

theorem mem_l8 {i : ℕ} (h : i < 8) : i ∈ l8 := by
  simp only [l8, List.mem_cons, List.not_mem_nil, or_false]
  omega

theorem lt_of_mem_l16 {i : ℕ} (h : i ∈ l16) : i < 16 := by
  simp only [l16, List.mem_cons, List.not_mem_nil, or_false] at h
  omega

theorem lt_of_mem_l256 {c : ℕ} (h : c ∈ l256) : c < 256 := by
  obtain ⟨j, hj, h⟩ := List.mem_flatMap.1 h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 h
  have := lt_of_mem_l16 hj
  have := lt_of_mem_l16 hi
  omega

theorem mem_l128 {c : ℕ} (h : c < 128) : c ∈ l128 :=
  List.mem_flatMap.2 ⟨c / 16, mem_l8 (by omega), List.mem_map.2 ⟨c % 16, mem_l16 (by omega),
    by omega⟩⟩

theorem conjK_enc (a b : Msp) : conjK (enc a) (enc b) = enc (a * b * a⁻¹) := by
  rw [conjK, enc_mul, enc_mul, enc_inv]

variable {D : Tabs}

theorem fullOf_eq (ht : tabOK D = true) (c : ℕ) : fullOf D c = enc (elS c) := by
  rw [fullOf, elS, enc_mul, enc_ePhi_rd ht (Nat.mod_lt c (by norm_num)),
    enc_pPhi_rd ht (Nat.mod_lt (c / 16) (by norm_num))]

theorem memA_iff (ha : aOK D = true) {c : ℕ} (hc : c < 256) :
    memA D c = true ↔ ∃ r < 32, phiS D r = c := by
  refine ⟨(a_facts ha).1 c hc, ?_⟩
  rintro ⟨r, hr, rfl⟩
  rw [aOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at ha
  have h := List.all_eq_true.1 ha.1.1.1 (phiS D r) (mem_l256 hc)
  rw [beq_iff_eq] at h
  rw [h, List.any_eq_true]
  exact ⟨r, mem_l32 hr, beq_self_eq_true _⟩

theorem elS_mem_Asp_iff (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {c : ℕ}
    (hlt : c < 256) : elS c ∈ Asp ↔ memA D c = true := by
  rw [mem_Asp_iff ht hc ha, memA_iff ha hlt]
  constructor
  · rintro ⟨r, hr, h⟩
    refine ⟨r, hr, elS_injective ht (mulS_lt _ _) hlt ?_⟩
    rw [elS_phiS ht, h]
  · rintro ⟨r, hr, rfl⟩
    exact ⟨r, hr, (elS_phiS ht r).symm⟩

theorem exists_spPhi_eq (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true) {a : Msp}
    (h : a ∈ Asp) : ∃ r, r < 32 ∧ spPhi r = a := by
  obtain ⟨r, hr, e⟩ := (mem_Asp_iff ht hc ha).1 h
  exact ⟨r, hr, e⟩

theorem testBit_two_eq_false {c : ℕ} (h : c / 64 % 2 = 0) : (c / 16 % 16).testBit 2 = false := by
  have h4 : (2 : ℕ) ^ 2 = 4 := rfl
  rw [Nat.testBit_eq_decide_div_mod_eq, h4, decide_eq_false_iff_not]
  omega

theorem pPhi_mem_of_testBit {H : Subgroup Msp} (h1 : spX ∈ H) (h2 : spY ∈ H) (h4 : spW ∈ H)
    {r : ℕ} (hr : r.testBit 2 = false) : pPhi r ∈ H := by
  have h3 : (if r.testBit 2 = true then spU else 1) ∈ H := by simp [hr]
  unfold pPhi
  exact mul_mem (mul_mem (mul_mem (ite_one_mem _ h1) (ite_one_mem _ h2)) h3) (ite_one_mem _ h4)

theorem mem_AEsp_iff (ht : tabOK D = true) (hc : clOK D = true) {g : Msp} :
    g ∈ AEsp ↔ ∃ c < 256, memAE c = true ∧ elS c = g := by
  constructor
  · intro hg
    have hle : AEsp ≤ subS D memAE ht (cl_facts hc).2.1 := by
      refine (Subgroup.closure_le _).2 fun x hx => ?_
      simp only [Set.mem_setOf_eq, gensAEsp, List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨1, by norm_num, rfl, elS_1⟩
      · exact ⟨2, by norm_num, rfl, elS_2⟩
      · exact ⟨16, by norm_num, rfl, elS_16⟩
      · exact ⟨32, by norm_num, rfl, elS_32⟩
      · exact ⟨128, by norm_num, rfl, elS_128⟩
      · exact ⟨4, by norm_num, rfl, elS_4⟩
      · exact ⟨8, by norm_num, rfl, elS_8⟩
    exact hle hg
  · rintro ⟨c, -, hm, rfl⟩
    have hA : ∀ g ∈ gensAEsp, g ∈ AEsp := fun g hg => gen_mem hg
    have hb : c / 64 % 2 = 0 := by simpa [memAE] using hm
    exact mul_mem
      (ePhi_mem (hA _ (by simp [gensAEsp])) (hA _ (by simp [gensAEsp]))
        (hA _ (by simp [gensAEsp])) (hA _ (by simp [gensAEsp])) _)
      (pPhi_mem_of_testBit (hA _ (by simp [gensAEsp])) (hA _ (by simp [gensAEsp]))
        (hA _ (by simp [gensAEsp])) (testBit_two_eq_false hb))

theorem elS_mem_Esp_iff (ht : tabOK D = true) (hc : clOK D = true) {c : ℕ} (hlt : c < 256) :
    elS c ∈ Esp ↔ c / 16 = 0 := by
  rw [mem_Esp_iff ht hc]
  constructor
  · rintro ⟨d, hd, h⟩
    have := elS_injective ht (by omega) hlt h
    omega
  · intro h
    exact ⟨c, by omega, rfl⟩

theorem bool_char {b1 b2 b3 b4 b5 : Bool} (h : (b1 == (b2 && (!b3 || b4) && (b3 || b5))) = true) :
    b1 = true ↔ b2 = true ∧ (b3 = true → b4 = true) ∧ (¬ b3 = true → b5 = true) := by
  revert h
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;> decide

theorem elS_sq_iff (ht : tabOK D = true) (c : ℕ) : (mulS D c c == 0) = true ↔ elS c * elS c = 1 := by
  rw [beq_iff_eq, ← elS_mulS ht, ← elS_zero]
  exact ⟨congrArg elS, elS_injective ht (mulS_lt _ _) (by norm_num)⟩

theorem mem_Esp_char (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    (he : eCharOK D = true) {s : Msp} (hs : s ∈ AEsp) : s ∈ Esp ↔ s * s = 1 ∧
      (s ∈ Asp → ∀ z ∈ AEsp, s * z = z * s) ∧
      (s ∉ Asp → ∃ z ∈ AEsp, z ∉ Asp ∧ s⁻¹ * z ∉ Asp ∧ z * z = 1 ∧ s * z = z * s) := by
  obtain ⟨c, hlt, hm, rfl⟩ := (mem_AEsp_iff ht hc).1 hs
  have h := List.all_eq_true.1 he c (mem_l256 hlt)
  simp only [hm, Bool.not_true, Bool.false_or] at h
  have key := bool_char h
  have hall : (l256.all fun z => !memAE z || commS D c z) = true ↔
      ∀ z ∈ AEsp, elS c * z = z * elS c := by
    rw [List.all_eq_true]
    constructor
    · intro h z hz
      obtain ⟨d, hd, hmd, rfl⟩ := (mem_AEsp_iff ht hc).1 hz
      have := h d (mem_l256 hd)
      rw [hmd, Bool.not_true, Bool.false_or] at this
      exact (commS_iff ht).1 this
    · intro h d hd
      by_cases hmd : memAE d = true
      · rw [hmd, Bool.not_true, Bool.false_or]
        exact (commS_iff ht).2 (h _ ((mem_AEsp_iff ht hc).2 ⟨d, lt_of_mem_l256 hd, hmd, rfl⟩))
      · rw [Bool.eq_false_iff.2 hmd]
        rfl
  have hany : (l256.any fun z => memAE z && !memA D z && !memA D (mulS D (invS D c) z) &&
        mulS D z z == 0 && commS D c z) = true ↔
      ∃ z ∈ AEsp, z ∉ Asp ∧ (elS c)⁻¹ * z ∉ Asp ∧ z * z = 1 ∧ elS c * z = z * elS c := by
    rw [List.any_eq_true]
    constructor
    · rintro ⟨d, hd, h⟩
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
      have hdl := lt_of_mem_l256 hd
      refine ⟨elS d, (mem_AEsp_iff ht hc).2 ⟨d, hdl, h1, rfl⟩, ?_, ?_, (elS_sq_iff ht d).1 h4,
        (commS_iff ht).1 h5⟩
      · rw [elS_mem_Asp_iff ht hc ha hdl, h2]
        exact Bool.false_ne_true
      · rw [← elS_invS ht, ← elS_mulS ht, elS_mem_Asp_iff ht hc ha (mulS_lt _ _), h3]
        exact Bool.false_ne_true
    · rintro ⟨z, hz, h2, h3, h4, h5⟩
      obtain ⟨d, hd, h1, rfl⟩ := (mem_AEsp_iff ht hc).1 hz
      refine ⟨d, mem_l256 hd, ?_⟩
      rw [← elS_invS ht, ← elS_mulS ht, elS_mem_Asp_iff ht hc ha (mulS_lt _ _)] at h3
      rw [elS_mem_Asp_iff ht hc ha hd] at h2
      simp only [Bool.and_eq_true, Bool.not_eq_true']
      exact ⟨⟨⟨⟨h1, Bool.eq_false_iff.2 h2⟩, Bool.eq_false_iff.2 h3⟩, (elS_sq_iff ht d).2 h4⟩,
        (commS_iff ht).2 h5⟩
  rw [elS_mem_Esp_iff ht hc hlt, elS_mem_Asp_iff ht hc ha hlt, ← elS_sq_iff ht, ← hall, ← hany]
  exact beq_iff_eq.symm.trans key

theorem elS_dS_mem (ht : tabOK D = true) (r : ℕ) : elS (dS D r) ∈ Dsp := by
  have hD : ∀ g ∈ gensDsp, g ∈ Dsp := fun g hg => gen_mem hg
  simp only [dS, elS_mulS ht, elS_selK, elS_4, elS_8, elS_64]
  exact mul_mem (mul_mem (ite_one_mem _ (hD _ (by simp [gensDsp])))
    (ite_one_mem _ (hD _ (by simp [gensDsp])))) (ite_one_mem _ (hD _ (by simp [gensDsp])))

theorem exists_mem_Dsp (ht : tabOK D = true) (hc : clOK D = true) (ha : aOK D = true)
    (had : adOK D = true) {s : Msp} (hs : s ∈ Tsp) : ∃ d ∈ Dsp, s * d⁻¹ ∈ Asp := by
  obtain ⟨c, hlt, rfl⟩ := (mem_Tsp_iff ht).1 hs
  obtain ⟨r, -, hr⟩ := List.any_eq_true.1 (List.all_eq_true.1 had c (mem_l256 hlt))
  refine ⟨elS (dS D r), elS_dS_mem ht r, ?_⟩
  rw [← elS_invS ht, ← elS_mulS ht]
  exact (elS_mem_Asp_iff ht hc ha (mulS_lt _ _)).2 hr

theorem act_of_actS (ht : tabOK D = true) {g r0 r1 r2 r3 r4 : ℕ}
    (h : actS D g r0 r1 r2 r3 r4 = true) :
    elS g * spX1 * (elS g)⁻¹ = spPhi r0 ∧ elS g * spY1 * (elS g)⁻¹ = spPhi r1 ∧
      elS g * spX * (elS g)⁻¹ = spPhi r2 ∧ elS g * spY * (elS g)⁻¹ = spPhi r3 ∧
      elS g * spW * (elS g)⁻¹ = spPhi r4 := by
  simp only [actS, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [← elS_1, ← elS_conjS ht, h0, elS_phiS ht]
  · rw [← elS_2, ← elS_conjS ht, h1, elS_phiS ht]
  · rw [← elS_16, ← elS_conjS ht, h2, elS_phiS ht]
  · rw [← elS_32, ← elS_conjS ht, h3, elS_phiS ht]
  · rw [← elS_128, ← elS_conjS ht, h4, elS_phiS ht]

theorem act_of_actF (ht : tabOK D = true) {a : Msp} {g r0 r1 r2 r3 r4 : ℕ} (hg : enc a = g)
    (h : actF D g r0 r1 r2 r3 r4 = true) :
    a * spX1 * a⁻¹ = spPhi r0 ∧ a * spY1 * a⁻¹ = spPhi r1 ∧ a * spX * a⁻¹ = spPhi r2 ∧
      a * spY * a⁻¹ = spPhi r3 ∧ a * spW * a⁻¹ = spPhi r4 := by
  subst hg
  simp only [actF, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> refine enc_injective ?_ <;> rw [← conjK_enc]
  · rw [enc_spX1, h0, fullOf_eq ht, elS_phiS ht]
  · rw [enc_spY1, h1, fullOf_eq ht, elS_phiS ht]
  · rw [enc_spX, h2, fullOf_eq ht, elS_phiS ht]
  · rw [enc_spY, h3, fullOf_eq ht, elS_phiS ht]
  · rw [enc_spW, h4, fullOf_eq ht, elS_phiS ht]

theorem act_spUV (ht : tabOK D = true) (h : actS D 4 1 2 6 9 19 = true) :
    spUV * spX1 * spUV⁻¹ = spPhi (GL5.r0 GL5.uvC) ∧
      spUV * spY1 * spUV⁻¹ = spPhi (GL5.r1 GL5.uvC) ∧
      spUV * spX * spUV⁻¹ = spPhi (GL5.r2 GL5.uvC) ∧
      spUV * spY * spUV⁻¹ = spPhi (GL5.r3 GL5.uvC) ∧
      spUV * spW * spUV⁻¹ = spPhi (GL5.r4 GL5.uvC) := by
  have e := act_of_actS ht h
  rw [elS_4] at e
  exact e

theorem act_spT (ht : tabOK D = true) (h : actS D 8 1 2 5 11 17 = true) :
    spT * spX1 * spT⁻¹ = spPhi (GL5.r0 GL5.tC) ∧ spT * spY1 * spT⁻¹ = spPhi (GL5.r1 GL5.tC) ∧
      spT * spX * spT⁻¹ = spPhi (GL5.r2 GL5.tC) ∧ spT * spY * spT⁻¹ = spPhi (GL5.r3 GL5.tC) ∧
      spT * spW * spT⁻¹ = spPhi (GL5.r4 GL5.tC) := by
  have e := act_of_actS ht h
  rw [elS_8] at e
  exact e

theorem act_spU (ht : tabOK D = true) (h : actS D 64 2 1 8 4 16 = true) :
    spU * spX1 * spU⁻¹ = spPhi (GL5.r0 GL5.uC) ∧ spU * spY1 * spU⁻¹ = spPhi (GL5.r1 GL5.uC) ∧
      spU * spX * spU⁻¹ = spPhi (GL5.r2 GL5.uC) ∧ spU * spY * spU⁻¹ = spPhi (GL5.r3 GL5.uC) ∧
      spU * spW * spU⁻¹ = spPhi (GL5.r4 GL5.uC) := by
  have e := act_of_actS ht h
  rw [elS_64] at e
  exact e

theorem act_spRho (ht : tabOK D = true) (h : actF D rhoK 2 3 8 12 16 = true) :
    spRho * spX1 * spRho⁻¹ = spPhi (GL5.r0 GL5.rhoC) ∧
      spRho * spY1 * spRho⁻¹ = spPhi (GL5.r1 GL5.rhoC) ∧
      spRho * spX * spRho⁻¹ = spPhi (GL5.r2 GL5.rhoC) ∧
      spRho * spY * spRho⁻¹ = spPhi (GL5.r3 GL5.rhoC) ∧
      spRho * spW * spRho⁻¹ = spPhi (GL5.r4 GL5.rhoC) :=
  act_of_actF ht enc_spRho h

theorem pPhi_sg : ∀ j < 16, (sg (pPhi j).perm = 0 ↔ j < 8) := by decide +kernel

theorem elS_sg_iff (ht : tabOK D = true) {c : ℕ} (hc : c < 256) :
    sg (elS c).perm = 0 ↔ c < 128 := by
  rw [elS, Msp.perm_mul, ePhi_perm ht (Nat.mod_lt c (by norm_num)), one_mul,
    pPhi_sg _ (Nat.mod_lt (c / 16) (by norm_num))]
  omega

theorem mem_S1_iff {s : Msp} : s ∈ Tsp ⊓ (Perm.sign.comp θsp).ker ↔ s ∈ Tsp ∧ sg s.perm = 0 := by
  rw [Subgroup.mem_inf, MonoidHom.mem_ker, MonoidHom.comp_apply, θsp_apply]
  unfold sg
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by rw [if_pos h2]⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, ?_⟩
    by_contra h
    rw [if_neg h] at h2
    exact absurd h2 (by decide)

theorem mem_S1_iff_elS (ht : tabOK D = true) {g : Msp} :
    g ∈ Tsp ⊓ (Perm.sign.comp θsp).ker ↔ ∃ c < 128, elS c = g := by
  rw [mem_S1_iff, mem_Tsp_iff ht]
  constructor
  · rintro ⟨⟨c, hc, rfl⟩, hs⟩
    exact ⟨c, (elS_sg_iff ht hc).1 hs, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    exact ⟨⟨c, by omega, rfl⟩, (elS_sg_iff ht (by omega)).2 hc⟩

theorem card_S1 (ht : tabOK D = true) : Nat.card ↥(Tsp ⊓ (Perm.sign.comp θsp).ker) = 128 :=
  card_of_param elS (fun _ => mem_S1_iff_elS ht) fun _ hk _ hl h =>
    elS_injective ht (by omega) (by omega) h

theorem w4_facts (hw : w4OK D = true) {c : ℕ} (hc : c < 256) (hm : memB D.W4M c = true) :
    ∃ r < 16, phiS D r = c := by
  have h := List.all_eq_true.1 hw c (mem_l256 hc)
  simp only [hm, Bool.not_true, Bool.false_or, List.any_eq_true, beq_iff_eq] at h
  obtain ⟨r, hr, h⟩ := h
  exact ⟨r, lt_of_mem_l16 hr, h⟩

theorem exists_conj_W4 (ht : tabOK D = true) (hw : w4OK D = true) (hs1 : s1OK D = true)
    {z : Msp} (hz : z ∈ Tsp ⊓ (Perm.sign.comp θsp).ker) (hz2 : z * z = 1) :
    ∃ m : Msp, ∃ r, r < 16 ∧ m * z * m⁻¹ = spPhi r := by
  obtain ⟨c, hc, rfl⟩ := (mem_S1_iff_elS ht).1 hz
  have hsq : (mulS D c c == 0) = true := (elS_sq_iff ht c).2 hz2
  have h := List.all_eq_true.1 hs1 c (mem_l128 hc)
  simp only [hsq, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
  generalize rd 18 D.WIT c = e at h
  obtain ⟨hw4, hcase⟩ := h
  obtain ⟨r, hr, hre⟩ := w4_facts hw (Nat.mod_lt _ (by norm_num)) hw4
  have hW : elS (e % 256) = spPhi r := by rw [← hre, elS_phiS ht]
  have hy := elS_conjS ht (e / 256 % 256) c
  split_ifs at hcase
  · refine ⟨elS (e / 256 % 256), r, hr, ?_⟩
    rw [← hy, ← hW, beq_iff_eq.1 hcase]
  · refine ⟨spM1 * elS (e / 256 % 256), r, hr, ?_⟩
    have h2 := beq_iff_eq.1 hcase
    rw [fullOf_eq ht, fullOf_eq ht, ← enc_spM1, conjK_enc] at h2
    have h3 := enc_injective h2
    rw [hy, hW] at h3
    rw [← h3]
    group
  · refine ⟨spM2 * elS (e / 256 % 256), r, hr, ?_⟩
    have h2 := beq_iff_eq.1 hcase
    rw [fullOf_eq ht, fullOf_eq ht, ← enc_spM2, conjK_enc] at h2
    have h3 := enc_injective h2
    rw [hy, hW] at h3
    rw [← h3]
    group

end CFSG.KC.Stroth77SP
