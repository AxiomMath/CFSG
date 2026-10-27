module

public import Certificates.Data.Kernel.CertF8.Syl9640
public import CFSG.Certificates.Kernel.CertF8.F512Sound
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanChevOuterD48SylowGroup

public section

namespace CFSG.KC.CertF8.S9640

open CFSG.AGLEmbedding.ChevOuterD48 CFSG.KC.CertF8 CFSG.KC.Misc.Clos CFSG.Open
open CFSG.KC.CertF8.D48 (letK oneK)
open CFSG.KC.G28 (fld)

@[expose] noncomputable def encG (g : GL (Fin 8) GF512) : ℕ :=
  codeA (ofMat (g : Matrix (Fin 8) (Fin 8) GF512))

theorem ofMat_mul (M N : Matrix (Fin 8) (Fin 8) GF512) :
    ofMat (M * N) = mulArr (ofMat M) (ofMat N) :=
  eq_of_toMat_eq (size_ofMat _) (size_mulArr _ _) (by
    rw [toMat_mulArr, toMat_ofMat, toMat_ofMat, toMat_ofMat])

theorem encG_enc (h1 : codeA oneArr = oneK) : ClosEnc encG mulS512 oneK where
  enc_one := h1
  enc_mul a b := by
    change codeA (ofMat ((a : Matrix (Fin 8) (Fin 8) GF512) * b)) = _
    rw [ofMat_mul, codeA_mulArr]
    rfl
  inj a b h := by
    have e := codeA_inj (size_ofMat _) (size_ofMat _) h
    refine Units.ext ?_
    rw [← toMat_ofMat (a : Matrix (Fin 8) (Fin 8) GF512), e, toMat_ofMat]

theorem encG_letter (hl : ∀ k < 24, codeA (letterArr k) = letK.getD k oneK) {k : ℕ}
    (hk : k < 24) : encG (letterGL k) = letK.getD k oneK := by
  have e : ofMat (letterMat k) = letterArr k :=
    eq_of_toMat_eq (size_ofMat _) (size_letterArr k) (by rw [toMat_ofMat, toMat_letterArr hk])
  change codeA (ofMat (letterMat k)) = _
  rw [e, hl k hk]

theorem encG_word (h1 : codeA oneArr = oneK)
    (hl : ∀ k < 24, codeA (letterArr k) = letK.getD k oneK) :
    ∀ w : List ℕ, (∀ l ∈ w, l < 24) → encG (wordGL w) = wordS w
  | [], _ => (encG_enc h1).enc_one
  | l :: w, hw => by
    have e : wordGL (l :: w) = letterGL l * wordGL w := by simp [wordGL]
    rw [e, (encG_enc h1).enc_mul, encG_letter hl (hw l List.mem_cons_self),
      encG_word h1 hl w (fun a ha => hw a (List.mem_cons_of_mem l ha))]
    rfl

theorem encG_pow (h1 : codeA oneArr = oneK) (g : GL (Fin 8) GF512) :
    ∀ n : ℕ, encG (g ^ n) = powS (encG g) n
  | 0 => by rw [pow_zero]; exact (encG_enc h1).enc_one
  | n + 1 => by
    rw [pow_succ', (encG_enc h1).enc_mul, encG_pow h1 g n]
    rfl

theorem orB_true {a b : Bool} (h : CFSG.KC.Ord.orB a b = true) : a = true ∨ b = true := by
  cases a
  · exact Or.inr h
  · exact Or.inl rfl

theorem eqB_eq {a b : Bool} (h : eqB a b = true) : a = b := by
  revert h
  cases a <;> cases b <;> decide

theorem memF_spec {r o j : ℕ} : ∀ n, memF r o n j = true → ∃ t < n, fld r (o + 10 * t) 10 = j
  | 0, h => by
    change false = true at h
    cases h
  | n + 1, h => by
    change CFSG.KC.Ord.orB (Nat.beq (fld r (Nat.add o (Nat.mul 10 n)) 10) j) (memF r o n j) = true
      at h
    rcases orB_true h with h | h
    · exact ⟨n, by omega, Nat.eq_of_beq_eq_true h⟩
    · obtain ⟨t, ht, e⟩ := memF_spec n h
      exact ⟨t, by omega, e⟩

theorem rowAt_parts {T : ℕ → ℕ} {j : ℕ} (h : rowAt T j = true) :
    treeAt mulS512 oneK (G T) 2 (E T) (PA T) j = true ∧ sortAt 729 (E T) (SG T) j = true ∧
      closedAt mulS512 (G T) 2 729 (E T) (CT T) j = true ∧ cubeF T j = cubeK (E T j) ∧
      conjAt T j (E T j) = true := by
  rw [rowAt] at h
  obtain ⟨h1, h⟩ := andB_eq_true h
  obtain ⟨h2, h⟩ := andB_eq_true h
  obtain ⟨h3, h⟩ := andB_eq_true h
  rw [letB_eq] at h
  obtain ⟨h4, h5⟩ := andB_eq_true h
  exact ⟨h1, h2, h3, eqB_eq h4, h5⟩

theorem cubeK_of {c : ℕ} (h : mulS512 c (mulS512 c c) = oneK) : cubeK c = true := by
  rw [cubeK, letB_eq, h]
  exact Nat.beq_refl oneK

theorem conj_parts {T : ℕ → ℕ} {j : ℕ} (h : conjAt T j (E T j) = true) (hc : cubeF T j = true) :
    (∃ t < 3, fld (T 739) (0 + 10 * t) 10 = j) ∨
      (fld (T j) 618 10 < 729 ∧ fld (T j) 628 3 < 8 ∧
        mulS512 (E T (fld (T j) 618 10)) (E T j) =
          mulS512 (E T (fld (T (731 + fld (T j) 628 3)) 0 10)) (E T (fld (T j) 618 10))) := by
  rw [conjAt] at h
  rcases orB_true (impB_eq_true h hc) with h | h
  · exact Or.inl (memF_spec 3 h)
  · rw [letB_eq, letB_eq, letB_eq, letB_eq] at h
    obtain ⟨h1, h⟩ := andB_eq_true h
    obtain ⟨h2, h3⟩ := andB_eq_true h
    exact Or.inr ⟨Nat.blt_eq.mp h1, Nat.blt_eq.mp h2, Nat.eq_of_beq_eq_true h3⟩

theorem rep_lt {T : ℕ → ℕ} {q j : ℕ} (h : repAt T q j = true) :
    fld (T (731 + q)) 0 10 < 729 := by
  rw [repAt, letB_eq, letB_eq] at h
  exact Nat.blt_eq.mp (andB_eq_true h).1

theorem rep_mem {T : ℕ → ℕ} {q j : ℕ} (h : repAt T q j = true) (hc : cubeF T j = true)
    (hm : mulS512 (E T j) (E T (fld (T (731 + q)) 0 10)) =
      mulS512 (E T (fld (T (731 + q)) 0 10)) (E T j)) :
    ∃ t < 9, fld (T (731 + q)) (10 + 10 * t) 10 = j := by
  rw [repAt, letB_eq, letB_eq] at h
  have h2 := impB_eq_true (andB_eq_true h).2 hc
  rw [letB_eq, letB_eq] at h2
  refine memF_spec 9 (impB_eq_true h2 ?_)
  have hm' : mulS512 (E T j) (E T (fld (T (Nat.add 731 q)) 0 10)) =
      mulS512 (E T (fld (T (Nat.add 731 q)) 0 10)) (E T j) := hm
  rw [hm']
  exact Nat.beq_refl _

theorem sound9640 {T : ℕ → ℕ} (h1 : codeA oneArr = oneK)
    (hl : ∀ k < 24, codeA (letterArr k) = letK.getD k oneK)
    (hrow : ∀ j < 729, rowAt T j = true) (hrep : ∀ q < 8, ∀ j < 729, repAt T q j = true)
    (hgen : gensOK T = true) :
    Nat.card sylowGroup = 3 ^ 6 ∧ ∀ A : Subgroup (GL (Fin 8) GF512), A ≤ sylowGroup →
      IsElemAbelian 3 A → Nat.card A ≤ 3 ^ 2 := by
  classical
  have henc := encG_enc h1
  rw [gensOK] at hgen
  obtain ⟨hgA, hgB⟩ := andB_eq_true hgen
  have eA : G T 0 = encG sylowA := by
    rw [Nat.eq_of_beq_eq_true hgA, sylowA, encG_word h1 hl _ sylowWordA_lt]
  have eB : G T 1 = encG sylowB := by
    rw [Nat.eq_of_beq_eq_true hgB, CFSG.KC.G28.letN_eq, sylowB, encG_pow h1,
      encG_word h1 hl _ sylowWordT_lt]
  let gens : List (GL (Fin 8) GF512) := [sylowA, sylowB]
  have hcl : Subgroup.closure {g | g ∈ gens} = sylowGroup := by
    rw [sylowGroup]
    congr 1
    ext g
    simp [gens]
  have hG : ∀ j < gens.length, G T j = encG (gens.getD j 1) := by
    intro j hj
    have : j = 0 ∨ j = 1 := by
      simp only [gens, List.length_cons, List.length_nil] at hj
      omega
    rcases this with rfl | rfl
    · exact eA
    · exact eB
  have hrw := fun j hj => rowAt_parts (hrow j hj)
  obtain ⟨hmem, -, hclosed⟩ := clos_card henc gens hG (by norm_num : 0 < 729)
    (fun k hk => (hrw k hk).1) (fun i hi => (hrw i hi).2.1)
  obtain ⟨hcard, hall⟩ := hclosed (CT := CT T) (fun k hk => (hrw k hk).2.2.1)
  rw [hcl] at hmem hcard hall
  refine ⟨by rw [hcard]; norm_num, ?_⟩
  intro A hAP hA
  have hcube : ∀ y ∈ sylowGroup, y ^ 3 = 1 → ∀ j < 729, encG y = E T j → cubeF T j = true := by
    intro y _ h3 j hj hyj
    rw [(hrw j hj).2.2.2.1]
    apply cubeK_of
    rw [← hyj, ← henc.enc_mul, ← henc.enc_mul, ← pow_three, h3, henc.enc_one]
  by_cases hZ : ∀ y ∈ A, ∃ t < 3, encG y = E T (fld (T 739) (0 + 10 * t) 10)
  · choose! f hf hfe using hZ
    have hinj : Function.Injective (fun y : A => (⟨f y, hf y y.2⟩ : Fin 3)) := by
      intro a b hab
      have e : f a = f b := congrArg Fin.val hab
      exact Subtype.ext (henc.inj (by rw [hfe a a.2, hfe b b.2, e]))
    have := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    norm_num
    omega
  · push Not at hZ
    obtain ⟨y, hyA, hy⟩ := hZ
    have hyP := hAP hyA
    obtain ⟨j, hj, hyj⟩ := hall y hyP
    have hcj := hcube y hyP (hA.2 y hyA) j hj hyj
    rcases conj_parts (hrw j hj).2.2.2.2 hcj with ⟨t, ht, e⟩ | ⟨hg, hq, hgy⟩
    · exact absurd (by rw [e]; exact hyj) (hy t ht)
    have hr := rep_lt (hrep _ hq 0 (by norm_num))
    obtain ⟨h, hhP, hh⟩ := hmem _ hg
    obtain ⟨x, hxP, hx⟩ := hmem _ hr
    have hhy : h * y = x * h := henc.inj (by rw [henc.enc_mul, henc.enc_mul, hh, hx, hyj, hgy])
    have hx' : x = h * y * h⁻¹ := by rw [hhy, mul_inv_cancel_right]
    have key : ∀ w ∈ A, ∃ t < 9, ∃ k, encG (h * w * h⁻¹) = E T k ∧
        fld (T (731 + fld (T j) 628 3)) (10 + 10 * t) 10 = k := by
      intro w hw
      have hwP : h * w * h⁻¹ ∈ sylowGroup := mul_mem (mul_mem hhP (hAP hw)) (inv_mem hhP)
      obtain ⟨k, hk, hwk⟩ := hall _ hwP
      have hw3 : (h * w * h⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hA.2 w hw, mul_one, mul_inv_cancel]
      have hck := hcube _ hwP hw3 k hk hwk
      have hwy : w * y = y * w := congrArg Subtype.val (hA.1.is_comm.comm ⟨w, hw⟩ ⟨y, hyA⟩)
      have hcomm : (h * w * h⁻¹) * x = x * (h * w * h⁻¹) := by
        rw [hx']
        simp only [mul_assoc, inv_mul_cancel_left]
        rw [← mul_assoc w y, hwy, mul_assoc]
      obtain ⟨t, ht, e⟩ := rep_mem (hrep _ hq k hk) hck (by
        rw [← hwk, ← hx, ← henc.enc_mul, ← henc.enc_mul, hcomm])
      exact ⟨t, ht, k, hwk, e⟩
    choose! f hf k hke hfe using key
    have hinj : Function.Injective (fun w : A => (⟨f w, hf w w.2⟩ : Fin 9)) := by
      intro a b hab
      have e1 : f a = f b := congrArg Fin.val hab
      have e2 : k a = k b := by rw [← hfe a a.2, ← hfe b b.2, e1]
      have e3 : h * a * h⁻¹ = h * b * h⁻¹ := henc.inj (by rw [hke a a.2, hke b b.2, e2])
      exact Subtype.ext (mul_left_cancel (mul_right_cancel e3))
    have := Nat.card_le_card_of_injective _ hinj
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at this
    norm_num
    exact this

end CFSG.KC.CertF8.S9640
