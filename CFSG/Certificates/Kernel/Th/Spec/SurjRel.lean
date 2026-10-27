
module

public import CFSG.Certificates.Kernel.Th.Spec.SurjCheckBase
public import CFSG.Certificates.Kernel.Th.SoundnessGen

public section

namespace CFSG.KC.Th.Spec

open CFSG.KC.Th CFSG.KC.Th.BigS CFSG.KC.Th.Soundness

private theorem srAndB {a b : Bool} : andB a b = true ↔ a = true ∧ b = true := by
  cases a <;> cases b <;> simp [andB]

private theorem srRels (RB : ℕ → ℕ) (c rm ONE GR IR : ℕ) : ∀ n : ℕ,
    (Nat.rec (motive := fun _ => Bool) true (fun r ih => andB ih (relOK RB c rm ONE GR IR r)) n) =
      true → ∀ k < n, relOK RB c rm ONE GR IR k = true
  | 0, _, k, hk => absurd hk (Nat.not_lt_zero _)
  | n + 1, h, k, hk => by
    obtain ⟨h1, h2⟩ := srAndB.1 h
    by_cases hkn : k = n
    · subst hkn
      exact h2
    · exact srRels RB c rm ONE GR IR n h1 k (by omega)

private theorem srSel : ∀ k < 39, Hsw.sel k = Hsw.list.getD k 0 := by decide +kernel

private theorem srByte : ∀ (r : List (ℕ × Bool)), (∀ l ∈ r, l.1 < 8) →
    ∀ (i : ℕ) (hi : i < r.length), wordNatN r / 256 ^ i % 256 = codeN (r[i]'hi)
  | [], _, i, hi => absurd hi (Nat.not_lt_zero _)
  | l :: w, hl, i, hi => by
    have hc : codeN l < 256 := by
      have := hl l (by simp)
      unfold codeN
      split_ifs <;> omega
    cases i with
    | zero =>
      show (codeN l + 256 * wordNatN w) / 256 ^ 0 % 256 = codeN l
      omega
    | succ j =>
      have ih := srByte w (fun m hm => hl m (by simp [hm])) j (by simpa using hi)
      show (codeN l + 256 * wordNatN w) / 256 ^ (j + 1) % 256 = codeN (w[j]'(by simpa using hi))
      rw [pow_succ', ← Nat.div_div_eq_div_mul,
        show (codeN l + 256 * wordNatN w) / 256 = wordNatN w by omega]
      exact ih

private theorem srEnt (r : List (ℕ × Bool)) (hl : ∀ l ∈ r, l.1 < 8) (hlen : r.length < 1024) :
    bitsN (entN r) 2 10 = r.length ∧ ∀ (i : ℕ) (hi : i < r.length),
      Nat.land (Nat.shiftRight (Nat.shiftRight (entN r) 12) (Nat.mul 8 i)) 255 =
        2 * (r[i]'hi).1 + (if (r[i]'hi).2 then 0 else 1) := by
  have e : entN r = 4 * r.length + 4096 * wordNatN r := rfl
  constructor
  · rw [CFSG.KC.Th.Spec.bitsN_eq, e, Nat.shiftRight_eq_div_pow]
    omega
  · intro i hi
    have h2 : Nat.shiftRight (entN r) 12 = wordNatN r := by
      rw [e]
      show (4 * r.length + 4096 * wordNatN r) >>> 12 = _
      rw [Nat.shiftRight_eq_div_pow]
      norm_num
      omega
    have h1 : Nat.shiftRight (Nat.shiftRight (entN r) 12) (Nat.mul 8 i) = wordNatN r / 256 ^ i := by
      rw [h2]
      show wordNatN r >>> (8 * i) = _
      rw [Nat.shiftRight_eq_div_pow, pow_mul]
      norm_num
    rw [h1]
    show wordNatN r / 256 ^ i &&& 255 = _
    rw [show (255 : ℕ) = 2 ^ 8 - 1 by norm_num, Nat.and_two_pow_sub_one_eq_mod]
    have h3 := srByte r hl i hi
    unfold codeN at h3
    simpa using h3

theorem relators_spec {RB : ℕ → ℕ} {c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE : ℕ}
    (K : constsOK c rm tm0 tm1 tm2 tm3 tm4 tm5 tm6 tm7 up dg ONE = true)
    (p : TauCeti.GroupPresentation) (hp : IsHsw p)
    (h : relsOK RB c rm ONE SurjS.GR SurjS.IR = true) :
    ∀ r ∈ p.relatorLetters, (∀ l ∈ r, l.1 < 8) ∧ wordMat RB r = 1 := by
  obtain ⟨hgen, hlen, hmap⟩ := hp
  intro r hr
  have hl : ∀ l ∈ r, l.1 < 8 := by
    rw [TauCeti.GroupPresentation.relatorLetters_def, List.mem_map] at hr
    obtain ⟨w, -, rfl⟩ := hr
    intro l hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    show (l'.1 : ℕ) < 8
    calc (l'.1 : ℕ) < p.generatorCount := l'.1.isLt
      _ = 8 := hgen
  have hmem : entN r ∈ Hsw.list := by
    rw [← hmap]
    exact List.mem_map_of_mem hr
  obtain ⟨k, hk, hkr⟩ := List.mem_iff_getElem.1 hmem
  have hk39 : k < 39 := by simpa [Hsw.list] using hk
  have hsel : Hsw.sel k = entN r := by
    rw [srSel k hk39, List.getD_eq_getElem _ _ hk, hkr]
  have hrel := srRels RB c rm ONE SurjS.GR SurjS.IR 39 h k hk39
  unfold relOK at hrel
  rw [hsel] at hrel
  obtain ⟨-, hrel2⟩ := srAndB.1 hrel
  have hONE := Nat.eq_of_beq_eq_true hrel2
  obtain ⟨he1, he2⟩ := srEnt r hl (hlen r hr)
  have hprod := relProd_spec (RB := RB) K hl he1 he2
  refine ⟨hl, ?_⟩
  rw [← hprod, ← hONE]
  exact pkMat_one K

end CFSG.KC.Th.Spec

end
