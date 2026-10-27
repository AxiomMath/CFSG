module

public import Certificates.Data.Kernel.FiveStdKDiag
public import CFSG.Certificates.Kernel.FiveStdKOrbSound

public section

namespace CFSG.KC.FiveStdK

open CFSG.GH74.GLS.LU.Local.FiveStd

theorem orB_eq (a b : Bool) : orB a b = (a || b) := by cases a <;> rfl

theorem anyN_iff (n : Nat) (f : Nat → Bool) : anyN n f = true ↔ ∃ i < n, f i = true := by
  induction n with
  | zero => exact ⟨fun h => absurd h Bool.false_ne_true, fun ⟨i, hi, _⟩ => absurd hi (Nat.not_lt_zero i)⟩
  | succ n ih =>
    change orB (f n) (anyN n f) = true ↔ _
    rw [orB_eq, Bool.or_eq_true, ih]
    constructor
    · rintro (h | ⟨i, hi, h⟩)
      · exact ⟨n, Nat.lt_succ_self n, h⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi, h⟩
    · rintro ⟨i, hi, h⟩
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with h' | rfl
      · exact Or.inr ⟨i, h', h⟩
      · exact Or.inl h

theorem beq_iff_eq' (a b : Nat) : Nat.beq a b = true ↔ a = b :=
  ⟨Nat.eq_of_beq_eq_true, fun h => h ▸ Nat.beq_refl a⟩

theorem powK_codeE (x : E) (n : Nat) : powK (codeE x) n = codeE (powE x n) := by
  induction n with
  | zero => exact codeE_oneE.symm
  | succ n ih =>
    change mulK (powK (codeE x) n) (codeE x) = _
    rw [ih, ← codeE_mulE, powE]

theorem codeE_zE : codeE zE = zK := rfl

theorem codeE_eq_oneK {x : E} : codeE x = oneK ↔ x = oneE :=
  ⟨fun h => codeE_injective (h.trans codeE_oneE.symm), fun h => h ▸ codeE_oneE⟩

theorem fS_codeE (x : E) : fS (codeE x) = bv x.s := (fields_codeE x).2.2.2.2.2.2.2.2

theorem beq5 : ∀ u v : Fin 5, Nat.beq u.val v.val = (u == v) := by decide

theorem bv_beq0 (s : Bool) : Nat.beq (bv s) 0 = !s := by cases s <;> rfl

theorem inKKK_codeE (x : E) : inKKK (codeE x) = inKK x := by
  obtain ⟨x0, x1, x2, x3, x4, x5, x6, x7, x8⟩ := fields_codeE x
  unfold inKKK
  rw [x0, x1, x2, x3, x4, x5, x6, x7, x8, andB_eq]
  have hA : Nat.mod (Nat.add (Nat.mul x.a0.val x.a3.val) (Nat.mul 4 (Nat.mul x.a1.val x.a2.val))) 5 =
      (detA x).val := val_det _ _ _ _
  have hB : Nat.mod (Nat.add (Nat.mul x.b0.val x.b3.val) (Nat.mul 4 (Nat.mul x.b1.val x.b2.val))) 5 =
      (detB x).val := val_det _ _ _ _
  rw [hA, hB, beq5, bv_beq0]
  rfl

theorem memA_iff {A nA c : Nat} : memA A nA c = true ↔ ∃ i < nA, f20 A i = c := by
  unfold memA
  rw [anyN_iff]
  exact exists_congr fun i => and_congr_right fun _ => beq_iff_eq' _ _

theorem sylOK_spec {OR OM : List Nat} {nR x y p W : Nat} (h : sylOK OR OM nR x y p W = true) :
    validK x = true ∧ validK y = true ∧ mulK x y = mulK y x ∧ powK x p = oneK ∧ powK y p = oneK ∧
      x ≠ oneK ∧ y ≠ oneK ∧ ∀ t < p * p - 1, ∃ k < nR, ∃ j < OM.getD k 0,
        oCode (f96 (OR.getD k 0) j) = mulK (powK x ((t + 1) / p)) (powK y ((t + 1) % p)) := by
  unfold sylOK at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h4
  obtain ⟨h7, h8⟩ := andB_true h6
  obtain ⟨h9, h10⟩ := andB_true h8
  obtain ⟨h11, h12⟩ := andB_true h10
  obtain ⟨h13, h14⟩ := andB_true h12
  refine ⟨h1, h3, Nat.eq_of_beq_eq_true h5, Nat.eq_of_beq_eq_true h7, Nat.eq_of_beq_eq_true h9,
    fun e => by rw [e, Nat.beq_refl] at h11; exact absurd h11 (by decide),
    fun e => by rw [e, Nat.beq_refl] at h13; exact absurd h13 (by decide), fun t ht => ?_⟩
  have := (allN_iff _ _).1 h14 t ht
  unfold sylPt at this
  rw [letB_eq, letB_eq, letB_eq] at this
  obtain ⟨ha, hb⟩ := andB_true this
  obtain ⟨hc, hd⟩ := andB_true hb
  exact ⟨_, (blt_iff _ _).1 ha, _, (blt_iff _ _).1 hc, Nat.eq_of_beq_eq_true hd⟩

theorem syl_sound {OR OM : List Nat} {nR x y p W : Nat} (h : sylOK OR OM nR x y p W = true) :
    validE (decE x) = true ∧ validE (decE y) = true ∧
      mulE (decE x) (decE y) = mulE (decE y) (decE x) ∧ powE (decE x) p = oneE ∧
      powE (decE y) p = oneE ∧ decE x ≠ oneE ∧ decE y ≠ oneE ∧
      ∀ i < p, ∀ j < p, (i ≠ 0 ∨ j ≠ 0) → ∃ k < nR, ∃ j' < OM.getD k 0,
        oCode (f96 (OR.getD k 0) j') = codeE (mulE (powE (decE x) i) (powE (decE y) j)) := by
  obtain ⟨hx, hy, hxy, hxp, hyp, hx1, hy1, hall⟩ := sylOK_spec h
  have cx := codeE_decE (validK_lt hx)
  have cy := codeE_decE (validK_lt hy)
  refine ⟨valid_decE hx, valid_decE hy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply codeE_injective
    rw [codeE_mulE, codeE_mulE, cx, cy, hxy]
  · rw [← codeE_eq_oneK, ← powK_codeE, cx, hxp]
  · rw [← codeE_eq_oneK, ← powK_codeE, cy, hyp]
  · intro e
    exact hx1 (by rw [← cx, codeE_eq_oneK.2 e])
  · intro e
    exact hy1 (by rw [← cy, codeE_eq_oneK.2 e])
  · intro i hi j hj hij
    have hp : 0 < p := by omega
    have hpos : 1 ≤ p * i + j := by
      rcases hij with h | h
      · have : 1 ≤ p * i := Nat.mul_pos hp (Nat.pos_of_ne_zero h)
        omega
      · omega
    have hlt : p * i + j - 1 < p * p - 1 := by
      have : p * i + j < p * p := by
        calc p * i + j < p * i + p := by omega
          _ = p * (i + 1) := by ring
          _ ≤ p * p := Nat.mul_le_mul_left p hi
      omega
    obtain ⟨k, hk, j', hj', he⟩ := hall _ hlt
    have hs : p * i + j - 1 + 1 = p * i + j := by omega
    rw [hs] at he
    have hdiv : (p * i + j) / p = i := by
      rw [Nat.add_comm, Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hj, Nat.zero_add]
    have hmod : (p * i + j) % p = j := by
      rw [Nat.add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hj]
    rw [hdiv, hmod, ← cx, ← cy, powK_codeE, powK_codeE, ← codeE_mulE] at he
    exact ⟨k, hk, j', hj', he⟩

theorem dAPt_spec {A nA g i : Nat} (h : dAPt A nA g i = true) :
    (i + 1 < nA → f20 A i < f20 A (i + 1)) ∧ validK (f20 A i) = true ∧
      mulK (f20 A i) g = mulK g (f20 A i) ∧ powK (f20 A i) 5 = oneK ∧ inKKK (f20 A i) = true ∧
      ∀ j < nA, ∃ i' < nA, f20 A i' = mulK (f20 A i) (f20 A j) := by
  unfold dAPt at h
  rw [letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  obtain ⟨h5, h6⟩ := andB_true h4
  obtain ⟨h7, h8⟩ := andB_true h6
  obtain ⟨h9, h10⟩ := andB_true h8
  exact ⟨fun hi => (blt_iff _ _).1 ((ifB_true h1).1 ((blt_iff _ _).2 hi)), h3, Nat.eq_of_beq_eq_true h5,
    Nat.eq_of_beq_eq_true h7, h9, fun j hj => memA_iff.1 ((allN_iff _ _).1 h10 j hj)⟩

theorem dBPt_spec {A nA B v0 k : Nat} (h : dBPt A nA B v0 k = true) :
    (powK (f20 B k) 5 = oneK → ∃ i < nA, f20 A i = f20 B k) ∧
      (∀ j < nA, ∃ i < nA, f20 A i = cjK (f20 B k) (invK (f20 B k)) (f20 A j)) ∧
      (fS (mulK v0 (f20 B k)) = 0 → ∀ j < nA,
        cjK (mulK v0 (f20 B k)) (invK (mulK v0 (f20 B k))) (f20 A j) = invK (f20 A j)) := by
  unfold dBPt at h
  rw [letB_eq, letB_eq] at h
  obtain ⟨h1, h2⟩ := andB_true h
  obtain ⟨h3, h4⟩ := andB_true h2
  rw [letB_eq, letB_eq] at h4
  refine ⟨fun hp => memA_iff.1 ((ifB_true h1).1 ((beq_iff_eq' _ _).2 hp)),
    fun j hj => memA_iff.1 ((allN_iff _ _).1 h3 j hj), fun hs j hj => ?_⟩
  have := (allN_iff _ _).1 ((ifB_true h4).1 ((beq_iff_eq' _ _).2 hs)) j hj
  rw [letB_eq] at this
  exact Nat.eq_of_beq_eq_true this

theorem dgOK_spec {A nA B Mc g v0 : Nat} (h : dgOK A nA B Mc g v0 = true) :
    (∀ i < nA, dAPt A nA g i = true) ∧ ∀ k < Mc, dBPt A nA B v0 k = true := by
  obtain ⟨h1, h2⟩ := andB_true h
  exact ⟨(allN_iff _ _).1 h1, (allN_iff _ _).1 h2⟩

theorem dg_sound {A nA B Mc g v0 : Nat} (h : dgOK A nA B Mc g v0 = true) (hg : validK g = true)
    (hv0 : validK v0 = true) (hB : ∀ k < Mc, validK (f20 B k) = true) :
    (decL (f20 A) nA).Nodup ∧
    (∀ a ∈ decL (f20 A) nA, validE a = true ∧ mulE a (decE g) = mulE (decE g) a ∧
      powE a 5 = oneE ∧ inKK a = true ∧ ∀ a' ∈ decL (f20 A) nA, mulE a a' ∈ decL (f20 A) nA) ∧
    (∀ b ∈ decL (f20 B) Mc, (powE b 5 = oneE → b ∈ decL (f20 A) nA) ∧
      (∀ a ∈ decL (f20 A) nA, conjE b a ∈ decL (f20 A) nA) ∧
      ((mulE (decE v0) b).s = false → ∀ a ∈ decL (f20 A) nA, conjE (mulE (decE v0) b) a = invE a)) := by
  obtain ⟨hA, hBp⟩ := dgOK_spec h
  have hAs := fun i hi => dAPt_spec (hA i hi)
  have hlt : ∀ i < nA, f20 A i < 781250 := fun i hi => validK_lt (hAs i hi).2.1
  have hcA : ∀ i < nA, codeE (decE (f20 A i)) = f20 A i := fun i hi => codeE_decE (hlt i hi)
  have hcB : ∀ k < Mc, codeE (decE (f20 B k)) = f20 B k := fun k hk => codeE_decE (validK_lt (hB k hk))
  have cg := codeE_decE (validK_lt hg)
  have cv := codeE_decE (validK_lt hv0)
  have hmemA : ∀ c, (∃ i < nA, f20 A i = codeE c) → c ∈ decL (f20 A) nA := by
    rintro c ⟨i, hi, he⟩
    exact mem_decL.2 ⟨i, hi, by rw [he, decE_codeE]⟩
  refine ⟨decL_nodup hlt fun i j hij hj => ?_, ?_, ?_⟩
  · induction j with
    | zero => omega
    | succ j ih =>
      have hs := (hAs j (by omega)).1 hj
      rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h' | rfl
      · exact (ih h' (by omega)).trans hs
      · exact hs
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := mem_decL.1 ha
    obtain ⟨-, hv, hc, h5, hk, hcl⟩ := hAs i hi
    refine ⟨valid_decE hv, ?_, ?_, ?_, ?_⟩
    · apply codeE_injective
      rw [codeE_mulE, codeE_mulE, hcA i hi, cg, hc]
    · rw [← codeE_eq_oneK, ← powK_codeE, hcA i hi, h5]
    · rw [← inKKK_codeE, hcA i hi, hk]
    · intro a' ha'
      obtain ⟨j, hj, rfl⟩ := mem_decL.1 ha'
      obtain ⟨i', hi', he⟩ := hcl j hj
      exact hmemA _ ⟨i', hi', by rw [he, codeE_mulE, hcA i hi, hcA j hj]⟩
  · intro b hb
    obtain ⟨k, hk, rfl⟩ := mem_decL.1 hb
    obtain ⟨h1, h2, h3⟩ := dBPt_spec (hBp k hk)
    refine ⟨fun h5 => ?_, fun a ha => ?_, fun hs a ha => ?_⟩
    · obtain ⟨i, hi, he⟩ := h1 (by rw [← hcB k hk, powK_codeE, h5, codeE_oneE])
      exact hmemA _ ⟨i, hi, by rw [he, hcB k hk]⟩
    · obtain ⟨j, hj, rfl⟩ := mem_decL.1 ha
      obtain ⟨i, hi, he⟩ := h2 j hj
      exact hmemA _ ⟨i, hi, by rw [he, ← cjK_codeE, codeE_invE, hcB k hk, hcA j hj]⟩
    · obtain ⟨j, hj, rfl⟩ := mem_decL.1 ha
      have hs' : fS (mulK v0 (f20 B k)) = 0 := by
        rw [← cv, ← hcB k hk, ← codeE_mulE, fS_codeE, hs]
        rfl
      have := h3 hs' j hj
      apply codeE_injective
      rw [← cjK_codeE, codeE_invE, codeE_invE, codeE_mulE, cv, hcB k hk, hcA j hj, this]

theorem noInv_sound {B Mc : Nat} (h : noInvK B Mc = true) (hB : ∀ k < Mc, validK (f20 B k) = true) :
    ∀ b ∈ decL (f20 B) Mc, mulE b b = oneE → b = oneE ∨ b = zE := by
  intro b hb hbb
  obtain ⟨k, hk, rfl⟩ := mem_decL.1 hb
  have hc := codeE_decE (validK_lt (hB k hk))
  have := (allN_iff _ _).1 h k hk
  unfold nvPt at this
  rw [letB_eq] at this
  have h2 := (ifB_true this).1 (by rw [← hc, ← codeE_mulE, hbb, codeE_oneE, Nat.beq_refl])
  rw [orB_eq, Bool.or_eq_true, beq_iff_eq', beq_iff_eq'] at h2
  rcases h2 with h2 | h2
  · exact Or.inl (codeE_eq_oneK.1 (hc.trans h2))
  · exact Or.inr (codeE_injective (hc.trans (h2.trans codeE_zE.symm)))

end CFSG.KC.FiveStdK

end
