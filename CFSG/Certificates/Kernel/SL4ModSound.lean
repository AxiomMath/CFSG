module

public import CFSG.LargeExtraspecial.SL4ModHecke
public import CFSG.LargeExtraspecial.SL4ModEmbed
public import Certificates.Data.Kernel.SL4ModCerts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial.SL4Mod

open Module Native CFSG.Sporadic.SmallF2.Native

@[expose] def SpinCertData : Prop :=
  ∀ j < 3, ∃ d : CosetData, checkTau j d = true ∧ ∀ i < 3, ∃ od : OrbData,
    checkOrb d i od = true ∧ ∀ c < 128, c ≠ 0 → ∃ cert, valid d.tau (expand od c) cert = true

theorem getElem!_eq_toList_getD {α : Type} [Inhabited α] (a : Array α) (i : ℕ) :
    a[i]! = a.toList.getD i default := by
  rw [List.getD_eq_getElem?_getD, Array.getElem?_toList, getElem!_def]
  cases a[i]? <;> rfl

theorem tabL_getD (taus : Array (Array ℕ)) (s : ℕ) : (tabL taus).getD s [] = taus[s]!.toList := by
  rw [tabL, getElem!_eq_toList_getD]
  exact List.getD_map _ _ _

theorem bitsGo_eq (g : ℕ → Bool) : ∀ (t : List ℕ) (k acc : ℕ), bitsGo g t k acc =
    (List.range t.length).foldl
      (fun acc j => if g (t.getD j 0) then acc ||| (1 <<< (j + k)) else acc) acc
  | [], _, _ => rfl
  | a :: t, k, acc => by
    rw [bitsGo, bitsGo_eq g t (k + 1), List.length_cons, List.range_succ_eq_map, List.foldl_cons,
      List.foldl_map, List.getD_cons_zero, Nat.zero_add]
    congr 1
    funext acc j
    rw [List.getD_cons_succ]
    have e : j + 1 + k = j + (k + 1) := by omega
    rw [e]

theorem bitsL_eq (g : ℕ → Bool) (t : List ℕ) :
    bitsL g t = ofBits 105 fun k => g (t.getD k 0) := by
  rw [bitsL]
  split_ifs with h
  · rw [bitsGo_eq, ofBits, h]
    simp only [Nat.add_zero]
  · rfl

theorem xorGo_eq : ∀ (m : ℕ) (L : List ℕ) (acc : ℕ), xorGo m L acc =
    (List.range L.length).foldl
      (fun acc t => if m.testBit t then acc ^^^ L.getD t 0 else acc) acc
  | _, [], _ => rfl
  | m, a :: L, acc => by
    rw [xorGo, xorGo_eq (m / 2) L, List.length_cons, List.range_succ_eq_map, List.foldl_cons,
      List.foldl_map, List.getD_cons_zero]
    congr 1
    funext acc t
    rw [List.getD_cons_succ, Nat.testBit_div_two]

theorem actV_eq (t : Array ℕ) (x : ℕ) : actV t x = actVL t.toList x := by
  rw [actVL, bitsL_eq, actV]
  simp only [getElem!_eq_toList_getD]
  rfl

theorem expand_eq (od : OrbData) (c : ℕ) : expand od c = expandL od.lab.toList c := by
  rw [expandL, bitsL_eq, expand]
  simp only [getElem!_eq_toList_getD]
  rfl

theorem xorSel_eq (mask : ℕ) (L : Array ℕ) : xorSel mask L = xorSelL mask L.toList := by
  rw [xorSelL, xorGo_eq, xorSel, Array.length_toList]
  simp only [getElem!_eq_toList_getD]
  rfl

theorem inSpan_eq (x : ℕ) (B : Array ℕ) : inSpan x B = inSpanL x B.toList := by
  simp only [inSpan, inSpanL, xorSel_eq, Array.length_toList]

theorem indep9_eq (L : Array ℕ) : indep9 L = indep9L L.toList := by
  simp only [indep9, indep9L, xorSel_eq]

theorem derivOK_eq (taus : Array (Array ℕ)) (m : ℕ) (L : Array ℕ) (src : Array (ℕ × ℕ)) :
    derivOK taus m L src = derivOKL (tabL taus) m L.toList src.toList := by
  simp only [derivOK, derivOKL, actV_eq, tabL_getD, Array.length_toList]
  simp only [getElem!_eq_toList_getD]
  rfl

theorem closedOK_eq (taus : Array (Array ℕ)) (B : Array ℕ) :
    closedOK taus B = closedOKL (tabL taus) B.toList := by
  simp only [closedOK, closedOKL, actV_eq, inSpan_eq, tabL_getD, Array.length_toList]
  simp only [getElem!_eq_toList_getD]
  rfl

theorem validL_eq (taus : Array (Array ℕ)) (m : ℕ) (c : SpinCert) :
    validL (tabL taus) m c = valid taus m c := by
  simp only [valid, validL, derivOK_eq, indep9_eq, xorSel_eq, inSpan_eq, closedOK_eq,
    Array.length_toList]

theorem valid_of_checkSpinFrom {taus : Array (Array ℕ)} {od : OrbData} :
    ∀ (cs : List SpinCert) (n : ℕ), checkSpinFrom (tabL taus) od n cs = true →
      ∀ k < cs.length, valid taus (expand od (n + k)) (cs.getD k default) = true
  | [], _, _, k, hk => absurd hk (Nat.not_lt_zero k)
  | c :: cs, n, h, k, hk => by
    rw [checkSpinFrom, Bool.and_eq_true, validL_eq, ← expand_eq] at h
    cases k with
    | zero => simpa using h.1
    | succ k =>
      have := valid_of_checkSpinFrom cs (n + 1) h.2 k (by simpa using hk)
      have e : n + (k + 1) = n + 1 + k := by omega
      rw [e]
      simpa using this

theorem checkSpinFrom_append (tl : List (List ℕ)) (od : OrbData) :
    ∀ (l₁ l₂ : List SpinCert) (n : ℕ), checkSpinFrom tl od n (l₁ ++ l₂) =
      (checkSpinFrom tl od n l₁ && checkSpinFrom tl od (n + l₁.length) l₂)
  | [], l₂, n => by rw [List.nil_append, checkSpinFrom, List.length_nil, Nat.add_zero,
      Bool.true_and]
  | c :: l₁, l₂, n => by
    rw [List.cons_append, checkSpinFrom, checkSpinFrom, checkSpinFrom_append tl od l₁ l₂ (n + 1),
      Bool.and_assoc, List.length_cons]
    have e : n + 1 + l₁.length = n + (l₁.length + 1) := by omega
    rw [e]

theorem checkSpinFrom_split {tl : List (List ℕ)} {od : OrbData} {n : ℕ} (m : ℕ)
    {cs : List SpinCert} (hm : m ≤ cs.length) (h₁ : checkSpinFrom tl od n (cs.take m) = true)
    (h₂ : checkSpinFrom tl od (n + m) (cs.drop m) = true) : checkSpinFrom tl od n cs = true := by
  rw [← List.take_append_drop m cs, checkSpinFrom_append, List.length_take, Nat.min_eq_left hm,
    h₁, h₂, Bool.and_self]

theorem exists_valid_of_checkSpinL {d : CosetData} {od : OrbData} {cs : List SpinCert}
    (h : checkSpinL d od cs = true) {c : ℕ} (hc : c < 128) (hc0 : c ≠ 0) :
    ∃ cert, valid d.tau (expand od c) cert = true := by
  rw [checkSpinL, Bool.and_eq_true, beq_iff_eq] at h
  have := valid_of_checkSpinFrom cs 1 h.2 (c - 1) (by omega)
  have e : 1 + (c - 1) = c := by omega
  rw [e] at this
  exact ⟨_, this⟩

theorem spinCertData_of
    (h : ∀ j < 3, ∃ d : CosetData, checkTau j d = true ∧ ∀ i < 3, ∃ od : OrbData,
      checkOrb d i od = true ∧ ∃ cs, checkSpinL d od cs = true) : SpinCertData := by
  intro j hj
  obtain ⟨d, hT, hd⟩ := h j hj
  refine ⟨d, hT, fun i hi => ?_⟩
  obtain ⟨od, hO, cs, hS⟩ := hd i hi
  exact ⟨od, hO, fun c hc hc0 => exists_valid_of_checkSpinL hS hc hc0⟩

variable {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def dualRep (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) :
    SL4 →* (Module.Dual (ZMod 2) V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V) where
  toFun g := (ρ g⁻¹).dualMap
  map_one' := by
    ext f w
    change f (ρ 1⁻¹ w) = f w
    rw [inv_one, map_one]
    rfl
  map_mul' g h := by
    ext f w
    change f (ρ (g * h)⁻¹ w) = f (ρ h⁻¹ (ρ g⁻¹ w))
    rw [mul_inv_rev, act_mul]

theorem dualRep_apply (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) (g : SL4) (f : Module.Dual (ZMod 2) V)
    (w : V) : dualRep ρ g f w = f (ρ g⁻¹ w) := rfl

theorem not_isIrredGen_of (hD : SpinCertData) [FiniteDimensional (ZMod 2) V]
    (hV : finrank (ZMod 2) V = 8) (ρ : SL4 →* (V ≃ₗ[ZMod 2] V)) : ¬ IsIrredGen ρ := by
  intro hirr
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (by rw [hV]; norm_num)
  have hVd : finrank (ZMod 2) (Module.Dual (ZMod 2) V) = 8 := by
    rw [Subspace.dual_finrank_eq, hV]
  have : Nontrivial (Module.Dual (ZMod 2) V) :=
    Module.nontrivial_of_finrank_pos (by rw [hVd]; norm_num)
  obtain ⟨i, v, hv0, hvn, hvU⟩ := exists_fixed_parabolic ρ (by rw [hV]; norm_num)
  obtain ⟨j, f, hf0, hfn, hfU⟩ := exists_fixed_parabolic (dualRep ρ) (by rw [hVd]; norm_num)
  have hf : IsFixPj ρ j.val f := by
    refine ⟨fun u hu w => ?_, fun w => ?_⟩
    · have : dualRep ρ u⁻¹ f w = f w :=
        congrArg (fun φ : Module.Dual (ZMod 2) V => φ w) (hfU u⁻¹ (U.inv_mem hu))
      rwa [dualRep_apply, inv_inv] at this
    · have : dualRep ρ (nn j) f w = f w := congrArg (fun φ : Module.Dual (ZMod 2) V => φ w) hfn
      rwa [dualRep_apply, nn_inv] at this
  obtain ⟨d, hT, hd⟩ := hD j.val j.isLt
  obtain ⟨od, hO, hS⟩ := hd i.val i.isLt
  have hinj := iota_injective hirr hT hf hf0
  have hX := isTauInv_range_iota hT hf
  have hdim : finrank (ZMod 2) (LinearMap.range (iota ρ d f)) = 8 := by
    rw [LinearMap.finrank_range_of_inj hinj, hV]
  have hF : ∀ s ∈ orbGens i.val, iota ρ d f v ∘ tauF d.tau[s]! = iota ρ d f v := by
    intro s hs
    have hs6 : s < 6 := by
      simp only [orbGens, List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl <;> omega
    rw [← iota_gen ρ hT hf hs6]
    congr 1
    simp only [orbGens, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact hvU _ (xx_mem 0)
    · exact hvU _ (xx_mem 1)
    · exact hvU _ (xx_mem 2)
    · exact hvn
  have hF0 : iota ρ d f v ≠ 0 := by
    intro h0
    exact hv0 (hinj (h0.trans (map_zero _).symm))
  obtain ⟨c, hc, hFc, hc0⟩ := eq_vec_expand hO hF
  obtain ⟨cert, hcert⟩ := hS c hc (hc0 hF0)
  have hm : vec (expand od c) ∈ LinearMap.range (iota ρ d f) := hFc ▸ ⟨v, rfl⟩
  exact false_of_valid hX hdim (range_iota_le hirr hT hf) hm hcert

end CFSG.LargeExtraspecial.SL4Mod
