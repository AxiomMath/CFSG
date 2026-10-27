module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrCheck
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS8WrModel

public section

namespace CFSG.EvenSporadicStandard.Fin76b.TS8Wr

open CFSG.QuasithinUnique.A6Facts Equiv Subgroup

@[expose] noncomputable def e0 (i : Nat) : Equiv.Perm (Fin 10) :=
  if h : c0 i ∈ Core.p0Lit then Classical.choose (exists_P0_of_code h) else 1

theorem e0_spec {i : Nat} (h : c0 i ∈ Core.p0Lit) : e0 i ∈ P0 ∧ code (e0 i) = c0 i := by
  have hi : e0 i = Classical.choose (exists_P0_of_code h) := dif_pos h
  rw [hi]
  exact Classical.choose_spec (exists_P0_of_code h)

theorem c0_eq {i : Nat} (hi : i < 32) : c0 i = Core.p0Lit[i]'(by rw [Core.p0_length]; exact hi) := by
  unfold c0
  rw [List.getD_eq_getElem]

theorem mem_c0 {i : Nat} (hi : i < 32) : c0 i ∈ Core.p0Lit := by
  rw [c0_eq hi]
  exact List.getElem_mem _

theorem c0_inj {a b : Nat} (ha : a < 32) (hb : b < 32) (h : c0 a = c0 b) : a = b := by
  rw [c0_eq ha, c0_eq hb] at h
  exact (List.Nodup.getElem_inj_iff Core.p0_nodup).1 h

theorem e0_mem {i : Nat} (hi : i < 32) : e0 i ∈ P0 := (e0_spec (mem_c0 hi)).1

theorem code_e0 {i : Nat} (hi : i < 32) : code (e0 i) = c0 i := (e0_spec (mem_c0 hi)).2

theorem e0_inj {a b : Nat} (ha : a < 32) (hb : b < 32) (h : e0 a = e0 b) : a = b := by
  apply c0_inj ha hb
  rw [← code_e0 ha, ← code_e0 hb, h]

theorem e0_surj {x : Equiv.Perm (Fin 10)} (hx : x ∈ P0) : ∃ a < 32, e0 a = x := by
  have hc : code x ∈ Core.p0Lit := (mem_P0_iff x).1 hx
  obtain ⟨a, ha, hax⟩ := List.mem_iff_getElem.1 hc
  have ha32 : a < 32 := by rw [← Core.p0_length]; exact ha
  refine ⟨a, ha32, code_injective ?_⟩
  rw [code_e0 ha32, c0_eq ha32]
  exact hax

theorem p0Ok_spec (h : p0Ok () = true) :
    (∀ a < 32, ∀ b < 32, Core.cmul (c0 a) (c0 b) ∈ Core.p0Lit) ∧ Core.cid ∈ Core.p0Lit ∧
      c0 i0 = Core.cid := by
  simp only [p0Ok, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, List.mem_range,
    List.contains_iff_mem] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨fun a ha b hb => h1 a ha b hb, h2, h3⟩

theorem i0_lt (h2 : Core.cid ∈ Core.p0Lit) : i0 < 32 := by
  unfold i0
  rw [← Core.p0_length]
  exact List.idxOf_lt_length_iff.2 h2

theorem t0_lt {a b : Nat} (hab : Core.cmul (c0 a) (c0 b) ∈ Core.p0Lit) : t0 a b < 32 := by
  unfold t0
  rw [← Core.p0_length]
  exact List.idxOf_lt_length_iff.2 hab

theorem c0_t0 {a b : Nat} (hab : Core.cmul (c0 a) (c0 b) ∈ Core.p0Lit) :
    c0 (t0 a b) = Core.cmul (c0 a) (c0 b) := by
  rw [c0_eq (t0_lt hab)]
  unfold t0
  exact List.getElem_idxOf _

theorem mtab_get {a b : Nat} (ha : a < 32) (hb : b < 32) :
    (mtab ()).getD (a * 32 + b) 0 = t0 a b := by
  have hk : a * 32 + b < 1024 := by omega
  have e1 : (a * 32 + b) / 32 = a := by omega
  have e2 : (a * 32 + b) % 32 = b := by omega
  unfold mtab
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_ofFn, dif_pos hk]
  simp only [Option.getD_some, Fin.val_mk, e1, e2]

@[expose] def Valid (x : Nat × Nat × Bool) : Prop := x.1 < 32 ∧ x.2.1 < 32

theorem mulI_false (M : Array Nat) (a b c d : Nat) (e : Bool) :
    mulI M (a, b, false) (c, d, e) = (M.getD (a * 32 + c) 0, M.getD (b * 32 + d) 0, e) := rfl

theorem mulI_true (M : Array Nat) (a b c d : Nat) (e : Bool) :
    mulI M (a, b, true) (c, d, e) = (M.getD (a * 32 + d) 0, M.getD (b * 32 + c) 0, !e) := rfl

theorem e0_mul (hcl : ∀ a < 32, ∀ b < 32, Core.cmul (c0 a) (c0 b) ∈ Core.p0Lit)
    {a b : Nat} (ha : a < 32) (hb : b < 32) : e0 (t0 a b) = e0 a * e0 b := by
  apply code_injective
  rw [code_e0 (t0_lt (hcl a ha b hb)), code_mul, code_e0 ha, code_e0 hb,
    c0_t0 (hcl a ha b hb)]

@[expose] noncomputable def rep (x : Nat × Nat × Bool) : Pt :=
  Equiv.Perm.sumCongr (e0 x.1) (e0 x.2.1) * (if x.2.2 then sw else 1)

theorem rep_mk (a b : Nat) (e : Bool) :
    rep (a, b, e) = Equiv.Perm.sumCongr (e0 a) (e0 b) * (if e then sw else 1) := rfl

theorem rep_one (hcid : Core.cid ∈ Core.p0Lit) (hci : c0 i0 = Core.cid) : rep oneI = 1 := by
  have h0 : e0 i0 = 1 := by
    apply code_injective
    rw [code_e0 (i0_lt hcid), hci, code_one]
  simp [rep, oneI, h0, sumCongr_one_one]

theorem rep_mulI (hcl : ∀ a < 32, ∀ b < 32, Core.cmul (c0 a) (c0 b) ∈ Core.p0Lit)
    {x y : Nat × Nat × Bool} (hx : Valid x) (hy : Valid y) :
    rep (mulI (mtab ()) x y) = rep x * rep y := by
  obtain ⟨a, b, e⟩ := x
  obtain ⟨c, d, f⟩ := y
  obtain ⟨ha, hb⟩ := hx
  obtain ⟨hc, hd⟩ := hy
  cases e <;> cases f
  · rw [mulI_false, mtab_get ha hc, mtab_get hb hd, rep_mk, rep_mk, rep_mk,
      e0_mul hcl ha hc, e0_mul hcl hb hd]
    simp only [if_false, Bool.false_eq_true, mul_one, ← mul_assoc, Equiv.Perm.sumCongr_mul]
  · rw [mulI_false, mtab_get ha hc, mtab_get hb hd, rep_mk, rep_mk, rep_mk,
      e0_mul hcl ha hc, e0_mul hcl hb hd]
    simp only [if_false, if_true, Bool.false_eq_true, mul_one, ← mul_assoc, Equiv.Perm.sumCongr_mul]
  · rw [mulI_true, mtab_get ha hd, mtab_get hb hc, rep_mk, rep_mk, rep_mk,
      e0_mul hcl ha hd, e0_mul hcl hb hc]
    simp only [if_false, if_true, Bool.false_eq_true, mul_one, Bool.not_true, Bool.not_false]
    rw [sumCongr_sw_sumCongr]
  · rw [mulI_true, mtab_get ha hd, mtab_get hb hc, rep_mk, rep_mk, rep_mk,
      e0_mul hcl ha hd, e0_mul hcl hb hc]
    simp only [if_true, Bool.false_eq_true, Bool.not_true, if_false, mul_one]
    rw [← mul_assoc, sumCongr_sw_sumCongr, mul_assoc, sw_mul_sw, mul_one]

theorem rep_inj {x y : Nat × Nat × Bool} (hx : Valid x) (hy : Valid y) (h : rep x = rep y) :
    x = y := by
  obtain ⟨a, b, e⟩ := x
  obtain ⟨c, d, f⟩ := y
  obtain ⟨ha, hb⟩ := hx
  obtain ⟨hc, hd⟩ := hy
  cases e <;> cases f
  · rw [rep_mk, rep_mk] at h
    simp only [if_false, Bool.false_eq_true, mul_one] at h
    obtain ⟨h1, h2⟩ := sumCongr_inj h
    obtain rfl := e0_inj ha hc h1
    obtain rfl := e0_inj hb hd h2
    rfl
  · exfalso
    rw [rep_mk, rep_mk] at h
    simp only [if_false, if_true, Bool.false_eq_true, mul_one] at h
    have := congrArg (fun g : Pt => g (Sum.inl 0)) h
    simp [sw] at this
  · exfalso
    rw [rep_mk, rep_mk] at h
    simp only [if_false, if_true, Bool.false_eq_true, mul_one] at h
    have := congrArg (fun g : Pt => g (Sum.inl 0)) h
    simp [sw] at this
  · rw [rep_mk, rep_mk] at h
    simp only [if_true] at h
    obtain ⟨h1, h2⟩ := sumCongr_inj (mul_right_cancel h)
    obtain rfl := e0_inj ha hc h1
    obtain rfl := e0_inj hb hd h2
    rfl

theorem rep_surj {g : Pt} (hg : g ∈ Sig) : ∃ x, Valid x ∧ rep x = g := by
  have hg' : ∃ a ∈ P0, ∃ b ∈ P0, g = Equiv.Perm.sumCongr a b ∨
      g = Equiv.Perm.sumCongr a b * sw := hg
  obtain ⟨a, ha, b, hb, h | h⟩ := hg'
  · obtain ⟨i, hi, rfl⟩ := e0_surj ha
    obtain ⟨j, hj, rfl⟩ := e0_surj hb
    exact ⟨(i, j, false), ⟨hi, hj⟩, by rw [rep_mk]; simp [h]⟩
  · obtain ⟨i, hi, rfl⟩ := e0_surj ha
    obtain ⟨j, hj, rfl⟩ := e0_surj hb
    exact ⟨(i, j, true), ⟨hi, hj⟩, by rw [rep_mk]; simp [h]⟩

end CFSG.EvenSporadicStandard.Fin76b.TS8Wr
