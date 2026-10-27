
module


public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5SWIsoModel
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsRealB

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso

open CFSG Subgroup CFSG.PSL3Four CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34 CFSG.CosetTable
open CFSG.ComponentClassification.GrSLit.L34Facts CFSG.ComponentClassification.GrSLit

variable {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)} {l : Cover →* E}

theorem exists_kb
    (l : Cover →* E) : ∃ kb ∈ kbList, ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true := by
  let K : AddSubgroup (ZMod 4 × ZMod 4) :=
    { carrier := {p | zz l p.1 p.2 = 1}
      zero_mem' := zz_zero
      add_mem' := fun {a b} ha hb => by
        change zz l (a.1 + b.1) (a.2 + b.2) = 1
        rw [← zz_mul, ha, hb, one_mul]
      neg_mem' := fun {a} ha => by
        change zz l (-a.1) (-a.2) = 1
        rw [← zz_inv, ha, inv_one] }
  obtain ⟨kb, hkb, h⟩ := wIsoTypeParts.kClass K
  exact ⟨kb, hkb, fun i j => (h i j).symm⟩

section Setting

variable
  {kb : List Bool}

theorem eqKB_iff (h : IsQSetting q l) (hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true)
    {x y : MElt} (hx : x.1 < 64) (hy : y.1 < 64) : eqKB kb x y = true ↔ nfM l x = nfM l y := by
  rw [nfM, nfM, nf_eq_iff h hx hy, hkb, eqKB, Bool.and_eq_true, beq_iff_eq]

theorem isInvKB_iff (h : IsQSetting q l)
    (hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true) {x : MElt} (hx : x.1 < 64) :
    isInvKB kb x = true ↔ nfM l x * nfM l x = 1 ∧ nfM l x ≠ 1 := by
  have e1 := eqKB_iff h hkb (mulM_lt hx hx) (show oneM.1 < 64 by decide)
  have e2 := eqKB_iff h hkb hx (show oneM.1 < 64 by decide)
  rw [nfM_one, ← nfM_mul h hx hx] at e1
  rw [nfM_one] at e2
  rw [isInvKB, Bool.and_eq_true, Bool.not_eq_true', ← Bool.not_eq_true, e1, e2]

theorem commKB_iff (h : IsQSetting q l)
    (hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true) {x y : MElt} (hx : x.1 < 64)
    (hy : y.1 < 64) :
    eqKB kb (mulM x y) (mulM y x) = true ↔ nfM l x * nfM l y = nfM l y * nfM l x := by
  rw [eqKB_iff h hkb (mulM_lt hx hy) (mulM_lt hy hx), ← nfM_mul h hx hy, ← nfM_mul h hy hx]

theorem liftsKB_of
    (h : IsQSetting q l) (hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true)
    {β : E ≃* E} {i : ℕ} (hi : i < 36)
    (hβ : ∀ w, β (l (cv w)) = l (cv (substWord (aut i) w))) : liftsKB kb i = true := by
  unfold liftsKB
  simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true']
  intro a _ b _
  by_cases hab : inKB kb a b = true
  · right
    rw [← hkb, ← beta_zz h hi hβ, (hkb a b).2 hab, map_one]
  · left
    simpa using hab

theorem mem_ker_iff_zz (h : IsQSetting q l) {e : E} :
    e ∈ q.ker ↔ ∃ i j : ZMod 4, e = zz l i j := by
  rw [mem_ker_iff h.ql h.lsurj h.three]
  constructor
  · rintro ⟨i, j, rfl⟩
    exact ⟨i, j, (zz_ofNat i j).symm⟩
  · rintro ⟨i, j, rfl⟩
    refine ⟨i.val, j.val, ?_⟩
    rw [← zz_ofNat, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]

theorem card_ker_of_kbZero (h : IsQSetting q l)
    (hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true) (hz : kbZero kb = true) :
    Nat.card q.ker = 16 := by
  obtain rfl := eq_of_kbZero hz
  let f : ZMod 4 × ZMod 4 → q.ker := fun p => ⟨zz l p.1 p.2, zz_mem_ker h _ _⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, b⟩ ⟨c, d⟩ hfe
    have h1 : zz l a b = zz l c d := congrArg Subtype.val hfe
    have h2 : zz l (a - c) (b - d) = 1 := by
      rw [sub_eq_add_neg, sub_eq_add_neg, ← zz_mul, h1, ← zz_inv, mul_inv_cancel]
    obtain ⟨h3, h4⟩ := inKB_zero_iff.mp ((hkb _ _).1 h2)
    rw [sub_eq_zero] at h3 h4
    rw [h3, h4]
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨i, j, rfl⟩ := (mem_ker_iff_zz h).1 he
    exact ⟨(i, j), rfl⟩
  rw [← Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩), Nat.card_prod, Nat.card_zmod]

theorem exists_ker_eq_zpowers (h : IsQSetting q l)
    (hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true) (hc : kbCyc kb = true) :
    ∃ g : E, q.ker = zpowers g ∧ g ^ 4 = 1 := by
  obtain ⟨g₁, g₂, hg⟩ := kbCyc_spec hc
  refine ⟨zz l g₁ g₂, le_antisymm (fun e he => ?_) ?_, ?_⟩
  · obtain ⟨i, j, rfl⟩ := (mem_ker_iff_zz h).1 he
    obtain ⟨m, hm⟩ := hg i j
    have e1 : zz l i j = zz l g₁ g₂ ^ m.val * zz l (i - m * g₁) (j - m * g₂) := by
      rw [zz_pow, zz_mul, ZMod.natCast_zmod_val, add_sub_cancel, add_sub_cancel]
    rw [e1, (hkb _ _).2 hm, mul_one]
    exact pow_mem (mem_zpowers _) _
  · rw [zpowers_le]
    exact zz_mem_ker h _ _
  · rw [zz_pow]
    have h4 : ((4 : ℕ) : ZMod 4) = 0 := rfl
    rw [h4, zero_mul, zero_mul, zz_zero]

theorem ker_eq_bot_of_kbFull (h : IsQSetting q l)
    (hkb : ∀ i j : ZMod 4, zz l i j = 1 ↔ inKB kb i j = true) (hf : kbFull kb = true) :
    q.ker = ⊥ := by
  obtain rfl := eq_of_kbFull hf
  rw [eq_bot_iff]
  intro e he
  obtain ⟨i, j, rfl⟩ := (mem_ker_iff_zz h).1 he
  exact (hkb i j).2 (inKB_full i j)

end Setting

end CFSG.ComponentClassification.GrSLit.L34Facts.Real.WIso
