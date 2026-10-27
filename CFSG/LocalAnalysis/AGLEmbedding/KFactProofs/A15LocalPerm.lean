module

public import CFSG.Open.LocalVocabulary

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.AGLEmbedding.A15Local

open Equiv CFSG.Open

abbrev Pt : Type := ZMod 3 × ZMod 5

@[expose] def shiftPerm (f : ZMod 3 → ZMod 5) : Perm Pt where
  toFun p := (p.1, p.2 + f p.1)
  invFun p := (p.1, p.2 - f p.1)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem shiftPerm_apply (f : ZMod 3 → ZMod 5) (p : Pt) :
    shiftPerm f p = (p.1, p.2 + f p.1) := rfl

@[simp] theorem shiftPerm_symm_apply (f : ZMod 3 → ZMod 5) (p : Pt) :
    (shiftPerm f).symm p = (p.1, p.2 - f p.1) := rfl

theorem shiftPerm_add (f g : ZMod 3 → ZMod 5) :
    shiftPerm (f + g) = shiftPerm f * shiftPerm g := by
  ext p <;> simp [add_comm, add_left_comm]

theorem shiftPerm_zero : shiftPerm 0 = 1 := by
  ext p <;> simp

theorem shiftPerm_injective : Function.Injective shiftPerm := by
  intro f g h
  funext i
  have := congrArg (fun σ : Perm Pt => (σ (i, 0)).2) h
  simpa using this

theorem shiftPerm_pow (f : ZMod 3 → ZMod 5) (n : ℕ) : shiftPerm f ^ n = shiftPerm (n • f) := by
  induction n with
  | zero => simp [shiftPerm_zero]
  | succ n ih => rw [pow_succ, ih, ← shiftPerm_add, succ_nsmul]

@[expose] def shiftHom : Multiplicative (ZMod 3 → ZMod 5) →* Perm Pt where
  toFun f := shiftPerm (Multiplicative.toAdd f)
  map_one' := shiftPerm_zero
  map_mul' _ _ := shiftPerm_add _ _

@[expose] def sylowT : Subgroup (Perm Pt) := shiftHom.range

theorem mem_sylowT_iff {g : Perm Pt} : g ∈ sylowT ↔ ∃ f, g = shiftPerm f := by
  constructor
  · rintro ⟨f, rfl⟩
    exact ⟨Multiplicative.toAdd f, rfl⟩
  · rintro ⟨f, rfl⟩
    exact ⟨Multiplicative.ofAdd f, rfl⟩

theorem shiftPerm_mem_sylowT (f : ZMod 3 → ZMod 5) : shiftPerm f ∈ sylowT :=
  mem_sylowT_iff.2 ⟨f, rfl⟩

theorem card_sylowT : Nat.card sylowT = 5 ^ 3 := by
  have hinj : Function.Injective shiftHom := fun f g h => by
    exact Multiplicative.toAdd.injective (shiftPerm_injective h)
  rw [sylowT, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
  simp [Nat.card_eq_fintype_card]

theorem isElemAbelian_sylowT : IsElemAbelian 5 sylowT := by
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨f, hf⟩ := mem_sylowT_iff.1 a.2
    obtain ⟨g, hg⟩ := mem_sylowT_iff.1 b.2
    apply Subtype.ext
    change (a : Perm Pt) * b = b * a
    rw [hf, hg, ← shiftPerm_add, ← shiftPerm_add, add_comm]
  · obtain ⟨f, rfl⟩ := mem_sylowT_iff.1 hx
    rw [shiftPerm_pow, ← shiftPerm_zero]
    congr 1
    funext i
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((5 : ℕ) : ZMod 5) = 0 from ZMod.natCast_self 5, zero_mul]

theorem isPGroup_sylowT : IsPGroup 5 sylowT := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact IsPGroup.of_card (n := 3) card_sylowT

@[expose] def blockShift : Perm Pt where
  toFun p := (p.1 + 1, p.2)
  invFun p := (p.1 - 1, p.2)
  left_inv p := by simp
  right_inv p := by simp

@[simp] theorem blockShift_apply (p : Pt) : blockShift p = (p.1 + 1, p.2) := rfl

@[simp] theorem blockShift_symm_apply (p : Pt) : blockShift.symm p = (p.1 - 1, p.2) := rfl

theorem blockShift_conj_shiftPerm (f : ZMod 3 → ZMod 5) :
    blockShift * shiftPerm f * blockShift⁻¹ = shiftPerm (fun i => f (i - 1)) := by
  ext p <;> simp [Perm.inv_def]

theorem blockShift_pow_three : blockShift ^ 3 = 1 := by
  decide +kernel

theorem blockShift_mem_alternatingGroup : blockShift ∈ alternatingGroup Pt := by
  have : Perm.sign blockShift ^ 3 = 1 := by rw [← map_pow, blockShift_pow_three, map_one]
  rcases Int.units_eq_one_or (Perm.sign blockShift) with h | h
  · exact Perm.mem_alternatingGroup.2 h
  · rw [h] at this
    exact absurd this (by decide)

@[expose] def FibConst (g : Perm Pt) : Prop := ∀ p q : Pt, p.1 = q.1 → (g p).1 = (g q).1

@[expose] def wr : Subgroup (Perm Pt) where
  carrier := {g | FibConst g ∧ FibConst g⁻¹}
  one_mem' := ⟨fun _ _ h => h, fun _ _ h => h⟩
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨fun p q hpq => hg _ _ (hh p q hpq), fun p q hpq => ?_⟩
    rw [mul_inv_rev]
    exact hh' _ _ (hg' p q hpq)
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨hg', by rwa [inv_inv]⟩

@[expose] def blk (g : Perm Pt) (i : ZMod 3) : ZMod 3 := (g (i, 0)).1

theorem fst_apply_eq_blk {g : Perm Pt} (hg : g ∈ wr) (p : Pt) : (g p).1 = blk g p.1 :=
  hg.1 p (p.1, 0) rfl

theorem blockShift_mem_wr : blockShift ∈ wr :=
  ⟨fun p q h => by simpa using h, fun p q h => by simpa [Perm.inv_def] using h⟩

@[expose] def blockAlt (i : ZMod 3) : Subgroup (Perm Pt) :=
  (alternatingGroup {p : Pt // p.1 = i}).map Perm.ofSubtype

theorem fst_apply_iff_of_fix {i : ZMod 3} {g : Perm Pt} (hfix : ∀ p : Pt, p.1 ≠ i → g p = p)
    (x : Pt) : (g x).1 = i ↔ x.1 = i := by
  constructor
  · intro h
    by_contra hx
    have := hfix x hx
    rw [this] at h
    exact hx h
  · intro h
    by_contra hgx
    have h1 := hfix (g x) hgx
    have h2 : g x = x := g.injective h1
    rw [h2] at hgx
    exact hgx h

theorem mem_blockAlt_iff {i : ZMod 3} {g : Perm Pt} :
    g ∈ blockAlt i ↔ (∀ p : Pt, p.1 ≠ i → g p = p) ∧ g ∈ alternatingGroup Pt := by
  constructor
  · rintro ⟨σ, hσ, rfl⟩
    have hσ' : Perm.sign σ = 1 := Perm.mem_alternatingGroup.1 hσ
    refine ⟨fun p hp => Perm.ofSubtype_apply_of_not_mem σ hp, ?_⟩
    rw [Perm.mem_alternatingGroup, Perm.sign_ofSubtype]
    exact hσ'
  · rintro ⟨hfix, hev⟩
    have h1 := fst_apply_iff_of_fix hfix
    have h2 : ∀ x, g x ≠ x → x.1 = i := fun x hx => by_contra fun h => hx (hfix x h)
    refine ⟨g.subtypePerm h1, ?_, Perm.ofSubtype_subtypePerm h1 h2⟩
    exact Perm.mem_alternatingGroup.2
      ((Perm.sign_subtypePerm g h1 h2).trans (Perm.mem_alternatingGroup.1 hev))

theorem blockAlt_le_alternatingGroup (i : ZMod 3) : blockAlt i ≤ alternatingGroup Pt :=
  fun _ hg => (mem_blockAlt_iff.1 hg).2

theorem blockAlt_commute {i j : ZMod 3} (hij : i ≠ j) {g h : Perm Pt} (hg : g ∈ blockAlt i)
    (hh : h ∈ blockAlt j) : g * h = h * g := by
  have hgf := (mem_blockAlt_iff.1 hg).1
  have hhf := (mem_blockAlt_iff.1 hh).1
  have hg1 := fst_apply_iff_of_fix hgf
  have hh1 := fst_apply_iff_of_fix hhf
  refine Equiv.ext fun p => ?_
  simp only [Perm.mul_apply]
  by_cases hpi : p.1 = i
  · have hpj : p.1 ≠ j := fun h' => hij (hpi.symm.trans h')
    have hgp : (g p).1 = i := (hg1 p).2 hpi
    have hgpj : (g p).1 ≠ j := fun h' => hij (hgp.symm.trans h')
    rw [hhf p hpj, hhf (g p) hgpj]
  · by_cases hpj : p.1 = j
    · have hhp : (h p).1 = j := (hh1 p).2 hpj
      have hhpi : (h p).1 ≠ i := fun h' => hij (h'.symm.trans hhp)
      rw [hgf p hpi, hgf (h p) hhpi]
    · simp only [hgf p hpi, hhf p hpj]

theorem conj_mem_blockAlt {w : Perm Pt} (hw : w ∈ wr) {i : ZMod 3} {h : Perm Pt}
    (hh : h ∈ blockAlt i) : w * h * w⁻¹ ∈ blockAlt (blk w i) := by
  rw [mem_blockAlt_iff]
  obtain ⟨hfix, hev⟩ := mem_blockAlt_iff.1 hh
  refine ⟨fun p hp => ?_, ?_⟩
  · have hq : (w⁻¹ p).1 ≠ i := by
      intro h'
      apply hp
      have h0 : w (w⁻¹ p) = p := by simp
      have := fst_apply_eq_blk hw (w⁻¹ p)
      rw [h0, h'] at this
      exact this
    show w (h (w⁻¹ p)) = p
    rw [hfix _ hq]
    simp
  · rw [Perm.mem_alternatingGroup] at hev ⊢
    simp [hev]

theorem mem_alternatingGroup_of_pow_eq_one {α : Type*} [Fintype α] [DecidableEq α]
    {g : Perm α} {n : ℕ} (hn : Odd n) (h : g ^ n = 1) : g ∈ alternatingGroup α := by
  rw [Perm.mem_alternatingGroup]
  have h1 : Perm.sign g ^ n = 1 := by rw [← map_pow, h, map_one]
  rcases Int.units_eq_one_or (Perm.sign g) with h2 | h2
  · exact h2
  · rw [h2, hn.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem shiftPerm_single_mem_blockAlt (i : ZMod 3) (c : ZMod 5) :
    shiftPerm (Pi.single i c) ∈ blockAlt i := by
  rw [mem_blockAlt_iff]
  refine ⟨fun p hp => ?_, ?_⟩
  · simp [hp]
  · refine mem_alternatingGroup_of_pow_eq_one (n := 5) (by decide) ?_
    rw [shiftPerm_pow, ← shiftPerm_zero]
    congr 1
    funext j
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [show ((5 : ℕ) : ZMod 5) = 0 from ZMod.natCast_self 5, zero_mul]

theorem sylowT_le_iSup_blockAlt : sylowT ≤ ⨆ i, blockAlt i := by
  intro g hg
  obtain ⟨f, rfl⟩ := mem_sylowT_iff.1 hg
  have hf : f = Pi.single 0 (f 0) + Pi.single 1 (f 1) + Pi.single 2 (f 2) := by
    funext i
    rcases (by decide : ∀ i : ZMod 3, i = 0 ∨ i = 1 ∨ i = 2) i with rfl | rfl | rfl <;>
      simp +decide
  rw [hf, shiftPerm_add, shiftPerm_add]
  exact mul_mem (mul_mem (Subgroup.mem_iSup_of_mem 0 (shiftPerm_single_mem_blockAlt _ _))
    (Subgroup.mem_iSup_of_mem 1 (shiftPerm_single_mem_blockAlt _ _)))
    (Subgroup.mem_iSup_of_mem 2 (shiftPerm_single_mem_blockAlt _ _))

@[expose] def fibEquiv (i : ZMod 3) : {p : Pt // p.1 = i} ≃ Fin 5 where
  toFun p := p.1.2
  invFun z := ⟨(i, z), rfl⟩
  left_inv := fun ⟨⟨a, b⟩, h⟩ => by
    simp only at h
    subst h
    rfl
  right_inv _ := rfl

@[expose] noncomputable def blockAltEquiv (i : ZMod 3) :
    blockAlt i ≃* alternatingGroup (Fin 5) :=
  (Subgroup.equivMapOfInjective (alternatingGroup {p : Pt // p.1 = i}) Perm.ofSubtype
    Perm.ofSubtype_injective).symm.trans (Equiv.altCongrHom (fibEquiv i))

theorem isSimpleGroup_blockAlt (i : ZMod 3) : IsSimpleGroup (blockAlt i) :=
  (blockAltEquiv i).isSimpleGroup

theorem card_blockAlt (i : ZMod 3) : Nat.card (blockAlt i) = 60 := by
  rw [Nat.card_congr (blockAltEquiv i).toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

@[expose] def cyc3 (i : ZMod 3) (a b c : ZMod 5) : Perm Pt :=
  swap (i, a) (i, b) * swap (i, a) (i, c)

theorem isThreeCycle_cyc3 (i : ZMod 3) {a b c : ZMod 5} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : (cyc3 i a b c).IsThreeCycle :=
  Perm.isThreeCycle_swap_mul_swap_same (fun h => hab (congrArg Prod.snd h))
    (fun h => hac (congrArg Prod.snd h)) (fun h => hbc (congrArg Prod.snd h))

theorem cyc3_mem_blockAlt (i : ZMod 3) {a b c : ZMod 5} (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : cyc3 i a b c ∈ blockAlt i := by
  rw [mem_blockAlt_iff]
  refine ⟨fun p hp => ?_, (isThreeCycle_cyc3 i hab hac hbc).mem_alternatingGroup⟩
  have h1 : p ≠ (i, a) := fun h => hp (by rw [h])
  have h2 : p ≠ (i, b) := fun h => hp (by rw [h])
  have h3 : p ≠ (i, c) := fun h => hp (by rw [h])
  simp [cyc3, Perm.mul_apply, swap_apply_of_ne_of_ne h1 h2, swap_apply_of_ne_of_ne h1 h3]

end CFSG.AGLEmbedding.A15Local
