module

public import CFSG.LocalAnalysis.ComponentClassification.HSFLitAutL34CertInputs
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsBorel

public section

namespace CFSG.ComponentClassification.HSFLit.AutL34

open CFSG.PSL3Four.Native CFSG.ComponentClassification.PSL3Four
open CFSG.ComponentClassification.GrSLit.L34Facts

@[expose] def code (g : Equiv.Perm (Fin 42)) : ℕ :=
  enc ((List.finRange 42).map fun i => (g i : ℕ))

theorem pg_eq (c i : ℕ) : pg c i = c / 64 ^ i % 64 := by
  change (c >>> (6 * i)) &&& (2 ^ 6 - 1) = _
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow, pow_mul]
  norm_num

theorem pg_enc (l : List ℕ) (hl : ∀ a ∈ l, a < 64) (i : ℕ) (hi : i < l.length) :
    pg (enc l) i = l[i] := by
  induction l generalizing i with
  | nil => simp at hi
  | cons a l ih =>
    have ha : a < 64 := hl a (by simp)
    cases i with
    | zero =>
      rw [pg_eq, pow_zero, Nat.div_one, enc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha]
      rfl
    | succ i =>
      have h1 : pg (enc (a :: l)) (i + 1) = pg (enc l) i := by
        rw [pg_eq, pg_eq, enc, pow_succ', ← Nat.div_div_eq_div_mul,
          Nat.add_mul_div_left _ _ (by norm_num), Nat.div_eq_of_lt ha, zero_add]
      rw [h1, ih (fun b hb => hl b (List.mem_cons_of_mem a hb)) i (by simpa using hi)]
      rfl

theorem pg_code (g : Equiv.Perm (Fin 42)) (i : Fin 42) : pg (code g) i = g i := by
  unfold code
  rw [pg_enc _ (fun a ha => ?_) i (by simp)]
  · simp
  · obtain ⟨j, -, rfl⟩ := List.mem_map.1 ha
    exact (g j).isLt.trans (by norm_num)

theorem code_injective : Function.Injective code := fun g h e =>
  Equiv.ext fun i => Fin.ext (by rw [← pg_code g i, ← pg_code h i, e])

theorem code_inj {g h : Equiv.Perm (Fin 42)} : code g = code h ↔ g = h :=
  code_injective.eq_iff

theorem pcomp_eq (c d : ℕ) : pcomp c d = enc ((List.range 42).map fun i => pg c (pg d i)) :=
  rfl

theorem code_mul (g h : Equiv.Perm (Fin 42)) : code (g * h) = pcomp (code g) (code h) := by
  rw [pcomp_eq, show code (g * h) = enc ((List.finRange 42).map fun i => ((g * h) i : ℕ)) from rfl]
  congr 1
  apply List.ext_getElem (by simp)
  intro i h1 h2
  have hi : i < 42 := by simpa using h1
  simp only [List.getElem_map, List.getElem_finRange, List.getElem_range]
  have e1 : pg (code h) i = h ⟨i, hi⟩ := pg_code h ⟨i, hi⟩
  rw [e1, pg_code g (h ⟨i, hi⟩)]
  rfl

theorem code_one : code 1 = pid := by
  unfold code pid
  congr 1

theorem code_of_tabRep {t : Tab} {g : Equiv.Perm (Fin 42)} (h : TabRep t g) : code g = tcode t := by
  unfold code tcode
  congr 1
  apply List.ext_getElem (by simp [h.1])
  intro i h1 h2
  have hi : i < 42 := by simpa using h1
  simp only [List.getElem_map, List.getElem_finRange, Array.getElem_toList]
  have := h.apply ⟨i, hi⟩
  rw [getElem!_pos t i (by rw [h.1]; exact hi)] at this
  exact this.symm

theorem code_genS (j : ℕ) : code (genS j) = gcode j := code_of_tabRep (tabRep_genT j)

theorem code_r₂ : code r₂ = r2c := code_of_tabRep tabRep_r₂

theorem code_r₃ : code r₃ = r3c := code_of_tabRep tabRep_r₃

theorem code_r₄ : code r₄ = r4c := by
  rw [show r₄ = r₂ * r₃ from rfl, code_mul, code_r₂, code_r₃]
  rfl

theorem code_wordPerm (w : List ℕ) : code (wordPerm w) = wcode w := by
  unfold wordPerm wcode
  suffices h : ∀ g : Equiv.Perm (Fin 42), code (w.foldl (fun g j => g * genS j) g) =
      w.foldl (fun c j => pcomp c (gcode j)) (code g) by
    rw [h, code_one]
  induction w with
  | nil => intro g; rfl
  | cons j w ih =>
    intro g
    simp only [List.foldl_cons]
    rw [ih, code_mul, code_genS]

@[expose] def t0prod (w : List ℕ) : Equiv.Perm (Fin 42) :=
  w.foldl (fun g j => g * wordPerm (wT₀.getD j [])) 1

theorem code_t0prod (w : List ℕ) : code (t0prod w) = t0code w := by
  unfold t0prod t0code
  have hg : ∀ j, code (wordPerm (wT₀.getD j [])) = t0g.getD j pid := by
    intro j
    rw [code_wordPerm, t0g, show pid = wcode [] from rfl, List.getD_map]
  suffices h : ∀ g : Equiv.Perm (Fin 42),
      code (w.foldl (fun g j => g * wordPerm (wT₀.getD j [])) g) =
        w.foldl (fun c j => pcomp c (t0g.getD j pid)) (code g) by
    rw [h, code_one]
  induction w with
  | nil => intro g; rfl
  | cons j w ih =>
    intro g
    simp only [List.foldl_cons]
    rw [ih, code_mul, hg]

theorem wordPerm_getD_mem (j : ℕ) : wordPerm (wT₀.getD j []) ∈ T0 := by
  by_cases hj : j < wT₀.length
  · rw [List.getD_eq_getElem _ _ hj]
    exact Subgroup.subset_closure ⟨_, List.getElem_mem hj, rfl⟩
  · rw [List.getD_eq_default _ _ (by omega)]
    exact T0.one_mem

theorem t0prod_mem (w : List ℕ) : t0prod w ∈ T0 := by
  unfold t0prod
  suffices h : ∀ g ∈ T0, w.foldl (fun g j => g * wordPerm (wT₀.getD j [])) g ∈ T0 from
    h 1 T0.one_mem
  induction w with
  | nil => intro g hg; exact hg
  | cons j w ih =>
    intro g hg
    exact ih _ (T0.mul_mem hg (wordPerm_getD_mem j))

theorem memB_iff (x : ℕ) (L : List ℕ) : memB x L = true ↔ x ∈ L := by
  induction L with
  | nil => simp [memB]
  | cons a L ih => rw [memB, Bool.or_eq_true, ih, List.mem_cons, Nat.beq_eq]

theorem nodup_of_nodupB {L : List ℕ} (h : nodupB L = true) : L.Nodup := by
  induction L with
  | nil => exact List.nodup_nil
  | cons a L ih =>
    simp only [nodupB, Bool.and_eq_true, Bool.not_eq_true'] at h
    refine List.nodup_cons.2 ⟨fun ha => ?_, ih h.2⟩
    rw [← memB_iff] at ha
    rw [ha] at h
    exact Bool.noConfusion h.1

theorem isId_iff (g : Equiv.Perm (Fin 42)) : isId (code g) = true ↔ g = 1 := by
  rw [isId, Nat.beq_eq, ← code_one, code_inj]

theorem commC_iff (g h : Equiv.Perm (Fin 42)) : commC (code g) (code h) = true ↔ g * h = h * g := by
  rw [commC, Nat.beq_eq, ← code_mul, ← code_mul, code_inj]

theorem psq_code (g : Equiv.Perm (Fin 42)) : psq (code g) = code (g * g) := (code_mul g g).symm

theorem card_subtype_eq_countP {H : Subgroup (Equiv.Perm (Fin 42))} {L : List ℕ} (hL : L.Nodup)
    (hmem : ∀ g, g ∈ H ↔ code g ∈ L) (hsurj : ∀ c ∈ L, ∃ g, code g = c)
    (p : Equiv.Perm (Fin 42) → Prop) (f : ℕ → Bool) (hpf : ∀ g ∈ H, p g ↔ f (code g) = true) :
    Nat.card {g // g ∈ H ∧ p g} = L.countP f := by
  classical
  have hset : code '' {g | g ∈ H ∧ p g} = {c | c ∈ L.filter f} := by
    ext c
    simp only [Set.mem_image, Set.mem_ofPred_eq, List.mem_filter]
    constructor
    · rintro ⟨g, ⟨hgH, hgp⟩, rfl⟩
      exact ⟨(hmem g).1 hgH, (hpf g hgH).1 hgp⟩
    · rintro ⟨hcL, hcf⟩
      obtain ⟨g, rfl⟩ := hsurj c hcL
      have hgH := (hmem g).2 hcL
      exact ⟨g, ⟨hgH, (hpf g hgH).2 hcf⟩, rfl⟩
  have h1 : Nat.card {g // g ∈ H ∧ p g} = Nat.card (code '' {g | g ∈ H ∧ p g}) :=
    (Nat.card_image_of_injective code_injective _).symm
  rw [h1, hset, List.countP_eq_length_filter]
  have e2 : {c | c ∈ L.filter f} ≃ (L.filter f).toFinset :=
    Equiv.subtypeEquivRight fun c => List.mem_toFinset.symm
  rw [Nat.card_congr e2, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup (hL.filter f)]

theorem card_eq_length {H : Subgroup (Equiv.Perm (Fin 42))} {L : List ℕ} (hL : L.Nodup)
    (hmem : ∀ g, g ∈ H ↔ code g ∈ L) (hsurj : ∀ c ∈ L, ∃ g, code g = c) :
    Nat.card H = L.length := by
  have h := card_subtype_eq_countP hL hmem hsurj (fun _ => True) (fun _ => true) (by simp)
  rw [List.countP_true] at h
  rw [← h]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun g => by simp)

end CFSG.ComponentClassification.HSFLit.AutL34
