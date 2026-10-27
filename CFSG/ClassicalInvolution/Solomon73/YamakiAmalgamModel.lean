module

public import CFSG.ClassicalInvolution.Solomon73.YamakiTables
public import Certificates.Certificate550712

public section

namespace CFSG.ClassicalInvolution.Solomon73.Yamaki

open CFSG.Open

section Checks


theorem crGenCheck_holds : crGenCheck () = true := Certificates.certificate550712.1

theorem autCheck_holds : autCheck () = true := Certificates.certificate550712.2.1

theorem stabCheck_holds : stabCheck () = true := Certificates.certificate550712.2.2.1

theorem stdCheck_holds : stdCheck () = true := Certificates.certificate550712.2.2.2.1

theorem c1Check_holds : c1Check () = true := Certificates.certificate550712.2.2.2.2.1

theorem c2Check_holds : c2Check () = true := Certificates.certificate550712.2.2.2.2.2.1

theorem chainCheck_holds : chainCheck () = true := Certificates.certificate550712.2.2.2.2.2.2

end Checks

theorem sigmaWords_length : sigmaWords.length = 2 := rfl
theorem tau1Words_length : tau1Words.length = 2 := rfl
theorem tau2Words_length : tau2Words.length = 2 := rfl
theorem r1Words_length : r1Words.length = 2 := rfl
theorem repWords_length : repWords.length = 16 := rfl
theorem chainData_length : chainData.length = 8 := rfl

theorem letters_lt_two :
    (∀ w ∈ r1Words, ∀ l ∈ w, l < 2) ∧ (∀ p ∈ repWords, (∀ l ∈ p.1, l < 2) ∧ ∀ l ∈ p.2, l < 2) ∧
      (∀ w ∈ tests1, ∀ l ∈ w, l = 0) ∧ (∀ w ∈ tests2, ∀ l ∈ w, l < 2) ∧
      ∀ c ∈ chainData, (∀ l ∈ c.1, l < 2) ∧ ∀ s ∈ c.2, ∀ l ∈ s.2.2, l < 2 := by
  decide


@[expose] def sigmafam (j : ℕ) : StatedSp 3 (ZMod 2) := yword (sigmaWords.getD j [])

@[expose] def tau1fam (j : ℕ) : StatedSp 3 (ZMod 2) := yword (tau1Words.getD j [])

@[expose] def tau2fam (j : ℕ) : StatedSp 3 (ZMod 2) := yword (tau2Words.getD j [])

section Gen


theorem crGenCheck_spec :
    (∀ w ∈ sigmaWords, ∀ i ∈ w, i ∈ idxN0) ∧ (∀ w ∈ tau1Words, ∀ i ∈ w, i ∈ idxHhat) ∧
      ∀ w ∈ tau2Words, ∀ i ∈ w, i ∈ idxHhat := by
  have h := crGenCheck_holds
  simp only [crGenCheck, Bool.and_eq_true] at h
  exact ⟨mem_of_wordsIn h.1.1, mem_of_wordsIn h.1.2, mem_of_wordsIn h.2⟩

theorem sigmaA_get {j : ℕ} (hj : j < 2) : (sigmaA ())[j]! = code (sigmafam j) :=
  code_yword_getD (fun _ hi => (idxN0_spec hi).1) crGenCheck_spec.1
    (by rw [sigmaWords_length]; exact hj)

theorem tau1A_get {j : ℕ} (hj : j < 2) : (tau1A ())[j]! = code (tau1fam j) :=
  code_yword_getD (fun _ hi => (idxHhat_spec hi).1) crGenCheck_spec.2.1
    (by rw [tau1Words_length]; exact hj)

theorem tau2A_get {j : ℕ} (hj : j < 2) : (tau2A ())[j]! = code (tau2fam j) :=
  code_yword_getD (fun _ hi => (idxHhat_spec hi).1) crGenCheck_spec.2.2
    (by rw [tau2Words_length]; exact hj)

theorem sigmafam_mem_N0 (j : ℕ) : sigmafam j ∈ N0 :=
  yword_mem_N0 (letters_getD crGenCheck_spec.1 j)

theorem tau1fam_mem_Hhat (j : ℕ) : tau1fam j ∈ Hhat :=
  yword_mem_Hhat (letters_getD crGenCheck_spec.2.1 j)

theorem tau2fam_mem_Hhat (j : ℕ) : tau2fam j ∈ Hhat :=
  yword_mem_Hhat (letters_getD crGenCheck_spec.2.2 j)

end Gen

section Auts


theorem autCheck_spec :
    autOK (enumN ()) (gN ()) (sigmaA ()) (tabS ()) = true ∧
      autOK (enumH ()) (gH ()) (tau1A ()) (tabT1 ()) = true ∧
      autOK (enumH ()) (gH ()) (tau2A ()) (tabT2 ()) = true := by
  have h := autCheck_holds
  simp only [autCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem stabCheck_spec :
    (∀ j < 2, ((enumX ()).lookup (appF (enumN ()) (tabS ()) (gX ())[j]!)).isSome = true ∧
      ((enumX ()).lookup (appF (enumH ()) (tabT1 ()) (gX ())[j]!)).isSome = true ∧
      ((enumX ()).lookup (appF (enumH ()) (tabT2 ()) (gX ())[j]!)).isSome = true) ∧
      appF (enumH ()) (tabT1 ()) (genA ())[5]! = (genA ())[5]! ∧
      appF (enumH ()) (tabT2 ()) (genA ())[5]! = (genA ())[5]! := by
  have h := stabCheck_holds
  simp only [stabCheck, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at h
  exact ⟨fun j hj => ⟨(h.1.1 j hj).1.1, (h.1.1 j hj).1.2, (h.1.1 j hj).2⟩, h.1.2, h.2⟩

theorem exists_aut_closure {L : Subgroup (StatedSp 3 (ZMod 2))} {s h : ℕ → StatedSp 3 (ZMod 2)}
    {E : Enum} {gs hs F : Array (Array ℕ)} (hL : L = Subgroup.closure (s '' Set.Iio gs.size))
    (hgs : ∀ j < gs.size, gs[j]! = code (s j)) (hhs : ∀ j < gs.size, hs[j]! = code (h j))
    (hmem : ∀ j < gs.size, h j ∈ L) (henum : enumOK E gs = true)
    (haut : autOK E gs hs F = true) :
    ∃ φ : ↥L ≃* ↥L, ∀ x : ↥L, code (φ x : StatedSp 3 (ZMod 2)) = appF E F (code x) := by
  subst hL
  obtain ⟨φ, hφ, -⟩ := exists_mulEquiv_of_autOK hgs hhs hmem henum haut
  exact ⟨φ, hφ⟩

theorem exists_sigmaN : ∃ φ : ↥N0 ≃* ↥N0,
    ∀ x : ↥N0, code (φ x : StatedSp 3 (ZMod 2)) = appF (enumN ()) (tabS ()) (code x) :=
  exists_aut_closure (by rw [size_gN]; exact N0_eq_closure)
    (fun j hj => gN_get (size_gN ▸ hj)) (fun j hj => sigmaA_get (size_gN ▸ hj))
    (fun j _ => sigmafam_mem_N0 j) enumCheck_spec.2.1 autCheck_spec.1

theorem exists_tau1H : ∃ φ : ↥Hhat ≃* ↥Hhat,
    ∀ x : ↥Hhat, code (φ x : StatedSp 3 (ZMod 2)) = appF (enumH ()) (tabT1 ()) (code x) :=
  exists_aut_closure (by rw [size_gH]; exact Hhat_eq_closure)
    (fun j hj => gH_get (size_gH ▸ hj)) (fun j hj => tau1A_get (size_gH ▸ hj))
    (fun j _ => tau1fam_mem_Hhat j) enumCheck_spec.2.2 autCheck_spec.2.1

theorem exists_tau2H : ∃ φ : ↥Hhat ≃* ↥Hhat,
    ∀ x : ↥Hhat, code (φ x : StatedSp 3 (ZMod 2)) = appF (enumH ()) (tabT2 ()) (code x) :=
  exists_aut_closure (by rw [size_gH]; exact Hhat_eq_closure)
    (fun j hj => gH_get (size_gH ▸ hj)) (fun j hj => tau2A_get (size_gH ▸ hj))
    (fun j _ => tau2fam_mem_Hhat j) enumCheck_spec.2.2 autCheck_spec.2.2

noncomputable def sigmaN : ↥N0 ≃* ↥N0 := exists_sigmaN.choose

noncomputable def tau1H : ↥Hhat ≃* ↥Hhat := exists_tau1H.choose

noncomputable def tau2H : ↥Hhat ≃* ↥Hhat := exists_tau2H.choose

theorem code_sigmaN (x : ↥N0) :
    code (sigmaN x : StatedSp 3 (ZMod 2)) = appF (enumN ()) (tabS ()) (code x) :=
  exists_sigmaN.choose_spec x

theorem code_tau1H (x : ↥Hhat) :
    code (tau1H x : StatedSp 3 (ZMod 2)) = appF (enumH ()) (tabT1 ()) (code x) :=
  exists_tau1H.choose_spec x

theorem code_tau2H (x : ↥Hhat) :
    code (tau2H x : StatedSp 3 (ZMod 2)) = appF (enumH ()) (tabT2 ()) (code x) :=
  exists_tau2H.choose_spec x

theorem mem_X0_iff_of_gen {L : Subgroup (StatedSp 3 (ZMod 2))} (hXL : X0 ≤ L) (φ : ↥L ≃* ↥L)
    (hg : ∀ j < 2, (φ ⟨gfam j, hXL (gfam_mem_X0 j)⟩ : StatedSp 3 (ZMod 2)) ∈ X0) (x : ↥L) :
    (φ x : StatedSp 3 (ZMod 2)) ∈ X0 ↔ (x : StatedSp 3 (ZMod 2)) ∈ X0 := by
  have hfwd : ∀ y ∈ X0, ∀ hy : y ∈ L, (φ ⟨y, hy⟩ : StatedSp 3 (ZMod 2)) ∈ X0 := by
    intro y hyX
    rw [X0_eq_closure] at hyX
    induction hyX using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact fun _ => hg j hj
    | one =>
      intro h1
      have e : (⟨1, h1⟩ : ↥L) = 1 := rfl
      rw [e, map_one]
      exact X0.one_mem
    | mul y z hy hz ihy ihz =>
      intro hyz
      have hyL : y ∈ L := hXL (X0_eq_closure ▸ hy)
      have hzL : z ∈ L := hXL (X0_eq_closure ▸ hz)
      have e : (⟨y * z, hyz⟩ : ↥L) = ⟨y, hyL⟩ * ⟨z, hzL⟩ := rfl
      rw [e, map_mul]
      exact X0.mul_mem (ihy hyL) (ihz hzL)
    | inv y hy ih =>
      intro hy'
      have hyL : y ∈ L := hXL (X0_eq_closure ▸ hy)
      have e : (⟨y⁻¹, hy'⟩ : ↥L) = (⟨y, hyL⟩ : ↥L)⁻¹ := rfl
      rw [e, map_inv]
      exact X0.inv_mem (ih hyL)
  refine ⟨fun hx => ?_, fun hx => hfwd x hx x.2⟩
  let f : ↥X0 → ↥X0 := fun y => ⟨φ ⟨y, hXL y.2⟩, hfwd y y.2 (hXL y.2)⟩
  have hf : Function.Injective f := by
    intro y z hyz
    have h1 : (φ ⟨y, hXL y.2⟩ : StatedSp 3 (ZMod 2)) = φ ⟨z, hXL z.2⟩ :=
      congrArg (Subtype.val : ↥X0 → StatedSp 3 (ZMod 2)) hyz
    have h3 : (⟨y, hXL y.2⟩ : ↥L) = ⟨z, hXL z.2⟩ := φ.injective (Subtype.ext h1)
    exact Subtype.ext (congrArg (Subtype.val : ↥L → StatedSp 3 (ZMod 2)) h3)
  obtain ⟨y, hy⟩ := (Finite.injective_iff_surjective.mp hf) ⟨φ x, hx⟩
  have h2 : (φ ⟨y, hXL y.2⟩ : StatedSp 3 (ZMod 2)) = φ x :=
    congrArg (Subtype.val : ↥X0 → StatedSp 3 (ZMod 2)) hy
  have hxy : (⟨y, hXL y.2⟩ : ↥L) = x := φ.injective (Subtype.ext h2)
  rw [← hxy]
  exact y.2

theorem mem_X0_sigmaN_iff (x : ↥N0) :
    (sigmaN x : StatedSp 3 (ZMod 2)) ∈ X0 ↔ (x : StatedSp 3 (ZMod 2)) ∈ X0 :=
  mem_X0_iff_of_gen X0_le_N0 sigmaN (fun j hj => by
    rw [mem_X0_iff_isSome, code_sigmaN, ← gX_get hj]
    exact (stabCheck_spec.1 j hj).1) x

theorem mem_X0_tau1H_iff (x : ↥Hhat) :
    (tau1H x : StatedSp 3 (ZMod 2)) ∈ X0 ↔ (x : StatedSp 3 (ZMod 2)) ∈ X0 :=
  mem_X0_iff_of_gen X0_le_Hhat tau1H (fun j hj => by
    rw [mem_X0_iff_isSome, code_tau1H, ← gX_get hj]
    exact (stabCheck_spec.1 j hj).2.1) x

theorem mem_X0_tau2H_iff (x : ↥Hhat) :
    (tau2H x : StatedSp 3 (ZMod 2)) ∈ X0 ↔ (x : StatedSp 3 (ZMod 2)) ∈ X0 :=
  mem_X0_iff_of_gen X0_le_Hhat tau2H (fun j hj => by
    rw [mem_X0_iff_isSome, code_tau2H, ← gX_get hj]
    exact (stabCheck_spec.1 j hj).2.2) x

theorem alpha_mem_Hhat : alpha ∈ Hhat := S0_le_Hhat alpha_mem_S0

private theorem code_alpha : code alpha = (genA ())[5]! := code_yamakiSp 5

theorem tau1H_alpha : (tau1H ⟨alpha, alpha_mem_Hhat⟩ : StatedSp 3 (ZMod 2)) = alpha :=
  code_injective (by rw [code_tau1H, code_alpha]; exact stabCheck_spec.2.1)

theorem tau2H_alpha : (tau2H ⟨alpha, alpha_mem_Hhat⟩ : StatedSp 3 (ZMod 2)) = alpha :=
  code_injective (by rw [code_tau2H, code_alpha]; exact stabCheck_spec.2.2)

end Auts

section Coverage


@[expose] def gX0 (j : ℕ) : ↥X0 := ⟨gfam j, gfam_mem_X0 j⟩

@[expose] def gvalX (u : List ℕ) : ↥X0 := (u.map gX0).prod

theorem coe_gvalX (u : List ℕ) : (gvalX u : StatedSp 3 (ZMod 2)) = (u.map gfam).prod := by
  rw [gvalX, ← Subgroup.coe_subtype, map_list_prod, List.map_map]
  rfl

@[expose] def r1fam (r : ℕ) : ↥X0 := gvalX (r1Words.getD r [])

@[expose] def repfam (k j : ℕ) : ↥X0 :=
  gvalX (if j = 0 then (repWords.getD k ([], [])).1 else (repWords.getD k ([], [])).2)

theorem wordA_gX {u : List ℕ} (hu : ∀ l ∈ u, l < 2) :
    wordA (gX ()) u = code (gvalX u : StatedSp 3 (ZMod 2)) := by
  rw [coe_gvalX]
  exact (code_prod_map u fun l hl => gX_get (hu l hl)).symm

theorem size_r1A : (r1A ()).size = 2 := size_wordsA _ _

theorem r1A_get {r : ℕ} (hr : r < 2) : (r1A ())[r]! = code (r1fam r : StatedSp 3 (ZMod 2)) := by
  rw [r1A, getElem!_wordsA _ _ (by rw [r1Words_length]; exact hr), r1fam]
  exact wordA_gX (letters_lt_two.1 _ (getD_mem (by rw [r1Words_length]; exact hr)))

theorem size_repsA : (repsA ()).size = 16 := by
  simp [repsA, repWords_length]

theorem repsA_get {k : ℕ} (hk : k < 16) :
    (repsA ())[k]!.1 = code (repfam k 0 : StatedSp 3 (ZMod 2)) ∧
      (repsA ())[k]!.2 = code (repfam k 1 : StatedSp 3 (ZMod 2)) := by
  have hk' : k < repWords.length := by rw [repWords_length]; exact hk
  have hmem : repWords.getD k ([], []) ∈ repWords := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk', Option.getD_some]
    exact List.getElem_mem hk'
  have he : (repsA ())[k]! = (wordA (gX ()) (repWords.getD k ([], [])).1,
      wordA (gX ()) (repWords.getD k ([], [])).2) := by
    rw [getElem!_pos (repsA ()) k (by rw [size_repsA]; exact hk), List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hk', Option.getD_some]
    simp [repsA]
  rw [he, repfam, repfam, if_pos rfl, if_neg one_ne_zero]
  exact ⟨wordA_gX (letters_lt_two.2.1 _ hmem).1, wordA_gX (letters_lt_two.2.1 _ hmem).2⟩

theorem code_eq_idA_iff (x : StatedSp 3 (ZMod 2)) : code x = idA () ↔ x = 1 := by
  rw [← code_one]
  exact code_injective.eq_iff

theorem pattOK_of_injective (ψ : ↥X0 →* StatedSp 3 (ZMod 2)) (hψ : Function.Injective ψ)
    {ys gs : Array (Array ℕ)} :
    ∀ tests : List (List ℕ), (∀ w ∈ tests, ∀ l ∈ w, ys[l]! = code (ψ (gX0 l))) →
      (∀ w ∈ tests, ∀ l ∈ w, gs[l]! = code (gfam l)) →
      pattOK ys tests (tests.map fun w => decide (wordA gs w = idA ())) = true
  | [], _, _ => rfl
  | w :: ws, hys, hgs => by
    have hrest := pattOK_of_injective ψ hψ ws (fun v hv => hys v (List.mem_cons_of_mem w hv))
      (fun v hv => hgs v (List.mem_cons_of_mem w hv))
    simp only [pattOK, List.map_cons, List.zip_cons_cons, List.all_cons,
      Bool.and_eq_true] at hrest ⊢
    refine ⟨?_, hrest⟩
    have h1 : wordA ys w = code (ψ (gvalX w)) := by
      rw [gvalX, map_list_prod, List.map_map]
      exact (code_prod_map w fun l hl => hys w List.mem_cons_self l hl).symm
    have h2 : wordA gs w = code (gvalX w : StatedSp 3 (ZMod 2)) := by
      rw [coe_gvalX]
      exact (code_prod_map w fun l hl => hgs w List.mem_cons_self l hl).symm
    rw [h1, h2, beq_iff_eq, decide_eq_decide, code_eq_idA_iff, code_eq_idA_iff,
      map_eq_one_iff ψ hψ, OneMemClass.coe_eq_one]

theorem c1Check_spec : ∀ i < (enumX ()).elems.size,
    pattOK #[(enumX ()).elems[i]!] tests1
      (tests1.map fun w => decide (wordA #[(gX ())[0]!] w = idA ())) = true →
    ∃ r < (r1A ()).size, ∃ j < (enumX ()).elems.size,
      compA (enumX ()).elems[j]! (enumX ()).elems[i]! =
        compA (r1A ())[r]! (enumX ()).elems[j]! := by
  intro i hi hp
  have h := c1Check_holds
  simp only [c1Check, allLt_iff, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h i hi with h | h
  · rw [hp] at h
    cases h
  · split at h
    · rename_i r j _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨r, h.1.1, j, h.1.2, h.2⟩
    · cases h

theorem c2Check_spec : ∀ r < (r1A ()).size, ∀ i < (enumX ()).elems.size,
    pattOK #[(r1A ())[r]!, (enumX ()).elems[i]!] tests2
      (tests2.map fun w => decide (wordA (gX ()) w = idA ())) = true →
    ∃ k < (repsA ()).size, ∃ j < (enumX ()).elems.size,
      compA (enumX ()).elems[j]! (r1A ())[r]! = compA (repsA ())[k]!.1 (enumX ()).elems[j]! ∧
      compA (enumX ()).elems[j]! (enumX ()).elems[i]! =
        compA (repsA ())[k]!.2 (enumX ()).elems[j]! := by
  intro r hr i hi hp
  have h := c2Check_holds
  simp only [c2Check, allLt_iff, Bool.or_eq_true, Bool.not_eq_true'] at h
  rcases h r hr i hi with h | h
  · rw [hp] at h
    cases h
  · split at h
    · rename_i k j _
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact ⟨k, h.1.1.1, j, h.1.1.2, h.1.2, h.2⟩
    · cases h

theorem getElem!_singleton (a : Array ℕ) : #[a][0]! = a := rfl

theorem getElem!_pair_zero (a b : Array ℕ) : #[a, b][0]! = a := rfl

theorem getElem!_pair_one (a b : Array ℕ) : #[a, b][1]! = b := rfl

theorem exists_rep_of_injective (ψ : ↥X0 →* StatedSp 3 (ZMod 2)) (hψ : Function.Injective ψ)
    (hX : ∀ x, ψ x ∈ X0) :
    ∃ k < 16, ∃ w ∈ X0, ∀ j < 2,
      ψ (gX0 j) = w⁻¹ * (repfam k j : StatedSp 3 (ZMod 2)) * w := by
  obtain ⟨i₁, hi₁, hi₁e⟩ := exists_lt_of_mem_X0 (hX (gX0 0))
  have hp1 := pattOK_of_injective (ys := #[(enumX ()).elems[i₁]!]) (gs := #[(gX ())[0]!]) ψ hψ
    tests1 (fun w hw l hl => by
      rw [letters_lt_two.2.2.1 w hw l hl, getElem!_singleton]
      exact hi₁e)
    (fun w hw l hl => by
      rw [letters_lt_two.2.2.1 w hw l hl, getElem!_singleton]
      exact gX_get (by norm_num))
  obtain ⟨r, hr, j₀, hj₀, hc⟩ := c1Check_spec i₁ hi₁ hp1
  rw [size_r1A] at hr
  obtain ⟨z, hz, hze⟩ := exists_mem_X0_of_lt hj₀
  have hzc : z * ψ (gX0 0) = (r1fam r : StatedSp 3 (ZMod 2)) * z := by
    apply code_injective
    rw [code_mul z, code_mul (r1fam r : StatedSp 3 (ZMod 2)) z, hze, ← hi₁e, hc, r1A_get hr]
  set ψ' : ↥X0 →* StatedSp 3 (ZMod 2) := (MulAut.conj z).toMonoidHom.comp ψ with hψ'def
  have hψ' : Function.Injective ψ' := (MulAut.conj z).injective.comp hψ
  have hψ'x : ∀ x, ψ' x = z * ψ x * z⁻¹ := fun x => rfl
  have hψ'0 : ψ' (gX0 0) = r1fam r := by
    rw [hψ'x, hzc, mul_inv_cancel_right]
  have hy₂' : z * ψ (gX0 1) * z⁻¹ ∈ X0 := X0.mul_mem (X0.mul_mem hz (hX _)) (X0.inv_mem hz)
  obtain ⟨i₂, hi₂, hi₂e⟩ := exists_lt_of_mem_X0 hy₂'
  have hp2 := pattOK_of_injective (ys := #[(r1A ())[r]!, (enumX ()).elems[i₂]!]) (gs := gX ())
    ψ' hψ' tests2 (fun w hw l hl => by
      have hl2 := letters_lt_two.2.2.2.1 w hw l hl
      interval_cases l
      · rw [getElem!_pair_zero, hψ'0, r1A_get hr]
      · rw [getElem!_pair_one, hψ'x, hi₂e])
    (fun w hw l hl => gX_get (letters_lt_two.2.2.2.1 w hw l hl))
  obtain ⟨k, hk, j₁, hj₁, hk1, hk2⟩ := c2Check_spec r (by rw [size_r1A]; exact hr) i₂ hi₂ hp2
  rw [size_repsA] at hk
  obtain ⟨x, hx, hxe⟩ := exists_mem_X0_of_lt hj₁
  obtain ⟨hR1, hR2⟩ := repsA_get hk
  have hxc : x * (r1fam r : StatedSp 3 (ZMod 2)) = (repfam k 0 : StatedSp 3 (ZMod 2)) * x := by
    apply code_injective
    rw [code_mul x, code_mul (repfam k 0 : StatedSp 3 (ZMod 2)) x, hxe, ← hR1, ← r1A_get hr, hk1]
  have hxy : x * (z * ψ (gX0 1) * z⁻¹) = (repfam k 1 : StatedSp 3 (ZMod 2)) * x := by
    apply code_injective
    rw [code_mul x (z * ψ (gX0 1) * z⁻¹), code_mul (repfam k 1 : StatedSp 3 (ZMod 2)) x, hxe,
      ← hR2, ← hi₂e, hk2]
  refine ⟨k, hk, x * z, X0.mul_mem hx hz, fun j hj => ?_⟩
  rw [mul_assoc, eq_inv_mul_iff_mul_eq]
  interval_cases j
  · calc x * z * ψ (gX0 0) = x * (z * ψ (gX0 0)) := mul_assoc _ _ _
      _ = x * (r1fam r : StatedSp 3 (ZMod 2)) * z := by rw [hzc, mul_assoc]
      _ = (repfam k 0 : StatedSp 3 (ZMod 2)) * (x * z) := by rw [hxc, mul_assoc]
  · calc x * z * ψ (gX0 1) = x * (z * ψ (gX0 1) * z⁻¹) * z := by group
      _ = (repfam k 1 : StatedSp 3 (ZMod 2)) * (x * z) := by rw [hxy, mul_assoc]

end Coverage

section Standard


@[expose] noncomputable def stdH (k : ℕ) : MulAut ↥Hhat :=
  (if k / 2 % 2 = 1 then tau1H else 1) * (if k % 2 = 1 then tau2H else 1)

@[expose] noncomputable def stdN (k : ℕ) : MulAut ↥N0 := if k / 4 % 2 = 1 then sigmaN else 1

theorem stdH_mem_X0_iff (k : ℕ) (x : ↥Hhat) :
    (stdH k x : StatedSp 3 (ZMod 2)) ∈ X0 ↔ (x : StatedSp 3 (ZMod 2)) ∈ X0 := by
  have h1 : ∀ y : ↥Hhat, ((if k / 2 % 2 = 1 then tau1H else 1 : MulAut ↥Hhat) y :
      StatedSp 3 (ZMod 2)) ∈ X0 ↔ (y : StatedSp 3 (ZMod 2)) ∈ X0 := by
    intro y
    split_ifs
    · exact mem_X0_tau1H_iff y
    · rfl
  have h2 : ∀ y : ↥Hhat, ((if k % 2 = 1 then tau2H else 1 : MulAut ↥Hhat) y :
      StatedSp 3 (ZMod 2)) ∈ X0 ↔ (y : StatedSp 3 (ZMod 2)) ∈ X0 := by
    intro y
    split_ifs
    · exact mem_X0_tau2H_iff y
    · rfl
  rw [stdH, MulAut.mul_apply, h1, h2]

theorem stdN_mem_X0_iff (k : ℕ) (x : ↥N0) :
    (stdN k x : StatedSp 3 (ZMod 2)) ∈ X0 ↔ (x : StatedSp 3 (ZMod 2)) ∈ X0 := by
  rw [stdN]
  split_ifs
  · exact mem_X0_sigmaN_iff x
  · rfl

theorem stdH_alpha (k : ℕ) : stdH k ⟨alpha, alpha_mem_Hhat⟩ = ⟨alpha, alpha_mem_Hhat⟩ := by
  have h1 : (tau1H ⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) = ⟨alpha, alpha_mem_Hhat⟩ :=
    Subtype.ext tau1H_alpha
  have h2 : (tau2H ⟨alpha, alpha_mem_Hhat⟩ : ↥Hhat) = ⟨alpha, alpha_mem_Hhat⟩ :=
    Subtype.ext tau2H_alpha
  rw [stdH, MulAut.mul_apply]
  split_ifs <;> simp only [h1, h2, MulAut.one_apply]

@[expose] noncomputable def stdHom (k : ℕ) : ↥X0 →* StatedSp 3 (ZMod 2) :=
  N0.subtype.comp ((stdN k).toMonoidHom.comp (MonoidHom.codRestrict
    (Hhat.subtype.comp ((stdH k).toMonoidHom.comp (Subgroup.inclusion X0_le_Hhat))) N0
    fun x => X0_le_N0 ((stdH_mem_X0_iff k _).mpr x.2)))

theorem stdH_mem_N0 (k : ℕ) (x : ↥X0) :
    (stdH k ⟨x, X0_le_Hhat x.2⟩ : StatedSp 3 (ZMod 2)) ∈ N0 :=
  X0_le_N0 ((stdH_mem_X0_iff k _).mpr x.2)

theorem stdHom_apply (k : ℕ) (x : ↥X0) :
    stdHom k x = (stdN k ⟨stdH k ⟨x, X0_le_Hhat x.2⟩, stdH_mem_N0 k x⟩ : StatedSp 3 (ZMod 2)) :=
  rfl

theorem code_stdHom (k : ℕ) (x : ↥X0) :
    code (stdHom k x) = stdRep (enumN ()) (enumH ()) (tabS ()) (tabT1 ()) (tabT2 ()) k
      (code (x : StatedSp 3 (ZMod 2))) := by
  rw [stdHom_apply, stdRep]
  simp only [stdN, stdH, MulAut.mul_apply]
  have hb : ∀ y : ↥Hhat, code ((if k % 2 = 1 then tau2H else 1 : MulAut ↥Hhat) y :
      StatedSp 3 (ZMod 2)) =
      if k % 2 = 1 then appF (enumH ()) (tabT2 ()) (code y) else code y := by
    intro y
    split_ifs
    · exact code_tau2H y
    · rfl
  have ha : ∀ y : ↥Hhat, code ((if k / 2 % 2 = 1 then tau1H else 1 : MulAut ↥Hhat) y :
      StatedSp 3 (ZMod 2)) =
      if k / 2 % 2 = 1 then appF (enumH ()) (tabT1 ()) (code y) else code y := by
    intro y
    split_ifs
    · exact code_tau1H y
    · rfl
  have he : ∀ y : ↥N0, code ((if k / 4 % 2 = 1 then sigmaN else 1 : MulAut ↥N0) y :
      StatedSp 3 (ZMod 2)) =
      if k / 4 % 2 = 1 then appF (enumN ()) (tabS ()) (code y) else code y := by
    intro y
    split_ifs
    · exact code_sigmaN y
    · rfl
  rw [he, ha, hb]

theorem stdCheck_spec : ∀ k < 8,
    (repsA ())[k]!.1 =
        stdRep (enumN ()) (enumH ()) (tabS ()) (tabT1 ()) (tabT2 ()) k (gX ())[0]! ∧
      (repsA ())[k]!.2 =
        stdRep (enumN ()) (enumH ()) (tabS ()) (tabT1 ()) (tabT2 ()) k (gX ())[1]! := by
  have h := stdCheck_holds
  simp only [stdCheck, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at h
  exact fun k hk => h.2 k hk

theorem repfam_std {k : ℕ} (hk : k < 8) {j : ℕ} (hj : j < 2) :
    (repfam k j : StatedSp 3 (ZMod 2)) = stdHom k (gX0 j) := by
  apply code_injective
  rw [code_stdHom]
  obtain ⟨h1, h2⟩ := stdCheck_spec k hk
  obtain ⟨hR1, hR2⟩ := repsA_get (by omega : k < 16)
  interval_cases j
  · rw [← hR1, h1, gX_get (by norm_num)]
    rfl
  · rw [← hR2, h2, gX_get (by norm_num)]
    rfl

theorem hom_ext_X0 {K : Type*} [Group K] {f₁ f₂ : ↥X0 →* K}
    (h : ∀ j < 2, f₁ (gX0 j) = f₂ (gX0 j)) : f₁ = f₂ := by
  ext x
  have key : ∀ y ∈ Subgroup.closure (gfam '' Set.Iio 2), ∀ hy : y ∈ X0,
      f₁ ⟨y, hy⟩ = f₂ ⟨y, hy⟩ := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      obtain ⟨j, hj, rfl⟩ := hy
      exact fun _ => h j hj
    | one =>
      intro h1
      have e : (⟨1, h1⟩ : ↥X0) = 1 := rfl
      rw [e, map_one, map_one]
    | mul y z hy hz ihy ihz =>
      intro hyz
      have hyX : y ∈ X0 := X0_eq_closure ▸ hy
      have hzX : z ∈ X0 := X0_eq_closure ▸ hz
      have e : (⟨y * z, hyz⟩ : ↥X0) = ⟨y, hyX⟩ * ⟨z, hzX⟩ := rfl
      rw [e, map_mul, map_mul, ihy hyX, ihz hzX]
    | inv y hy ih =>
      intro hy'
      have hyX : y ∈ X0 := X0_eq_closure ▸ hy
      have e : (⟨y⁻¹, hy'⟩ : ↥X0) = (⟨y, hyX⟩ : ↥X0)⁻¹ := rfl
      rw [e, map_inv, map_inv, ih hyX]
  exact key x (X0_eq_closure ▸ x.2) x.2

theorem eq_std_of_rep (ψ : ↥X0 →* StatedSp 3 (ZMod 2)) {k : ℕ} (hk : k < 8)
    {w : StatedSp 3 (ZMod 2)}
    (hψ : ∀ j < 2, ψ (gX0 j) = w⁻¹ * (repfam k j : StatedSp 3 (ZMod 2)) * w)
    (x : ↥X0) : ψ x = w⁻¹ * stdHom k x * w := by
  have := hom_ext_X0 (f₁ := ψ) (f₂ := (MulAut.conj w⁻¹).toMonoidHom.comp (stdHom k)) (by
    intro j hj
    rw [hψ j hj, repfam_std hk hj]
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulAut.conj_apply, inv_inv])
  rw [this]
  simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]

end Standard

theorem pi12_mem_X0 : pi12 ∈ X0 := S0_le_X0 pi12_mem_S0

theorem pi3_mem_X0 : pi3 ∈ X0 := S0_le_X0 pi3_mem_S0

inductive FusionStep (ψ : ↥X0 →* StatedSp 3 (ZMod 2)) : ↥X0 → ↥X0 → Prop
  | hhat {x y : ↥X0} (c : StatedSp 3 (ZMod 2)) : c ∈ Hhat →
      c * (y : StatedSp 3 (ZMod 2)) = x * c → FusionStep ψ x y
  | n0 {x y : ↥X0} (c : StatedSp 3 (ZMod 2)) : c ∈ N0 → c * ψ y = ψ x * c → FusionStep ψ x y

section Chains


private theorem code_pi12 : code pi12 = (genA ())[4]! := code_yamakiSp 4

private theorem code_pi3 : code pi3 = compA (genA ())[5]! (genA ())[4]! := by
  rw [pi3, code_mul, code_alpha, code_pi12]

theorem chainCheck_spec : ∀ t < 8,
    wordA (gX ()) (chainData[t]!).1 = (genA ())[4]! ∧
      stepsOK (genA ()) (gX ()) #[(repsA ())[8 + t]!.1, (repsA ())[8 + t]!.2] (chainData[t]!).1
        (chainData[t]!).2 = true := by
  have h := chainCheck_holds
  simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq, allLt_iff] at h
  exact fun t ht => h.2 t ht

theorem psi_gvalX (ψ : ↥X0 →* StatedSp 3 (ZMod 2)) {k : ℕ} {w : StatedSp 3 (ZMod 2)}
    (hψ : ∀ j < 2, ψ (gX0 j) = w⁻¹ * (repfam k j : StatedSp 3 (ZMod 2)) * w) :
    ∀ u : List ℕ, (∀ l ∈ u, l < 2) →
      ψ (gvalX u) = w⁻¹ * (u.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod * w
  | [], _ => by
    rw [gvalX, List.map_nil, List.prod_nil, map_one, List.map_nil, List.prod_nil, mul_one,
      inv_mul_cancel]
  | l :: u, hu => by
    have ih := psi_gvalX ψ hψ u fun l' hl' => hu l' (List.mem_cons_of_mem l hl')
    rw [gvalX, List.map_cons, List.prod_cons, map_mul, ← gvalX, ih,
      hψ l (hu l List.mem_cons_self), List.map_cons, List.prod_cons]
    group

theorem chain_of_stepsOK (ψ : ↥X0 →* StatedSp 3 (ZMod 2)) {k : ℕ} (hk : k < 16)
    {w : StatedSp 3 (ZMod 2)} (hw : w ∈ X0)
    (hψ : ∀ j < 2, ψ (gX0 j) = w⁻¹ * (repfam k j : StatedSp 3 (ZMod 2)) * w) :
    ∀ (steps : List (Bool × List ℕ × List ℕ)) (cur : List ℕ), (∀ l ∈ cur, l < 2) →
      (∀ s ∈ steps, ∀ l ∈ s.2.2, l < 2) →
      stepsOK (genA ()) (gX ()) #[(repsA ())[k]!.1, (repsA ())[k]!.2] cur steps = true →
      Relation.ReflTransGen (FusionStep ψ) (gvalX cur) ⟨pi3, pi3_mem_X0⟩ := by
  obtain ⟨hR1, hR2⟩ := repsA_get hk
  have hys : ∀ u : List ℕ, (∀ l ∈ u, l < 2) →
      wordA #[(repsA ())[k]!.1, (repsA ())[k]!.2] u =
        code (u.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod := by
    intro u hu
    refine (code_prod_map u fun l hl => ?_).symm
    have hl2 := hu l hl
    interval_cases l
    · rw [getElem!_pair_zero, hR1]
    · rw [getElem!_pair_one, hR2]
  intro steps
  induction steps with
  | nil =>
    intro cur hcur _ h
    simp only [stepsOK, decide_eq_true_eq] at h
    have he : gvalX cur = ⟨pi3, pi3_mem_X0⟩ :=
      Subtype.ext (code_injective (by rw [← wordA_gX hcur, h, code_pi3]))
    rw [he]
  | cons st rest ih =>
    obtain ⟨kind, wc, nxt⟩ := st
    intro cur hcur hsteps h
    have hnxt : ∀ l ∈ nxt, l < 2 := hsteps _ List.mem_cons_self
    simp only [stepsOK, Bool.and_eq_true] at h
    obtain ⟨hstep, hrest⟩ := h
    refine Relation.ReflTransGen.head ?_ (ih nxt hnxt (fun s hs => hsteps s
      (List.mem_cons_of_mem _ hs)) hrest)
    cases kind with
    | true =>
      simp only [if_true, Bool.and_eq_true, decide_eq_true_eq] at hstep
      obtain ⟨hin, hc⟩ := hstep
      have hwc := mem_of_wordsIn hin wc List.mem_cons_self
      refine FusionStep.hhat (yword wc) (yword_mem_Hhat hwc) (code_injective ?_)
      rw [code_mul, code_mul, code_yword fun i hi => (idxHhat_spec (hwc i hi)).1,
        ← wordA_gX hnxt, ← wordA_gX hcur, hc]
    | false =>
      simp only [Bool.false_eq_true, if_false, Bool.and_eq_true, decide_eq_true_eq] at hstep
      obtain ⟨hin, hc⟩ := hstep
      have hwc := mem_of_wordsIn hin wc List.mem_cons_self
      set c := yword wc
      have hcN : c ∈ N0 := yword_mem_N0 hwc
      have hcY : c * (nxt.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod =
          (cur.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod * c := by
        apply code_injective
        rw [code_mul, code_mul, code_yword fun i hi => (idxN0_spec (hwc i hi)).1,
          ← hys nxt hnxt, ← hys cur hcur, hc]
      refine FusionStep.n0 (w⁻¹ * c * w)
        (N0.mul_mem (N0.mul_mem (N0.inv_mem (X0_le_N0 hw)) hcN) (X0_le_N0 hw)) ?_
      rw [psi_gvalX ψ hψ nxt hnxt, psi_gvalX ψ hψ cur hcur]
      calc w⁻¹ * c * w * (w⁻¹ * (nxt.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod * w)
          = w⁻¹ * (c * (nxt.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod) * w := by
            group
        _ = w⁻¹ * ((cur.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod * c) * w := by
            rw [hcY]
        _ = w⁻¹ * (cur.map fun l => (repfam k l : StatedSp 3 (ZMod 2))).prod * w *
            (w⁻¹ * c * w) := by group

theorem chain_of_twisted (ψ : ↥X0 →* StatedSp 3 (ZMod 2)) {k : ℕ} (hk8 : 8 ≤ k) (hk : k < 16)
    {w : StatedSp 3 (ZMod 2)} (hw : w ∈ X0)
    (hψ : ∀ j < 2, ψ (gX0 j) = w⁻¹ * (repfam k j : StatedSp 3 (ZMod 2)) * w) :
    Relation.ReflTransGen (FusionStep ψ) ⟨pi12, pi12_mem_X0⟩ ⟨pi3, pi3_mem_X0⟩ := by
  obtain ⟨hstart, hsteps⟩ := chainCheck_spec (k - 8) (by omega)
  rw [show 8 + (k - 8) = k by omega] at hsteps
  have hlen : k - 8 < chainData.length := by rw [chainData_length]; omega
  have hmem : chainData[k - 8]! ∈ chainData := by
    rw [getElem!_pos chainData (k - 8) hlen]
    exact List.getElem_mem hlen
  have hl := letters_lt_two.2.2.2.2 _ hmem
  have h0 : gvalX (chainData[k - 8]!).1 = ⟨pi12, pi12_mem_X0⟩ :=
    Subtype.ext (code_injective (by rw [← wordA_gX hl.1, hstart, code_pi12]))
  rw [← h0]
  exact chain_of_stepsOK ψ hk hw hψ _ _ hl.1 hl.2 hsteps

end Chains

end CFSG.ClassicalInvolution.Solomon73.Yamaki
