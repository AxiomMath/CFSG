module

public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModelsTests
public import CFSG.LocalAnalysis.ComponentClassification.AS81Sec4HeModels

public section

namespace CFSG.ComponentClassification.AS81.HeTri

open Subgroup CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
open CFSG.Monster.B.Fischer CFSG.ComponentClassification.AS81.HeSylow
open CFSG.ComponentClassification.AS81.Hexa

section Enum

variable {n : ℕ} {ps : List ℕ} {gs : List (Array ℕ)} {m : ℕ}

theorem enumOK_of_enumCheckK (h : enumCheckK n ps gs m = true) :
    enumOK n gs.toArray ps (certK n ps gs m) = true := by
  simp only [enumCheckK, Bool.and_eq_true] at h
  exact h.1

theorem mem_grpN_iffK (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true)
    {x : Equiv.Perm (Fin n)} : x ∈ grpN n gs ↔ ∃ t ∈ eltsK n ps gs m, Rep n t x := by
  have hok := enumOK_of_enumCheckK h
  constructor
  · intro hx
    obtain ⟨i, hi, hr⟩ := enumOK_exists_rep hps hok hx
    refine ⟨_, ?_, hr⟩
    rw [getElem!_pos (certK n ps gs m).pts i hi]
    exact Array.getElem_mem_toList hi
  · rintro ⟨t, ht, hr⟩
    exact enumOK_mem_of_mem hps hok hr ht

theorem card_grpNK (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true) :
    Nat.card (grpN n gs) = m := by
  have hok := enumOK_of_enumCheckK h
  have hm : (certK n ps gs m).pts.size = m := by
    simp only [enumCheckK, Bool.and_eq_true, beq_iff_eq] at h
    exact h.2
  rw [grpN, (enumOK_spec hps hok).2.1, hm]

theorem validA_of_mem_gensK (h : enumCheckK n ps gs m = true) {a : Array ℕ} (ha : a ∈ gs) :
    validA n a = true := by
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem ha
  have := enumOK_gens_valid (enumOK_of_enumCheckK h) (k := k) (by simpa using hk)
  simpa [getElem!_pos gs.toArray k (by simpa using hk)] using this

theorem validA_of_mem_eltsK (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true)
    {t : Array ℕ} (ht : t ∈ eltsK n ps gs m) : validA n t = true := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hi' : i < (certK n ps gs m).pts.size := by simpa [eltsK] using hi
  have := (enumOK_spec hps (enumOK_of_enumCheckK h)).2.2 i hi'
  rw [getElem!_pos (certK n ps gs m).pts i hi'] at this
  simpa [eltsK] using this

theorem mem_of_inLNK (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true) {t : Array ℕ}
    {x : Equiv.Perm (Fin n)} (hin : inLN n (eltsK n ps gs m) t = true) (ht : Rep n t x) :
    x ∈ grpN n gs := by
  rw [inLN, List.any_eq_true] at hin
  obtain ⟨u, hu, he⟩ := hin
  exact (mem_grpN_iffK hps h).2 ⟨u, hu, rep_of_eqA ht he⟩

theorem inLN_of_memK (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true) {t : Array ℕ}
    {x : Equiv.Perm (Fin n)} (hx : x ∈ grpN n gs) (ht : Rep n t x) :
    inLN n (eltsK n ps gs m) t = true := by
  obtain ⟨u, hu, hr⟩ := (mem_grpN_iffK hps h).1 hx
  rw [inLN, List.any_eq_true]
  exact ⟨u, hu, (eqA_iff ht hr).2 rfl⟩

theorem exists_rep_of_memK (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true)
    {x : Equiv.Perm (Fin n)} (hx : x ∈ grpN n gs) :
    ∃ t ∈ eltsK n ps gs m, Rep n t x ∧ validA n t = true := by
  obtain ⟨t, ht, hr⟩ := (mem_grpN_iffK hps h).1 hx
  exact ⟨t, ht, hr, validA_of_mem_eltsK hps h ht⟩

theorem perm_mem_of_mem_eltsK (hps : ∀ p ∈ ps, p < n) (h : enumCheckK n ps gs m = true)
    {t : Array ℕ} (ht : t ∈ eltsK n ps gs m) : permOfArr n t ∈ grpN n gs :=
  (mem_grpN_iffK hps h).2 ⟨t, ht, rep_of_validA (validA_of_mem_eltsK hps h ht)⟩

theorem grpN_le_of_allK (hps : ∀ p ∈ ps, p < n) (hg : enumCheckK n ps gs m = true)
    {gs' : List (Array ℕ)} (hv : ∀ a ∈ gs', validA n a = true)
    (hall : gs'.all (inLN n (eltsK n ps gs m)) = true) : grpN n gs' ≤ grpN n gs :=
  grpN_le fun a ha => mem_of_inLNK hps hg (List.all_eq_true.1 hall a ha) (rep_of_validA (hv a ha))

theorem card_setIP_of_uniqENK (hps : ∀ p ∈ ps, p < n) {es fs : List (Array ℕ)} {mE mF : ℕ}
    (hX : enumCheckK n ps gs m = true) (hE : enumCheckK n ps es mE = true)
    (hF : enumCheckK n ps fs mF = true)
    (h : uniqEN n (eltsK n ps gs m) (eltsK n ps es mE) (eltsK n ps fs mF) = true) :
    ∀ x ∈ grpN n gs, x * x = 1 → x ≠ 1 → x ∉ grpN n es → x ∉ grpN n fs →
      Nat.card (setIP (grpN n gs) x) < 64 := by
  intro x hx hx2 hx1 hxE hxF
  obtain ⟨t, ht, hrt⟩ := (mem_grpN_iffK hps hX).1 hx
  have hb := List.all_eq_true.1 h t ht
  simp only [Bool.or_eq_true] at hb
  have h1 : eqA n (mulN n t t) (idA n) = true := (eqA_iff (rep_mulN hrt hrt) rep_idA).2 hx2
  have h2 : eqA n t (idA n) = false := by
    by_contra hc
    exact hx1 (eq_of_eqA hrt rep_idA (by simpa using hc))
  have h3 : inLN n (eltsK n ps es mE) t = false := by
    by_contra hc
    exact hxE (mem_of_inLNK hps hE (by simpa using hc) hrt)
  have h4 : inLN n (eltsK n ps fs mF) t = false := by
    by_contra hc
    exact hxF (mem_of_inLNK hps hF (by simpa using hc) hrt)
  rw [h1, h2, h3, h4] at hb
  simp only [Bool.not_true, Bool.false_eq_true, false_or, decide_eq_true_eq] at hb
  have hS : ∀ y ∈ setIP (grpN n gs) x, ∃ u ∈ (eltsK n ps gs m).filter
      (fun y => eqA n (mulN n y y) (idA n) && commN n t y), Rep n u y := by
    rintro y ⟨hyX, hy2, hyc⟩
    obtain ⟨u, hu, hru⟩ := (mem_grpN_iffK hps hX).1 hyX
    refine ⟨u, List.mem_filter.2 ⟨hu, ?_⟩, hru⟩
    rw [Bool.and_eq_true]
    exact ⟨(eqA_iff (rep_mulN hru hru) rep_idA).2 hy2, (commN_iff hrt hru).2 hyc⟩
  exact lt_of_le_of_lt (card_le_length hS) hb

end Enum

section Norm

variable {n : ℕ} {ps : List ℕ} {fs : List (Array ℕ)} {mf : ℕ}

theorem mem_normalizer_of_gens {w : Equiv.Perm (Fin n)}
    (hw : ∀ a ∈ fs, w * permOfArr n a * w⁻¹ ∈ grpN n fs) :
    w ∈ normalizer (grpN n fs : Set (Equiv.Perm (Fin n))) := by
  refine mem_normalizer_of_map_conj_le' ?_
  rw [grpN, MonoidHom.map_closure, closure_le]
  rintro _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hq : fs.toArray[k]! ∈ fs := by
    rw [getElem!_pos fs.toArray k hk]
    simp
  have h1 := hw _ hq
  rw [grpN] at h1
  simpa [MulAut.conj_apply] using h1

theorem mem_normalizer_of_normsN (hps : ∀ p ∈ ps, p < n) (hf : enumCheckK n ps fs mf = true)
    {a : Array ℕ} (ha : validA n a = true) (hn : normsN n (eltsK n ps fs mf) fs a = true) :
    permOfArr n a ∈ normalizer (grpN n fs : Set (Equiv.Perm (Fin n))) := by
  refine mem_normalizer_of_gens fun f hf' => ?_
  have hin := List.all_eq_true.1 hn f hf'
  exact mem_of_inLNK hps hf hin (rep_conjA ha (rep_of_validA (validA_of_mem_gensK hf hf')))

theorem normsN_of_mem_normalizer (hps : ∀ p ∈ ps, p < n) (hf : enumCheckK n ps fs mf = true)
    {a : Array ℕ} {w : Equiv.Perm (Fin n)} (ha : validA n a = true) (hr : Rep n a w)
    (hw : w ∈ normalizer (grpN n fs : Set (Equiv.Perm (Fin n)))) :
    normsN n (eltsK n ps fs mf) fs a = true := by
  refine List.all_eq_true.2 fun f hf' => ?_
  have hvf := validA_of_mem_gensK hf hf'
  have hrc := rep_conjA ha (rep_of_validA hvf)
  rw [permOfArr_eq_of_rep hr] at hrc
  exact inLN_of_memK hps hf ((mem_normalizer_iff.mp hw _).mp (gen_mem_grpN hf')) hrc

theorem comm_of_allK {gs : List (Array ℕ)} {m : ℕ} (hg : enumCheckK n ps gs m = true)
    (hc : gs.all (fun a => gs.all (commN n a)) = true) :
    ∀ x ∈ grpN n gs, ∀ y ∈ grpN n gs, x * y = y * x := by
  have hmem : ∀ k < gs.toArray.size, gs.toArray[k]! ∈ gs := fun k hk => by
    rw [getElem!_pos gs.toArray k hk]
    simp
  have hle : grpN n gs ≤ centralizer (grpN n gs : Set (Equiv.Perm (Fin n))) := by
    rw [grpN, centralizer_closure]
    refine (closure_le _).mpr ?_
    rintro _ ⟨k, hk, rfl⟩
    rw [SetLike.mem_coe, mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have hcm := List.all_eq_true.1 (List.all_eq_true.1 hc _ (hmem l hl)) _ (hmem k hk)
    exact (commN_iff (rep_of_validA (validA_of_mem_gensK hg (hmem l hl)))
      (rep_of_validA (validA_of_mem_gensK hg (hmem k hk)))).1 hcm
  intro x hx y hy
  exact mem_centralizer_iff.mp (hle hy) x hx

end Norm

theorem le_or_le_of_subset_union {G : Type*} [Group G] {X A B : Subgroup G}
    (h : ∀ x ∈ X, x ∈ A ∨ x ∈ B) : X ≤ A ∨ X ≤ B := by
  by_contra hc
  push Not at hc
  obtain ⟨⟨a, haX, haA⟩, ⟨b, hbX, hbB⟩⟩ := And.intro (Set.not_subset.1 hc.1)
    (Set.not_subset.1 hc.2)
  have haB : a ∈ B := (h a haX).resolve_left haA
  have hbA : b ∈ A := (h b hbX).resolve_right hbB
  rcases h (a * b) (X.mul_mem haX hbX) with hab | hab
  · exact haA (by simpa using A.mul_mem hab (A.inv_mem hbA))
  · exact hbB (by simpa using B.mul_mem (B.inv_mem haB) hab)

theorem eq_or_eq_of_setIP {n : ℕ} {gs es fs : List (Array ℕ)}
    (hcard : ∀ x ∈ grpN n gs, x * x = 1 → x ≠ 1 → x ∉ grpN n es → x ∉ grpN n fs →
      Nat.card (setIP (grpN n gs) x) < 64)
    (hE : Nat.card (grpN n es) = 64) (hF : Nat.card (grpN n fs) = 64)
    (X : Subgroup (Equiv.Perm (Fin n))) (hX : X ≤ grpN n gs) (hsq : ∀ x ∈ X, x * x = 1)
    (h64 : Nat.card X = 64) : X = grpN n es ∨ X = grpN n fs := by
  have hsub : ∀ x ∈ X, x ∈ grpN n es ∨ x ∈ grpN n fs := by
    intro x hx
    by_contra hc
    push Not at hc
    have hx1 : x ≠ 1 := fun h1 => hc.1 (h1 ▸ one_mem _)
    have hlt := hcard x (hX hx) (hsq x hx) hx1 hc.1 hc.2
    have hle : Nat.card X ≤ Nat.card (setIP (grpN n gs) x) := by
      refine Nat.card_le_card_of_injective (fun y : X => (⟨y, hX y.2, hsq y y.2,
        comm_of_sq hsq hx y.2⟩ : setIP (grpN n gs) x)) fun a b hab => ?_
      have := congrArg Subtype.val hab
      exact Subtype.ext this
    omega
  rcases le_or_le_of_subset_union hsub with hle | hle
  · exact Or.inl (Subgroup.eq_of_le_of_card_ge hle (by rw [hE, h64]))
  · exact Or.inr (Subgroup.eq_of_le_of_card_ge hle (by rw [hF, h64]))

theorem heModelCheck_parts (h : heModelCheck = true) :
    heCheckEnum = true ∧ heCheckZeta = true ∧ heCheckOrbit = true ∧ heCheckB0 = true ∧
      heCheckP23 = true ∧ heCheckC = true ∧ heCheckCount = true := by
  simp only [heModelCheck, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem base64_lt : ∀ p ∈ base64, p < 64 := by decide

theorem base32_lt : ∀ p ∈ base32, p < 32 := by decide

theorem heTL_eq : heTL = eltsK 64 base64 hexaTGens 64 := rfl
theorem heML_eq : heML = eltsK 64 base64 hexaMGens 2160 := rfl
theorem heP12L_eq : heP12L = eltsK 64 base64 heP12Gens 3072 := rfl
theorem heBL_eq : heBL = eltsK 64 base64 heB0Gens 1024 := rfl
theorem heFL_eq : heFL = eltsK 64 base64 heF0Gens 64 := rfl
theorem heCL_eq : heCL = eltsK 32 base32 hePCGens 21504 := rfl
theorem heBCL_eq : heBCL = eltsK 32 base32 heBCGens 1024 := rfl
theorem heP0L_eq : heP0L = eltsK 32 base32 heP12CGens 3072 := rfl
theorem heP1L_eq : heP1L = eltsK 32 base32 heP13CGens 3072 := rfl
theorem heU0L_eq : heU0L = eltsK 32 base32 heECGens 64 := rfl
theorem heU1L_eq : heU1L = eltsK 32 base32 heFCGens 64 := rfl

theorem heCheckEnum_parts (h : heCheckEnum = true) :
    enumCheckK 64 base64 hexaTGens 64 = true ∧ enumCheckK 64 base64 hexaMGens 2160 = true ∧
      enumCheckK 64 base64 heP12Gens 3072 = true ∧ enumCheckK 64 base64 heB0Gens 1024 = true ∧
      enumCheckK 64 base64 heF0Gens 64 = true ∧ enumCheckK 64 base64 heP23Gens 9216 = true ∧
      enumCheckK 32 base32 hePCGens 21504 = true ∧ enumCheckK 32 base32 heBCGens 1024 = true ∧
      enumCheckK 32 base32 heP12CGens 3072 = true ∧ enumCheckK 32 base32 heP13CGens 3072 = true ∧
      enumCheckK 32 base32 heECGens 64 = true ∧ enumCheckK 32 base32 heFCGens 64 = true ∧
      validA 64 heZetaArr = true ∧ validA 64 hexaT0 = true ∧ validA 32 heTCArr = true := by
  simp only [heCheckEnum, Bool.and_eq_true, and_assoc] at h
  exact h

section E

variable (h : heModelCheck = true)
include h

theorem hT : enumCheckK 64 base64 hexaTGens 64 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).1
theorem hM : enumCheckK 64 base64 hexaMGens 2160 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.1
theorem hP12 : enumCheckK 64 base64 heP12Gens 3072 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.1
theorem hB : enumCheckK 64 base64 heB0Gens 1024 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.1
theorem hF0 : enumCheckK 64 base64 heF0Gens 64 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.1
theorem hP23 : enumCheckK 64 base64 heP23Gens 9216 = true :=
  (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.1
theorem rep_zeta : Rep 64 heZetaArr heZeta :=
  rep_of_validA (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.2.2.2.2.2.1
theorem rep_t0' : Rep 64 hexaT0 hexaT0P :=
  rep_of_validA (heCheckEnum_parts (heModelCheck_parts h).1).2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem heCheckZeta_parts :
    (eltsK 64 base64 hexaTGens 64).all (fun t => !(inLN 64 (eltsK 64 base64 hexaMGens 2160) t) ||
        eqA 64 t (idA 64)) = true ∧
      inLN 64 (eltsK 64 base64 hexaMGens 2160) heZetaArr = true ∧
      eqA 64 (powN 64 heZetaArr 3) (idA 64) = true ∧ (!(eqA 64 heZetaArr (idA 64))) = true ∧
      (eltsK 64 base64 hexaTGens 64).all (fun t => !(commN 64 heZetaArr t) ||
        eqA 64 t (idA 64)) = true ∧
      (eltsK 64 base64 hexaMGens 2160).all (fun m => eqA 64 (conjA 64 m heZetaArr) heZetaArr ||
        eqA 64 (conjA 64 m heZetaArr) (powN 64 heZetaArr 2)) = true := by
  have h2 := (heModelCheck_parts h).2.1
  simp only [heCheckZeta, heTL_eq, heML_eq, Bool.and_eq_true, and_assoc] at h2
  exact h2

theorem T_inf_M_of : hexaT ⊓ hexaM = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxT, hxM⟩
  obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_memK base64_lt (hT h) hxT
  have hb := List.all_eq_true.1 (heCheckZeta_parts h).1 t ht
  rw [inLN_of_memK base64_lt (hM h) hxM hrt] at hb
  simp only [Bool.not_true, Bool.false_or] at hb
  exact mem_bot.2 (eq_of_eqA hrt rep_idA hb)

theorem zeta_mem_of : heZeta ∈ hexaM :=
  mem_of_inLNK base64_lt (hM h) (heCheckZeta_parts h).2.1 (rep_zeta h)

theorem zeta_pow_of : heZeta ^ 3 = 1 :=
  eq_of_eqA (rep_powN (rep_zeta h) 3) rep_idA (heCheckZeta_parts h).2.2.1

theorem zeta_ne_of : heZeta ≠ 1 := by
  intro he
  have hb := (heCheckZeta_parts h).2.2.2.1
  rw [(eqA_iff (rep_zeta h) rep_idA).2 he] at hb
  exact absurd hb (by decide)

theorem zeta_fix_of : ∀ t ∈ hexaT, heZeta * t * heZeta⁻¹ = t → t = 1 := by
  intro t ht hc
  obtain ⟨a, ha, hra, -⟩ := exists_rep_of_memK base64_lt (hT h) ht
  have hb := List.all_eq_true.1 (heCheckZeta_parts h).2.2.2.2.1 a ha
  have hcomm : heZeta * t = t * heZeta := by
    calc heZeta * t = heZeta * t * heZeta⁻¹ * heZeta := by group
      _ = t * heZeta := by rw [hc]
  rw [(commN_iff (rep_zeta h) hra).2 hcomm] at hb
  simp only [Bool.not_true, Bool.false_or] at hb
  exact eq_of_eqA hra rep_idA hb

theorem zeta_normal_of :
    ∀ m ∈ hexaM, m * heZeta * m⁻¹ = heZeta ∨ m * heZeta * m⁻¹ = heZeta⁻¹ := by
  intro m hm
  obtain ⟨a, ha, hra, hva⟩ := exists_rep_of_memK base64_lt (hM h) hm
  have hb := List.all_eq_true.1 (heCheckZeta_parts h).2.2.2.2.2 a ha
  rw [Bool.or_eq_true] at hb
  have hrc := rep_conjA hva (rep_zeta h)
  rw [permOfArr_eq_of_rep hra] at hrc
  have hz2 : heZeta ^ 2 = heZeta⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← pow_succ, zeta_pow_of h]
  rcases hb with hb | hb
  · exact Or.inl (eq_of_eqA hrc (rep_zeta h) hb)
  · exact Or.inr ((eq_of_eqA hrc (rep_powN (rep_zeta h) 2) hb).trans hz2)

theorem orbit_of' : ∀ t ∈ hexaT, t ≠ 1 → (∃ m ∈ hexaM, m * t * m⁻¹ = hexaT0P) ∨
    ∃ m ∈ hexaM, m * t = t * m ∧ orderOf m = 5 := by
  intro t ht ht1
  obtain ⟨a, ha, hra, -⟩ := exists_rep_of_memK base64_lt (hT h) ht
  have hob := (heModelCheck_parts h).2.2.1
  rw [heCheckOrbit, heTL_eq, heML_eq] at hob
  have hb := List.all_eq_true.1 hob a ha
  simp only [Bool.or_eq_true] at hb
  rcases hb with (hb | hb) | hb
  · exact absurd (eq_of_eqA hra rep_idA hb) ht1
  · obtain ⟨m', hm', he⟩ := List.any_eq_true.1 hb
    have hvm := validA_of_mem_eltsK base64_lt (hM h) hm'
    refine Or.inl ⟨permOfArr 64 m', perm_mem_of_mem_eltsK base64_lt (hM h) hm', ?_⟩
    exact eq_of_eqA (rep_conjA hvm hra) (rep_t0' h) he
  · obtain ⟨m', hm', he⟩ := List.any_eq_true.1 hb
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at he
    obtain ⟨⟨hc, h5⟩, h1⟩ := he
    have hvm := validA_of_mem_eltsK base64_lt (hM h) hm'
    have hrm := rep_of_validA hvm
    refine Or.inr ⟨permOfArr 64 m', perm_mem_of_mem_eltsK base64_lt (hM h) hm',
      (commN_iff hrm hra).1 hc, orderOf_eq_prime (eq_of_eqA (rep_powN hrm 5) rep_idA h5) ?_⟩
    intro he1
    rw [(eqA_iff hrm rep_idA).2 he1] at h1
    exact absurd h1 (by decide)

theorem heCheckB0_parts :
    hexaTGens.all (fun a => hexaTGens.all (commN 64 a)) = true ∧
      inLN 64 (eltsK 64 base64 hexaTGens 64) hexaT0 = true ∧
      hexaCGens.all (inLN 64 (eltsK 64 base64 hexaMGens 2160)) = true ∧
      hexaCGens.all (fun g => commN 64 g hexaT0) = true ∧
      heB0Gens.all (inLN 64 (eltsK 64 base64 heP12Gens 3072)) = true ∧
      hexaTGens.all (inLN 64 (eltsK 64 base64 heB0Gens 1024)) = true ∧
      heF0Gens.all (inLN 64 (eltsK 64 base64 heB0Gens 1024)) = true ∧
      (eltsK 64 base64 heF0Gens 64).all (fun x => eqA 64 (mulN 64 x x) (idA 64)) = true ∧
      (eltsK 64 base64 heF0Gens 64).any (fun x => !(inLN 64 (eltsK 64 base64 hexaTGens 64) x)) =
        true ∧
      heB0Gens.all (normsN 64 (eltsK 64 base64 heF0Gens 64) heF0Gens) = true ∧
      uniqEN 64 (eltsK 64 base64 heB0Gens 1024) (eltsK 64 base64 hexaTGens 64)
        (eltsK 64 base64 heF0Gens 64) = true := by
  have h2 := (heModelCheck_parts h).2.2.2.1
  simp only [heCheckB0, heTL_eq, heML_eq, heP12L_eq, heBL_eq, heFL_eq, Bool.and_eq_true,
    and_assoc] at h2
  exact h2

theorem heCheckP23_parts :
    heP23Gens.all inTMN = true ∧
      heP23Gens.all (normsN 64 (eltsK 64 base64 heF0Gens 64) heF0Gens) = true ∧
      heP23Gens.all (fun g => eqA 64 (powN 64 g 8) (idA 64)) = true ∧
      ((eltsK 64 base64 hexaMGens 2160).filter
        (normsN 64 (eltsK 64 base64 heF0Gens 64) heF0Gens)).length = 144 := by
  have h2 := (heModelCheck_parts h).2.2.2.2.1
  simp only [heCheckP23, heML_eq, heFL_eq, Bool.and_eq_true, beq_iff_eq, and_assoc] at h2
  exact h2

theorem T_comm : ∀ x ∈ hexaT, ∀ y ∈ hexaT, x * y = y * x :=
  comm_of_allK (hT h) (heCheckB0_parts h).1

theorem t0_mem_T : hexaT0P ∈ hexaT :=
  mem_of_inLNK base64_lt (hT h) (heCheckB0_parts h).2.1 (rep_t0' h)

theorem P12gens_le : grpN 64 heP12Gens ≤ heP12 := by
  refine grpN_le fun a ha => ?_
  have hva := validA_of_mem_gensK (hP12 h) ha
  rcases List.mem_append.1 ha with haT | haC
  · have hmem : permOfArr 64 a ∈ hexaT := gen_mem_grpN haT
    exact ⟨mem_sup_left hmem, mem_centralizer_singleton_iff.mpr
      (T_comm h _ hmem _ (t0_mem_T h))⟩
  · have hmem : permOfArr 64 a ∈ hexaM := mem_of_inLNK base64_lt (hM h)
      (List.all_eq_true.1 (heCheckB0_parts h).2.2.1 a haC) (rep_of_validA hva)
    exact ⟨mem_sup_right hmem, mem_centralizer_singleton_iff.mpr ((commN_iff
      (rep_of_validA hva) (rep_t0' h)).1 (List.all_eq_true.1 (heCheckB0_parts h).2.2.2.1 a haC))⟩

variable (hF : HexaFacts)
include hF

omit h in
theorem exists_mul_of_mem_N0 {x : Equiv.Perm (Fin 64)} (hx : x ∈ heN0) :
    ∃ t ∈ hexaT, ∃ m ∈ hexaM, t * m = x := by
  have hx' : x ∈ ((hexaT ⊔ hexaM : Subgroup _) : Set (Equiv.Perm (Fin 64))) := hx
  rw [coe_mul_of_right_le_normalizer_left hexaT hexaM hF.normT] at hx'
  obtain ⟨t, ht, m, hm, rfl⟩ := hx'
  exact ⟨t, ht, m, hm, rfl⟩

omit h in
theorem mem_C0 : ∀ y ∈ hexaC0, y ∈ hexaM ∧ y * hexaT0P = hexaT0P * y := fun y hy => by
  rw [← hF.cent] at hy
  exact ⟨hy.1, mem_centralizer_singleton_iff.mp hy.2⟩

omit h in
theorem card_C0 : Nat.card hexaC0 = 48 := by
  obtain ⟨e⟩ := hF.iso
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm,
    Nat.card_eq_fintype_card (α := Multiplicative (ZMod 2))]
  simp [Nat.factorial]

theorem P12_eq : heP12 = grpN 64 heP12Gens := by
  symm
  refine Subgroup.eq_of_le_of_card_ge (P12gens_le h) ?_
  rw [card_grpNK base64_lt (hP12 h)]
  have hsurj : Function.Surjective (fun p : ↥hexaT × ↥hexaC0 =>
      (⟨(p.1 : Equiv.Perm (Fin 64)) * p.2, mul_mem (mem_sup_left p.1.2)
        (mem_sup_right (mem_C0 hF _ p.2.2).1),
        mem_centralizer_singleton_iff.mpr (by
          have h1 := T_comm h _ p.1.2 _ (t0_mem_T h)
          have h2 := (mem_C0 hF _ p.2.2).2
          calc (p.1 : Equiv.Perm (Fin 64)) * p.2 * hexaT0P = p.1 * (p.2 * hexaT0P) := by group
            _ = p.1 * (hexaT0P * p.2) := by rw [h2]
            _ = p.1 * hexaT0P * p.2 := by group
            _ = hexaT0P * p.1 * p.2 := by rw [h1]
            _ = hexaT0P * (p.1 * p.2) := by group)⟩ : ↥heP12)) := by
    rintro ⟨x, hxN, hxc⟩
    obtain ⟨t, ht, m, hm, rfl⟩ := exists_mul_of_mem_N0 hF hxN
    have hmc : m ∈ hexaC0 := by
      rw [← hF.cent]
      refine ⟨hm, mem_centralizer_singleton_iff.mpr ?_⟩
      have h1 := T_comm h _ ht _ (t0_mem_T h)
      have h2 := mem_centralizer_singleton_iff.mp hxc
      have : t * (m * hexaT0P) = t * (hexaT0P * m) := by
        calc t * (m * hexaT0P) = t * m * hexaT0P := by group
          _ = hexaT0P * (t * m) := h2
          _ = hexaT0P * t * m := by group
          _ = t * hexaT0P * m := by rw [h1]
          _ = t * (hexaT0P * m) := by group
      exact mul_left_cancel this
    exact ⟨(⟨t, ht⟩, ⟨m, hmc⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, card_grpNK base64_lt (hT h), card_C0 hF] at this
  exact this

theorem card_P12_of : Nat.card heP12 = 3072 := by
  rw [P12_eq h hF, card_grpNK base64_lt (hP12 h)]

theorem B0_le_of : heB0 ≤ heP12 := by
  rw [P12_eq h hF]
  exact grpN_le_of_allK base64_lt (hP12 h) (fun _ ha => validA_of_mem_gensK (hB h) ha)
    (heCheckB0_parts h).2.2.2.2.1

omit hF in
theorem T_le_B0_of : hexaT ≤ heB0 :=
  grpN_le_of_allK base64_lt (hB h) (fun _ ha => validA_of_mem_gensK (hT h) ha)
    (heCheckB0_parts h).2.2.2.2.2.1

omit hF in
theorem F0_le_B0_of : heF0 ≤ heB0 :=
  grpN_le_of_allK base64_lt (hB h) (fun _ ha => validA_of_mem_gensK (hF0 h) ha)
    (heCheckB0_parts h).2.2.2.2.2.2.1

omit hF in
theorem F0_sq_of : ∀ x ∈ heF0, x * x = 1 := by
  intro x hx
  obtain ⟨t, ht, hrt, -⟩ := exists_rep_of_memK base64_lt (hF0 h) hx
  exact eq_of_eqA (rep_mulN hrt hrt) rep_idA
    (List.all_eq_true.1 (heCheckB0_parts h).2.2.2.2.2.2.2.1 t ht)

omit hF in
theorem F0_ne_of : heF0 ≠ hexaT := by
  intro he
  obtain ⟨a, ha, hn⟩ := List.any_eq_true.1 (heCheckB0_parts h).2.2.2.2.2.2.2.2.1
  have hmem : permOfArr 64 a ∈ heF0 := perm_mem_of_mem_eltsK base64_lt (hF0 h) ha
  rw [he] at hmem
  have := inLN_of_memK base64_lt (hT h) hmem
    (rep_of_validA (validA_of_mem_eltsK base64_lt (hF0 h) ha))
  rw [this] at hn
  exact absurd hn (by decide)

omit hF in
theorem B0_le_normalizer_F0 : heB0 ≤ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) :=
  grpN_le fun a ha => mem_normalizer_of_normsN base64_lt (hF0 h) (validA_of_mem_gensK (hB h) ha)
    (List.all_eq_true.1 (heCheckB0_parts h).2.2.2.2.2.2.2.2.2.1 a ha)

omit hF in
theorem normal_B0_of : ∀ X : Subgroup (Equiv.Perm (Fin 64)), X ≤ heB0 →
    (∀ b ∈ heB0, ∀ x ∈ X, b * x * b⁻¹ ∈ X) → (∀ x ∈ X, x * x = 1) → Nat.card X = 64 →
      X = hexaT ∨ X = heF0 := fun X hX _ hsq h64 =>
  eq_or_eq_of_setIP (card_setIP_of_uniqENK base64_lt (hB h) (hT h) (hF0 h)
    (heCheckB0_parts h).2.2.2.2.2.2.2.2.2.2) (card_grpNK base64_lt (hT h))
    (card_grpNK base64_lt (hF0 h)) X hX hsq h64

omit hF in
theorem P23_le : heP23 ≤ heN0 ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) := by
  refine grpN_le fun a ha => ⟨?_, ?_⟩
  · have hb := List.all_eq_true.1 (heCheckP23_parts h).1 a ha
    rw [inTMN, heTL_eq, heML_eq] at hb
    obtain ⟨t, ht, hm⟩ := List.any_eq_true.1 hb
    have hvt := validA_of_mem_eltsK base64_lt (hT h) ht
    have hva := validA_of_mem_gensK (hP23 h) ha
    have hrm := rep_compA (rep_inv_of_validA hvt) (rep_of_validA hva)
    have hmM := mem_of_inLNK base64_lt (hM h) hm hrm
    have htT := perm_mem_of_mem_eltsK base64_lt (hT h) ht
    have := mul_mem (mem_sup_left htT : permOfArr 64 t ∈ heN0) (mem_sup_right hmM)
    simpa using this
  · exact mem_normalizer_of_normsN base64_lt (hF0 h) (validA_of_mem_gensK (hP23 h) ha)
      (List.all_eq_true.1 (heCheckP23_parts h).2.1 a ha)

omit hF in
theorem card_M_normalizer_le :
    Nat.card ↥(hexaM ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64)))) ≤ 144 := by
  rw [← (heCheckP23_parts h).2.2.2]
  refine card_le_length (S := ((hexaM ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) :
    Subgroup _) : Set (Equiv.Perm (Fin 64)))) ?_
  rintro x ⟨hxM, hxN⟩
  obtain ⟨t, ht, hr, hv⟩ := exists_rep_of_memK base64_lt (hM h) hxM
  exact ⟨t, List.mem_filter.2 ⟨ht, normsN_of_mem_normalizer base64_lt (hF0 h) hv hr hxN⟩, hr⟩

theorem P23_eq_of : heP23 = heN0 ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) := by
  refine Subgroup.eq_of_le_of_card_ge (P23_le h) ?_
  rw [card_grpNK base64_lt (hP23 h)]
  have hTN : hexaT ≤ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) :=
    (T_le_B0_of h).trans (B0_le_normalizer_F0 h)
  have hsurj : Function.Surjective (fun p : ↥hexaT ×
      ↥(hexaM ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64)))) =>
      (⟨(p.1 : Equiv.Perm (Fin 64)) * p.2, mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2.1),
        mul_mem (hTN p.1.2) p.2.2.2⟩ :
        ↥(heN0 ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64)))))) := by
    rintro ⟨x, hxN, hxn⟩
    obtain ⟨t, ht, m, hm, rfl⟩ := exists_mul_of_mem_N0 hF hxN
    have hmn : m ∈ normalizer (heF0 : Set (Equiv.Perm (Fin 64))) := by
      have := mul_mem (inv_mem (hTN ht)) hxn
      simpa using this
    exact ⟨(⟨t, ht⟩, ⟨m, hm, hmn⟩), rfl⟩
  have := Nat.card_le_card_of_surjective _ hsurj
  rw [Nat.card_prod, card_grpNK base64_lt (hT h)] at this
  calc Nat.card ↥(heN0 ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64))))
      ≤ 64 * Nat.card ↥(hexaM ⊓ normalizer (heF0 : Set (Equiv.Perm (Fin 64)))) := this
    _ ≤ 64 * 144 := Nat.mul_le_mul_left 64 (card_M_normalizer_le h)
    _ = 9216 := by norm_num

omit hF in
theorem P23_gens_of : ∀ a ∈ heP23Gens, ∃ k : ℕ, permOfArr 64 a ^ (2 ^ k) = 1 := by
  intro a ha
  refine ⟨3, ?_⟩
  exact eq_of_eqA (rep_powN (rep_of_validA (validA_of_mem_gensK (hP23 h) ha)) 8) rep_idA
    (List.all_eq_true.1 (heCheckP23_parts h).2.2.1 a ha)

end E

end CFSG.ComponentClassification.AS81.HeTri
