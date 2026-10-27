module

public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.A6FactsBasic

public section

namespace CFSG.QuasithinUnique.A6Facts

open Equiv

@[expose] def pslGens : List P10 := [A6Models.tAdd, A6Models.tSq, A6Models.tInv]

@[expose] def autGens : List P10 :=
  [A6Models.tAdd, A6Models.tSq, A6Models.tInv, A6Models.tMul, A6Models.tFrob]

@[expose] def p0Gens : List P10 :=
  [A6Models.perm10 [[0, 3, 9, 6], [4, 8, 5, 7]],
    A6Models.perm10 [[0, 5], [1, 2], [3, 8], [4, 9], [6, 7]],
    A6Models.perm10 [[0, 8, 3, 5, 9, 7, 6, 4]],
    A6Models.perm10 [[0, 5, 3, 7, 9, 4, 6, 8], [1, 2]]]

@[expose] def P0 : Subgroup P10 := Subgroup.closure {g | g ∈ p0Gens}

@[expose] def autRepsP : List P10 :=
  [1, A6Models.tMul, A6Models.tFrob, A6Models.tMul * A6Models.tFrob]

theorem pslGens_code : pslGens.map code = Core.pslGenC := by decide +kernel

theorem autGens_code : autGens.map code = Core.autGenC := by decide +kernel

theorem autGens_inv_code : (autGens.map (·⁻¹)).map code = Core.autGenInvC := by decide +kernel

theorem p0Gens_code : p0Gens.map code = Core.p0GenC := by decide +kernel

theorem autRepsP_code : autRepsP.map code = Core.autReps := by decide +kernel

theorem autRepsP_inv_code : (autRepsP.map (·⁻¹)).map code = Core.autRepsInv := by decide +kernel

theorem psl29_eq : A6Models.psl29 = Subgroup.closure {g | g ∈ pslGens} := by
  unfold A6Models.psl29 pslGens
  congr 1
  ext g
  simp

theorem autA6_eq : A6Models.autA6 = Subgroup.closure {g | g ∈ autGens} := by
  unfold A6Models.autA6 autGens
  congr 1
  ext g
  simp

theorem mem_psl29_iff (x : P10) : x ∈ A6Models.psl29 ↔ code x ∈ Core.pslLit := by
  rw [psl29_eq]
  have h := (mem_closure_iff_of_tbl (gens := pslGens) pslGens_code (tree := Core.pslTree)
    (T := Core.pslTbl) (by rw [← Core.psl_build]; exact Core.psl_tbl)).1 x
  rw [Core.psl_build]
  exact h

theorem exists_psl29_of_code {c : List ℕ} (hc : c ∈ Core.pslLit) : ∃ x ∈ A6Models.psl29, code x = c := by
  rw [psl29_eq]
  have h := (mem_closure_iff_of_tbl (gens := pslGens) pslGens_code (tree := Core.pslTree)
    (T := Core.pslTbl) (by rw [← Core.psl_build]; exact Core.psl_tbl)).2 c
    (by rw [← Core.psl_build]; exact hc)
  exact h

theorem card_psl29 : Nat.card A6Models.psl29 = 360 := by
  rw [psl29_eq, card_closure_eq_of_tbl (gens := pslGens) pslGens_code (tree := Core.pslTree)
    (T := Core.pslTbl) (by rw [← Core.psl_build]; exact Core.psl_tbl)
    (by rw [← Core.psl_build]; exact Core.psl_nodup), ← Core.psl_build]
  exact Core.psl_length

theorem mem_P0_iff (x : P10) : x ∈ P0 ↔ code x ∈ Core.p0Lit := by
  unfold P0
  have h := (mem_closure_iff_of_tbl (gens := p0Gens) p0Gens_code (tree := Core.p0Tree)
    (T := Core.p0Tbl) (by rw [← Core.p0_build]; exact Core.p0_tbl)).1 x
  rw [Core.p0_build]
  exact h

theorem card_P0 : Nat.card P0 = 32 := by
  unfold P0
  rw [card_closure_eq_of_tbl (gens := p0Gens) p0Gens_code (tree := Core.p0Tree)
    (T := Core.p0Tbl) (by rw [← Core.p0_build]; exact Core.p0_tbl)
    (by rw [← Core.p0_build]; exact Core.p0_nodup), ← Core.p0_build]
  exact Core.p0_length

theorem mem_closure_iff_of_cosets {gens reps : List P10} {N : Subgroup P10}
    (hN : N ≤ Subgroup.closure {g | g ∈ gens})
    (hreps : ∀ r ∈ reps, r ∈ Subgroup.closure {g | g ∈ gens}) (h1 : (1 : P10) ∈ reps)
    (hstep : ∀ r ∈ reps, ∀ g ∈ gens, ∃ r' ∈ reps, r * g * r'⁻¹ ∈ N) (x : P10) :
    x ∈ Subgroup.closure {g | g ∈ gens} ↔ ∃ r ∈ reps, x * r⁻¹ ∈ N := by
  constructor
  · intro hx
    have hsub : (Subgroup.closure {g | g ∈ gens}).toSubmonoid = Submonoid.closure {g | g ∈ gens} :=
      Subgroup.closure_toSubmonoid_of_finite
    have hx' : x ∈ Submonoid.closure {g | g ∈ gens} := by rw [← hsub]; exact hx
    refine Submonoid.closure_induction_right
      (motive := fun m _ => ∃ r ∈ reps, m * r⁻¹ ∈ N) ?_ ?_ hx'
    · exact ⟨1, h1, by simp⟩
    · intro m _ y hy ⟨r, hr, hmr⟩
      obtain ⟨r', hr', hrg⟩ := hstep r hr y hy
      refine ⟨r', hr', ?_⟩
      have : m * y * r'⁻¹ = (m * r⁻¹) * (r * y * r'⁻¹) := by group
      rw [this]
      exact N.mul_mem hmr hrg
  · rintro ⟨r, hr, hxr⟩
    have : x = (x * r⁻¹) * r := by group
    rw [this]
    exact Subgroup.mul_mem _ (hN hxr) (hreps r hr)

theorem autReps_mem_closure : ∀ r ∈ autRepsP, r ∈ Subgroup.closure {g | g ∈ autGens} := by
  intro r hr
  have hmem : ∀ g ∈ autGens, g ∈ Subgroup.closure {g | g ∈ autGens} :=
    fun g hg => Subgroup.subset_closure hg
  simp only [autRepsP, List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · exact Subgroup.one_mem _
  · exact hmem _ (by simp [autGens])
  · exact hmem _ (by simp [autGens])
  · exact Subgroup.mul_mem _ (hmem _ (by simp [autGens])) (hmem _ (by simp [autGens]))

theorem psl29_le_closure_autGens : A6Models.psl29 ≤ Subgroup.closure {g | g ∈ autGens} := by
  rw [psl29_eq, Subgroup.closure_le]
  intro g hg
  apply Subgroup.subset_closure
  have h1 : g = A6Models.tAdd ∨ g = A6Models.tSq ∨ g = A6Models.tInv := by
    simpa [pslGens] using (show g ∈ pslGens from hg)
  show g ∈ autGens
  simp only [autGens, List.mem_cons, List.not_mem_nil, or_false]
  rcases h1 with h | h | h <;> simp [h]

theorem mem_autA6_iff_exists (x : P10) :
    x ∈ A6Models.autA6 ↔ ∃ r ∈ autRepsP, x * r⁻¹ ∈ A6Models.psl29 := by
  rw [autA6_eq]
  refine mem_closure_iff_of_cosets psl29_le_closure_autGens autReps_mem_closure
    (by simp [autRepsP]) ?_ x
  intro r hr g hg
  have hcheck := Core.aut_cosets
  unfold Core.cosetCheck at hcheck
  rw [List.all_eq_true] at hcheck
  have h1 := hcheck (code r) (by rw [← autRepsP_code]; exact List.mem_map_of_mem hr)
  rw [List.all_eq_true] at h1
  have h2 := h1 (code g) (by rw [← autGens_code]; exact List.mem_map_of_mem hg)
  rw [List.any_eq_true] at h2
  obtain ⟨rinv, hrinv, hmem⟩ := h2
  rw [← autRepsP_inv_code] at hrinv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrinv
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hc
  refine ⟨r', hr', ?_⟩
  rw [mem_psl29_iff, code_mul, code_mul]
  simpa [List.contains_eq_any_beq] using hmem

theorem psl29_le_autA6 : A6Models.psl29 ≤ A6Models.autA6 := by
  rw [autA6_eq]; exact psl29_le_closure_autGens

theorem P0_le_autA6 : P0 ≤ A6Models.autA6 := by
  unfold P0
  rw [Subgroup.closure_le]
  intro g hg
  rw [SetLike.mem_coe, mem_autA6_iff_exists]
  have hcheck := Core.p0Gen_aut
  rw [List.all_eq_true] at hcheck
  have h1 := hcheck (code g) (by rw [← p0Gens_code]; exact List.mem_map_of_mem hg)
  rw [List.any_eq_true] at h1
  obtain ⟨rinv, hrinv, hmem⟩ := h1
  rw [← autRepsP_inv_code] at hrinv
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrinv
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  refine ⟨r, hr, ?_⟩
  rw [mem_psl29_iff, code_mul]
  simpa [List.contains_eq_any_beq] using hmem

theorem code_mem_autL {x : P10} (hx : x ∈ A6Models.autA6) : code x ∈ Core.autL := by
  obtain ⟨r, hr, hxr⟩ := (mem_autA6_iff_exists x).1 hx
  have hy := (mem_psl29_iff _).1 hxr
  unfold Core.autL
  rw [List.mem_flatMap]
  refine ⟨code (x * r⁻¹), hy, ?_⟩
  rw [List.mem_map]
  refine ⟨code r, by rw [← autRepsP_code]; exact List.mem_map_of_mem hr, ?_⟩
  rw [← code_mul]
  congr 1
  group

theorem card_autA6 : Nat.card A6Models.autA6 = 1440 := by
  have h1 : Nat.card A6Models.autA6 ≤ 1440 := by
    have himg : code '' (A6Models.autA6 : Set P10) ⊆ ↑Core.autL.toFinset := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using code_mem_autL hx
    calc Nat.card A6Models.autA6 = Nat.card (code '' (A6Models.autA6 : Set P10)) :=
          (Nat.card_image_of_injective code_injective _).symm
      _ ≤ Nat.card ↥(↑Core.autL.toFinset : Set (List ℕ)) :=
          Nat.card_mono (Set.toFinite _) himg
      _ = Core.autL.toFinset.card := by rw [Nat.card_coe_set_eq, Set.ncard_coe_finset]
      _ ≤ Core.autL.length := List.toFinset_card_le _
      _ = 1440 := by decide +kernel
  have h2 : 360 ∣ Nat.card A6Models.autA6 := by
    rw [← card_psl29]; exact Subgroup.card_dvd_of_le psl29_le_autA6
  have h3 : 32 ∣ Nat.card A6Models.autA6 := by
    rw [← card_P0]; exact Subgroup.card_dvd_of_le P0_le_autA6
  have h4 : 0 < Nat.card A6Models.autA6 := Nat.card_pos
  omega

theorem gens_conj : autGens.all (fun y => pslGens.all (fun x =>
    Core.pslLit.contains (code (y * x * y⁻¹)))) = true := by
  decide +kernel

theorem conj_mem_psl29_of_gen {y : P10} (hy : y ∈ autGens) :
    ∀ x ∈ A6Models.psl29, y * x * y⁻¹ ∈ A6Models.psl29 := by
  have h := gens_conj
  rw [List.all_eq_true] at h
  have h1 := h y hy
  rw [List.all_eq_true] at h1
  have hx : Subgroup.closure {g | g ∈ pslGens} ≤
      A6Models.psl29.comap (MulAut.conj y).toMonoidHom := by
    rw [Subgroup.closure_le]
    intro x hx
    have := h1 x hx
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    show y * x * y⁻¹ ∈ A6Models.psl29
    rw [mem_psl29_iff]
    simpa [List.contains_eq_any_beq] using this
  rw [← psl29_eq] at hx
  intro x hxp
  simpa [MulAut.conj_apply] using hx hxp

theorem psl29_normal : ∀ g ∈ A6Models.autA6, ∀ x ∈ A6Models.psl29, g * x * g⁻¹ ∈ A6Models.psl29 := by
  intro g hg
  rw [autA6_eq] at hg
  have hsub : (Subgroup.closure {g | g ∈ autGens}).toSubmonoid = Submonoid.closure {g | g ∈ autGens} :=
    Subgroup.closure_toSubmonoid_of_finite
  have hg' : g ∈ Submonoid.closure {g | g ∈ autGens} := by rw [← hsub]; exact hg
  refine Submonoid.closure_induction_right
    (motive := fun m _ => ∀ x ∈ A6Models.psl29, m * x * m⁻¹ ∈ A6Models.psl29) ?_ ?_ hg'
  · intro x hx; simpa using hx
  · intro m _ y hy ih x hx
    have h1 := conj_mem_psl29_of_gen hy x hx
    have h2 := ih _ h1
    have : m * y * x * (m * y)⁻¹ = m * (y * x * y⁻¹) * m⁻¹ := by group
    rw [this]
    exact h2

theorem centralizer_psl29 {g : P10} (hg : g ∈ A6Models.autA6)
    (h : ∀ x ∈ A6Models.psl29, g * x = x * g) : g = 1 := by
  have hc := Core.cent_psl
  rw [List.all_eq_true] at hc
  have h1 := hc (code g) (code_mem_autL hg)
  have hcomm : (Core.pslGenC.all fun x => Core.cmul (code g) x == Core.cmul x (code g)) = true := by
    rw [List.all_eq_true]
    intro x hx
    rw [← pslGens_code] at hx
    obtain ⟨x', hx', rfl⟩ := List.mem_map.mp hx
    have hxp : x' ∈ A6Models.psl29 := by
      rw [psl29_eq]; exact Subgroup.subset_closure hx'
    have := h x' hxp
    simp only [beq_iff_eq]
    rw [← code_mul, ← code_mul, this]
  rw [hcomm] at h1
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  apply code_injective
  rw [h1, code_one]

theorem code_pow (x : P10) (n : ℕ) : code (x ^ n) = Core.cpow (code x) n := by
  induction n with
  | zero =>
    rw [pow_zero, code_one, Core.cpow, code_length]
    rfl
  | succ n ih => rw [pow_succ, code_mul, ih, Core.cpow]

theorem exists_P0_of_code {c : List ℕ} (hc : c ∈ Core.p0Lit) : ∃ x ∈ P0, code x = c := by
  unfold P0
  have h := (mem_closure_iff_of_tbl (gens := p0Gens) p0Gens_code (tree := Core.p0Tree)
    (T := Core.p0Tbl) (by rw [← Core.p0_build]; exact Core.p0_tbl)).2 c (by rw [← Core.p0_build]; exact hc)
  exact h

theorem P0_pow_eight {x : P10} (hx : x ∈ P0) : x ^ 8 = 1 := by
  rw [mem_P0_iff] at hx
  have h := Core.p0_exp8
  rw [List.all_eq_true] at h
  have h1 := h _ hx
  simp only [beq_iff_eq] at h1
  apply code_injective
  rw [code_pow, h1, code_one]

theorem P0_not_Q16 {a b : P10} (ha : a ∈ P0) (hb : b ∈ P0) (h4 : a ^ 4 ≠ 1) (hb2 : b * b = a ^ 4)
    (hab : a * b * a = b) : False := by
  rw [mem_P0_iff] at ha hb
  have h := Core.p0_noQ16
  rw [List.all_eq_true] at h
  have h1 := h _ ha
  rw [List.all_eq_true] at h1
  have h2 := h1 _ hb
  have e1 : (Core.cpow (code a) 4 != Core.cid) = true := by
    rw [bne_iff_ne, ← code_pow, ← code_one]
    intro hc
    exact h4 (code_injective hc)
  have e2 : (Core.cmul (code b) (code b) == Core.cpow (code a) 4) = true := by
    rw [beq_iff_eq, ← code_pow, ← code_mul, hb2]
  have e3 : (Core.cmul (Core.cmul (code a) (code b)) (code a) == code b) = true := by
    rw [beq_iff_eq, ← code_mul, ← code_mul, hab]
  simp only [e1, e2, e3, Bool.and_self, Bool.not_true] at h2
  exact absurd h2 (by simp)

theorem code_mem_dLit {d : P10} (hd : d ∈ P0) (hd' : d ∈ A6Models.psl29) : code d ∈ Core.dLit := by
  rw [Core.d_eq]
  rw [List.mem_filter]
  exact ⟨(mem_P0_iff d).1 hd, by simpa using (mem_psl29_iff d).1 hd'⟩

theorem P0_sq_of_centralizes_D {c : P10} (hc : c ∈ P0)
    (h : ∀ d ∈ P0, d ∈ A6Models.psl29 → c * d = d * c) : c * c = 1 := by
  have hall := Core.p0_cent_d
  rw [List.all_eq_true] at hall
  have h1 := hall (code c) ((mem_P0_iff c).1 hc)
  have hd : (Core.dLit.all fun d => Core.cmul (code c) d == Core.cmul d (code c)) = true := by
    rw [List.all_eq_true]
    intro d hd
    rw [Core.d_eq, List.mem_filter] at hd
    obtain ⟨hd0, hd1⟩ := hd
    obtain ⟨d', hd'0, rfl⟩ := exists_P0_of_code hd0
    have hd'1 : d' ∈ A6Models.psl29 := by
      rw [mem_psl29_iff]; simpa using hd1
    have := h d' hd'0 hd'1
    rw [beq_iff_eq, ← code_mul, ← code_mul, this]
  rw [hd] at h1
  simp only [Bool.not_true, Bool.false_or, beq_iff_eq] at h1
  apply code_injective
  rw [code_mul, h1, code_one]

@[expose] def s6Gens : List P10 := [A6Models.tAdd, A6Models.tSq, A6Models.tInv, A6Models.tFrob]

@[expose] def s6 : Subgroup P10 := Subgroup.closure {g | g ∈ s6Gens}

@[expose] def s6RepsP : List P10 := [1, A6Models.tFrob]

theorem s6Gens_code : s6Gens.map code = Core.s6GenC := by decide +kernel

theorem s6RepsP_code : s6RepsP.map code = Core.s6Reps := by decide +kernel

theorem s6RepsP_inv_code : (s6RepsP.map (·⁻¹)).map code = Core.s6RepsInv := by decide +kernel

theorem psl29_le_s6 : A6Models.psl29 ≤ s6 := by
  rw [psl29_eq, Subgroup.closure_le]
  intro g hg
  apply Subgroup.subset_closure
  have h1 : g = A6Models.tAdd ∨ g = A6Models.tSq ∨ g = A6Models.tInv := by
    simpa [pslGens] using (show g ∈ pslGens from hg)
  show g ∈ s6Gens
  simp only [s6Gens, List.mem_cons, List.not_mem_nil, or_false]
  rcases h1 with h | h | h <;> simp [h]

theorem s6_le_autA6 : s6 ≤ A6Models.autA6 := by
  rw [autA6_eq]
  unfold s6
  rw [Subgroup.closure_le]
  intro g hg
  apply Subgroup.subset_closure
  show g ∈ autGens
  have h1 : g = A6Models.tAdd ∨ g = A6Models.tSq ∨ g = A6Models.tInv ∨ g = A6Models.tFrob := by
    simpa [s6Gens] using (show g ∈ s6Gens from hg)
  simp only [autGens, List.mem_cons, List.not_mem_nil, or_false]
  rcases h1 with h | h | h | h <;> simp [h]

theorem s6RepsP_mem_closure : ∀ r ∈ s6RepsP, r ∈ s6 := by
  intro r hr
  simp only [s6RepsP, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact Subgroup.one_mem _
  · exact Subgroup.subset_closure (by simp [s6Gens])

theorem mem_s6_iff_exists (x : P10) : x ∈ s6 ↔ ∃ r ∈ s6RepsP, x * r⁻¹ ∈ A6Models.psl29 := by
  unfold s6
  refine mem_closure_iff_of_cosets (gens := s6Gens) (N := A6Models.psl29) ?_ ?_
    (by simp [s6RepsP]) ?_ x
  · exact psl29_le_s6
  · exact s6RepsP_mem_closure
  · intro r hr g hg
    have hcheck := Core.s6_cosets
    unfold Core.cosetCheck at hcheck
    rw [List.all_eq_true] at hcheck
    have h1 := hcheck (code r) (by rw [← s6RepsP_code]; exact List.mem_map_of_mem hr)
    rw [List.all_eq_true] at h1
    have h2 := h1 (code g) (by rw [← s6Gens_code]; exact List.mem_map_of_mem hg)
    rw [List.any_eq_true] at h2
    obtain ⟨rinv, hrinv, hmem⟩ := h2
    rw [← s6RepsP_inv_code] at hrinv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrinv
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hc
    refine ⟨r', hr', ?_⟩
    rw [mem_psl29_iff, code_mul, code_mul]
    simpa [List.contains_eq_any_beq] using hmem

theorem mem_s6_iff (x : P10) : x ∈ s6 ↔ Core.inS6 (code x) = true := by
  rw [mem_s6_iff_exists, Core.inS6, List.any_eq_true]
  constructor
  · rintro ⟨r, hr, hxr⟩
    refine ⟨code r⁻¹, ?_, ?_⟩
    · rw [← s6RepsP_inv_code]; exact List.mem_map_of_mem (List.mem_map_of_mem hr)
    · rw [← code_mul]
      simpa [List.contains_eq_any_beq, mem_psl29_iff] using (mem_psl29_iff _).1 hxr
  · rintro ⟨rinv, hrinv, hmem⟩
    rw [← s6RepsP_inv_code] at hrinv
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hrinv
    obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hc
    refine ⟨r', hr', ?_⟩
    rw [mem_psl29_iff, code_mul]
    simpa [List.contains_eq_any_beq] using hmem

theorem card_psl29_centralizer {α : P10} :
    Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({α} : Set P10)) =
      (Core.cpslList (code α)).length := by
  refine card_eq_of_code_mem (E := Core.cpslList (code α)) ?_ ?_ ?_
  · unfold Core.cpslList
    exact Core.psl_nodup.filter _
  · intro x
    unfold Core.cpslList
    rw [List.mem_filter, Subgroup.mem_inf, mem_psl29_iff,
      Subgroup.mem_centralizer_singleton_iff]
    simp only [beq_iff_eq]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      rw [← code_mul, ← code_mul, h2]
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      apply code_injective
      rw [code_mul, code_mul, h2]
  · intro c hc
    unfold Core.cpslList at hc
    rw [List.mem_filter] at hc
    obtain ⟨hc1, hc2⟩ := hc
    obtain ⟨x, hx, rfl⟩ := exists_psl29_of_code hc1
    simp only [beq_iff_eq] at hc2
    refine ⟨x, ⟨hx, ?_⟩, rfl⟩
    show x ∈ Subgroup.centralizer ({α} : Set P10)
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply code_injective
    rw [code_mul, code_mul, hc2]

theorem card_psl29_centralizer_of_not_mem {α : P10} (hα : α ∈ A6Models.autA6) (h2 : α * α = 1)
    (hne : α ≠ 1) (hpsl : α ∉ A6Models.psl29) (hs6 : α ∉ s6) :
    Nat.card ↥(A6Models.psl29 ⊓ Subgroup.centralizer ({α} : Set P10)) = 10 := by
  have h := Core.inv_classification
  rw [List.all_eq_true] at h
  have h1 := h (code α) (code_mem_autL hα)
  have e1 : (Core.cmul (code α) (code α) != Core.cid) = false := by
    rw [← code_mul, h2, code_one]; simp
  have e2 : (code α == Core.cid) = false := by
    simp only [beq_eq_false_iff_ne, ne_eq]
    rw [← code_one]
    intro hc
    exact hne (code_injective hc)
  have e3 : Core.pslLit.contains (code α) = false := by
    rw [← Bool.not_eq_true, List.contains_iff_mem, ← mem_psl29_iff]
    exact hpsl
  have e4 : Core.inS6 (code α) = false := by
    rw [← Bool.not_eq_true, ← mem_s6_iff]
    exact hs6
  rw [e1, e2, e3, e4] at h1
  simp only [Bool.false_or, beq_iff_eq] at h1
  rw [card_psl29_centralizer, h1]

end CFSG.QuasithinUnique.A6Facts
