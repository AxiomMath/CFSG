module

public import CFSG.GF2Type.Smith1979.IdxFourModelDefs
public import CFSG.GF2Type.Smith1979.GammaU.Enum

public section

namespace CFSG.GF2Type.Smith1979.IdxFour

open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum

theorem rep_one (N : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Rep N idR :=
  ⟨idR_ok, 1, one_mem _, fun v => (linOfRows_idR v).symm⟩

theorem rep_mul {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {x y : Array ℕ} (hx : Rep N x) (hy : Rep N y) :
    Rep N (mulR x y) := by
  obtain ⟨hxo, U, hU, hUx⟩ := hx
  obtain ⟨hyo, V, hV, hVx⟩ := hy
  exact ⟨okRows_mulR hxo hyo, U * V, mul_mem hU hV, fun v => by
    rw [LinearEquiv.mul_apply, hVx, hUx, linOfRows_mulR]⟩

theorem rep_gen {gs : List (Array ℕ)} (hgs : GensOK gs) {g : Array ℕ} (hg : g ∈ gs) :
    Rep (genGrp gs) g :=
  ⟨(hgs g hg).1, eqvOf g (invR g) (hgs g hg).2.2.1 (hgs g hg).2.2.2, gen_mem hgs hg, fun _ => rfl⟩

@[expose] def wordRows (gs : List (Array ℕ)) (w : List ℕ) : Array ℕ :=
  (w.map fun i => gs[i]!).foldr mulR idR

theorem rep_word {gs : List (Array ℕ)} (hgs : GensOK gs) :
    ∀ w : List ℕ, (∀ i ∈ w, i < gs.length) → Rep (genGrp gs) (wordRows gs w)
  | [], _ => rep_one _
  | i :: w, h => by
    have hi : i < gs.length := h i List.mem_cons_self
    have hmem : gs[i]! ∈ gs := by
      rw [getElem!_pos gs i hi]
      exact List.getElem_mem hi
    have := rep_mul (rep_gen hgs hmem) (rep_word hgs w fun j hj => h j (List.mem_cons_of_mem i hj))
    simpa [wordRows] using this

theorem genGrp_le_of_rep {gs : List (Array ℕ)} {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (h : ∀ g ∈ gs, Rep N g) : genGrp gs ≤ N := by
  refine (Subgroup.closure_le N).2 ?_
  rintro l ⟨r, hr, hl⟩
  obtain ⟨-, U, hU, hUx⟩ := h r hr
  have : l = U := LinearEquiv.ext fun x => (hl x).trans (hUx x).symm
  rw [this]
  exact hU

abbrev IsInvRows (r : Array ℕ) : Prop := mulR r (invR r) = idR ∧ mulR (invR r) r = idR

@[expose] noncomputable def rowsE (r : Array ℕ) (h : IsInvRows r) : V12 ≃ₗ[ZMod 2] V12 :=
  eqvOf r (invR r) h.1 h.2

theorem rowsE_apply (r : Array ℕ) (h : IsInvRows r) (x : V12) : rowsE r h x = linOfRows r x := rfl

theorem rowsE_mul {r s : Array ℕ} (hr : IsInvRows r) (hs : IsInvRows s) (hrs : IsInvRows (mulR r s)) :
    rowsE (mulR r s) hrs = rowsE r hr * rowsE s hs :=
  LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, rowsE_apply, rowsE_apply, rowsE_apply, linOfRows_mulR]

theorem rowsE_eq_of_rows_eq {r s : Array ℕ} (hr : IsInvRows r) (hs : IsInvRows s) (h : r = s) :
    rowsE r hr = rowsE s hs := by
  subst h
  rfl

theorem rowsE_mem {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {r : Array ℕ} (hr : IsInvRows r)
    (h : Rep N r) : rowsE r hr ∈ N := by
  obtain ⟨-, U, hU, hUx⟩ := h
  have : U = rowsE r hr := LinearEquiv.ext fun v => (hUx v).trans rfl
  rw [← this]
  exact hU

theorem rep_of_mem {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {r : Array ℕ} (hok : okRows r = true)
    (hr : IsInvRows r) (h : rowsE r hr ∈ N) : Rep N r :=
  ⟨hok, rowsE r hr, h, fun _ => rfl⟩

theorem okRows_invR (r : Array ℕ) : okRows (invR r) = true := by
  simp only [okRows, invR, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true']
  refine ⟨by simp, fun x hx => ?_⟩
  simp only [List.mem_toArray, List.mem_map, List.mem_range] at hx
  obtain ⟨j, -, rfl⟩ := hx
  cases h : (List.range 4096).find? fun n => appN r n == 2 ^ j with
  | none => simp
  | some n =>
    have := List.mem_of_find?_eq_some h
    simpa using List.mem_range.1 this

theorem okRows_of {r : Array ℕ} (h1 : r.size = 12) (h2 : ∀ x ∈ r.toList, x < 4096) :
    okRows r = true := by
  simp only [okRows, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true']
  exact ⟨h1, fun x hx => by simpa using h2 x (Array.mem_toList_iff.2 hx)⟩

theorem isoN_of_list {r : Array ℕ} (h1 : r.size = 12) (h2 : ∀ x ∈ r.toList, x < 4096)
    (h3 : (List.range 4096).all (fun n => q0b (appN r n) == q0b n) = true) : isoN r = true := by
  simp only [isoN, Bool.and_eq_true, beq_iff_eq, Array.all_eq_true']
  exact ⟨⟨h1, fun x hx => by simpa using h2 x (Array.mem_toList_iff.2 hx)⟩, h3⟩

theorem invR_eq {g gi : Array ℕ} (h1 : mulR g gi = idR) (h2 : mulR gi g = idR) (hsz : gi.size = 12)
    (hlt : ∀ x ∈ gi.toList, x < 4096) : invR g = gi := by
  have hid : ∀ j : ℕ, j < 12 → idR[j]! = 2 ^ j := by decide
  have hL : ∀ x, linOfRows gi (linOfRows g x) = x := fun x => by
    rw [← linOfRows_mulR, h2, linOfRows_idR]
  refine Array.ext (by simp [invR, hsz]) fun j hj hj' => ?_
  have hj12 : j < 12 := by simpa [invR] using hj
  have hjlt : gi[j] < 4096 := hlt _ (by simp)
  have hfix : appN g gi[j] = 2 ^ j := by
    have := congrArg (fun a : Array ℕ => a[j]!) h1
    simp only [mulR, getElem!_map_appN, hid j hj12] at this
    rwa [getElem!_pos gi j hj'] at this
  have hfind : (List.range 4096).find? (fun n => appN g n == 2 ^ j) = some gi[j] := by
    rw [List.find?_eq_some_iff_getElem]
    refine ⟨by simpa using hfix, gi[j], by simpa using hjlt, by simp, fun i hi => ?_⟩
    simp only [List.getElem_range, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
    intro hgi
    have hi4 : i < 4096 := by omega
    have h3 : vecOf gi[j] = vecOf i := by
      have := hL (vecOf i)
      rw [← vecOf_appN, hgi] at this
      have h4 := linOfRows_unit gi ⟨j, hj12⟩
      simp only [] at h4
      rw [h4, getElem!_pos gi j hj'] at this
      exact this
    exact absurd (vecOf_inj hjlt hi4 h3) (by omega)
  simp [invR, hfind]

theorem gensOK_of_pairs {gs : List (Array ℕ)} (ps : List (Array ℕ × Array ℕ))
    (hps : ∀ p ∈ ps, p.1.size = 12 ∧ (∀ x ∈ p.1.toList, x < 4096) ∧ p.2.size = 12 ∧
      (∀ x ∈ p.2.toList, x < 4096) ∧ mulR p.1 p.2 = idR ∧ mulR p.2 p.1 = idR)
    (h : ∀ g ∈ gs, ∃ p ∈ ps, p.1 = g) : GensOK gs := by
  intro g hg
  obtain ⟨p, hp, rfl⟩ := h g hg
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hps p hp
  have := invR_eq a5 a6 a3 a4
  rw [this]
  exact ⟨okRows_of a1 a2, okRows_of a3 a4, a5, a6⟩

@[expose] def invPairs : List (Array ℕ × Array ℕ) :=
  [(s12Rows, #[2, 1, 4, 8, 16, 32, 128, 64, 256, 512, 1024, 2048]),
   (s6Rows, #[32, 1, 2, 4, 8, 16, 2048, 64, 128, 256, 512, 1024]),
   (sigRows, #[1, 2, 4, 8, 16, 32, 65, 130, 260, 520, 1040, 2080]),
   (y3Rows, #[385, 263, 135, 3128, 2072, 1064, 454, 196, 322, 560, 3616, 3600]),
   (a3Rows, #[4, 1, 2, 8, 16, 32, 256, 64, 128, 512, 1024, 2048]),
   (a5Rows, #[1, 32, 2, 4, 8, 16, 64, 2048, 128, 256, 512, 1024]),
   (d5Rows[0]!, #[65, 128, 4, 8, 16, 32, 1, 130, 256, 512, 1024, 2048]),
   (d5Rows[1]!, #[1, 130, 256, 8, 16, 32, 64, 2, 260, 512, 1024, 2048]),
   (d5Rows[2]!, #[1, 2, 260, 512, 16, 32, 64, 128, 4, 520, 1024, 2048]),
   (d5Rows[3]!, #[1, 2, 4, 520, 1024, 32, 64, 128, 256, 8, 1040, 2048]),
   (d5Rows[4]!, #[1, 2, 4, 8, 1040, 2048, 64, 128, 256, 512, 16, 2080]),
   (omegaRows, #[65, 130, 260, 520, 1040, 2080, 1, 2, 4, 8, 16, 32])]

theorem invPairs_ok : ∀ p ∈ invPairs, p.1.size = 12 ∧ (∀ x ∈ p.1.toList, x < 4096) ∧
    p.2.size = 12 ∧ (∀ x ∈ p.2.toList, x < 4096) ∧ mulR p.1 p.2 = idR ∧ mulR p.2 p.1 = idR := by
  decide +kernel

theorem gensOK_m0Gens : GensOK m0Gens :=
  gensOK_of_pairs invPairs invPairs_ok (by decide +kernel)

theorem gensOK_e0Gens : GensOK e0Gens :=
  gensOK_of_pairs invPairs invPairs_ok (by decide +kernel)

theorem gensOK_n0Gens : GensOK n0Gens :=
  gensOK_of_pairs invPairs invPairs_ok (by decide +kernel)

theorem isInvRows_of_mem {r : Array ℕ} (h : ∃ p ∈ invPairs, p.1 = r) : IsInvRows r := by
  obtain ⟨p, hp, rfl⟩ := h
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := invPairs_ok p hp
  unfold IsInvRows
  rw [invR_eq a5 a6 a3 a4]
  exact ⟨a5, a6⟩

theorem isInvRows_omegaRows : IsInvRows omegaRows :=
  isInvRows_of_mem (by decide +kernel)
theorem isInvRows_s12Rows : IsInvRows s12Rows :=
  isInvRows_of_mem (by decide +kernel)
theorem isInvRows_s6Rows : IsInvRows s6Rows :=
  isInvRows_of_mem (by decide +kernel)
theorem isInvRows_sigRows : IsInvRows sigRows :=
  isInvRows_of_mem (by decide +kernel)
theorem isInvRows_y3Rows : IsInvRows y3Rows :=
  isInvRows_of_mem (by decide +kernel)

theorem rep_mono {N N' : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (h : N ≤ N') {r : Array ℕ} (hr : Rep N r) :
    Rep N' r := by
  obtain ⟨hok, U, hU, hUx⟩ := hr
  exact ⟨hok, U, h hU, hUx⟩

theorem rep_M0_a3 : Rep M0 a3Rows := by
  have h := rep_word gensOK_m0Gens [0, 1, 0, 1, 1, 1, 1, 1] (by decide)
  rwa [show wordRows m0Gens [0, 1, 0, 1, 1, 1, 1, 1] = a3Rows by decide +kernel] at h

theorem rep_M0_a5 : Rep M0 a5Rows := by
  have h := rep_word gensOK_m0Gens [0, 1] (by decide)
  rwa [show wordRows m0Gens [0, 1] = a5Rows by decide +kernel] at h

theorem E0_le_M0 : E0 ≤ M0 := by
  refine genGrp_le_of_rep fun g hg => ?_
  simp only [e0Gens, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact rep_M0_a3
  · exact rep_M0_a5
  · exact rep_gen gensOK_m0Gens (by simp [m0Gens])

@[expose] def d5Words : List (List ℕ) :=
  [[0, 2, 0, 2, 2], [2, 2, 0, 0, 2], [1, 2, 2, 0, 0, 2, 1, 1, 1, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 2, 1, 1, 2, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 2, 2, 1, 0, 0, 1,
    1, 1, 1, 0, 0, 1],
   [1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 0, 0, 2, 1, 1]]

theorem d5Words_eq : (d5Words.map (wordRows e0Gens)) = d5Rows := by decide +kernel

theorem rep_E0_d5 : ∀ r ∈ d5Rows, Rep E0 r := by
  intro r hr
  rw [← d5Words_eq] at hr
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hr
  refine rep_word gensOK_e0Gens w ?_
  intro i hi
  have : ∀ w ∈ d5Words, ∀ i ∈ w, i < 3 := by decide
  simpa [e0Gens] using this w hw i hi

theorem N0_le_M0 : N0 ≤ M0 := by
  refine genGrp_le_of_rep fun g hg => ?_
  simp only [n0Gens, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with hg | rfl | rfl | rfl
  · exact rep_mono E0_le_M0 (rep_E0_d5 g hg)
  all_goals exact rep_gen gensOK_m0Gens (by simp [m0Gens])

theorem gammaUN_of {r : Array ℕ} (h1 : r.size = 12) (h2 : ∀ x ∈ r.toList, x < 4096)
    (h3 : (List.range 4096).all (fun n => q0b (appN r n) == q0b n) = true)
    (h4 : unitaryN r = true ∨ antiN r = true) : gammaUN r = true := by
  simp only [gammaUN, Bool.and_eq_true, Bool.or_eq_true]
  exact ⟨isoN_of_list h1 h2 h3, h4⟩

theorem rep_gammaU_of {r : Array ℕ} (hok : okRows r = true) (h : gammaUN r = true) :
    Rep gammaU r :=
  ⟨hok, toU r h, gammaUN_spec h, fun _ => rfl⟩

theorem rep_gammaU_s12 : Rep gammaU s12Rows :=
  rep_gammaU_of (okRows_of (by rfl) (by decide))
    (gammaUN_of (by rfl) (by decide) (by decide +kernel) (by decide +kernel))

theorem rep_gammaU_s6 : Rep gammaU s6Rows :=
  rep_gammaU_of (okRows_of (by rfl) (by decide))
    (gammaUN_of (by rfl) (by decide) (by decide +kernel) (by decide +kernel))

theorem rep_gammaU_sig : Rep gammaU sigRows :=
  rep_gammaU_of (okRows_of (by rfl) (by decide))
    (gammaUN_of (by rfl) (by decide) (by decide +kernel) (by decide +kernel))

theorem rep_gammaU_y3 : Rep gammaU y3Rows :=
  rep_gammaU_of (okRows_of (by rfl) (by decide))
    (gammaUN_of (by rfl) (by decide) (by decide +kernel) (by decide +kernel))

theorem M0_le_gammaU : M0 ≤ gammaU := by
  refine genGrp_le_of_rep fun g hg => ?_
  simp only [m0Gens, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact rep_gammaU_s12
  · exact rep_gammaU_s6
  · exact rep_gammaU_sig
  · exact rep_gammaU_y3

theorem E0_le_gammaU : E0 ≤ gammaU := E0_le_M0.trans M0_le_gammaU

theorem N0_le_gammaU : N0 ≤ gammaU := N0_le_M0.trans M0_le_gammaU

theorem linOfRows_omegaRows (x : V12) : linOfRows omegaRows x = theta0 x := by
  have hf : linOfRows omegaRows = theta0 := linMap_ext fun j => by
    rw [linOfRows_unit, ← vecOf_theta0N (two_pow_lt j)]
    congr 1
    fin_cases j <;> decide
  exact LinearMap.congr_fun hf x

@[expose] noncomputable def omegaE : V12 ≃ₗ[ZMod 2] V12 := rowsE omegaRows isInvRows_omegaRows

theorem omegaE_apply (x : V12) : omegaE x = theta0 x := linOfRows_omegaRows x

@[expose] noncomputable def s12e : V12 ≃ₗ[ZMod 2] V12 := rowsE s12Rows isInvRows_s12Rows

@[expose] noncomputable def s6e : V12 ≃ₗ[ZMod 2] V12 := rowsE s6Rows isInvRows_s6Rows

@[expose] noncomputable def sige : V12 ≃ₗ[ZMod 2] V12 := rowsE sigRows isInvRows_sigRows

@[expose] noncomputable def y3R : V12 ≃ₗ[ZMod 2] V12 := rowsE y3Rows isInvRows_y3Rows

theorem rowsE_comm {r s : Array ℕ} (hr : IsInvRows r) (hs : IsInvRows s) (h : mulR r s = mulR s r) :
    rowsE r hr * rowsE s hs = rowsE s hs * rowsE r hr :=
  LinearEquiv.ext fun x => by
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, rowsE_apply, rowsE_apply, rowsE_apply,
      rowsE_apply, ← linOfRows_mulR, ← linOfRows_mulR, h]

theorem s12e_comm_omegaE : s12e * omegaE = omegaE * s12e :=
  rowsE_comm _ _ (by decide +kernel)

theorem s6e_comm_omegaE : s6e * omegaE = omegaE * s6e :=
  rowsE_comm _ _ (by decide +kernel)

theorem y3R_comm_omegaE : y3R * omegaE = omegaE * y3R :=
  rowsE_comm _ _ (by decide +kernel)

theorem sige_omegaE : sige * omegaE = omegaE * omegaE * sige := by
  have h : mulR sigRows omegaRows = mulR omegaRows (mulR omegaRows sigRows) := by decide +kernel
  refine LinearEquiv.ext fun x => ?_
  simp only [LinearEquiv.mul_apply, sige, omegaE, rowsE_apply]
  rw [← linOfRows_mulR sigRows omegaRows, ← linOfRows_mulR omegaRows sigRows,
    ← linOfRows_mulR omegaRows (mulR omegaRows sigRows), h]

theorem s12e_mem_M0 : s12e ∈ M0 := rowsE_mem _ (rep_gen gensOK_m0Gens (by simp [m0Gens]))
theorem s6e_mem_M0 : s6e ∈ M0 := rowsE_mem _ (rep_gen gensOK_m0Gens (by simp [m0Gens]))
theorem sige_mem_M0 : sige ∈ M0 := rowsE_mem _ (rep_gen gensOK_m0Gens (by simp [m0Gens]))
theorem y3R_mem_M0 : y3R ∈ M0 := rowsE_mem _ (rep_gen gensOK_m0Gens (by simp [m0Gens]))

@[expose] def thetaWord : List ℕ :=
  [1, 1, 1, 1, 0, 1, 2, 2, 1, 0, 2, 1, 1, 1, 1, 2, 0, 1, 1, 1, 1, 2, 1, 2, 2, 0, 2, 1, 1, 0, 2, 2,
    0, 0, 2, 1, 1]

theorem rep_E0_omega : Rep E0 omegaRows := by
  have h := rep_word gensOK_e0Gens thetaWord (by decide)
  rwa [show wordRows e0Gens thetaWord = omegaRows by decide +kernel] at h

theorem omegaE_mem_E0 : omegaE ∈ E0 := rowsE_mem _ rep_E0_omega

theorem E0_comm_omegaE : ∀ g ∈ E0, g * omegaE = omegaE * g := by
  have h : E0 ≤ Subgroup.centralizer {omegaE} := by
    refine (Subgroup.closure_le _).2 ?_
    rintro l ⟨r, hr, hl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    rintro _ rfl
    refine LinearEquiv.ext fun x => ?_
    have hc : ∀ r ∈ e0Gens, mulR omegaRows r = mulR r omegaRows := by decide +kernel
    simp only [LinearEquiv.mul_apply, hl, omegaE, rowsE_apply]
    rw [← linOfRows_mulR, ← linOfRows_mulR, hc r hr]
  exact fun g hg => (Subgroup.mem_centralizer_iff.1 (h hg) _ rfl).symm

theorem okRows_s12Rows : okRows s12Rows = true := (gensOK_m0Gens _ (by simp [m0Gens])).1
theorem okRows_s6Rows : okRows s6Rows = true := (gensOK_m0Gens _ (by simp [m0Gens])).1
theorem okRows_sigRows : okRows sigRows = true := (gensOK_m0Gens _ (by simp [m0Gens])).1
theorem okRows_y3Rows : okRows y3Rows = true := (gensOK_m0Gens _ (by simp [m0Gens])).1
theorem okRows_omegaRows : okRows omegaRows = true := okRows_of (by rfl) (by decide)

end CFSG.GF2Type.Smith1979.IdxFour
