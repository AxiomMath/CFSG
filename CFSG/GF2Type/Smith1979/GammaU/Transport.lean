module

public import CFSG.GF2Type.Smith1979.GammaU.CensusC

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem NLMem.inv {i : ℕ} {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) : NLMem i h⁻¹ where
  mem := inv_mem hh.mem
  fix := by
    calc h⁻¹ (vecOf a0) = h⁻¹ (h (vecOf a0)) := by rw [hh.fix]
      _ = vecOf a0 := inv_apply_apply h _
  d0 y := by
    have := hh.d0 (h⁻¹ y)
    rw [apply_inv_apply] at this
    exact this.symm
  norm l := by
    have := hh.norm (h⁻¹ * l * h⁻¹⁻¹)
    rw [show h * (h⁻¹ * l * h⁻¹⁻¹) * h⁻¹ = l by group] at this
    exact this.symm

theorem NLMem.mul {i : ℕ} {g h : V12 ≃ₗ[ZMod 2] V12} (hg : NLMem i g) (hh : NLMem i h) :
    NLMem i (g * h) where
  mem := mul_mem hg.mem hh.mem
  fix := by rw [LinearEquiv.mul_apply, hh.fix, hg.fix]
  d0 y := by rw [LinearEquiv.mul_apply, hg.d0, hh.d0]
  norm l := by
    rw [show g * h * l * (g * h)⁻¹ = g * (h * l * h⁻¹) * g⁻¹ by group, hg.norm, hh.norm]

theorem gammaU_theta {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ gammaU) :
    ((∀ y, h (theta0 y) = theta0 (h y)) ∧ ∀ y, h⁻¹ (theta0 y) = theta0 (h⁻¹ y)) ∨
      ((∀ y, h (theta0 y) = theta0 (theta0 (h y))) ∧
        ∀ y, h⁻¹ (theta0 y) = theta0 (theta0 (h⁻¹ y))) := by
  rcases hh.2 with hu | ha
  · refine Or.inl ⟨hu, fun y => h.injective ?_⟩
    change h (h⁻¹ (theta0 y)) = h (theta0 (h⁻¹ y))
    rw [apply_inv_apply, hu, apply_inv_apply]
  · refine Or.inr ⟨ha, fun y => h.injective ?_⟩
    change h (h⁻¹ (theta0 y)) = h (theta0 (theta0 (h⁻¹ y)))
    rw [apply_inv_apply, ha, ha, apply_inv_apply, theta0_theta0_theta0]

theorem unitary_conj {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ gammaU) {f : V12 → V12}
    (hf : ∀ x, f (theta0 x) = theta0 (f x)) (x : V12) :
    h (f (h⁻¹ (theta0 x))) = theta0 (h (f (h⁻¹ x))) := by
  rcases gammaU_theta hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, hf, h1]
  · rw [h2, hf, hf, h1, h1, theta0_theta0_theta0]

theorem anti_conj {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ gammaU) {f : V12 → V12}
    (hf : ∀ x, f (theta0 x) = theta0 (theta0 (f x))) (x : V12) :
    h (f (h⁻¹ (theta0 x))) = theta0 (theta0 (h (f (h⁻¹ x)))) := by
  rcases gammaU_theta hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, hf, h1, h1]
  · rw [h2, hf, hf, theta0_theta0_theta0, h1]

theorem compGens_mem_of (hfr : CompFacts) {c : ℕ} (hc : c < 32)
    {g : Array ℕ} (hg : g ∈ ResPair.compGens c) :
    ∃ U ∈ gammaU, ∀ y, U y = linOfRows g y :=
  hfr c hc g hg

theorem realized_of_gens {c : ℕ}
    (hcg : ∀ g ∈ ResPair.compGens c, ∃ U ∈ gammaU, ∀ y, U y = linOfRows g y)
    {r : Array ℕ} (hr : r ∈ compOf c) :
    ∃ l : V12 ≃ₗ[ZMod 2] V12, ∀ y, l y = linOfRows r y := by
  rw [compOf_eq] at hr
  obtain ⟨l, -, hl⟩ := subsetProducts_mem (L := ⊤)
    (fun g hg => by
      obtain ⟨U, -, hU⟩ := hcg g hg
      exact ⟨U, Subgroup.mem_top _, hU⟩) r hr
  exact ⟨l, hl⟩

theorem realized_of_mem_compOf (hfr : CompFacts) {c : ℕ}
    (hc : c < 32) {r : Array ℕ} (hr : r ∈ compOf c) :
    ∃ l : V12 ≃ₗ[ZMod 2] V12, ∀ y, l y = linOfRows r y :=
  realized_of_gens (fun _ hg => compGens_mem_of hfr hc hg) hr

theorem exists_rows_conj_of_gens {i : ℕ}
    (hcg : ∀ g ∈ ResPair.compGens i, ∃ U ∈ gammaU, ∀ y, U y = linOfRows g y)
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) {r : Array ℕ} (hr : r ∈ compOf i) :
    ∃ l : V12 ≃ₗ[ZMod 2] V12, (∀ y, l y = linOfRows r y) ∧
      ∃ r₁ ∈ compOf i, ∀ y, (h * l * h⁻¹) y = linOfRows r₁ y := by
  obtain ⟨l, hl⟩ := realized_of_gens hcg hr
  exact ⟨l, hl, (hh.norm l).2 ⟨r, hr, hl⟩⟩

theorem exists_rows_conj (hfr : CompFacts) {i : ℕ} (hi : i < 32)
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) {r : Array ℕ} (hr : r ∈ compOf i) :
    ∃ l : V12 ≃ₗ[ZMod 2] V12, (∀ y, l y = linOfRows r y) ∧
      ∃ r₁ ∈ compOf i, ∀ y, (h * l * h⁻¹) y = linOfRows r₁ y :=
  exists_rows_conj_of_gens (fun _ hg => compGens_mem_of hfr hi hg) hh hr

theorem inFrame_conj {i : ℕ} {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h)
    {u l : V12 ≃ₗ[ZMod 2] V12} {r r₁ : Array ℕ} (hl : ∀ y, l y = linOfRows r y)
    (hr₁ : ∀ y, (h * l * h⁻¹) y = linOfRows r₁ y) (hf : Viol.InFrame (compOf i) u r) :
    Viol.InFrame (compOf i) (h * u * h⁻¹) r₁ := by
  obtain ⟨r', hr', hr'x⟩ := hf
  have hm : RowsSet (compOf i) (u⁻¹ * l * u) := ⟨r', hr', fun x => by
    rw [← hr'x x, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hl]⟩
  obtain ⟨r'', hr'', hr''x⟩ := (hh.norm _).2 hm
  refine ⟨r'', hr'', fun x => ?_⟩
  rw [← hr''x x, ← hr₁]
  simp only [LinearEquiv.mul_apply, mul_inv_rev, inv_inv, inv_apply_apply]

theorem f2Indep3_map {x y w : V12} (h : V12 ≃ₗ[ZMod 2] V12) (hi : Viol.F2Indep3 x y w) :
    Viol.F2Indep3 (h x) (h y) (h w) := fun a b c habc => hi a b c (h.injective (by
  rw [map_add, map_add, map_smul, map_smul, map_smul, habc, map_zero]))

theorem violation_conj_of_gens {i : ℕ}
    (hcg : ∀ g ∈ ResPair.compGens i, ∃ U ∈ gammaU, ∀ y, U y = linOfRows g y)
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hv : Viol.Violation N (compOf i) (compOf i)) :
    Viol.Violation (N.map (MulAut.conj h).toMonoidHom) (compOf i) (compOf i) := by
  rcases hv with ⟨h₀, hh₀, hfix, r, hr, hnot⟩ | ⟨r, hr, -, hrH, -⟩ |
      ⟨r, hr, hanti, u₁, hu₁, u₂, hu₂, u₃, hu₃, hf₁, hf₂, hf₃, hind⟩
  · obtain ⟨l, hl, r₁, hr₁, hr₁l⟩ := exists_rows_conj_of_gens hcg hh hr
    refine Or.inl ⟨h * h₀ * h⁻¹, mem_map_conj.2 ⟨h₀, hh₀, rfl⟩, ?_, r₁, hr₁, ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hh.inv.fix, hfix, hh.fix]
    · rintro ⟨r', hr', hr'x⟩
      apply hnot
      have hm : RowsSet (compOf i) (h * (h₀ * l * h₀⁻¹) * h⁻¹) := ⟨r', hr', fun x => by
        rw [← hr'x x, ← hr₁l]
        simp only [LinearEquiv.mul_apply, mul_inv_rev, inv_inv, inv_apply_apply]⟩
      obtain ⟨r'', hr'', hr''x⟩ := (hh.norm _).1 hm
      refine ⟨r'', hr'', fun x => ?_⟩
      rw [← hr''x x, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hl]
  · exact absurd hr hrH
  · obtain ⟨l, hl, r₁, hr₁, hr₁l⟩ := exists_rows_conj_of_gens hcg hh hr
    refine Or.inr (Or.inr ⟨r₁, hr₁, fun x => ?_, h * u₁ * h⁻¹, mem_map_conj.2 ⟨u₁, hu₁, rfl⟩,
      h * u₂ * h⁻¹, mem_map_conj.2 ⟨u₂, hu₂, rfl⟩, h * u₃ * h⁻¹, mem_map_conj.2 ⟨u₃, hu₃, rfl⟩,
      inFrame_conj hh hl hr₁l hf₁, inFrame_conj hh hl hr₁l hf₂, inFrame_conj hh hl hr₁l hf₃, ?_⟩)
    · rw [← hr₁l, ← hr₁l]
      simp only [LinearEquiv.mul_apply]
      exact anti_conj hh.mem (f := l) (fun y => by rw [hl, hl]; exact hanti y) x
    · simp only [LinearEquiv.mul_apply, hh.inv.fix]
      exact f2Indep3_map h hind

theorem violation_conj (hfr : CompFacts) {i : ℕ} (hi : i < 32)
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hv : Viol.Violation N (compOf i) (compOf i)) :
    Viol.Violation (N.map (MulAut.conj h).toMonoidHom) (compOf i) (compOf i) :=
  violation_conj_of_gens (fun _ hg => compGens_mem_of hfr hi hg) hh hv

theorem mem_colPts {s : Array ℕ} {e : ℕ} :
    e ∈ colPts s ↔ e ∈ spanList d0 ∧ e ≠ 0 ∧ q0b e = false ∧ e ≠ a0 ∧ e ≠ theta0N a0 ∧
      e ≠ a0 ^^^ theta0N a0 ∧ ∃ m < 4096, appN s m ^^^ m = e := by
  simp only [colPts, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
    List.contains_iff_mem, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨hS, ⟨⟨⟨⟨⟨h0, hq⟩, ha⟩, ht⟩, hat⟩, m, hm, hme⟩⟩
    exact ⟨hS, h0, hq, ha, ht, hat, m, hm, hme⟩
  · rintro ⟨hS, h0, hq, ha, ht, hat, m, hm, hme⟩
    exact ⟨hS, ⟨⟨⟨⟨⟨h0, hq⟩, ha⟩, ht⟩, hat⟩, m, hm, hme⟩⟩

theorem theta0_theta0_eq (x : V12) : theta0 (theta0 x) = x + theta0 x :=
  ext_lo_hi (fun i => by simp only [theta0_lo, theta0_hi, Pi.add_apply])
    (fun i => by simp only [theta0_lo, theta0_hi, Pi.add_apply])

theorem a0_lt : a0 < 4096 := by norm_num [a0]

theorem vecOf_theta0N_a0 : vecOf (theta0N a0) = theta0 (vecOf a0) := vecOf_theta0N a0_lt

theorem vecOf_xor_a0 : vecOf (a0 ^^^ theta0N a0) = vecOf a0 + theta0 (vecOf a0) := by
  rw [vecOf_xor, vecOf_theta0N_a0]

theorem point_a0_conj {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ gammaU)
    (hfix : h (vecOf a0) = vecOf a0) :
    (h (theta0 (vecOf a0)) = theta0 (vecOf a0) ∧
        h (vecOf a0 + theta0 (vecOf a0)) = vecOf a0 + theta0 (vecOf a0)) ∨
      (h (theta0 (vecOf a0)) = vecOf a0 + theta0 (vecOf a0) ∧
        h (vecOf a0 + theta0 (vecOf a0)) = theta0 (vecOf a0)) := by
  rcases gammaU_theta hh with ⟨h1, -⟩ | ⟨h1, -⟩
  · left
    rw [map_add, h1, hfix]
    exact ⟨rfl, rfl⟩
  · right
    rw [map_add, h1, hfix, theta0_theta0_eq]
    refine ⟨rfl, ?_⟩
    rw [← add_assoc, ← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul, zero_add]

theorem colPts_conj {i : ℕ} {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) {s s0 : Array ℕ}
    (hs0c : Canon s0) (hs0 : ∀ y, linOfRows s0 y = h⁻¹ (linOfRows s (h y))) {e : ℕ}
    (he : e ∈ colPts s) : codeOf (h⁻¹ (vecOf e)) ∈ colPts s0 := by
  obtain ⟨hS, h0, hq, ha, ht, hat, m, hm, hme⟩ := mem_colPts.1 he
  have he4 : e < 4096 := spanList_lt d0_lt e hS
  have hve' : vecOf (codeOf (h⁻¹ (vecOf e))) = h⁻¹ (vecOf e) := vecOf_codeOf _
  have hlt' := codeOf_lt (h⁻¹ (vecOf e))
  have hcode : ∀ c, c < 4096 → codeOf (h⁻¹ (vecOf e)) = c → vecOf e = h (vecOf c) := by
    intro c _ hc
    rw [← hc, hve', apply_inv_apply]
  refine mem_colPts.2 ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem_spanList_iff d0_lt hlt', hve', hh.inv.d0, ← mem_spanList_iff d0_lt he4]
    exact hS
  · intro hc
    apply h0
    have := hcode 0 (by norm_num) hc
    rw [vecOf_zero, map_zero] at this
    exact (vecOf_eq_zero he4).1 this
  · rw [q0b_codeOf, (inv_mem hh.mem).1, ← q0b_codeOf, codeOf_vecOf he4]
    exact hq
  · intro hc
    apply ha
    have := hcode a0 a0_lt hc
    rw [hh.fix] at this
    exact vecOf_inj he4 a0_lt this
  · intro hc
    have := hcode _ (theta0N_lt a0_lt) hc
    rw [vecOf_theta0N_a0] at this
    rcases point_a0_conj hh.mem hh.fix with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1, ← vecOf_theta0N_a0] at this
      exact ht (vecOf_inj he4 (theta0N_lt a0_lt) this)
    · rw [h1, ← vecOf_xor_a0] at this
      exact hat (vecOf_inj he4 (xor_lt a0_lt (theta0N_lt a0_lt)) this)
  · intro hc
    have := hcode _ (xor_lt a0_lt (theta0N_lt a0_lt)) hc
    rw [vecOf_xor_a0] at this
    rcases point_a0_conj hh.mem hh.fix with ⟨-, h2⟩ | ⟨-, h2⟩
    · rw [h2, ← vecOf_xor_a0] at this
      exact hat (vecOf_inj he4 (xor_lt a0_lt (theta0N_lt a0_lt)) this)
    · rw [h2, ← vecOf_theta0N_a0] at this
      exact ht (vecOf_inj he4 (theta0N_lt a0_lt) this)
  · refine ⟨codeOf (h⁻¹ (vecOf m)), codeOf_lt _, vecOf_inj
      (xor_lt (appN_lt hs0c.2 _) (codeOf_lt _)) hlt' ?_⟩
    rw [vecOf_xor, vecOf_appN, vecOf_codeOf, hve', hs0, apply_inv_apply, ← map_add, ← hme,
      vecOf_xor, vecOf_appN]

theorem thetaU_inv_apply (x : V12) : thetaU⁻¹ x = theta0 (theta0 x) := rfl

theorem thetaU_conj {h : V12 ≃ₗ[ZMod 2] V12} (hh : h ∈ gammaU) :
    h * thetaU * h⁻¹ = thetaU ∨ h * thetaU * h⁻¹ = thetaU⁻¹ := by
  rcases gammaU_theta hh with ⟨h1, -⟩ | ⟨h1, -⟩
  · refine Or.inl (LinearEquiv.ext fun x => ?_)
    simp only [LinearEquiv.mul_apply, thetaU_apply, h1, apply_inv_apply]
  · refine Or.inr (LinearEquiv.ext fun x => ?_)
    simp only [LinearEquiv.mul_apply, thetaU_apply, h1, apply_inv_apply, thetaU_inv_apply]

theorem closure_theta_inv (S : Set (V12 ≃ₗ[ZMod 2] V12)) :
    Subgroup.closure (S ∪ {thetaU⁻¹}) = Subgroup.closure (S ∪ {thetaU}) := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    rintro x (hx | rfl)
    · exact Subgroup.subset_closure (Or.inl hx)
    · exact inv_mem (Subgroup.subset_closure (Or.inr rfl))
  · rw [Subgroup.closure_le]
    rintro x (hx | rfl)
    · exact Subgroup.subset_closure (Or.inl hx)
    · have := inv_mem (Subgroup.subset_closure (k := S ∪ {thetaU⁻¹}) (Or.inr rfl))
      rwa [inv_inv] at this

theorem closure_conj {i : ℕ} {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h)
    (Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)) :
    (Subgroup.closure ({l | RowsSet (compOf i) l} ∪ ↑Le ∪ {thetaU})).map
        (MulAut.conj h).toMonoidHom =
      Subgroup.closure ({l | RowsSet (compOf i) l} ∪ ↑(Le.map (MulAut.conj h).toMonoidHom) ∪
        {thetaU}) := by
  rw [MonoidHom.map_closure, Set.image_union, Set.image_union, Set.image_singleton]
  have hA : (MulAut.conj h).toMonoidHom '' {l | RowsSet (compOf i) l} =
      {l | RowsSet (compOf i) l} := by
    ext l
    simp only [Set.mem_image, Set.mem_setOf_eq, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨l₀, hl₀, rfl⟩
      exact (hh.norm l₀).2 hl₀
    · intro hl
      refine ⟨h⁻¹ * l * h, ?_, by group⟩
      have := hh.norm (h⁻¹ * l * h)
      rw [show h * (h⁻¹ * l * h) * h⁻¹ = l by group] at this
      exact this.1 hl
  have hB : (MulAut.conj h).toMonoidHom '' ↑Le = ↑(Le.map (MulAut.conj h).toMonoidHom) :=
    (Subgroup.coe_map _ _).symm
  rw [hA, hB]
  have hθ : (MulAut.conj h).toMonoidHom thetaU = h * thetaU * h⁻¹ := rfl
  rw [hθ]
  rcases thetaU_conj hh.mem with h1 | h1
  · rw [h1]
  · rw [h1, closure_theta_inv]

theorem census_of_cfg (h16963 : StepAOrbitFacts) (h16964 : StepATFacts)
    {i m : ℕ} {T : ℕ → V12 ≃ₗ[ZMod 2] V12} (hT : FrameTr T m) {r0 : Array ℕ}
    {te : ℕ → V12 ≃ₗ[ZMod 2] V12} (hte : ColTr te r0) {P : Subgroup (V12 ≃ₗ[ZMod 2] V12) → Prop}
    (hC : CfgAll i r0 T m te P)
    {n : ℕ} (hn : n ∈ colPts r0) {De : Submodule (ZMod 2) V12}
    {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp (vecOf n) De Le)
    (hs : ∃ l ∈ Le, ∀ y, l y = linOfRows r0 y) (ha : vecOf a0 ∈ De)
    (hcard : Nat.card (candGrp i Le) = 1152) : P (candGrp i Le) := by
  obtain ⟨hg, hga⟩ := hte n hn
  rw [← hga] at H
  obtain ⟨j, hj, c, hc, hD, hL⟩ := frame_at h16963 h16964 T hT.1 hT.2.1 hT.2.2 hg H
  exact hC n hn j hj c hc Le hL (hD ▸ ha) hs hcard

theorem census_conj_of {i : ℕ} (hi : i < 32) (h16964 : StepATFacts)
    {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) {r r0 : Array ℕ} (hr0 : r0 ∈ unitaryElts i)
    (hrr : RowsConj h r r0)
    {P : Subgroup (V12 ≃ₗ[ZMod 2] V12) → Prop}
    (hC0 : ∀ {n : ℕ}, n ∈ colPts r0 → ∀ {De : Submodule (ZMod 2) V12}
      {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)}, Hyp (vecOf n) De Le →
      (∃ l ∈ Le, ∀ y, l y = linOfRows r0 y) → vecOf a0 ∈ De →
      Nat.card (candGrp i Le) = 1152 → P (candGrp i Le))
    {n : ℕ} (hn : n ∈ colPts r)
    {De : Submodule (ZMod 2) V12} {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp (vecOf n) De Le)
    (hs : ∃ l ∈ Le, ∀ y, l y = linOfRows r y) (ha : vecOf a0 ∈ De)
    (hcard : Nat.card (candGrp i Le) = 1152) :
    ∃ G, P G ∧ candGrp i Le = G.map (MulAut.conj h).toMonoidHom := by
  simp only [candGrp] at hC0 hcard ⊢
  unfold RowsConj at hrr
  have hr0c : Canon r0 := canon_of_mem_compOf h16964 hi (List.mem_filter.1 hr0).1
  have H' := H.conj (inv_mem hh.mem)
  rw [← vecOf_codeOf (h⁻¹ (vecOf n))] at H'
  have hn' := colPts_conj hh hr0c hrr hn
  have hs' : ∃ l ∈ Le.map (MulAut.conj h⁻¹).toMonoidHom, ∀ y, l y = linOfRows r0 y := by
    obtain ⟨l, hl, hlr⟩ := hs
    refine ⟨h⁻¹ * l * h⁻¹⁻¹, mem_map_conj.2 ⟨l, hl, rfl⟩, fun y => ?_⟩
    rw [hrr, inv_inv, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hlr]
  have ha' : vecOf a0 ∈ De.map ((h⁻¹ : V12 ≃ₗ[ZMod 2] V12) : V12 →ₗ[ZMod 2] V12) :=
    ⟨vecOf a0, ha, hh.inv.fix⟩
  have hconj := closure_conj hh.inv Le
  have hcard' : Nat.card (Subgroup.closure ({l | RowsSet (compOf i) l} ∪
      ↑(Le.map (MulAut.conj h⁻¹).toMonoidHom) ∪ {thetaU})) = 1152 := by
    rw [← hconj, Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective, hcard]
  refine ⟨_, hC0 hn' H' hs' ha' hcard', ?_⟩
  have hid : (MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom = MonoidHom.id _ := by
    ext x y
    simp [MulAut.conj_apply]
  rw [← hconj, Subgroup.map_map, hid, Subgroup.map_id]

theorem census_conj_cfg (h16963 : StepAOrbitFacts) (h16964 : StepATFacts)
    {i : ℕ} (hi : i < 32) {r0 : Array ℕ} {T : ℕ → V12 ≃ₗ[ZMod 2] V12} {m : ℕ}
    {te : ℕ → V12 ≃ₗ[ZMod 2] V12} (hB : CensusBase i r0 T m te) {h : V12 ≃ₗ[ZMod 2] V12}
    (hh : NLMem i h) {r : Array ℕ} (hrr : RowsConj h r r0)
    {P : Subgroup (V12 ≃ₗ[ZMod 2] V12) → Prop} (hC : CfgAll i r0 T m te P)
    {n : ℕ} (hn : n ∈ colPts r)
    {De : Submodule (ZMod 2) V12} {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (H : Hyp (vecOf n) De Le)
    (hs : ∃ l ∈ Le, ∀ y, l y = linOfRows r y) (ha : vecOf a0 ∈ De)
    (hcard : Nat.card (candGrp i Le) = 1152) :
    ∃ G, P G ∧ candGrp i Le = G.map (MulAut.conj h).toMonoidHom :=
  census_conj_of hi h16964 hh hB.1 hrr
    (fun {_} hn {_} {_} H hs ha hcard => census_of_cfg h16963 h16964 hB.2.1 hB.2.2 hC hn H hs ha hcard)
    hn H hs ha hcard

end CFSG.GF2Type.Smith1979.GammaU.StepA
