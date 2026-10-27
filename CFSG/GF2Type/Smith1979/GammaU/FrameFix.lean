module

public import CFSG.GF2Type.Smith1979.GammaU.Transport
public import CFSG.GF2Type.Smith1979.GammaU.PairBridge
public import Certificates.Certificate16971

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem frameFixAt_spec {i : ℕ} (h : frameFixAt i = true) :
    (∀ n < 4096, (∀ g ∈ ResPair.compGens i, appN g n = n) → n = 0 ∨ n = a0) ∧
    (∀ r ∈ compOf i, appN r a0 = a0) ∧
    (∀ r ∈ compOf i, ∀ x < 4096, f0b x a0 = false → appN r x ^^^ x ∈ spanList d0) ∧
    (∀ d ∈ d0, d = a0 ∨ ∃ l ∈ compOf i, ∃ x < 4096, f0b x a0 = false ∧ appN l x ^^^ x = d) ∧
    ∀ g ∈ ResPair.n2Gens i, gammaUN g = true := by
  simp only [frameFixAt, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hfix, ha⟩, hcomm⟩, hd⟩, hN⟩ := h
  refine ⟨fun n hn hg => ?_, fun r hr => ?_, fun r hr x hx hf => ?_, fun d hdm => ?_,
    fun g hg => ?_⟩
  · have h1 := List.all_eq_true.1 hfix n (List.mem_range.2 hn)
    have hall : (CFSG.GammaU.Native.compGens i).all
        (fun g => CFSG.GammaU.Native.appN g n == n) = true :=
      List.all_eq_true.2 fun g hgm => by
        rw [native_compGens] at hgm
        rw [native_appN, beq_iff_eq]
        exact hg g hgm
    rw [hall] at h1
    simp only [Bool.not_true, Bool.or_false, Bool.or_eq_true, beq_iff_eq, native_a0] at h1
    exact h1
  · have := List.all_eq_true.1 ha r (by rw [native_compOf]; exact hr)
    simpa only [beq_iff_eq, native_appN, native_a0] using this
  · have := List.all_eq_true.1 (List.all_eq_true.1 hcomm r (by rw [native_compOf]; exact hr)) x
      (List.mem_range.2 hx)
    simp only [Bool.or_eq_true, List.contains_iff_mem, native_f0b, native_a0, native_appN,
      native_spanList, native_d0] at this
    rcases this with h1 | h1
    · rw [hf] at h1; exact absurd h1 (by decide)
    · exact h1
  · have := List.all_eq_true.1 hd d (by rw [native_d0]; exact hdm)
    simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', List.mem_range, native_a0, native_compOf, native_f0b, native_appN] at this
    rcases this with h1 | ⟨l, hl, x, hx, hf, hlx⟩
    · exact Or.inl h1
    · exact Or.inr ⟨l, hl, x, hx, hf, hlx⟩
  · have := List.all_eq_true.1 hN g (by rw [native_n2Gens]; exact hg)
    rwa [native_gammaUN] at this

theorem frameFixAt_of {i : ℕ} (hi : i = 0 ∨ i = 1) :
    frameFixAt i = true := by
  have hF := Certificates.certificate16971
  simp only [frameFixCheck, Bool.and_eq_true] at hF
  rcases hi with rfl | rfl
  · exact hF.1
  · exact hF.2

theorem fix_of_normalizes
    {i : ℕ} (hi : i = 0 ∨ i = 1) {g : V12 ≃ₗ[ZMod 2] V12}
    (hg : ∀ l, RowsSet (compOf i) (g * l * g⁻¹) ↔ RowsSet (compOf i) l) :
    g (vecOf a0) = vecOf a0 := by
  have hi32 : i < 32 := by omega
  obtain ⟨hfix, ha, -, -, -⟩ := frameFixAt_spec (frameFixAt_of hi)
  have hcg := Certificates.certificate16966
  have hlt : ∀ r ∈ ResPair.compGens i, ∀ y ∈ r, y < 4096 := by
    rcases hi with rfl | rfl <;> decide +kernel
  have hv : ∀ r ∈ ResPair.compGens i, linOfRows r (g (vecOf a0)) = g (vecOf a0) := by
    intro r hr
    obtain ⟨lr, -, hlrr⟩ := hcg i hi32 r hr
    have hlr : RowsSet (compOf i) lr := by
      rw [compOf_eq]; exact rowsSet_subsetProducts hr hlrr
    obtain ⟨r', hr', hr'x⟩ := (hg (g⁻¹ * lr * g)).1 (by
      rw [show g * (g⁻¹ * lr * g) * g⁻¹ = lr by group]; exact hlr)
    have hm : (g⁻¹ * lr * g) (vecOf a0) = vecOf a0 := by
      rw [hr'x, ← vecOf_appN, ha r' hr']
    have := congrArg g hm
    simp only [LinearEquiv.mul_apply, apply_inv_apply] at this
    rw [← hlrr]
    exact this
  have hcode := hfix (codeOf (g (vecOf a0))) (codeOf_lt _) fun r hr => by
    apply vecOf_inj (appN_lt (hlt r hr) _) (codeOf_lt _)
    rw [vecOf_appN, vecOf_codeOf, hv r hr]
  rcases hcode with h0 | h0
  · exfalso
    have : g (vecOf a0) = 0 := by rw [← vecOf_codeOf (g (vecOf a0)), h0, vecOf_zero]
    rw [show (0 : V12) = g 0 from (map_zero g).symm] at this
    have ha0 := g.injective this
    rw [vecOf_eq_zero a0_lt] at ha0
    exact absurd ha0 (by decide)
  · rw [← vecOf_codeOf (g (vecOf a0)), h0]

theorem d0_of_normalizes
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {g : V12 ≃ₗ[ZMod 2] V12} (hgU : g ∈ gammaU) (hfix : g (vecOf a0) = vecOf a0)
    (hg : ∀ l, RowsSet (compOf i) (g * l * g⁻¹) ↔ RowsSet (compOf i) l) :
    ∀ y, g y ∈ spanOf d0 ↔ y ∈ spanOf d0 := by
  have hi32 : i < 32 := by omega
  obtain ⟨-, -, hcomm, hd, -⟩ := frameFixAt_spec (frameFixAt_of hi)
  have key : ∀ (h : V12 ≃ₗ[ZMod 2] V12), h ∈ gammaU → h (vecOf a0) = vecOf a0 →
      (∀ l, RowsSet (compOf i) l → RowsSet (compOf i) (h * l * h⁻¹)) →
      ∀ y ∈ spanOf d0, h y ∈ spanOf d0 := by
    intro h hhU hhfix hhn y hy
    have hle : spanOf d0 ≤ (spanOf d0).comap (h : V12 →ₗ[ZMod 2] V12) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨d, hdm, rfl⟩
      change h (vecOf d) ∈ spanOf d0
      rcases hd d hdm with rfl | ⟨l, hl, x, hx, hf, rfl⟩
      · rw [hhfix]; exact mem_spanOf_of_mem hdm
      · obtain ⟨m, hm⟩ := realized_of_mem_compOf Certificates.certificate16966 hi32 hl
        obtain ⟨r'', hr'', hr''x⟩ := hhn m ⟨l, hl, hm⟩
        have hgx : f0b (codeOf (h (vecOf x))) a0 = false := by
          have h0 : f0 (vecOf x) (vecOf a0) = 0 := by
            rw [f0_vecOf, hf]; rfl
          have h1 : f0 (h (vecOf x)) (vecOf a0) = 0 := by
            rw [← hhfix, f0_gammaU hhU, h0]
          rw [← vecOf_codeOf (h (vecOf x)), f0_vecOf] at h1
          cases hb : f0b (codeOf (h (vecOf x))) a0
          · rfl
          · rw [hb] at h1; exact absurd h1 (by decide)
        have hc := hcomm r'' hr'' _ (codeOf_lt _) hgx
        have hc'' := canon_of_mem_compOf Certificates.certificate16964 hi32 hr''
        rw [mem_spanList_iff d0_lt (xor_lt (appN_lt hc''.2 _) (codeOf_lt _)), vecOf_xor, vecOf_appN,
          vecOf_codeOf, ← hr''x] at hc
        rw [vecOf_xor, vecOf_appN, map_add, ← hm]
        simpa only [LinearEquiv.mul_apply, inv_apply_apply] using hc
    exact hle hy
  have hn : ∀ l, RowsSet (compOf i) l → RowsSet (compOf i) (g * l * g⁻¹) := fun l hl =>
    (hg l).2 hl
  have hni : ∀ l, RowsSet (compOf i) l → RowsSet (compOf i) (g⁻¹ * l * g⁻¹⁻¹) := fun l hl => by
    have := hg (g⁻¹ * l * g⁻¹⁻¹)
    rw [show g * (g⁻¹ * l * g⁻¹⁻¹) * g⁻¹ = l by group] at this
    exact this.1 hl
  have hfixi : g⁻¹ (vecOf a0) = vecOf a0 := by
    calc g⁻¹ (vecOf a0) = g⁻¹ (g (vecOf a0)) := by rw [hfix]
      _ = vecOf a0 := inv_apply_apply g _
  intro y
  constructor
  · intro hy
    have := key g⁻¹ (inv_mem hgU) hfixi hni _ hy
    rwa [inv_apply_apply] at this
  · exact key g hgU hfix hn y

theorem nlMem_of_normalizes
    {i : ℕ} (hi : i = 0 ∨ i = 1) {g : V12 ≃ₗ[ZMod 2] V12} (hgU : g ∈ gammaU)
    (hg : ∀ l, RowsSet (compOf i) (g * l * g⁻¹) ↔ RowsSet (compOf i) l) : NLMem i g :=
  ⟨hgU, fix_of_normalizes hi hg, d0_of_normalizes hi hgU (fix_of_normalizes hi hg) hg, hg⟩

theorem n2_le_gammaU {i : ℕ} (hi : i = 0 ∨ i = 1) :
    ResPair.n2 i ≤ gammaU := by
  obtain ⟨-, -, -, -, hN⟩ := frameFixAt_spec (frameFixAt_of hi)
  refine (Subgroup.closure_le _).2 fun l ⟨r, hr, hl⟩ => ?_
  have : l = toU r (hN r hr) := LinearEquiv.ext fun x => by rw [hl, toU_apply]
  rw [SetLike.mem_coe, this]
  exact gammaUN_spec (hN r hr)

end CFSG.GF2Type.Smith1979.GammaU.StepA
