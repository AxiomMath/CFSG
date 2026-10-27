module

public import CFSG.GF2Type.Smith1979.GammaU.Step4
public import CFSG.GF2Type.Smith1979.GammaU.FrameFix
public import CFSG.GF2Type.Smith1979.GammaU.Sigma

public section

namespace CFSG.GF2Type.Smith1979.GammaU.StepA

open CFSG.GF2Type.Smith1979.GammaU

theorem unitaryN_of_unitary {r : Array ℕ} (hr : Canon r)
    (h : ∀ x, linOfRows r (theta0 x) = theta0 (linOfRows r x)) : unitaryN r = true := by
  simp only [unitaryN, List.all_eq_true, List.mem_range, beq_iff_eq]
  intro j hj
  have hj' : (2 : ℕ) ^ j < 4096 :=
    lt_of_lt_of_le (Nat.pow_lt_pow_right (by norm_num) hj) (by norm_num)
  apply vecOf_inj (appN_lt hr.2 _) (theta0N_lt (appN_lt hr.2 _))
  rw [vecOf_appN, vecOf_theta0N hj', h, vecOf_theta0N (appN_lt hr.2 _), vecOf_appN]

theorem linOfRows_ne_idR {r : Array ℕ} (hr : Canon r) (hne : r ≠ idR) :
    ∃ x, linOfRows r x ≠ x := by
  by_contra h
  push Not at h
  exact hne (rows_eq hr.1 rfl hr.2 (by decide) fun x => by rw [h x, linOfRows_idR])

theorem mem_unitaryElts {i : ℕ} {r : Array ℕ} (hr : r ∈ compOf i) (hc : Canon r) (hne : r ≠ idR)
    (hu : ∀ x, linOfRows r (theta0 x) = theta0 (linOfRows r x)) : r ∈ unitaryElts i := by
  simp only [unitaryElts, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq]
  exact ⟨hr, hne, unitaryN_of_unitary hc hu⟩

theorem ConfigOf.conj {i : ℕ} {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {h : V12 ≃ₗ[ZMod 2] V12}
    (hh : NLMem i h) {r r0 : Array ℕ} (hr0c : Canon r0)
    (hrr : ∀ y, linOfRows r0 y = h (linOfRows r (h⁻¹ y))) {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hc : ConfigOf i M r Le) :
    ConfigOf i (M.map (MulAut.conj h).toMonoidHom) r0 (Le.map (MulAut.conj h).toMonoidHom) := by
  obtain ⟨n, hn, De, H, ⟨l, hl, hlr⟩, ha, hle, hcard⟩ := hc
  have hn' := colPts_conj hh.inv hr0c (fun y => by rw [hrr, inv_inv]) hn
  rw [inv_inv] at hn'
  have H' := H.conj hh.mem
  rw [← vecOf_codeOf (h (vecOf n))] at H'
  refine ⟨_, hn', _, H', ⟨h * l * h⁻¹, mem_map_conj.2 ⟨l, hl, rfl⟩, fun y => ?_⟩,
    ⟨vecOf a0, ha, hh.fix⟩, Subgroup.map_mono hle, ?_⟩
  · rw [hrr, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hlr]
  · rw [candGrp, ← closure_conj hh Le, Subgroup.card_map_of_injective (MulAut.conj h).injective]
    exact hcard

theorem ConfigOf.mono {i : ℕ} {M M' : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hMM : M ≤ M')
    {r : Array ℕ} {Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hc : ConfigOf i M r Le) :
    ConfigOf i M' r Le := by
  obtain ⟨n, hn, De, H, hs, ha, hle, hcard⟩ := hc
  exact ⟨n, hn, De, H, hs, ha, hle.trans hMM, hcard⟩

theorem exists_rows_conj_unitary
    {i : ℕ} (hi : i = 0 ∨ i = 1) {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h) {r : Array ℕ}
    (hr : r ∈ unitaryElts i) :
    ∃ r0 ∈ unitaryElts i, ∀ y, linOfRows r0 y = h (linOfRows r (h⁻¹ y)) := by
  have hi32 : i < 32 := by omega
  obtain ⟨hrc, hne, hun⟩ := by
    simpa only [unitaryElts, List.mem_filter, Bool.and_eq_true, bne_iff_ne, ne_eq] using hr
  obtain ⟨l, hl, r0, hr0, hr0l⟩ := exists_rows_conj Certificates.certificate16966 hi32 hh hrc
  have hc0 := canon_of_mem_compOf Certificates.certificate16964 hi32 hr0
  have hcr := canon_of_mem_compOf Certificates.certificate16964 hi32 hrc
  have hrel : ∀ y, linOfRows r0 y = h (linOfRows r (h⁻¹ y)) := fun y => by
    rw [← hr0l, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hl]
  refine ⟨r0, mem_unitaryElts hr0 hc0 ?_ ?_, hrel⟩
  · rintro rfl
    obtain ⟨x, hx⟩ := linOfRows_ne_idR hcr hne
    apply hx
    have := hrel (h x)
    rw [linOfRows_idR, inv_apply_apply] at this
    exact h.injective this.symm
  · intro x
    rw [hrel, hrel]
    exact unitary_conj hh.mem (unitary_spec hcr.2 hun) x

structure Step5Hyp (i : ℕ) (M : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Prop extends Step4Hyp i M where
  n2_le : ResPair.n2 i ≤ M
  config : ∀ r ∈ unitaryElts i, ∀ u₁ ∈ M, ∀ u₂ ∈ M, Viol.InFrame (compOf i) u₁ r →
    Viol.InFrame (compOf i) u₂ r → Viol.F4Indep (u₁ (vecOf a0)) (u₂ (vecOf a0)) →
      HasConfig i M r

theorem no_violation_hyp10
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step5Hyp i M) {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hN : N ≤ M) : ¬ Viol.Violation N (compOf i) (idR :: ResPair.hyp10 i) := by
  have hi32 : i < 32 := by omega
  rintro (hv | ⟨r, hr, hu, hrH, u₁, hu₁, u₂, hu₂, hf₁, hf₂, hind⟩ | hv)
  · exact hM.noViol N hN (Or.inl hv)
  · have hc := canon_of_mem_compOf Certificates.certificate16964 hi32 hr
    have hne : r ≠ idR := fun h => hrH (h ▸ List.mem_cons_self)
    have hrH' : r ∉ ResPair.hyp10 i := fun h => hrH (List.mem_cons_of_mem _ h)
    have hrU := mem_unitaryElts hr hc hne hu
    exact hrH' (mem_hyp10_of_hasConfig hi hM.toStep4Hyp hM.n2_le hrU
      (hM.config r hrU u₁ (hN hu₁) u₂ (hN hu₂) hf₁ hf₂ hind))
  · exact hM.noViol N hN (Or.inr (Or.inr hv))

@[expose] def N2Rep (i : ℕ) (M : Subgroup (V12 ≃ₗ[ZMod 2] V12)) : Prop :=
  ∃ r₁ ∈ unitaryElts i, ∃ r₂ ∈ unitaryElts i, r₁ ≠ r₂ ∧
    ∃ Le₁ Le₂ : Subgroup (V12 ≃ₗ[ZMod 2] V12), ConfigOf i M r₁ Le₁ ∧ ConfigOf i M r₂ Le₂ ∧
      candGrp i Le₁ ⊔ candGrp i Le₂ = ResPair.n2 i

theorem map_conj_le {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {g : V12 ≃ₗ[ZMod 2] V12} (hg : g ∈ M) :
    M.map (MulAut.conj g).toMonoidHom ≤ M := by
  rintro _ ⟨x, hx, rfl⟩
  exact mul_mem (mul_mem hg hx) (inv_mem hg)

theorem map_conj_eq_of_mem {N : Subgroup (V12 ≃ₗ[ZMod 2] V12)} {g : V12 ≃ₗ[ZMod 2] V12}
    (hg : g ∈ N) : N.map (MulAut.conj g).toMonoidHom = N := by
  refine le_antisymm (map_conj_le hg) fun x hx => ?_
  exact mem_map_conj.2 ⟨g⁻¹ * x * g, mul_mem (mul_mem (inv_mem hg) hx) hg, by group⟩

theorem candGrp_conj {i : ℕ} {h : V12 ≃ₗ[ZMod 2] V12} (hh : NLMem i h)
    (Le : Subgroup (V12 ≃ₗ[ZMod 2] V12)) :
    candGrp i (Le.map (MulAut.conj h).toMonoidHom) =
      (candGrp i Le).map (MulAut.conj h).toMonoidHom :=
  (closure_conj hh Le).symm

theorem rows_conj_ne {i : ℕ} (hi : i = 0 ∨ i = 1)
    {h : V12 ≃ₗ[ZMod 2] V12} {r₁ r₂ r₁' r₂' : Array ℕ} (hr₁ : r₁ ∈ unitaryElts i)
    (hr₂ : r₂ ∈ unitaryElts i) (hne : r₁ ≠ r₂)
    (h₁ : ∀ y, linOfRows r₁' y = h (linOfRows r₁ (h⁻¹ y)))
    (h₂ : ∀ y, linOfRows r₂' y = h (linOfRows r₂ (h⁻¹ y))) : r₁' ≠ r₂' := by
  have hi32 : i < 32 := by omega
  rintro rfl
  have hc₁ := canon_of_mem_compOf Certificates.certificate16964 hi32 (List.mem_filter.1 hr₁).1
  have hc₂ := canon_of_mem_compOf Certificates.certificate16964 hi32 (List.mem_filter.1 hr₂).1
  refine hne (rows_eq hc₁.1 hc₂.1 hc₁.2 hc₂.2 fun y => h.injective ?_)
  have e := (h₁ (h y)).symm.trans (h₂ (h y))
  rwa [inv_apply_apply] at e

theorem eqvOf_idR (h1 : mulR idR (Viol.invR idR) = idR) (h2 : mulR (Viol.invR idR) idR = idR) :
    Viol.eqvOf idR (Viol.invR idR) h1 h2 = 1 :=
  LinearEquiv.ext fun x => by rw [Viol.eqvOf_apply, linOfRows_idR]; rfl

theorem exists_normalized
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step4Hyp i M) {r₁ r₂ : Array ℕ}
    (hr₁ : r₁ ∈ unitaryElts i) (hr₂ : r₂ ∈ unitaryElts i) (hne : r₁ ≠ r₂)
    (hc₁ : HasConfig i M r₁) (hc₂ : HasConfig i M r₂) :
    ∃ g : V12 ≃ₗ[ZMod 2] V12, NLMem i g ∧ Step4Hyp i (M.map (MulAut.conj g).toMonoidHom) ∧
      N2Rep i (M.map (MulAut.conj g).toMonoidHom) := by
  have hi32 : i < 32 := by omega
  obtain ⟨Le₁, hC₁⟩ := hc₁
  obtain ⟨Le₂, hC₂⟩ := hc₂
  obtain ⟨n₁, hn₁, De₁, H₁, hs₁, ha₁, hle₁, hcard₁⟩ := hC₁
  obtain ⟨n₂, hn₂, De₂, H₂, hs₂, ha₂, hle₂, hcard₂⟩ := hC₂
  have hsup : candGrp i Le₁ ⊔ candGrp i Le₂ ≤ M :=
    sup_le (candGrp_le hM hle₁) (candGrp_le hM hle₂)
  rcases pair_census hi hr₁ hr₂ hne hn₁ hn₂ H₁ H₂ hs₁ hs₂ ha₁ ha₂ hcard₁ hcard₂ with hv | hres
  · exact absurd hv (hM.noViol _ hsup)
  obtain ⟨c, hc, h1, h2, heq⟩ := hres
  set e := Viol.eqvOf c (Viol.invR c) h1 h2
  have he := resConj_nlMem hi hc h1 h2
  refine ⟨e⁻¹, he.inv, hM.conj_resConj hi hc h1 h2, ?_⟩
  obtain ⟨r₁', hr₁', hrr₁⟩ := exists_rows_conj_unitary hi he.inv hr₁
  obtain ⟨r₂', hr₂', hrr₂⟩ := exists_rows_conj_unitary hi he.inv hr₂
  have hc₁' := canon_of_mem_compOf Certificates.certificate16964 hi32
    (List.mem_filter.1 hr₁').1
  have hc₂' := canon_of_mem_compOf Certificates.certificate16964 hi32
    (List.mem_filter.1 hr₂').1
  refine ⟨r₁', hr₁', r₂', hr₂', rows_conj_ne hi hr₁ hr₂ hne hrr₁ hrr₂, _, _,
    ConfigOf.conj he.inv hc₁' hrr₁ ⟨n₁, hn₁, De₁, H₁, hs₁, ha₁, hle₁, hcard₁⟩,
    ConfigOf.conj he.inv hc₂' hrr₂ ⟨n₂, hn₂, De₂, H₂, hs₂, ha₂, hle₂, hcard₂⟩, ?_⟩
  rw [candGrp_conj he.inv, candGrp_conj he.inv, ← Subgroup.map_sup, heq, map_conj_map_conj,
    inv_mul_cancel, show (MulAut.conj (1 : V12 ≃ₗ[ZMod 2] V12)).toMonoidHom = MonoidHom.id _ by
      ext; simp, Subgroup.map_id]

@[expose] def FrameCensus (i : ℕ) : Prop :=
  ∀ {x : V12} {D : Submodule (ZMod 2) V12} {F : Subgroup (V12 ≃ₗ[ZMod 2] V12)}, Hyp x D F →
    (∃ n ∈ ResPair.n2 i, ∀ l, l ∈ F ↔ RowsSet (compOf i) (n⁻¹ * l * n)) ∨
      Viol.Violation (ResPair.n2 i ⊔ F) (compOf i) (idR :: ResPair.hyp10 i)

@[expose] def ResidualPairs (i : ℕ) : Prop :=
  ∀ c ∈ ResPair.resConj i, c ≠ idR → ∃ (h1 : mulR c (Viol.invR c) = idR)
    (h2 : mulR (Viol.invR c) c = idR),
    Viol.Violation (ResPair.n2 i ⊔
      (ResPair.n2 i).map (MulAut.conj (Viol.eqvOf c (Viol.invR c) h1 h2)).toMonoidHom)
      (compOf i) (idR :: ResPair.hyp10 i)

theorem decomp
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step5Hyp i M) (hD : FrameCensus i)
    {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hL : ∀ l, l ∈ L ↔ RowsSet (compOf i) l)
    (HL : Hyp (vecOf a0) (spanOf d0) L) {k : V12 ≃ₗ[ZMod 2] V12} (hkM : k ∈ M)
    (hkU : k ∈ gammaU) : ∃ n ∈ ResPair.n2 i, ∃ g ∈ M, NLMem i g ∧ k = n * g := by
  have hLM : L ≤ M := fun l hl => hM.frame l ((hL l).1 hl)
  have hFM : L.map (MulAut.conj k).toMonoidHom ≤ M := by
    rintro _ ⟨l, hl, rfl⟩
    exact mul_mem (mul_mem hkM (hLM hl)) (inv_mem hkM)
  rcases hD (HL.conj hkU) with ⟨n, hn, hnF⟩ | hv
  · have hnM := hM.n2_le hn
    refine ⟨n, hn, n⁻¹ * k, mul_mem (inv_mem hnM) hkM, nlMem_of_normalizes hi
      (mul_mem (inv_mem (n2_le_gammaU hi hn)) hkU) fun l => ?_, by group⟩
    rw [show n⁻¹ * k * l * (n⁻¹ * k)⁻¹ = n⁻¹ * (k * l * k⁻¹) * n by group, ← hnF, mem_map_conj,
      ← hL]
    constructor
    · rintro ⟨l', hl', he⟩
      rw [show l = l' from mul_left_cancel (mul_right_cancel he).symm]
      exact hl'
    · intro hl
      exact ⟨l, hl, rfl⟩
  · exact absurd hv (no_violation_hyp10 hi hM (sup_le hM.n2_le hFM))

theorem normalizes_n2
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step5Hyp i M) (hrep : N2Rep i M)
    (hD : ResidualPairs i) {g : V12 ≃ₗ[ZMod 2] V12} (hgM : g ∈ M) (hg : NLMem i g) :
    (ResPair.n2 i).map (MulAut.conj g).toMonoidHom = ResPair.n2 i := by
  have hi32 : i < 32 := by omega
  obtain ⟨r₁, hr₁, r₂, hr₂, hne, Le₁, Le₂, hC₁, hC₂, hrep⟩ := hrep
  obtain ⟨r₁', hr₁', hrr₁⟩ := exists_rows_conj_unitary hi hg hr₁
  obtain ⟨r₂', hr₂', hrr₂⟩ := exists_rows_conj_unitary hi hg hr₂
  have hc₁' := canon_of_mem_compOf Certificates.certificate16964 hi32
    (List.mem_filter.1 hr₁').1
  have hc₂' := canon_of_mem_compOf Certificates.certificate16964 hi32
    (List.mem_filter.1 hr₂').1
  obtain ⟨n₁, hn₁, De₁, H₁, hs₁, ha₁, hle₁, hcard₁⟩ :=
    (hC₁.conj hg hc₁' hrr₁).mono (map_conj_le hgM)
  obtain ⟨n₂, hn₂, De₂, H₂, hs₂, ha₂, hle₂, hcard₂⟩ :=
    (hC₂.conj hg hc₂' hrr₂).mono (map_conj_le hgM)
  have hsup : candGrp i (Le₁.map (MulAut.conj g).toMonoidHom) ⊔
      candGrp i (Le₂.map (MulAut.conj g).toMonoidHom) =
      (ResPair.n2 i).map (MulAut.conj g).toMonoidHom := by
    rw [candGrp_conj hg, candGrp_conj hg, ← Subgroup.map_sup, hrep]
  have hgN : (ResPair.n2 i).map (MulAut.conj g).toMonoidHom ≤ M :=
    (Subgroup.map_mono hM.n2_le).trans (map_conj_le hgM)
  rcases pair_census hi hr₁' hr₂' (rows_conj_ne hi hr₁ hr₂ hne hrr₁ hrr₂) hn₁ hn₂ H₁ H₂ hs₁ hs₂
      ha₁ ha₂ hcard₁ hcard₂ with hv | hres
  · rw [hsup] at hv
    exact absurd hv (hM.noViol _ hgN)
  rw [hsup] at hres
  obtain ⟨c, hc, h1, h2, heq⟩ := hres
  by_cases hc1 : c = idR
  · subst hc1
    rw [heq, eqvOf_idR, show (MulAut.conj (1 : V12 ≃ₗ[ZMod 2] V12)).toMonoidHom = MonoidHom.id _ by
      ext; simp, Subgroup.map_id]
  · obtain ⟨h1', h2', hv⟩ := hD c hc hc1
    rw [← heq] at hv
    exact absurd hv (no_violation_hyp10 hi hM (sup_le hM.n2_le hgN))

theorem step5
    {i : ℕ} (hi : i = 0 ∨ i = 1)
    {M : Subgroup (V12 ≃ₗ[ZMod 2] V12)} (hM : Step5Hyp i M) (hrep : N2Rep i M)
    (hD' : FrameCensus i) (hD'' : ResidualPairs i) {L : Subgroup (V12 ≃ₗ[ZMod 2] V12)}
    (hL : ∀ l, l ∈ L ↔ RowsSet (compOf i) l) (HL : Hyp (vecOf a0) (spanOf d0) L)
    {k : V12 ≃ₗ[ZMod 2] V12} (hkM : k ∈ M) (hkU : k ∈ gammaU) :
    (ResPair.n2 i).map (MulAut.conj k).toMonoidHom = ResPair.n2 i ∧
      ∃ y ∈ SigmaP.s45 i, k (vecOf a0) = vecOf y := by
  obtain ⟨n, hn, g, hgM, hg, rfl⟩ := decomp hi hM hD' hL HL hkM hkU
  refine ⟨?_, ?_⟩
  · rw [← map_conj_map_conj, normalizes_n2 hi hM hrep hD'' hgM hg, map_conj_eq_of_mem hn]
  · rw [LinearEquiv.mul_apply, hg.fix]
    exact SigmaP.orbit_subset hi n hn

end CFSG.GF2Type.Smith1979.GammaU.StepA
