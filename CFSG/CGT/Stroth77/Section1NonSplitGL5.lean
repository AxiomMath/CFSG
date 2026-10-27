module

public import CFSG.CGT.Stroth77.Section1NonSplitSetup
public import CFSG.CGT.Stroth77.Section1GL5

public section

namespace CFSG.CGT.Stroth77

open Subgroup GL5

variable {G : Type*} [Group G] (ι : ↥Tsp →* G)

abbrev trSAspCommGroup : CommGroup ↥(trS ι Asp) :=
  { (inferInstance : Group ↥(trS ι Asp)) with
    mul_comm := fun a b => Subtype.ext (trS_Asp_comm a.2 b.2) }

attribute [local instance] trSAspCommGroup

@[expose] noncomputable def basisA (i : Fin 5) : ↥(trS ι Asp) :=
  ⟨ιe ι (spBasis i), ιe_mem_trS (spBasis_mem_Asp i) (Asp_le_Tsp (spBasis_mem_Asp i))⟩

theorem coe_basisA (i : Fin 5) : (basisA ι i : G) = ιe ι (spBasis i) := rfl

theorem coe_Φ_basisA (r : Nat) :
    ((Φ (basisA ι) r : ↥(trS ι Asp)) : G) = ιe ι (spPhi r) := by
  rw [ιe_spPhi, Φ, Fin.prod_univ_five]
  simp only [Subgroup.coe_mul, apply_ite (fun a : ↥(trS ι Asp) => (a : G)), Subgroup.coe_one,
    coe_basisA]
  rfl

theorem sq_trS_Asp (a : ↥(trS ι Asp)) : a * a = 1 := Subtype.ext (trS_Asp_sq a.2)

theorem closure_basisA : closure (Set.range (basisA ι)) = ⊤ := by
  refine eq_top_iff.2 fun a _ => ?_
  obtain ⟨m, hmA, hmT, hm⟩ := mem_trS.1 a.2
  obtain ⟨r, -, rfl⟩ := exists_spPhi_eq hmA
  have : a = Φ (basisA ι) r := Subtype.ext (by rw [coe_Φ_basisA, hm])
  rw [this, Φ]
  refine prod_mem fun j _ => ?_
  split_ifs
  · exact subset_closure ⟨j, rfl⟩
  · exact one_mem _

variable {ι}

theorem normalizer_range_le_normalizer_trS_Asp (hι : Function.Injective ι) :
    normalizer (ι.range : Set G) ≤ normalizer (trS ι Asp : Set G) := by
  intro s hs
  have hs' := mem_normalizer_iff.1 hs
  have hB : (trS ι Asp).map (MulAut.conj s).toMonoidHom = trS ι Asp := by
    refine eq_trS_Asp hι _ ?_ ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      exact (hs' a).1 (trS_le_range _ ha)
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have := trS_Asp_comm ha hb
      calc s * a * s⁻¹ * (s * b * s⁻¹) = s * (a * b) * s⁻¹ := by group
        _ = s * (b * a) * s⁻¹ := by rw [this]
        _ = s * b * s⁻¹ * (s * a * s⁻¹) := by group
    · rw [card_map_of_injective (MulAut.conj s).injective, card_trS_Asp hι]
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← hB]; exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← hB] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hyx
    have : y = x := mul_left_cancel (mul_right_cancel hyx)
    rw [← this]; exact hy

theorem range_le_normalizer_trS_Asp (hι : Function.Injective ι) :
    ι.range ≤ normalizer (trS ι Asp : Set G) :=
  le_normalizer.trans (normalizer_range_le_normalizer_trS_Asp hι)

abbrev Mconj (g : normalizer (trS ι Asp : Set G)) : MulAut ↥(trS ι Asp) :=
  (trS ι Asp).normalizerMonoidHom g

theorem coe_Mconj_apply (g : normalizer (trS ι Asp : Set G)) (a : ↥(trS ι Asp)) :
    ((Mconj g a : ↥(trS ι Asp)) : G) = (g : G) * a * (g : G)⁻¹ :=
  normalizerMonoidHom_apply_apply_coe _ g a

theorem code_Mconj_eq (hι : Function.Injective ι) (g : normalizer (trS ι Asp : Set G)) {c : Nat}
    (hc : c < N) (h0 : (g : G) * ιe ι spX1 * (g : G)⁻¹ = ιe ι (spPhi (r0 c)))
    (h1 : (g : G) * ιe ι spY1 * (g : G)⁻¹ = ιe ι (spPhi (r1 c)))
    (h2 : (g : G) * ιe ι spX * (g : G)⁻¹ = ιe ι (spPhi (r2 c)))
    (h3 : (g : G) * ιe ι spY * (g : G)⁻¹ = ιe ι (spPhi (r3 c)))
    (h4 : (g : G) * ιe ι spW * (g : G)⁻¹ = ιe ι (spPhi (r4 c))) :
    code (basisA ι) (Mconj g) = c := by
  refine code_eq_of_apply (sq_trS_Asp ι) (closure_basisA ι) (card_trS_Asp hι) hc ?_ ?_ ?_ ?_ ?_ <;>
  · apply Subtype.ext
    rw [coe_Mconj_apply, coe_Φ_basisA]
    first | exact h0 | exact h1 | exact h2 | exact h3 | exact h4

noncomputable def nA (hι : Function.Injective ι) {m : Msp} (hm : m ∈ Tsp) :
    normalizer (trS ι Asp : Set G) :=
  ⟨ιe ι m, range_le_normalizer_trS_Asp hι (ιe_mem_range hm)⟩

theorem code_of_act (hι : Function.Injective ι) {m : Msp} (hm : m ∈ Tsp) {c : Nat} (hc : c < N)
    (h : m * spX1 * m⁻¹ = spPhi (r0 c) ∧ m * spY1 * m⁻¹ = spPhi (r1 c) ∧
      m * spX * m⁻¹ = spPhi (r2 c) ∧ m * spY * m⁻¹ = spPhi (r3 c) ∧
      m * spW * m⁻¹ = spPhi (r4 c)) :
    code (basisA ι) (Mconj (nA hι hm)) = c := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  refine code_Mconj_eq hι _ hc ?_ ?_ ?_ ?_ ?_ <;> simp only [nA]
  · rw [ιe_conj hm spX1_mem_Tsp, h0]
  · rw [ιe_conj hm spY1_mem_Tsp, h1]
  · rw [ιe_conj hm spX_mem_Tsp, h2]
  · rw [ιe_conj hm spY_mem_Tsp, h3]
  · rw [ιe_conj hm spW_mem_Tsp, h4]

theorem code_uv (hι : Function.Injective ι) :
    code (basisA ι) (Mconj (nA hι spUV_mem_Tsp)) = uvC :=
  code_of_act hι spUV_mem_Tsp (by decide) act_spUV
theorem code_t (hι : Function.Injective ι) :
    code (basisA ι) (Mconj (nA hι spT_mem_Tsp)) = tC :=
  code_of_act hι spT_mem_Tsp (by decide) act_spT
theorem code_u (hι : Function.Injective ι) :
    code (basisA ι) (Mconj (nA hι spU_mem_Tsp)) = uC :=
  code_of_act hι spU_mem_Tsp (by decide) act_spU

theorem Mconj_eq_one_of_mem (g : normalizer (trS ι Asp : Set G)) (hg : (g : G) ∈ trS ι Asp) :
    Mconj g = 1 := by
  ext a
  rw [coe_Mconj_apply, MulAut.one_apply, trS_Asp_comm hg a.2, mul_inv_cancel_right]

theorem Mconj_mul (g h : normalizer (trS ι Asp : Set G)) : Mconj (g * h) = Mconj g * Mconj h :=
  map_mul _ g h

theorem Mconj_one : Mconj (1 : normalizer (trS ι Asp : Set G)) = 1 := map_one _

theorem Mconj_inv (g : normalizer (trS ι Asp : Set G)) : Mconj g⁻¹ = (Mconj g)⁻¹ := map_inv _ g

theorem nA_mul (hι : Function.Injective ι) {a b : Msp} (ha : a ∈ Tsp) (hb : b ∈ Tsp) :
    nA hι (mul_mem ha hb) = nA hι ha * nA hι hb := Subtype.ext (ιe_mul ha hb)

theorem nA_inv (hι : Function.Injective ι) {a : Msp} (ha : a ∈ Tsp) :
    nA hι (inv_mem ha) = (nA hι ha)⁻¹ := Subtype.ext (ιe_inv ha)

theorem code_nA_mem_dCodes (hι : Function.Injective ι) {d : Msp} (hd : d ∈ Dsp) :
    code (basisA ι) (Mconj (nA hι (Dsp_le_Tsp hd))) ∈ dCodes := by
  have hsq := sq_trS_Asp ι
  have hgen := closure_basisA ι
  have hcard := card_trS_Asp hι
  induction hd using Subgroup.closure_induction with
  | mem x hx =>
    simp only [gensDsp, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
    rcases hx with rfl | rfl | rfl
    · rw [code_uv hι]; exact uvC_mem_dCodes
    · rw [code_t hι]; exact tC_mem_dCodes
    · rw [code_u hι]; exact uC_mem_dCodes
  | one =>
    have : Mconj (nA hι (Dsp_le_Tsp (one_mem Dsp))) = 1 := by
      rw [show nA hι (Dsp_le_Tsp (one_mem Dsp)) = 1 from Subtype.ext ιe_one, Mconj_one]
    rw [this, code_one hsq hgen hcard]; exact idC_mem_dCodes
  | mul x y hx hy ihx ihy =>
    have : nA hι (Dsp_le_Tsp (mul_mem hx hy)) = nA hι (Dsp_le_Tsp hx) * nA hι (Dsp_le_Tsp hy) :=
      nA_mul hι _ _
    rw [this, Mconj_mul, code_mul hsq hgen hcard]
    exact mulC_mem_dCodes _ ihx _ ihy
  | inv x hx ihx =>
    have e : nA hι (Dsp_le_Tsp (inv_mem hx)) = (nA hι (Dsp_le_Tsp hx))⁻¹ := nA_inv hι _
    set f := Mconj (nA hι (Dsp_le_Tsp hx))
    have h8 : f ^ 8 = 1 := code_inj hsq hgen (by
      rw [code_pow hsq hgen hcard, powC_eight_dCodes _ ihx, code_one hsq hgen hcard])
    have hf : f⁻¹ = f ^ 7 := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, h8]
    rw [e, Mconj_inv, hf, code_pow hsq hgen hcard]
    exact powC_seven_mem_dCodes _ ihx

theorem code_mem_dCodes (hι : Function.Injective ι) (g : normalizer (trS ι Asp : Set G))
    (hg : (g : G) ∈ ι.range) : code (basisA ι) (Mconj g) ∈ dCodes := by
  obtain ⟨d, hdD, hdT, hgd⟩ := exists_Dsp_mul_mem hι hg
  have : Mconj g = Mconj (nA hι hdT) := by
    have e : g = (g * (nA hι hdT)⁻¹) * nA hι hdT := by group
    rw [e, Mconj_mul, Mconj_eq_one_of_mem _ (by simpa [nA] using hgd), one_mul]
  rw [this]
  exact code_nA_mem_dCodes hι hdD

theorem eq_of_Mconj_eq_one (g : normalizer (trS ι Asp : Set G)) (h : Mconj g = 1) :
    ∀ a ∈ trS ι Asp, (g : G) * a = a * g := by
  intro a ha
  have := congrArg (fun f : MulAut ↥(trS ι Asp) => ((f ⟨a, ha⟩ : ↥(trS ι Asp)) : G)) h
  simp only [coe_Mconj_apply, MulAut.one_apply] at this
  calc (g : G) * a = (g : G) * a * (g : G)⁻¹ * g := by group
    _ = a * g := by rw [this]

theorem code_nA_mem_vCodes (hι : Function.Injective ι) {m : Msp} (hm : m ∈ AEsp) :
    code (basisA ι) (Mconj (nA hι (AEsp_le_Tsp hm))) ∈ vCodes := by
  have hsq := sq_trS_Asp ι
  have hgen := closure_basisA ι
  have hcard := card_trS_Asp hι
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    simp only [gensAEsp, List.mem_cons, List.not_mem_nil, or_false, Set.mem_setOf_eq] at hx
    have hA : ∀ {a : Msp} (ha : a ∈ Asp) (haT : a ∈ AEsp),
        code (basisA ι) (Mconj (nA hι (AEsp_le_Tsp haT))) ∈ vCodes := by
      intro a ha haT
      rw [Mconj_eq_one_of_mem _ (ιe_mem_trS ha (Asp_le_Tsp ha)), code_one hsq hgen hcard]
      decide
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact hA spX1_mem_Asp (Asp_le_AEsp spX1_mem_Asp)
    · exact hA spY1_mem_Asp (Asp_le_AEsp spY1_mem_Asp)
    · exact hA spX_mem_Asp (Asp_le_AEsp spX_mem_Asp)
    · exact hA spY_mem_Asp (Asp_le_AEsp spY_mem_Asp)
    · exact hA spW_mem_Asp (Asp_le_AEsp spW_mem_Asp)
    · rw [code_uv hι]; decide
    · rw [code_t hι]; decide
  | one =>
    have : Mconj (nA hι (AEsp_le_Tsp (one_mem AEsp))) = 1 := by
      rw [show nA hι (AEsp_le_Tsp (one_mem AEsp)) = 1 from Subtype.ext ιe_one, Mconj_one]
    rw [this, code_one hsq hgen hcard]; decide
  | mul x y hx hy ihx ihy =>
    rw [show nA hι (AEsp_le_Tsp (mul_mem hx hy)) =
      nA hι (AEsp_le_Tsp hx) * nA hι (AEsp_le_Tsp hy) from nA_mul hι _ _, Mconj_mul,
      code_mul hsq hgen hcard]
    exact mulC_mem_vCodes _ ihx _ ihy
  | inv x hx ihx =>
    set f := Mconj (nA hι (AEsp_le_Tsp hx))
    have h2 : f ^ 2 = 1 := code_inj hsq hgen (by
      rw [code_pow hsq hgen hcard, powC_two_vCodes _ ihx, code_one hsq hgen hcard])
    have hf : f⁻¹ = f := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← sq, h2]
    rw [show nA hι (AEsp_le_Tsp (inv_mem hx)) = (nA hι (AEsp_le_Tsp hx))⁻¹ from nA_inv hι _,
      Mconj_inv, hf]
    exact ihx

theorem mem_trS_AEsp_of_code (hι : Function.Injective ι) (g : normalizer (trS ι Asp : Set G))
    (hg : (g : G) ∈ ι.range) (hc : code (basisA ι) (Mconj g) ∈ vCodes) :
    (g : G) ∈ trS ι AEsp := by
  have hsq := sq_trS_Asp ι
  have hgen := closure_basisA ι
  have hcard := card_trS_Asp hι
  obtain ⟨e', he'E, he'T, he'⟩ : ∃ e', e' ∈ Esp ∧ ∃ he'T : e' ∈ Tsp,
      code (basisA ι) (Mconj (nA hι he'T)) = code (basisA ι) (Mconj g) := by
    simp only [vCodes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h
    · refine ⟨1, one_mem _, one_mem _, ?_⟩
      rw [h, show nA hι (one_mem Tsp) = 1 from Subtype.ext ιe_one, Mconj_one,
        code_one hsq hgen hcard]
    · exact ⟨spUV, spUV_mem_Esp, spUV_mem_Tsp, by rw [h, code_uv hι]⟩
    · exact ⟨spT, spT_mem_Esp, spT_mem_Tsp, by rw [h, code_t hι]⟩
    · refine ⟨spUV * spT, mul_mem spUV_mem_Esp spT_mem_Esp, mul_mem spUV_mem_Tsp spT_mem_Tsp, ?_⟩
      rw [h, nA_mul hι spUV_mem_Tsp spT_mem_Tsp, Mconj_mul, code_mul hsq hgen hcard, code_uv hι,
        code_t hι, mulC_uvC_tC]
  have he : Mconj (g * (nA hι he'T)⁻¹) = 1 := by
    rw [Mconj_mul, Mconj_inv, code_inj hsq hgen he'.symm, mul_inv_cancel]
  have hA : (g : G) * (ιe ι e')⁻¹ ∈ trS ι Asp := by
    refine mem_trS_Asp_of_commute hι (mul_mem hg (inv_mem (ιe_mem_range he'T))) ?_
    exact eq_of_Mconj_eq_one _ he
  have : (g : G) = (g : G) * (ιe ι e')⁻¹ * ιe ι e' := by group
  rw [this]
  exact mul_mem (trS_mono Asp_le_AEsp hA) (ιe_mem_trS (Esp_le_AEsp he'E) he'T)

theorem mem_normalizer_trS_AEsp (hι : Function.Injective ι) {g : G}
    (hg : g ∈ normalizer (ι.range : Set G)) : g ∈ normalizer (trS ι AEsp : Set G) := by
  have hsq := sq_trS_Asp ι
  have hgen := closure_basisA ι
  have hcard := card_trS_Asp hι
  suffices key : ∀ g : G, g ∈ normalizer (ι.range : Set G) →
      ∀ y ∈ trS ι AEsp, g * y * g⁻¹ ∈ trS ι AEsp by
    rw [mem_normalizer_iff]
    intro y
    refine ⟨key g hg y, fun h => ?_⟩
    have := key g⁻¹ (inv_mem hg) _ h
    simpa [mul_assoc] using this
  clear hg g
  intro g hg y hy
  have hgS := mem_normalizer_iff.1 hg
  set gA : normalizer (trS ι Asp : Set G) := ⟨g, normalizer_range_le_normalizer_trS_Asp hι hg⟩
  set f := Mconj gA with hf
  set guv := Mconj (nA hι spUV_mem_Tsp)
  set gt := Mconj (nA hι spT_mem_Tsp)
  set gu := Mconj (nA hι spU_mem_Tsp)
  have hconj : ∀ {m : Msp} (hm : m ∈ Tsp), f * Mconj (nA hι hm) * f⁻¹ =
      Mconj (gA * nA hι hm * gA⁻¹) := by
    intro m hm; rw [Mconj_mul, Mconj_mul, Mconj_inv]
  have hconjS : ∀ {m : Msp} (hm : m ∈ Tsp),
      ((gA * nA hι hm * gA⁻¹ : normalizer (trS ι Asp : Set G)) : G) ∈ ι.range := by
    intro m hm
    exact (hgS _).1 (ιe_mem_range hm)
  have hD : ∀ {m : Msp} (hm : m ∈ Tsp), code (basisA ι) (f * Mconj (nA hι hm) * f⁻¹) ∈ dCodes :=
    fun hm => by rw [hconj hm]; exact code_mem_dCodes hι _ (hconjS hm)
  have hcomm_inv : ∀ {m : Msp} (hm : m ∈ Tsp), ∃ y : MulAut ↥(trS ι Asp),
      code (basisA ι) y ∈ dCodes ∧ Mconj (nA hι hm) = f * y * f⁻¹ := by
    intro m hm
    have hs : (g⁻¹ * ιe ι m * g : G) ∈ ι.range := by
      have := (mem_normalizer_iff.1 (inv_mem hg) (ιe ι m)).1 (ιe_mem_range hm)
      simpa using this
    refine ⟨Mconj (gA⁻¹ * nA hι hm * gA), ?_, ?_⟩
    · have e : ((gA⁻¹ * nA hι hm * gA : normalizer (trS ι Asp : Set G)) : G) =
          g⁻¹ * ιe ι m * g := rfl
      exact code_mem_dCodes hι _ (by rw [e]; exact hs)
    · rw [Mconj_mul, Mconj_mul, Mconj_inv, ← hf]; group
  have hcent : ∀ y : MulAut ↥(trS ι Asp), code (basisA ι) y ∈ dCodes → guv * y = y * guv := by
    intro y hy
    refine code_inj hsq hgen ?_
    rw [code_mul hsq hgen hcard, code_mul hsq hgen hcard, code_uv hι]
    exact (uvC_central_dCodes _ hy).symm
  set z := f * guv * f⁻¹ with hz
  have hzc : ∀ {m : Msp} (hm : m ∈ Tsp), z * Mconj (nA hι hm) = Mconj (nA hι hm) * z := by
    intro m hm
    obtain ⟨y, hyD, hy⟩ := hcomm_inv hm
    rw [hy, hz]
    have := hcent y hyD
    calc f * guv * f⁻¹ * (f * y * f⁻¹) = f * (guv * y) * f⁻¹ := by group
      _ = f * (y * guv) * f⁻¹ := by rw [this]
      _ = f * y * f⁻¹ * (f * guv * f⁻¹) := by group
  have hzD : code (basisA ι) z ∈ dCodes := hD spUV_mem_Tsp
  have hzt : mulC (code (basisA ι) z) tC = mulC tC (code (basisA ι) z) := by
    rw [← code_t hι, ← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard, hzc spT_mem_Tsp]
  have hzu : mulC (code (basisA ι) z) uC = mulC uC (code (basisA ι) z) := by
    rw [← code_u hι, ← code_mul hsq hgen hcard, ← code_mul hsq hgen hcard, hzc spU_mem_Tsp]
  have hzuv : z = guv := by
    rcases center_dCodes _ hzD hzt hzu with h | h
    · exfalso
      have h1 : z = 1 := code_inj hsq hgen (h.trans (code_one hsq hgen hcard).symm)
      have h2 : guv = 1 := by
        have : guv = f⁻¹ * z * f := by rw [hz]; group
        rw [this, h1]; group
      apply uvC_ne_idC
      rw [← code_uv hι, ← code_one hsq hgen hcard]
      exact congrArg _ h2
    · exact code_inj hsq hgen (h.trans (code_uv hι).symm)
  have hfuv : f * guv = guv * f := by
    calc f * guv = f * guv * f⁻¹ * f := by group
      _ = guv * f := by rw [← hz, hzuv]
  have hV := normalizes_V hsq hgen hcard (code_uv hι) (code_t hι) (code_u hι) f hfuv (by
    intro d hd
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    have key : ∀ {m : Msp} (hm : m ∈ Tsp), ∃ d' : MulAut ↥(trS ι Asp),
        code (basisA ι) d' ∈ dCodes ∧ f * Mconj (nA hι hm) = d' * f :=
      fun hm => ⟨f * Mconj (nA hι hm) * f⁻¹, hD hm, by group⟩
    rcases hd with rfl | rfl | rfl
    · exact key spUV_mem_Tsp
    · exact key spT_mem_Tsp
    · exact key spU_mem_Tsp)
  have hVset : ∀ v : MulAut ↥(trS ι Asp), (v = 1 ∨ v = guv ∨ v = gt ∨ v = guv * gt) →
      code (basisA ι) (f * v * f⁻¹) ∈ vCodes := by
    have hgen1 : ∀ v ∈ [guv, gt], code (basisA ι) (f * v * f⁻¹) ∈ vCodes := by
      intro v hv
      obtain ⟨v', hv', hfv⟩ := hV v hv
      have : f * v * f⁻¹ = v' := by rw [hfv]; group
      rw [this]
      exact code_mem_vCodes hsq hgen hcard (code_uv hι) (code_t hι) hv'
    rintro v (rfl | rfl | rfl | rfl)
    · rw [mul_one, mul_inv_cancel, code_one hsq hgen hcard]; decide
    · exact hgen1 _ (by simp)
    · exact hgen1 _ (by simp)
    · have e : f * (guv * gt) * f⁻¹ = (f * guv * f⁻¹) * (f * gt * f⁻¹) := by group
      rw [e, code_mul hsq hgen hcard]
      exact mulC_mem_vCodes _ (hgen1 _ (by simp)) _ (hgen1 _ (by simp))
  obtain ⟨m, hmAE, hmT, rfl⟩ := mem_trS.1 hy
  have hv := eq_of_code_mem_vCodes hsq hgen hcard (code_uv hι) (code_t hι)
    (code_nA_mem_vCodes hι hmAE)
  have h1 := hVset _ hv
  have h2 : f * Mconj (nA hι (AEsp_le_Tsp hmAE)) * f⁻¹ =
      Mconj (gA * nA hι hmT * gA⁻¹) := hconj hmT
  rw [h2] at h1
  exact mem_trS_AEsp_of_code hι _ (hconjS hmT) h1

end CFSG.CGT.Stroth77
