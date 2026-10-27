module

public import CFSG.ClassicalGroups.UnitaryFlag.SU3NonisotropicStabilizer
import CFSG.ClassicalGroups.UnitaryFlag.HomologyEigen
public import CFSG.ClassicalGroups.UnitaryFlag.NaturalModulePerp

public section

namespace CFSG.ClassicalGroups.UnitaryFlag

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open NonisotropicStabilizer
open scoped Pointwise CharTwo

variable {m : ℕ} {K : Type} [Field K]

theorem finrank_hermPerp_span_singleton_of_nonisotropic (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) :
    Module.finrank K ↥(hermPerp h (K ∙ v)) = 2 := by
  have hker : hermPerp h (K ∙ v) = LinearMap.ker (stdHermForm h 3 v) := by
    rw [hermPerp, Submodule.orthogonalBilin_span_singleton]
  have hne : stdHermForm h 3 v ≠ 0 := fun h0 => hv (by
    have h := congrArg (fun f : (Fin 3 → K) →ₗ[K] K => f v) h0
    simpa using h)
  have hdim := Module.Dual.finrank_ker_add_one_of_ne_zero (K := K)
    (V₁ := Fin 3 → K) (f := stdHermForm h 3 v) hne
  rw [Module.finrank_fin_fun] at hdim
  rw [hker]
  omega

theorem linearIndependent_pair_of_hyperbolic (h : UnitaryFieldData 2 m K) {e f : Fin 3 → K}
    (he : stdHermForm h 3 e e = 0) (hf : stdHermForm h 3 f f = 0)
    (hef : stdHermForm h 3 e f = 1) : LinearIndependent K ![e, f] := by
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    rw [hef, map_one] at h'
    exact h'.symm
  rw [LinearIndependent.pair_iff]
  intro a b hab
  constructor
  · have hh := congrArg (stdHermForm h 3 f) hab
    simp only [map_add, map_smul, smul_eq_mul, hfe, hf, mul_one, mul_zero, add_zero,
      map_zero] at hh
    exact hh
  · have hh := congrArg (stdHermForm h 3 e) hab
    simp only [map_add, map_smul, smul_eq_mul, he, hef, mul_zero, mul_one, zero_add,
      map_zero] at hh
    exact hh

theorem hermPerp_span_singleton_eq_span_pair (h : UnitaryFieldData 2 m K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    hermPerp h (K ∙ v) = Submodule.span K {e, f} := by
  have hle : Submodule.span K {e, f} ≤ hermPerp h (K ∙ v) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_insert_iff] at hx
    rcases hx with rfl | hx
    · refine mem_hermPerp.mpr ?_
      intro a ha
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul,
        ((stdHermForm_isSymm h 3).eq_iff).mpr hev, mul_zero]
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      refine mem_hermPerp.mpr ?_
      intro a ha
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
      rw [LinearMap.map_smulₛₗ₂, smul_eq_mul,
        ((stdHermForm_isSymm h 3).eq_iff).mpr hfv, mul_zero]
  have hfin : Module.finrank K ↥(Submodule.span K {e, f}) = 2 := by
    have h := finrank_span_eq_card (linearIndependent_pair_of_hyperbolic h he hf hef)
    rwa [Matrix.range_cons_cons_empty, Fintype.card_fin] at h
  refine (Submodule.eq_of_le_of_finrank_eq hle ?_).symm
  rw [hfin, finrank_hermPerp_span_singleton_of_nonisotropic h hv]

theorem linearIndependent_of_hyperbolic_pair (h : UnitaryFieldData 2 m K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    LinearIndependent K ![e, f, v] := by
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    rw [hef, map_one] at h'
    exact h'.symm
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hg' : g 0 • e + g 1 • f + g 2 • v = 0 := by
    simpa [Fin.sum_univ_three] using hg
  have h0 : g 0 = 0 := by
    have hh := congrArg (stdHermForm h 3 f) hg'
    simp only [map_add, map_smul, smul_eq_mul, hfe, hf, hfv, mul_one, mul_zero, add_zero,
      map_zero] at hh
    exact hh
  have h1 : g 1 = 0 := by
    have hh := congrArg (stdHermForm h 3 e) hg'
    simp only [map_add, map_smul, smul_eq_mul, he, hef, hev, mul_one, mul_zero, add_zero,
      zero_add, map_zero] at hh
    exact hh
  have h2 : g 2 = 0 := by
    have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0]; simp)
    have hh : g 2 • v = 0 := by simpa [h0, h1] using hg'
    exact (smul_eq_zero.mp hh).resolve_right hv0
  intro i
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

theorem span_range_hyperbolic_eq_top (h : UnitaryFieldData 2 m K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    Submodule.span K (Set.range ![e, f, v]) = ⊤ := by
  have hind := linearIndependent_of_hyperbolic_pair h hv he hf hef hev hfv
  apply Submodule.eq_top_of_finrank_eq
  rw [finrank_span_eq_card hind, Fintype.card_fin, Module.finrank_fin_fun]

theorem exists_eq_smul_of_stdHermForm_eq_zero (h : UnitaryFieldData 2 m K) {v e f w : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    (hew : stdHermForm h 3 e w = 0) (hfw : stdHermForm h 3 f w = 0) :
    ∃ c : K, w = c • v := by
  have hspan := span_range_hyperbolic_eq_top h hv he hf hef hev hfv
  have hwe : stdHermForm h 3 w e = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hew
  have hwf : stdHermForm h 3 w f = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hfw
  have hve : stdHermForm h 3 v e = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hev
  have hvf : stdHermForm h 3 v f = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hfv
  have hsymm_vw : h.bar (stdHermForm h 3 v w) = stdHermForm h 3 w v :=
    (stdHermForm_isSymm h 3).eq v w
  have hsymm_vv : h.bar (stdHermForm h 3 v v) = stdHermForm h 3 v v :=
    (stdHermForm_isSymm h 3).eq v v
  let c : K := stdHermForm h 3 v w / stdHermForm h 3 v v
  have hye : stdHermForm h 3 (w - c • v) e = 0 := by
    rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    simp only [hwe, hve, mul_zero, sub_zero]
  have hyf : stdHermForm h 3 (w - c • v) f = 0 := by
    rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    simp only [hwf, hvf, mul_zero, sub_zero]
  have hyv : stdHermForm h 3 (w - c • v) v = 0 := by
    rw [map_sub, LinearMap.sub_apply, LinearMap.map_smulₛₗ₂, smul_eq_mul]
    dsimp only [c]
    rw [map_div₀, hsymm_vw, hsymm_vv, div_mul_cancel₀ _ hv, sub_self]
  have hzero : stdHermForm h 3 (w - c • v) = 0 := by
    apply LinearMap.ext_on_range hspan
    intro i
    fin_cases i
    · simpa using hye
    · simpa using hyf
    · simpa using hyv
  have hsub : w - c • v = 0 :=
    stdHermForm_separatingLeft h 3 _ fun z => by rw [hzero]; rfl
  exact ⟨c, sub_eq_zero.mp hsub⟩

theorem exists_hyperbolic_pair_of_nonisotropic (h : UnitaryFieldData 2 m K) {v : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) :
    ∃ e f : Fin 3 → K, stdHermForm h 3 e e = 0 ∧ stdHermForm h 3 f f = 0 ∧
      stdHermForm h 3 e f = 1 ∧ stdHermForm h 3 e v = 0 ∧ stdHermForm h 3 f v = 0 := by
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0]; simp)
  let W : Submodule K (Fin 3 → K) := hermPerp h (K ∙ v)
  have hdim : Module.finrank K ↥W = 2 :=
    finrank_hermPerp_span_singleton_of_nonisotropic h hv
  have hinf : W ⊓ K ∙ v = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxW, hxv⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxv
    have h0 := (mem_hermPerp.mp hxW) v (Submodule.mem_span_singleton_self v)
    rw [map_smul, smul_eq_mul] at h0
    have hc : c = 0 := (mul_eq_zero.mp h0).resolve_right hv
    rw [hc, zero_smul]
    exact Submodule.zero_mem _
  have hsup : W ⊔ K ∙ v = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have h := Submodule.finrank_sup_add_finrank_inf_eq W (K ∙ v)
    rw [hinf, finrank_bot, hdim, finrank_span_singleton hv0] at h
    rw [Module.finrank_fin_fun]
    omega
  have hsep : ((stdHermForm h 3).domRestrict₁₂ W W).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    apply stdHermForm_separatingLeft h 3 (x : Fin 3 → K)
    intro z
    have hz : z ∈ W ⊔ K ∙ v := by rw [hsup]; exact Submodule.mem_top
    obtain ⟨w, hwW, y, hyv, hwy⟩ := Submodule.mem_sup.mp hz
    have hxw : stdHermForm h 3 (x : Fin 3 → K) w = 0 := by
      have := hx ⟨w, hwW⟩
      simpa [LinearMap.domRestrict₁₂_apply] using this
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hyv
    have hxv0 : stdHermForm h 3 (x : Fin 3 → K) v = 0 :=
      ((stdHermForm_isSymm h 3).eq_iff).mpr
        ((mem_hermPerp.mp x.2) v (Submodule.mem_span_singleton_self v))
    rw [← hwy, map_add, hxw, map_smul, smul_eq_mul, hxv0, mul_zero, add_zero]
  have hsymm : ((stdHermForm h 3).domRestrict₁₂ W W).IsSymm :=
    ⟨fun x y => by
      rw [LinearMap.domRestrict₁₂_apply, LinearMap.domRestrict₁₂_apply]
      exact (stdHermForm_isSymm h 3).eq (x : Fin 3 → K) (y : Fin 3 → K)⟩
  obtain ⟨w, hw⟩ := exists_hypBasis h hsymm hsep (r := 1) (ε := 0) (by rw [hdim])
  refine ⟨w (Sum.inl 0), w (Sum.inr (Sum.inr 0)), ?_, ?_, ?_, ?_, ?_⟩
  · have h := hw (Sum.inl 0) (Sum.inl 0)
    simpa [LinearMap.domRestrict₁₂_apply] using h
  · have h := hw (Sum.inr (Sum.inr 0)) (Sum.inr (Sum.inr 0))
    simpa [LinearMap.domRestrict₁₂_apply] using h
  · have h := hw (Sum.inl 0) (Sum.inr (Sum.inr 0))
    simpa [LinearMap.domRestrict₁₂_apply] using h
  · exact ((stdHermForm_isSymm h 3).eq_iff).mpr
      ((mem_hermPerp.mp (w (Sum.inl 0)).2) v (Submodule.mem_span_singleton_self v))
  · exact ((stdHermForm_isSymm h 3).eq_iff).mpr
      ((mem_hermPerp.mp (w (Sum.inr (Sum.inr 0))).2) v
        (Submodule.mem_span_singleton_self v))

theorem exists_eq_smul_of_forall_mem_mulVec_eq (h : UnitaryFieldData 2 m K) {v : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {w : Fin 3 → K} (hw : ∀ g ∈ L, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = w) :
    ∃ c : K, w = c • v := by
  obtain ⟨e, f, hee, hff, hef, hev, hfv⟩ := exists_hyperbolic_pair_of_nonisotropic h hv
  have he0 : e ≠ 0 := by
    intro h0
    rw [h0] at hef
    simp at hef
  have h1 : (1 : K) ∈ h.traceZero := mem_traceZero_of_bar_eq h (map_one h.bar)
  obtain ⟨ge, hge_lin⟩ := exists_mem_unitarySU_hermTransvection h hee h1
  have hgeL : ge ∈ L := by
    refine (hL ge).mpr ?_
    rw [← Matrix.mulVecLin_apply, hge_lin, hermTransvection_apply, one_mul, hev]
    simp
  have hge_w : ge • w = w + stdHermForm h 3 e w • e := by
    rw [unitarySU_smul_def h, hge_lin, hermTransvection_apply, one_mul]
  have hew : stdHermForm h 3 e w = 0 := by
    have hfix : ge • w = w := by
      rw [unitarySU_smul_def h, Matrix.mulVecLin_apply, hw ge hgeL]
    rw [hge_w] at hfix
    have h2 : (stdHermForm h 3 e w) • e = 0 := by
      have h' : w + stdHermForm h 3 e w • e = w + 0 := by simpa using hfix
      exact add_left_cancel h'
    exact (smul_eq_zero.mp h2).resolve_right he0
  obtain ⟨gf, hgf_lin⟩ := exists_mem_unitarySU_hermTransvection h hff h1
  have hgfL : gf ∈ L := by
    refine (hL gf).mpr ?_
    rw [← Matrix.mulVecLin_apply, hgf_lin, hermTransvection_apply, one_mul, hfv]
    simp
  have hgf_w : gf • w = w + stdHermForm h 3 f w • f := by
    rw [unitarySU_smul_def h, hgf_lin, hermTransvection_apply, one_mul]
  have hfw : stdHermForm h 3 f w = 0 := by
    have hfix : gf • w = w := by
      rw [unitarySU_smul_def h, Matrix.mulVecLin_apply, hw gf hgfL]
    rw [hgf_w] at hfix
    have h2 : (stdHermForm h 3 f w) • f = 0 := by
      have h' : w + stdHermForm h 3 f w • f = w + 0 := by simpa using hfix
      exact add_left_cancel h'
    have hf0 : f ≠ 0 := by
      intro h0
      rw [h0] at hef
      simp at hef
    exact (smul_eq_zero.mp h2).resolve_right hf0
  exact exists_eq_smul_of_stdHermForm_eq_zero h hv hee hff hef hev hfv hew hfw

theorem exists_mem_trace_eq (h : UnitaryFieldData 2 m K) {v : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {t : K} (ht : h.bar t = t) :
    ∃ k ∈ L, Matrix.trace ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + t := by
  have : CharP K 2 := h.charP
  obtain ⟨e, f, hee, hff, hef, hev, hfv⟩ := exists_hyperbolic_pair_of_nonisotropic h hv
  have h1 : (1 : K) ∈ h.traceZero := mem_traceZero_of_bar_eq h (map_one h.bar)
  have ht0 : t ∈ h.traceZero := mem_traceZero_of_bar_eq h ht
  obtain ⟨ge, hge⟩ := exists_mem_unitarySU_hermTransvection h hee h1
  obtain ⟨gf, hgf⟩ := exists_mem_unitarySU_hermTransvection h hff ht0
  have hgeL : ge ∈ L := by
    refine (hL ge).mpr ?_
    rw [← Matrix.mulVecLin_apply, hge, hermTransvection_apply, one_mul, hev]
    simp
  have hgfL : gf ∈ L := by
    refine (hL gf).mpr ?_
    rw [← Matrix.mulVecLin_apply, hgf, hermTransvection_apply, hfv]
    simp
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    rw [hef, map_one] at h'
    exact h'.symm
  let A : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := (stdHermForm h 3 e).smulRight e
  let B : (Fin 3 → K) →ₗ[K] (Fin 3 → K) := (t • stdHermForm h 3 f).smulRight f
  have hTe : hermTransvection (stdHermForm h 3) e 1 = 1 + A := by
    ext x
    simp [A, hermTransvection_apply]
  have hTf : hermTransvection (stdHermForm h 3) f t = 1 + B := by
    ext x
    simp [B, hermTransvection_apply, smul_eq_mul, mul_assoc]
  have hAB : A * B = (t • stdHermForm h 3 f).smulRight e := by
    ext x
    simp [A, B, Module.End.mul_apply, LinearMap.smulRight_apply, hef, smul_eq_mul, mul_assoc]
  have hexp : hermTransvection (stdHermForm h 3) e 1 * hermTransvection (stdHermForm h 3) f t =
      1 + A + B + A * B := by
    rw [hTe, hTf]
    noncomm_ring
  have htraceT : LinearMap.trace K (Fin 3 → K)
      (hermTransvection (stdHermForm h 3) e 1 * hermTransvection (stdHermForm h 3) f t) =
      1 + t := by
    rw [hexp, hAB]
    dsimp only [A, B]
    simp [LinearMap.smul_apply, hee, hff, hfe]
  let k : unitarySU 2 m K 3 := ge * gf
  refine ⟨k, L.mul_mem hgeL hgfL, ?_⟩
  have hkmat : ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((gf : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    rw [show (k : GL (Fin 3) K) = (ge : GL (Fin 3) K) * (gf : GL (Fin 3) K) from rfl,
      Units.val_mul]
  have hlin : Matrix.toLin' (((ge : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((gf : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) =
      hermTransvection (stdHermForm h 3) e 1 * hermTransvection (stdHermForm h 3) f t := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_apply', Matrix.toLin'_apply', hge, hgf,
      Module.End.mul_eq_comp]
  exact (show Matrix.trace ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 + t by
    rw [hkmat, ← Matrix.trace_toLin'_eq, hlin, htraceT])

theorem exists_norm_one_orderOf_eq_succ (h : UnitaryFieldData 2 m K) :
    ∃ μ : K, orderOf μ = 2 ^ m + 1 ∧ h.norm μ = 1 := by
  have hcard : Nat.card (rootsOfUnity (2 ^ m + 1) K) = 2 ^ m + 1 := by
    rw [← h.ker_normUnits]
    exact h.card_ker_normUnits_and_surjective.1
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity (2 ^ m + 1) K)
  have hu' : orderOf u = 2 ^ m + 1 := by rw [hu, hcard]
  let μu : Kˣ := (u : Kˣ)
  have hμker : μu ∈ (Units.map h.normHom).ker := by
    rw [h.ker_normUnits]
    exact u.2
  refine ⟨(μu : K), ?_, (h.mem_ker_normUnits).mp hμker⟩
  rw [orderOf_units, Subgroup.orderOf_coe, hu']

theorem exists_gl_mulVec_single_eq (h : UnitaryFieldData 2 m K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0) :
    ∃ P : GL (Fin 3) K,
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1) = e ∧
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 1 1) = f ∧
      (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 1) = v := by
  let Q : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![e, f, v] j i
  have hQcol : Q.col = ![e, f, v] := rfl
  have hQli : LinearIndependent K Q.col := by
    rw [hQcol]
    exact linearIndependent_of_hyperbolic_pair h hv he hf hef hev hfv
  have hQdet : Q.det ≠ 0 :=
    Matrix.nonsingular_iff_det_ne_zero.mp (Matrix.Nonsingular.of_linearIndependent_col hQli)
  let P : GL (Fin 3) K := Matrix.GeneralLinearGroup.mkOfDetNeZero Q hQdet
  have hP : (P : Matrix (Fin 3) (Fin 3) K) = Q := by simp [P]
  have h0 : (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 0 1) = e := by
    rw [hP]
    change (Matrix.of fun i j => ![e, f, v] j i) *ᵥ (Pi.single 0 1) = e
    rw [Matrix.mulVec_single_one]
    rfl
  have h1 : (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 1 1) = f := by
    rw [hP]
    change (Matrix.of fun i j => ![e, f, v] j i) *ᵥ (Pi.single 1 1) = f
    rw [Matrix.mulVec_single_one]
    rfl
  have h2 : (P : Matrix (Fin 3) (Fin 3) K) *ᵥ (Pi.single 2 1) = v := by
    rw [hP]
    change (Matrix.of fun i j => ![e, f, v] j i) *ᵥ (Pi.single 2 1) = v
    rw [Matrix.mulVec_single_one]
    rfl
  exact ⟨P, h0, h1, h2⟩

theorem exists_gl_mulVec_eq_hyperbolicBasis (h : UnitaryFieldData 2 m K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    {μ : K} (hμ0 : μ ≠ 0) :
    ∃ g : GL (Fin 3) K,
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e = μ • e ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ f = μ • f ∧
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (μ ^ 2)⁻¹ • v ∧
      (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
  obtain ⟨P, hPe0, hPe1, hPe2⟩ := exists_gl_mulVec_single_eq h hv he hf hef hev hfv
  let Dm : Matrix (Fin 3) (Fin 3) K := !![μ, 0, 0; 0, μ, 0; 0, 0, (μ ^ 2)⁻¹]
  have hDdet : Dm.det = 1 := by
    rw [Matrix.det_fin_three]
    simp [Dm]
    field_simp
  let DGL : GL (Fin 3) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero Dm (by rw [hDdet]; exact one_ne_zero)
  have hDGL : (DGL : Matrix (Fin 3) (Fin 3) K) = Dm := by simp [DGL]
  let g : GL (Fin 3) K := P * DGL * P⁻¹
  have hge : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e = μ • e := by
    change ((P * DGL * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ e = μ • e
    rw [mulVec_conj P DGL e, inv_mulVec_eq_of_mulVec_eq P hPe0, hDGL,
      Matrix.mulVec_single_one]
    rw [show Dm.col 0 = μ • (Pi.single 0 1 : Fin 3 → K) by
      funext i; fin_cases i <;> simp [Dm], Matrix.mulVec_smul, hPe0]
  have hgf : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ f = μ • f := by
    change ((P * DGL * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ f = μ • f
    rw [mulVec_conj P DGL f, inv_mulVec_eq_of_mulVec_eq P hPe1, hDGL,
      Matrix.mulVec_single_one]
    rw [show Dm.col 1 = μ • (Pi.single 1 1 : Fin 3 → K) by
      funext i; fin_cases i <;> simp [Dm], Matrix.mulVec_smul, hPe1]
  have hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (μ ^ 2)⁻¹ • v := by
    change ((P * DGL * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ v =
      (μ ^ 2)⁻¹ • v
    rw [mulVec_conj P DGL v, inv_mulVec_eq_of_mulVec_eq P hPe2, hDGL,
      Matrix.mulVec_single_one]
    rw [show Dm.col 2 = (μ ^ 2)⁻¹ • (Pi.single 2 1 : Fin 3 → K) by
      funext i; fin_cases i <;> simp [Dm], Matrix.mulVec_smul, hPe2]
  have hdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    change ((P * DGL * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1
    rw [show ((P * DGL * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        (P : Matrix (Fin 3) (Fin 3) K) * (DGL : Matrix (Fin 3) (Fin 3) K) *
          ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) by
      rw [Units.val_mul, Units.val_mul]]
    rw [Matrix.det_units_conj (P : (Matrix (Fin 3) (Fin 3) K)ˣ), hDGL, hDdet]
  exact ⟨g, hge, hgf, hgv, hdet⟩

theorem isometry_of_mulVec_eq_hyperbolicBasis (h : UnitaryFieldData 2 m K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    {g : GL (Fin 3) K} {μ : K} (hμ : h.norm μ = 1)
    (hge : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e = μ • e)
    (hgf : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ f = μ • f)
    (hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (μ ^ 2)⁻¹ • v) :
    ∀ x y : Fin 3 → K,
      stdHermForm h 3 ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x)
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ y) = stdHermForm h 3 x y := by
  have hspan := span_range_hyperbolic_eq_top h hv he hf hef hev hfv
  have hfe : stdHermForm h 3 f e = 1 := by
    have h' := (stdHermForm_isSymm h 3).eq e f
    rw [hef, map_one] at h'
    exact h'.symm
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : h.norm (0 : K) = 1 := by rw [← h0]; exact hμ
    simp [UnitaryFieldData.norm] at h1
  have hμbar : h.bar μ = μ⁻¹ := by
    have h1 : μ * h.bar μ = 1 := by simpa [UnitaryFieldData.norm] using hμ
    exact eq_inv_of_mul_eq_one_right h1
  have hμ2cancel : ∀ x : K, (μ ^ 2)⁻¹ * (μ ^ 2 * x) = x := by
    intro x
    rw [← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hμ0), one_mul]
  have hve : stdHermForm h 3 v e = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hev
  have hvf : stdHermForm h 3 v f = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hfv
  have hiso_basis : ∀ i j : Fin 3,
      stdHermForm h 3 ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![e, f, v] i)
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![e, f, v] j) =
      stdHermForm h 3 (![e, f, v] i) (![e, f, v] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hge, hgf, hgv, he, hf, hef, hfe, hev, hfv, hve, hvf, hμbar, hμ2cancel,
        mul_inv_cancel₀ hμ0]
  intro x y
  have h1 : ∀ i : Fin 3,
      (stdHermForm h 3 ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ (![e, f, v] i))).comp
        (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) =
      stdHermForm h 3 (![e, f, v] i) := by
    intro i
    apply LinearMap.ext_on_range hspan
    intro j
    exact hiso_basis i j
  have h2 :
      (stdHermForm h 3 ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x)).comp
        (Matrix.mulVecLin (g : Matrix (Fin 3) (Fin 3) K)) =
      stdHermForm h 3 x := by
    apply LinearMap.ext_on_range hspan
    intro i
    have hi := LinearMap.congr_fun (h1 i) x
    simp only [LinearMap.comp_apply, Matrix.mulVecLin_apply] at hi ⊢
    rw [← (stdHermForm_isSymm h 3).eq
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ ![e, f, v] i)
        ((g : Matrix (Fin 3) (Fin 3) K) *ᵥ x),
      ← (stdHermForm_isSymm h 3).eq (![e, f, v] i) x]
    exact congrArg h.bar hi
  have h3 := LinearMap.congr_fun h2 y
  simpa [LinearMap.comp_apply, Matrix.mulVecLin_apply] using h3

theorem mem_unitarySU_of_mulVec_eq_hyperbolicBasis (h : UnitaryFieldData 2 m K)
    {v e f : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0)
    (he : stdHermForm h 3 e e = 0) (hf : stdHermForm h 3 f f = 0)
    (hef : stdHermForm h 3 e f = 1) (hev : stdHermForm h 3 e v = 0)
    (hfv : stdHermForm h 3 f v = 0) {g : GL (Fin 3) K} {μ : K} (hμ : h.norm μ = 1)
    (hge : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e = μ • e)
    (hgf : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ f = μ • f)
    (hgv : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = (μ ^ 2)⁻¹ • v)
    (hgdet : (g : Matrix (Fin 3) (Fin 3) K).det = 1) :
    g ∈ unitarySU 2 m K 3 :=
  (mem_unitarySU_iff_isometry h).mpr
    ⟨hgdet, isometry_of_mulVec_eq_hyperbolicBasis h hv he hf hef hev hfv hμ hge hgf hgv⟩

theorem mulVec_eq_smul_of_mem_hermPerp (h : UnitaryFieldData 2 m K) {v e f : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) (he : stdHermForm h 3 e e = 0)
    (hf : stdHermForm h 3 f f = 0) (hef : stdHermForm h 3 e f = 1)
    (hev : stdHermForm h 3 e v = 0) (hfv : stdHermForm h 3 f v = 0)
    {g : GL (Fin 3) K} {μ : K}
    (hge : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ e = μ • e)
    (hgf : (g : Matrix (Fin 3) (Fin 3) K) *ᵥ f = μ • f) :
    ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
      (g : Matrix (Fin 3) (Fin 3) K) *ᵥ w = μ • w := by
  intro w hw
  have hwperp : w ∈ hermPerp h (K ∙ v) := by
    refine mem_hermPerp.mpr ?_
    intro a ha
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ha
    rw [LinearMap.map_smulₛₗ₂, smul_eq_mul, hw, mul_zero]
  rw [hermPerp_span_singleton_eq_span_pair h hv he hf hef hev hfv] at hwperp
  obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.mp hwperp
  rw [← hab, mulVec_add, mulVec_smul, mulVec_smul, hge, hgf]
  simp only [smul_add, smul_smul]
  rw [mul_comm a μ, mul_comm b μ]

theorem eq_one_of_pow_eq_one_of_smul_eq_smul_of_orderOf (h : UnitaryFieldData 2 m K)
    {v : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0) {g : unitarySU 2 m K 3} {μ : K}
    (hμorder : orderOf μ = 2 ^ m + 1) (hgv : g • v = (μ ^ 2)⁻¹ • v) {n : ℕ}
    (hgn : g ^ n = 1) : μ ^ n = 1 := by
  have h1 : ((μ ^ 2)⁻¹) ^ n • v = v := by
    rw [← pow_smul_eq_smul_pow (a := g) (e := v) (c := (μ ^ 2)⁻¹) hgv n, hgn, one_smul]
  have hv0 : v ≠ 0 := fun h0 => hv (by rw [h0]; simp)
  have h2 : ((μ ^ 2)⁻¹) ^ n = 1 := by
    by_contra hne
    have h3 : (((μ ^ 2)⁻¹) ^ n - 1) • v = 0 := by
      rw [sub_smul, one_smul, h1, sub_self]
    rcases smul_eq_zero.mp h3 with h4 | h4
    · exact absurd (sub_eq_zero.mp h4) hne
    · exact hv0 h4
  have h3 : μ ^ (2 * n) = 1 := by
    have h4 : ((μ ^ 2) ^ n)⁻¹ = 1 := by simpa [inv_pow] using h2
    rw [← pow_mul] at h4
    exact inv_eq_one.mp h4
  have hm0 : m ≠ 0 := by have := h.one_le; omega
  have heven : Even (2 ^ m) := Even.pow_of_ne_zero (by norm_num : Even 2) hm0
  have hodd : Odd (2 ^ m + 1) := heven.add_one
  have hcop : Nat.Coprime (2 ^ m + 1) 2 := Odd.coprime_two_right hodd
  have hdvd : 2 ^ m + 1 ∣ n := by
    refine hcop.dvd_of_dvd_mul_left ?_
    rw [← hμorder]
    exact (orderOf_dvd_iff_pow_eq_one).mpr h3
  exact (orderOf_dvd_iff_pow_eq_one).mp (by simpa [hμorder] using hdvd)

theorem orderOf_eq_succ_of_smul_eq_hyperbolicBasis (h : UnitaryFieldData 2 m K)
    {v e f : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0)
    (he : stdHermForm h 3 e e = 0) (hf : stdHermForm h 3 f f = 0)
    (hef : stdHermForm h 3 e f = 1) (hev : stdHermForm h 3 e v = 0)
    (hfv : stdHermForm h 3 f v = 0) {μ : K} (hμorder : orderOf μ = 2 ^ m + 1)
    {g : unitarySU 2 m K 3} (hge : g • e = μ • e) (hgf : g • f = μ • f)
    (hgv : g • v = (μ ^ 2)⁻¹ • v) : orderOf g = 2 ^ m + 1 := by
  have hiff : ∀ n : ℕ, g ^ n = 1 ↔ μ ^ n = 1 := by
    intro n
    constructor
    · intro hgn
      exact eq_one_of_pow_eq_one_of_smul_eq_smul_of_orderOf h hv hμorder hgv hgn
    · intro hμn
      apply unitarySU_ext_mulVecLin
      apply LinearMap.ext_on_range (span_range_hyperbolic_eq_top h hv he hf hef hev hfv)
      intro i
      rw [← unitarySU_smul_def h (g ^ n), ← unitarySU_smul_def h 1]
      fin_cases i
      · change g ^ n • e = 1 • e
        rw [pow_smul_eq_smul_pow (a := g) (e := e) (c := μ) hge n, hμn]
        simp
      · change g ^ n • f = 1 • f
        rw [pow_smul_eq_smul_pow (a := g) (e := f) (c := μ) hgf n, hμn]
        simp
      · change g ^ n • v = 1 • v
        have hμ2invn : ((μ ^ 2)⁻¹) ^ n = 1 := by
          have h1 : ((μ ^ 2)⁻¹) ^ n = ((μ ^ 2) ^ n)⁻¹ := inv_pow (μ ^ 2) n
          have h2 : (μ ^ 2) ^ n = μ ^ (2 * n) := (pow_mul μ 2 n).symm
          have h3 : μ ^ (2 * n) = 1 := by
            rw [mul_comm 2 n, pow_mul, hμn, one_pow]
          rw [h1, h2, h3, inv_one]
        rw [pow_smul_eq_smul_pow (a := g) (e := v) (c := (μ ^ 2)⁻¹) hgv n, hμ2invn]
        simp
  have hord : orderOf g = orderOf μ := orderOf_eq_orderOf_iff.mpr hiff
  rw [hord, hμorder]

theorem mem_centralizer_of_smul_eq_hyperbolicBasis (h : UnitaryFieldData 2 m K)
    {v e f : Fin 3 → K} (hv : stdHermForm h 3 v v ≠ 0)
    (he : stdHermForm h 3 e e = 0) (hf : stdHermForm h 3 f f = 0)
    (hef : stdHermForm h 3 e f = 1) (hev : stdHermForm h 3 e v = 0)
    (hfv : stdHermForm h 3 f v = 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ k, k ∈ L ↔ ((k : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v)
    {g : unitarySU 2 m K 3} {μ : K} (hge : g • e = μ • e) (hgf : g • f = μ • f)
    (hgv : g • v = (μ ^ 2)⁻¹ • v)
    (hgw : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 → g • w = μ • w) :
    g ∈ Subgroup.centralizer (L : Set (unitarySU 2 m K 3)) := by
  have hspan := span_range_hyperbolic_eq_top h hv he hf hef hev hfv
  have hve : stdHermForm h 3 v e = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hev
  have hvf : stdHermForm h 3 v f = 0 := ((stdHermForm_isSymm h 3).eq_iff).mpr hfv
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hkv : k • v = v := by
    rw [unitarySU_smul_def h, Matrix.mulVecLin_apply, (hL k).mp hk]
  have hkperp : ∀ x : Fin 3 → K, stdHermForm h 3 v x = 0 →
      stdHermForm h 3 v (k • x) = 0 := by
    intro x hx
    have h := stdHermForm_smul_smul h k v x
    simpa [hkv, hx] using h
  apply unitarySU_ext_mulVecLin
  apply LinearMap.ext_on_range hspan
  intro i
  rw [← unitarySU_smul_def h (k * g), ← unitarySU_smul_def h (g * k)]
  rw [mul_smul, mul_smul]
  fin_cases i
  · change k • (g • e) = g • (k • e)
    rw [hge, smul_comm k μ e, hgw (k • e) (hkperp e hve)]
  · change k • (g • f) = g • (k • f)
    rw [hgf, smul_comm k μ f, hgw (k • f) (hkperp f hvf)]
  · change k • (g • v) = g • (k • v)
    rw [hgv, smul_comm k ((μ ^ 2)⁻¹) v, hkv, hgv]

theorem exists_mem_centralizer_of_nonisotropic (h : UnitaryFieldData 2 m K) {v : Fin 3 → K}
    (hv : stdHermForm h 3 v v ≠ 0) {L : Subgroup (unitarySU 2 m K 3)}
    (hL : ∀ g, g ∈ L ↔ ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = v) :
    ∃ μ : K, orderOf μ = 2 ^ m + 1 ∧
      ∃ g ∈ Subgroup.centralizer (L : Set (unitarySU 2 m K 3)), orderOf g = 2 ^ m + 1 ∧
        ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec v = (μ ^ 2)⁻¹ • v ∧
        ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 →
          ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).mulVec w = μ • w := by
  obtain ⟨μ, hμorder, hμnorm⟩ := exists_norm_one_orderOf_eq_succ h
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : h.norm (0 : K) = 1 := by rw [← h0]; exact hμnorm
    simp [UnitaryFieldData.norm] at h1
  obtain ⟨e, f, hee, hff, hef, hev, hfv⟩ := exists_hyperbolic_pair_of_nonisotropic h hv
  obtain ⟨gGL, hge_mat, hgf_mat, hgv_mat, hgdet⟩ :=
    exists_gl_mulVec_eq_hyperbolicBasis h hv hee hff hef hev hfv hμ0
  have hgSU : gGL ∈ unitarySU 2 m K 3 :=
    mem_unitarySU_of_mulVec_eq_hyperbolicBasis h hv hee hff hef hev hfv hμnorm
      hge_mat hgf_mat hgv_mat hgdet
  let g : unitarySU 2 m K 3 := ⟨gGL, hgSU⟩
  have hge : g • e = μ • e := by
    rw [unitarySU_smul_def h, Matrix.mulVecLin_apply, hge_mat]
  have hgf : g • f = μ • f := by
    rw [unitarySU_smul_def h, Matrix.mulVecLin_apply, hgf_mat]
  have hgv : g • v = (μ ^ 2)⁻¹ • v := by
    rw [unitarySU_smul_def h, Matrix.mulVecLin_apply, hgv_mat]
  have hgw_mat := mulVec_eq_smul_of_mem_hermPerp h hv hee hff hef hev hfv hge_mat hgf_mat
  have hgw : ∀ w : Fin 3 → K, stdHermForm h 3 v w = 0 → g • w = μ • w := by
    intro w hw
    rw [unitarySU_smul_def h, Matrix.mulVecLin_apply]
    exact hgw_mat w hw
  have horder := orderOf_eq_succ_of_smul_eq_hyperbolicBasis h hv hee hff hef hev hfv
    hμorder hge hgf hgv
  have hcentral := mem_centralizer_of_smul_eq_hyperbolicBasis h hv hee hff hef hev hfv
    hL hge hgf hgv hgw
  exact ⟨μ, hμorder, g, hcentral, horder, hgv_mat, hgw_mat⟩

end CFSG.ClassicalGroups.UnitaryFlag

end
