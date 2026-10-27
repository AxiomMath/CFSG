module

public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIISixLocal
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypIISixCheck
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoAltHypII
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A6Aut
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.ComponentClassification.RankTwoAlt.Six

open Equiv Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.QuasithinUnique.A6Facts
  CFSG.ComponentClassification.AS76b CFSG.ComponentClassification.RankTwoSporadic
  CFSG.ComponentClassification.RankTwoHypIIY

theorem exists_autA6_of_code {c : List ℕ} (hc : c ∈ Core.autL) :
    ∃ x ∈ A6Models.autA6, code x = c := by
  unfold Core.autL at hc
  rw [List.mem_flatMap] at hc
  obtain ⟨y, hy, hc⟩ := hc
  rw [List.mem_map] at hc
  obtain ⟨r, hr, rfl⟩ := hc
  obtain ⟨y', hy', rfl⟩ := exists_psl29_of_code hy
  rw [← autRepsP_code] at hr
  obtain ⟨r', hr', rfl⟩ := List.mem_map.mp hr
  have hr'mem : r' ∈ A6Models.autA6 := by rw [autA6_eq]; exact autReps_mem_closure r' hr'
  exact ⟨y' * r', A6Models.autA6.mul_mem (psl29_le_autA6 hy') hr'mem, by rw [code_mul]⟩

@[expose] def tFrobT : P10 := A6Models.perm10 [[1, 6], [2, 3], [4, 8]]

theorem tFrobT_code : code tFrobT = tFrobTC := by decide +kernel
theorem tMul_code' : code A6Models.tMul = tMulC' := by decide +kernel
theorem sixPa_code : code sixPa = t0C := by decide +kernel
theorem sixPb_code : code sixPb = v0C := by decide +kernel
theorem sixF1b_code : code sixF1b = f1bC := by decide +kernel
theorem sixF0a_eq : sixF0a = A6Models.tFrob := by decide +kernel
theorem sixF1a_eq : sixF1a = A6Models.tFrob := by decide +kernel
theorem sixF0b_eq : sixF0b = sixPb := by decide +kernel

theorem tMul_mul_tFrobT : A6Models.tMul * tFrobT = A6Models.tFrob * A6Models.tMul := by
  apply code_injective
  rw [code_mul, code_mul, tMul_code', tFrobT_code, tFrob_code]
  exact tMul_tFrobT

theorem mul_eq_of_code {x y z w : P10}
    (h : Core.cmul (code x) (code y) = Core.cmul (code z) (code w)) : x * y = z * w := by
  apply code_injective
  rw [code_mul, code_mul]
  exact h

theorem cmul_self_ne_cid {t : P10} (ht2 : t * t = 1) :
    (Core.cmul (code t) (code t) != Core.cid) = false := by
  rw [← code_mul, ht2, code_one]
  exact bne_self_eq_false _

theorem exists_conj_outer {t : P10} (ht : t ∈ A6Models.autA6) (ht2 : t * t = 1)
    (htX : t ∉ A6Models.psl29) :
    ∃ g ∈ A6Models.autA6, g * t * g⁻¹ = A6Models.tFrob ∨ g * t * g⁻¹ = sixPa := by
  have h : (Core.cmul (code t) (code t) != Core.cid || Core.pslLit.contains (code t) ||
      Core.pslLit.any fun g => Core.cmul g (code t) == Core.cmul Core.tFrobC g ||
        Core.cmul g (code t) == Core.cmul tFrobTC g || Core.cmul g (code t) == Core.cmul t0C g) =
      true :=
    List.all_eq_true.mp outer_conj_check (code t) (code_mem_autL ht)
  have h2 : Core.pslLit.contains (code t) = false := by
    rw [Bool.eq_false_iff]
    intro hc
    exact htX ((mem_psl29_iff t).2 (List.contains_iff_mem.mp hc))
  rw [cmul_self_ne_cid ht2, h2, Bool.false_or, Bool.false_or, List.any_eq_true] at h
  obtain ⟨c, hc, hgc⟩ := h
  obtain ⟨g, hg, rfl⟩ := exists_psl29_of_code hc
  have hgA := psl29_le_autA6 hg
  simp only [Bool.or_eq_true, beq_iff_eq] at hgc
  rw [← tFrob_code, ← tFrobT_code, ← sixPa_code] at hgc
  rcases hgc with (h1 | h1) | h1
  · exact ⟨g, hgA, Or.inl (by rw [mul_eq_of_code h1, mul_inv_cancel_right])⟩
  · refine ⟨A6Models.tMul * g, A6Models.autA6.mul_mem DoubleA3.tMul_mem hgA, Or.inl ?_⟩
    have h1' := mul_eq_of_code h1
    calc A6Models.tMul * g * t * (A6Models.tMul * g)⁻¹
        = A6Models.tMul * (g * t) * g⁻¹ * A6Models.tMul⁻¹ := by group
      _ = A6Models.tMul * tFrobT * A6Models.tMul⁻¹ := by rw [h1']; group
      _ = A6Models.tFrob := by rw [tMul_mul_tFrobT, mul_inv_cancel_right]
  · exact ⟨g, hgA, Or.inr (by rw [mul_eq_of_code h1, mul_inv_cancel_right])⟩

theorem exists_conj_frob {c : P10} (hc : c ∈ A6Models.autA6) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcF : c ≠ A6Models.tFrob) (hcomm : c * A6Models.tFrob = A6Models.tFrob * c) :
    ∃ h ∈ A6Models.autA6, h * A6Models.tFrob = A6Models.tFrob * h ∧
      (h * c * h⁻¹ = sixPb ∨ h * c * h⁻¹ = A6Models.tFrob * sixPb ∨ h * c * h⁻¹ = sixF1b ∨
        h * c * h⁻¹ = A6Models.tFrob * sixF1b) := by
  have h : (Core.cmul (code c) (code c) != Core.cid || code c == Core.cid ||
      code c == Core.tFrobC || Core.cmul (code c) Core.tFrobC != Core.cmul Core.tFrobC (code c) ||
      cFrobL.any fun h => Core.cmul h (code c) == Core.cmul v0C h ||
        Core.cmul h (code c) == Core.cmul (Core.cmul Core.tFrobC v0C) h ||
        Core.cmul h (code c) == Core.cmul f1bC h ||
        Core.cmul h (code c) == Core.cmul (Core.cmul Core.tFrobC f1bC) h) = true :=
    List.all_eq_true.mp frob_cent_check (code c) (code_mem_autL hc)
  have e1 : (code c == Core.cid) = false := by
    rw [← code_one, beq_eq_false_iff_ne]
    exact fun h => hc1 (code_injective h)
  have e2 : (code c == Core.tFrobC) = false := by
    rw [← tFrob_code, beq_eq_false_iff_ne]
    exact fun h => hcF (code_injective h)
  have e3 : (Core.cmul (code c) Core.tFrobC != Core.cmul Core.tFrobC (code c)) = false := by
    rw [← tFrob_code, ← code_mul, ← code_mul, hcomm]
    exact bne_self_eq_false _
  rw [cmul_self_ne_cid hc2, e1, e2, e3, Bool.false_or, Bool.false_or, Bool.false_or,
    Bool.false_or, List.any_eq_true] at h
  obtain ⟨hc', hhL, hhc⟩ := h
  have hL := List.all_eq_true.mp cFrobL_check hc' hhL
  simp only [Bool.and_eq_true, beq_iff_eq] at hL
  obtain ⟨hcomm', hmem⟩ := hL
  obtain ⟨k, hk, rfl⟩ := exists_autA6_of_code (List.contains_iff_mem.mp hmem)
  refine ⟨k, hk, mul_eq_of_code (by rw [tFrob_code]; exact hcomm'), ?_⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at hhc
  rw [← tFrob_code, ← sixPb_code, ← sixF1b_code] at hhc
  rcases hhc with ((h1 | h1) | h1) | h1
  · exact Or.inl (by rw [mul_eq_of_code h1, mul_inv_cancel_right])
  · rw [← code_mul A6Models.tFrob sixPb] at h1
    exact Or.inr (Or.inl (by rw [mul_eq_of_code h1, mul_inv_cancel_right]))
  · exact Or.inr (Or.inr (Or.inl (by rw [mul_eq_of_code h1, mul_inv_cancel_right])))
  · rw [← code_mul A6Models.tFrob sixF1b] at h1
    exact Or.inr (Or.inr (Or.inr (by rw [mul_eq_of_code h1, mul_inv_cancel_right])))

theorem exists_conj_pgl {c : P10} (hc : c ∈ A6Models.autA6) (hc2 : c * c = 1) (hc1 : c ≠ 1)
    (hcP : c ≠ sixPa) (hcomm : c * sixPa = sixPa * c) :
    ∃ h ∈ A6Models.autA6, h * sixPa = sixPa * h ∧
      (h * c * h⁻¹ = sixPb ∨ h * c * h⁻¹ = sixPa * sixPb) := by
  have h : (Core.cmul (code c) (code c) != Core.cid || code c == Core.cid || code c == t0C ||
      Core.cmul (code c) t0C != Core.cmul t0C (code c) ||
      c0L.any fun h => Core.cmul h (code c) == Core.cmul v0C h ||
        Core.cmul h (code c) == Core.cmul (Core.cmul t0C v0C) h) = true :=
    List.all_eq_true.mp pgl_cent_check (code c) (code_mem_autL hc)
  have e1 : (code c == Core.cid) = false := by
    rw [← code_one, beq_eq_false_iff_ne]
    exact fun h => hc1 (code_injective h)
  have e2 : (code c == t0C) = false := by
    rw [← sixPa_code, beq_eq_false_iff_ne]
    exact fun h => hcP (code_injective h)
  have e3 : (Core.cmul (code c) t0C != Core.cmul t0C (code c)) = false := by
    rw [← sixPa_code, ← code_mul, ← code_mul, hcomm]
    exact bne_self_eq_false _
  rw [cmul_self_ne_cid hc2, e1, e2, e3, Bool.false_or, Bool.false_or, Bool.false_or,
    Bool.false_or, List.any_eq_true] at h
  obtain ⟨hc', hhL, hhc⟩ := h
  have hL := List.all_eq_true.mp c0L_check hc' hhL
  simp only [Bool.and_eq_true, beq_iff_eq] at hL
  obtain ⟨hcomm', hmem⟩ := hL
  obtain ⟨k, hk, rfl⟩ := exists_autA6_of_code (List.contains_iff_mem.mp hmem)
  refine ⟨k, hk, mul_eq_of_code (by rw [sixPa_code]; exact hcomm'), ?_⟩
  simp only [Bool.or_eq_true, beq_iff_eq] at hhc
  rw [← sixPa_code, ← sixPb_code] at hhc
  rcases hhc with h1 | h1
  · exact Or.inl (by rw [mul_eq_of_code h1, mul_inv_cancel_right])
  · rw [← code_mul sixPa sixPb] at h1
    exact Or.inr (by rw [mul_eq_of_code h1, mul_inv_cancel_right])

theorem map_conj_psl29 {k : P10} (hk : k ∈ A6Models.autA6) :
    A6Models.psl29.map (MulAut.conj k).toMonoidHom = A6Models.psl29 := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact psl29_normal k hk y hy
  · intro hx
    refine ⟨k⁻¹ * x * k, ?_, ?_⟩
    · simpa using psl29_normal k⁻¹ (A6Models.autA6.inv_mem hk) x hx
    · simp [MulAut.conj_apply, mul_assoc]

theorem psl29_le_nE_of_conj {k t s a b : P10} (hk : k ∈ A6Models.autA6) (hat : k * t * k⁻¹ = a)
    (hbs : k * s * k⁻¹ = b) (h : A6Models.psl29 ≤ nE A6Models.psl29 (closure {a, b})) :
    A6Models.psl29 ≤ nE A6Models.psl29 (closure {t, s}) := by
  let f : P10 →* P10 := (MulAut.conj k⁻¹).toMonoidHom
  have hf : Function.Injective f := (MulAut.conj k⁻¹).injective
  have hfa : f a = t := by
    show k⁻¹ * a * k⁻¹⁻¹ = t
    rw [← hat]
    group
  have hfb : f b = s := by
    show k⁻¹ * b * k⁻¹⁻¹ = s
    rw [← hbs]
    group
  have hX : A6Models.psl29.map f = A6Models.psl29 :=
    map_conj_psl29 (A6Models.autA6.inv_mem hk)
  have hE : (closure ({a, b} : Set P10)).map f = closure {t, s} := by
    rw [MonoidHom.map_closure, Set.image_pair, hfa, hfb]
  have h' := Subgroup.map_mono (f := f) h
  rwa [hX, map_nE f hf, hX, hE] at h'

theorem closure_pair_le_closure_pair_mul {a b : P10} (ha : a * a = 1) :
    closure ({a, b} : Set P10) ≤ closure {a, a * b} := by
  rw [closure_le]
  rintro x (rfl | rfl)
  · exact subset_closure (Set.mem_insert _ _)
  · have h : a * (a * x) ∈ closure ({a, a * x} : Set P10) :=
      mul_mem (subset_closure (Set.mem_insert _ _)) (subset_closure (Set.mem_insert_of_mem _ rfl))
    rwa [← mul_assoc, ha, one_mul] at h

theorem tFrob_mul_self' : A6Models.tFrob * A6Models.tFrob = 1 := by decide +kernel
theorem sixPa_mul_self : sixPa * sixPa = 1 := by decide +kernel

theorem psl29_le_nE_pair {t s : P10} (ht : t ∈ A6Models.autA6) (hs : s ∈ A6Models.autA6)
    (ht2 : t * t = 1) (htX : t ∉ A6Models.psl29) (hs2 : s * s = 1) (hs1 : s ≠ 1) (hst : s ≠ t)
    (hts : t * s = s * t) : A6Models.psl29 ≤ nE A6Models.psl29 (closure {t, s}) := by
  obtain ⟨g, hg, hgt⟩ := exists_conj_outer ht ht2 htX
  have hs' : g * s * g⁻¹ ∈ A6Models.autA6 :=
    A6Models.autA6.mul_mem (A6Models.autA6.mul_mem hg hs) (A6Models.autA6.inv_mem hg)
  have hs'2 : g * s * g⁻¹ * (g * s * g⁻¹) = 1 := by
    calc g * s * g⁻¹ * (g * s * g⁻¹) = g * (s * s) * g⁻¹ := by group
      _ = 1 := by rw [hs2, mul_one, mul_inv_cancel]
  have hs'1 : g * s * g⁻¹ ≠ 1 := by
    intro h
    apply hs1
    calc s = g⁻¹ * (g * s * g⁻¹) * g := by group
      _ = 1 := by rw [h]; group
  have hconj : ∀ x y : P10, g * x * g⁻¹ = g * y * g⁻¹ → x = y := fun x y h => by
    calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
      _ = g⁻¹ * (g * y * g⁻¹) * g := by rw [h]
      _ = y := by group
  have hcomm' : g * s * g⁻¹ * (g * t * g⁻¹) = g * t * g⁻¹ * (g * s * g⁻¹) := by
    calc g * s * g⁻¹ * (g * t * g⁻¹) = g * (s * t) * g⁻¹ := by group
      _ = g * (t * s) * g⁻¹ := by rw [hts]
      _ = g * t * g⁻¹ * (g * s * g⁻¹) := by group
  rcases hgt with hgt | hgt
  · rw [hgt] at hcomm'
    obtain ⟨h, hh, hhF, hcases⟩ := exists_conj_frob hs' hs'2 hs'1
      (fun h => hst (hconj s t (h.trans hgt.symm))) hcomm'
    have hk : h * g ∈ A6Models.autA6 := A6Models.autA6.mul_mem hh hg
    have hkt : h * g * t * (h * g)⁻¹ = A6Models.tFrob := by
      calc h * g * t * (h * g)⁻¹ = h * (g * t * g⁻¹) * h⁻¹ := by group
        _ = A6Models.tFrob := by rw [hgt, hhF, mul_inv_cancel_right]
    have hks : ∀ b, h * (g * s * g⁻¹) * h⁻¹ = b → h * g * s * (h * g)⁻¹ = b := fun b hb => by
      rw [← hb]; group
    have hF0 : A6Models.psl29 ≤ nE A6Models.psl29 (closure {A6Models.tFrob, sixPb}) := by
      have := psl29_le_nE_sixF0
      rwa [sixF0a_eq, sixF0b_eq] at this
    have hF1 : A6Models.psl29 ≤ nE A6Models.psl29 (closure {A6Models.tFrob, sixF1b}) := by
      have := psl29_le_nE_sixF1
      rwa [sixF1a_eq] at this
    rcases hcases with hb | hb | hb | hb
    · exact psl29_le_nE_of_conj hk hkt (hks _ hb) hF0
    · exact psl29_le_nE_of_conj hk hkt (hks _ hb)
        (hF0.trans (nE_mono (closure_pair_le_closure_pair_mul tFrob_mul_self')))
    · exact psl29_le_nE_of_conj hk hkt (hks _ hb) hF1
    · exact psl29_le_nE_of_conj hk hkt (hks _ hb)
        (hF1.trans (nE_mono (closure_pair_le_closure_pair_mul tFrob_mul_self')))
  · rw [hgt] at hcomm'
    obtain ⟨h, hh, hhP, hcases⟩ := exists_conj_pgl hs' hs'2 hs'1
      (fun h => hst (hconj s t (h.trans hgt.symm))) hcomm'
    have hk : h * g ∈ A6Models.autA6 := A6Models.autA6.mul_mem hh hg
    have hkt : h * g * t * (h * g)⁻¹ = sixPa := by
      calc h * g * t * (h * g)⁻¹ = h * (g * t * g⁻¹) * h⁻¹ := by group
        _ = sixPa := by rw [hgt, hhP, mul_inv_cancel_right]
    have hks : ∀ b, h * (g * s * g⁻¹) * h⁻¹ = b → h * g * s * (h * g)⁻¹ = b := fun b hb => by
      rw [← hb]; group
    rcases hcases with hb | hb
    · exact psl29_le_nE_of_conj hk hkt (hks _ hb) psl29_le_nE_sixP
    · exact psl29_le_nE_of_conj hk hkt (hks _ hb)
        (psl29_le_nE_sixP.trans (nE_mono (closure_pair_le_closure_pair_mul sixPa_mul_self)))

abbrev psl29' : Subgroup ↥A6Models.autA6 := A6Models.psl29.subgroupOf A6Models.autA6

theorem map_subtype_psl29' : psl29'.map A6Models.autA6.subtype = A6Models.psl29 := by
  rw [subgroupOf_map_subtype, inf_eq_left.mpr psl29_le_autA6]

theorem nonempty_psl29'_equiv : Nonempty (↥psl29' ≃* alternatingGroup (Fin 6)) := by
  obtain ⟨ψ, -⟩ := DoubleA3.exists_psl_equiv
  exact ⟨(subgroupOfEquivOfLe psl29_le_autA6).trans ψ⟩

theorem autModel_autA6 : AutModel (alternatingGroup (Fin 6)) ↥A6Models.autA6 psl29' where
  normal := ⟨fun x hx g => by
    rw [mem_subgroupOf] at hx ⊢
    exact psl29_normal g g.2 x hx⟩
  centralizer_eq_bot := by
    rw [eq_bot_iff]
    intro g hg
    rw [mem_bot]
    refine Subtype.ext (centralizer_psl29 g.2 fun x hx => ?_)
    have h := mem_centralizer_iff.mp hg ⟨x, psl29_le_autA6 hx⟩ (by rw [SetLike.mem_coe, mem_subgroupOf]; exact hx)
    exact (congrArg Subtype.val h).symm
  nonempty_mulEquiv := nonempty_psl29'_equiv
  exists_conj := fun α => by
    obtain ⟨b, hb, hbα⟩ := DoubleA3.exists_aut_model (subgroupOfEquivOfLe psl29_le_autA6) α
    refine ⟨⟨b, hb⟩, fun x => Subtype.ext ?_⟩
    exact hbα x

theorem commutator_psl29' : ⁅psl29', psl29'⁆ = psl29' := by
  obtain ⟨e⟩ := nonempty_psl29'_equiv
  have : Group.IsPerfect (alternatingGroup (Fin 6)) :=
    (Group.isPerfect_def).2 (commutator_alternatingGroup_eq_top (by simp))
  have : Group.IsPerfect ↥psl29' :=
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Subgroup.isPerfect_iff.mp this

theorem qWitness_six {E : Subgroup ↥A6Models.autA6} (hE : IsElemAbelian 2 E)
    (h4 : 4 ≤ Nat.card E) (hEX : ¬ E ≤ psl29') : QWitness psl29' E := by
  obtain ⟨t, htE, htX⟩ := IsConcreteLE.not_le_iff_exists.mp hEX
  obtain ⟨s, hsE, hs1, hst⟩ : ∃ s ∈ E, s ≠ 1 ∧ s ≠ t := by
    by_contra h
    push Not at h
    have hle : E ≤ zpowers t := fun s hs => by
      by_cases h1 : s = 1
      · rw [h1]
        exact one_mem _
      · rw [h s hs h1]
        exact mem_zpowers t
    have hcard := Subgroup.card_le_of_le hle
    rw [Nat.card_zpowers] at hcard
    have := orderOf_le_of_pow_eq_one two_pos (hE.2 t htE)
    omega
  have ht2 : (t : P10) * t = 1 := by
    have h := congrArg Subtype.val (hE.2 t htE)
    rwa [sq] at h
  have hs2 : (s : P10) * s = 1 := by
    have h := congrArg Subtype.val (hE.2 s hsE)
    rwa [sq] at h
  have hts : (t : P10) * s = s * t :=
    congrArg (fun x : ↥E => ((x : ↥A6Models.autA6) : P10)) (hE.1.is_comm.comm ⟨t, htE⟩ ⟨s, hsE⟩)
  have htX' : (t : P10) ∉ A6Models.psl29 := fun h => htX (mem_subgroupOf.mpr h)
  have hs1' : (s : P10) ≠ 1 := fun h => hs1 (Subtype.ext h)
  have hst' : (s : P10) ≠ t := fun h => hst (Subtype.ext h)
  have hP := psl29_le_nE_pair t.2 s.2 ht2 htX' hs2 hs1' hst' hts
  have hle : closure ({(t : P10), (s : P10)} : Set P10) ≤ E.map A6Models.autA6.subtype := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact ⟨t, htE, rfl⟩
    · exact ⟨s, hsE, rfl⟩
  have hkey : (nE psl29' E).map A6Models.autA6.subtype =
      nE A6Models.psl29 (E.map A6Models.autA6.subtype) := by
    rw [map_nE _ A6Models.autA6.subtype_injective, map_subtype_psl29']
  have hP' := hP.trans (nE_mono hle)
  rw [← hkey] at hP'
  refine ⟨psl29', fun x hx => ?_, commutator_psl29', ?_⟩
  · obtain ⟨y, hy, hyx⟩ := hP' (mem_subgroupOf.mp hx)
    rwa [Subtype.ext hyx] at hy
  · rw [Nat.card_congr (subgroupOfEquivOfLe psl29_le_autA6).toEquiv, card_psl29]
    decide

theorem hypII_of_alternating_six {A : Type*} [Group A] (hA : commutator A = ⊤)
    (e : A ⧸ center A ≃* alternatingGroup (Fin 6)) : HypII A :=
  hypII_of_witness autModel_autA6 (fun _ hE h4 hEX => Or.inr
    (not_isTwoNilpotent_of_qWitness (qWitness_six hE h4 hEX))) hA e

end CFSG.ComponentClassification.RankTwoAlt.Six

namespace CFSG.ComponentClassification.RankTwoAlt

theorem hypII_of_alternating_ge_five {n : ℕ} (hn : 5 ≤ n) {A : Type*} [Group A]
    (hA : commutator A = ⊤) (e : A ⧸ Subgroup.center A ≃* alternatingGroup (Fin n)) :
    AS76b.HypII A := by
  by_cases h6 : n = 6
  · subst h6
    exact Six.hypII_of_alternating_six hA e
  · exact hypII_of_alternating (by omega) hA e

end CFSG.ComponentClassification.RankTwoAlt
