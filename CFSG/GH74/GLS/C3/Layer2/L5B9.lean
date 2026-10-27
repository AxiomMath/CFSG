module

public import CFSG.GH74.GLS.C3.Layer2.L5B8

public section

namespace CFSG.GH74.GLS.C3.Layer2.L5

open Equiv Perm Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.C3.Prop121
  CFSG.GH74.GLS.C3.Layer2 CFSG.GH74.GLS.C3.Layer2.Model CFSG.GH74.GLS.Stage1.Thm6
  CFSG.GH74.GLS.Stage1.Thm6.Sec12 CFSG.GH74.GLS.Stage1.Thm6.Sec12b

variable {G : Type} [Group G] [Finite G] {x : G} {K T Q S : Subgroup G} {a : G}

section CaseII

variable {h : IsAConfig 5 x K T Q S a} {c : Coord5 h}

theorem T_sq_mem_R
    (c : Coord5 h) {t : G} (ht : t ∈ T) : t * t ∈ c.lift Rm := by
  rw [Coord5.mem_lift_rco c]
  refine ⟨h.T_le_C (T.mul_mem ht ht), ?_⟩
  rw [c.rco_T_mul ht ht]
  exact T5_sq_mem_R (c.rco_mem_T5 ht)

theorem T_pow4
    (c : Coord5 h) {t : G} (ht : t ∈ T) : t * t * (t * t) = 1 := by
  apply c.rco_T_inj (T.mul_mem (T.mul_mem ht ht) (T.mul_mem ht ht)) T.one_mem
  rw [c.rco_T_mul (T.mul_mem ht ht) (T.mul_mem ht ht), c.rco_T_mul ht ht, Coord5.rco_one]
  exact T5_pow4 (c.rco_mem_T5 ht)

theorem conj_mod_R
    (hc : Case47 h c) {t : G} (ht : t ∈ T) :
    t⁻¹ * (a⁻¹ * t * a) ∈ c.lift Rm := by
  have hRT := relIndex_R_T h c
  have hw : a⁻¹ * t * a ∈ T := a_inv_conj_mem h ht
  by_cases htR : t ∈ c.lift Rm
  · have h1 : a⁻¹ * t * a ∈ c.lift Rm := by
      have := S_norm_R hc (S.inv_mem h.a_mem.1) htR
      simpa using this
    exact (c.lift Rm).mul_mem ((c.lift Rm).inv_mem htR) h1
  · have hwR : a⁻¹ * t * a ∉ c.lift Rm := by
      intro hh
      apply htR
      have := S_norm_R hc h.a_mem.1 hh
      have e : a * (a⁻¹ * t * a) * a⁻¹ = t := by group
      rwa [e] at this
    exact inv_mul_mem_of_relIndex_two hRT ht hw htR hwR

theorem wt_mem_R
    (hc : Case47 h c) {t : G} (ht : t ∈ T) : (a⁻¹ * t * a) * t ∈ c.lift Rm := by
  have h1 := conj_mod_R hc ht
  have h2 : t * t ∈ c.lift Rm := T_sq_mem_R c ht
  have e2 : (a⁻¹ * t * a) * t = (t * (t⁻¹ * (a⁻¹ * t * a)) * t⁻¹) * (t * t) := by group
  rw [e2]
  exact (c.lift Rm).mul_mem (Coord5.Rg_norm_T (c := c) ht h1) h2

theorem sq_nT_not_R
    (hc : Case47 h c) (haR : a * a ∉ c.lift Rm) {s : G} (hs : s ∈ S)
    (hsT : s ∉ T) : s * s ∈ T ∧ s * s ∉ c.lift Rm := by
  obtain ⟨t, ht, rfl⟩ : ∃ t ∈ T, s = a * t := by
    rcases (mem_S_iff hc).1 hs with h1 | ⟨t, ht, h1⟩
    · exact absurd h1 hsT
    · exact ⟨t, ht, h1⟩
  have hw : a⁻¹ * t * a ∈ T := a_inv_conj_mem h ht
  have haa : a * a ∈ T := a_sq_mem h
  have e : a * t * (a * t) = (a * a) * ((a⁻¹ * t * a) * t) := by group
  have hR := wt_mem_R hc ht
  rw [e]
  refine ⟨T.mul_mem haa (T.mul_mem hw ht), fun hh => haR ?_⟩
  have := (c.lift Rm).mul_mem hh ((c.lift Rm).inv_mem hR)
  rwa [mul_inv_cancel_right] at this

theorem Z_cases
    (hc : Case47 h c) {s : G} (hs : s ∈ T) (hsZ : c.rco s ∈ ZTl) (hs1 : s ≠ 1) :
    s = x ∨ s = a * x * a⁻¹ ∨ s = L4.vElt x a := by
  have h1 : c.rco s ≠ 1 := fun hh => hs1 (c.rco_T_inj hs T.one_mem (by rw [hh, Coord5.rco_one]))
  simp only [ZTl, List.mem_cons, List.not_mem_nil, or_false] at hsZ
  rcases hsZ with e | e | e | e
  · exact absurd e h1
  · right; left
    exact c.rco_T_inj hs h.conj_x_mem (by rw [e, Coord5.rco_x' hc])
  · left
    exact c.rco_T_inj hs h.x_mem_T (by rw [e, Coord5.rco_x])
  · right; right
    refine c.rco_T_inj hs (L4.v_mem_T h) ?_
    rw [e, Coord5.rco_v hc]
    exact (PQ_comm e1 e1_mem_Pm f1 f1_mem_Qm')

omit [Finite G] in
theorem isConj_conj (g y : G) : IsConj y (g * y * g⁻¹) := isConj_iff.2 ⟨g, rfl⟩

open CFSG.GH74.GLS.Stage1.Thm6.Sec13 in
theorem caseII_false
    (hsimple : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hc : Case47 h c) (haR : a * a ∉ c.lift Rm) : False := by
  classical
  have hvsq : L4.vElt x a * L4.vElt x a = 1 := L4.v_mul_self h
  have hv1 : L4.vElt x a ≠ 1 := L4.v_ne_one h
  have hvT : L4.vElt x a ∈ T := L4.v_mem_T h
  have hvR : L4.vElt x a ∈ c.lift Rm := v_mem_R hc
  have hTS : T ≤ S := h.T_lt_S.le
  have hvS : L4.vElt x a ∈ S := hTS hvT
  obtain ⟨u₀, hu₀S, hu₀T, hu₀min⟩ : ∃ u₀ ∈ S, u₀ ∉ T ∧
      ∀ w ∈ S, w ∉ T → orderOf u₀ ≤ orderOf w := by
    have hex : ∃ n, ∃ s ∈ S, s ∉ T ∧ orderOf s = n :=
      ⟨orderOf a, a, h.a_mem.1, h.a_mem.2.2.1, rfl⟩
    obtain ⟨u₀, hu₀S, hu₀T, hu₀o⟩ := Nat.find_spec hex
    refine ⟨u₀, hu₀S, hu₀T, fun w hwS hwT => ?_⟩
    rw [hu₀o]
    exact Nat.find_min' hex ⟨w, hwS, hwT, rfl⟩
  have hS' : IsSylow2In S ⊤ := isSylowOf_iff.1 h.sylowS
  have hidx := relIndex_T_S hc
  have hnorm : ∀ t ∈ S, ∀ q ∈ T, t * q * t⁻¹ ∈ T := fun t ht q hq => S_norm_T hc ht hq
  have hcyc : ∃ b ∈ S, ∀ t ∈ S, ∃ k : ℤ, (b ^ k)⁻¹ * t ∈ T := by
    refine ⟨a, h.a_mem.1, fun t ht => ?_⟩
    by_cases htT : t ∈ T
    · exact ⟨0, by simpa using htT⟩
    · exact ⟨1, by simpa using inv_mul_mem_of_relIndex_two hidx h.a_mem.1 ht h.a_mem.2.2.1 htT⟩
  have hext : ∀ y ∈ S, (∃ g : G, g⁻¹ * u₀ * g = y) → IsExtremal S y → y ∈ T ∨ u₀⁻¹ * y ∈ T := by
    intro y hyS _ _
    by_cases hyT : y ∈ T
    · exact Or.inl hyT
    · exact Or.inr (inv_mul_mem_of_relIndex_two hidx hu₀S hyS hu₀T hyT)
  obtain ⟨g₁, hg₁T, hg₁ext⟩ := transfer_conj ig_15_15 hsimple hnab hS' hTS hnorm h.T_lt_S.ne hcyc
    hu₀S hu₀T hu₀min hext
  have ht₀T : g₁⁻¹ * u₀ * g₁ ∈ T := hg₁T
  obtain ⟨hy₀T, hy₀R⟩ := sq_nT_not_R hc haR hu₀S hu₀T
  have hy₀1 : u₀ * u₀ ≠ 1 := fun e => hy₀R (e ▸ (c.lift Rm).one_mem)
  have hy₀S : u₀ * u₀ ∈ S := hTS hy₀T
  have hy₀sq : (u₀ * u₀) * (u₀ * u₀) = 1 := by
    have h4 := T_pow4 c ht₀T
    have e : u₀ * u₀ * (u₀ * u₀) = g₁ * (g₁⁻¹ * u₀ * g₁ * (g₁⁻¹ * u₀ * g₁) *
        (g₁⁻¹ * u₀ * g₁ * (g₁⁻¹ * u₀ * g₁))) * g₁⁻¹ := by group
    rw [e, h4]
    group
  have hg₀ : g₁⁻¹ * u₀ * g₁⁻¹⁻¹ = g₁⁻¹ * u₀ * g₁ := by simp
  obtain ⟨g, hg1, hg2⟩ := scp (isSylowOf_iff.1 h.sylowS).2.1 hg₁ext hg₀
  have hVgS : g * L4.vElt x a * g⁻¹ ∈ S ⊓ centralizer ({g₁⁻¹ * u₀ * g₁} : Set G) :=
    hg2 _ hvS (v_comm_S hc hu₀S).symm
  have hVgc : g * L4.vElt x a * g⁻¹ * (g₁⁻¹ * u₀ * g₁) = (g₁⁻¹ * u₀ * g₁) *
      (g * L4.vElt x a * g⁻¹) := mem_centralizer_singleton_iff.1 hVgS.2
  set t₀ : G := g₁⁻¹ * u₀ * g₁ with ht₀
  have hVgsq : (g * L4.vElt x a * g⁻¹) * (g * L4.vElt x a * g⁻¹) = 1 := by
    calc (g * L4.vElt x a * g⁻¹) * (g * L4.vElt x a * g⁻¹)
        = g * (L4.vElt x a * L4.vElt x a) * g⁻¹ := by group
      _ = 1 := by rw [hvsq]; group
  have hVg1 : g * L4.vElt x a * g⁻¹ ≠ 1 := by
    intro e
    apply hv1
    calc L4.vElt x a = g⁻¹ * (g * L4.vElt x a * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  have hVgT : g * L4.vElt x a * g⁻¹ ∈ T := by
    by_contra hnot
    exact (sq_nT_not_R hc haR hVgS.1 hnot).2 (by rw [hVgsq]; exact (c.lift Rm).one_mem)
  have hY₁ : t₀ * t₀ = g * (u₀ * u₀) * g⁻¹ := by rw [← hg1]; group
  have hY₁1 : t₀ * t₀ ≠ 1 := by
    intro e
    apply hy₀1
    rw [hY₁] at e
    calc u₀ * u₀ = g⁻¹ * (g * (u₀ * u₀) * g⁻¹) * g := by group
      _ = 1 := by rw [e]; group
  have hY₁T : t₀ * t₀ ∈ T := T.mul_mem ht₀T ht₀T
  have hm2 : c.rco t₀ * c.rco t₀ ≠ 1 := by
    intro e
    apply hY₁1
    apply c.rco_T_inj hY₁T T.one_mem
    rw [c.rco_T_mul ht₀T ht₀T, e, Coord5.rco_one]
  have hVgZ : c.rco (g * L4.vElt x a * g⁻¹) ∈ ZTl := by
    refine T5_cent_invol_Z (c.rco_mem_T5 ht₀T) hm2 (c.rco_mem_T5 hVgT) ?_ ?_ ?_
    · rw [← c.rco_T_mul hVgT hVgT, hVgsq, Coord5.rco_one]
    · intro e
      exact hVg1 (c.rco_T_inj hVgT T.one_mem (by rw [e, Coord5.rco_one]))
    · rw [← c.rco_T_mul hVgT ht₀T, ← c.rco_T_mul ht₀T hVgT, hVgc]
  have hVgv : g * L4.vElt x a * g⁻¹ = L4.vElt x a := by
    rcases Z_cases hc hVgT hVgZ hVg1 with e | e | e
    · exfalso
      have h1 : IsConj (L4.vElt x a) (g * L4.vElt x a * g⁻¹) := isConj_conj g _
      rw [e] at h1
      exact x_not_conj_v hc h1.symm
    · exfalso
      have h1 : IsConj (L4.vElt x a) (g * L4.vElt x a * g⁻¹) := isConj_conj g _
      rw [e] at h1
      exact x_not_conj_v hc (h1.trans (x'_conj_x x a)).symm
    · exact e
  have hY₁Z : c.rco (t₀ * t₀) ∈ ZTl := by
    refine T5_cent_invol_Z (c.rco_mem_T5 ht₀T) hm2 (c.rco_mem_T5 hY₁T) ?_ ?_ ?_
    · rw [← c.rco_T_mul hY₁T hY₁T, T_pow4 c ht₀T, Coord5.rco_one]
    · intro e
      exact hY₁1 (c.rco_T_inj hY₁T T.one_mem (by rw [e, Coord5.rco_one]))
    · rw [← c.rco_T_mul hY₁T ht₀T, ← c.rco_T_mul ht₀T hY₁T]
      congr 1
      group
  have hy₀x : IsConj (u₀ * u₀) x := by
    rcases Z_cases hc hY₁T hY₁Z hY₁1 with e | e | e
    · exact isConj_iff.2 ⟨g, by rw [← hY₁]; exact e⟩
    · have h1 : IsConj (u₀ * u₀) (a * x * a⁻¹) := isConj_iff.2 ⟨g, by rw [← hY₁]; exact e⟩
      exact h1.trans (x'_conj_x x a)
    · exfalso
      apply hy₀R
      have h2 : g * (u₀ * u₀) * g⁻¹ = g * L4.vElt x a * g⁻¹ := by rw [← hY₁, e, hVgv]
      have h3 : u₀ * u₀ = L4.vElt x a := mul_left_cancel (mul_right_cancel h2)
      rw [h3]
      exact hvR
  have hJ : ∀ t ∈ T, t ∉ c.lift Rm → t * t = 1 → IsConj t x := by
    intro t ht htR hts
    obtain ⟨r, _, hrt⟩ := JR_conj_G c hy₀T hy₀R hy₀sq ht htR hts
    exact (isConj_iff.2 ⟨r, hrt⟩ : IsConj (u₀ * u₀) t).symm.trans hy₀x
  obtain ⟨g', hg'1, hg'2⟩ := scp_x h hy₀x
  have hxS : x ∈ S := hTS h.x_mem_T
  have ht1T : g' * u₀ * g'⁻¹ ∈ T := hg'2 u₀ hu₀S (by group)
  have hX1T : g' * x * g'⁻¹ ∈ T :=
    hg'2 x hxS (mem_centralizer_singleton_iff.1 (h.T_le_C hy₀T)).symm
  have hVT : g' * L4.vElt x a * g'⁻¹ ∈ T := hg'2 _ hvS (v_comm_S hc hy₀S).symm
  have hX1sq : (g' * x * g'⁻¹) * (g' * x * g'⁻¹) = 1 := by
    calc (g' * x * g'⁻¹) * (g' * x * g'⁻¹) = g' * (x * x) * g'⁻¹ := by group
      _ = 1 := by rw [L4.x_mul_self h]; group
  have hX1nm : ¬ Mixm (c.rco (g' * x * g'⁻¹)) := by
    intro hm
    have h1 : IsConj x (g' * x * g'⁻¹) := isConj_conj g' x
    exact x_not_conj_v hc (h1.trans (isConj_v_of_Mixm hc hX1T hm))
  have hVsq : (g' * L4.vElt x a * g'⁻¹) * (g' * L4.vElt x a * g'⁻¹) = 1 := by
    calc (g' * L4.vElt x a * g'⁻¹) * (g' * L4.vElt x a * g'⁻¹)
        = g' * (L4.vElt x a * L4.vElt x a) * g'⁻¹ := by group
      _ = 1 := by rw [hvsq]; group
  have hV1 : g' * L4.vElt x a * g'⁻¹ ≠ 1 := by
    intro e
    apply hv1
    calc L4.vElt x a = g'⁻¹ * (g' * L4.vElt x a * g'⁻¹) * g' := by group
      _ = 1 := by rw [e]; group
  have hVR : g' * L4.vElt x a * g'⁻¹ ∈ c.lift Rm := by
    by_contra hnot
    have h1 := hJ _ hVT hnot hVsq
    have h2 : IsConj (L4.vElt x a) (g' * L4.vElt x a * g'⁻¹) := isConj_conj g' _
    exact x_not_conj_v hc (h1.symm.trans h2.symm)
  have hVm : Mixm (c.rco (g' * L4.vElt x a * g'⁻¹)) := by
    by_contra hnm
    have h1 := isConj_x_of_R_nonmixed hc hVR hV1 hnm
    have h2 : IsConj (L4.vElt x a) (g' * L4.vElt x a * g'⁻¹) := isConj_conj g' _
    exact x_not_conj_v hc (h1.symm.trans h2.symm)
  have hsq1 : c.rco (g' * u₀ * g'⁻¹) * c.rco (g' * u₀ * g'⁻¹) = f1 := by
    rw [← c.rco_T_mul ht1T ht1T]
    have e : g' * u₀ * g'⁻¹ * (g' * u₀ * g'⁻¹) = x := by
      calc g' * u₀ * g'⁻¹ * (g' * u₀ * g'⁻¹) = g' * (u₀ * u₀) * g'⁻¹ := by group
        _ = x := hg'1
    rw [e, Coord5.rco_x]
  have hrel : g' * u₀ * g'⁻¹ * (g' * x * g'⁻¹) * (g' * u₀ * g'⁻¹)⁻¹ =
      (g' * x * g'⁻¹) * (g' * L4.vElt x a * g'⁻¹) := by
    have h1 := S_nT_conj_x hc hu₀S hu₀T
    have h2 := x'_eq_x_mul_v h
    calc g' * u₀ * g'⁻¹ * (g' * x * g'⁻¹) * (g' * u₀ * g'⁻¹)⁻¹
        = g' * (u₀ * x * u₀⁻¹) * g'⁻¹ := by group
      _ = g' * (x * L4.vElt x a) * g'⁻¹ := by rw [h1, h2]
      _ = (g' * x * g'⁻¹) * (g' * L4.vElt x a * g'⁻¹) := by group
  have hrco := congrArg c.rco hrel
  rw [c.rco_T_mul (T.mul_mem ht1T hX1T) (T.inv_mem ht1T), c.rco_T_mul ht1T hX1T,
    c.rco_T_inv ht1T, c.rco_T_mul hX1T hVT] at hrco
  exact fz_model (c.rco_mem_T5 ht1T) hsq1 (c.rco_mem_T5 hX1T)
    (by rw [← c.rco_T_mul hX1T hX1T, hX1sq, Coord5.rco_one]) hX1nm hVm hrco

end CaseII

end CFSG.GH74.GLS.C3.Layer2.L5
