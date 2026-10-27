module

public import CFSG.Fischer.Classification.Orthogonal3.Local
public import CFSG.Fischer.Classification.Uniqueness.Star

public section

namespace CFSG.Fischer.Classification

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

open CFSG.Blueprint.Fischer CFSG.Fischer F3

variable {m : ℕ} {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)}

variable (f) in
@[expose] def muPt (v z : Fin m → ZMod 3) : Set (R3 f) :=
  {q | ∃ w, f w w = 1 ∧ f w v = 0 ∧ f w z = 0 ∧ reflBar f w = q}

theorem eq_or_eq_neg_of_reflBar_eq (hf : IsF3Form f) (hm : 4 ≤ m) {w w' : Fin m → ZMod 3}
    (hw : f w w = 1) (hw' : f w' w' = 1) (h : reflBar f w' = reflBar f w) :
    w = w' ∨ w = -w' :=
  (reflBar_eq_reflBar_iff hf hm hw' hw).1 h

theorem pair_eq_zero_of_reflBar_eq (hf : IsF3Form f) (hm : 4 ≤ m) {w w' x : Fin m → ZMod 3}
    (hw : f w w = 1) (hw' : f w' w' = 1) (h : reflBar f w' = reflBar f w) (hx : f w' x = 0) :
    f w x = 0 := by
  rcases eq_or_eq_neg_of_reflBar_eq hf hm hw hw' h with rfl | rfl
  · exact hx
  · rw [LinearMap.BilinForm.neg_left, hx, neg_zero]

theorem reflBar_mem_localClass_iff (hf : IsF3Form f) (hm : 4 ≤ m) {v w : Fin m → ZMod 3}
    (hv : f v v = 1) (hw : f w w = 1) :
    reflBar f w ∈ LocalClass (D3 f) (reflBar f v) ↔ f w v = 0 := by
  rw [localClass_D3 hf hm hv]
  constructor
  · rintro ⟨w', hw', hw'v, h⟩
    exact pair_eq_zero_of_reflBar_eq hf hm hw hw' h hw'v
  · intro h
    exact ⟨w, hw, h, rfl⟩

theorem reflBar_mem_muPt_iff (hf : IsF3Form f) (hm : 4 ≤ m) {v z w : Fin m → ZMod 3}
    (hw : f w w = 1) : reflBar f w ∈ muPt f v z ↔ f w v = 0 ∧ f w z = 0 := by
  constructor
  · rintro ⟨w', hw', hw'v, hw'z, h⟩
    exact ⟨pair_eq_zero_of_reflBar_eq hf hm hw hw' h hw'v,
      pair_eq_zero_of_reflBar_eq hf hm hw hw' h hw'z⟩
  · rintro ⟨h1, h2⟩
    exact ⟨w, hw, h1, h2, rfl⟩

theorem muPt_smul {c : ZMod 3} (hc : c ≠ 0) (v z : Fin m → ZMod 3) :
    muPt f v (c • z) = muPt f v z := by
  ext q
  constructor
  · rintro ⟨w, hw, hwv, hwz, rfl⟩
    rw [LinearMap.BilinForm.smul_right] at hwz
    exact ⟨w, hw, hwv, (mul_eq_zero.1 hwz).resolve_left hc, rfl⟩
  · rintro ⟨w, hw, hwv, hwz, rfl⟩
    exact ⟨w, hw, hwv, by rw [LinearMap.BilinForm.smul_right, hwz, mul_zero], rfl⟩

theorem muSet_eq_muPt (hf : IsF3Form f) (hm : 4 ≤ m) {v u : Fin m → ZMod 3} (hv : f v v = 1)
    (hu : f u u = 1) : muSet (D3 f) (reflBar f v) (reflBar f u) = muPt f v (u - v) := by
  ext q
  constructor
  · rintro ⟨hq1, hq2⟩
    rw [localClass_D3 hf hm hv] at hq1
    obtain ⟨w, hw, hwv, rfl⟩ := hq1
    have hwu := (reflBar_mem_localClass_iff hf hm hu hw).1 hq2
    exact ⟨w, hw, hwv, by rw [LinearMap.BilinForm.sub_right, hwu, hwv, sub_zero], rfl⟩
  · rintro ⟨w, hw, hwv, hwz, rfl⟩
    rw [LinearMap.BilinForm.sub_right, hwv, sub_zero] at hwz
    exact ⟨reflBar_mem_localClass hf hm hv hw hwv, reflBar_mem_localClass hf hm hu hw hwz⟩

@[expose] def IsIsoPt (f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3))
    (v z : Fin m → ZMod 3) : Prop :=
  z ≠ 0 ∧ f z z = 0 ∧ f z v = 0

theorem reflBar_add_not_commute (hf : IsF3Form f) (hm : 4 ≤ m) {v z : Fin m → ZMod 3}
    (hv : f v v = 1) (hz : IsIsoPt f v z) :
    reflBar f (v + z) * reflBar f v ≠ reflBar f v * reflBar f (v + z) := by
  obtain ⟨hz0, hzz, hzv⟩ := hz
  have hvz : f v z = 0 := by rw [hf.symm]; exact hzv
  have hu : f (v + z) (v + z) = 1 := by rw [norm_add hf, hv, hvz, hzz]; ring
  intro h
  rcases (reflBar_commute_iff hf hm hu hv).1 h with h1 | h1 | h1
  · rw [LinearMap.BilinForm.add_left, hv, hzv, add_zero] at h1
    exact one_ne_zero h1
  · apply hz0
    linear_combination (norm := module) (-1 : ZMod 3) • h1
  · apply one_ne_zero (α := ZMod 3)
    have : z = v := by linear_combination (norm := module) h1 - three_eq_zero • v
    calc (1 : ZMod 3) = f v v := hv.symm
      _ = f z v := by rw [this]
      _ = 0 := hzv

theorem muPt_mem_muFamily (hf : IsF3Form f) (hm : 4 ≤ m) {v z : Fin m → ZMod 3}
    (hv : f v v = 1) (hz : IsIsoPt f v z) : muPt f v z ∈ muFamily (D3 f) (reflBar f v) := by
  obtain ⟨hz0, hzz, hzv⟩ := hz
  have hvz : f v z = 0 := by rw [hf.symm]; exact hzv
  have hu : f (v + z) (v + z) = 1 := by rw [norm_add hf, hv, hvz, hzz]; ring
  refine ⟨reflBar f (v + z), reflBar_mem_D3 hu, reflBar_add_not_commute hf hm hv ⟨hz0, hzz, hzv⟩,
    ?_⟩
  rw [muSet_eq_muPt hf hm hv hu, add_sub_cancel_left]

theorem muFamily_D3 (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1) :
    muFamily (D3 f) (reflBar f v) = {O | ∃ z, IsIsoPt f v z ∧ muPt f v z = O} := by
  ext O
  constructor
  · rintro ⟨c, hc, hcd, rfl⟩
    obtain ⟨u, hu, rfl⟩ := mem_D3_iff.1 hc
    have huv : f u v ≠ 0 := fun h => hcd ((reflBar_commute_iff hf hm hu hv).2 (Or.inl h))
    obtain ⟨u₁, hu₁u₁, hu₁v, hreq⟩ :
        ∃ u₁, f u₁ u₁ = 1 ∧ f u₁ v = 1 ∧ reflBar f u₁ = reflBar f u :=
      ⟨f u v • u, by rw [norm_smul, mul_self_of_ne_zero huv, hu, one_mul],
        by rw [LinearMap.BilinForm.smul_left, mul_self_of_ne_zero huv], reflBar_smul huv u⟩
    rw [← hreq] at hcd ⊢
    rw [muSet_eq_muPt hf hm hv hu₁u₁]
    refine ⟨u₁ - v, ⟨fun h0 => hcd (by rw [sub_eq_zero.1 h0]), ?_, ?_⟩, rfl⟩
    · simp only [sub_eq_add_neg, norm_add hf, LinearMap.BilinForm.neg_right,
        LinearMap.BilinForm.neg_left, hu₁u₁, hu₁v, hv, neg_neg]
      ring
    · rw [LinearMap.BilinForm.sub_left, hu₁v, hv, sub_self]
  · rintro ⟨z, hz, rfl⟩
    exact muPt_mem_muFamily hf hm hv hz

theorem exists_eq_muPt (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1)
    (O : muFamily (D3 f) (reflBar f v)) : ∃ z, IsIsoPt f v z ∧ (O : Set (R3 f)) = muPt f v z := by
  obtain ⟨z, hz, hO⟩ := (Set.ext_iff.1 (muFamily_D3 hf hm hv) O).1 O.2
  exact ⟨z, hz, hO.symm⟩

theorem isIsoPt_act_refl (hf : IsF3Form f) {v w z : Fin m → ZMod 3} (hw : f w w = 1)
    (hwv : f w v = 0) (hz : IsIsoPt f v z) : IsIsoPt f v (act (F3.refl f w) z) := by
  have hiso := isIsom_refl hf w
  have hfix : act (F3.refl f w) v = v := act_refl_of_perp hw (by rw [hf.symm]; exact hwv)
  refine ⟨fun h => hz.1 (act_injective _ (h.trans (act_zero _).symm)), by rw [hiso.norm, hz.2.1],
    ?_⟩
  rw [← hfix, hiso, hz.2.2]

theorem muPt_eq_muPt_iff (hf : IsF3Form f) (hm : 5 ≤ m) {v z z' : Fin m → ZMod 3}
    (hv : f v v = 1) (hz : IsIsoPt f v z) (hz' : IsIsoPt f v z') :
    muPt f v z = muPt f v z' ↔ z' = z ∨ z' = -z := by
  constructor
  · intro h
    obtain ⟨γ, hγ⟩ := exists_smul_eq_of_perp hf hm hv hz.1 hz.2.1 hz.2.2 hz'.2.2
      (fun w hw hwv hwz => by
        have : reflBar f w ∈ muPt f v z' := h ▸ ⟨w, hw, hwv, hwz, rfl⟩
        rw [hf.symm]
        exact ((reflBar_mem_muPt_iff hf (by omega) hw).1 this).2)
      (Or.inl hz'.2.1)
    have hγ0 : γ ≠ 0 := by
      rintro rfl
      rw [zero_smul] at hγ
      exact hz'.1 hγ
    rcases (show ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 by decide) γ hγ0 with rfl | rfl
    · left; rw [hγ, one_smul]
    · right; rw [hγ, neg_one_smul]
  · rintro (rfl | rfl)
    · rfl
    · rw [← neg_one_smul (ZMod 3) z, muPt_smul (by decide)]

theorem image_conj_muPt (hf : IsF3Form f) {v w : Fin m → ZMod 3} (hw : f w w = 1)
    (hwv : f w v = 0) (z : Fin m → ZMod 3) :
    (fun s => reflBar f w * s * reflBar f w) '' muPt f v z =
      muPt f v (act (F3.refl f w) z) := by
  have hiso := isIsom_refl hf w
  have hfix : act (F3.refl f w) v = v := act_refl_of_perp hw (by rw [hf.symm]; exact hwv)
  have hinv : ∀ x, act (F3.refl f w) (act (F3.refl f w) x) = x := fun x => by
    rw [← act_mul, refl_mul_self, act_one]
  ext q
  constructor
  · rintro ⟨_, ⟨w', hw', hw'v, hw'z, rfl⟩, rfl⟩
    refine ⟨act (F3.refl f w) w', by rw [hiso.norm, hw'], ?_, ?_, (reflBar_conj hf w w').symm⟩
    · rw [← hfix, hiso, hw'v]
    · rw [hiso, hw'z]
  · rintro ⟨w'', hw'', hw''v, hw''z, rfl⟩
    refine ⟨reflBar f (act (F3.refl f w) w''), ⟨act (F3.refl f w) w'', by rw [hiso.norm, hw''],
      ?_, ?_, rfl⟩, ?_⟩
    · calc f (act (F3.refl f w) w'') v = f (act (F3.refl f w) w'') (act (F3.refl f w) v) := by
            rw [hfix]
        _ = 0 := by rw [hiso, hw''v]
    · calc f (act (F3.refl f w) w'') z
          = f (act (F3.refl f w) w'') (act (F3.refl f w) (act (F3.refl f w) z)) := by
            rw [hinv]
        _ = 0 := by rw [hiso, hw''z]
    · show reflBar f w * reflBar f (act (F3.refl f w) w'') * reflBar f w = reflBar f w''
      rw [reflBar_conj hf, hinv]

theorem muGraph_adj_iff (hf : IsF3Form f) (hm : 5 ≤ m) {v : Fin m → ZMod 3} (hv : f v v = 1)
    {O Q : muFamily (D3 f) (reflBar f v)} {z z' : Fin m → ZMod 3} (hz : IsIsoPt f v z)
    (hz' : IsIsoPt f v z') (hO : (O : Set (R3 f)) = muPt f v z)
    (hQ : (Q : Set (R3 f)) = muPt f v z') :
    (muGraph (D3 f) (reflBar f v)).Adj O Q ↔ f z z' ≠ 0 := by
  have hm4 : 4 ≤ m := by omega
  rw [Pair.muGraph_adj (pair_R3 hf hm4), Ne, Subtype.ext_iff, hO, hQ]
  constructor
  · rintro ⟨-, g, hg, hgO, himg⟩
    rw [localClass_D3 hf hm4 hv] at hg
    obtain ⟨w, hw, hwv, rfl⟩ := hg
    have hwz : f w z ≠ 0 := fun h => hgO ⟨w, hw, hwv, h, rfl⟩
    rw [image_conj_muPt hf hw hwv] at himg
    have hzw : f z w ≠ 0 := by rwa [hf.symm]
    have hsq : f z (act (F3.refl f w) z) ≠ 0 := by
      rw [act_refl hw, LinearMap.BilinForm.add_right, LinearMap.BilinForm.smul_right, hz.2.1,
        zero_add, hf.symm z w, mul_self_of_ne_zero hwz]
      exact one_ne_zero
    rcases (muPt_eq_muPt_iff hf hm hv (isIsoPt_act_refl hf hw hwv hz) hz').1 himg with h | h
    · rwa [h]
    · rw [h, LinearMap.BilinForm.neg_right]
      exact neg_ne_zero.2 hsq
  · intro hzz'
    have hβ := mul_self_of_ne_zero hzz'
    have hz'z : f z' z = f z z' := hf.symm z' z
    refine ⟨fun h => ?_, reflBar f (f z z' • z' - z), ?_, ?_, ?_⟩
    · rcases (muPt_eq_muPt_iff hf hm hv hz hz').1 h with h | h <;> rw [h] at hzz'
      · exact hzz' hz.2.1
      · rw [LinearMap.BilinForm.neg_right, hz.2.1, neg_zero] at hzz'
        exact hzz' rfl
    · have hn : f (f z z' • z' - z) (f z z' • z' - z) = 1 := by
        simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
          LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hz.2.1, hz'.2.1, hz'z]
        linear_combination (-2 : ZMod 3) * hβ - three_eq_zero
      exact reflBar_mem_localClass hf hm4 hv hn (by
        rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hz'.2.2, hz.2.2]
        ring)
    · rintro ⟨w, hw, -, hwz, h⟩
      have hw' : f (f z z' • z' - z) (f z z' • z' - z) = 1 := by
        simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
          LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hz.2.1, hz'.2.1, hz'z]
        linear_combination (-2 : ZMod 3) * hβ - three_eq_zero
      have := pair_eq_zero_of_reflBar_eq hf hm4 hw' hw h hwz
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hz'z, hz.2.1, hβ,
        sub_zero] at this
      exact one_ne_zero this
    · have hn : f (f z z' • z' - z) (f z z' • z' - z) = 1 := by
        simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
          LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, hz.2.1, hz'.2.1, hz'z]
        linear_combination (-2 : ZMod 3) * hβ - three_eq_zero
      rw [image_conj_muPt hf hn (by
        rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hz'.2.2, hz.2.2]
        ring), act_refl hn]
      have : f z (f z z' • z' - z) = 1 := by
        rw [LinearMap.BilinForm.sub_right, LinearMap.BilinForm.smul_right, hz.2.1, hβ, sub_zero]
      rw [this, one_smul, add_sub_cancel, muPt_smul hzz']

theorem localQuotientEquivR3_image_muPt {n : ℕ} (hf : IsF3Form f) (hm : 4 ≤ m)
    {v : Fin m → ZMod 3} (hv : f v v = 1) (e : F3.perpOne f v ≃ₗ[ZMod 3] (Fin n → ZMod 3))
    {f' : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)}
    (hf' : ∀ a b : F3.perpOne f v, f' (e a) (e b) = f a b) {z : Fin m → ZMod 3}
    (hzv : f z v = 0) :
    localQuotientEquivR3 hf hm hv e hf' ''
        (starImage (D3 f) (reflBar f v) '' {p | (p : R3 f) ∈ muPt f v z}) =
      {q | ∃ w', f' w' w' = 1 ∧ f' w' (e ⟨z, F3.mem_perpOne.2 hzv⟩) = 0 ∧ reflBar f' w' = q} := by
  ext q
  constructor
  · rintro ⟨_, ⟨p, ⟨w, hw, hwv, hwz, hpw⟩, rfl⟩, rfl⟩
    have hp : p = ⟨reflBar f w, reflBar_mem_localClass hf hm hv hw hwv⟩ := Subtype.ext hpw.symm
    rw [hp, localQuotientEquivR3_starImage hf hm hv e hf' hw hwv]
    exact ⟨e ⟨w, F3.mem_perpOne.2 hwv⟩, by rw [hf']; exact hw, by rw [hf']; exact hwz, rfl⟩
  · rintro ⟨w', hw', hw'z, rfl⟩
    have hx : f (e.symm w' : Fin m → ZMod 3) (e.symm w') = 1 := by
      rw [← hf', e.apply_symm_apply]; exact hw'
    have hxv : f (e.symm w' : Fin m → ZMod 3) v = 0 := F3.mem_perpOne.1 (e.symm w').2
    have hxz : f (e.symm w' : Fin m → ZMod 3) z = 0 := by
      have := hf' (e.symm w') ⟨z, F3.mem_perpOne.2 hzv⟩
      rw [e.apply_symm_apply] at this
      rw [← this]
      exact hw'z
    refine ⟨_, ⟨⟨reflBar f (e.symm w'), reflBar_mem_localClass hf hm hv hx hxv⟩,
      ⟨_, hx, hxv, hxz, rfl⟩, rfl⟩, ?_⟩
    rw [localQuotientEquivR3_starImage hf hm hv e hf' hx hxv, Subtype.coe_eta,
      e.apply_symm_apply]

theorem tripleProperty_D3 (hf : IsF3Form f) (hm : 5 ≤ m) : TripleProperty (D3 f) := by
  have hm4 : 4 ≤ m := by omega
  intro e x he hx hex y hy
  obtain ⟨v, hv, rfl⟩ := mem_D3_iff.1 he
  obtain ⟨u, hu, rfl⟩ := mem_D3_iff.1 hx
  have hvu : f v u ≠ 0 := fun h => hex ((reflBar_commute_iff hf hm4 hv hu).2 (Or.inl h))
  have huv : f u v ≠ 0 := by rwa [hf.symm]
  obtain ⟨u₁, hu₁u₁, hu₁v, hreq⟩ :
      ∃ u₁, f u₁ u₁ = 1 ∧ f u₁ v = 1 ∧ reflBar f u₁ = reflBar f u :=
    ⟨f u v • u, by rw [norm_smul, mul_self_of_ne_zero huv, hu, one_mul],
      by rw [LinearMap.BilinForm.smul_left, mul_self_of_ne_zero huv], reflBar_smul huv u⟩
  rw [← hreq] at hy hex ⊢
  obtain ⟨hyD, hsub⟩ := hy
  obtain ⟨t, ht, rfl⟩ := mem_D3_iff.1 hyD
  rw [muSet_eq_muPt hf hm4 hv hu₁u₁] at hsub
  have hvu₁ : f v u₁ = 1 := by rw [hf.symm]; exact hu₁v
  have hzv : f (u₁ - v) v = 0 := by rw [LinearMap.BilinForm.sub_left, hu₁v, hv, sub_self]
  have hzz : f (u₁ - v) (u₁ - v) = 0 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right, hu₁u₁, hu₁v, hvu₁,
      hv]
    ring
  have hz0 : u₁ - v ≠ 0 := fun h0 => hex (by rw [sub_eq_zero.1 h0])
  have htN : ∀ w, f w w = 1 → f w v = 0 → f w (u₁ - v) = 0 → f w t = 0 := fun w hw hwv hwz =>
    (reflBar_mem_localClass_iff hf hm4 ht hw).1 (hsub ⟨w, hw, hwv, hwz, rfl⟩)
  have hvv : ∀ w, f w v = 0 → f v w = 0 := fun w h => by rw [hf.symm]; exact h
  obtain ⟨γ, hγ⟩ := exists_smul_eq_of_perp hf hm hv hz0 hzz hzv (s := t - f t v • v)
    (by rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hv, mul_one, sub_self])
    (fun w hw hwv hwz => by
      rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hvv w hwv, mul_zero,
        sub_zero, hf.symm]
      exact htN w hw hwv hwz)
    (by
      have key : ∀ a : ZMod 3, 1 - a * a - a * a + a * a * 1 = 0 ∨
          1 - a * a - a * a + a * a * 1 = 1 := by decide
      simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
        LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right, ht, hv, hf.symm v t]
      have := key (f t v)
      ring_nf at this ⊢
      exact this)
  set β := f t v
  have ht' : t = β • v + γ • (u₁ - v) := by rw [← hγ]; abel
  have hβ : β * β = 1 := by
    have := ht
    rw [ht', norm_add hf, norm_smul, norm_smul, hv, hzz, LinearMap.BilinForm.smul_left,
      LinearMap.BilinForm.smul_right, hvv _ hzv] at this
    linear_combination this
  have hβ0 : β ≠ 0 := fun h => by rw [h, mul_zero] at hβ; exact zero_ne_one hβ
  have hrefl : reflBar f t = reflBar f (v + (β * γ) • (u₁ - v)) := by
    rw [← reflBar_smul hβ0 (v + (β * γ) • (u₁ - v)), smul_add, smul_smul, ← mul_assoc, hβ,
      one_mul, ← ht']
  rw [hrefl]
  rcases (show ∀ c : ZMod 3, c = 0 ∨ c = 1 ∨ c = -1 by decide) (β * γ) with hc | hc | hc <;>
    rw [hc]
  · left
    rw [zero_smul, add_zero]
  · right; left
    rw [one_smul, add_sub_cancel]
  · right; right
    rw [reflBar_conj hf, act_refl hv, hu₁v, one_smul, ← reflBar_neg]
    congr 1
    linear_combination (norm := module) three_eq_zero • v

@[expose] noncomputable def muVertex (hf : IsF3Form f) (hm : 4 ≤ m) {v : Fin m → ZMod 3}
    (hv : f v v = 1) {z : Fin m → ZMod 3} (hz : IsIsoPt f v z) :
    muFamily (D3 f) (reflBar f v) :=
  ⟨muPt f v z, muPt_mem_muFamily hf hm hv hz⟩

theorem isIsoPt_of_pair_ne_zero {v x y : Fin m → ZMod 3} (hxx : f x x = 0) (hxv : f x v = 0)
    (hxy : f x y ≠ 0) : IsIsoPt f v x :=
  ⟨fun h => hxy (by rw [h, map_zero, LinearMap.zero_apply]), hxx, hxv⟩

section Rigid

variable (hf : IsF3Form f) (hm : 5 ≤ m) {v z₀ : Fin m → ZMod 3} (hv : f v v = 1)
  (hz₀ : IsIsoPt f v z₀)

include hf hm hv hz₀ in
theorem coverRigid_muGraph_D3 :
    CoverRigid (muGraph (D3 f) (reflBar f v)) (muVertex hf (by omega) hv hz₀) := by
  have hm4 : 4 ≤ m := by omega
  set G := muGraph (D3 f) (reflBar f v)
  have hadj : ∀ {O Q : muFamily (D3 f) (reflBar f v)} {z z' : Fin m → ZMod 3},
      IsIsoPt f v z → IsIsoPt f v z' → (O : Set (R3 f)) = muPt f v z →
        (Q : Set (R3 f)) = muPt f v z' → (G.Adj O Q ↔ f z z' ≠ 0) :=
    fun hz hz' hO hQ => muGraph_adj_iff hf hm hv hz hz' hO hQ
  have far : ∀ O : muFamily (D3 f) (reflBar f v), O ≠ muVertex hf hm4 hv hz₀ →
      ¬ G.Adj (muVertex hf hm4 hv hz₀) O → ∀ z, IsIsoPt f v z →
        (O : Set (R3 f)) = muPt f v z → f z₀ z = 0 ∧ ∀ a : ZMod 3, z ≠ a • z₀ := by
    intro O hO hrO z hz hOz
    refine ⟨by_contra fun h => hrO ((hadj hz₀ hz rfl hOz).2 h), fun a ha => hO ?_⟩
    have ha0 : a ≠ 0 := by
      rintro rfl
      rw [zero_smul] at ha
      exact hz.1 ha
    apply Subtype.ext
    show (O : Set (R3 f)) = muPt f v z₀
    rw [hOz, ha, muPt_smul ha0]
  refine ⟨fun O hO hrO => ?_, fun O hO hrO => ?_, fun O O' hO hrO hO' hrO' hOO' => ?_⟩
  ·
    obtain ⟨z, hz, hOz⟩ := exists_eq_muPt hf hm4 hv O
    obtain ⟨hz₀z, hind⟩ := far O hO hrO z hz hOz
    obtain ⟨x, hxx, hxv, hxz₀, hxz⟩ :=
      exists_isotropic_pairings hf hv hz₀.1 hz₀.2.1 hz₀.2.2 hz.2.2 hz₀z hind 1
    have hx := isIsoPt_of_pair_ne_zero hxx hxv (y := z₀) (by rw [hxz₀]; exact one_ne_zero)
    refine ⟨muVertex hf hm4 hv hx, (hadj hz₀ hx rfl rfl).2 ?_, (hadj hx hz rfl hOz).2 ?_⟩
    · rw [hf.symm, hxz₀]; exact one_ne_zero
    · rw [hxz]; exact one_ne_zero
  ·
    obtain ⟨z, hz, hOz⟩ := exists_eq_muPt hf hm4 hv O
    obtain ⟨hz₀z, hind⟩ := far O hO hrO z hz hOz
    set C := {x | G.Adj (muVertex hf hm4 hv hz₀) x ∧ G.Adj x O}
    have memC : ∀ {y} (hy : IsIsoPt f v y), f y z₀ ≠ 0 → f y z ≠ 0 →
        muVertex hf hm4 hv hy ∈ C := fun hy h1 h2 =>
      ⟨(hadj hz₀ hy rfl rfl).2 (by rwa [hf.symm]), (hadj hy hz rfl hOz).2 h2⟩
    have repC : ∀ a : C, ∃ y, IsIsoPt f v y ∧ ((a : muFamily (D3 f) (reflBar f v)) :
        Set (R3 f)) = muPt f v y ∧ f y z₀ ≠ 0 ∧ f y z ≠ 0 := by
      intro a
      obtain ⟨y, hy, hay⟩ := exists_eq_muPt hf hm4 hv a
      refine ⟨y, hy, hay, ?_, (hadj hy hz hay hOz).1 a.2.2⟩
      rw [hf.symm]
      exact (hadj hz₀ hy rfl hay).1 a.2.1
    have step : ∀ (a : C) (y₁ y₂ : Fin m → ZMod 3), IsIsoPt f v y₁ →
        ((a : muFamily (D3 f) (reflBar f v)) : Set (R3 f)) = muPt f v y₁ →
        f y₁ z₀ ≠ 0 → f y₁ z ≠ 0 → f y₂ z₀ ≠ 0 → f y₂ z ≠ 0 →
        f y₁ z * f y₁ z₀ = f y₂ z * f y₂ z₀ →
        ∃ y, ∃ hy : IsIsoPt f v y, ∃ hyC : muVertex hf hm4 hv hy ∈ C,
          (G.induce C).Adj a ⟨_, hyC⟩ ∧ f y y₂ ≠ 0 ∧ f y z₀ ≠ 0 ∧ f y z ≠ 0 ∧
            f y z * f y z₀ = -(f y₁ z * f y₁ z₀) := by
      intro a y₁ y₂ hy₁ ha h1 h1' h2 h2' hs
      obtain ⟨y, hyy, hyv, hyz₀, hyz, hyy₁, hyy₂, hσ⟩ := exists_common_neighbor hf hv hz₀.1
        hz₀.2.1 hz₀.2.2 hz.2.1 hz.2.2 hz₀z hind h1 h1' h2 h2' hs
      have hy := isIsoPt_of_pair_ne_zero hyy hyv hyz₀
      refine ⟨y, hy, memC hy hyz₀ hyz, ?_, hyy₂, hyz₀, hyz, hσ⟩
      rw [SimpleGraph.induce_adj]
      exact (hadj hy₁ hy ha rfl).2 (by rwa [hf.symm])
    have same : ∀ (a b : C) (y₁ y₂ : Fin m → ZMod 3), IsIsoPt f v y₁ → IsIsoPt f v y₂ →
        ((a : muFamily (D3 f) (reflBar f v)) : Set (R3 f)) = muPt f v y₁ →
        ((b : muFamily (D3 f) (reflBar f v)) : Set (R3 f)) = muPt f v y₂ →
        f y₁ z₀ ≠ 0 → f y₁ z ≠ 0 → f y₂ z₀ ≠ 0 → f y₂ z ≠ 0 →
        f y₁ z * f y₁ z₀ = f y₂ z * f y₂ z₀ → (G.induce C).Reachable a b := by
      intro a b y₁ y₂ hy₁ hy₂ ha hb h1 h1' h2 h2' hs
      obtain ⟨y, hy, hyC, haY, hyy₂, -⟩ := step a y₁ y₂ hy₁ ha h1 h1' h2 h2' hs
      have hYb : (G.induce C).Adj ⟨_, hyC⟩ b := by
        rw [SimpleGraph.induce_adj]
        exact (hadj hy hy₂ rfl hb).2 hyy₂
      exact haY.reachable.trans hYb.reachable
    rw [SimpleGraph.connected_iff]
    refine ⟨fun a b => ?_, ?_⟩
    · obtain ⟨y₁, hy₁, ha, h1, h1'⟩ := repC a
      obtain ⟨y₂, hy₂, hb, h2, h2'⟩ := repC b
      by_cases hs : f y₁ z * f y₁ z₀ = f y₂ z * f y₂ z₀
      · exact same a b y₁ y₂ hy₁ hy₂ ha hb h1 h1' h2 h2' hs
      · obtain ⟨y, hy, hyC, haY, -, hyz₀, hyz, hσ⟩ := step a y₁ y₁ hy₁ ha h1 h1' h1 h1' rfl
        have hσ' : f y z * f y z₀ = f y₂ z * f y₂ z₀ := by
          rw [hσ]
          have key : ∀ s t : ZMod 3, s ≠ 0 → t ≠ 0 → s ≠ t → -s = t := by decide
          exact key _ _ (mul_ne_zero h1' h1) (mul_ne_zero h2' h2) hs
        exact haY.reachable.trans (same ⟨_, hyC⟩ b y y₂ hy hy₂ rfl hb hyz₀ hyz h2 h2' hσ')
    · obtain ⟨z₁, hz₁, hz₀z₁, hz₁z⟩ : ∃ x, ∃ hx : IsIsoPt f v x, f x z₀ ≠ 0 ∧ f x z ≠ 0 := by
        obtain ⟨x, hxx, hxv, hxz₀, hxz⟩ :=
          exists_isotropic_pairings hf hv hz₀.1 hz₀.2.1 hz₀.2.2 hz.2.2 hz₀z hind 1
        exact ⟨x, isIsoPt_of_pair_ne_zero hxx hxv (y := z₀) (by rw [hxz₀]; exact one_ne_zero),
          by rw [hxz₀]; exact one_ne_zero, by rw [hxz]; exact one_ne_zero⟩
      exact ⟨⟨_, memC hz₁ hz₀z₁ hz₁z⟩⟩
  ·
    obtain ⟨z, hz, hOz⟩ := exists_eq_muPt hf hm4 hv O
    obtain ⟨z', hz', hO'z'⟩ := exists_eq_muPt hf hm4 hv O'
    obtain ⟨hz₀z, -⟩ := far O hO hrO z hz hOz
    obtain ⟨hz₀z', -⟩ := far O' hO' hrO' z' hz' hO'z'
    have hzz' : f z z' ≠ 0 := (hadj hz hz' hOz hO'z').1 hOO'
    obtain ⟨x, hxx, hxv, hxz₀, hxz, hxz'⟩ := exists_isotropic_pairings₄ hf hv hz₀.1 hz₀.2.1
      hz₀.2.2 hz.2.1 hz.2.2 hz'.2.1 hz'.2.2 hz₀z hz₀z' hzz'
    have hx := isIsoPt_of_pair_ne_zero hxx hxv (y := z₀) (by rw [hxz₀]; exact one_ne_zero)
    refine ⟨muVertex hf hm4 hv hx, (hadj hz₀ hx rfl rfl).2 ?_, (hadj hx hz rfl hOz).2 ?_,
      (hadj hx hz' rfl hO'z').2 ?_⟩
    · rw [hf.symm, hxz₀]; exact one_ne_zero
    · rw [hxz]; exact one_ne_zero
    · rw [hxz']; exact one_ne_zero

end Rigid

end CFSG.Fischer.Classification

