module

public import CFSG.LargeExtraspecial.AS35QDefs
public import CFSG.LargeExtraspecial.AS35ZNSchur

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

namespace AS35Z

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {q : QuadraticForm (ZMod 2) V}

theorem polar_sub_self_of_isTypeA {d : V ≃ₗ[ZMod 2] V} (hd : IsTypeA q d 2) (x : V) :
    polar q x (d x - x) = 0 := by
  have h1 := hd.1 x
  have h2 := hd.2.2.2.2 _ (sub_mem_commSpace d x)
  have e : d x = x + (d x - x) := by abel
  rw [e, map_add_eq, h2, add_zero] at h1
  linear_combination h1

variable [FiniteDimensional (ZMod 2) V]

theorem polar_sub_eq_one (hq : q.polarBilin.Nondegenerate) {d : V ≃ₗ[ZMod 2] V}
    (hd : IsTypeA q d 2) {x y : V} (hx : x ∉ fixSpace d) (hy : y ∉ fixSpace d)
    (hxy : x - y ∉ fixSpace d) : polar q x (d y - y) = 1 := by
  set R := fixSpace d with hR
  have hRfin : finrank (ZMod 2) R + 2 = finrank (ZMod 2) V := by
    have := finrank_commSpace_add_finrank_fixSpace d
    rw [hd.2.2.2.1, ← hR] at this
    omega
  have h1 : R < R ⊔ (ZMod 2) ∙ x := lt_of_le_of_ne le_sup_left fun h =>
    hx (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self x))
  have h2 : R ⊔ (ZMod 2) ∙ x < R ⊔ (ZMod 2) ∙ x ⊔ (ZMod 2) ∙ y := by
    refine lt_of_le_of_ne le_sup_left fun h => ?_
    have hy' : y ∈ R ⊔ (ZMod 2) ∙ x := h ▸ Submodule.mem_sup_right
      (Submodule.mem_span_singleton_self y)
    obtain ⟨r, hr, w, hw, hrw⟩ := Submodule.mem_sup.1 hy'
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
    · rw [zero_smul, add_zero] at hrw
      exact hy (hrw ▸ hr)
    · rw [one_smul] at hrw
      apply hxy
      rw [← hrw, sub_add_cancel_right]
      exact R.neg_mem hr
  have htop : R ⊔ (ZMod 2) ∙ x ⊔ (ZMod 2) ∙ y = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    have e1 := Submodule.finrank_lt_finrank_of_lt h1
    have e2 := Submodule.finrank_lt_finrank_of_lt h2
    have e3 := Submodule.finrank_le (R ⊔ (ZMod 2) ∙ x ⊔ (ZMod 2) ∙ y)
    omega
  rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) (polar q x (d y - y)) with h0 | h0
  · exfalso
    apply hx
    rw [hR, fixSpace_eq_orthogonal_commSpace_of_mem hq (OrthoF2.mem_orthogonalGroup_of_isTypeA hd),
      OrthoF2.mem_orthogonal_iff_polar]
    intro a ha
    obtain ⟨z, rfl⟩ := mem_commSpace.1 ha
    have hz : z ∈ R ⊔ (ZMod 2) ∙ x ⊔ (ZMod 2) ∙ y := htop ▸ Submodule.mem_top
    obtain ⟨rx, hrx, w, hw, rfl⟩ := Submodule.mem_sup.1 hz
    obtain ⟨r, hr, w', hw', rfl⟩ := Submodule.mem_sup.1 hrx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    obtain ⟨c', rfl⟩ := Submodule.mem_span_singleton.1 hw'
    have hdr : d r = r := mem_fixSpace.1 hr
    have e : d (r + c' • x + c • y) - (r + c' • x + c • y) = c' • (d x - x) + c • (d y - y) := by
      rw [map_add, map_add, map_smul, map_smul, hdr, smul_sub, smul_sub]
      abel
    rw [e, polar_add_right, polar_smul_right, polar_smul_right, polar_sub_self_of_isTypeA hd,
      h0, smul_zero, smul_zero, add_zero]
  · exact h0

theorem polar_map_map_of_commSpace (hq : q.polarBilin.Nondegenerate) {d : V ≃ₗ[ZMod 2] V}
    (hd : IsTypeA q d 2) {J : V →ₗ[ZMod 2] V} (hJ : Function.Injective J)
    (hJd : ∀ v, J (d v) = d (J v)) (x : V) {a : V} (ha : a ∈ commSpace d) :
    polar q (J x) (J a) = polar q x a := by
  obtain ⟨y, rfl⟩ := mem_commSpace.1 ha
  have hJR : ∀ v, J v ∈ fixSpace d ↔ v ∈ fixSpace d := by
    intro v
    rw [mem_fixSpace, mem_fixSpace, ← hJd]
    exact ⟨fun h => hJ h, fun h => by rw [h]⟩
  have hRorth : ∀ u ∈ fixSpace d, ∀ v : V, polar q u (d v - v) = 0 := by
    intro u hu v
    rw [fixSpace_eq_orthogonal_commSpace_of_mem hq (OrthoF2.mem_orthogonalGroup_of_isTypeA hd),
      OrthoF2.mem_orthogonal_iff_polar] at hu
    exact hu _ (sub_mem_commSpace d v)
  have hJa : J (d y - y) = d (J y) - J y := by rw [map_sub, hJd]
  rw [hJa]
  by_cases hx : x ∈ fixSpace d
  · rw [hRorth x hx, hRorth _ ((hJR x).2 hx)]
  by_cases hy : y ∈ fixSpace d
  · rw [mem_fixSpace.1 hy, mem_fixSpace.1 ((hJR y).2 hy), sub_self, sub_self, polar_zero_right,
      polar_zero_right]
  by_cases hxy : x - y ∈ fixSpace d
  ·
    have e : ∀ u w : V, u - w ∈ fixSpace d → d w - w = d u - u := by
      intro u w h
      have h' := mem_fixSpace.1 h
      rw [map_sub, sub_eq_iff_eq_add] at h'
      rw [h']
      abel
    rw [e x y hxy, e (J x) (J y) (by rw [← map_sub]; exact (hJR _).2 hxy),
      polar_sub_self_of_isTypeA hd, polar_sub_self_of_isTypeA hd]
  rw [polar_sub_eq_one hq hd hx hy hxy, polar_sub_eq_one hq hd (fun h => hx ((hJR x).1 h))
    (fun h => hy ((hJR y).1 h)) (fun h => hxy ((hJR _).1 (by rwa [map_sub])))]

theorem polar_map_map_of_commute (hq : q.polarBilin.Nondegenerate)
    (L : Subgroup (V ≃ₗ[ZMod 2] V)) (hiso : ∀ g ∈ L, ∀ v, q (g v) = q v)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {d : V ≃ₗ[ZMod 2] V} (hdL : d ∈ L) (hd : IsTypeA q d 2) {J : V →ₗ[ZMod 2] V}
    (hJ : Function.Injective J) (hJL : ∀ g ∈ L, ∀ v, g (J v) = J (g v)) (x a : V) :
    polar q (J x) (J a) = polar q x a := by
  have hpolar : ∀ g ∈ L, ∀ u v, polar q (g u) (g v) = polar q u v := by
    intro g hg u v
    simp only [polar, ← map_add, hiso g hg]
  set W : Submodule (ZMod 2) V :=
    { carrier := {a | ∀ x, polar q (J x) (J a) = polar q x a}
      add_mem' := fun {a b} ha hb x => by rw [map_add, polar_add_right, polar_add_right, ha, hb]
      zero_mem' := fun x => by rw [map_zero, polar_zero_right, polar_zero_right]
      smul_mem' := fun c a ha x => by rw [map_smul, polar_smul_right, polar_smul_right, ha] }
    with hW
  have hWinv : ∀ g ∈ L, ∀ w ∈ W, g w ∈ W := by
    intro g hg w hw y
    have hg' := L.inv_mem hg
    have hgg : ∀ u : V, g⁻¹ (g u) = u := fun u => by
      rw [← LinearEquiv.mul_apply, inv_mul_cancel]; rfl
    have e1 : polar q (J y) (J (g w)) = polar q (g⁻¹ (J y)) (J w) := by
      rw [← hJL g hg, ← hpolar g⁻¹ hg' (J y) (g (J w)), hgg]
    have e2 : polar q y (g w) = polar q (g⁻¹ y) w := by
      rw [← hpolar g⁻¹ hg' y (g w), hgg]
    rw [e1, hJL g⁻¹ hg', e2]
    exact hw _
  have hcomm : ∀ v, J (d v) = d (J v) := fun v => (hJL d hdL v).symm
  rcases hirr W hWinv with h0 | htop
  · exfalso
    apply hd.2.1
    refine LinearEquiv.ext fun v => ?_
    have hmem : d v - v ∈ W := fun x =>
      polar_map_map_of_commSpace hq hd hJ hcomm x (sub_mem_commSpace d v)
    rw [h0, Submodule.mem_bot, sub_eq_zero] at hmem
    exact hmem
  · have hmem : a ∈ W := htop ▸ Submodule.mem_top
    exact hmem x

omit [FiniteDimensional (ZMod 2) V] in
theorem quad_map_of_commute (L : Subgroup (V ≃ₗ[ZMod 2] V)) (hiso : ∀ g ∈ L, ∀ v, q (g v) = q v)
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hdim : 2 ≤ finrank (ZMod 2) V) {J : V →ₗ[ZMod 2] V}
    (hJL : ∀ g ∈ L, ∀ v, g (J v) = J (g v)) (hJp : ∀ x a, polar q (J x) (J a) = polar q x a)
    (v : V) : q (J v) = q v := by
  let φ : V →ₗ[ZMod 2] ZMod 2 :=
    { toFun := fun x => q (J x) - q x
      map_add' := fun x y => by
        have h1 := map_add_eq q (J x) (J y)
        have h2 := map_add_eq q x y
        rw [map_add, h1, h2, hJp]
        ring
      map_smul' := fun c x => by
        rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) c with rfl | rfl
        · simp
        · simp }
  have hker : ∀ g ∈ L, ∀ w ∈ LinearMap.ker φ, g w ∈ LinearMap.ker φ := by
    intro g hg w hw
    rw [LinearMap.mem_ker] at hw ⊢
    change q (J (g w)) - q (g w) = 0
    rw [← hJL g hg, hiso g hg, hiso g hg]
    exact hw
  rcases hirr _ hker with h0 | htop
  · exfalso
    have hinj : Function.Injective φ := LinearMap.ker_eq_bot.1 h0
    have := LinearMap.finrank_le_finrank_of_injective hinj
    rw [Module.finrank_self] at this
    omega
  · have hv : v ∈ LinearMap.ker φ := htop ▸ Submodule.mem_top
    rw [LinearMap.mem_ker] at hv
    exact sub_eq_zero.1 hv

theorem sq_add_add_one_of_commute [Nontrivial V] (L : Subgroup (V ≃ₗ[ZMod 2] V))
    (hirr : ∀ W : Submodule (ZMod 2) V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤)
    {d : V ≃ₗ[ZMod 2] V} (hdL : d ∈ L) (hd2 : finrank (ZMod 2) (commSpace d) = 2)
    {f : V →ₗ[ZMod 2] V} (hfL : ∀ g ∈ L, ∀ v, g (f v) = f (g v)) (hf0 : f ≠ 0) (hf1 : f ≠ 1) :
    f * f + f + 1 = 0 := by
  set D : Set (Module.End (ZMod 2) V) :=
    (fun g : V ≃ₗ[ZMod 2] V => (g : Module.End (ZMod 2) V)) '' (L : Set (V ≃ₗ[ZMod 2] V)) with hD
  have hirr' : ∀ W : Submodule (ZMod 2) V, (∀ e ∈ D, ∀ w ∈ W, e w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun g hg w hw => hW _ ⟨g, hg, rfl⟩ w hw
  set C : Set (Module.End (ZMod 2) V) := {e | ∀ g ∈ L, ∀ v, g (e v) = e (g v)} with hC
  have hCD : ∀ e ∈ C, ∀ x ∈ D, x * e = e * x := by
    rintro e he _ ⟨g, hg, rfl⟩
    exact LinearMap.ext fun v => he g hg v
  have hCinj : ∀ e ∈ C, e ≠ 0 → Function.Injective e := fun e he he0 =>
    AS35Z.injective_of_commute D hirr' (hCD e he) he0
  have hCsub : ∀ e ∈ C, ∀ e' ∈ C, e - e' ∈ C := by
    intro e he e' he' g hg v
    simp only [LinearMap.sub_apply, map_sub, he g hg, he' g hg]
  have h1C : (1 : Module.End (ZMod 2) V) ∈ C := fun g _ v => rfl
  have h0C : (0 : Module.End (ZMod 2) V) ∈ C := fun g _ v => by simp
  have hfC : f ∈ C := hfL
  have hmulC : ∀ e ∈ C, ∀ e' ∈ C, e * e' ∈ C := by
    intro e he e' he' g hg v
    simp only [Module.End.mul_apply, he g hg, he' g hg]
  have haddC : ∀ e ∈ C, ∀ e' ∈ C, e + e' ∈ C := by
    intro e he e' he' g hg v
    simp only [LinearMap.add_apply, map_add, he g hg, he' g hg]
  obtain ⟨a, ha, ha0⟩ : ∃ a ∈ commSpace d, a ≠ 0 := by
    by_contra h
    push Not at h
    have : commSpace d = ⊥ := eq_bot_iff.2 fun x hx => (Submodule.mem_bot _).2 (h x hx)
    rw [this, finrank_bot] at hd2
    exact absurd hd2 (by norm_num)
  have hev : ∀ e ∈ C, e a ∈ commSpace d := by
    intro e he
    obtain ⟨v, hv⟩ := mem_commSpace.1 ha
    rw [← hv, map_sub, ← he d hdL v]
    exact sub_mem_commSpace d _
  have hevinj : ∀ e ∈ C, ∀ e' ∈ C, e a = e' a → e = e' := by
    intro e he e' he' h
    by_contra hne
    have hinj := hCinj _ (hCsub e he e' he') (sub_ne_zero.2 hne)
    exact ha0 (hinj (by rw [LinearMap.sub_apply, h, sub_self, map_zero]))
  have : Finite V := Module.finite_of_finite (ZMod 2)
  have : Fintype (commSpace d) := Fintype.ofFinite _
  have hcard : Fintype.card (commSpace d) = 4 := by
    rw [Module.card_eq_pow_finrank (K := ZMod 2), ZMod.card, hd2]
    norm_num
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have h2E : ∀ e : Module.End (ZMod 2) V, e + e = 0 := fun e => LinearMap.ext fun x => h2 _
  have hf1' : f + 1 ≠ 0 := fun h => hf1 (by
    have := congrArg (· + 1) h
    simp only [zero_add, add_assoc, h2E, add_zero] at this
    exact this)
  have h01 : (0 : Module.End (ZMod 2) V) ≠ 1 := by
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    intro h
    exact hv (by have := congrArg (fun e : Module.End (ZMod 2) V => e v) h; simpa using this.symm)
  have hsq : f * f = 0 ∨ f * f = 1 ∨ f * f = f ∨ f * f = f + 1 := by
    by_contra hall
    push Not at hall
    obtain ⟨hs0, hs1, hsf, hsf1⟩ := hall
    set es : Fin 5 → Module.End (ZMod 2) V := ![0, 1, f, f + 1, f * f] with hes
    have hesC : ∀ i, es i ∈ C := by
      intro i
      fin_cases i
      · exact h0C
      · exact h1C
      · exact hfC
      · exact haddC _ hfC _ h1C
      · exact hmulC _ hfC _ hfC
    let F : Fin 5 → commSpace d := fun i => ⟨es i a, hev _ (hesC i)⟩
    have hFinj : Function.Injective F := by
      intro i j hij
      have h := hevinj _ (hesC i) _ (hesC j) (congrArg Subtype.val hij)
      by_contra hne
      fin_cases i <;> fin_cases j <;> simp [hes] at h hne <;>
        first
        | exact h01 h | exact h01 h.symm | exact hf0 h.symm | exact hf0 h
        | exact hf1 h.symm | exact hf1 h | exact hf1' h.symm | exact hf1' h
        | exact hs0 h.symm | exact hs0 h | exact hs1 h.symm | exact hs1 h
        | exact hsf h.symm | exact hsf h | exact hsf1 h.symm | exact hsf1 h
    have := Fintype.card_le_of_injective F hFinj
    rw [hcard, Fintype.card_fin] at this
    omega
  rcases hsq with h | h | h | h
  · exfalso
    apply hf0
    refine LinearMap.ext fun v => ?_
    have hinj := hCinj f hfC hf0
    apply hinj
    have := congrArg (fun e : Module.End (ZMod 2) V => e v) h
    simpa using this
  · exfalso
    have hsq1 : (f + 1) * (f + 1) = 0 := by
      have e : (f + 1) * (f + 1) = f * f + (f + f) + 1 := by noncomm_ring
      rw [e, h, h2E, add_zero, h2E]
    have hinj := hCinj _ (haddC _ hfC _ h1C) hf1'
    apply hf1'
    refine LinearMap.ext fun v => ?_
    apply hinj
    have := congrArg (fun e : Module.End (ZMod 2) V => e v) hsq1
    simpa using this
  · exfalso
    have hinj := hCinj f hfC hf0
    apply hf1
    refine LinearMap.ext fun v => ?_
    apply hinj
    have := congrArg (fun e : Module.End (ZMod 2) V => e v) h
    simpa using this
  · rw [h]
    calc f + 1 + f + 1 = (f + f) + (1 + 1) := by abel
      _ = 0 := by rw [h2E, h2E, add_zero]

end AS35Z

namespace S14

open CFSG.Fischer.Classification.Unitary in
@[expose] def SUModuleEndInput : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
    (q : QuadraticForm (ZMod 2) V), q.polarBilin.Nondegenerate → ∀ n : ℕ, 4 ≤ n →
    Module.finrank (ZMod 2) V = 2 * n →
    ∀ (L : Subgroup (V ≃ₗ[ZMod 2] V)) (D : Set (V ≃ₗ[ZMod 2] V)) (hDL : D ⊆ L),
      closure D = L → (∀ d ∈ D, IsTypeA q d 2) → (∀ g ∈ L, ∀ v, q (g v) = q v) →
      (∃ ψ : L ⧸ center L ≃* PG n, ∀ d (hd : d ∈ D),
        ψ (QuotientGroup.mk (⟨d, hDL hd⟩ : L)) ∈ DG n) →
      (∀ W : Submodule (ZMod 2) V, (∀ g ∈ L, ∀ w ∈ W, g w ∈ W) → W = ⊥ ∨ W = ⊤) →
      ∃ f : V →ₗ[ZMod 2] V, (∀ g ∈ L, ∀ v, g (f v) = f (g v)) ∧ f ≠ 0 ∧ f ≠ 1

theorem suModuleInput_of_endInput (h : SUModuleEndInput) : SUModuleInput := by
  intro V _ _ _ q hq n hn hfin L D hDL hcl hA hiso hψ hirr
  obtain ⟨f, hfL, hf0, hf1⟩ := h V q hq n hn hfin L D hDL hcl hA hiso hψ hirr
  have : Nontrivial V := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
  obtain ⟨d, hd⟩ : D.Nonempty := by
    by_contra hD
    rw [Set.not_nonempty_iff_eq_empty] at hD
    have hL : L = ⊥ := by rw [← hcl, hD, Subgroup.closure_empty]
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    rcases hirr ((ZMod 2) ∙ v) (fun g hg w hw => by
        rw [hL, Subgroup.mem_bot] at hg
        rw [hg]
        exact hw) with h0 | htop
    · exact hv ((Submodule.span_singleton_eq_bot).1 h0)
    · have h1 := finrank_span_singleton (K := ZMod 2) hv
      rw [htop, finrank_top] at h1
      omega
  have hf2 := AS35Z.sq_add_add_one_of_commute L hirr (hDL hd) (hA d hd).2.2.2.1 hfL hf0 hf1
  have hfJ : ∀ v, f (f v) + f v + v = 0 := fun v => by
    have := congrArg (fun e : Module.End (ZMod 2) V => e v) hf2
    simpa using this
  have h2 : ∀ x : V, x + x = 0 := fun x => by
    rw [← two_smul (ZMod 2), show (2 : ZMod 2) = 0 from rfl, zero_smul]
  have hinv : ∀ v, f (f v) + f v = v := fun v => by
    have e := hfJ v
    calc f (f v) + f v = f (f v) + f v + v + v := by rw [add_assoc _ v v, h2, add_zero]
      _ = v := by rw [e, zero_add]
  let J : V ≃ₗ[ZMod 2] V :=
    { f with
      invFun := fun v => f v + v
      left_inv := fun v => by
        change f (f v) + f v = v
        exact hinv v
      right_inv := fun v => by
        change f (f v + v) = v
        rw [map_add]
        exact hinv v }
  have hJf : ∀ v, J v = f v := fun v => rfl
  have hfinj : Function.Injective f := fun a b hab => J.injective (by rw [hJf, hJf, hab])
  have hJp := AS35Z.polar_map_map_of_commute hq L hiso hirr (hDL hd) (hA d hd) hfinj hfL
  refine ⟨J, fun v => by rw [hJf, hJf]; exact hfJ v, fun v => ?_, fun g hg v => ?_⟩
  · rw [hJf]
    exact AS35Z.quad_map_of_commute L hiso hirr (by omega) hfL hJp v
  · rw [hJf, hJf]
    exact hfL g hg v

end S14

end CFSG.LargeExtraspecial
