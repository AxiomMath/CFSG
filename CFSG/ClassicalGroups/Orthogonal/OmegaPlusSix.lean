module

public import CFSG.ClassicalGroups.Orthogonal.RootGroupExt
public import CFSG.ClassicalGroups.Orthogonal.OmegaMinusFour

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.ClassicalGroups CFSG.ClassicalGroups.F2Fixed QuadraticMap Module

section Anisotropic

theorem exists_anisotropic_form (K : Type*) [Field K] [Finite K] [CharP K 2] :
    ∃ c : K, ∀ s t : K, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0 := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hnotinj : ¬ Function.Injective (fun x : K => x ^ 2 + x) := by
    intro h
    have h01 : (fun x : K => x ^ 2 + x) 0 = (fun x : K => x ^ 2 + x) 1 := by
      simp only
      linear_combination (-1 : K) * h2
    exact zero_ne_one (h h01)
  have hnotsurj : ¬ Function.Surjective (fun x : K => x ^ 2 + x) := fun hs =>
    hnotinj (Finite.injective_iff_surjective.mpr hs)
  simp only [Function.Surjective, not_forall, not_exists] at hnotsurj
  obtain ⟨c, hc⟩ := hnotsurj
  refine ⟨c, fun s t h => ?_⟩
  by_cases ht : t = 0
  · subst ht
    have hs : s ^ 2 = 0 := by simpa using h
    exact ⟨pow_eq_zero_iff two_ne_zero |>.mp hs, rfl⟩
  · exfalso
    apply hc (s / t)
    field_simp
    linear_combination h - c * t ^ 2 * h2

end Anisotropic

section Frame

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

structure MinusFrame (Q : QuadraticForm K V) (c : K) (e f a b : V) : Prop where
  Q_e : Q e = 0
  Q_f : Q f = 0
  Q_a : Q a = 1
  Q_b : Q b = c
  ef : polar Q e f = 1
  ea : polar Q e a = 0
  eb : polar Q e b = 0
  fa : polar Q f a = 0
  fb : polar Q f b = 0
  ab : polar Q a b = 1
  anis : ∀ s t : K, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0

variable (K) in
@[expose] def frame4 (e f a b : V) : Submodule K V := Submodule.span K (Set.range ![e, f, a, b])

theorem mem_frame4 {e f a b z : V} :
    z ∈ frame4 K e f a b ↔ ∃ x y s t : K, z = x • e + y • f + s • a + t • b := by
  rw [frame4, Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g 0, g 1, g 2, g 3, ?_⟩
    rw [← hg, Fin.sum_univ_four]
    simp
  · rintro ⟨x, y, s, t, rfl⟩
    refine ⟨![x, y, s, t], ?_⟩
    rw [Fin.sum_univ_four]
    simp

theorem mem_span_range_pair_iff {a b y : V} :
    y ∈ Submodule.span K (Set.range ![a, b]) ↔ ∃ s t : K, y = s • a + t • b := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨g, hg⟩
    refine ⟨g 0, g 1, ?_⟩
    rw [← hg, Fin.sum_univ_two]
    simp
  · rintro ⟨s, t, rfl⟩
    refine ⟨![s, t], ?_⟩
    rw [Fin.sum_univ_two]
    simp

theorem polar_comb4_left {e f a b : V} (x y s t : K) (z : V) :
    polar Q (x • e + y • f + s • a + t • b) z =
      x * polar Q e z + y * polar Q f z + s * polar Q a z + t * polar Q b z := by
  simp only [polar_add_left, polar_smul_left_eq]

namespace MinusFrame

variable {c : K} {e f a b : V} (hF : MinusFrame Q c e f a b)

include hF

theorem fe : polar Q f e = 1 := by rw [polar_comm, hF.ef]

theorem ae : polar Q a e = 0 := by rw [polar_comm, hF.ea]

theorem af : polar Q a f = 0 := by rw [polar_comm, hF.fa]

theorem be : polar Q b e = 0 := by rw [polar_comm, hF.eb]

theorem bf : polar Q b f = 0 := by rw [polar_comm, hF.fb]

theorem ba : polar Q b a = 1 := by rw [polar_comm, hF.ab]

theorem ee : polar Q e e = 0 := polar_self_eq_zero hF.Q_e

theorem ff : polar Q f f = 0 := polar_self_eq_zero hF.Q_f

theorem aa [CharP K 2] : polar Q a a = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

theorem bb [CharP K 2] : polar Q b b = 0 := by
  rw [polar_self_eq_two_mul, CharTwo.two_eq_zero, zero_mul]

theorem polar_comb_e [CharP K 2] (x y s t : K) :
    polar Q (x • e + y • f + s • a + t • b) e = y := by
  rw [polar_comb4_left, hF.ee, hF.fe, hF.ae, hF.be]; ring

theorem polar_comb_f [CharP K 2] (x y s t : K) :
    polar Q (x • e + y • f + s • a + t • b) f = x := by
  rw [polar_comb4_left, hF.ef, hF.ff, hF.af, hF.bf]; ring

theorem polar_comb_a [CharP K 2] (x y s t : K) :
    polar Q (x • e + y • f + s • a + t • b) a = t := by
  rw [polar_comb4_left, hF.ea, hF.fa, hF.aa, hF.ba]; ring

theorem polar_comb_b [CharP K 2] (x y s t : K) :
    polar Q (x • e + y • f + s • a + t • b) b = s := by
  rw [polar_comb4_left, hF.eb, hF.fb, hF.ab, hF.bb]; ring

theorem Q_comb (x y s t : K) :
    Q (x • e + y • f + s • a + t • b) = x * y + (s ^ 2 + s * t + c * t ^ 2) := by
  rw [QuadraticMap.map_add Q (x • e + y • f + s • a) (t • b),
    QuadraticMap.map_add Q (x • e + y • f) (s • a), QuadraticMap.map_add Q (x • e) (y • f),
    map_smul_eq_sq, map_smul_eq_sq, map_smul_eq_sq, map_smul_eq_sq]
  simp only [polar_add_left, polar_add_right, polar_smul_left_eq, polar_smul_right_eq, hF.Q_e,
    hF.Q_f, hF.Q_a, hF.Q_b, hF.ef, hF.fe, hF.ea, hF.eb, hF.fa, hF.fb, hF.ae, hF.af, hF.be, hF.bf,
    hF.ab, hF.ba, hF.ee, hF.ff]
  ring

theorem Q_pair (s t : K) : Q (s • a + t • b) = s ^ 2 + s * t + c * t ^ 2 := by
  have := hF.Q_comb 0 0 s t
  simpa using this

theorem coeffs_eq_zero [CharP K 2] {x y s t : K}
    (he : polar Q (x • e + y • f + s • a + t • b) e = 0)
    (hf : polar Q (x • e + y • f + s • a + t • b) f = 0)
    (ha : polar Q (x • e + y • f + s • a + t • b) a = 0)
    (hb : polar Q (x • e + y • f + s • a + t • b) b = 0) :
    x = 0 ∧ y = 0 ∧ s = 0 ∧ t = 0 := by
  rw [hF.polar_comb_e] at he
  rw [hF.polar_comb_f] at hf
  rw [hF.polar_comb_a] at ha
  rw [hF.polar_comb_b] at hb
  exact ⟨hf, he, hb, ha⟩

theorem linearIndependent [CharP K 2] : LinearIndependent K ![e, f, a, b] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_four] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.cons_val_three, Matrix.tail_cons] at hg
  have h := hF.coeffs_eq_zero (x := g 0) (y := g 1) (s := g 2) (t := g 3)
    (by rw [hg, polar_zero_left]) (by rw [hg, polar_zero_left]) (by rw [hg, polar_zero_left])
    (by rw [hg, polar_zero_left])
  intro i
  fin_cases i
  · exact h.1
  · exact h.2.1
  · exact h.2.2.1
  · exact h.2.2.2

theorem linearIndependent_pair : LinearIndependent K ![a, b] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_two] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
  have hQ0 : Q (g 0 • a + g 1 • b) = 0 := by rw [hg]; exact QuadraticMap.map_zero Q
  rw [hF.Q_pair] at hQ0
  obtain ⟨h0, h1⟩ := hF.anis _ _ hQ0
  intro i
  fin_cases i
  · exact h0
  · exact h1

theorem e_mem : e ∈ frame4 K e f a b := Submodule.subset_span ⟨0, rfl⟩

theorem f_mem : f ∈ frame4 K e f a b := Submodule.subset_span ⟨1, rfl⟩

theorem a_mem : a ∈ frame4 K e f a b := Submodule.subset_span ⟨2, rfl⟩

theorem b_mem : b ∈ frame4 K e f a b := Submodule.subset_span ⟨3, rfl⟩

theorem finrank_frame4 [CharP K 2] : Module.finrank K (frame4 K e f a b) = 4 := by
  rw [frame4, finrank_span_eq_card hF.linearIndependent]
  simp

theorem polarNondegOn_frame4 [CharP K 2] : PolarNondegOn Q (frame4 K e f a b) := by
  intro z hz hz'
  obtain ⟨x, y, s, t, rfl⟩ := mem_frame4.mp hz
  obtain ⟨hx, hy, hs, ht⟩ := hF.coeffs_eq_zero (hz' e hF.e_mem) (hz' f hF.f_mem)
    (hz' a hF.a_mem) (hz' b hF.b_mem)
  simp [hx, hy, hs, ht]

theorem exists_ne_zero_restrict [CharP K 2] [FiniteDimensional K V] {W : Submodule K V}
    (hW : W = frame4 K e f a b) (U : Submodule K W) (hU : Module.finrank K U = 2) :
    ∃ x ∈ U, (Q.restrict W) x ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hWfin : Module.finrank K W = 4 := by rw [hW]; exact hF.finrank_frame4
  have he_mem : e ∈ W := by rw [hW]; exact hF.e_mem
  have hf_mem : f ∈ W := by rw [hW]; exact hF.f_mem
  set A : Submodule K V := Submodule.span K (Set.range ![a, b]) with hA
  have hmemA : ∀ y : V, y ∈ A ↔ ∃ s t : K, y = s • a + t • b := fun y => mem_span_range_pair_iff
  have hAW : A ≤ W := by
    intro y hy
    obtain ⟨s, t, rfl⟩ := (hmemA y).mp hy
    rw [hW]
    exact mem_frame4.mpr ⟨0, 0, s, t, by simp⟩
  have hAdim : Module.finrank K A = 2 := by
    rw [hA, finrank_span_eq_card hF.linearIndependent_pair]
    simp
  set U' : Submodule K V := U.map W.subtype with hU'
  have hU'dim : Module.finrank K U' = 2 := by
    rw [hU', Submodule.finrank_map_subtype_eq]; exact hU
  have hU'W : U' ≤ W := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hQU' : ∀ x ∈ U', Q x = 0 := by
    rintro _ ⟨y, hy, rfl⟩
    exact hcon y hy
  have hdisj : U' ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy1, hy2⟩
    obtain ⟨s, t, rfl⟩ := (hmemA y).mp hy2
    have h0 := hQU' _ hy1
    rw [hF.Q_pair] at h0
    obtain ⟨hs, ht⟩ := hF.anis _ _ h0
    rw [hs, ht]
    simp
  have hsup : U' ⊔ A = W := by
    refine Submodule.eq_of_le_of_finrank_eq (sup_le hU'W hAW) ?_
    have h4 := Submodule.finrank_sup_add_finrank_inf_eq U' A
    rw [hdisj, finrank_bot, hU'dim, hAdim] at h4
    rw [hWfin]
    omega
  have key : ∀ v ∈ W, Q v = 0 → (∀ y ∈ A, polar Q v y = 0) → v ∈ U' := by
    intro v hv hQv hperp
    have hv' : v ∈ U' ⊔ A := by rw [hsup]; exact hv
    obtain ⟨x₁, hx₁, y₁, hy₁, rfl⟩ := Submodule.mem_sup.mp hv'
    have h1 : Q y₁ = 0 := by
      have h3 : Q ((x₁ + y₁) + -y₁) = 0 := by
        rw [add_neg_cancel_right]
        exact hQU' x₁ hx₁
      rw [QuadraticMap.map_add Q, hQv, QuadraticMap.map_neg, polar_neg_right,
        hperp y₁ hy₁] at h3
      simpa using h3
    obtain ⟨s, t, rfl⟩ := (hmemA y₁).mp hy₁
    rw [hF.Q_pair] at h1
    obtain ⟨hs, ht⟩ := hF.anis _ _ h1
    rw [hs, ht]
    simpa using hx₁
  have heU : e ∈ U' := by
    refine key e he_mem hF.Q_e fun y hy => ?_
    obtain ⟨s, t, rfl⟩ := (hmemA y).mp hy
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hF.ea, hF.eb]
    ring
  have hfU : f ∈ U' := by
    refine key f hf_mem hF.Q_f fun y hy => ?_
    obtain ⟨s, t, rfl⟩ := (hmemA y).mp hy
    rw [polar_add_right, polar_smul_right_eq, polar_smul_right_eq, hF.fa, hF.fb]
    ring
  have hef : polar Q e f = 0 := by
    rw [polar, hQU' _ (U'.add_mem heU hfU), hQU' e heU, hQU' f hfU]
    ring
  rw [hF.ef] at hef
  exact one_ne_zero hef

end MinusFrame

end Frame

section Complement

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def polarPerp (Q : QuadraticForm K V) (W : Submodule K V) : Submodule K V :=
  LinearMap.BilinForm.orthogonal (polarBilin Q) W

theorem mem_polarPerp {W : Submodule K V} {z : V} :
    z ∈ polarPerp Q W ↔ ∀ x ∈ W, polar Q z x = 0 := by
  rw [polarPerp, LinearMap.BilinForm.mem_orthogonal_iff]
  constructor
  · intro h x hx
    have := h x hx
    rw [polarBilin_apply_apply] at this
    rw [polar_comm]
    exact this
  · intro h x hx
    show polarBilin Q x z = 0
    rw [polarBilin_apply_apply, polar_comm]
    exact h x hx

theorem isCompl_polarPerp [FiniteDimensional K V] {W : Submodule K V} (hW : PolarNondegOn Q W) :
    IsCompl W (polarPerp Q W) := by
  have h : polarBilin (Q.comp W.subtype) = LinearMap.BilinForm.restrict (polarBilin Q) W := by
    refine LinearMap.ext₂ fun x y => ?_
    simp [polarBilin_apply_apply, polar]
  have hrefl : (polarBilin Q).IsRefl := fun x y h => by
    rw [polarBilin_apply_apply] at h ⊢
    rwa [polar_comm]
  exact LinearMap.BilinForm.isCompl_orthogonal_of_restrict_nondegenerate hrefl
    (by rw [← h]; exact nondegenerate_polarBilin_restrict hW)

end Complement

section Pairs

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

@[expose] def HypPair.mapGom (P : HypPair Q) (g : Gom Q) : HypPair Q where
  e := g.app P.e
  f := g.app P.f
  Q_e := by rw [Gom.map_of_mem, P.Q_e]
  Q_f := by rw [Gom.map_of_mem, P.Q_f]
  polar_ef := by rw [Gom.polar_app, P.polar_ef]

theorem HypPair.Orth.mapGom {P P' : HypPair Q} (h : P.Orth P') (g : Gom Q) :
    (P.mapGom g).Orth (P'.mapGom g) where
  ee := by
    show polar Q (g.app P.e) (g.app P'.e) = 0
    rw [Gom.polar_app, h.ee]
  ef := by
    show polar Q (g.app P.e) (g.app P'.f) = 0
    rw [Gom.polar_app, h.ef]
  fe := by
    show polar Q (g.app P.f) (g.app P'.e) = 0
    rw [Gom.polar_app, h.fe]
  ff := by
    show polar Q (g.app P.f) (g.app P'.f) = 0
    rw [Gom.polar_app, h.ff]

theorem HypPair.Orth.of_gom_app_eq {P P' R : HypPair Q} (h : P.Orth P') (g : Gom Q)
    (he : g.app P.e = R.e) (hf : g.app P.f = R.f) : R.Orth (P'.mapGom g) where
  ee := by
    rw [← he]
    show polar Q (g.app P.e) (g.app P'.e) = 0
    rw [Gom.polar_app, h.ee]
  ef := by
    rw [← he]
    show polar Q (g.app P.e) (g.app P'.f) = 0
    rw [Gom.polar_app, h.ef]
  fe := by
    rw [← hf]
    show polar Q (g.app P.f) (g.app P'.e) = 0
    rw [Gom.polar_app, h.fe]
  ff := by
    rw [← hf]
    show polar Q (g.app P.f) (g.app P'.f) = 0
    rw [Gom.polar_app, h.ff]

theorem MinusFrame.of_orth {Ph P₂ P₃ : HypPair Q} (h₁₂ : Ph.Orth P₂) (h₁₃ : Ph.Orth P₃)
    (h₂₃ : P₂.Orth P₃) {c : K} (hc : ∀ s t : K, s ^ 2 + s * t + c * t ^ 2 = 0 → s = 0 ∧ t = 0) :
    MinusFrame Q c Ph.e Ph.f (P₂.e + P₂.f) (P₂.e + P₃.e + c • P₃.f) where
  Q_e := Ph.Q_e
  Q_f := Ph.Q_f
  Q_a := by
    rw [QuadraticMap.map_add Q, P₂.Q_e, P₂.Q_f, P₂.polar_ef]
    ring
  Q_b := by
    rw [QuadraticMap.map_add Q (P₂.e + P₃.e) (c • P₃.f), QuadraticMap.map_add Q P₂.e P₃.e,
      map_smul_eq_sq, P₂.Q_e, P₃.Q_e, P₃.Q_f, polar_add_left, polar_smul_right_eq,
      polar_smul_right_eq, h₂₃.ee, h₂₃.ef, P₃.polar_ef]
    ring
  ef := Ph.polar_ef
  ea := by rw [polar_add_right, h₁₂.ee, h₁₂.ef, add_zero]
  eb := by
    rw [polar_add_right, polar_add_right, polar_smul_right_eq, h₁₂.ee, h₁₃.ee, h₁₃.ef]
    ring
  fa := by rw [polar_add_right, h₁₂.fe, h₁₂.ff, add_zero]
  fb := by
    rw [polar_add_right, polar_add_right, polar_smul_right_eq, h₁₂.fe, h₁₃.fe, h₁₃.ff]
    ring
  ab := by
    rw [polar_add_left, polar_add_right, polar_add_right, polar_smul_right_eq, P₂.polar_ee,
      h₂₃.ee, h₂₃.ef, polar_add_right, polar_add_right, polar_smul_right_eq, P₂.polar_fe,
      h₂₃.fe, h₂₃.ff]
    ring
  anis := hc

end Pairs

section Reduction

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {M : Type*} [AddCommGroup M] [DistribMulAction (Gom Q) M]

theorem fixedSub_compHom_Lom_eq {P W : Submodule K V} (hPW : IsCompl P W)
    (horth : ∀ p ∈ P, ∀ w ∈ W, polar Q p w = 0) {u w : V} (hu : u ∈ W) (hw : w ∈ W)
    (huw : polar Q u w = 0)
    (hfix : fixedSub M ({Eom Q u w} : Set (Gom Q)) = fixedSub M (Lom Q u : Set (Gom Q))) :
    @fixedSub (Gom (Q.restrict W)) _ M _ (DistribMulAction.compHom M (extId hPW horth))
        (Lom (Q.restrict W) ⟨u, hu⟩ : Set (Gom (Q.restrict W))) =
      fixedSub M (Lom Q u : Set (Gom Q)) := by
  rw [fixedSub_compHom]
  refine le_antisymm ?_ (fixedSub_anti ?_)
  · rw [← hfix]
    refine fixedSub_anti ?_
    rintro _ rfl
    refine ⟨Eom (Q.restrict W) ⟨u, hu⟩ ⟨w, hw⟩, Eom_mem_Lom (by rw [polar_restrict]; exact huw), ?_⟩
    exact extId_Eom hPW horth ⟨u, hu⟩ ⟨w, hw⟩
  · rintro _ ⟨g, hg, rfl⟩
    exact extId_mem_Lom hPW horth ⟨u, hu⟩ hg

theorem card_eq_pow_of_minusFrame [Finite K] [CharP K 2] [FiniteDimensional K V] [Finite M]
    (hQ : (polarBilin Q).Nondegenerate) (h2 : ∀ x : M, x + x = 0) (Ph : HypPair Q) {c : K}
    {a b : V} (hF : MinusFrame Q c Ph.e Ph.f a b) (hswap : ∃ g : Gom Q, g.app Ph.e = Ph.f)
    (hdec : IsCompl (fixedSub M (Lom Q Ph.e : Set (Gom Q)))
      (fixedSub M (Lom Q Ph.f : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (4 * n) := by
  obtain ⟨W, hW⟩ : ∃ W : Submodule K V, W = frame4 K Ph.e Ph.f a b := ⟨_, rfl⟩
  have hWnd : PolarNondegOn Q W := by rw [hW]; exact hF.polarNondegOn_frame4
  have hWdim : Module.finrank K W = 4 := by rw [hW]; exact hF.finrank_frame4
  have he : Ph.e ∈ W := by rw [hW]; exact hF.e_mem
  have hf : Ph.f ∈ W := by rw [hW]; exact hF.f_mem
  have ha : a ∈ W := by rw [hW]; exact hF.a_mem
  have hcompl : IsCompl (polarPerp Q W) W := (isCompl_polarPerp hWnd).symm
  have horth : ∀ p ∈ polarPerp Q W, ∀ w ∈ W, polar Q p w = 0 := fun p hp w hw =>
    mem_polarPerp.mp hp w hw
  obtain ⟨g₀, hg₀⟩ := hswap
  have hcard : Nat.card (fixedSub M (Lom Q Ph.f : Set (Gom Q))) =
      Nat.card (fixedSub M (Lom Q Ph.e : Set (Gom Q))) := by
    have := card_fixedSub_Lom (M := M) g₀ Ph.e
    rwa [hg₀] at this
  have hQa : Q a ≠ 0 := by rw [hF.Q_a]; exact one_ne_zero
  have hfe : polar Q Ph.f Ph.e ≠ 0 := by rw [Ph.polar_fe]; exact one_ne_zero
  have hef : polar Q Ph.e Ph.f ≠ 0 := by rw [Ph.polar_ef]; exact one_ne_zero
  obtain ⟨hfixe, -, -⟩ := pair_facts h2 (L₁ := Lom Q Ph.f) (L₂ := Lom Q Ph.e)
    (x := Eom Q Ph.e a) (Eom_mem_Lom hF.ea) (Eom_mul_self hF.ea)
    (closure_Lom_insert_Eom hQ Ph.Q_f Ph.Q_e hfe hF.ea hQa) hdec.symm hcard
  obtain ⟨hfixf, -, -⟩ := pair_facts h2 (L₁ := Lom Q Ph.e) (L₂ := Lom Q Ph.f)
    (x := Eom Q Ph.f a) (Eom_mem_Lom hF.fa) (Eom_mul_self hF.fa)
    (closure_Lom_insert_Eom hQ Ph.Q_e Ph.Q_f hef hF.fa hQa) hdec hcard.symm
  letI inst : DistribMulAction (Gom (Q.restrict W)) M :=
    DistribMulAction.compHom M (extId hcompl horth)
  have hdec' : IsCompl (fixedSub M (Lom (Q.restrict W) ⟨Ph.e, he⟩ : Set (Gom (Q.restrict W))))
      (fixedSub M (Lom (Q.restrict W) ⟨Ph.f, hf⟩ : Set (Gom (Q.restrict W)))) := by
    have e1 := fixedSub_compHom_Lom_eq (M := M) hcompl horth he ha hF.ea hfixe
    have e2 := fixedSub_compHom_Lom_eq (M := M) hcompl horth hf ha hF.fa hfixf
    rw [show fixedSub M (Lom (Q.restrict W) ⟨Ph.e, he⟩ : Set (Gom (Q.restrict W))) =
      fixedSub M (Lom Q Ph.e : Set (Gom Q)) from e1,
      show fixedSub M (Lom (Q.restrict W) ⟨Ph.f, hf⟩ : Set (Gom (Q.restrict W))) =
      fixedSub M (Lom Q Ph.f : Set (Gom Q)) from e2]
    exact hdec
  exact omegaMinus4_card_eq_pow (Q.restrict W) (nondegenerate_polarBilin_restrict hWnd) hWdim
    (fun U hU => hF.exists_ne_zero_restrict hW U hU) h2 (u := ⟨Ph.e, he⟩) (u' := ⟨Ph.f, hf⟩)
    Ph.Q_e Ph.Q_f (by rw [polar_restrict]; exact hef) hdec'

end Reduction

section Main

theorem omegaPlus_card_eq_pow_of_threePairs {K V : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hpairs : ∃ P : Fin 3 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    [DistribMulAction (Gom Q) M] (Ph : HypPair Q)
    (hdec : IsCompl (fixedSub M (Lom Q Ph.e : Set (Gom Q)))
      (fixedSub M (Lom Q Ph.f : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (4 * n) := by
  obtain ⟨P, hP⟩ := hpairs
  obtain ⟨c, hc⟩ := exists_anisotropic_form K
  obtain ⟨g, hge, hgf⟩ := exists_gom_pair hQ (hP 0 1 (by decide)) (P 0).Q_e (P 0).Q_f Ph.Q_e
    Ph.Q_f (P 0).polar_ef Ph.polar_ef
  obtain ⟨g₀, hg₀, -⟩ := exists_gom_pair hQ (hP 0 1 (by decide)) Ph.Q_e Ph.Q_f Ph.Q_f Ph.Q_e
    Ph.polar_ef Ph.polar_fe
  have h₁₂ : Ph.Orth ((P 1).mapGom g) := (hP 0 1 (by decide)).of_gom_app_eq g hge hgf
  have h₁₃ : Ph.Orth ((P 2).mapGom g) := (hP 0 2 (by decide)).of_gom_app_eq g hge hgf
  have h₂₃ : ((P 1).mapGom g).Orth ((P 2).mapGom g) := (hP 1 2 (by decide)).mapGom g
  exact card_eq_pow_of_minusFrame hQ h2 Ph (MinusFrame.of_orth h₁₂ h₁₃ h₂₃ hc) ⟨g₀, hg₀⟩ hdec

theorem omegaPlus6_card_eq_pow {K V : Type*} [Field K] [Finite K] [CharP K 2] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hdim : Module.finrank K V = 6)
    (hpairs : ∃ P : Fin 3 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j))
    {M : Type*} [AddCommGroup M] [Finite M] (h2 : ∀ m : M, m + m = 0)
    [DistribMulAction (Gom Q) M] (Ph : HypPair Q)
    (hdec : IsCompl (fixedSub M (Lom Q Ph.e : Set (Gom Q)))
      (fixedSub M (Lom Q Ph.f : Set (Gom Q)))) :
    ∃ n : ℕ, Nat.card M = Nat.card K ^ (4 * n) := by
  have _ := hdim
  exact omegaPlus_card_eq_pow_of_threePairs Q hQ hpairs h2 Ph hdec

end Main

end CFSG.ClassicalGroups.Orthogonal
