module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthLayer
public import CFSG.ClassicalInvolution.Orders.OrthogonalCount

public section

namespace CFSG.ClassicalInvolution.RouteD.NonClassical

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.Timmesfeld.ClassicalOrders CFSG.ClassicalInvolution

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section HypPairs

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V}

theorem hypPair_ext {P P' : HypPair Q} (h1 : P.e = P'.e) (h2 : P.f = P'.f) : P = P' := by
  obtain ⟨e, f, a, b, c⟩ := P
  obtain ⟨e', f', a', b', c'⟩ := P'
  simp only at h1 h2
  subst h1 h2
  rfl

theorem polar_isometryEquiv {Q' : QuadraticForm K W} (e : Q.IsometryEquiv Q') (x y : V) :
    polar Q' (e x) (e y) = polar Q x y := by
  simp only [polar, ← map_add e, QuadraticMap.IsometryEquiv.map_app]

@[expose] def hypPairMap {Q' : QuadraticForm K W} (e : Q.IsometryEquiv Q') (P : HypPair Q) :
    HypPair Q' where
  e := e P.e
  f := e P.f
  Q_e := by rw [QuadraticMap.IsometryEquiv.map_app, P.Q_e]
  Q_f := by rw [QuadraticMap.IsometryEquiv.map_app, P.Q_f]
  polar_ef := by rw [polar_isometryEquiv, P.polar_ef]

theorem stdOrth_components {Q' : QuadraticForm K W} {P' : HypPair (hypSum Q')}
    (h : (hypPair Q').Orth P') : P'.e.1 = (0, 0) ∧ P'.f.1 = (0, 0) := by
  have h1 := h.ee
  have h2 := h.fe
  have h3 := h.ef
  have h4 := h.ff
  simp only [hypPair_e, hypPair_f, polar_hypSum] at h1 h2 h3 h4
  simp at h1 h2 h3 h4
  exact ⟨Prod.ext h2 h1, Prod.ext h4 h3⟩

@[expose] noncomputable def stdComplEquiv (Q' : QuadraticForm K W) :
    {P' : HypPair (hypSum Q') // (hypPair Q').Orth P'} ≃ HypPair Q' where
  toFun P' := ⟨P'.1.e.2, P'.1.f.2, by
      have h := P'.1.Q_e
      rw [hypSum_apply, (stdOrth_components P'.2).1] at h
      simpa using h,
    by
      have h := P'.1.Q_f
      rw [hypSum_apply, (stdOrth_components P'.2).2] at h
      simpa using h,
    by
      have h := P'.1.polar_ef
      rw [polar_hypSum, (stdOrth_components P'.2).1, (stdOrth_components P'.2).2] at h
      simpa using h⟩
  invFun P := ⟨⟨((0, 0), P.e), ((0, 0), P.f), by simp [hypSum_apply, P.Q_e],
      by simp [hypSum_apply, P.Q_f], by simp [polar_hypSum, P.polar_ef]⟩,
    ⟨by simp [hypPair_e, polar_hypSum], by simp [hypPair_e, polar_hypSum],
      by simp [hypPair_f, polar_hypSum], by simp [hypPair_f, polar_hypSum]⟩⟩
  left_inv P' := by
    refine Subtype.ext (hypPair_ext ?_ ?_)
    · exact Prod.ext (stdOrth_components P'.2).1.symm rfl
    · exact Prod.ext (stdOrth_components P'.2).2.symm rfl
  right_inv P := rfl

@[expose] noncomputable def orthMapEquiv {Q' : QuadraticForm K W} (e : Q.IsometryEquiv Q')
    (P : HypPair Q) :
    {P' : HypPair Q // P.Orth P'} ≃ {P' : HypPair Q' // (hypPairMap e P).Orth P'} where
  toFun P' := ⟨hypPairMap e P'.1, ⟨by simpa [hypPairMap, polar_isometryEquiv] using P'.2.ee,
    by simpa [hypPairMap, polar_isometryEquiv] using P'.2.ef,
    by simpa [hypPairMap, polar_isometryEquiv] using P'.2.fe,
    by simpa [hypPairMap, polar_isometryEquiv] using P'.2.ff⟩⟩
  invFun P' := ⟨hypPairMap e.symm P'.1, by
    refine ⟨?_, ?_, ?_, ?_⟩
    · have := P'.2.ee
      simp only [hypPairMap] at this ⊢
      rw [← polar_isometryEquiv e, QuadraticMap.IsometryEquiv.apply_symm_apply]
      exact this
    · have := P'.2.ef
      simp only [hypPairMap] at this ⊢
      rw [← polar_isometryEquiv e, QuadraticMap.IsometryEquiv.apply_symm_apply]
      exact this
    · have := P'.2.fe
      simp only [hypPairMap] at this ⊢
      rw [← polar_isometryEquiv e, QuadraticMap.IsometryEquiv.apply_symm_apply]
      exact this
    · have := P'.2.ff
      simp only [hypPairMap] at this ⊢
      rw [← polar_isometryEquiv e, QuadraticMap.IsometryEquiv.apply_symm_apply]
      exact this⟩
  left_inv P' := Subtype.ext (hypPair_ext (by simp [hypPairMap]) (by simp [hypPairMap]))
  right_inv P' := Subtype.ext (hypPair_ext (by simp [hypPairMap]) (by simp [hypPairMap]))

@[expose] def isoOfMem {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) : Q.IsometryEquiv Q :=
  { g with map_app' := fun x => map_of_mem hg x }

theorem card_orth_hypPair {Q' : QuadraticForm K W} (hQ' : (polarBilin Q').Nondegenerate)
    (P : HypPair (hypSum Q')) :
    Nat.card {P' : HypPair (hypSum Q') // P.Orth P'} = Nat.card (HypPair Q') := by
  obtain ⟨g, hg, hge, hgf⟩ := exists_mem_orthogonalGroup_apply_pair_of_nondegenerate
    (nondegenerate_polarBilin_hypSum hQ') (hypPair Q') P
  have hmap : hypPairMap (isoOfMem hg) (hypPair Q') = P := hypPair_ext hge hgf
  have e1 := Nat.card_congr (orthMapEquiv (isoOfMem hg) (hypPair Q'))
  rw [hmap] at e1
  rw [← Nat.card_congr (stdComplEquiv Q')]
  exact e1.symm

end HypPairs

section FrameCount

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V}

@[expose] def frameEquivSigma (Q : QuadraticForm K V) :
    OFrame Q ≃ Σ P : HypPair Q, {P' : HypPair Q // P.Orth P'} where
  toFun F := ⟨F.P, F.P', F.orth⟩
  invFun x := ⟨x.1, x.2.1, x.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance finite_hypPair [Finite V] : Finite (HypPair Q) :=
  Finite.of_injective (fun P : HypPair Q => (P.e, P.f))
    (fun _ _ h => hypPair_ext (congrArg Prod.fst h) (congrArg Prod.snd h))

theorem card_frame_hypSum [Finite K] [Finite W] {Q' : QuadraticForm K W}
    (hQ' : (polarBilin Q').Nondegenerate) :
    Nat.card (OFrame (hypSum Q')) =
      Nat.card (HypPair (hypSum Q')) * Nat.card (HypPair Q') := by
  classical
  let _ : Fintype (HypPair (hypSum Q')) := Fintype.ofFinite _
  rw [Nat.card_congr (frameEquivSigma _), Nat.card_sigma,
    Finset.sum_congr rfl fun P _ => card_orth_hypPair hQ' P, Finset.sum_const, Finset.card_univ,
    smul_eq_mul, ← Nat.card_eq_fintype_card]

theorem card_hypPair_of_isometry {Q₁ : QuadraticForm K W} (e : Q.IsometryEquiv Q₁) :
    Nat.card (HypPair Q) = Nat.card (HypPair Q₁) :=
  Nat.card_congr
    { toFun := hypPairMap e
      invFun := hypPairMap e.symm
      left_inv := fun P => hypPair_ext (by simp [hypPairMap]) (by simp [hypPairMap])
      right_inv := fun P => hypPair_ext (by simp [hypPairMap]) (by simp [hypPairMap]) }

theorem card_frame_of_isometry {Q₁ : QuadraticForm K W} (e : Q.IsometryEquiv Q₁) :
    Nat.card (OFrame Q) = Nat.card (OFrame Q₁) :=
  Nat.card_congr
    { toFun := fun F => ⟨hypPairMap e F.P, hypPairMap e F.P', ⟨by
          simpa [hypPairMap, polar_isometryEquiv] using F.orth.ee,
        by simpa [hypPairMap, polar_isometryEquiv] using F.orth.ef,
        by simpa [hypPairMap, polar_isometryEquiv] using F.orth.fe,
        by simpa [hypPairMap, polar_isometryEquiv] using F.orth.ff⟩⟩
      invFun := fun F => ⟨hypPairMap e.symm F.P, hypPairMap e.symm F.P', ⟨by
          have := F.orth.ee
          rw [← polar_isometryEquiv e.symm] at this
          simpa [hypPairMap] using this,
        by
          have := F.orth.ef
          rw [← polar_isometryEquiv e.symm] at this
          simpa [hypPairMap] using this,
        by
          have := F.orth.fe
          rw [← polar_isometryEquiv e.symm] at this
          simpa [hypPairMap] using this,
        by
          have := F.orth.ff
          rw [← polar_isometryEquiv e.symm] at this
          simpa [hypPairMap] using this⟩⟩
      left_inv := fun F => by
        obtain ⟨⟨e₁, f₁, a₁, b₁, c₁⟩, ⟨e₂, f₂, a₂, b₂, c₂⟩, o⟩ := F
        simp [hypPairMap]
      right_inv := fun F => by
        obtain ⟨⟨e₁, f₁, a₁, b₁, c₁⟩, ⟨e₂, f₂, a₂, b₂, c₂⟩, o⟩ := F
        simp [hypPairMap] }

end FrameCount

section Nested

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

theorem polar_of_isometric {Q : QuadraticForm K V} {Q₂ : QuadraticForm K W} (ι : W →ₗ[K] V)
    (hι : ∀ w, Q (ι w) = Q₂ w) (x y : W) : polar Q (ι x) (ι y) = polar Q₂ x y := by
  simp only [polar, ← map_add ι, hι]

@[expose] noncomputable def nestedFrame (Q₂ : QuadraticForm K W) : OFrame (hypSum (hypSum Q₂)) where
  P := ⟨((1, 0), ((0, 0), 0)), ((0, 1), ((0, 0), 0)), by simp [hypSum_apply],
    by simp [hypSum_apply], by rw [polar_hypSum, polar_hypSum]; simp⟩
  P' := ⟨((0, 0), ((1, 0), 0)), ((0, 0), ((0, 1), 0)), by simp [hypSum_apply],
    by simp [hypSum_apply], by rw [polar_hypSum, polar_hypSum]; simp⟩
  orth := ⟨by rw [polar_hypSum, polar_hypSum]; simp, by rw [polar_hypSum, polar_hypSum]; simp,
    by rw [polar_hypSum, polar_hypSum]; simp, by rw [polar_hypSum, polar_hypSum]; simp⟩

@[expose] def nestedEmb (K W : Type) [Field K] [AddCommGroup W] [Module K W] :
    W →ₗ[K] (K × K) × ((K × K) × W) :=
  LinearMap.inr K (K × K) ((K × K) × W) ∘ₗ LinearMap.inr K (K × K) W

theorem nestedEmb_apply (w : W) : nestedEmb K W w = ((0, 0), ((0, 0), w)) := rfl

theorem nestedEmb_isometric (Q₂ : QuadraticForm K W) (w : W) :
    hypSum (hypSum Q₂) (nestedEmb K W w) = Q₂ w := by
  simp [nestedEmb_apply, hypSum_apply]

theorem nestedEmb_injective : Function.Injective (nestedEmb K W) := fun a b h => by
  simpa [nestedEmb_apply] using h

theorem nestedFrame_perp (Q₂ : QuadraticForm K W) :
    (nestedFrame Q₂).perp = LinearMap.range (nestedEmb K W) := by
  ext x
  rw [Frame.mem_perp_iff, Frame.coords_apply]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    have h10 := congrFun (congrFun h 1) 0
    have h11 := congrFun (congrFun h 1) 1
    simp [nestedFrame, polar_hypSum] at h00 h01 h10 h11
    refine ⟨x.2.2, ?_⟩
    rw [nestedEmb_apply]
    ext <;> simp [h00, h01, h10, h11]
  · rintro ⟨w, rfl⟩
    ext i j
    fin_cases i <;> fin_cases j <;> simp [nestedFrame, polar_hypSum, nestedEmb_apply]

end Nested

section PerpCount

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V} {Q₂ : QuadraticForm K W}

@[expose] def frameMapEmb (ι : W →ₗ[K] V) (hι : ∀ w, Q (ι w) = Q₂ w) (F : OFrame Q₂) :
    OFrame Q where
  P := ⟨ι F.e₁, ι F.f₁, by rw [hι, F.Q_e₁], by rw [hι, F.Q_f₁],
    by rw [polar_of_isometric ι hι, F.polar_e₁_f₁]⟩
  P' := ⟨ι F.e₂, ι F.f₂, by rw [hι, F.Q_e₂], by rw [hι, F.Q_f₂],
    by rw [polar_of_isometric ι hι, F.polar_e₂_f₂]⟩
  orth := ⟨by rw [polar_of_isometric ι hι]; exact F.polar_e₁_e₂,
    by rw [polar_of_isometric ι hι]; exact F.polar_e₁_f₂,
    by rw [polar_of_isometric ι hι]; exact F.polar_f₁_e₂,
    by rw [polar_of_isometric ι hι]; exact F.polar_f₁_f₂⟩

theorem frameMapEmb_incl (ι : W →ₗ[K] V) (hι : ∀ w, Q (ι w) = Q₂ w) (F : OFrame Q₂)
    (X : Matrix (Fin 2) (Fin 2) K) : (frameMapEmb ι hι F).incl X = ι (F.incl X) := by
  simp [Frame.incl_apply, frameMapEmb]

theorem card_frames_perp (F₀ : OFrame Q) (ι : W →ₗ[K] V) (hι : ∀ w, Q (ι w) = Q₂ w)
    (hinj : Function.Injective ι) (hrange : LinearMap.range ι = F₀.perp) :
    Nat.card {F : OFrame Q // F.span ≤ F₀.perp} = Nat.card (OFrame Q₂) := by
  classical
  have hle : ∀ F : OFrame Q₂, (frameMapEmb ι hι F).span ≤ F₀.perp := by
    rintro F _ ⟨X, rfl⟩
    rw [frameMapEmb_incl, ← hrange]
    exact ⟨_, rfl⟩
  symm
  refine Nat.card_eq_of_bijective (fun F => ⟨frameMapEmb ι hι F, hle F⟩) ⟨?_, ?_⟩
  · intro F F' h
    have h' := congrArg Subtype.val h
    refine ModelFacts.Frame.ext_vec ?_ ?_ ?_ ?_
    · exact hinj (congrArg (fun G : OFrame Q => G.e₁) h')
    · exact hinj (congrArg (fun G : OFrame Q => G.f₁) h')
    · exact hinj (congrArg (fun G : OFrame Q => G.e₂) h')
    · exact hinj (congrArg (fun G : OFrame Q => G.f₂) h')
  · rintro ⟨F, hF⟩
    have hmem : ∀ X : Matrix (Fin 2) (Fin 2) K, F.incl X ∈ LinearMap.range ι := fun X => by
      rw [hrange]
      exact hF ⟨X, rfl⟩
    obtain ⟨w₁, hw₁⟩ := hmem !![1, 0; 0, 0]
    obtain ⟨w₂, hw₂⟩ := hmem !![0, 0; 0, 1]
    obtain ⟨w₃, hw₃⟩ := hmem !![0, -1; 0, 0]
    obtain ⟨w₄, hw₄⟩ := hmem !![0, 0; 1, 0]
    rw [← ModelFacts.Frame.e₁_eq_incl] at hw₁
    rw [← ModelFacts.Frame.f₁_eq_incl] at hw₂
    rw [← ModelFacts.Frame.e₂_eq_incl] at hw₃
    rw [← ModelFacts.Frame.f₂_eq_incl] at hw₄
    have hQ : ∀ w, Q₂ w = Q (ι w) := fun w => (hι w).symm
    let F' : OFrame Q₂ :=
      ⟨⟨w₁, w₂, by rw [hQ, hw₁, F.Q_e₁], by rw [hQ, hw₂, F.Q_f₁],
          by rw [← polar_of_isometric ι hι, hw₁, hw₂, F.polar_e₁_f₁]⟩,
        ⟨w₃, w₄, by rw [hQ, hw₃, F.Q_e₂], by rw [hQ, hw₄, F.Q_f₂],
          by rw [← polar_of_isometric ι hι, hw₃, hw₄, F.polar_e₂_f₂]⟩,
        ⟨by rw [← polar_of_isometric ι hι, hw₁, hw₃]; exact F.polar_e₁_e₂,
          by rw [← polar_of_isometric ι hι, hw₁, hw₄]; exact F.polar_e₁_f₂,
          by rw [← polar_of_isometric ι hι, hw₂, hw₃]; exact F.polar_f₁_e₂,
          by rw [← polar_of_isometric ι hι, hw₂, hw₄]; exact F.polar_f₁_f₂⟩⟩
    refine ⟨F', Subtype.ext (ModelFacts.Frame.ext_vec ?_ ?_ ?_ ?_)⟩
    · exact hw₁
    · exact hw₂
    · exact hw₃
    · exact hw₄

theorem exists_frame_perp_emb (e : Q.IsometryEquiv (hypSum (hypSum Q₂))) :
    ∃ (F₀ : OFrame Q) (ι : W →ₗ[K] V), (∀ w, Q (ι w) = Q₂ w) ∧ Function.Injective ι ∧
      LinearMap.range ι = F₀.perp := by
  let ι₀ : (K × K) × ((K × K) × W) →ₗ[K] V := (e.symm : _ ≃ₗ[K] _).toLinearMap
  have hι₀ : ∀ w', Q (ι₀ w') = hypSum (hypSum Q₂) w' := fun w' => e.symm.map_app w'
  let F₀ := frameMapEmb ι₀ hι₀ (nestedFrame Q₂)
  have hF₀incl : ∀ Y, F₀.incl Y = ι₀ ((nestedFrame Q₂).incl Y) := frameMapEmb_incl ι₀ hι₀ _
  refine ⟨F₀, ι₀ ∘ₗ nestedEmb K W, fun w => ?_, fun a b h => ?_, ?_⟩
  · simp [hι₀, nestedEmb_isometric]
  · exact nestedEmb_injective (e.symm.injective h)
  · ext x
    rw [Frame.mem_perp_iff_forall_incl]
    constructor
    · rintro ⟨w, rfl⟩ Y
      rw [hF₀incl]
      have hw : nestedEmb K W w ∈ (nestedFrame Q₂).perp := by
        rw [nestedFrame_perp]
        exact ⟨w, rfl⟩
      simpa [polar_of_isometric ι₀ hι₀] using (Frame.mem_perp_iff_forall_incl _).mp hw Y
    · intro h
      have hz : e x ∈ (nestedFrame Q₂).perp := by
        rw [Frame.mem_perp_iff_forall_incl]
        intro Y
        have := h Y
        rw [hF₀incl] at this
        have h2 := polar_isometryEquiv e x (ι₀ ((nestedFrame Q₂).incl Y))
        simp only [ι₀, LinearEquiv.coe_coe, QuadraticMap.IsometryEquiv.coe_toLinearEquiv,
          QuadraticMap.IsometryEquiv.apply_symm_apply] at h2
        rw [h2]
        exact this
      rw [nestedFrame_perp] at hz
      obtain ⟨w, hw⟩ := hz
      refine ⟨w, ?_⟩
      simp only [LinearMap.comp_apply, ι₀]
      rw [hw]
      simp

end PerpCount

section Tower

variable {K V W₀ W₁ W₂ : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V]
  [AddCommGroup W₀] [Module K W₀] [Finite W₀] [AddCommGroup W₁] [Module K W₁] [Finite W₁]
  [AddCommGroup W₂] [Module K W₂] [Finite W₂]
  {Q₀ : QuadraticForm K W₀} {Q₁ : QuadraticForm K W₁} {Q₂ : QuadraticForm K W₂}

theorem card_hypPair_hypSum (hQ' : (polarBilin Q₀).Nondegenerate) :
    Nat.card (HypPair (hypSum Q₀)) =
      (Nat.card {v : (K × K) × W₀ // hypSum Q₀ v = 0} - 1) * Nat.card W₀ := by
  rw [← card_hypPairs_hypSum hQ']
  exact Nat.card_congr
    { toFun := fun P => ⟨(P.e, P.f), P.Q_e, P.Q_f, P.polar_ef⟩
      invFun := fun p => ⟨p.1.1, p.1.2, p.2.1, p.2.2.1, p.2.2.2⟩
      left_inv := fun P => rfl
      right_inv := fun p => rfl }

omit [Finite K] in
theorem card_hypPair_of_aniso {Q : QuadraticForm K V} (h : ∀ v, Q v = 0 → v = 0) :
    Nat.card (HypPair Q) = 0 := by
  rw [Nat.card_eq_zero]
  exact Or.inl ⟨fun P => P.e_ne_zero (h _ P.Q_e)⟩

omit [Finite W₂] in
theorem card_frame_two_step (hQ₀ : (polarBilin Q₀).Nondegenerate)
    (hQ₁ : (polarBilin Q₁).Nondegenerate) (e₂ : Q₂.IsometryEquiv (hypSum Q₁))
    (e₁ : Q₁.IsometryEquiv (hypSum Q₀)) :
    Nat.card (OFrame Q₂) =
      (Nat.card {v // Q₂ v = 0} - 1) * Nat.card W₁ *
        ((Nat.card {v // Q₁ v = 0} - 1) * Nat.card W₀) := by
  rw [card_frame_of_isometry e₂, card_frame_hypSum hQ₁, card_hypPair_hypSum hQ₁,
    ← card_singular_congr e₂, card_hypPair_of_isometry e₁, card_hypPair_hypSum hQ₀,
    ← card_singular_congr e₁]

omit [Finite W₂] in
theorem card_frame_one_step_aniso (hQ₁ : (polarBilin Q₁).Nondegenerate)
    (e₂ : Q₂.IsometryEquiv (hypSum Q₁)) (h : ∀ v, Q₁ v = 0 → v = 0) :
    Nat.card (OFrame Q₂) = 0 := by
  rw [card_frame_of_isometry e₂, card_frame_hypSum hQ₁, card_hypPair_of_aniso h, mul_zero]

@[expose] def hypSumCongr {Q : QuadraticForm K W₀} {Q' : QuadraticForm K W₁}
    (e : Q.IsometryEquiv Q') : (hypSum Q).IsometryEquiv (hypSum Q') :=
  { LinearEquiv.prodCongr (LinearEquiv.refl K (K × K)) e.toLinearEquiv with
    map_app' := fun p => by
      simp [hypSum_apply, QuadraticMap.IsometryEquiv.map_app] }

end Tower

end CFSG.ClassicalInvolution.RouteD.NonClassical
