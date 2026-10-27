module

public import CFSG.ClassicalInvolution.RouteD.TypeTwistedE6PerpOrthTransport
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinV

public section

namespace CFSG.ClassicalInvolution.RouteD.TwinY

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.RouteD.NonClassical (frameMapEmb frameMapEmb_incl
  frame_La_neg_one_eq_of_range_eq two_mul_card_frames_range)
open CFSG.ClassicalInvolution.ModelFacts (plusSp minusSp mem_plusSp mem_minusSp)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Count

variable {K V W : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
  {Q : QuadraticForm K V} {Q₂ : QuadraticForm K W}

theorem card_frames_span_le_range (X : Submodule K V) (ι : W →ₗ[K] V)
    (hι : ∀ w, Q (ι w) = Q₂ w) (hinj : Function.Injective ι) (hrange : LinearMap.range ι = X) :
    Nat.card {F : OFrame Q // F.span ≤ X} = Nat.card (OFrame Q₂) := by
  classical
  have hle : ∀ F : OFrame Q₂, (frameMapEmb ι hι F).span ≤ X := by
    rintro F _ ⟨Y, rfl⟩
    rw [frameMapEmb_incl, ← hrange]
    exact ⟨_, rfl⟩
  symm
  refine Nat.card_eq_of_bijective (fun F => ⟨frameMapEmb ι hι F, hle F⟩) ⟨?_, ?_⟩
  · intro F F' h
    have h' := congrArg Subtype.val h
    refine CFSG.ClassicalInvolution.ModelFacts.Frame.ext_vec ?_ ?_ ?_ ?_
    · exact hinj (congrArg (fun G : OFrame Q => G.e₁) h')
    · exact hinj (congrArg (fun G : OFrame Q => G.f₁) h')
    · exact hinj (congrArg (fun G : OFrame Q => G.e₂) h')
    · exact hinj (congrArg (fun G : OFrame Q => G.f₂) h')
  · rintro ⟨F, hF⟩
    have hmem : ∀ Y : Matrix (Fin 2) (Fin 2) K, F.incl Y ∈ LinearMap.range ι := fun Y => by
      rw [hrange]
      exact hF ⟨Y, rfl⟩
    obtain ⟨w₁, hw₁⟩ := hmem !![1, 0; 0, 0]
    obtain ⟨w₂, hw₂⟩ := hmem !![0, 0; 0, 1]
    obtain ⟨w₃, hw₃⟩ := hmem !![0, -1; 0, 0]
    obtain ⟨w₄, hw₄⟩ := hmem !![0, 0; 1, 0]
    rw [← CFSG.ClassicalInvolution.ModelFacts.Frame.e₁_eq_incl] at hw₁
    rw [← CFSG.ClassicalInvolution.ModelFacts.Frame.f₁_eq_incl] at hw₂
    rw [← CFSG.ClassicalInvolution.ModelFacts.Frame.e₂_eq_incl] at hw₃
    rw [← CFSG.ClassicalInvolution.ModelFacts.Frame.f₂_eq_incl] at hw₄
    have hQ : ∀ w, Q₂ w = Q (ι w) := fun w => (hι w).symm
    have hpol := CFSG.ClassicalInvolution.RouteD.NonClassical.polar_of_isometric (Q := Q)
      (Q₂ := Q₂) ι hι
    let F' : OFrame Q₂ :=
      ⟨⟨w₁, w₂, by rw [hQ, hw₁, F.Q_e₁], by rw [hQ, hw₂, F.Q_f₁],
          by rw [← hpol, hw₁, hw₂, F.polar_e₁_f₁]⟩,
        ⟨w₃, w₄, by rw [hQ, hw₃, F.Q_e₂], by rw [hQ, hw₄, F.Q_f₂],
          by rw [← hpol, hw₃, hw₄, F.polar_e₂_f₂]⟩,
        ⟨by rw [← hpol, hw₁, hw₃]; exact F.polar_e₁_e₂,
          by rw [← hpol, hw₁, hw₄]; exact F.polar_e₁_f₂,
          by rw [← hpol, hw₂, hw₃]; exact F.polar_f₁_e₂,
          by rw [← hpol, hw₂, hw₄]; exact F.polar_f₁_f₂⟩⟩
    refine ⟨F', Subtype.ext (CFSG.ClassicalInvolution.ModelFacts.Frame.ext_vec ?_ ?_ ?_ ?_)⟩
    · exact hw₁
    · exact hw₂
    · exact hw₃
    · exact hw₄

theorem card_frames_span_le_restrict (X : Submodule K V) :
    Nat.card {F : OFrame Q // F.span ≤ X} = Nat.card (OFrame (Q.restrict X)) :=
  card_frames_span_le_range X X.subtype (fun _ => rfl) X.injective_subtype
    (Submodule.range_subtype X)

end Count

section Fibres

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [Finite V]
  {Q : QuadraticForm K V}

theorem two_mul_card_frames_span_le (hodd : Odd (Nat.card K)) (X : Submodule K V) :
    2 * Nat.card {F : OFrame Q // F.span ≤ X} =
      ({S : Subgroup (V ≃ₗ[K] V) | ∃ F : OFrame Q, F.La.range = S ∧ F.span ≤ X}).ncard *
        Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
  classical
  have h2 : (2 : K) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  set N' : Set (Subgroup (V ≃ₗ[K] V)) :=
    {S | ∃ F : OFrame Q, F.La.range = S ∧ F.span ≤ X} with hN'
  have hle : ∀ F : OFrame Q, F.La.range ∈ N' → F.span ≤ X := by
    rintro F ⟨F', hF', hle⟩
    have hneg := frame_La_neg_one_eq_of_range_eq hodd hF'
    exact (Frame.span_eq_of_La_neg_one_eq h2 hneg.symm).symm ▸ hle
  let f : {F : OFrame Q // F.span ≤ X} → N' := fun F => ⟨F.1.La.range, F.1, rfl, F.2⟩
  let _ : Fintype N' := Fintype.ofFinite N'
  have hfib : ∀ S : N', 2 * Nat.card {F : {F : OFrame Q // F.span ≤ X} // f F = S} =
      Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := K))) := by
    intro S
    obtain ⟨F₁, hF₁, hF₁le⟩ := S.2
    have e : {F : {F : OFrame Q // F.span ≤ X} // f F = S} ≃
        {F : OFrame Q // F.La.range = F₁.La.range} :=
      { toFun := fun F => ⟨F.1.1, (congrArg Subtype.val F.2).trans hF₁.symm⟩
        invFun := fun F => ⟨⟨F.1, hle F.1 ⟨F₁, F.2.symm, hF₁le⟩⟩, Subtype.ext (F.2.trans hF₁)⟩
        left_inv := fun F => rfl
        right_inv := fun F => rfl }
    rw [Nat.card_congr e]
    exact two_mul_card_frames_range hodd F₁
  have hsum : Nat.card {F : OFrame Q // F.span ≤ X} =
      ∑ S : N', Nat.card {F : {F : OFrame Q // F.span ≤ X} // f F = S} := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f)]
  rw [hsum, Finset.mul_sum, Finset.sum_congr rfl fun S _ => hfib S, Finset.sum_const,
    Finset.card_univ, smul_eq_mul, ← Nat.card_eq_fintype_card, Nat.card_coe_set_eq]

end Fibres

section Commute

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem mem_perp_of_fix_span (fr : OFrame Q) {u : V ≃ₗ[K] V}
    (hu : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ x ∈ fr.span, u x = x) {r : V}
    (hr : r ∈ fr.perp) : u r ∈ fr.perp := by
  rw [Frame.mem_perp_iff_forall_incl] at hr ⊢
  intro Y
  have h1 := polar_map_of_mem hu r (fr.incl Y)
  rw [hfix _ ⟨Y, rfl⟩] at h1
  rw [h1]
  exact hr Y

theorem commute_La_of_span_le_fixed (fr : OFrame Q) {u : V ≃ₗ[K] V}
    (hu : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hfix : ∀ x ∈ fr.span, u x = x)
    (A : SL(2, K)) : u * fr.La A = fr.La A * u := by
  refine LinearEquiv.ext fun v => ?_
  have hdec : v = fr.incl (fr.coords v) + (v - fr.incl (fr.coords v)) := by abel
  have hperp : v - fr.incl (fr.coords v) ∈ fr.perp := by
    rw [Frame.mem_perp_iff, map_sub, Frame.coords_incl, sub_self]
  set c := fr.coords v with hc
  set r := v - fr.incl c with hr
  have hur : u r ∈ fr.perp := mem_perp_of_fix_span fr hu hfix hperp
  have e1 : u v = fr.incl c + u r := by
    conv_lhs => rw [hdec]
    rw [map_add, hfix _ ⟨c, rfl⟩]
  have e2 : fr.coords (u v) = c := by
    rw [e1, map_add, Frame.coords_incl, (Frame.mem_perp_iff fr).mp hur, add_zero]
  simp only [LinearEquiv.mul_apply]
  rw [Frame.La_apply, Frame.La_apply, e2, map_add, hfix _ ⟨_, rfl⟩]

theorem La_range_le_centralizer_iff [FiniteDimensional K V] (h2 : (2 : K) ≠ 0) (fr : OFrame Q)
    {u : V ≃ₗ[K] V} (hu : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hu2 : u * u = 1)
    (hminus : Module.finrank K (minusSp u) < 4) :
    fr.La.range ≤ Subgroup.centralizer ({u} : Set (V ≃ₗ[K] V)) ↔ fr.span ≤ plusSp u := by
  constructor
  · intro h
    have hcomm : ∀ A : SL(2, K), u * fr.La A = fr.La A * u := fun A =>
      (Subgroup.mem_centralizer_singleton_iff.mp (h ⟨A, rfl⟩)).symm
    have hneg : ¬ fr.span ≤ minusSp u := by
      intro hle
      have := Submodule.finrank_mono hle
      rw [Frame.finrank_span] at this
      omega
    exact span_le_plusSp_of_commute h2 fr hu hu2 hcomm hneg
  · intro h
    rintro _ ⟨A, rfl⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    exact (commute_La_of_span_le_fixed fr hu (fun x hx => mem_plusSp.mp (h hx)) A).symm

end Commute

end CFSG.ClassicalInvolution.RouteD.TwinY
