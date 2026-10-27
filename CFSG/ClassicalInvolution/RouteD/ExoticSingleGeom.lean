module

public import CFSG.ClassicalInvolution.RouteD.ExoticSingleLayers
public import CFSG.ClassicalInvolution.RouteD.ExoticTwinProofOrthBridge
public import Certificates.Certificate45
public import Certificates.Certificate46
public import Certificates.Certificate47
public import Certificates.Certificate48
public import Certificates.Certificate49
public import Certificates.Certificate50
public import Certificates.Certificate51
public import Certificates.Certificate52
public import Certificates.Certificate53
public import Certificates.Certificate54
public import Certificates.Certificate55
public import Certificates.Certificate56
public import Certificates.Certificate57
public import Certificates.Certificate58
public import Certificates.Certificate59
public import Certificates.Certificate60
public import Certificates.Certificate61
public import Certificates.Certificate62
public import Certificates.Certificate63
public import Certificates.Certificate64
public import Certificates.Certificate65
public import Certificates.Certificate66
public import Certificates.Certificate67
public import Certificates.Certificate68
public import Certificates.Certificate69
public import Certificates.Certificate70
public import Certificates.Certificate71
public import Certificates.Certificate72
public import Certificates.Certificate73
public import Certificates.Certificate74
public import Certificates.Certificate75
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate120
public import Certificates.Certificate123
public import CFSG.ClassicalInvolution.Generic.InductionMain
public import CFSG.ClassicalInvolution.RouteD.ExoticShapes
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBAdapt
public import CFSG.ClassicalInvolution.RouteD.LocalTwinBWeakNodes
public import CFSG.ClassicalInvolution.RouteD.TypeDAdapt
public import CFSG.ClassicalInvolution.RouteD.TypeEAdapt

public section

namespace CFSG.ClassicalInvolution.RouteD.Exotic

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.LieType.Universal.Spin
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet orth_or_twin not_commutes_of_nonorth)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Transport

variable {X Y : Type} [Group X] [Group Y]

theorem map_eq_map_iff_of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {R S : Subgroup X} (hR : ⁅R, R⁆ = R) (hS : ⁅S, S⁆ = S) : R.map π = S.map π ↔ R = S :=
  ⟨fun h => ModelFacts.eq_of_map_eq_of_isPerfect π hker hR hS h, fun h => by rw [h]⟩

theorem IsFundTwin.of_map (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖) {R R' : Subgroup X} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (htw : IsFundTwin 𝓖 (R.map π) (R'.map π)) : IsFundTwin 𝓕 R R' := by
  refine ⟨fun e => htw.1 (by rw [e]), (Gaps.commutes_map_iff hker (hperf R hR)).mp htw.2.1,
    fun S hS => ?_⟩
  have key := htw.2.2 (S.map π) (hmap S hS)
  rw [map_eq_map_iff_of_central π hker (hperf S hS) (hperf R hR),
    map_eq_map_iff_of_central π hker (hperf S hS) (hperf R' hR'),
    Gaps.commutes_map_iff hker (hperf S hS), Gaps.commutes_map_iff hker (hperf S hS)] at key
  exact key

theorem FundTwinsExist.of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖) (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L)
    (h : ∀ L ∈ 𝓖, ∃ L' ∈ 𝓖, IsFundTwin 𝓖 L L') : FundTwinsExist 𝓕 := by
  intro R hR
  obtain ⟨L', hL', htw⟩ := h _ (hmap R hR)
  obtain ⟨R', hR', rfl⟩ := hsurj L' hL'
  exact ⟨R', hR', IsFundTwin.of_map π hker hperf hmap hR hR' htw⟩

theorem FundHubUnique.of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖) (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L)
    (h : FundHubUnique 𝓖) : FundHubUnique 𝓕 := by
  intro R hR S₁ hS₁ S₂ hS₂ h₁ h₂
  have hub : ∀ S ∈ 𝓕, IsHub 𝓕 R S → IsHub 𝓖 (R.map π) (S.map π) := by
    rintro S hS ⟨hne, hc, hall⟩
    refine ⟨fun e => hne ((map_eq_map_iff_of_central π hker (hperf S hS) (hperf R hR)).mp e),
      (Gaps.commutes_map_iff hker (hperf S hS)).mpr hc, fun S'' hS'' hc'' hne'' => ?_⟩
    obtain ⟨S', hS', rfl⟩ := hsurj S'' hS''
    have hcS' : Commutes S' R := (Gaps.commutes_map_iff hker (hperf S' hS')).mp hc''
    have hneS : S' ≠ S := fun e => hne'' (by rw [e])
    exact (Gaps.commutes_map_iff hker (hperf S' hS')).mpr (hall S' hS' hcS' hneS)
  exact (map_eq_map_iff_of_central π hker (hperf S₁ hS₁) (hperf S₂ hS₂)).mp
    (h _ (hmap R hR) _ (hmap S₁ hS₁) _ (hmap S₂ hS₂) (hub S₁ hS₁ h₁) (hub S₂ hS₂ h₂))

theorem TwinWithinCentralizer.of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖) (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L)
    (h : TwinWithinCentralizer 𝓖) : TwinWithinCentralizer 𝓕 := by
  intro R hR A hA B hB hAB hcAB hAR hBR hnb
  have hinj : ∀ {S T : Subgroup X}, S ∈ 𝓕 → T ∈ 𝓕 → (S.map π = T.map π ↔ S = T) :=
    fun hS hT => map_eq_map_iff_of_central π hker (hperf _ hS) (hperf _ hT)
  refine IsFundTwin.of_map π hker hperf hmap hA hB
    (h (R.map π) (hmap R hR) (A.map π) (hmap A hA) (B.map π) (hmap B hB)
      (fun e => hAB ((hinj hA hB).mp e)) ((Gaps.commutes_map_iff hker (hperf A hA)).mpr hcAB)
      ((Gaps.commutes_map_iff hker (hperf A hA)).mpr hAR)
      ((Gaps.commutes_map_iff hker (hperf B hB)).mpr hBR) fun T' hT' hT'R => ?_)
  obtain ⟨T, hT, rfl⟩ := hsurj T' hT'
  have hc := (Gaps.commutes_map_iff hker (hperf T hT)).mp hT'R
  rw [hinj hT hA, hinj hT hB, Gaps.commutes_map_iff hker (hperf T hT),
    Gaps.commutes_map_iff hker (hperf T hT)]
  exact hnb T hT hc

theorem IsFundTwin.to_map (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L) {R R' : Subgroup X} (hR : R ∈ 𝓕) (hR' : R' ∈ 𝓕)
    (htw : IsFundTwin 𝓕 R R') : IsFundTwin 𝓖 (R.map π) (R'.map π) := by
  refine ⟨fun e => htw.1 ((map_eq_map_iff_of_central π hker (hperf R hR) (hperf R' hR')).mp e),
    (Gaps.commutes_map_iff hker (hperf R hR)).mpr htw.2.1, fun S' hS' => ?_⟩
  obtain ⟨S, hS, rfl⟩ := hsurj S' hS'
  have key := htw.2.2 S hS
  rw [map_eq_map_iff_of_central π hker (hperf S hS) (hperf R hR),
    map_eq_map_iff_of_central π hker (hperf S hS) (hperf R' hR'),
    Gaps.commutes_map_iff hker (hperf S hS), Gaps.commutes_map_iff hker (hperf S hS)]
  exact key

theorem FundHasOrthogonal.of_central (π : X →* Y) (hker : π.ker ≤ Subgroup.center X)
    {𝓕 : Set (Subgroup X)} {𝓖 : Set (Subgroup Y)} (hperf : ∀ R ∈ 𝓕, ⁅R, R⁆ = R)
    (hmap : ∀ R ∈ 𝓕, R.map π ∈ 𝓖) (hsurj : ∀ L ∈ 𝓖, ∃ R ∈ 𝓕, R.map π = L)
    (h : FundHasOrthogonal 𝓖) : FundHasOrthogonal 𝓕 := by
  intro R hR
  obtain ⟨S', hS', hne, hc, hnt⟩ := h _ (hmap R hR)
  obtain ⟨S, hS, rfl⟩ := hsurj S' hS'
  exact ⟨S, hS, fun e => hne (by rw [e]), (Gaps.commutes_map_iff hker (hperf S hS)).mp hc,
    fun htw => hnt (IsFundTwin.to_map π hker hperf hsurj hR hS htw)⟩

theorem mul_eq_of_map_eq (π : X →* Y) (hker : π.ker ≤ Subgroup.center X) {ε : X}
    (hεker : ε ∈ π.ker) (hker' : ∀ k ∈ π.ker, k = 1 ∨ k = ε) {r r' : X} (hr' : r' * r' = 1)
    (hπ : π r = π r') (hne : r ≠ r') : r * r' = ε := by
  have hmem : r'⁻¹ * r ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hπ, inv_mul_cancel]
  rcases hker' _ hmem with h1 | h1
  · exact absurd (inv_mul_eq_one.mp h1).symm hne
  · have hrr : r = r' * ε := by rw [← h1]; group
    have hc : r' * ε = ε * r' := Subgroup.mem_center_iff.mp (hker hεker) r'
    rw [hrr, hc, mul_assoc, hr', mul_one]

end Transport

section Geometry

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

omit [Finite K] in
theorem exists_aniso_perp₃ (hQ : (polarBilin Q).Nondegenerate) (hdim : 13 ≤ Module.finrank K V)
    (F₀ F₁ F₂ : OFrame Q) (h01 : F₁.span ≤ F₀.perp) (h02 : F₂.span ≤ F₀.perp)
    (h12 : F₂.span ≤ F₁.perp) : ∃ r ∈ (F₀.perp ⊓ F₁.perp) ⊓ F₂.perp, Q r ≠ 0 := by
  have hF1 : ∀ x ∈ F₁.perp, x ∈ F₁.P.perp ∧ x ∈ F₁.P'.perp := fun x hx => by
    have h := (mem_perp_iff_four F₁).mp hx
    exact ⟨HypPair.mem_perp.mpr ⟨by rw [polar_comm]; exact h.1, by rw [polar_comm]; exact h.2.1⟩,
      HypPair.mem_perp.mpr ⟨by rw [polar_comm]; exact h.2.2.1, by rw [polar_comm]; exact h.2.2.2⟩⟩
  have hnd₁ := (CFSG.ClassicalInvolution.ModelFacts.polarNondegOn_perp hQ F₀).inf_perp F₁.P
    (h01 F₁.e₁_mem_span) (h01 F₁.f₁_mem_span)
  have hnd₂ := hnd₁.inf_perp F₁.P'
    ⟨h01 F₁.e₂_mem_span, HypPair.mem_perp.mpr ⟨F₁.polar_e₁_e₂, F₁.polar_f₁_e₂⟩⟩
    ⟨h01 F₁.f₂_mem_span, HypPair.mem_perp.mpr ⟨F₁.polar_e₁_f₂, F₁.polar_f₁_f₂⟩⟩
  have hmem2 : ∀ y ∈ F₂.span, y ∈ (F₀.perp ⊓ F₁.P.perp) ⊓ F₁.P'.perp := fun y hy =>
    ⟨⟨h02 hy, (hF1 y (h12 hy)).1⟩, (hF1 y (h12 hy)).2⟩
  have hnd₃ := hnd₂.inf_perp F₂.P (hmem2 _ F₂.e₁_mem_span) (hmem2 _ F₂.f₁_mem_span)
  have hnd₄ := hnd₃.inf_perp F₂.P'
    ⟨hmem2 _ F₂.e₂_mem_span, HypPair.mem_perp.mpr ⟨F₂.polar_e₁_e₂, F₂.polar_f₁_e₂⟩⟩
    ⟨hmem2 _ F₂.f₂_mem_span, HypPair.mem_perp.mpr ⟨F₂.polar_e₁_f₂, F₂.polar_f₁_f₂⟩⟩
  let ℓ : V →ₗ[K] (Matrix (Fin 2) (Fin 2) K × (Fin 4 → K) × (Fin 4 → K)) :=
    F₀.coords.prod ((LinearMap.pi ![polarBilin Q F₁.e₁, polarBilin Q F₁.f₁, polarBilin Q F₁.e₂,
      polarBilin Q F₁.f₂]).prod (LinearMap.pi ![polarBilin Q F₂.e₁, polarBilin Q F₂.f₁,
      polarBilin Q F₂.e₂, polarBilin Q F₂.f₂]))
  have hker : LinearMap.ker ℓ ≠ ⊥ := by
    refine LinearMap.ker_ne_bot_of_finrank_lt ?_
    rw [Module.finrank_prod, Module.finrank_prod, Module.finrank_matrix, Module.finrank_fin_fun]
    simp
    omega
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hw' := LinearMap.mem_ker.mp hw
  have hw₀ : F₀.coords w = 0 := congrArg Prod.fst hw'
  have hw₁ : ∀ j : Fin 4, (ℓ w).2.1 j = 0 := fun j => by simp [hw']
  have hw₂ : ∀ j : Fin 4, (ℓ w).2.2 j = 0 := fun j => by simp [hw']
  have c1 : polar Q F₁.e₁ w = 0 := hw₁ 0
  have c2 : polar Q F₁.f₁ w = 0 := hw₁ 1
  have c3 : polar Q F₁.e₂ w = 0 := hw₁ 2
  have c4 : polar Q F₁.f₂ w = 0 := hw₁ 3
  have d1 : polar Q F₂.e₁ w = 0 := hw₂ 0
  have d2 : polar Q F₂.f₁ w = 0 := hw₂ 1
  have d3 : polar Q F₂.e₂ w = 0 := hw₂ 2
  have d4 : polar Q F₂.f₂ w = 0 := hw₂ 3
  have hwW : w ∈ ((((F₀.perp ⊓ F₁.P.perp) ⊓ F₁.P'.perp) ⊓ F₂.P.perp) ⊓ F₂.P'.perp) :=
    ⟨⟨⟨⟨(Frame.mem_perp_iff F₀).mpr hw₀, HypPair.mem_perp.mpr ⟨c1, c2⟩⟩,
      HypPair.mem_perp.mpr ⟨c3, c4⟩⟩, HypPair.mem_perp.mpr ⟨d1, d2⟩⟩,
      HypPair.mem_perp.mpr ⟨d3, d4⟩⟩
  obtain ⟨y, hy, hwy⟩ := hnd₄.exists_polar_ne_zero hwW hw0
  have hQ' : ∃ r ∈ ((((F₀.perp ⊓ F₁.P.perp) ⊓ F₁.P'.perp) ⊓ F₂.P.perp) ⊓ F₂.P'.perp), Q r ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hwy
    have e1 := hcon w hwW
    have e2 := hcon y hy
    have e3 := hcon (w + y) (Submodule.add_mem _ hwW hy)
    have : polar Q w y = Q (w + y) - Q w - Q y := rfl
    rw [this, e1, e2, e3]
    ring
  obtain ⟨r, hr, hQr⟩ := hQ'
  refine ⟨r, ⟨⟨hr.1.1.1.1, ?_⟩, ?_⟩, hQr⟩
  · show r ∈ F₁.perp
    rw [mem_perp_iff_four]
    have a1 := HypPair.mem_perp.mp hr.1.1.1.2
    have a2 := HypPair.mem_perp.mp hr.1.1.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_comm]; exact a1.1
    · rw [polar_comm]; exact a1.2
    · rw [polar_comm]; exact a2.1
    · rw [polar_comm]; exact a2.2
  · show r ∈ F₂.perp
    rw [mem_perp_iff_four]
    have a1 := HypPair.mem_perp.mp hr.1.2
    have a2 := HypPair.mem_perp.mp hr.2
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [polar_comm]; exact a1.1
    · rw [polar_comm]; exact a1.2
    · rw [polar_comm]; exact a2.1
    · rw [polar_comm]; exact a2.2

omit [FiniteDimensional K V] in
theorem isFundTwin_aux (hodd : Odd (Nat.card K)) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) (h' : IsFundamental Q L' i) (hne : L ≠ L')
    (hcomm : Commutes L L') : IsFundTwin (fundSet Q) L L' := by
  classical
  refine ⟨hne, hcomm, fun S hS => ?_⟩
  obtain ⟨j, hj⟩ := hS
  by_cases hSL : S = L
  · subst hSL
    exact ⟨fun _ => Or.inr hcomm, fun _ => Or.inl rfl⟩
  by_cases hSL' : S = L'
  · subst hSL'
    exact ⟨fun _ => Or.inl rfl, fun _ => Or.inr fun x hx y hy => (hcomm y hy x hx).symm⟩
  simp only [hSL, hSL', false_or]
  by_cases hji : j * i = i * j
  · exact (IsFundamental.commute_iff hodd hj h hji hSL).trans
      (IsFundamental.commute_iff hodd hj h' hji hSL').symm
  · have h1 : ¬ Commutes S L := fun hc => hji (hc j hj.mem i h.mem)
    have h2 : ¬ Commutes S L' := fun hc => hji (hc j hj.mem i h'.mem)
    exact ⟨fun hc => absurd hc h1, fun hc => absurd hc h2⟩

omit [FiniteDimensional K V] in
theorem isFundTwin_of_involution_eq (hodd : Odd (Nat.card K)) {L L' : Subgroup (V ≃ₗ[K] V)}
    {i : V ≃ₗ[K] V} (h : IsFundamental Q L i) (h' : IsFundamental Q L' i) (hne : L ≠ L') :
    IsFundTwin (fundSet Q) L L' := by
  obtain ⟨L₀, -, -, hcomm₀, huniq⟩ := IsFundamental.exists_twin hodd h
  have e : L' = L₀ := (huniq L' h').resolve_left fun e => hne e.symm
  subst e
  exact isFundTwin_aux hodd h h' hne hcomm₀

omit [FiniteDimensional K V] in
theorem exists_isFundTwin_fundSet (hodd : Odd (Nat.card K)) {L : Subgroup (V ≃ₗ[K] V)}
    (hL : L ∈ fundSet Q) : ∃ L' ∈ fundSet Q, IsFundTwin (fundSet Q) L L' := by
  obtain ⟨i, hi⟩ := hL
  obtain ⟨L', hL'i, hne, hcomm, -⟩ := IsFundamental.exists_twin hodd hi
  exact ⟨L', ⟨i, hL'i⟩, isFundTwin_aux hodd hi hL'i hne.symm hcomm⟩

omit [Finite K] [FiniteDimensional K V] in
theorem not_commutes_self_fundSet {L : Subgroup (V ≃ₗ[K] V)} (hL : L ∈ fundSet Q) :
    ¬ Commutes L L := by
  obtain ⟨i, F, rfl, -⟩ := hL
  intro h
  let A : SL(2, K) := Matrix.SpecialLinearGroup.transvection (show (0 : Fin 2) ≠ 1 by decide) 1
  let B : SL(2, K) := Matrix.SpecialLinearGroup.transvection (show (1 : Fin 2) ≠ 0 by decide) 1
  have h1 := h (F.La A) ⟨A, rfl⟩ (F.La B) ⟨B, rfl⟩
  rw [← map_mul, ← map_mul] at h1
  have h2 := F.La_injective h1
  have h3 := congrArg (fun g : SL(2, K) => (g : Matrix (Fin 2) (Fin 2) K) 0 0) h2
  simp [A, B, Frame.coe_transvection_zero_one, Frame.coe_transvection_one_zero, Matrix.mul_apply,
    Fin.sum_univ_two] at h3

omit [Finite K] in
theorem three_orth_dim {F₀ F₁ F₂ : OFrame Q} (h01 : F₁.span ≤ F₀.perp) (h02 : F₂.span ≤ F₀.perp)
    (h12 : F₂.span ≤ F₁.perp) : 12 ≤ Module.finrank K V := by
  have hdisj : Disjoint F₁.span F₂.span := by
    rw [Submodule.disjoint_def]
    intro x hx1 hx2
    exact Submodule.disjoint_def.mp F₁.isCompl_span_perp.disjoint x hx1 (h12 hx2)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq F₁.span F₂.span
  rw [disjoint_iff.mp hdisj, finrank_bot, F₁.finrank_span, F₂.finrank_span] at hsum
  have hle : Module.finrank K ↥(F₁.span ⊔ F₂.span) ≤ Module.finrank K F₀.perp :=
    Submodule.finrank_mono (sup_le h01 h02)
  have h4 := CFSG.ClassicalInvolution.ModelFacts.finrank_perp_add_four F₀
  omega

theorem hub_involution (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) {R₀ R₁ : Subgroup (V ≃ₗ[K] V)} {i₀ i₁ : V ≃ₗ[K] V}
    (h₀ : IsFundamental Q R₀ i₀) (h₁ : IsFundamental Q R₁ i₁) (hh : IsHub (fundSet Q) R₀ R₁) :
    i₁ = i₀ := by
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  rcases orth_or_twin hodd h₀ h₁ hh.2.1.symm with horth | heq
  swap
  · exact heq
  exfalso
  obtain ⟨F₀, rfl, rfl⟩ := h₀
  obtain ⟨F₁, rfl, rfl⟩ := h₁
  have hsp : F₁.span ≤ F₀.perp := span_le_perp_of_negSpace hodd horth
  obtain ⟨r, hr, hQr⟩ := exists_aniso_perp hQ hdim F₀ F₁ hsp
  have hGsp := sepFrame_span_le F₀ F₁ hsp hr.1 hr.2
  obtain ⟨hne1, hne0⟩ := sepFrame_ne_fixed h2 F₀ F₁ hsp hr.2 hQr
  set G := sepFrame F₁ r hr.2 with hG
  have hS : G.La.range ∈ fundSet Q := ⟨_, IsFundamental.of_frame G⟩
  have hS1 : G.La.range ≠ F₁.La.range := fun e =>
    hne1 (IsFundamental.involution_unique hodd (IsFundamental.of_frame G)
      (by rw [e]; exact IsFundamental.of_frame F₁))
  have horth0 := (span_le_perp_iff F₀ G).mp hGsp
  have hc0 : Commutes G.La.range F₀.La.range := by
    rintro _ ⟨A, rfl⟩ _ ⟨B, rfl⟩
    exact Frame.La_comm_of_orth (fun X Y => by rw [polar_comm]; exact horth0 Y X) A B
  have hc1 := hh.2.2 _ hS hc0 hS1
  refine not_commutes_of_nonorth hodd (IsFundamental.of_frame F₁) (IsFundamental.of_frame G) hne1
    (x := F₁.e₁) (y := G.f₁) ?_ ?_ ?_ hc1.symm
  · rw [negSpace_La_neg_one h2]; exact F₁.e₁_mem_span
  · rw [negSpace_La_neg_one h2]; exact G.f₁_mem_span
  · rw [hG, polar_sepFrame F₁ hr.2]
    exact neg_ne_zero.mpr hQr

theorem fundSet_hubUnique (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V ∨ Module.finrank K V < 8) : FundHubUnique (fundSet Q) := by
  intro R hR S₁ hS₁ S₂ hS₂ h₁ h₂
  obtain ⟨i, hi⟩ := hR
  obtain ⟨j₁, hj₁⟩ := hS₁
  obtain ⟨j₂, hj₂⟩ := hS₂
  have hinv : ∀ (S : Subgroup (V ≃ₗ[K] V)) (j : V ≃ₗ[K] V), IsFundamental Q S j →
      IsHub (fundSet Q) R S → j = i := by
    intro S j hj hh
    rcases hdim with hd | hd
    · exact hub_involution hodd hQ hd hi hj hh
    · exact commuting_same_involution hodd hd hi hj hh.2.1.symm
  obtain ⟨L', -, -, -, huniq⟩ := IsFundamental.exists_twin hodd hi
  have e₁ : S₁ = L' := (huniq S₁ (hinv S₁ j₁ hj₁ h₁ ▸ hj₁)).resolve_left h₁.1
  have e₂ : S₂ = L' := (huniq S₂ (hinv S₂ j₂ hj₂ h₂ ▸ hj₂)).resolve_left h₂.1
  rw [e₁, e₂]

omit [FiniteDimensional K V] in
theorem fundSet_twinWithinCentralizer_of (hodd : Odd (Nat.card K))
    (hhub : FundHubUnique (fundSet Q))
    (h3 : ∀ F₀ F₁ F₂ : OFrame Q, F₁.span ≤ F₀.perp → F₂.span ≤ F₀.perp → F₂.span ≤ F₁.perp →
      ∃ r ∈ (F₀.perp ⊓ F₁.perp) ⊓ F₂.perp, Q r ≠ 0) : TwinWithinCentralizer (fundSet Q) := by
  classical
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  intro R hR A hA B hB hAB hcAB hAR hBR hnb
  have hR' := hR
  obtain ⟨iR, hRi⟩ := hR
  obtain ⟨iA, hAi⟩ := hA
  obtain ⟨iB, hBi⟩ := hB
  have hubOf : ∀ X Y : Subgroup (V ≃ₗ[K] V), X ∈ fundSet Q → Y ∈ fundSet Q → Commutes Y R →
      X ≠ Y → IsHub (fundSet Q) R X →
      (∀ T ∈ fundSet Q, Commutes T R → ((T = X ∨ Commutes T X) ↔ (T = Y ∨ Commutes T Y))) →
      False := by
    intro X Y hX hY hYR hXY hubX hXY'
    have hYne : Y ≠ R := by
      rintro rfl
      exact not_commutes_self_fundSet hY hYR
    refine hXY (hhub R hR' X hX Y hY hubX ⟨hYne, hYR, fun T hT hTR hTY => ?_⟩)
    have hTX : T = X ∨ Commutes T X := by
      by_cases hTX : T = X
      · exact Or.inl hTX
      · exact Or.inr (hubX.2.2 T hT hTR hTX)
    exact ((hXY' T hT hTR).mp hTX).resolve_left hTY
  by_cases hAinv : iA = iR
  · exfalso
    have hAne : A ≠ R := by
      rintro rfl
      exact not_commutes_self_fundSet ⟨iR, hRi⟩ hAR
    have htw := isFundTwin_of_involution_eq hodd hRi (hAinv ▸ hAi) hAne.symm
    exact hubOf A B ⟨iA, hAi⟩ ⟨iB, hBi⟩ hBR hAB htw.isHub hnb
  by_cases hBinv : iB = iR
  · exfalso
    have hBne : B ≠ R := by
      rintro rfl
      exact not_commutes_self_fundSet ⟨iR, hRi⟩ hBR
    have htw := isFundTwin_of_involution_eq hodd hRi (hBinv ▸ hBi) hBne.symm
    exact hubOf B A ⟨iB, hBi⟩ ⟨iA, hAi⟩ hAR (Ne.symm hAB) htw.isHub
      fun T hT hTR => (hnb T hT hTR).symm
  by_cases hABinv : iA = iB
  · exact isFundTwin_of_involution_eq hodd hAi (hABinv ▸ hBi) hAB
  exfalso
  have oRA := (orth_or_twin hodd hRi hAi hAR.symm).resolve_right hAinv
  have oRB := (orth_or_twin hodd hRi hBi hBR.symm).resolve_right hBinv
  have oAB := (orth_or_twin hodd hAi hBi hcAB).resolve_right (Ne.symm hABinv)
  obtain ⟨FR, rfl, rfl⟩ := hRi
  obtain ⟨FA, rfl, rfl⟩ := hAi
  obtain ⟨FB, rfl, rfl⟩ := hBi
  have sRA : FA.span ≤ FR.perp := span_le_perp_of_negSpace hodd oRA
  have sRB : FB.span ≤ FR.perp := span_le_perp_of_negSpace hodd oRB
  have sAB : FB.span ≤ FA.perp := span_le_perp_of_negSpace hodd oAB
  obtain ⟨r, hr, hQr⟩ := h3 FR FA FB sRA sRB sAB
  have hGR := sepFrame_span_le FR FB sRB hr.1.1 hr.2
  have hGA := sepFrame_span_le FA FB sAB hr.1.2 hr.2
  obtain ⟨hne1, -⟩ := sepFrame_ne_fixed h2 FR FB sRB hr.2 hQr
  set G := sepFrame FB r hr.2 with hG
  have hS : G.La.range ∈ fundSet Q := ⟨_, IsFundamental.of_frame G⟩
  have hSB : G.La.range ≠ FB.La.range := fun e =>
    hne1 (IsFundamental.involution_unique hodd (IsFundamental.of_frame G)
      (by rw [e]; exact IsFundamental.of_frame FB))
  have comm_of_span : ∀ F : OFrame Q, G.span ≤ F.perp → Commutes G.La.range F.La.range := by
    intro F hF
    have horth := (span_le_perp_iff F G).mp hF
    rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
    exact Frame.La_comm_of_orth (fun X' Y' => by rw [polar_comm]; exact horth Y' X') X Y
  have hcR := comm_of_span FR hGR
  have hcA := comm_of_span FA hGA
  have hcB := ((hnb _ hS hcR).mp (Or.inr hcA)).resolve_left hSB
  refine not_commutes_of_nonorth hodd (IsFundamental.of_frame FB) (IsFundamental.of_frame G) hne1
    (x := FB.e₁) (y := G.f₁) ?_ ?_ ?_ hcB.symm
  · rw [negSpace_La_neg_one h2]; exact FB.e₁_mem_span
  · rw [negSpace_La_neg_one h2]; exact G.f₁_mem_span
  · rw [hG, polar_sepFrame FB hr.2]
    exact neg_ne_zero.mpr hQr

theorem fundSet_twinWithinCentralizer (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate)
    (hdim : Module.finrank K V < 8 ∨ (9 ≤ Module.finrank K V ∧ Module.finrank K V < 12) ∨
      13 ≤ Module.finrank K V) : TwinWithinCentralizer (fundSet Q) :=
  fundSet_twinWithinCentralizer_of hodd (fundSet_hubUnique hodd hQ (by omega))
    fun F₀ F₁ F₂ h01 h02 h12 =>
      exists_aniso_perp₃ hQ (by have := three_orth_dim h01 h02 h12; omega) F₀ F₁ F₂ h01 h02 h12

omit [Finite K] [FiniteDimensional K V] in
theorem span_le_of_gens {F : OFrame Q} {S : Submodule K V} (h₁ : F.e₁ ∈ S) (h₂ : F.f₁ ∈ S)
    (h₃ : F.e₂ ∈ S) (h₄ : F.f₂ ∈ S) : F.span ≤ S := by
  rintro _ ⟨X, rfl⟩
  rw [Frame.incl_apply]
  exact add_mem (add_mem (add_mem (S.smul_mem _ h₁) (S.smul_mem _ h₂)) (S.smul_mem _ h₃))
    (S.smul_mem _ h₄)

omit [Finite K] [FiniteDimensional K V] in
theorem commutes_La_range_of_span_le_perp (F G : OFrame Q) (h : G.span ≤ F.perp) :
    Commutes G.La.range F.La.range := by
  have horth := (span_le_perp_iff F G).mp h
  rintro _ ⟨X, rfl⟩ _ ⟨Y, rfl⟩
  exact Frame.La_comm_of_orth (fun X' Y' => by rw [polar_comm]; exact horth Y' X') X Y

theorem exists_hypPair_in_nondeg (hodd : Odd (Nat.card K)) {C : Submodule K V}
    (hC : PolarNondegOn Q C) (h3 : 3 ≤ Module.finrank K C) :
    ∃ P : HypPair Q, P.e ∈ C ∧ P.f ∈ C := by
  have hnd' : (polarBilin (Q.restrict C)).Nondegenerate := nondegenerate_polarBilin_restrict hC
  obtain ⟨v, hv0, hvQ⟩ :=
    ModelFacts.exists_isotropic_of_finrank_ge_three hodd (Q.restrict C) hnd' h3
  have hQe : Q (v : V) = 0 := by simpa using hvQ
  have hve : (v : V) ≠ 0 := fun h => hv0 (Subtype.ext h)
  obtain ⟨y, hy, hey⟩ := hC.exists_polar_ne_zero v.2 hve
  have h1 : polar Q (v : V) ((polar Q (v : V) y)⁻¹ • y) = 1 := by
    rw [polar_smul_right_eq, inv_mul_cancel₀ hey]
  exact ⟨HypPair.ofPolarEqOne hQe h1, v.2,
    Submodule.sub_mem _ (Submodule.smul_mem _ _ hy) (Submodule.smul_mem _ _ v.2)⟩

omit [Finite K] in
theorem finrank_le_inf_perp_add_two (hQ : (polarBilin Q).Nondegenerate) (C : Submodule K V)
    (P : HypPair Q) : Module.finrank K C ≤ Module.finrank K ↥(C ⊓ P.perp) + 2 := by
  have h1 := ModelFacts.finrank_hypPair_perp hQ P
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq C P.perp
  have h3 : Module.finrank K ↥(C ⊔ P.perp) ≤ Module.finrank K V := Submodule.finrank_le _
  omega

theorem exists_frame_in_perp (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) (F₁ : OFrame Q) : ∃ G : OFrame Q, G.span ≤ F₁.perp := by
  have hnd₀ : PolarNondegOn Q F₁.perp := ModelFacts.polarNondegOn_perp hQ F₁
  have hd₀ := ModelFacts.finrank_perp_add_four F₁
  obtain ⟨P', hP'e, hP'f⟩ := exists_hypPair_in_nondeg hodd hnd₀ (by omega)
  have hnd₁ : PolarNondegOn Q (F₁.perp ⊓ P'.perp) := hnd₀.inf_perp P' hP'e hP'f
  have hd₁ := finrank_le_inf_perp_add_two hQ F₁.perp P'
  obtain ⟨P'', hP''e, hP''f⟩ := exists_hypPair_in_nondeg hodd hnd₁ (by omega)
  have hort : P'.Orth P'' := by
    have h3 := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP''e).2
    have h4 := HypPair.mem_perp.mp (Submodule.mem_inf.mp hP''f).2
    exact ⟨h3.1, h4.1, h3.2, h4.2⟩
  exact ⟨⟨P', P'', hort⟩, span_le_of_gens (S := F₁.perp) hP'e hP'f
    (Submodule.mem_inf.mp hP''e).1 (Submodule.mem_inf.mp hP''f).1⟩

omit [Finite K] [FiniteDimensional K V] in
theorem La_neg_one_ne_of_span_le_perp (h2 : (2 : K) ≠ 0) {F₁ G : OFrame Q}
    (h : G.span ≤ F₁.perp) : G.La (-1) ≠ F₁.La (-1) := by
  intro e
  have hsp : G.span = F₁.span := Frame.span_eq_of_La_neg_one_eq h2 e
  have hmem := Submodule.disjoint_def.mp F₁.isCompl_span_perp.disjoint G.e₁
    (hsp ▸ G.e₁_mem_span) (h G.e₁_mem_span)
  exact G.P.e_ne_zero hmem

theorem fundSet_hasOrthogonal (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) : FundHasOrthogonal (fundSet Q) := by
  intro R hR
  have h2 := IsFundamental.two_ne_zero_of_odd hodd
  obtain ⟨i, F₁, rfl, rfl⟩ := hR
  obtain ⟨G, hG⟩ := exists_frame_in_perp hodd hQ hdim F₁
  have hne := La_neg_one_ne_of_span_le_perp h2 hG
  refine ⟨G.La.range, ⟨_, IsFundamental.of_frame G⟩, ?_, commutes_La_range_of_span_le_perp F₁ G hG,
    ?_⟩
  · intro e
    exact hne (IsFundamental.involution_unique hodd (IsFundamental.of_frame G)
      (by rw [e]; exact IsFundamental.of_frame F₁))
  · intro htw
    exact hne (hub_involution hodd hQ hdim (IsFundamental.of_frame F₁) (IsFundamental.of_frame G)
      htw.isHub)

theorem fundSet_twin_involution (hodd : Odd (Nat.card K)) (hQ : (polarBilin Q).Nondegenerate)
    (hdim : 9 ≤ Module.finrank K V) {L L' : Subgroup (V ≃ₗ[K] V)} {i i' : V ≃ₗ[K] V}
    (hL : IsFundamental Q L i) (hL' : IsFundamental Q L' i')
    (htw : IsFundTwin (fundSet Q) L L') : i' = i :=
  hub_involution hodd hQ hdim hL hL' htw.isHub

end Geometry

section Kernel

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {KY : Type} [Group KY] {π : KY →* (V ≃ₗ[K] V)} {𝓕 : Set (Subgroup KY)}

theorem TwinInvolutionKernel.of_centralQuot (hodd : Odd (Nat.card K))
    (hQ : (polarBilin Q).Nondegenerate) (hdim : 9 ≤ Module.finrank K V)
    (h : Gaps.CentralQuot π 𝓕 (fundSet Q) (scalars K V))
    (hker : ∃ ε ∈ π.ker, ∀ k ∈ π.ker, k = 1 ∨ k = ε) : TwinInvolutionKernel 𝓕 := by
  obtain ⟨ε, hεker, hker'⟩ := hker
  refine ⟨ε, fun R hR R' hR' hRR' r hr r' hr' hr2 hr'2 => ?_⟩
  have htw := IsFundTwin.to_map π h.ker_le h.perf h.surj hR hR' hRR'
  obtain ⟨i, hi⟩ := h.map_mem R hR
  obtain ⟨i', hi'⟩ := h.map_mem R' hR'
  have hπr : π r = i := Gaps.invOf_eq hodd hi (h.invOf hR ⟨hr, hr2⟩)
  have hπr' : π r' = i' := Gaps.invOf_eq hodd hi' (h.invOf hR' ⟨hr', hr'2⟩)
  have hii : i' = i := fundSet_twin_involution hodd hQ hdim hi hi' htw
  have hr'sq : r' * r' = 1 := by
    have := pow_orderOf_eq_one r'
    rwa [hr'2, pow_two] at this
  by_cases hrr : r = r'
  · exact Or.inl hrr
  · exact Or.inr (mul_eq_of_map_eq π h.ker_le hεker hker' hr'sq (by rw [hπr, hπr', hii]) hrr)

end Kernel

section Odd

variable {p f : ℕ} [Fact p.Prime]

theorem commutator_self_eq_of_le {G : Type} [Group G] {R : Subgroup G} (h : R ≤ ⁅R, R⁆) :
    ⁅R, R⁆ = R :=
  le_antisymm (Subgroup.commutator_le.mpr fun _ ha _ hb =>
    R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb)) h

theorem oddTwinsExist (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) :
    FundTwinsExist (modelFund p f .POmegaOdd n) := by
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have key : FundTwinsExist (fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f))) :=
    FundTwinsExist.of_central (spinAction (quadOdd n (GaloisField p f)))
      (ker_spinAction_le_center _) (fun R hR => commutator_self_eq_of_le (hperf R hR))
      (fundCorr_odd hp2 hq hadm).1 (fundCorr_odd hp2 hq hadm).2
      (fun L hL => exists_isFundTwin_fundSet hodd hL)
  exact key

theorem oddHubUnique (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f) {n : ℕ}
    (hadm : StatedLieAdmissible .POmegaOdd n p f) :
    FundHubUnique (modelFund p f .POmegaOdd n) := by
  obtain ⟨hodd, -⟩ := ModelFacts.card_galoisField_facts hp2 hq
  have hn3 : 3 ≤ n := hadm.2.2.1
  have hperf : Gaps.FundPerfect .POmegaOdd (modelUniv .POmegaOdd n p f Fact.out).D :=
    Gaps.fundPerfect_modelUniv hp2 trivial hadm (by omega)
  have hdim : Module.finrank (GaloisField p f) (Fin n ⊕ Fin n ⊕ Unit → GaloisField p f) =
      2 * n + 1 := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum, Fintype.card_fin,
      Fintype.card_unit]
    ring
  have key : FundHubUnique (fundamentalSubgroups .POmegaOdd (oddDatum n (GaloisField p f))) :=
    FundHubUnique.of_central (spinAction (quadOdd n (GaloisField p f)))
      (ker_spinAction_le_center _) (fun R hR => commutator_self_eq_of_le (hperf R hR))
      (fundCorr_odd hp2 hq hadm).1 (fundCorr_odd hp2 hq hadm).2
      (fundSet_hubUnique hodd (nondegenerate_polarBilin_quadOdd n (GaloisField p f)
        (ModelFacts.two_ne_zero_galoisField f hp2)) (by rw [hdim]; omega))
  exact key

end Odd

end CFSG.ClassicalInvolution.RouteD.Exotic
