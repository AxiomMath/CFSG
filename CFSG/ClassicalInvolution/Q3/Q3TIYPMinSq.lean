module

public import CFSG.ClassicalInvolution.Q3.Q3TLKSq
public import CFSG.ClassicalInvolution.Q3.Q3E8BCent
public import CFSG.ClassicalInvolution.RouteD.TWZSpinCount

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3TIY

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal CFSG.LieType.Universal.Spin CFSG.Assembly.LowTwoRank
  CFSG.ClassicalInvolution.RouteD.TWZ CFSG.ClassicalInvolution.RouteD.TwinY
  CFSG.ClassicalInvolution.Q3.Q3TLK
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)
open CFSG.ClassicalInvolution.Q3.Q3W (Pow3 CentralQuot3)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

local notation "GFund" => CFSG.ClassicalInvolution.Generic.fundamentalSubgroups


section Count

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem spin_sq_count3 (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (hV : 7 ≤ Module.finrank F (ι → F)) (hV8 : Module.finrank F (ι → F) ≤ 8)
    (hproj : ∀ F₁ F₂ : OFrame Q, F₂.La (-1) = LinearEquiv.neg F * F₁.La (-1) → False)
    {X : Type} [Group X] {θ : spinGroup Q →* X} (hθs : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSim Q θ)
    {t : StatedLieTag} {D : UniversalRootDatum (spinGroup Q)}
    {Z' : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (cq : CentralQuot3 (spinAction Q) (GFund t D) (fundSet Q) Z')
    {R R' : Subgroup (spinGroup Q)} (hR : R ∈ GFund t D) (hR' : R' ∈ GFund t D) (hne : R ≠ R')
    {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1) (hxx' : θ x = θ x')
    (α : MulAut X) (hα4 : α * α * (α * α) = 1)
    (hαR : ∀ r ∈ R, α (θ r) = θ r) (hαR' : ∀ r ∈ R', α (θ r) = θ r) :
    α * α = 1 ∨ α * α = MulAut.conj (θ x) ∨
      ∃ X' : Submodule F (ι → F), PolarNondegOn Q X' ∧
        Module.finrank F X' + 2 = Module.finrank F (ι → F) ∧
        Nat.card {S : Subgroup (spinGroup Q) // S ∈ GFund t D ∧
            ∀ r ∈ S, (α * α) (θ r) = θ r} *
          Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F))) =
        2 * Nat.card (OFrame (Q.restrict X')) := by
  classical
  obtain ⟨fr, ŷ, hF₁, hF₁', hθx, hsq, hy2, hspan_y, hy_mem⟩ :=
    exists_sq_data3 hodd hF3 hQ hrange hZ hZ3 hV hproj hθs hθk hlift
      (fun e => cq.map_inj hR hR' e) (cq.map_mem R hR) (cq.map_mem R' hR') (cq.inj R hR)
      (cq.inj R' hR') hne hx hx2 hx1 hx' hx'2 hx'1 hxx' α hα4 hαR hαR'
  have h2 : (2 : F) ≠ 0 := IsFundamental.two_ne_zero_of_odd hodd
  have : Invertible (2 : F) := invertibleOfNonzero h2
  have hyO : spinAction Q ŷ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    elementaryGroup_le_orthogonalGroup Q hy_mem
  have hθcent : ∀ c : spinGroup Q, c ∈ Subgroup.center (spinGroup Q) → ∀ g : X,
      θ c * g = g * θ c := by
    intro c hc g
    obtain ⟨t, rfl⟩ := hθs g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc t]
  by_cases hA : minusSp (spinAction Q ŷ) = ⊥
  ·
    left
    have hy1 : spinAction Q ŷ = 1 := eq_one_of_minusSp_eq_bot h2 hy2 hA
    have hŷc : ŷ ∈ Subgroup.center (spinGroup Q) :=
      ker_spinAction_le_center Q (by rw [MonoidHom.mem_ker]; exact hy1)
    refine MulEquiv.ext fun g => ?_
    rw [hsq g, MulAut.one_apply]
    have := hθcent ŷ hŷc g
    calc θ ŷ * g * (θ ŷ)⁻¹ = g * θ ŷ * (θ ŷ)⁻¹ := by rw [this]
      _ = g := by group
  by_cases hB : plusSp (spinAction Q ŷ) ⊓ fr.perp = ⊥
  ·
    right
    left
    have hneg := mul_La_neg_one_eq_neg h2 fr hyO hy2 hspan_y hB
    have hscal : (LinearEquiv.neg F : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) :=
      mem_scalars.mpr ⟨-1, fun v => by simp⟩
    have hc : ŷ * x⁻¹ ∈ Subgroup.center (spinGroup Q) := by
      refine Orth15.mem_center_of_commutators_central fun t => ker_spinAction_le_center Q ?_
      rw [MonoidHom.mem_ker, map_commutatorElement, map_mul, map_inv, hθx]
      have : spinAction Q ŷ * (fr.La (-1))⁻¹ = LinearEquiv.neg F := by
        rw [inv_eq_of_mul_eq_one_right fr.La_neg_one_mul_self]
        exact hneg
      rw [this]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (commute_of_mem_scalars hscal _)
    refine MulEquiv.ext fun g => ?_
    rw [hsq g, MulAut.conj_apply]
    have hŷ : θ ŷ = θ (ŷ * x⁻¹) * θ x := by rw [← map_mul]; congr 1; group
    have hcc := hθcent _ hc g
    rw [hŷ]
    calc θ (ŷ * x⁻¹) * θ x * g * (θ (ŷ * x⁻¹) * θ x)⁻¹
        = θ (ŷ * x⁻¹) * (θ x * g * (θ x)⁻¹) * (θ (ŷ * x⁻¹))⁻¹ := by group
      _ = θ x * g * (θ x)⁻¹ := by
        rw [hθcent _ hc (θ x * g * (θ x)⁻¹)]
        group
  right
  right
  have hdet : LinearEquiv.det (spinAction Q ŷ) = 1 :=
    CFSG.ClassicalInvolution.Asc77.T7H.det_spinAction_eq_one ŷ
  have heven : Even (Module.finrank F (minusSp (spinAction Q ŷ))) :=
    even_finrank_minusSp h2 hy2 hdet
  have hne0 : Module.finrank F (minusSp (spinAction Q ŷ)) ≠ 0 := fun h =>
    hA (Submodule.finrank_eq_zero.mp h)
  have hle : minusSp (spinAction Q ŷ) ≤ fr.perp := minusSp_le_perp fr h2 hyO hspan_y
  have hlt : minusSp (spinAction Q ŷ) < fr.perp := lt_of_le_of_ne hle fun h =>
    hB (by
      rw [← h]
      exact disjoint_iff.mp (isCompl_plusSp_minusSp h2 hy2).disjoint)
  have hperp4 : Module.finrank F fr.perp ≤ 4 := by
    have := finrank_perp_add_four fr
    omega
  have hlt4 : Module.finrank F (minusSp (spinAction Q ŷ)) < 4 := by
    have := Submodule.finrank_lt_finrank_of_lt hlt
    omega
  have hminus2 : Module.finrank F (minusSp (spinAction Q ŷ)) = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hker := ker_spinAction_le_center Q
  have hdimX := Submodule.finrank_add_eq_of_isCompl (isCompl_plusSp_minusSp h2 hy2)
  have hnd : PolarNondegOn Q (plusSp (spinAction Q ŷ)) :=
    CFSG.ClassicalInvolution.Asc77.polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hy2)
      (fun x hx y hy => polar_plusSp_minusSp h2 hyO hx hy)
  refine ⟨plusSp (spinAction Q ŷ), hnd, by omega, ?_⟩
  set X' := plusSp (spinAction Q ŷ) with hX'
  have hfix_iff : ∀ S ∈ GFund t D,
      ((∀ r ∈ S, (α * α) (θ r) = θ r) ↔ S ≤ Subgroup.centralizer ({ŷ} : Set (spinGroup Q))) := by
    intro S hS
    constructor
    · intro h r hr
      have hcomm : ∀ r ∈ S, ŷ * r = r * ŷ := by
        refine Q3TY.commutes_of_commutator_mem_center3 hZ3 (cq.pow3 S hS) fun r hr => hθk ?_
        rw [MonoidHom.mem_ker, map_commutatorElement]
        have h1 := h r hr
        rw [hsq] at h1
        refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
        calc θ ŷ * θ r = θ ŷ * θ r * (θ ŷ)⁻¹ * θ ŷ := by group
          _ = θ r * θ ŷ := by rw [h1]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hcomm r hr).symm
    · intro h r hr
      have h1 : r * ŷ = ŷ * r := Subgroup.mem_centralizer_singleton_iff.mp (h hr)
      have h2' : θ ŷ * θ r = θ r * θ ŷ := by
        rw [← map_mul, ← map_mul, h1]
      rw [hsq]
      calc θ ŷ * θ r * (θ ŷ)⁻¹ = θ r * θ ŷ * (θ ŷ)⁻¹ := by rw [h2']
        _ = θ r := by group
  have hLa : ∀ fr' : OFrame Q, fr'.La.range ≤ Subgroup.centralizer
      ({spinAction Q ŷ} : Set ((ι → F) ≃ₗ[F] (ι → F))) ↔ fr'.span ≤ X' := fun fr' =>
    La_range_le_centralizer_iff h2 fr' hyO hy2 hlt4
  let Lset : Set (Subgroup ((ι → F) ≃ₗ[F] (ι → F))) :=
    {L | ∃ fr' : OFrame Q, fr'.La.range = L ∧ fr'.span ≤ X'}
  have hmem : ∀ S : {S : Subgroup (spinGroup Q) // S ∈ GFund t D ∧
      ∀ r ∈ S, (α * α) (θ r) = θ r}, S.1.map (spinAction Q) ∈ Lset := by
    rintro ⟨S, hS, hSf⟩
    obtain ⟨i₀, fr', hfr, -⟩ := cq.map_mem S hS
    refine ⟨fr', hfr.symm, (hLa fr').mp ?_⟩
    have := (Q3W.le_centralizer_iff_map3 (spinAction Q) hker cq.cop (cq.pow3 S hS) ŷ).mp
      ((hfix_iff S hS).mp hSf)
    rw [hfr] at this
    exact this
  have hNat : Nat.card {S : Subgroup (spinGroup Q) // S ∈ GFund t D ∧
      ∀ r ∈ S, (α * α) (θ r) = θ r} = Lset.ncard := by
    rw [← Nat.card_coe_set_eq]
    refine Nat.card_congr (Equiv.ofBijective (fun S => ⟨S.1.map (spinAction Q), hmem S⟩)
      ⟨?_, ?_⟩)
    · intro S₁ S₂ h
      have h' := congrArg Subtype.val h
      exact Subtype.ext (cq.map_inj S₁.2.1 S₂.2.1 h')
    · rintro ⟨L, fr', hfr, hspan⟩
      have hL : L ∈ fundSet Q := ⟨_, hfr ▸ IsFundamental.of_frame fr'⟩
      obtain ⟨S, hS, hSL⟩ := cq.surj L hL
      refine ⟨⟨S, hS, ?_⟩, Subtype.ext hSL⟩
      refine (hfix_iff S hS).mpr ?_
      refine (Q3W.le_centralizer_iff_map3 (spinAction Q) hker cq.cop (cq.pow3 S hS) ŷ).mpr ?_
      rw [hSL, ← hfr]
      exact (hLa fr').mpr hspan
  have h1 := two_mul_card_frames_span_le (Q := Q) hodd X'
  have h3 := card_frames_span_le_restrict (Q := Q) X'
  rw [hNat]
  calc Lset.ncard * Nat.card (TauCeti.QuadraticMap.orthogonalGroup (detQ (K := F)))
      = 2 * Nat.card {fr' : OFrame Q // fr'.span ≤ X'} := h1.symm
    _ = 2 * Nat.card (OFrame (Q.restrict X')) := by rw [h3]

end Count

end CFSG.ClassicalInvolution.Q3.Q3TIY
