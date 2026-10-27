module

public import CFSG.ClassicalInvolution.RouteD.TWZSpinModel
public import CFSG.ClassicalInvolution.ModelFacts.Orth15RFixLift
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Inner
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
public import Certificates.Certificate76
public import Certificates.Certificate77
public import Certificates.Certificate78
public import Certificates.Certificate79
public import Certificates.Certificate80
public import Certificates.Certificate81
public import Certificates.Certificate113
public import Certificates.Certificate114
public import Certificates.Certificate115
public import Certificates.Certificate116
public import Certificates.Certificate117
public import Certificates.Certificate118
public import Certificates.Certificate119
public import Certificates.Certificate120
public import Certificates.Certificate121
public import Certificates.Certificate122
public import Certificates.Certificate123
public import Certificates.Certificate3951
public import Certificates.Certificate3952

public section

namespace CFSG.ClassicalInvolution.RouteD.TWT4

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.G2D4Models.Twin
  CFSG.ClassicalInvolution.RouteD.TWZ
open CFSG.ClassicalInvolution.RouteD.Exotic (commutes_of_commutator_mem_center)
open CFSG.ClassicalInvolution.RouteD.Gaps (fundSet)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Fixer

variable {S X : Type} [Group S] [Group X]

@[expose] def fixSub (θ : S →* X) (α : MulAut X) : Subgroup S where
  carrier := {s | α (θ s) = θ s}
  one_mem' := by simp
  mul_mem' {a b} ha hb := by
    show α (θ (a * b)) = θ (a * b)
    rw [map_mul, map_mul]
    exact congrArg₂ (· * ·) ha hb
  inv_mem' {a} ha := by
    show α (θ a⁻¹) = θ a⁻¹
    rw [map_inv, map_inv]
    exact congrArg (·⁻¹) ha

end Fixer

section Main

variable {F : Type} [Field F] [Finite F] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q : QuadraticForm F (ι → F)}

theorem exists_sq_data_ord (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : 7 ≤ Module.finrank F (ι → F))
    {X : Type} [Group X] {θ : spinGroup Q →* X} (hθs : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSimFr Q θ)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x')
    (α : MulAut X) (hα4 : α * α * (α * α) = 1)
    (hαR : ∀ r ∈ R, α (θ r) = θ r) (hαR' : ∀ r ∈ R', α (θ r) = θ r) :
    ∃ (fr : OFrame Q) (ŷ : spinGroup Q),
      R.map (spinAction Q) = fr.La.range ∧ R'.map (spinAction Q) = fr.swap.La.range ∧
      spinAction Q x = fr.La (-1) ∧ (∀ g : X, (α * α) g = θ ŷ * g * (θ ŷ)⁻¹) ∧
      spinAction Q ŷ * spinAction Q ŷ = 1 ∧ (∀ s ∈ fr.span, spinAction Q ŷ s = s) ∧
      spinAction Q ŷ ∈ elementaryGroup Q := by
  classical
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨fr, hF₁, hF₁', hθx, -⟩ := swap_of_twin_pair_ord hodd hRp hR'p hR hR' hinj hinj' hne
    hx hx2 hx1 hx' hx'2 hx'1 hord
  set σ := autRange θ hθs α with hσ
  have hfix : R ⊔ R' ≤ fixSub θ α := sup_le (fun r hr => hαR r hr) (fun r hr => hαR' r hr)
  have hσc : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥θ.range, σ (θ.rangeRestrict s * ℓ * (θ.rangeRestrict s)⁻¹) =
        θ.rangeRestrict s * σ ℓ * (θ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    rw [← hF₁, ← hF₁', ← Subgroup.map_sup] at hs
    obtain ⟨w, hw, hws⟩ := hs
    have hwfix : α (θ w) = θ w := hfix hw
    have hκ : w⁻¹ * s ∈ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hws, inv_mul_cancel])
    have hcc : ∀ g : X, θ (w⁻¹ * s) * g = g * θ (w⁻¹ * s) := by
      intro g
      obtain ⟨t, rfl⟩ := hθs g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hκ t]
    have hθs' : θ s = θ w * θ (w⁻¹ * s) := by rw [← map_mul]; congr 1; group
    have key : ∀ g : X, θ s * g * (θ s)⁻¹ = θ w * g * (θ w)⁻¹ := by
      intro g
      rw [hθs', mul_inv_rev]
      calc θ w * θ (w⁻¹ * s) * g * ((θ (w⁻¹ * s))⁻¹ * (θ w)⁻¹)
          = θ w * (θ (w⁻¹ * s) * g * (θ (w⁻¹ * s))⁻¹) * (θ w)⁻¹ := by group
        _ = θ w * g * (θ w)⁻¹ := by rw [hcc g]; group
    apply Subtype.ext
    show α (θ s * (ℓ : X) * (θ s)⁻¹) = θ s * α (ℓ : X) * (θ s)⁻¹
    rw [key, key, map_mul, map_mul, map_inv, hwfix]
  obtain ⟨α_K, w, hαψ, hwiso, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing_at hodd h5 hrange fr hθk σ (hlift fr σ hσc) hσc
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwiso
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α_K hy_mem hθw
  have hθα : ∀ s : spinGroup Q, θ (α_K s) = α (θ s) := fun s => by
    have := congrArg Subtype.val (hαψ s)
    exact this
  have hsq : ∀ g : X, (α * α) g = θ ŷ * g * (θ ŷ)⁻¹ := by
    intro g
    obtain ⟨s, rfl⟩ := hθs g
    rw [MulAut.mul_apply, ← hθα, ← hθα, hαα, map_mul, map_mul, map_inv]
  have hspan_y : ∀ s ∈ fr.span, spinAction Q ŷ s = s := fun s hs => by
    rw [hŷ, LinearEquiv.mul_apply, hwspan s hs, hwspan s hs]
  have hy2 : spinAction Q ŷ * spinAction Q ŷ = 1 := by
    have hcent : ∀ g : X, θ (ŷ * ŷ) * g = g * θ (ŷ * ŷ) := by
      intro g
      have h4 := congrArg (fun a : MulAut X => a g) hα4
      simp only [MulAut.mul_apply, MulAut.one_apply, hsq] at h4
      have h5' : θ (ŷ * ŷ) * g * (θ (ŷ * ŷ))⁻¹ = g := by
        rw [map_mul]
        calc θ ŷ * θ ŷ * g * (θ ŷ * θ ŷ)⁻¹
            = θ ŷ * (θ ŷ * g * (θ ŷ)⁻¹) * (θ ŷ)⁻¹ := by group
          _ = g := h4
      calc θ (ŷ * ŷ) * g = θ (ŷ * ŷ) * g * (θ (ŷ * ŷ))⁻¹ * θ (ŷ * ŷ) := by group
        _ = g * θ (ŷ * ŷ) := by rw [h5']
    have hcenter : ŷ * ŷ ∈ Subgroup.center (spinGroup Q) := by
      refine mem_center_of_commutators_central fun t => hθk ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (hcent (θ t))
    obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hcenter
    have hne1 : fr.incl 1 ≠ 0 := by
      intro h0
      have := congrArg fr.coords h0
      rw [Frame.coords_incl, map_zero] at this
      exact one_ne_zero (congrFun (congrFun this 0) 0)
    have hv : fr.incl 1 ∈ fr.span := ⟨1, rfl⟩
    have h1 : spinAction Q (ŷ * ŷ) (fr.incl 1) = fr.incl 1 := by
      rw [map_mul, LinearEquiv.mul_apply, hspan_y _ hv, hspan_y _ hv]
    have hμ1 : μ = 1 := by
      have h2 := hμ (fr.incl 1)
      rw [h1] at h2
      have : (μ - 1) • fr.incl 1 = 0 := by rw [sub_smul, ← h2, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hne1)
    rw [← map_mul]
    ext v
    rw [hμ v, hμ1, one_smul]
    rfl
  exact ⟨fr, ŷ, hF₁, hF₁', hθx, hsq, hy2, hspan_y, hŷ ▸ hy_mem⟩

theorem spin_sq_trichotomy_ord (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (hZ : CenterScalar Q) (hV : Module.finrank F (ι → F) = 8)
    {X : Type} [Group X] {θ : spinGroup Q →* X} (hθs : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSimFr Q θ)
    {R R' : Subgroup (spinGroup Q)} (hRp : R ≤ ⁅R, R⁆) (hR'p : R' ≤ ⁅R', R'⁆)
    (hR : R.map (spinAction Q) ∈ fundSet Q) (hR' : R'.map (spinAction Q) ∈ fundSet Q)
    (hinj : ∀ r ∈ R, spinAction Q r = 1 → r = 1) (hinj' : ∀ r ∈ R', spinAction Q r = 1 → r = 1)
    (hne : R ≠ R') {x x' : spinGroup Q} (hx : x ∈ R) (hx2 : x * x = 1) (hx1 : x ≠ 1)
    (hx' : x' ∈ R') (hx'2 : x' * x' = 1) (hx'1 : x' ≠ 1)
    (hord : spinAction Q x = spinAction Q x')
    {R₂ : Subgroup (spinGroup Q)} (hR₂p : R₂ ≤ ⁅R₂, R₂⁆)
    (hR₂ : R₂.map (spinAction Q) ∈ fundSet Q) (hinj₂ : ∀ r ∈ R₂, spinAction Q r = 1 → r = 1)
    {x₂ : spinGroup Q} (hx₂ : x₂ ∈ R₂) (hx₂2 : x₂ * x₂ = 1) (hx₂1 : x₂ ≠ 1)
    (α : MulAut X) (hα4 : α * α * (α * α) = 1)
    (hαR : ∀ r ∈ R, α (θ r) = θ r) (hαR' : ∀ r ∈ R', α (θ r) = θ r)
    (hαR₂ : ∀ r ∈ R₂, α (θ r) = θ r) :
    α * α = 1 ∨ α * α = MulAut.conj (θ x) ∨
      ∃ g : spinGroup Q,
        (∀ r ∈ R₂, (α * α) (θ x₂ * θ (g * r * g⁻¹) * (θ x₂)⁻¹) = θ (g * r * g⁻¹)) ∧
          ∃ r ∈ R₂, (α * α) (θ (g * r * g⁻¹)) ≠ θ (g * r * g⁻¹) := by
  classical
  obtain ⟨fr, ŷ, hF₁, hF₁', hθx, hsq, hy2, hspan_y, hy_mem⟩ :=
    exists_sq_data_ord hodd h5 hQ hrange hZ (by omega) hθs hθk hlift hRp hR'p hR hR' hinj hinj'
      hne hx hx2 hx1 hx' hx'2 hx'1 hord α hα4 hαR hαR'
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
  have h2le : 2 ≤ Module.finrank F (minusSp (spinAction Q ŷ)) := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hndW : PolarNondegOn Q (minusSp (spinAction Q ŷ)) :=
    polarNondegOn_minusSp h2 hQ hyO hy2
  have hQ'' : (Q.restrict (minusSp (spinAction Q ŷ))).Nondegenerate :=
    QuadraticMap.nondegenerate_polar_iff.mp (nondegenerate_polarBilin_restrict hndW)
  obtain ⟨l, hlen, hlorth, hlne, hlspan, -⟩ :=
    exists_orthogonal_list_restrict Q (minusSp (spinAction Q ŷ)) hQ''
  rcases l with _ | ⟨a₁, _ | ⟨a₂, rest⟩⟩
  · simp at hlen
    omega
  · simp at hlen
    omega
  have ha₁ : a₁ ∈ minusSp (spinAction Q ŷ) := hlspan ▸ Submodule.subset_span (by simp)
  have ha₂ : a₂ ∈ minusSp (spinAction Q ŷ) := hlspan ▸ Submodule.subset_span (by simp)
  have ha₁₂ : polar Q a₁ a₂ = 0 :=
    ((List.pairwise_cons.mp hlorth).1 a₂ (by simp)).polar_eq_zero
  have hQ₁ : Q a₁ ≠ 0 := hlne a₁ (by simp)
  have hQ₂ : Q a₂ ≠ 0 := hlne a₂ (by simp)
  obtain ⟨i₂, fr₂, hF₂, -⟩ := hR₂
  have hcomm₂ : ∀ r ∈ R₂, ŷ * r = r * ŷ := by
    refine commutes_of_commutator_mem_center hR₂p fun r hr => hθk ?_
    rw [MonoidHom.mem_ker, map_commutatorElement]
    have h1 : (α * α) (θ r) = θ r := by
      rw [MulAut.mul_apply, hαR₂ r hr, hαR₂ r hr]
    rw [hsq] at h1
    refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
    calc θ ŷ * θ r = θ ŷ * θ r * (θ ŷ)⁻¹ * θ ŷ := by group
      _ = θ r * θ ŷ := by rw [h1]
  have hycomm : ∀ A : SL(2, F), spinAction Q ŷ * fr₂.La A = fr₂.La A * spinAction Q ŷ := by
    intro A
    have hA' : fr₂.La A ∈ R₂.map (spinAction Q) := hF₂ ▸ ⟨A, rfl⟩
    obtain ⟨r, hr, hrA⟩ := hA'
    rw [← hrA, ← map_mul, ← map_mul, hcomm₂ r hr]
  rcases sign_on_span h2 fr₂ hyO hy2 hycomm with hpos | hneg₂
  swap
  ·
    exfalso
    have hle : fr₂.span ≤ fr.perp := fun x hx =>
      minusSp_le_perp fr h2 hyO hspan_y (mem_minusSp.mpr (hneg₂ x hx))
    have hd1 : Module.finrank F fr₂.span = 4 := fr₂.finrank_span
    have hd2 : Module.finrank F fr.perp = 4 := by
      have := finrank_perp_add_four fr
      omega
    have heq : fr₂.span = fr.perp := Submodule.eq_of_le_of_finrank_eq hle (by omega)
    refine hB ?_
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hv1, hv2⟩ := hv
    have hv3 : v ∈ fr₂.span := heq ▸ hv2
    have e1 : spinAction Q ŷ v = v := mem_plusSp.mp hv1
    have e2 := hneg₂ v hv3
    have : (2 : F) • v = 0 := by
      have h3 : v = -v := e1.symm.trans e2
      calc (2 : F) • v = v + v := two_smul F v
        _ = v + -v := by rw [← h3]
        _ = 0 := add_neg_cancel v
    exact (smul_eq_zero.mp this).resolve_left h2
  obtain ⟨fr', hτ, hnc⟩ := exists_linked_frame hodd fr₂ hyO hpos ha₁ ha₂ ha₁₂ hQ₁ hQ₂
  have hx₂θ : spinAction Q x₂ = fr₂.La (-1) := by
    have hmem : spinAction Q x₂ ∈ fr₂.La.range := hF₂ ▸ Subgroup.mem_map_of_mem _ hx₂
    have hsq' : spinAction Q x₂ * spinAction Q x₂ = 1 := by rw [← map_mul, hx₂2, map_one]
    have hne1 : spinAction Q x₂ ≠ 1 := fun h => hx₂1 (hinj₂ x₂ hx₂ h)
    have hord : orderOf (spinAction Q x₂) = 2 :=
      orderOf_eq_prime (by rw [pow_two]; exact hsq') hne1
    exact (IsFundamental.of_frame fr₂).eq_of_orderOf_eq_two hodd hmem hord
  have hperp : 2 ≤ Module.finrank F fr₂.perp := by
    have := finrank_perp_add_four fr₂
    omega
  have : Nontrivial (ι → F) := Module.nontrivial_of_finrank_pos (R := F) (by omega)
  obtain ⟨g, hg⟩ := exists_spin_conj hodd hQ fr₂ fr' hperp
  have hLa : ∀ r ∈ R₂, ∃ A : SL(2, F), fr'.La A = spinAction Q (g * r * g⁻¹) := by
    intro r hr
    have hmem : spinAction Q r ∈ fr₂.La.range := hF₂ ▸ Subgroup.mem_map_of_mem _ hr
    obtain ⟨A, hA'⟩ := hmem
    refine ⟨A, ?_⟩
    rw [hg A, hA', map_mul, map_mul, map_inv]
  have hLa' : ∀ A : SL(2, F), ∃ r ∈ R₂, fr'.La A = spinAction Q (g * r * g⁻¹) := by
    intro A
    have hA' : fr₂.La A ∈ R₂.map (spinAction Q) := hF₂ ▸ ⟨A, rfl⟩
    obtain ⟨r, hr, hrA⟩ := hA'
    refine ⟨r, hr, ?_⟩
    rw [hg A, ← hrA, map_mul, map_mul, map_inv]
  set R'' : Subgroup (spinGroup Q) := R₂.map (MulAut.conj g).toMonoidHom with hR''
  have hR''p : R'' ≤ ⁅R'', R''⁆ := by
    rw [hR'', ← Subgroup.map_commutator]
    exact Subgroup.map_mono hR₂p
  have hmemR'' : ∀ r ∈ R₂, g * r * g⁻¹ ∈ R'' := fun r hr =>
    ⟨r, hr, by simp [MulAut.conj_apply]⟩
  have hR''mem : ∀ r'' ∈ R'', ∃ r ∈ R₂, r'' = g * r * g⁻¹ := by
    rintro _ ⟨r, hr, rfl⟩
    exact ⟨r, hr, by simp [MulAut.conj_apply]⟩
  refine ⟨g, fun r hr => ?_, ?_⟩
  ·
    have hτO : spinAction Q ŷ * fr₂.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
      mul_mem hyO (fr₂.La_mem_orthogonalGroup (-1))
    have hcommR'' : ∀ r'' ∈ R'', ŷ * x₂ * r'' = r'' * (ŷ * x₂) := by
      refine commutes_of_commutator_mem_center hR''p fun r'' hr'' => ?_
      obtain ⟨r₁, hr₁, rfl⟩ := hR''mem r'' hr''
      refine ker_spinAction_le_center Q ?_
      rw [MonoidHom.mem_ker, map_commutatorElement]
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      obtain ⟨A, hA'⟩ := hLa r₁ hr₁
      rw [← hA', map_mul, hx₂θ]
      exact La_comm_of_neg_on_span fr' hτO hτ A
    have hu := hcommR'' _ (hmemR'' r hr)
    rw [hsq]
    have e1 : θ ŷ * (θ x₂ * θ (g * r * g⁻¹) * (θ x₂)⁻¹) * (θ ŷ)⁻¹ =
        θ (ŷ * x₂ * (g * r * g⁻¹) * (ŷ * x₂)⁻¹) := by
      simp only [map_mul, map_inv, mul_inv_rev]
      group
    rw [e1, hu, mul_inv_cancel_right]
  · by_contra hall
    push Not at hall
    have hcommR'' : ∀ r'' ∈ R'', ŷ * r'' = r'' * ŷ := by
      refine commutes_of_commutator_mem_center hR''p fun r'' hr'' => hθk ?_
      obtain ⟨r₁, hr₁, rfl⟩ := hR''mem r'' hr''
      rw [MonoidHom.mem_ker, map_commutatorElement]
      have h1 := hall r₁ hr₁
      rw [hsq] at h1
      refine commutatorElement_eq_one_iff_mul_comm.mpr ?_
      calc θ ŷ * θ (g * r₁ * g⁻¹) = θ ŷ * θ (g * r₁ * g⁻¹) * (θ ŷ)⁻¹ * θ ŷ := by group
        _ = θ (g * r₁ * g⁻¹) * θ ŷ := by rw [h1]
    refine hnc fun A => ?_
    obtain ⟨r₁, hr₁, hA'⟩ := hLa' A
    rw [hA', ← map_mul, ← map_mul, hcommR'' _ (hmemR'' r₁ hr₁)]

end Main

end CFSG.ClassicalInvolution.RouteD.TWT4
