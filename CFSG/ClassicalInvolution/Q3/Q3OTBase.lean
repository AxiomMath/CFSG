module

public import CFSG.ClassicalInvolution.Q3.Q3TLKAut
public import CFSG.ClassicalInvolution.Q3.Q3NMTwin
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinSpin
public import CFSG.ClassicalInvolution.RouteD.TWZSpinA
public import CFSG.ClassicalInvolution.Asc77.WP3L52Main
public import CFSG.ClassicalInvolution.ModelFacts.Orth15TwinModel
public import CFSG.ClassicalInvolution.Q3.Q3NMClass
public import CFSG.ClassicalInvolution.Q3.Q3PBranch
public import CFSG.ClassicalInvolution.Q3.Q3WStd

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.Q3OT

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal QuadraticMap
  CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.Q3.Q3NM CFSG.ClassicalInvolution.Q3.Q3TLK
  CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.RouteD.TWZ
open CFSG.ClassicalInvolution.G2D4Models.Twin (LiftSimFr)
open CFSG.ClassicalInvolution.Models.Transfer (CenterScalar)
open scoped MatrixGroups

local notation "OFrame" => CFSG.ClassicalInvolution.Models.OrthogonalPairs.Frame

section Klein

variable {H : Type} [Group H]

theorem alphaOf_klein_inner3 (L : Subgroup H) (hL : AutOddFreeInner ↥L)
    {a b : ↥(inducedAutOn L)} (ha2 : a * a = 1) (hb2 : b * b = 1) (hab : a * b = b * a)
    (hb1 : b ≠ 1) (ha : (a : MulAut ↥L) ∈ innSubgroup ↥L)
    (hb : (b : MulAut ↥L) ∈ innSubgroup ↥L) :
    alphaOf (Subgroup.closure ({b, a} : Set ↥(inducedAutOn L))) = ⊥ := by
  have hP : ∀ g ∈ Subgroup.closure ({b, a} : Set ↥(inducedAutOn L)),
      (g : MulAut ↥L) ∈ innSubgroup ↥L := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact hb
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        exact ha
    | one => exact (innSubgroup ↥L).one_mem
    | mul y z _ _ ihy ihz => exact (innSubgroup ↥L).mul_mem ihy ihz
    | inv y _ ihy => exact (innSubgroup ↥L).inv_mem ihy
  exact alphaOf_eq_bot_of_on L (fun τ => τ ∈ innSubgroup ↥L) hL.toOn _
    (mul_self_eq_one_of_mem_closure_pair hb2 ha2 hab.symm)
    ⟨b, Subgroup.subset_closure (Set.mem_insert _ _), hb1⟩ fun g hg _ => hP g hg

end Klein

theorem ker_rangeRestrict_le {G K : Type*} [Group G] [Group K] (ψ : G →* K) {N : Subgroup G}
    (h : ψ.ker ≤ N) : ψ.rangeRestrict.ker ≤ N := by
  rwa [MonoidHom.ker_rangeRestrict]

section Generic

theorem ker_comp_symm_le_center {K X : Type*} [Group K] [Group X] (θ : K →* X)
    (hθk : θ.ker ≤ Subgroup.center K) (σ : K ≃* K) :
    (θ.comp σ.symm.toMonoidHom).ker ≤ Subgroup.center K := by
  intro s hs
  have h1 : σ.symm s ∈ θ.ker := by
    rw [MonoidHom.mem_ker] at hs ⊢
    exact hs
  have h2 := hθk h1
  have h3 : s = σ (σ.symm s) := by simp
  rw [h3, Subgroup.mem_center_iff]
  intro y
  have h4 := Subgroup.mem_center_iff.mp h2 (σ.symm y)
  simpa using congrArg σ h4

theorem commute_conj_of_mem_sup {K X : Type*} [Group K] [Group X] (θ : K →* X)
    (hθs : Function.Surjective θ) (v : MulAut X) {R₁ R₂ : Subgroup K}
    (h₁ : ∀ r ∈ R₁, ∀ g : X, v (θ r * g * (θ r)⁻¹) = θ r * v g * (θ r)⁻¹)
    (h₂ : ∀ r ∈ R₂, ∀ g : X, v (θ r * g * (θ r)⁻¹) = θ r * v g * (θ r)⁻¹)
    {s w : K} (hw : w ∈ R₁ ⊔ R₂) (hc : w⁻¹ * s ∈ Subgroup.center K) :
    ∀ g : X, v (θ s * g * (θ s)⁻¹) = θ s * v g * (θ s)⁻¹ := by
  set Cv : Subgroup X := (Subgroup.centralizer ({v} : Set (MulAut X))).comap
    (MulAut.conj : X →* MulAut X) with hCvdef
  have hCv : ∀ g₀ : X, g₀ ∈ Cv ↔
      ∀ g : X, v (g₀ * g * g₀⁻¹) = g₀ * v g * g₀⁻¹ := by
    intro g₀
    rw [hCvdef, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    constructor
    · intro h g
      have h3 := h v rfl
      have h4 := congrArg (fun φ : MulAut X => φ g) h3
      simpa [MulAut.conj_apply] using h4
    · intro h x hx
      rw [Set.mem_singleton_iff] at hx
      subst hx
      refine MulEquiv.ext fun g => ?_
      simpa [MulAut.conj_apply] using h g
  have hle : R₁ ⊔ R₂ ≤ Cv.comap θ := by
    refine sup_le (fun r hr => ?_) (fun r hr => ?_)
    · exact (hCv _).mpr (h₁ r hr)
    · exact (hCv _).mpr (h₂ r hr)
  have hθw : θ w ∈ Cv := hle hw
  have hcc : θ (w⁻¹ * s) ∈ Cv := by
    rw [hCv]
    intro g
    have hcen : θ (w⁻¹ * s) ∈ Subgroup.center X := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨t, rfl⟩ := hθs y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hc t]
    have hz := Subgroup.mem_center_iff.mp hcen
    have e1 : θ (w⁻¹ * s) * g * (θ (w⁻¹ * s))⁻¹ = g := by
      calc θ (w⁻¹ * s) * g * (θ (w⁻¹ * s))⁻¹ = g * θ (w⁻¹ * s) * (θ (w⁻¹ * s))⁻¹ := by
            rw [← hz g]
        _ = g := by group
    have e2 : θ (w⁻¹ * s) * v g * (θ (w⁻¹ * s))⁻¹ = v g := by
      calc θ (w⁻¹ * s) * v g * (θ (w⁻¹ * s))⁻¹ = v g * θ (w⁻¹ * s) * (θ (w⁻¹ * s))⁻¹ := by
            rw [← hz (v g)]
        _ = v g := by group
    rw [e1, e2]
  have hs' : θ s ∈ Cv := by
    have : θ s = θ w * θ (w⁻¹ * s) := by
      rw [← map_mul]
      congr 1
      group
    rw [this]
    exact Cv.mul_mem hθw hcc
  exact (hCv _).mp hs'

theorem pointwise_of_comm_conj {X : Type*} [Group X] (v : MulAut X) (t : X)
    (h : v * MulAut.conj t = MulAut.conj t * v) : ∀ g : X, v (t * g * t⁻¹) = t * v g * t⁻¹ := by
  intro g
  have := congrArg (fun φ : MulAut X => φ g) h
  simpa [MulAut.conj_apply] using this

theorem comm_conj_of_pointwise {X : Type*} [Group X] (v : MulAut X) (t : X)
    (h : ∀ g : X, v (t * g * t⁻¹) = t * v g * t⁻¹) : v * MulAut.conj t = MulAut.conj t * v := by
  refine MulEquiv.ext fun g => ?_
  simpa [MulAut.conj_apply] using h g

theorem ker_quot_le_center {K X : Type} [Group K] [Group X] [Group.IsPerfect K] (θ : K →* X)
    (hθs : Function.Surjective θ) (hθk : θ.ker ≤ Subgroup.center K) :
    ((QuotientGroup.mk' (Subgroup.center X)).comp θ).ker ≤ Subgroup.center K := by
  intro k hk
  have hcen := CFSG.ClassicalInvolution.Q3.center_le_map_center_of_perfect θ hθs hθk
  have h1 : θ k ∈ Subgroup.center X := (QuotientGroup.eq_one_iff _).mp hk
  obtain ⟨c, hc, hck⟩ := hcen h1
  have h2 : c⁻¹ * k ∈ θ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hck, inv_mul_cancel]
  have h3 : k = c * (c⁻¹ * k) := by group
  rw [h3]
  exact mul_mem hc (hθk h2)

theorem innerHom_ne_one_of_not_central {K H : Type} [Group K] [Group H] [Group.IsPerfect K]
    (ψ : K →* H) (hψ : ψ.ker ≤ Subgroup.center K) {x : K} (hx : x ∉ Subgroup.center K) :
    CFSG.ClassicalInvolution.Asc77.FrameVertex.innerHom ψ x ≠ 1 := by
  intro h1
  have hbc : ((CFSG.ClassicalInvolution.Asc77.FrameVertex.innerHom ψ x :
      ↥(CFSG.ClassicalInvolution.Asc77.inducedAutOn ψ.range)) : MulAut ↥ψ.range) =
      MulAut.conj (ψ.rangeRestrict x) := by
    ext y
    rfl
  have h2 : MulAut.conj (ψ.rangeRestrict x) = 1 := by
    rw [← hbc, h1]
    rfl
  have h3 : ψ.rangeRestrict x ∈ Subgroup.center ↥ψ.range := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut ↥ψ.range => φ g) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * ψ.rangeRestrict x = (ψ.rangeRestrict x * g * (ψ.rangeRestrict x)⁻¹) *
        ψ.rangeRestrict x := by rw [this]
      _ = ψ.rangeRestrict x * g := by group
  exact hx (ker_quot_le_center ψ.rangeRestrict ψ.rangeRestrict_surjective
    (ker_rangeRestrict_le ψ hψ) ((MonoidHom.mem_ker).mpr ((QuotientGroup.eq_one_iff _).mpr h3)))

end Generic

section Square

theorem liftSimFr_of_liftSim {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F]
    [Finite F] {Q : QuadraticForm F (ι → F)} {H : Type} [Group H] {ψ : spinGroup Q →* H}
    (h : LiftSim Q ψ) : LiftSimFr Q ψ := fun _ σ _ => h σ

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {X : Type} [Group X]

theorem exists_isometry_abs (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    [Group.IsPerfect (spinGroup Q)] (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c) (fr : OFrame Q)
    {θ : spinGroup Q →* X} (hθs : Function.Surjective θ)
    (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (α : MulAut X)
    (hlift : LiftSimFr Q θ)
    (hα : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ g : X, α (θ s * g * (θ s)⁻¹) = θ s * α g * (θ s)⁻¹) :
    ∃ (αK : spinGroup Q ≃* spinGroup Q) (w : (ι → F) ≃ₗ[F] (ι → F)),
      (∀ x, θ (αK x) = α (θ x)) ∧ w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧
        (∀ x ∈ fr.span, w x = x) ∧ ∀ x, spinAction Q (αK x) = w * spinAction Q x * w⁻¹ := by
  classical
  have hσc : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥θ.range, (autRange θ hθs α) (θ.rangeRestrict s * ℓ * (θ.rangeRestrict s)⁻¹) =
        θ.rangeRestrict s * (autRange θ hθs α) ℓ * (θ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    exact Subtype.ext (hα s hs ℓ)
  obtain ⟨αK, w, hαψ, hwO, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing_at3 hodd hF3 hrange hZ3 fr hθk (autRange θ hθs α)
      (hlift fr _ hσc) hσc
  exact ⟨αK, w, fun x => congrArg Subtype.val (hαψ x), hwO, hwspan, hθw⟩

theorem sq_mem_inn_abs (hodd : Odd (Nat.card F)) (hF3 : Nat.card F = 3)
    (hQ : (polarBilin Q).Nondegenerate) [Group.IsPerfect (spinGroup Q)]
    (hrange : (spinAction Q).range = elementaryGroup Q)
    (hZ3 : ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c)
    (hV : 7 ≤ Module.finrank F (ι → F)) (fr : OFrame Q) {θ : spinGroup Q →* X}
    (hθs : Function.Surjective θ) (hθk : θ.ker ≤ Subgroup.center (spinGroup Q)) (α : MulAut X)
    (hlift : LiftSimFr Q θ)
    (hα : ∀ s : spinGroup Q, spinAction Q s ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ g : X, α (θ s * g * (θ s)⁻¹) = θ s * α g * (θ s)⁻¹) :
    α * α ∈ innSubgroup X := by
  classical
  obtain ⟨αK, w, hθα, hwO, -, hθw⟩ :=
    exists_isometry_abs hodd hF3 hrange hZ3 fr hθs hθk α hlift hα
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwO
  obtain ⟨ŷ, -, hαα⟩ := exists_sq_lift hrange αK hy_mem hθw
  refine ⟨θ ŷ, ?_⟩
  refine MulEquiv.ext fun g => ?_
  obtain ⟨s, rfl⟩ := hθs g
  rw [MulAut.conj_apply, MulAut.mul_apply, ← hθα, ← hθα, hαα, map_mul, map_mul, map_inv]

theorem center_no_three [Nontrivial (ι → F)] (hF3 : Nat.card F = 3)
    (hrange : (spinAction Q).range = elementaryGroup Q) (hZ : CenterScalar Q)
    (hker2 : ∀ x ∈ (spinAction Q).ker, x * x = 1) :
    ∀ c ∈ Subgroup.center (spinGroup Q), ¬ 3 ∣ orderOf c := by
  intro c hc h3
  obtain ⟨μ, hμ⟩ := exists_smul_of_central hrange hZ hc
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = 3 := by rwa [← Nat.card_eq_fintype_card]
  have hμ3 : μ ^ 3 = μ := by
    have := FiniteField.pow_card μ
    rwa [hcard] at this
  obtain ⟨v, hv⟩ := exists_ne (0 : ι → F)
  have hμ0 : μ ≠ 0 := by
    intro h0
    apply hv
    have h1 : spinAction Q c v = 0 := by rw [hμ v, h0, zero_smul]
    exact (spinAction Q c).injective (by rw [h1, map_zero])
  have hμ2 : μ * μ = 1 := by
    have : μ * (μ * μ - 1) = 0 := by linear_combination hμ3
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hμ0
    · exact sub_eq_zero.mp h
  have hsq : c * c ∈ (spinAction Q).ker := by
    rw [MonoidHom.mem_ker]
    refine LinearEquiv.ext fun u => ?_
    rw [map_mul, LinearEquiv.mul_apply, hμ u, map_smul, hμ u, smul_smul, hμ2, one_smul]
    rfl
  have h4 : c ^ 4 = 1 := by
    have := hker2 _ hsq
    calc c ^ 4 = (c * c) * (c * c) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := this
  have hdvd : orderOf c ∣ 4 := orderOf_dvd_of_pow_eq_one h4
  have := (h3.trans hdvd)
  omega

end Square

end CFSG.ClassicalInvolution.Q3.Q3OT
