module

public import CFSG.ClassicalInvolution.Asc77.AscSPN11
public import CFSG.ClassicalInvolution.ModelFacts.Orth15D4Lift
public import CFSG.ClassicalInvolution.RouteD.TwinYR2SpinGen

public section

namespace CFSG.ClassicalInvolution.Asc77

namespace SPN

set_option linter.unusedSectionVars false

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.G2D4Models.Twin CFSG.ClassicalInvolution.Models.OrthogonalPairs
  CFSG.ClassicalGroups.Orthogonal CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.RouteD.TwinY CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement MatrixGroups

section Geometry

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}
  [Finite F] [FiniteDimensional F V]

theorem elementaryGroup_le_of_involution (hodd : Odd (Nat.card F))
    (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) {w : V ≃ₗ[F] V}
    (hwO : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hww : w * w = 1)
    (hspan : ∀ x ∈ fr.span, w x = x) (hV : 7 ≤ Module.finrank F V) (hM0 : minusSp w ≠ ⊥)
    (hN0 : plusSp w ⊓ fr.perp ≠ ⊥) {H : Subgroup (V ≃ₗ[F] V)}
    (hHO : H ≤ TauCeti.QuadraticMap.orthogonalGroup Q) (hH₁ : elemOn Q (plusSp w) ≤ H)
    (hH₂ : elemOn Q fr.perp ≤ H) : elementaryGroup Q ≤ H := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  have hsp : PolarNondegOn Q fr.span :=
    polarNondegOn_of_isCompl hQ (Frame.isCompl_span_perp fr)
      (fun x hx y hy => polar_perp_of_mem_span fr hx hy)
  have hperp_dim : 3 ≤ Module.finrank F fr.perp := by
    have h := Submodule.finrank_add_eq_of_isCompl (Frame.isCompl_span_perp fr)
    rw [finrank_span_eq_four] at h
    omega
  have hperp_le : minusSp w ⊔ (plusSp w ⊓ fr.perp) = fr.perp := by
    refine le_antisymm (sup_le (minusSp_le_perp fr h2 hwO hspan) inf_le_right) fun p hp => ?_
    obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_eq_perp fr h2 hww hwO hspan hp
    exact Submodule.add_mem_sup hr hu |> fun h => by rwa [add_comm] at h
  have hndM : PolarNondegOn Q (minusSp w) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hww).symm
      (fun x hx z hz => by rw [polar_comm]; exact polar_plusSp_minusSp h2 hwO hz hx)
  have hndP : PolarNondegOn Q (plusSp w) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hww)
      (fun x hx z hz => polar_plusSp_minusSp h2 hwO hx hz)
  have hndN : PolarNondegOn Q (plusSp w ⊓ fr.perp) := by
    intro x hx hxx
    refine eq_zero_of_polar_eq_zero hQ fun v => ?_
    obtain ⟨s, hs, p, hp, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fr.span ⊔ fr.perp by rw [(Frame.isCompl_span_perp fr).sup_eq_top]; trivial)
    obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_eq_perp fr h2 hww hwO hspan hp
    have h1 : polar Q x s = 0 := by rw [polar_comm]; exact polar_perp_of_mem_span fr hs hx.2
    have h2' : polar Q x u = 0 := hxx u hu
    have h3 : polar Q x r = 0 := by
      have := polar_plusSp_minusSp h2 hwO hx.1 hr
      exact this
    rw [polar_add_right, polar_add_right, h1, h2', h3]
    ring
  have hplus : fr.span ⊔ (plusSp w ⊓ fr.perp) = plusSp w := by
    refine le_antisymm (sup_le (fun x hx => mem_plusSp.mpr (hspan x hx)) inf_le_left) fun v hv => ?_
    obtain ⟨hdec, hr⟩ := decomp_span_perp fr v
    have h1 : w (fr.incl (fr.coords v)) = fr.incl (fr.coords v) := hspan _ ⟨_, rfl⟩
    have hmem : v - fr.incl (fr.coords v) ∈ plusSp w := by
      rw [mem_plusSp, map_sub, h1, mem_plusSp.mp hv]
    exact Submodule.mem_sup.mpr ⟨fr.incl (fr.coords v), ⟨_, rfl⟩, v - fr.incl (fr.coords v),
      ⟨hmem, hr⟩, by abel⟩
  have hdim : 2 ≤ Module.finrank F ↥(plusSp w ⊓ fr.perp) ∨ 2 ≤ Module.finrank F ↥(minusSp w) := by
    have h1 := Submodule.finrank_add_le_finrank_add_finrank (minusSp w) (plusSp w ⊓ fr.perp)
    rw [hperp_le] at h1
    omega
  have htop : fr.span ⊔ (plusSp w ⊓ fr.perp) ⊔ minusSp w = ⊤ := by
    rw [hplus]
    exact (isCompl_plusSp_minusSp h2 hww).sup_eq_top
  refine elementaryGroup_le_of_overlap (U := fr.span) (N := plusSp w ⊓ fr.perp) (M := minusSp w)
    hodd hQ hsp (by rw [finrank_span_eq_four]; omega)
    (fun x hx y hy => polar_perp_of_mem_span fr hx hy.2)
    (fun x hx r hr => by rw [polar_comm]; exact polar_minusSp_span fr h2 hwO hspan hr hx)
    (fun n hn r hr => polar_plusSp_minusSp h2 hwO hn.1 hr) hndN hndM hN0 hM0 hdim htop hHO
    ?_ ?_
  · rw [hplus]
    exact hH₁
  · rw [sup_comm, hperp_le]
    exact hH₂

end Geometry

section Generation

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)}

theorem spinGroup_eq_fixed_sup_centralizer (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    {x : spinGroup Q} (hx : spinAction Q x = fr.La (-1)) (α : spinGroup Q ≃* spinGroup Q)
    {w : (ι → F) ≃ₗ[F] (ι → F)} (hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hww : w * w = 1) (hwspan : ∀ y ∈ fr.span, w y = y)
    (hθw : ∀ y, spinAction Q (α y) = w * spinAction Q y * w⁻¹) (hM : minusSp w ≠ ⊥)
    (hN : plusSp w ⊓ fr.perp ≠ ⊥) :
    CFSG.ClassicalInvolution.Balance.fixedGroup α ⊔
      Subgroup.centralizer ({x} : Set (spinGroup Q)) = ⊤ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  have hθker : (spinAction Q).ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hperp_nd : PolarNondegOn Q fr.perp := polarNondegOn_perp hQ fr
  have hperp3 : 3 ≤ Module.finrank F fr.perp := by
    have h := Submodule.finrank_add_eq_of_isCompl (Frame.isCompl_span_perp fr)
    rw [finrank_span_eq_four] at h
    omega
  have hplus_nd : PolarNondegOn Q (plusSp w) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hww)
      (fun x hx z hz => polar_plusSp_minusSp h2 hwiso hx hz)
  have hplus3 : 3 ≤ Module.finrank F (plusSp w) := by
    have h1 : fr.span ≤ plusSp w := fun x hx => mem_plusSp.mpr (hwspan x hx)
    have h2' := Submodule.finrank_mono h1
    rw [finrank_span_eq_four] at h2'
    omega
  have h₁ : elemOn Q (plusSp w) ≤
      (CFSG.ClassicalInvolution.Balance.fixedGroup α).map (spinAction Q) :=
    le_map_fixedGroup (spinAction Q) hθker α w hθw (elemOn_perfect hodd h5 hplus_nd hplus3)
      (by rw [hrange]; exact elemOn_le_elementaryGroup)
      (fun n hn => comm_of_scalar_elemOn hwiso (by simp : (1 : F) * 1 = 1)
        (fun y hy => by rw [mem_plusSp.mp hy, one_smul]) hn)
  have hθxO : spinAction Q x ∈ TauCeti.QuadraticMap.orthogonalGroup Q := by
    rw [hx]
    exact fr.La_mem_orthogonalGroup (-1)
  have h₂ : elemOn Q fr.perp ≤
      (Subgroup.centralizer ({x} : Set (spinGroup Q))).map (spinAction Q) :=
    elemOn_le_map_centralizer_of_fix hodd h5 hrange hperp_nd hperp3 hθxO
      (fun y hy => by rw [hx]; exact La_neg_one_of_mem_perp fr hy)
  have hHO : ((CFSG.ClassicalInvolution.Balance.fixedGroup α) ⊔
      Subgroup.centralizer ({x} : Set (spinGroup Q))).map (spinAction Q) ≤
        TauCeti.QuadraticMap.orthogonalGroup Q := by
    rintro _ ⟨y, -, rfl⟩
    have : spinAction Q y ∈ (spinAction Q).range := ⟨y, rfl⟩
    rw [hrange] at this
    exact elementaryGroup_le_orthogonalGroup Q this
  have hE : (spinAction Q).range ≤ ((CFSG.ClassicalInvolution.Balance.fixedGroup α) ⊔
      Subgroup.centralizer ({x} : Set (spinGroup Q))).map (spinAction Q) := by
    rw [hrange]
    exact elementaryGroup_le_of_involution hodd hQ fr hwiso hww hwspan hV hM hN hHO
      (h₁.trans (Subgroup.map_mono le_sup_left)) (h₂.trans (Subgroup.map_mono le_sup_right))
  exact eq_top_of_range_le_map (spinAction Q) hθker hE

end Generation

section Core

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

theorem eq_one_of_e_eq_one {X : Type} [Group X] (e : ↥(elementaryGroup Q) →* X)
    (hker : KerScalar Q e) (fr : Frame Q) {y : (ι → F) ≃ₗ[F] (ι → F)}
    (hy : y ∈ elementaryGroup Q) (hspan : ∀ x ∈ fr.span, y x = x) (hye : e ⟨y, hy⟩ = 1) :
    y = 1 := by
  obtain ⟨c', hc'⟩ := mem_scalars.mp (hker _ hye)
  have hne : fr.incl 1 ≠ 0 := by
    intro h0
    have := congrArg fr.coords h0
    rw [Frame.coords_incl, map_zero] at this
    exact one_ne_zero (congrFun (congrFun this 0) 0)
  have hspan1 : fr.incl 1 ∈ fr.span := ⟨1, rfl⟩
  have h4 : y (fr.incl 1) = fr.incl 1 := hspan _ hspan1
  have h5' : y (fr.incl 1) = c' • fr.incl 1 := hc' (fr.incl 1)
  have hc1 : c' = 1 := by
    rw [h4] at h5'
    have : (c' - 1) • fr.incl 1 = 0 := by rw [sub_smul, ← h5', one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hne)
  ext x
  rw [show y x = c' • x from hc' x, hc1, one_smul]
  rfl

theorem spinGen_core (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) {x : spinGroup Q}
    (hx : spinAction Q x = fr.La (-1)) (s : H) (hs : s ∈ Subgroup.normalizer (ψ.range : Set H))
    (hss : s * s = 1)
    (hlift : LiftSimAt Q ψ (toInducedAutOn ψ.range ⟨s, hs⟩ : MulAut ↥ψ.range))
    (hv : ∀ g : spinGroup Q, spinAction Q g ∈ fr.La.range ⊔ fr.swap.La.range →
      toInducedAutOn ψ.range ⟨s, hs⟩ * toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ =
        toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ *
          toInducedAutOn ψ.range ⟨s, hs⟩) :
    (∀ y ∈ ψ.range, s * y = y * s) ∨ (∀ y ∈ ψ.range, s * y * s⁻¹ = ψ x * y * (ψ x)⁻¹) ∨
      (∀ q ∈ ψ.range, q ∈ Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
        {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x})) := by
  classical
  set v : ↥(inducedAutOn ψ.range) := toInducedAutOn ψ.range ⟨s, hs⟩ with hvdef
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd hodd
  have h3 : 3 ≤ Module.finrank F (ι → F) := by omega
  obtain ⟨e, he, hker, hnorm, hcent⟩ := exists_hom_spin hodd hQ h3 hrange ψ hψ
  have hσ : ∀ g : spinGroup Q, spinAction Q g ∈ fr.La.range ⊔ fr.swap.La.range →
      ∀ ℓ : ↥ψ.range, (v : MulAut ↥ψ.range) (ψ.rangeRestrict g * ℓ * (ψ.rangeRestrict g)⁻¹) =
        ψ.rangeRestrict g * (v : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict g)⁻¹ := by
    intro g hg ℓ
    have h := congrArg (fun a : ↥(inducedAutOn ψ.range) => ((a : MulAut ↥ψ.range) ℓ : ↥ψ.range))
      (hv g hg)
    exact Subtype.ext (congrArg Subtype.val h)
  obtain ⟨α, w, hαψ, hwiso, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing_at hodd h5 hrange fr hψ (v : MulAut ↥ψ.range) hlift hσ
  have hy_mem : w * w ∈ elementaryGroup Q := sq_mem_of_frame hodd hQ fr hV hwiso
  have hspan_y : ∀ x ∈ fr.span, (w * w) x = x := fun x hx => by
    rw [LinearEquiv.mul_apply, hwspan x hx, hwspan x hx]
  obtain ⟨ŷ, hŷ, hαα⟩ := exists_sq_lift hrange α hy_mem hθw
  have hey : e ⟨w * w, hy_mem⟩ = v * v := e_sq_eq e he v α hαψ hy_mem hŷ hαα
  have hvv : v * v = 1 := by
    rw [hvdef, ← map_mul]
    have : (⟨s, hs⟩ * ⟨s, hs⟩ : ↥(Subgroup.normalizer (ψ.range : Set H))) = 1 := Subtype.ext hss
    rw [this, map_one]
  have hww : w * w = 1 := eq_one_of_e_eq_one e hker fr hy_mem hspan_y (by rw [hey, hvv])
  have hw_inv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww
  have hψα : ∀ g, ψ (α g) = s * ψ g * s⁻¹ := fun g => congrArg Subtype.val (hαψ g)
  by_cases hM : minusSp w = ⊥
  ·
    left
    have hw1 : w = 1 := eq_one_of_minusSp_eq_bot h2 hww hM
    have hαid : (α : spinGroup Q →* spinGroup Q) = MonoidHom.id _ := by
      refine hom_eq_of_central_diff _ _ fun g => ?_
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (spinAction Q g)⁻¹ * spinAction Q (α g) = 1
      rw [hθw, hw1, inv_one, one_mul, mul_one, inv_mul_cancel]
    rintro _ ⟨g, rfl⟩
    have h1 := hψα g
    have h2' : α g = g := DFunLike.congr_fun hαid g
    rw [h2'] at h1
    calc s * ψ g = (s * ψ g * s⁻¹) * s := by group
      _ = ψ g * s := by rw [← h1]
  by_cases hN : plusSp w ⊓ fr.perp = ⊥
  ·
    right
    left
    have hneg := mul_La_neg_one_eq_neg h2 fr hwiso hww hwspan hN
    have hττ : fr.La (-1) * fr.La (-1) = 1 := fr.La_neg_one_mul_self
    have hwτ : w = LinearEquiv.neg F * fr.La (-1) := by
      calc w = w * (fr.La (-1) * fr.La (-1)) := by rw [hττ, mul_one]
        _ = (w * fr.La (-1)) * fr.La (-1) := by rw [mul_assoc]
        _ = LinearEquiv.neg F * fr.La (-1) := by rw [hneg]
    have hnegc : ∀ h : (ι → F) ≃ₗ[F] (ι → F), LinearEquiv.neg F * h = h * LinearEquiv.neg F :=
      fun h => commute_of_mem_scalars (mem_scalars.mpr ⟨-1, fun v => by simp⟩) h
    have hθα : ∀ g, spinAction Q (α g) = fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹ := by
      intro g
      rw [hθw, hwτ]
      calc LinearEquiv.neg F * fr.La (-1) * spinAction Q g *
            (LinearEquiv.neg F * fr.La (-1))⁻¹
          = LinearEquiv.neg F * (fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹) *
            (LinearEquiv.neg F)⁻¹ := by group
        _ = (fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹) * LinearEquiv.neg F *
            (LinearEquiv.neg F)⁻¹ := by rw [hnegc]
        _ = fr.La (-1) * spinAction Q g * (fr.La (-1))⁻¹ := by group
    have hαconj : (α : spinGroup Q →* spinGroup Q) = (MulAut.conj x).toMonoidHom := by
      refine hom_eq_of_central_diff _ _ fun g => ?_
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, map_mul, map_inv]
      show (spinAction Q (x * g * x⁻¹))⁻¹ * spinAction Q (α g) = 1
      rw [hθα, map_mul, map_mul, map_inv, hx, inv_mul_cancel]
    rintro _ ⟨g, rfl⟩
    have h1 := hψα g
    have h2' : α g = x * g * x⁻¹ := DFunLike.congr_fun hαconj g
    rw [h2', map_mul, map_mul, map_inv] at h1
    exact h1.symm
  right
  right
  have htop := spinGroup_eq_fixed_sup_centralizer hodd h5 hQ hrange fr hV hx α hwiso hww hwspan hθw
    hM hN
  have hle : (CFSG.ClassicalInvolution.Balance.fixedGroup α ⊔
      Subgroup.centralizer ({x} : Set (spinGroup Q))).map ψ ≤
        Subgroup.closure ({q | q ∈ ψ.range ∧ s * q = q * s} ∪
          {q | q ∈ ψ.range ∧ ψ x * q = q * ψ x}) := by
    rw [Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨a, ha, rfl⟩
      refine Subgroup.subset_closure (Or.inl ⟨⟨a, rfl⟩, ?_⟩)
      have h1 := hψα a
      rw [CFSG.ClassicalInvolution.Balance.mem_fixedGroup.mp ha] at h1
      calc s * ψ a = (s * ψ a * s⁻¹) * s := by group
        _ = ψ a * s := by rw [← h1]
    · rintro _ ⟨b, hb, rfl⟩
      refine Subgroup.subset_closure (Or.inr ⟨⟨b, rfl⟩, ?_⟩)
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hb
      rw [← map_mul, ← map_mul, h1]
  rintro _ ⟨g, rfl⟩
  rw [htop] at hle
  exact hle ⟨g, Subgroup.mem_top g, rfl⟩

end Core

end SPN

end CFSG.ClassicalInvolution.Asc77
