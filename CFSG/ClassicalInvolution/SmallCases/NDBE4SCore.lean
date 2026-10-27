module

public import CFSG.ClassicalInvolution.SmallCases.NDBE3SCore

public section

namespace CFSG.ClassicalInvolution.NDB.SpinVertex

open CFSG.ClassicalInvolution.ModelFacts CFSG.ClassicalInvolution.ModelFacts.Orth15
  CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.Balance.StrongBalance.Orth
  CFSG.ClassicalInvolution.Asc77 CFSG.LieType.Universal.Spin CFSG.ClassicalInvolution.NDB.SpinStd
  CFSG.ClassicalInvolution.NDB.FourFrame QuadraticMap
open scoped MatrixGroups

variable {ι : Type} [Fintype ι] [DecidableEq ι] {F : Type} [Field F] [Finite F]
  {Q : QuadraticForm F (ι → F)} {H : Type} [Group H]

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem top_le_commutators (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] {J₁ J₂ : Subgroup ((ι → F) ≃ₗ[F] (ι → F))}
    (hJ₁ : J₁ ≤ elementaryGroup Q) (hJ₂ : J₂ ≤ elementaryGroup Q) (hp₁ : ⁅J₁, J₁⁆ = J₁)
    (hp₂ : ⁅J₂, J₂⁆ = J₂) (hgen : elementaryGroup Q ≤ J₁ ⊔ J₂) :
    (⊤ : Subgroup (spinGroup Q)) ≤ ⁅J₁.comap (spinAction Q), J₁.comap (spinAction Q)⁆ ⊔
      ⁅J₂.comap (spinAction Q), J₂.comap (spinAction Q)⁆ := by
  set θ := spinAction Q with hθ
  have hker : θ.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  set M : Subgroup (spinGroup Q) := ⁅J₁.comap θ, J₁.comap θ⁆ ⊔ ⁅J₂.comap θ, J₂.comap θ⁆ with hM
  have hlift : ∀ (J : Subgroup ((ι → F) ≃ₗ[F] (ι → F))), J ≤ elementaryGroup Q → ⁅J, J⁆ = J →
      ⁅J.comap θ, J.comap θ⁆ ≤ M → J ≤ M.map θ := by
    intro J hJ hp hJM g hg
    obtain ⟨s, hs, rfl⟩ := exists_lift_commutator θ (hJ.trans hrange.ge) hp g hg
    exact ⟨s, hJM hs, rfl⟩
  have h₁ := hlift J₁ hJ₁ hp₁ le_sup_left
  have h₂ := hlift J₂ hJ₂ hp₂ le_sup_right
  have hdec : ∀ x : spinGroup Q, ∃ m ∈ M, ∃ z ∈ Subgroup.center (spinGroup Q), x = m * z := by
    intro x
    obtain ⟨m, hm, hmx⟩ := (sup_le h₁ h₂) (hgen (show θ x ∈ elementaryGroup Q from
      hrange ▸ ⟨x, rfl⟩))
    refine ⟨m, hm, m⁻¹ * x, hker ?_, by group⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hmx, inv_mul_cancel]
  rw [← Group.IsPerfect.commutator_eq_top (G := spinGroup Q), commutator, Subgroup.commutator_le]
  intro x _ y _
  obtain ⟨m, hm, z, hz, rfl⟩ := hdec x
  obtain ⟨m', hm', z', hz', rfl⟩ := hdec y
  rw [Orth15.commutatorElement_mul_central hz hz', commutatorElement_def]
  exact M.mul_mem (M.mul_mem (M.mul_mem hm hm') (M.inv_mem hm)) (M.inv_mem hm')

theorem exists_lift (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q)) (hlift : LiftSim Q ψ)
    {R R' : Subgroup (spinGroup Q)} (hRfr : R.map (spinAction Q) = fr.La.range)
    (hR'fr : R'.map (spinAction Q) = fr.swap.La.range) {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) (hvR' : ∀ r ∈ R', v * ψ r = ψ r * v) :
    ∃ (α : spinGroup Q ≃* spinGroup Q) (w : (ι → F) ≃ₗ[F] (ι → F)),
      (∀ s, ψ (α s) = v * ψ s * v⁻¹) ∧ (∀ s, α (α s) = s) ∧
      w ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ (∀ y ∈ fr.span, w y = y) ∧
      (∀ s, spinAction Q (α s) = w * spinAction Q s * w⁻¹) ∧ w * w = 1 := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set θ := spinAction Q with hθ
  have hker : θ.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  set vI := toInducedAutOn ψ.range ⟨v, hv⟩ with hvI
  have hvRR : R ⊔ R' ≤ (Subgroup.centralizer ({v} : Set H)).comap ψ := by
    refine sup_le (fun r hr => ?_) (fun r hr => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hvR r hr).symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hvR' r hr).symm
  have hcen : ∀ k ∈ Subgroup.center (spinGroup Q), ∀ ℓ ∈ ψ.range, ψ k * ℓ = ℓ * ψ k := by
    rintro k hk _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hk y).symm]
  have hvn : ∀ ℓ ∈ ψ.range, v⁻¹ * ℓ * v ∈ ψ.range := fun ℓ hℓ => by
    have h := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hv) ℓ).mp hℓ
    rwa [inv_inv] at h
  have hσ : ∀ s : spinGroup Q, θ s ∈ fr.La.range ⊔ fr.swap.La.range → ∀ ℓ : ↥ψ.range,
      (vI : MulAut ↥ψ.range) (ψ.rangeRestrict s * ℓ * (ψ.rangeRestrict s)⁻¹) =
        ψ.rangeRestrict s * (vI : MulAut ↥ψ.range) ℓ * (ψ.rangeRestrict s)⁻¹ := by
    intro s hs ℓ
    rw [← hRfr, ← hR'fr, ← Subgroup.map_sup] at hs
    obtain ⟨r, hr, hrs⟩ := hs
    have hk : r⁻¹ * s ∈ Subgroup.center (spinGroup Q) := hker (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hrs, inv_mul_cancel])
    have hvr : v * ψ r = ψ r * v := (Subgroup.mem_centralizer_singleton_iff.mp (hvRR hr)).symm
    have hs' : ψ s = ψ r * ψ (r⁻¹ * s) := by rw [← map_mul, mul_inv_cancel_left]
    apply Subtype.ext
    show v * (ψ s * ↑ℓ * (ψ s)⁻¹) * v⁻¹ = ψ s * (v * ↑ℓ * v⁻¹) * (ψ s)⁻¹
    have hℓ := ℓ.2
    have hvℓ : v * (ℓ : H) * v⁻¹ ∈ ψ.range :=
      (Subgroup.mem_normalizer_iff.mp hv ℓ).mp hℓ
    have c1 := hcen _ hk ℓ hℓ
    have c2 := hcen _ hk _ (hvn (v * (ℓ : H) * v⁻¹) hvℓ)
    have c3 : v⁻¹ * (v * (ℓ : H) * v⁻¹) * v = ℓ := by group
    rw [c3] at c2
    rw [hs']
    calc v * (ψ r * ψ (r⁻¹ * s) * ↑ℓ * (ψ r * ψ (r⁻¹ * s))⁻¹) * v⁻¹
        = v * ψ r * (ψ (r⁻¹ * s) * ↑ℓ * (ψ (r⁻¹ * s))⁻¹) * (ψ r)⁻¹ * v⁻¹ := by group
      _ = v * ψ r * ↑ℓ * (ψ r)⁻¹ * v⁻¹ := by rw [c1]; group
      _ = ψ r * (v * ↑ℓ * v⁻¹) * (ψ r)⁻¹ := by
        rw [hvr]
        have hvr' : (ψ r)⁻¹ * v⁻¹ = v⁻¹ * (ψ r)⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hvr]
        calc ψ r * v * ↑ℓ * (ψ r)⁻¹ * v⁻¹ = ψ r * v * ↑ℓ * ((ψ r)⁻¹ * v⁻¹) := by group
          _ = ψ r * v * ↑ℓ * (v⁻¹ * (ψ r)⁻¹) := by rw [hvr']
          _ = ψ r * (v * ↑ℓ * v⁻¹) * (ψ r)⁻¹ := by group
      _ = ψ r * ψ (r⁻¹ * s) * (v * ↑ℓ * v⁻¹) * (ψ r * ψ (r⁻¹ * s))⁻¹ := by
        rw [mul_inv_rev]
        calc ψ r * (v * ↑ℓ * v⁻¹) * (ψ r)⁻¹
            = ψ r * (v * ↑ℓ * v⁻¹ * ψ (r⁻¹ * s)) * (ψ (r⁻¹ * s))⁻¹ * (ψ r)⁻¹ := by group
          _ = ψ r * (ψ (r⁻¹ * s) * (v * ↑ℓ * v⁻¹)) * (ψ (r⁻¹ * s))⁻¹ * (ψ r)⁻¹ := by
            rw [hcen _ hk _ hvℓ]
          _ = _ := by group
  obtain ⟨α, w, hαψ, hwiso, hwspan, hθw⟩ :=
    exists_isometry_of_centralizing hodd h5 hrange fr hψ hlift (vI : MulAut ↥ψ.range) hσ
  have hα' : ∀ s, ψ (α s) = v * ψ s * v⁻¹ := fun s => congrArg Subtype.val (hαψ s)
  have hvinv : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hα2 : ∀ s, α (α s) = s := by
    have key := OrthAut.eq_of_inv_mul_mem_center
      ((α : spinGroup Q →* spinGroup Q).comp (α : spinGroup Q →* spinGroup Q))
      (MonoidHom.id _) (fun s => by
        apply hψ
        rw [MonoidHom.mem_ker]
        change ψ (s⁻¹ * α (α s)) = 1
        rw [map_mul, map_inv, hα', hα', hvinv]
        calc (ψ s)⁻¹ * (v * (v * ψ s * v) * v) = (ψ s)⁻¹ * ((v * v) * ψ s * (v * v)) := by group
          _ = 1 := by rw [hv2]; group)
    exact fun y => (DFunLike.congr_fun key y).symm
  refine ⟨α, w, hα', hα2, hwiso, hwspan, hθw, ?_⟩
  have hcomm : ∀ g ∈ elementaryGroup Q, (w * w) * g = g * (w * w) := by
    intro g hg
    obtain ⟨s, rfl⟩ : g ∈ θ.range := hrange ▸ hg
    have h := hθw (α s)
    rw [hα2, hθw] at h
    have hw' : (w * w) * θ s * (w * w)⁻¹ = θ s := by
      calc (w * w) * θ s * (w * w)⁻¹ = w * (w * θ s * w⁻¹) * w⁻¹ := by group
        _ = θ s := h.symm
    calc w * w * θ s = (w * w) * θ s * (w * w)⁻¹ * (w * w) := by group
      _ = θ s * (w * w) := by rw [hw']
  have hA := hasAnisoPerp_of_three_le_finrank hQ (by omega : 3 ≤ Module.finrank F (ι → F))
  obtain ⟨P, -, -⟩ := exists_hypPair_le hodd (polarNondegOn_top hQ) (by
    rw [finrank_top]
    omega)
  have hsc := mem_scalars_of_commute_eichler h2 hQ hA P (mul_mem hwiso hwiso)
    (fun u w' _ _ => hcomm _ (eichler_mem_elementaryGroup Q u w'))
  obtain ⟨c, hc⟩ := mem_scalars.mp hsc
  have hne : fr.incl 1 ≠ 0 := by
    intro h0
    have := congrArg fr.coords h0
    rw [Frame.coords_incl, map_zero] at this
    exact one_ne_zero (congrFun (congrFun this 0) 0)
  have h4 : (w * w) (fr.incl 1) = fr.incl 1 := by
    rw [LinearEquiv.mul_apply, hwspan _ ⟨1, rfl⟩, hwspan _ ⟨1, rfl⟩]
  have hc1 : c = 1 := by
    have h5' := hc (fr.incl 1)
    rw [h4] at h5'
    have : (c - 1) • fr.incl 1 = 0 := by rw [sub_smul, ← h5', one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hne)
  ext y
  rw [show (w * w : (ι → F) ≃ₗ[F] (ι → F)) y = c • y from hc y, hc1, one_smul]
  rfl

omit [DecidableEq ι] in
theorem top_le_comap (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) {ψ : spinGroup Q →* H} {v : H}
    {x : spinGroup Q} (hx : spinAction Q x = fr.La (-1)) {α : spinGroup Q ≃* spinGroup Q}
    {w : (ι → F) ≃ₗ[F] (ι → F)} (hα' : ∀ s, ψ (α s) = v * ψ s * v⁻¹)
    (hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hwspan : ∀ y ∈ fr.span, w y = y)
    (hθw : ∀ s, spinAction Q (α s) = w * spinAction Q s * w⁻¹) (hw2 : w * w = 1) :
    (Subgroup.centralizer ({v} : Set H)).comap ψ ⊔
      (Subgroup.centralizer ({v * ψ x} : Set H)).comap ψ = ⊤ := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set θ := spinAction Q with hθ
  have hker : θ.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hzO : fr.La (-1) ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fr.La_mem_orthogonalGroup (-1)
  have hwz : w * fr.La (-1) = fr.La (-1) * w := by
    refine LinearEquiv.ext fun y => ?_
    obtain ⟨s, hs, t, ht, rfl⟩ := exists_decomp fr y
    have hwt : w t ∈ fr.perp := map_mem_perp_of_fix fr hwiso hwspan ht
    simp only [LinearEquiv.mul_apply, map_add, La_neg_one_of_mem_span fr hs,
      La_neg_one_of_mem_perp fr ht, map_neg, hwspan s hs, La_neg_one_of_mem_perp fr hwt]
  have huu : w * fr.La (-1) * (w * fr.La (-1)) = 1 := by
    calc w * fr.La (-1) * (w * fr.La (-1)) = w * (fr.La (-1) * w) * fr.La (-1) := by group
      _ = w * (w * fr.La (-1)) * fr.La (-1) := by rw [← hwz]
      _ = (w * w) * (fr.La (-1) * fr.La (-1)) := by group
      _ = 1 := by rw [hw2, fr.La_neg_one_mul_self, one_mul]
  set u := w * fr.La (-1) with hu
  have huO : u ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem hwiso hzO
  have hnd₁ : PolarNondegOn Q (plusSp w) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hw2)
      (fun a ha b hb => polar_plusSp_minusSp h2 hwiso ha hb)
  have hnd₂ : PolarNondegOn Q (minusSp u) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 huu).symm
      (fun a ha b hb => by rw [polar_comm]; exact polar_plusSp_minusSp h2 huO hb ha)
  have hspan₁ : fr.span ≤ plusSp w := fun y hy => mem_plusSp.mpr (hwspan y hy)
  have hspan₂ : fr.span ≤ minusSp u := fun y hy => mem_minusSp.mpr (by
    rw [hu, LinearEquiv.mul_apply, La_neg_one_of_mem_span fr hy, map_neg, hwspan y hy])
  have hU₁ : minusSp w ≤ minusSp u := fun r hr => mem_minusSp.mpr (by
    rw [hu, LinearEquiv.mul_apply,
      La_neg_one_of_mem_perp fr (minusSp_le_perp fr h2 hwiso hwspan hr), mem_minusSp.mp hr])
  have htop : minusSp w ⊔ (plusSp w ⊓ fr.perp) ⊔ fr.span = ⊤ := by
    rw [eq_top_iff]
    intro y _
    obtain ⟨a, ha, r, hr, rfl⟩ := exists_add_eq h2 hw2 y
    obtain ⟨s, hs, t, ht, rfl⟩ := exists_decomp fr a
    have htw : t ∈ plusSp w := by
      have := (plusSp w).sub_mem ha (hspan₁ hs)
      rwa [add_sub_cancel_left] at this
    have e : s + t + r = r + t + s := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _ (Submodule.mem_sup_left
      (Submodule.mem_sup_left hr)) (Submodule.mem_sup_left (Submodule.mem_sup_right ⟨htw, ht⟩)))
      (Submodule.mem_sup_right hs)
  have hgen0 := elementaryGroup_le_join_of_decomp hodd hQ (U₁ := minusSp w)
    (U₂ := plusSp w ⊓ fr.perp) (W := fr.span) (nd_span fr hQ) (by rw [finrank_span_eq_four]; omega)
    (fun a ha b hb => polar_minusSp_span fr h2 hwiso hwspan ha hb)
    (fun a ha b hb => by rw [polar_comm]; exact polar_perp_of_mem_span fr hb ha.2) htop
  have hgen : elementaryGroup Q ≤ elemOn Q (plusSp w) ⊔ elemOn Q (minusSp u) :=
    hgen0.trans (sup_le_sup (elemOn_mono (sup_le inf_le_left hspan₁))
      (elemOn_mono (sup_le hU₁ hspan₂)))
  have hperf : ∀ S : Submodule F (ι → F), PolarNondegOn Q S →
      ⁅elemOn Q S, elemOn Q S⁆ = elemOn Q S := fun S hS =>
    le_antisymm (commutator_le_self' _)
      (le_commutator_of_layerGenOn (layerGenOn_of_regular hodd h5 hS))
  have htop' := top_le_commutators hrange elemOn_le_elementaryGroup elemOn_le_elementaryGroup
    (hperf _ hnd₁) (hperf _ hnd₂) hgen
  have hc₁ : ⁅(elemOn Q (plusSp w)).comap θ, (elemOn Q (plusSp w)).comap θ⁆ ≤
      (Subgroup.centralizer ({v} : Set H)).comap ψ := by
    intro g hg
    have hfix := alpha_fixes_commutators α (S := (elemOn Q (plusSp w)).comap θ) (fun s hs => by
      apply hker
      have hc := comm_of_scalar_elemOn hwiso (one_mul (1 : F))
        (fun y hy => by rw [mem_plusSp.mp hy, one_smul]) (Subgroup.mem_comap.mp hs)
      rw [MonoidHom.mem_ker, map_mul, map_inv, hθw, hc, mul_assoc, mul_inv_cancel, mul_one,
        inv_mul_cancel]) g hg
    have h1 := hα' g
    rw [hfix] at h1
    show ψ g ∈ Subgroup.centralizer ({v} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ψ g * v = v * ψ g * v⁻¹ * v := by rw [← h1]
      _ = v * ψ g := by group
  have hc₂ : ⁅(elemOn Q (minusSp u)).comap θ, (elemOn Q (minusSp u)).comap θ⁆ ≤
      (Subgroup.centralizer ({v * ψ x} : Set H)).comap ψ := by
    intro g hg
    set β : spinGroup Q ≃* spinGroup Q := (MulAut.conj x).trans α with hβ
    have hβs : ∀ s, β s = α (x * s * x⁻¹) := fun s => rfl
    have hfix := alpha_fixes_commutators β (S := (elemOn Q (minusSp u)).comap θ) (fun s hs => by
      apply hker
      have hneg : (-1 : F) * -1 = 1 := by ring
      have hc := comm_of_scalar_elemOn huO hneg
        (fun y hy => by rw [mem_minusSp.mp hy, neg_one_smul]) (Subgroup.mem_comap.mp hs)
      rw [MonoidHom.mem_ker, map_mul, map_inv, hβs, hθw, map_mul, map_mul, map_inv, hx]
      have e : w * (fr.La (-1) * θ s * (fr.La (-1))⁻¹) * w⁻¹ = u * θ s * u⁻¹ := by
        rw [hu]
        group
      rw [e, hc, mul_assoc, mul_inv_cancel, mul_one, inv_mul_cancel]) g hg
    have h1 := hα' (x * g * x⁻¹)
    rw [← hβs, hfix, map_mul, map_mul, map_inv] at h1
    show ψ g ∈ Subgroup.centralizer ({v * ψ x} : Set H)
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc ψ g * (v * ψ x) = v * (ψ x * ψ g * (ψ x)⁻¹) * v⁻¹ * (v * ψ x) := by rw [← h1]
      _ = v * ψ x * ψ g := by group
  exact eq_top_iff.mpr (htop'.trans (sup_le_sup hc₁ hc₂))

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem conj_eq_of_scalar [Group.IsPerfect (spinGroup Q)] {g : spinGroup Q}
    (hg : spinAction Q g ∈ scalars F (ι → F)) (s : spinGroup Q) : g * s * g⁻¹ = s := by
  have key := OrthAut.eq_of_inv_mul_mem_center
    ((MulAut.conj g).toMonoidHom : spinGroup Q →* spinGroup Q) (MonoidHom.id _) (fun s => by
      apply ker_spinAction_le_center Q
      rw [MonoidHom.mem_ker, MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        map_mul, map_inv, map_mul, map_mul, map_inv, commute_of_mem_scalars hg]
      group)
  have := DFunLike.congr_fun key s
  simp only [MonoidHom.id_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
  exact this.symm

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem centralizes_of_inner [Group.IsPerfect (spinGroup Q)] {ψ : spinGroup Q →* H} {v : H}
    {g x : spinGroup Q} (hvg : ∀ s, v * ψ s * v⁻¹ = ψ g * ψ s * (ψ g)⁻¹) (hx2 : x * x = 1)
    (hvx : v * ψ x = ψ x * v) :
    (spinAction Q g ∈ scalars F (ι → F) → ∀ y ∈ ψ.range, v * y = y * v) ∧
      (spinAction Q (g * x) ∈ scalars F (ι → F) →
        ∀ y ∈ ψ.range, v * ψ x * y = y * (v * ψ x)) := by
  refine ⟨fun hg => ?_, fun hg => ?_⟩
  · rintro _ ⟨s, rfl⟩
    have h1 := hvg s
    rw [← map_mul, ← map_inv, ← map_mul, conj_eq_of_scalar hg s] at h1
    calc v * ψ s = v * ψ s * v⁻¹ * v := by group
      _ = ψ s * v := by rw [h1]
  · rintro _ ⟨s, rfl⟩
    have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have h0 := conj_eq_of_scalar hg (x * s * x⁻¹)
    have h1 := hvg s
    have e : g * s * g⁻¹ = x * s * x⁻¹ := by
      rw [← h0]
      calc g * s * g⁻¹ = g * x * (x * s * x⁻¹) * (g * x)⁻¹ := by
            rw [mul_inv_rev, hxi]
            calc g * s * g⁻¹ = g * (x * x) * s * (x * x) * g⁻¹ := by rw [hx2]; group
              _ = _ := by group
        _ = _ := rfl
    rw [← map_mul, ← map_inv, ← map_mul, e, map_mul, map_mul, map_inv] at h1
    have hψx : (ψ x)⁻¹ = ψ x := by rw [← map_inv, hxi]
    rw [hψx] at h1
    calc v * ψ x * ψ s = ψ x * (v * ψ s * v⁻¹) * v := by rw [hvx]; group
      _ = ψ x * (ψ x * ψ s * ψ x) * v := by rw [h1]
      _ = (ψ x * ψ x) * ψ s * (ψ x * v) := by group
      _ = ψ s * (v * ψ x) := by
        rw [← map_mul, hx2, map_one, one_mul, hvx]

end CFSG.ClassicalInvolution.NDB.SpinVertex
