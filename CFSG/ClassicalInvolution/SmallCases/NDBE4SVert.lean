module

public import CFSG.ClassicalInvolution.SmallCases.NDBE4SCore

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

omit [DecidableEq ι] in
theorem klein_trichotomy (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) {y : (ι → F) ≃ₗ[F] (ι → F)}
    (hy : y ∈ elementaryGroup Q) (hyy : y * y = 1) (hspan : ∀ x ∈ fr.span, y x = x)
    (hV : 7 ≤ Module.finrank F (ι → F)) {X : Type} [Group X] [Finite X]
    (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e) [e.range.Normal]
    (hcent : ∀ x : X, (∀ z ∈ e.range, x * z = z * x) → x = 1) :
    alphaOf (Subgroup.closure ({e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩, e ⟨y, hy⟩} :
      Set X)) = ⊥ ∨ y = 1 ∨ y * fr.La (-1) = LinearEquiv.neg F := by
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  by_cases hR : minusSp y = ⊥
  · exact Or.inr (Or.inl (eq_one_of_minusSp_eq_bot h2 hyy hR))
  by_cases hW : plusSp y ⊓ fr.perp = ⊥
  · exact Or.inr (Or.inr (mul_La_neg_one_eq_neg h2 fr
      (elementaryGroup_le_orthogonalGroup Q hy) hyy hspan hW))
  exact Or.inl (alphaOf_frame_klein_eq_bot hodd h5 hQ fr hy hyy hspan hV hR hW e hker hcent)

theorem closure_pair_mul {G : Type*} [Group G] (a b : G) :
    Subgroup.closure ({a, b * a} : Set G) = Subgroup.closure ({a, b} : Set G) := by
  have ha : ∀ {S : Subgroup G}, a ∈ S → b * a ∈ S → b ∈ S := fun {S} ha hba => by
    have := S.mul_mem hba (S.inv_mem ha)
    rwa [mul_inv_cancel_right] at this
  refine le_antisymm ?_ ?_
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))
        (Subgroup.subset_closure (Set.mem_insert _ _))
  · rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact ha (Subgroup.subset_closure (Set.mem_insert _ _))
        (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl))

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem neg_mem_scalars : (LinearEquiv.neg F : (ι → F) ≃ₗ[F] (ι → F)) ∈ scalars F (ι → F) :=
  mem_scalars.mpr ⟨-1, fun x => by simp⟩

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem comm_La_neg_one (fr : Frame Q) {w : (ι → F) ≃ₗ[F] (ι → F)}
    (hwiso : w ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hwspan : ∀ y ∈ fr.span, w y = y) :
    w * fr.La (-1) = fr.La (-1) * w := by
  refine LinearEquiv.ext fun y => ?_
  obtain ⟨s, hs, t, ht, rfl⟩ := exists_decomp fr y
  have hwt : w t ∈ fr.perp := map_mem_perp_of_fix fr hwiso hwspan ht
  simp only [LinearEquiv.mul_apply, map_add, La_neg_one_of_mem_span fr hs,
    La_neg_one_of_mem_perp fr ht, map_neg, hwspan s hs, La_neg_one_of_mem_perp fr hwt]

omit [Fintype ι] [DecidableEq ι] [Finite F] in
theorem toInducedAutOn_eq {ψ : spinGroup Q →* H} {v : H}
    (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) {g : spinGroup Q}
    (hg : ∀ s, v * ψ s * v⁻¹ = ψ g * ψ s * (ψ g)⁻¹) :
    toInducedAutOn ψ.range ⟨v, hv⟩ = toInducedAutOn ψ.range ⟨ψ g, mem_normalizer_range ψ g⟩ := by
  apply Subtype.ext
  refine MulEquiv.ext fun ℓ => Subtype.ext ?_
  obtain ⟨s, hs⟩ := ℓ.2
  show v * ↑ℓ * v⁻¹ = ψ g * ↑ℓ * (ψ g)⁻¹
  rw [← hs]
  exact hg s

theorem vertex (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (hrange : (spinAction Q).range = elementaryGroup Q)
    [Group.IsPerfect (spinGroup Q)] (fr : Frame Q) (hV : 7 ≤ Module.finrank F (ι → F))
    [Finite H] {ψ : spinGroup Q →* H} (hψ : ψ.ker ≤ Subgroup.center (spinGroup Q))
    (hlift : LiftSim Q ψ) {R R' : Subgroup (spinGroup Q)}
    (hRfr : R.map (spinAction Q) = fr.La.range) (hR'fr : R'.map (spinAction Q) = fr.swap.La.range)
    {x : spinGroup Q} (hxR : x ∈ R) (hx : spinAction Q x = fr.La (-1)) (hx2 : x * x = 1)
    {v : H} (hv : v ∈ Subgroup.normalizer (ψ.range : Set H)) (hv2 : v * v = 1)
    (hvR : ∀ r ∈ R, v * ψ r = ψ r * v) (hvR' : ∀ r ∈ R', v * ψ r = ψ r * v) :
    ((Subgroup.centralizer ({v} : Set H)).comap ψ ⊔
        (Subgroup.centralizer ({v * ψ x} : Set H)).comap ψ = ⊤) ∧
      ((∀ y ∈ ψ.range, v * y = y * v) ∨ (∀ y ∈ ψ.range, v * ψ x * y = y * (v * ψ x)) ∨
        alphaOf (Subgroup.closure ({toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩,
          toInducedAutOn ψ.range ⟨v, hv⟩} : Set ↥(inducedAutOn ψ.range))) = ⊥ ∨
        ∀ y : spinGroup Q, toInducedAutOn ψ.range ⟨v, hv⟩ ≠
          toInducedAutOn ψ.range ⟨ψ y, mem_normalizer_range ψ y⟩) := by
  classical
  have h2 : (2 : F) ≠ 0 := two_ne_zero_of_odd_card hodd
  set θ := spinAction Q with hθ
  have hker : θ.ker ≤ Subgroup.center (spinGroup Q) := ker_spinAction_le_center Q
  have hE : ∀ s, θ s ∈ elementaryGroup Q := fun s => hrange ▸ ⟨s, rfl⟩
  obtain ⟨α, w, hα', -, hwiso, hwspan, hθw, hw2⟩ :=
    exists_lift hodd h5 hQ hrange fr hV hψ hlift hRfr hR'fr hv hv2 hvR hvR'
  refine ⟨top_le_comap hodd h5 hQ hrange fr hx hα' hwiso hwspan hθw hw2, ?_⟩
  rw [← hθ] at hθw
  obtain ⟨e, he, hkerE, hnorm, hcent⟩ := exists_hom_spin hodd hQ (by omega) hrange ψ hψ
  have := hnorm
  have hvx : v * ψ x = ψ x * v := hvR x hxR
  have hzE : fr.La (-1) ∈ elementaryGroup Q := fr.La_mem_elementaryGroup (-1)
  have hez : e ⟨fr.La (-1), hzE⟩ = toInducedAutOn ψ.range ⟨ψ x, mem_normalizer_range ψ x⟩ := by
    rw [← he x (hE x)]
    congr 1
    exact Subtype.ext hx.symm
  have hwz := comm_La_neg_one fr hwiso hwspan
  have hneg := neg_mem_scalars (ι := ι) (F := F)
  have hconj : ∀ (β : spinGroup Q →* spinGroup Q) (g : spinGroup Q),
      (∀ s, θ (β s) = θ g * θ s * (θ g)⁻¹) → ∀ s, β s = g * s * g⁻¹ := by
    intro β g hβ s
    have key := OrthAut.eq_of_inv_mul_mem_center β (MulAut.conj g).toMonoidHom (fun s => by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        hβ, map_mul, map_mul, map_inv]
      group)
    have := DFunLike.congr_fun key s
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    exact this.symm
  have hvxx : v * ψ x * ψ x = v := by rw [mul_assoc, ← map_mul, hx2, map_one, mul_one]
  by_cases hwE : w ∈ elementaryGroup Q
  ·
    obtain ⟨ŵ, hŵ⟩ : w ∈ θ.range := hrange ▸ hwE
    have hαc := hconj (α : spinGroup Q →* spinGroup Q) ŵ (fun s => by
      show θ (α s) = θ ŵ * θ s * (θ ŵ)⁻¹
      rw [hθw, hŵ])
    have hvg : ∀ s, v * ψ s * v⁻¹ = ψ ŵ * ψ s * (ψ ŵ)⁻¹ := fun s => by
      rw [← hα', show (α s : spinGroup Q) = (α : spinGroup Q →* spinGroup Q) s from rfl, hαc s,
        map_mul, map_mul, map_inv]
    have hvI : toInducedAutOn ψ.range ⟨v, hv⟩ = e ⟨w, hwE⟩ := by
      rw [toInducedAutOn_eq hv hvg, ← he ŵ (hE ŵ)]
      congr 1
      exact Subtype.ext hŵ
    have hcen := centralizes_of_inner hvg hx2 hvx
    rcases klein_trichotomy hodd h5 hQ fr hwE hw2 hwspan hV e hkerE hcent with hα | h1 | hneg'
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [← hez, hvI]
      exact hα
    · exact Or.inl (hcen.1 (by rw [hŵ, h1]; exact Subgroup.one_mem _))
    · exact Or.inr (Or.inl (hcen.2 (by rw [map_mul, hŵ, hx, hneg']; exact hneg)))
  set w' := LinearEquiv.neg F * (w * fr.La (-1)) with hw'
  have hncomm : ∀ g : (ι → F) ≃ₗ[F] (ι → F), LinearEquiv.neg F * g = g * LinearEquiv.neg F :=
    commute_of_mem_scalars hneg
  by_cases hw'E : w' ∈ elementaryGroup Q
  ·
    obtain ⟨ŵ', hŵ'⟩ : w' ∈ θ.range := hrange ▸ hw'E
    have e1 : ∀ g : (ι → F) ≃ₗ[F] (ι → F), LinearEquiv.neg F * g * (LinearEquiv.neg F)⁻¹ = g :=
      fun g => by rw [hncomm, mul_assoc, mul_inv_cancel, mul_one]
    have hβc := hconj ((α : spinGroup Q →* spinGroup Q).comp (MulAut.conj x).toMonoidHom) ŵ'
      (fun s => by
        show θ (α (x * s * x⁻¹)) = θ ŵ' * θ s * (θ ŵ')⁻¹
        rw [hθw, map_mul, map_mul, map_inv, hx, hŵ', hw',
          show LinearEquiv.neg F * (w * fr.La (-1)) * θ s * (LinearEquiv.neg F * (w * fr.La (-1)))⁻¹
            = LinearEquiv.neg F * ((w * fr.La (-1)) * θ s * (w * fr.La (-1))⁻¹) *
              (LinearEquiv.neg F)⁻¹ by group, e1]
        group)
    have hvg : ∀ s, v * ψ x * ψ s * (v * ψ x)⁻¹ = ψ ŵ' * ψ s * (ψ ŵ')⁻¹ := fun s => by
      have h1 := hα' (x * s * x⁻¹)
      rw [show α (x * s * x⁻¹) = ((α : spinGroup Q →* spinGroup Q).comp
        (MulAut.conj x).toMonoidHom) s from rfl, hβc s, map_mul, map_mul, map_inv, map_mul,
        map_mul, map_inv] at h1
      calc v * ψ x * ψ s * (v * ψ x)⁻¹ = v * (ψ x * ψ s * (ψ x)⁻¹) * v⁻¹ := by group
        _ = ψ ŵ' * ψ s * (ψ ŵ')⁻¹ := h1.symm
    have hv'N : v * ψ x ∈ Subgroup.normalizer (ψ.range : Set H) :=
      mul_mem hv (mem_normalizer_range ψ x)
    have hvI : toInducedAutOn ψ.range ⟨v * ψ x, hv'N⟩ = e ⟨w', hw'E⟩ := by
      rw [toInducedAutOn_eq hv'N hvg, ← he ŵ' (hE ŵ')]
      congr 1
      exact Subtype.ext hŵ'
    have hvx' : v * ψ x * ψ x = ψ x * (v * ψ x) := by rw [hvxx, ← mul_assoc, ← hvx, hvxx]
    have hcen := centralizes_of_inner hvg hx2 hvx'
    have hw'span : ∀ y ∈ fr.span, w' y = y := fun y hy => by
      rw [hw', LinearEquiv.mul_apply, LinearEquiv.mul_apply, La_neg_one_of_mem_span fr hy, map_neg,
        hwspan y hy]
      simp
    have hw'2 : w' * w' = 1 := by
      rw [hw', show LinearEquiv.neg F * (w * fr.La (-1)) * (LinearEquiv.neg F * (w * fr.La (-1))) =
          (LinearEquiv.neg F * LinearEquiv.neg F) * (w * (fr.La (-1) * w) * fr.La (-1)) by
        rw [mul_assoc (LinearEquiv.neg F), ← mul_assoc (w * fr.La (-1)), ← hncomm]
        group, ← hwz]
      have hn : LinearEquiv.neg F * LinearEquiv.neg F = (1 : (ι → F) ≃ₗ[F] (ι → F)) := by
        ext y
        simp
      rw [hn, one_mul, show w * (w * fr.La (-1)) * fr.La (-1) = (w * w) * (fr.La (-1) *
        fr.La (-1)) by group, hw2, fr.La_neg_one_mul_self, one_mul]
    rcases klein_trichotomy hodd h5 hQ fr hw'E hw'2 hw'span hV e hkerE hcent with hα | h1 | hneg'
    · refine Or.inr (Or.inr (Or.inl ?_))
      rw [← closure_pair_mul, ← map_mul, show (⟨v, hv⟩ * ⟨ψ x, mem_normalizer_range ψ x⟩ :
        ↥(Subgroup.normalizer (ψ.range : Set H))) = ⟨v * ψ x, hv'N⟩ from rfl, hvI, ← hez]
      exact hα
    · exact Or.inr (Or.inl (hcen.1 (by rw [hŵ', h1]; exact Subgroup.one_mem _)))
    · have h3 := hcen.2 (by rw [map_mul, hŵ', hx, hneg']; exact hneg)
      rw [hvxx] at h3
      exact Or.inl h3
  refine Or.inr (Or.inr (Or.inr fun y hy => ?_))
  have hvy : ∀ s, v * ψ s * v⁻¹ = ψ y * ψ s * (ψ y)⁻¹ := fun s => by
    have h1 := congrArg (fun φ : ↥(inducedAutOn ψ.range) =>
      (((φ : MulAut ↥ψ.range) ⟨ψ s, s, rfl⟩ : ↥ψ.range) : H)) hy
    exact h1
  have key := OrthAut.eq_of_inv_mul_mem_center (α : spinGroup Q →* spinGroup Q)
    (MulAut.conj y).toMonoidHom (fun s => hψ (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        show ((α : spinGroup Q →* spinGroup Q) s) = α s from rfl, hα', map_mul, map_mul, map_inv,
        hvy]
      group))
  have hαy : ∀ s, α s = y * s * y⁻¹ := fun s => by
    have := DFunLike.congr_fun key s
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    exact this.symm
  have hcomm : ∀ s, ((θ y)⁻¹ * w) * θ s = θ s * ((θ y)⁻¹ * w) := fun s => by
    have h1 := hθw s
    rw [hαy, map_mul, map_mul, map_inv] at h1
    calc (θ y)⁻¹ * w * θ s = (θ y)⁻¹ * (w * θ s * w⁻¹) * w := by group
      _ = (θ y)⁻¹ * (θ y * θ s * (θ y)⁻¹) * w := by rw [h1]
      _ = θ s * ((θ y)⁻¹ * w) := by group
  have hO : ∀ s, θ s ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun s =>
    elementaryGroup_le_orthogonalGroup Q (hE s)
  have hνO : (θ y)⁻¹ * w ∈ TauCeti.QuadraticMap.orthogonalGroup Q := mul_mem (inv_mem (hO y)) hwiso
  have hA := hasAnisoPerp_of_three_le_finrank hQ (by omega : 3 ≤ Module.finrank F (ι → F))
  obtain ⟨P, -, -⟩ := exists_hypPair_le hodd (polarNondegOn_top hQ) (by
    rw [finrank_top]
    omega)
  have hsc := mem_scalars_of_commute_eichler h2 hQ hA P hνO (fun u w'' _ _ => by
    obtain ⟨s, hs⟩ : eichler Q u w'' ∈ θ.range := hrange ▸ eichler_mem_elementaryGroup Q u w''
    rw [← hs]
    exact hcomm s)
  obtain ⟨c, hc⟩ := mem_scalars.mp hsc
  have hQa : Q (fr.incl 1) = 1 := by rw [Frame.Q_incl, Matrix.det_one]
  have hcc : c * c = 1 := by
    have h1 := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hνO (fr.incl 1)
    rw [hc, QuadraticMap.map_smul, hQa, smul_eq_mul, mul_one] at h1
    exact h1
  rcases mul_self_eq_one_iff.mp hcc with rfl | rfl
  · apply hwE
    have hw : w = θ y := by
      refine LinearEquiv.ext fun u => ?_
      have h2' : (θ y)⁻¹ (w u) = u := by
        have := hc u
        rwa [one_smul, LinearEquiv.mul_apply] at this
      calc w u = (θ y) ((θ y)⁻¹ (w u)) := by rw [LinearEquiv.apply_inv_apply']
        _ = (θ y) u := by rw [h2']
    rw [hw]
    exact hE y
  · apply hw'E
    have hw : w = θ y * LinearEquiv.neg F := by
      refine LinearEquiv.ext fun u => ?_
      have h2' : (θ y)⁻¹ (w u) = -u := by
        have := hc u
        rwa [neg_one_smul, LinearEquiv.mul_apply] at this
      calc w u = (θ y) ((θ y)⁻¹ (w u)) := by rw [LinearEquiv.apply_inv_apply']
        _ = (θ y) (-u) := by rw [h2']
        _ = ((θ y * LinearEquiv.neg F : (ι → F) ≃ₗ[F] (ι → F))) u := by
          rw [LinearEquiv.mul_apply]
          rfl
    have hn : LinearEquiv.neg F * LinearEquiv.neg F = (1 : (ι → F) ≃ₗ[F] (ι → F)) := by
      ext u
      simp
    have hw'' : w' = θ (y * x) := by
      rw [hw', hw, map_mul, hx, ← mul_assoc, ← mul_assoc, hncomm, mul_assoc (θ y), hn, mul_one]
    rw [hw'']
    exact hE _

end CFSG.ClassicalInvolution.NDB.SpinVertex
