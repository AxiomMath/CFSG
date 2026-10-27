module

public import CFSG.ClassicalInvolution.ModelFacts.Orth15Frame

public section

namespace CFSG.ClassicalInvolution.ModelFacts.Orth15

open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Orthogonal
  CFSG.ClassicalGroups.Orthogonal.Small CFSG.ClassicalInvolution.Asc77 QuadraticMap

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V] {Q : QuadraticForm F V}

section Eigen

variable (fr : Frame Q) {y : V ≃ₗ[F] V}

theorem map_mem_perp_of_fix (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hspan : ∀ x ∈ fr.span, y x = x) {p : V} (hp : p ∈ fr.perp) : y p ∈ fr.perp := by
  rw [Frame.mem_perp_iff_forall_incl] at hp ⊢
  intro Y
  have hY : y (fr.incl Y) = fr.incl Y := hspan _ ⟨Y, rfl⟩
  have h := polar_map_of_mem hyO p (fr.incl Y)
  rw [hY] at h
  rw [h]
  exact hp Y

theorem polar_minusSp_span (h2 : (2 : F) ≠ 0) (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hspan : ∀ x ∈ fr.span, y x = x) {r s : V} (hr : r ∈ minusSp y) (hs : s ∈ fr.span) :
    polar Q r s = 0 := by
  rw [polar_comm]
  exact polar_plusSp_minusSp h2 hyO (mem_plusSp.mpr (hspan s hs)) hr

theorem minusSp_le_perp (h2 : (2 : F) ≠ 0) (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hspan : ∀ x ∈ fr.span, y x = x) : minusSp y ≤ fr.perp := by
  intro r hr
  rw [Frame.mem_perp_iff_forall_incl]
  intro Y
  exact polar_minusSp_span fr h2 hyO hspan hr ⟨Y, rfl⟩

theorem exists_add_eq_perp (h2 : (2 : F) ≠ 0) (hyy : y * y = 1)
    (hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hspan : ∀ x ∈ fr.span, y x = x) {p : V}
    (hp : p ∈ fr.perp) : ∃ u ∈ plusSp y ⊓ fr.perp, ∃ r ∈ minusSp y, p = u + r := by
  obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_eq h2 hyy p
  refine ⟨u, ⟨hu, ?_⟩, r, hr, rfl⟩
  have hr' : r ∈ fr.perp := minusSp_le_perp fr h2 hyO hspan hr
  have := fr.perp.sub_mem hp hr'
  simpa using this

end Eigen

section Datum

variable [FiniteDimensional F V]

theorem kleinDatum_of_frame_involution (h2 : (2 : F) ≠ 0) (hQ : (polarBilin Q).Nondegenerate)
    (fr : Frame Q) {y : V ≃ₗ[F] V} (hy : y ∈ elementaryGroup Q) (hyy : y * y = 1)
    (hspan : ∀ x ∈ fr.span, y x = x) (hV : 7 ≤ Module.finrank F V) (hR : minusSp y ≠ ⊥)
    (hW : plusSp y ⊓ fr.perp ≠ ⊥) :
    KleinDatum Q fr.span (minusSp y) (plusSp y ⊓ fr.perp) (fr.La (-1)) y := by
  have hyO : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q := elementaryGroup_le_orthogonalGroup Q hy
  have hsp : PolarNondegOn Q fr.span :=
    polarNondegOn_of_isCompl hQ (Frame.isCompl_span_perp fr)
      (fun x hx y hy => polar_perp_of_mem_span fr hx hy)
  have hperp_dim : 3 ≤ Module.finrank F fr.perp := by
    have h := Submodule.finrank_add_eq_of_isCompl (Frame.isCompl_span_perp fr)
    rw [finrank_span_eq_four] at h
    omega
  have hperp_le : minusSp y ⊔ (plusSp y ⊓ fr.perp) = fr.perp := by
    refine le_antisymm (sup_le (minusSp_le_perp fr h2 hyO hspan) inf_le_right) fun p hp => ?_
    obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_eq_perp fr h2 hyy hyO hspan hp
    exact Submodule.add_mem_sup hr hu |> fun h => by rwa [add_comm] at h
  have hnd₂ : PolarNondegOn Q (minusSp y) :=
    polarNondegOn_of_isCompl hQ (isCompl_plusSp_minusSp h2 hyy).symm
      (fun x hx z hz => by rw [polar_comm]; exact polar_plusSp_minusSp h2 hyO hz hx)
  have hndW : PolarNondegOn Q (plusSp y ⊓ fr.perp) := by
    intro x hx hxx
    refine eq_zero_of_polar_eq_zero hQ fun v => ?_
    obtain ⟨s, hs, p, hp, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fr.span ⊔ fr.perp by rw [(Frame.isCompl_span_perp fr).sup_eq_top]; trivial)
    obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_eq_perp fr h2 hyy hyO hspan hp
    have h1 : polar Q x s = 0 := by rw [polar_comm]; exact polar_perp_of_mem_span fr hs hx.2
    have h2' : polar Q x u = 0 := hxx u hu
    have h3 : polar Q x r = 0 := by
      rw [polar_comm]
      exact polar_plusSp_minusSp h2 hyO hx.1 hr |> fun h => by rw [polar_comm] at h; exact h
    rw [polar_add_right, polar_add_right, h1, h2', h3]
    ring
  have hspan_ne : fr.span ≠ ⊥ := by
    intro h
    have := finrank_span_eq_four fr
    rw [h, finrank_bot] at this
    omega
  refine
    { nd₁ := hsp
      nd₂ := hnd₂
      ndW := hndW
      o₁₂ := fun x hx r hr => by rw [polar_comm]; exact polar_minusSp_span fr h2 hyO hspan hr hx
      o₁W := fun x hx w hw => polar_perp_of_mem_span fr hx hw.2
      o₂W := fun r hr w hw => by
        rw [polar_comm]
        exact polar_plusSp_minusSp h2 hyO hw.1 hr
      top := ?_
      neg₁ := fun x hx => La_neg_one_of_mem_span fr hx
      fix₁ := fun x hx => ?_
      neg₂ := fun x hx => mem_minusSp.mp hx
      fix₂ := fun x hx => ?_
      mem₁ := fr.La_mem_elementaryGroup (-1)
      mem₂ := hy
      ne₁ := hspan_ne
      ne₂ := hR
      neW := hW
      d₁₂ := ?_
      d₁W := ?_
      d₂W := ?_
      gen := Or.inl (by rw [finrank_span_eq_four]; omega) }
  ·
    rw [eq_top_iff]
    intro v _
    obtain ⟨s, hs, p, hp, rfl⟩ := Submodule.mem_sup.mp
      (show v ∈ fr.span ⊔ fr.perp by rw [(Frame.isCompl_span_perp fr).sup_eq_top]; trivial)
    obtain ⟨u, hu, r, hr, rfl⟩ := exists_add_eq_perp fr h2 hyy hyO hspan hp
    have e : s + (u + r) = s + r + u := by abel
    rw [e]
    exact Submodule.add_mem _ (Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.mem_sup_left hs)) (Submodule.mem_sup_left
        (Submodule.mem_sup_right hr)) |> fun h => by simpa using h)
      (Submodule.mem_sup_right hu)
  ·
    obtain ⟨r, hr, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, La_neg_one_of_mem_perp fr (minusSp_le_perp fr h2 hyO hspan hr),
      La_neg_one_of_mem_perp fr hw.2]
  ·
    obtain ⟨s, hs, w, hw, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add, hspan s hs, mem_plusSp.mp hw.1]
  · exact (by rw [finrank_span_eq_four]; omega : 3 ≤ Module.finrank F fr.span).trans
      (Submodule.finrank_mono le_sup_left)
  · exact (by rw [finrank_span_eq_four]; omega : 3 ≤ Module.finrank F fr.span).trans
      (Submodule.finrank_mono le_sup_left)
  · rw [hperp_le]
    exact hperp_dim

end Datum

section Main

variable [Finite F] [FiniteDimensional F V]

theorem alphaOf_frame_klein_eq_bot (hodd : Odd (Nat.card F)) (h5 : 5 ≤ Nat.card F)
    (hQ : (polarBilin Q).Nondegenerate) (fr : Frame Q) {y : V ≃ₗ[F] V}
    (hy : y ∈ elementaryGroup Q) (hyy : y * y = 1) (hspan : ∀ x ∈ fr.span, y x = x)
    (hV : 7 ≤ Module.finrank F V) (hR : minusSp y ≠ ⊥) (hW : plusSp y ⊓ fr.perp ≠ ⊥)
    {X : Type} [Group X] [Finite X] (e : ↥(elementaryGroup Q) →* X) (hker : KerScalar Q e)
    [e.range.Normal] (hcent : ∀ x : X, (∀ z ∈ e.range, x * z = z * x) → x = 1) :
    alphaOf (Subgroup.closure ({e ⟨fr.La (-1), fr.La_mem_elementaryGroup (-1)⟩, e ⟨y, hy⟩} :
      Set X)) = ⊥ := by
  have h2 := two_ne_zero_of_odd_card hodd
  have T := kleinDatum_of_frame_involution h2 hQ fr hy hyy hspan hV hR hW
  exact alphaOf_klein_eq_bot hodd h5 hQ T e hker hcent

end Main

end CFSG.ClassicalInvolution.ModelFacts.Orth15
