module

public import CFSG.LieType.SeitzGeneration.ExcOuterLeOne.EntryLemma

open CFSG.RankThree.PartOne.CTP
open CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley
open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne



section EntryF2

variable {τ : Tag} {K : Type} [Field K]

private abbrev spanF2Long : Fin Tag.F4.rank := ⟨1, by decide⟩

private abbrev spanF2Short : Fin Tag.F4.rank := ⟨2, by decide⟩

private theorem spanF2_norm_long : rootNorm Tag.F4 (Pi.single spanF2Long 1) = 4 := by
  decide +kernel

private theorem spanF2_norm_short : rootNorm Tag.F4 (Pi.single spanF2Short 1) = 2 := by
  decide +kernel

private theorem spanF2_rootNorm_F4 {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) :
    rootNorm Tag.F4 γ = 2 ∨ rootNorm Tag.F4 γ = 4 := by
  induction hγ with
  | basis j => revert j; decide +kernel
  | reflect i hv ih => rw [rootNorm_reflect]; exact ih

private theorem spanF2_rootNorm_E (hE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {γ : Fin τ.rank → ℤ}
    (hγ : IsRoot τ γ) : rootNorm τ γ = 2 := by
  induction hγ with
  | basis j => rcases hE with rfl | rfl | rfl <;> revert j <;> decide +kernel
  | reflect i hv ih => rw [rootNorm_reflect, ih]

theorem span_orbit_eq_top_f2 (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Subfield K}
    (hk : Nat.card k = 2) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) :
    Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} = ⊤ := by
  classical
  set S := Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} with hS
  have hw : ∀ i : Fin τ.rank,
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily τ)) i (1 : Kˣ) ∈ R :=
    weylElement_one_mem_of_rat k R hrat
  have hRinv : ∀ r ∈ R, ∀ v ∈ S, endHom K r v ∈ S := by
    intro r hr v hv
    refine Submodule.span_induction (p := fun v _ => endHom K r v ∈ S) ?_ ?_ ?_ ?_ hv
    · rintro _ ⟨r', hr', rfl⟩
      exact Submodule.subset_span ⟨r * r', R.mul_mem hr hr', by rw [map_mul]; rfl⟩
    · simp
    · intro x y _ _ hx hy
      rw [map_add]
      exact S.add_mem hx hy
    · intro a x _ hx
      rw [map_smul]
      exact S.smul_mem a hx
  have transfer : ∀ {γ δ : Fin τ.rank → ℤ}, IsRoot τ γ → IsRoot τ δ →
      rootNorm τ γ = rootNorm τ δ → rootVec τ K γ ∈ S → rootVec τ K δ ∈ S := by
    intro γ δ hγ hδ hn hγS
    obtain ⟨r, hr, ε, hε, hv, -⟩ := exists_weyl_move hτ hw hγ hδ hn
    have hεε : ((ε : ℤ) : K) * ((ε : ℤ) : K) = 1 := by
      rcases hε with rfl | rfl <;> simp
    have e : rootVec τ K δ = ((ε : ℤ) : K) • endHom K r (rootVec τ K γ) := by
      rw [hv, smul_smul, hεε, one_smul]
    rw [e]
    exact S.smul_mem _ (hRinv r hr _ hγS)
  have hθS : rootVec τ K θ ∈ S := Submodule.subset_span ⟨1, R.one_mem, by simp⟩
  have hsame : ∀ γ, IsRoot τ γ → rootNorm τ γ = rootNorm τ θ → rootVec τ K γ ∈ S :=
    fun γ hγ hn => transfer hθ.1 hγ hn.symm hθS
  have hcart_of : ∀ i : Fin τ.rank, rootVec τ K (-Pi.single i 1) ∈ S →
      rootVec τ K (Pi.single i 1) ∈ S → hVec τ K i ∈ S := by
    intro i h1 h2
    have hxr : xPar (rootOperatorFamily τ) (Pi.single i 1) (1 : K) ∈ R :=
      hrat _ (isRoot_single τ i) 1 k.one_mem
    have h4 := hRinv _ hxr _ h1
    have e : endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) (1 : K)) = xOp τ K i 1 := by
      rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
    rw [e, CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single] at h4
    have h5 := S.sub_mem (S.sub_mem h4 h1) h2
    convert h5 using 1
    module
  have hroot : ∀ β, IsRoot τ β → rootVec τ K β ∈ S := by
    by_cases hF : τ = .F4
    · subst hF
      have hθ4 : rootNorm Tag.F4 θ = 4 := hθ.rootNorm_F4
      have hL : rootVec Tag.F4 K (Pi.single spanF2Long 1) ∈ S :=
        hsame _ (isRoot_single Tag.F4 spanF2Long) (by rw [spanF2_norm_long, hθ4])
      have hLn : rootVec Tag.F4 K (-Pi.single spanF2Long 1) ∈ S :=
        hsame _ (isRoot_neg_single Tag.F4 spanF2Long)
          (by rw [rootNorm_neg, spanF2_norm_long, hθ4])
      have hh1 : hVec Tag.F4 K spanF2Long ∈ S := hcart_of spanF2Long hLn hL
      have hc : (Tag.F4.cartan spanF2Long spanF2Short).natAbs = 1 := by decide +kernel
      have hS2 : rootVec Tag.F4 K (Pi.single spanF2Short 1) ∈ S := by
        have hx2 : xPar (rootOperatorFamily Tag.F4) (Pi.single spanF2Short 1) (1 : K) ∈ R :=
          hrat _ (isRoot_single Tag.F4 spanF2Short) 1 k.one_mem
        have e : endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single spanF2Short 1) (1 : K)) =
            xOp Tag.F4 K spanF2Short 1 := by
          rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.F4).elt_simple]
        have h1 := hRinv _ hx2 _ hh1
        rw [e, xOp_apply_hVec, hc] at h1
        have h2 := S.sub_mem h1 hh1
        convert h2 using 1
        simp
      have hshort : ∀ β, IsRoot Tag.F4 β → rootNorm Tag.F4 β = 2 → rootVec Tag.F4 K β ∈ S :=
        fun β hβ hn => transfer (isRoot_single Tag.F4 spanF2Short) hβ
          (by rw [spanF2_norm_short, hn]) hS2
      intro β hβ
      rcases spanF2_rootNorm_F4 hβ with h | h
      · exact hshort β hβ h
      · exact hsame β hβ (by rw [h, hθ4])
    · have hE : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 := by
        rcases hτ with h | h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr h)
        · exact absurd h hF
      intro β hβ
      exact hsame β hβ (by rw [spanF2_rootNorm_E hE hβ, spanF2_rootNorm_E hE hθ.1])
  have hcart : ∀ i : Fin τ.rank, hVec τ K i ∈ S := fun i =>
    hcart_of i (hroot _ (isRoot_neg_single τ i)) (hroot _ (isRoot_single τ i))
  rw [eq_top_iff, ← (Finsupp.basisSingleOne (R := K) (ι := Label τ)).span_eq]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨b, rfl⟩
  rw [Finsupp.coe_basisSingleOne]
  rcases b with i | ⟨β, hβ⟩
  · exact hcart i
  · have := hroot β hβ
    rwa [rootVec_of_isRoot' hβ] at this

private theorem f2E_rootCoord (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Subfield K}
    {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) {z : RootModule τ K}
    (hz : z ∈ vanishSub R (negLabel hθ.1)) {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hn : rootNorm τ β = rootNorm τ θ) : z (rootLabel hβ) = 0 := by
  have hτ4 : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4 := by
    rcases hτ with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
  have hw := weylElement_one_mem_of_rat k R hrat
  obtain ⟨r, hr, ε, hε, -, hcoord⟩ := exists_weyl_move hτ4 hw hβ (isRoot_neg_iff.2 hθ.1)
    (hn.trans (rootNorm_neg θ).symm)
  have h0 := mem_vanishSub.1 hz r hr
  rw [hcoord z] at h0
  rcases hε with rfl | rfl <;> simpa using h0

private theorem f2E_cartan_eq {z : RootModule τ K}
    (hz : ∀ (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β), z (rootLabel hβ) = 0) :
    z = ∑ j : Fin τ.rank, z (Sum.inl j) • hVec τ K j := by
  classical
  ext a
  rcases a with j | ⟨β, hβ⟩
  · simp [hVec, Finsupp.finset_sum_apply, Finsupp.single_apply]
  · have h : z (Sum.inr ⟨β, hβ⟩) = 0 := hz β hβ
    simp [hVec, Finsupp.finset_sum_apply, Finsupp.single_apply, h]

private theorem f2E_fix_of_coord (op : K → Module.End K (RootModule τ K)) (A : Fin τ.rank → K)
    {β : Fin τ.rank → ℤ} (hβ : IsRoot τ β) {z : RootModule τ K}
    (hdec : z = ∑ j : Fin τ.rank, z (Sum.inl j) • hVec τ K j)
    (hop : ∀ (c : K) (j : Fin τ.rank), op c (hVec τ K j) = hVec τ K j + (A j * c) • rootVec τ K β)
    (hw0 : (op 1 z - z) (rootLabel hβ) = 0) (c : K) : op c z = z := by
  have hsum : ∀ (t : Fin τ.rank → K) (c : K), op c (∑ j, t j • hVec τ K j) =
      (∑ j, t j • hVec τ K j) + (∑ j, t j * (A j * c)) • rootVec τ K β := by
    intro t c
    simp only [map_sum, map_smul, hop, smul_add, smul_smul, Finset.sum_add_distrib, Finset.sum_smul]
  have hopz : ∀ c : K, op c z = z + (∑ j, z (Sum.inl j) * (A j * c)) • rootVec τ K β := by
    intro c
    have h : op c (∑ j, z (Sum.inl j) • hVec τ K j) = (∑ j, z (Sum.inl j) • hVec τ K j) +
        (∑ j, z (Sum.inl j) * (A j * c)) • rootVec τ K β := hsum (fun j => z (Sum.inl j)) c
    rw [← hdec] at h
    exact h
  have hT : ∀ c : K, (∑ j, z (Sum.inl j) * (A j * c)) = (∑ j, z (Sum.inl j) * (A j * 1)) * c := by
    intro c
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hT1 : (∑ j, z (Sum.inl j) * (A j * 1)) = 0 := by
    have h1 : op 1 z - z = (∑ j, z (Sum.inl j) * (A j * 1)) • rootVec τ K β := by
      rw [hopz 1]
      abel
    rw [h1, rootVec_of_isRoot' hβ] at hw0
    simpa using hw0
  rw [hopz c, hT c, hT1, zero_mul, zero_smul, add_zero]

theorem vanishSub_le_top_f2_E (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {k : Subfield K}
    (hk : Nat.card k = 2) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) :
    vanishSub R (negLabel hθ.1) ≤ vanishSub (⊤ : Subgroup ↥(adjointGroup τ K)) (negLabel hθ.1) := by
  intro z hz
  have hroot : ∀ (β : Fin τ.rank → ℤ) (hβ : IsRoot τ β), z (rootLabel hβ) = 0 := fun β hβ =>
    f2E_rootCoord hτ hrat hθ hz hβ ((spanF2_rootNorm_E hτ hβ).trans (spanF2_rootNorm_E hτ hθ.1).symm)
  have hdec : z = ∑ j : Fin τ.rank, z (Sum.inl j) • hVec τ K j := f2E_cartan_eq (z := z) hroot
  have hRinv : ∀ r' ∈ R, endHom K r' z ∈ vanishSub R (negLabel hθ.1) := by
    intro r' hr'
    refine mem_vanishSub.2 fun r hr => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact mem_vanishSub.1 hz (r * r') (R.mul_mem hr hr')
  have hxz : ∀ i : Fin τ.rank, xOp τ K i 1 z ∈ vanishSub R (negLabel hθ.1) := by
    intro i
    have he : endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) (1 : K)) = xOp τ K i 1 := by
      rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
    rw [← he]
    exact hRinv _ (hrat _ (isRoot_single τ i) 1 k.one_mem)
  have hyz : ∀ i : Fin τ.rank, yOp τ K i 1 z ∈ vanishSub R (negLabel hθ.1) := by
    intro i
    have he : endHom K (xPar (rootOperatorFamily τ) (-Pi.single i 1) (1 : K)) = yOp τ K i 1 := by
      rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily τ).elt_neg_simple]
    rw [← he]
    exact hRinv _ (hrat _ (isRoot_neg_single τ i) 1 k.one_mem)
  have hxfix : ∀ (i : Fin τ.rank) (c : K), xOp τ K i c z = z := by
    intro i c
    have hw : xOp τ K i 1 z - z ∈ vanishSub R (negLabel hθ.1) := Submodule.sub_mem _ (hxz i) hz
    refine f2E_fix_of_coord (fun c => xOp τ K i c) (fun j => ((τ.cartan j i).natAbs : K))
      (isRoot_single τ i) hdec (fun c j => xOp_apply_hVec i j c) ?_ c
    exact f2E_rootCoord hτ hrat hθ hw (isRoot_single τ i)
      ((spanF2_rootNorm_E hτ (isRoot_single τ i)).trans (spanF2_rootNorm_E hτ hθ.1).symm)
  have hyfix : ∀ (i : Fin τ.rank) (c : K), yOp τ K i c z = z := by
    intro i c
    have hw : yOp τ K i 1 z - z ∈ vanishSub R (negLabel hθ.1) := Submodule.sub_mem _ (hyz i) hz
    refine f2E_fix_of_coord (fun c => yOp τ K i c) (fun j => ((τ.cartan j i).natAbs : K))
      (isRoot_neg_single τ i) hdec (fun c j => yOp_apply_hVec i j c) ?_ c
    exact f2E_rootCoord hτ hrat hθ hw (isRoot_neg_single τ i)
      ((spanF2_rootNorm_E hτ (isRoot_neg_single τ i)).trans (spanF2_rootNorm_E hτ hθ.1).symm)
  have hall : ∀ g : ↥(adjointGroup τ K), endHom K g z = z := by
    let Stab : Subgroup ↥(adjointGroup τ K) :=
      { carrier := {g | endHom K g z = z}
        one_mem' := by
          show endHom K 1 z = z
          rw [map_one, Module.End.one_apply]
        mul_mem' := fun {g₁ g₂} h1 h2 => by
          show endHom K (g₁ * g₂) z = z
          have h1' : endHom K g₁ z = z := h1
          have h2' : endHom K g₂ z = z := h2
          rw [map_mul, Module.End.mul_apply, h2', h1']
        inv_mem' := fun {g} h => by
          have h' : endHom K g z = z := h
          show endHom K g⁻¹ z = z
          calc endHom K g⁻¹ z = endHom K g⁻¹ (endHom K g z) := by rw [h']
            _ = z := by
              rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have htop : Stab = ⊤ := by
      set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
        (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
          (g : Module.End K (RootModule τ K)) = yOp τ K i c} with hS
      have hcl : Subgroup.closure (((↑) : ↥(adjointGroup τ K) → ModGL τ K) ⁻¹' S) = ⊤ :=
        Subgroup.closure_closure_coe_preimage
      rw [eq_top_iff, ← hcl, Subgroup.closure_le]
      rintro g ⟨i, c, hg | hg⟩
      · show endHom K g z = z
        rw [show endHom K g = xOp τ K i c from hg]
        exact hxfix i c
      · show endHom K g z = z
        rw [show endHom K g = yOp τ K i c from hg]
        exact hyfix i c
    intro g
    have hg : g ∈ Stab := by
      rw [htop]
      exact Subgroup.mem_top g
    exact hg
  rw [mem_vanishSub]
  intro g _
  rw [hall g]
  have h0 := mem_vanishSub.1 hz 1 R.one_mem
  rw [map_one, Module.End.one_apply] at h0
  exact h0

private theorem f4_two_eq_zero {k : Subfield K} (hk : Nat.card k = 2) : (2 : K) = 0 := by
  haveI : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; norm_num)
  have hdvd : addOrderOf (1 : k) ∣ 2 := by
    have h := addOrderOf_dvd_natCard (1 : k)
    rwa [hk] at h
  have h2 : (2 : k) = 0 := by
    have h := addOrderOf_dvd_iff_nsmul_eq_zero.1 hdvd
    simpa using h
  have h4 : ((2 : k) : K) = 0 := by rw [h2]; rfl
  exact h4

private theorem f4_natCast_eq_zero (h2 : (2 : K) = 0) {n : ℕ} (hn : 2 ∣ n) : (n : K) = 0 := by
  obtain ⟨m, rfl⟩ := hn
  push_cast
  rw [h2, zero_mul]

private theorem f4_symmetrizer_diag :
    ∀ i : Fin Tag.F4.rank, Tag.F4.symmetrizer i i = 1 ∨ Tag.F4.symmetrizer i i = 2 := by
  decide +kernel

private theorem f4_norm_single_short :
    ∀ i : Fin Tag.F4.rank, 2 ≤ i.val → rootNorm Tag.F4 (Pi.single i 1) = 2 := by decide +kernel

private theorem f4_norm_single_long :
    ∀ i : Fin Tag.F4.rank, i.val < 2 → rootNorm Tag.F4 (Pi.single i 1) = 4 := by decide +kernel

private theorem f4_short_of_norm :
    ∀ i : Fin Tag.F4.rank, rootNorm Tag.F4 (Pi.single i 1) = 2 → 2 ≤ i.val := by decide +kernel

private theorem f4_cartan_even :
    ∀ i j : Fin Tag.F4.rank, 2 ≤ j.val → i.val < 2 → 2 ∣ (Tag.F4.cartan j i).natAbs := by
  decide +kernel

private theorem rootVec_apply_rootLabel (γ : Fin τ.rank → ℤ) {δ : Fin τ.rank → ℤ} (hδ : IsRoot τ δ) :
    rootVec τ K γ (rootLabel hδ) = if γ = δ then 1 else 0 := by
  classical
  by_cases hγ : IsRoot τ γ
  · rw [rootVec_of_isRoot' hγ, Finsupp.single_apply]
    by_cases h : γ = δ
    · subst h
      simp
    · have hne : (Sum.inr ⟨γ, hγ⟩ : Label τ) ≠ rootLabel hδ := fun e => h (by simpa using e)
      simp [hne, h]
  · rw [rootVec_of_not_isRoot' hγ]
    have h : γ ≠ δ := fun e => hγ (e ▸ hδ)
    simp [h]

private theorem rootVec_apply_inl (γ : Fin τ.rank → ℤ) (j : Fin τ.rank) :
    rootVec τ K γ (Sum.inl j) = 0 := by
  by_cases hγ : IsRoot τ γ
  · rw [rootVec_of_isRoot' hγ]
    simp
  · rw [rootVec_of_not_isRoot' hγ]
    rfl

private def f4IdealSet : Set (Label Tag.F4) :=
  {a | Sum.elim (fun j : Fin Tag.F4.rank => 2 ≤ j.val) (fun β => rootNorm Tag.F4 β.1 = 2) a}

private noncomputable def f4Ideal (K : Type) [Field K] : Submodule K (RootModule Tag.F4 K) :=
  Finsupp.supported K K f4IdealSet

private theorem mem_f4Ideal_iff {z : RootModule Tag.F4 K} :
    z ∈ f4Ideal K ↔
      (z (Sum.inl ⟨0, by decide⟩) = 0 ∧ z (Sum.inl ⟨1, by decide⟩) = 0) ∧
        ∀ (β : Fin Tag.F4.rank → ℤ) (hβ : IsRoot Tag.F4 β), rootNorm Tag.F4 β = 4 →
          z (rootLabel hβ) = 0 := by
  unfold f4Ideal
  rw [Finsupp.mem_supported']
  constructor
  · intro h
    refine ⟨⟨h _ ?_, h _ ?_⟩, fun β hβ hn => h _ ?_⟩
    · simp [f4IdealSet]
    · simp [f4IdealSet]
    · simp [f4IdealSet, hn]
  · rintro ⟨⟨h0, h1⟩, hlong⟩ a ha
    rcases a with j | ⟨β, hβ⟩
    · have hj : j.val < 2 := by
        by_contra hcon
        exact ha (by simpa [f4IdealSet] using (by omega : 2 ≤ j.val))
      have hj01 : j = ⟨0, by decide⟩ ∨ j = ⟨1, by decide⟩ := by
        rcases j with ⟨j, hj'⟩
        simp only at hj
        interval_cases j
        · exact Or.inl rfl
        · exact Or.inr rfl
      rcases hj01 with rfl | rfl
      · exact h0
      · exact h1
    · have hn : ¬ rootNorm Tag.F4 β = 2 := by simpa [f4IdealSet] using ha
      rcases spanF2_rootNorm_F4 hβ with h | h
      · exact absurd h hn
      · exact hlong β hβ h

private theorem f4Ideal_map_mem (f : Module.End K (RootModule Tag.F4 K))
    (hh : ∀ j : Fin Tag.F4.rank, 2 ≤ j.val → f (hVec Tag.F4 K j) ∈ f4Ideal K)
    (hv : ∀ β : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 β → rootNorm Tag.F4 β = 2 →
      f (rootVec Tag.F4 K β) ∈ f4Ideal K)
    {z : RootModule Tag.F4 K} (hz : z ∈ f4Ideal K) : f z ∈ f4Ideal K := by
  have e : f4Ideal K = Submodule.span K ((fun a => Finsupp.single a (1 : K)) '' f4IdealSet) :=
    Finsupp.supported_eq_span_single K f4IdealSet
  have hle : f4Ideal K ≤ (f4Ideal K).comap f := by
    refine e.le.trans (Submodule.span_le.2 ?_)
    rintro _ ⟨a, ha, rfl⟩
    rcases a with j | ⟨β, hβ⟩
    · exact hh j ha
    · have h := hv β hβ ha
      rwa [rootVec_eq_basisVec_of_isRoot hβ] at h
  exact hle hz

private theorem f4Ideal_negLabel {θ : Fin Tag.F4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.F4 θ)
    {z : RootModule Tag.F4 K} (hz : z ∈ f4Ideal K) : z (negLabel hθ.1) = 0 := by
  have hn : rootNorm Tag.F4 (-θ) = 4 := by rw [rootNorm_neg]; exact hθ.rootNorm_F4
  exact (mem_f4Ideal_iff.1 hz).2 _ (isRoot_neg_iff.2 hθ.1) hn

private theorem f4_vanishSub_long {k : Subfield K} {R : Subgroup ↥(adjointGroup Tag.F4 K)}
    (hrat : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → ∀ c ∈ k,
      xPar (rootOperatorFamily Tag.F4) γ c ∈ R)
    {θ : Fin Tag.F4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.F4 θ) {z : RootModule Tag.F4 K}
    (hz : z ∈ vanishSub R (negLabel hθ.1)) {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hn : rootNorm Tag.F4 β = 4) : z (rootLabel hβ) = 0 := by
  have hw := weylElement_one_mem_of_rat k R hrat
  obtain ⟨r, hr, ε, hε, -, hcoord⟩ := exists_weyl_move (Or.inr (Or.inr (Or.inr rfl))) hw hβ
    (isRoot_neg_iff.2 hθ.1) (by rw [hn, rootNorm_neg, hθ.rootNorm_F4])
  have h0 := mem_vanishSub.1 hz r hr
  rw [hcoord z] at h0
  rcases hε with rfl | rfl <;> simpa using h0

private theorem f4_xOp_coord_simple (i : Fin Tag.F4.rank) (c : K) (z : RootModule Tag.F4 K) :
    (xOp Tag.F4 K i c z) (rootLabel (isRoot_single Tag.F4 i)) =
      z (rootLabel (isRoot_single Tag.F4 i)) +
        c ^ 2 * z (rootLabel (isRoot_neg_single Tag.F4 i)) +
        c * ∑ j : Fin Tag.F4.rank, ((Tag.F4.cartan j i).natAbs : K) * z (Sum.inl j) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h1 h2 =>
    simp only [map_add, Finsupp.add_apply, mul_add, Finset.sum_add_distrib, h1, h2]
    ring
  | single b a =>
    rcases b with j | ⟨α, hα⟩
    · have e : (Finsupp.single (Sum.inl j) a : RootModule Tag.F4 K) = a • hVec Tag.F4 K j := by
        simp [hVec]
      rw [e, map_smul, xOp_apply_hVec]
      simp only [Finsupp.smul_apply, Finsupp.add_apply, smul_eq_mul, rootVec_apply_rootLabel]
      simp [hVec, Finsupp.single_apply, mul_comm, mul_left_comm]
      done
    · have e : (Finsupp.single (Sum.inr ⟨α, hα⟩) a : RootModule Tag.F4 K) = a • rootVec Tag.F4 K α := by
        rw [rootVec_of_isRoot' hα]
        simp
      rw [e, map_smul]
      simp only [Finsupp.smul_apply, smul_eq_mul, rootVec_apply_rootLabel, rootVec_apply_inl,
        mul_zero, Finset.sum_const_zero, add_zero]
      have hne1 : (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ≠ -Pi.single i 1 := single_ne_neg_single i
      have hne2 : (-Pi.single i 1 : Fin Tag.F4.rank → ℤ) ≠ Pi.single i 1 := hne1.symm
      by_cases h1 : α = Pi.single i 1
      · subst h1
        rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_single]
        simp [rootVec_apply_rootLabel, hne1]
      · by_cases h2 : α = -Pi.single i 1
        · subst h2
          rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single]
          simp [rootVec_apply_rootLabel, hne2, rootVec_apply_inl, hVec, Finsupp.single_apply]
          ring
        · have hk : ∀ k : ℕ, α + (k : ℤ) • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) ≠ Pi.single i 1 := by
            intro k hk
            have hα' : α = (1 - (k : ℤ)) • (Pi.single i 1 : Fin Tag.F4.rank → ℤ) := by
              rw [sub_smul, one_smul]
              exact eq_sub_of_add_eq hk
            rcases (isRoot_smul_single_iff i (1 - (k : ℤ))).1 (hα' ▸ hα) with h | h
            · exact h1 (by rw [hα', h, one_smul])
            · exact h2 (by rw [hα', h, neg_one_smul])
          rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_of_ne i c hα h1 h2, Finsupp.finset_sum_apply, if_neg h1, if_neg h2]
          rw [Finset.sum_eq_zero, mul_zero, mul_zero, add_zero]
          intro k _
          rw [Finsupp.smul_apply, rootVec_apply_rootLabel, if_neg (hk k), smul_eq_mul, mul_zero]

private theorem f4_vanishSub_cartan (h2 : (2 : K) = 0) {k : Subfield K}
    {R : Subgroup ↥(adjointGroup Tag.F4 K)}
    (hrat : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → ∀ c ∈ k,
      xPar (rootOperatorFamily Tag.F4) γ c ∈ R)
    {θ : Fin Tag.F4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.F4 θ) {z : RootModule Tag.F4 K}
    (hz : z ∈ vanishSub R (negLabel hθ.1)) :
    z (Sum.inl ⟨0, by decide⟩) = 0 ∧ z (Sum.inl ⟨1, by decide⟩) = 0 := by
  have hRinv : ∀ r' ∈ R, endHom K r' z ∈ vanishSub R (negLabel hθ.1) := by
    intro r' hr'
    refine mem_vanishSub.2 fun r hr => ?_
    rw [← Module.End.mul_apply, ← map_mul]
    exact mem_vanishSub.1 hz (r * r') (R.mul_mem hr hr')
  have hxz : ∀ i : Fin Tag.F4.rank, xOp Tag.F4 K i 1 z ∈ vanishSub R (negLabel hθ.1) := by
    intro i
    have he : endHom K (xPar (rootOperatorFamily Tag.F4) (Pi.single i 1) (1 : K)) =
        xOp Tag.F4 K i 1 := by
      rw [xPar_simple, endHom_eltElement, (rootOperatorFamily Tag.F4).elt_simple]
    rw [← he]
    exact hRinv _ (hrat _ (isRoot_single Tag.F4 i) 1 k.one_mem)
  have key : ∀ i : Fin Tag.F4.rank, i.val < 2 →
      ∑ j : Fin Tag.F4.rank, ((Tag.F4.cartan j i).natAbs : K) * z (Sum.inl j) = 0 := by
    intro i hi
    have hl : rootNorm Tag.F4 (Pi.single i 1) = 4 := f4_norm_single_long i hi
    have c1 := f4_vanishSub_long hrat hθ (hxz i) (isRoot_single Tag.F4 i) hl
    have c2 := f4_vanishSub_long hrat hθ hz (isRoot_single Tag.F4 i) hl
    have c3 := f4_vanishSub_long hrat hθ hz (isRoot_neg_single Tag.F4 i)
      (by rw [rootNorm_neg]; exact hl)
    rw [f4_xOp_coord_simple, c2, c3] at c1
    simpa using c1
  have e0 := key ⟨0, by decide⟩ (by decide)
  have e1 := key ⟨1, by decide⟩ (by decide)
  have hs : ∀ g : Fin Tag.F4.rank → K, ∑ j, g j =
      g ⟨0, by decide⟩ + g ⟨1, by decide⟩ + g ⟨2, by decide⟩ + g ⟨3, by decide⟩ :=
    fun g => Fin.sum_univ_four g
  have a00 : (Tag.F4.cartan ⟨0, by decide⟩ ⟨0, by decide⟩).natAbs = 2 := by decide +kernel
  have a10 : (Tag.F4.cartan ⟨1, by decide⟩ ⟨0, by decide⟩).natAbs = 1 := by decide +kernel
  have a20 : (Tag.F4.cartan ⟨2, by decide⟩ ⟨0, by decide⟩).natAbs = 0 := by decide +kernel
  have a30 : (Tag.F4.cartan ⟨3, by decide⟩ ⟨0, by decide⟩).natAbs = 0 := by decide +kernel
  have a01 : (Tag.F4.cartan ⟨0, by decide⟩ ⟨1, by decide⟩).natAbs = 1 := by decide +kernel
  have a11 : (Tag.F4.cartan ⟨1, by decide⟩ ⟨1, by decide⟩).natAbs = 2 := by decide +kernel
  have a21 : (Tag.F4.cartan ⟨2, by decide⟩ ⟨1, by decide⟩).natAbs = 2 := by decide +kernel
  have a31 : (Tag.F4.cartan ⟨3, by decide⟩ ⟨1, by decide⟩).natAbs = 0 := by decide +kernel
  rw [hs, a00, a10, a20, a30] at e0
  rw [hs, a01, a11, a21, a31] at e1
  simp [h2] at e0 e1
  exact ⟨e1, e0⟩

private theorem f4_vanishSub_le_ideal (h2 : (2 : K) = 0) {k : Subfield K}
    {R : Subgroup ↥(adjointGroup Tag.F4 K)}
    (hrat : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → ∀ c ∈ k,
      xPar (rootOperatorFamily Tag.F4) γ c ∈ R)
    {θ : Fin Tag.F4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.F4 θ) :
    vanishSub R (negLabel hθ.1) ≤ f4Ideal K := by
  intro z hz
  rw [mem_f4Ideal_iff]
  exact ⟨f4_vanishSub_cartan h2 hrat hθ hz, fun β hβ hn => f4_vanishSub_long hrat hθ hz hβ hn⟩

private theorem f4_xOp_hVec (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {j : Fin Tag.F4.rank} (hj : 2 ≤ j.val) : xOp Tag.F4 K i c (hVec Tag.F4 K j) ∈ f4Ideal K := by
  rw [xOp_apply_hVec]
  refine Submodule.add_mem _ (Finsupp.single_mem_supported K 1 hj) ?_
  by_cases hi : 2 ≤ i.val
  · refine Submodule.smul_mem _ _ ?_
    rw [rootVec_eq_basisVec_of_isRoot (isRoot_single Tag.F4 i)]
    exact Finsupp.single_mem_supported K 1 (f4_norm_single_short i hi)
  · rw [f4_natCast_eq_zero h2 (f4_cartan_even i j hj (by omega)), zero_mul, zero_smul]
    exact Submodule.zero_mem _

private theorem f4_yOp_hVec (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {j : Fin Tag.F4.rank} (hj : 2 ≤ j.val) : yOp Tag.F4 K i c (hVec Tag.F4 K j) ∈ f4Ideal K := by
  rw [yOp_apply_hVec]
  refine Submodule.add_mem _ (Finsupp.single_mem_supported K 1 hj) ?_
  by_cases hi : 2 ≤ i.val
  · refine Submodule.smul_mem _ _ ?_
    rw [rootVec_eq_basisVec_of_isRoot (isRoot_neg_single Tag.F4 i)]
    refine Finsupp.single_mem_supported K 1 ?_
    show rootNorm Tag.F4 (-Pi.single i 1) = 2
    rw [rootNorm_neg]
    exact f4_norm_single_short i hi
  · rw [f4_natCast_eq_zero h2 (f4_cartan_even i j hj (by omega)), zero_mul, zero_smul]
    exact Submodule.zero_mem _

private theorem rootNorm_add_smul_single (i : Fin τ.rank) (v : Fin τ.rank → ℤ) (m : ℤ) :
    rootNorm τ (v + m • Pi.single i 1) =
      rootNorm τ v + 2 * m * (τ.symmetrizer i i * ∑ j, τ.cartan i j * v j) +
        m ^ 2 * (2 * τ.symmetrizer i i) := by
  have hsymm := symmetrizedCartan_isSymm τ
  have hsym : ∀ a b, τ.symmetrizedCartan a b = τ.symmetrizedCartan b a :=
    fun a b => hsymm.apply b a
  have hBv : Matrix.mulVec τ.symmetrizedCartan v i =
      τ.symmetrizer i i * ∑ j, τ.cartan i j * v j := by
    simp only [Matrix.mulVec, dotProduct, symmetrizedCartan_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hBii : τ.symmetrizedCartan i i = 2 * τ.symmetrizer i i := by
    rw [symmetrizedCartan_apply, τ.cartan_self, mul_comm]
  have h1 : dotProduct v (Matrix.mulVec τ.symmetrizedCartan (Pi.single i 1)) =
      Matrix.mulVec τ.symmetrizedCartan v i := by
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact Finset.sum_congr rfl fun a _ => by rw [hsym a i]; ring
  have h2 : dotProduct (Pi.single i (1 : ℤ)) (Matrix.mulVec τ.symmetrizedCartan v) =
      Matrix.mulVec τ.symmetrizedCartan v i := by
    simp
  have h3 : dotProduct (Pi.single i (1 : ℤ)) (Matrix.mulVec τ.symmetrizedCartan (Pi.single i 1)) =
      2 * τ.symmetrizer i i := by
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite,
      mul_one, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    exact hBii
  unfold rootNorm
  simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct, dotProduct_smul,
    smul_dotProduct, smul_eq_mul]
  linear_combination m * h1 + m * h2 + m ^ 2 * h3 + 2 * m * hBv

private theorem f4_string_even_x (i : Fin Tag.F4.rank) {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hn : rootNorm Tag.F4 β = 2) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1) {k : ℕ}
    (hk : k ≤ stringUp Tag.F4 i β) (hγ : rootNorm Tag.F4 (β + (k : ℤ) • Pi.single i 1) = 4) :
    2 ∣ (stringDown Tag.F4 i β + k).choose k := by
  obtain ⟨hrefl, -⟩ := root_string_reflection hβ i
  obtain ⟨hpq, -⟩ := isRoot_add_smul_single_iff hβ i h₁ h₂
  have hF0 := rootNorm_add_smul_single (τ := Tag.F4) i β (k : ℤ)
  rw [hγ, hn, hrefl] at hF0
  have hd := f4_symmetrizer_diag i
  generalize Tag.F4.symmetrizer i i = d at hF0 hd
  have key : (k : ℤ) * (d * ((stringDown Tag.F4 i β : ℤ) - stringUp Tag.F4 i β + k)) = 1 := by
    have h2' : (2 : ℤ) * ((k : ℤ) * (d * ((stringDown Tag.F4 i β : ℤ) - stringUp Tag.F4 i β + k)))
        = 2 * 1 := by
      linear_combination (-1 : ℤ) * hF0
    exact mul_left_cancel₀ (by norm_num) h2'
  rcases Int.eq_one_or_neg_one_of_mul_eq_one key with hk1 | hk1
  · have hk1' : k = 1 := by exact_mod_cast hk1
    rw [hk1] at key
    have hq : stringDown Tag.F4 i β = 1 := by
      rcases hd with rfl | rfl <;> omega
    rw [hq, hk1']
    decide
  · omega

private theorem f4_string_even_y (i : Fin Tag.F4.rank) {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β)
    (hn : rootNorm Tag.F4 β = 2) (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1) {k : ℕ}
    (hk : k ≤ stringDown Tag.F4 i β) (hγ : rootNorm Tag.F4 (β - (k : ℤ) • Pi.single i 1) = 4) :
    2 ∣ (stringUp Tag.F4 i β + k).choose k := by
  obtain ⟨hrefl, -⟩ := root_string_reflection hβ i
  obtain ⟨hpq, -⟩ := isRoot_add_smul_single_iff hβ i h₁ h₂
  have hγ' : rootNorm Tag.F4 (β + (-(k : ℤ)) • Pi.single i 1) = 4 := by
    rw [neg_smul, ← sub_eq_add_neg]
    exact hγ
  have hF0 := rootNorm_add_smul_single (τ := Tag.F4) i β (-(k : ℤ))
  rw [hγ', hn, hrefl] at hF0
  have hd := f4_symmetrizer_diag i
  generalize Tag.F4.symmetrizer i i = d at hF0 hd
  have key : (k : ℤ) * (d * ((k : ℤ) - ((stringDown Tag.F4 i β : ℤ) - stringUp Tag.F4 i β))) = 1 := by
    have h2' : (2 : ℤ) * ((k : ℤ) * (d * ((k : ℤ) -
        ((stringDown Tag.F4 i β : ℤ) - stringUp Tag.F4 i β)))) = 2 * 1 := by
      linear_combination (-1 : ℤ) * hF0
    exact mul_left_cancel₀ (by norm_num) h2'
  rcases Int.eq_one_or_neg_one_of_mul_eq_one key with hk1 | hk1
  · have hk1' : k = 1 := by exact_mod_cast hk1
    rw [hk1] at key
    have hp : stringUp Tag.F4 i β = 1 := by
      rcases hd with rfl | rfl <;> omega
    rw [hp, hk1']
    decide
  · omega

private theorem f4_xOp_rootVec_long (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hn : rootNorm Tag.F4 β = 2)
    (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) (hγn : rootNorm Tag.F4 γ = 4) :
    (xOp Tag.F4 K i c (rootVec Tag.F4 K β)) (rootLabel hγ) = 0 := by
  rw [xOp_apply_rootVec_of_ne i c hβ h₁ h₂, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finsupp.smul_apply, rootVec_apply_rootLabel, smul_eq_mul]
  split_ifs with heq
  · have hγ' : rootNorm Tag.F4 (β + (k : ℤ) • Pi.single i 1) = 4 := by
      rw [heq]
      exact hγn
    have hev := f4_string_even_x i hβ hn h₁ h₂ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hγ'
    rw [f4_natCast_eq_zero h2 hev, zero_mul, zero_mul]
  · rw [mul_zero]

private theorem f4_yOp_rootVec_long (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hn : rootNorm Tag.F4 β = 2)
    (h₁ : β ≠ Pi.single i 1) (h₂ : β ≠ -Pi.single i 1)
    {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ) (hγn : rootNorm Tag.F4 γ = 4) :
    (yOp Tag.F4 K i c (rootVec Tag.F4 K β)) (rootLabel hγ) = 0 := by
  rw [yOp_apply_rootVec_of_ne i c hβ h₁ h₂, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun k hk => ?_
  rw [Finsupp.smul_apply, rootVec_apply_rootLabel, smul_eq_mul]
  split_ifs with heq
  · have hγ' : rootNorm Tag.F4 (β - (k : ℤ) • Pi.single i 1) = 4 := by
      rw [heq]
      exact hγn
    have hev := f4_string_even_y i hβ hn h₁ h₂ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)) hγ'
    rw [f4_natCast_eq_zero h2 hev, zero_mul, zero_mul]
  · rw [mul_zero]

private theorem f4_rootVec_mem_short {γ : Fin Tag.F4.rank → ℤ} (hγ : IsRoot Tag.F4 γ)
    (hn : rootNorm Tag.F4 γ = 2) : rootVec Tag.F4 K γ ∈ f4Ideal K := by
  have hmem : rootLabel hγ ∈ f4IdealSet := hn
  rw [CFSG.Blueprint.Chevalley.rootVec_eq_basisVec_of_isRoot hγ]
  exact Finsupp.single_mem_supported (R := K) _ hmem

private theorem f4_hVec_mem {j : Fin Tag.F4.rank} (hj : 2 ≤ j.val) :
    hVec Tag.F4 K j ∈ f4Ideal K := by
  have hmem : (Sum.inl j : Label Tag.F4) ∈ f4IdealSet := hj
  exact Finsupp.single_mem_supported (R := K) _ hmem

private theorem f4_xOp_rootVec (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hn : rootNorm Tag.F4 β = 2) :
    xOp Tag.F4 K i c (rootVec Tag.F4 K β) ∈ f4Ideal K := by
  by_cases h₁ : β = Pi.single i 1
  · subst h₁
    rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_single]
    exact f4_rootVec_mem_short (isRoot_single Tag.F4 i) hn
  by_cases h₂ : β = -Pi.single i 1
  · subst h₂
    have hn' : rootNorm Tag.F4 (Pi.single i 1) = 2 := by
      rw [← rootNorm_neg]
      exact hn
    have hi : 2 ≤ i.val := f4_short_of_norm i hn'
    rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_neg_single]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (f4_rootVec_mem_short (isRoot_neg_single Tag.F4 i) hn)
        (Submodule.smul_mem _ c (f4_hVec_mem hi)))
      (Submodule.smul_mem _ _ (f4_rootVec_mem_short (isRoot_single Tag.F4 i) hn'))
  · have hcart : ∀ j : Fin Tag.F4.rank,
        (xOp Tag.F4 K i c (rootVec Tag.F4 K β)) (Sum.inl j) = 0 := by
      intro j
      rw [CFSG.Blueprint.Chevalley.xOp_apply_rootVec_of_ne i c hβ h₁ h₂, Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Finsupp.smul_apply, rootVec_apply_inl, smul_zero]
    exact mem_f4Ideal_iff.2 ⟨⟨hcart _, hcart _⟩,
      fun γ hγ hγn => f4_xOp_rootVec_long h2 i c hβ hn h₁ h₂ hγ hγn⟩

private theorem f4_yOp_rootVec (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {β : Fin Tag.F4.rank → ℤ} (hβ : IsRoot Tag.F4 β) (hn : rootNorm Tag.F4 β = 2) :
    yOp Tag.F4 K i c (rootVec Tag.F4 K β) ∈ f4Ideal K := by
  by_cases h₂ : β = -Pi.single i 1
  · subst h₂
    rw [CFSG.Blueprint.Chevalley.yOp_apply_rootVec_neg_single]
    exact f4_rootVec_mem_short (isRoot_neg_single Tag.F4 i) hn
  by_cases h₁ : β = Pi.single i 1
  · subst h₁
    have hi : 2 ≤ i.val := f4_short_of_norm i hn
    have hn' : rootNorm Tag.F4 (-Pi.single i 1) = 2 := by
      rw [rootNorm_neg]
      exact hn
    rw [CFSG.Blueprint.Chevalley.yOp_apply_rootVec_single]
    exact Submodule.add_mem _
      (Submodule.add_mem _ (f4_rootVec_mem_short (isRoot_single Tag.F4 i) hn)
        (Submodule.smul_mem _ c (f4_hVec_mem hi)))
      (Submodule.smul_mem _ _ (f4_rootVec_mem_short (isRoot_neg_single Tag.F4 i) hn'))
  · have hcart : ∀ j : Fin Tag.F4.rank,
        (yOp Tag.F4 K i c (rootVec Tag.F4 K β)) (Sum.inl j) = 0 := by
      intro j
      rw [CFSG.Blueprint.Chevalley.yOp_apply_rootVec_of_ne i c hβ h₁ h₂, Finsupp.finsetSum_apply]
      exact Finset.sum_eq_zero fun k _ => by
        rw [Finsupp.smul_apply, rootVec_apply_inl, smul_zero]
    exact mem_f4Ideal_iff.2 ⟨⟨hcart _, hcart _⟩,
      fun γ hγ hγn => f4_yOp_rootVec_long h2 i c hβ hn h₁ h₂ hγ hγn⟩

private theorem f4Ideal_xOp (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {z : RootModule Tag.F4 K} (hz : z ∈ f4Ideal K) : xOp Tag.F4 K i c z ∈ f4Ideal K :=
  f4Ideal_map_mem (xOp Tag.F4 K i c) (fun _ hj => f4_xOp_hVec h2 i c hj)
    (fun _ hβ hn => f4_xOp_rootVec h2 i c hβ hn) hz

private theorem f4Ideal_yOp (h2 : (2 : K) = 0) (i : Fin Tag.F4.rank) (c : K)
    {z : RootModule Tag.F4 K} (hz : z ∈ f4Ideal K) : yOp Tag.F4 K i c z ∈ f4Ideal K :=
  f4Ideal_map_mem (yOp Tag.F4 K i c) (fun _ hj => f4_yOp_hVec h2 i c hj)
    (fun _ hβ hn => f4_yOp_rootVec h2 i c hβ hn) hz

private theorem stable_of_generators (T : Submodule K (RootModule τ K))
    (hx : ∀ (i : Fin τ.rank) (c : K), ∀ z ∈ T, xOp τ K i c z ∈ T)
    (hy : ∀ (i : Fin τ.rank) (c : K), ∀ z ∈ T, yOp τ K i c z ∈ T)
    (g : ↥(adjointGroup τ K)) {z : RootModule τ K} (hz : z ∈ T) : endHom K g z ∈ T := by
  classical
  let Stab : Subgroup ↥(adjointGroup τ K) :=
    { carrier := {g | (∀ z ∈ T, endHom K g z ∈ T) ∧ (∀ z ∈ T, endHom K g⁻¹ z ∈ T)}
      one_mem' := ⟨fun z hz => by simpa using hz, fun z hz => by simpa using hz⟩
      mul_mem' := fun {g₁ g₂} h1 h2 => ⟨fun z hz => by
          rw [map_mul, Module.End.mul_apply]
          exact h1.1 _ (h2.1 z hz), fun z hz => by
          rw [mul_inv_rev, map_mul, Module.End.mul_apply]
          exact h2.2 _ (h1.2 z hz)⟩
      inv_mem' := fun {g} h => ⟨h.2, fun z hz => by simpa using h.1 z hz⟩ }
  have hinvgen : ∀ (i : Fin τ.rank) (c : K), xPar (rootOperatorFamily τ) (Pi.single i 1) c ∈ Stab ∧
      xPar (rootOperatorFamily τ) (-Pi.single i 1) c ∈ Stab := by
    intro i c
    have ex : ∀ c : K, endHom K (xPar (rootOperatorFamily τ) (Pi.single i 1) c) = xOp τ K i c := by
      intro c
      rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
    have ey : ∀ c : K, endHom K (xPar (rootOperatorFamily τ) (-Pi.single i 1) c) = yOp τ K i c := by
      intro c
      rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily τ).elt_neg_simple]
    refine ⟨⟨fun z hz => ?_, fun z hz => ?_⟩, ⟨fun z hz => ?_, fun z hz => ?_⟩⟩
    · rw [ex]
      exact hx i c z hz
    · rw [xPar_neg, ex]
      exact hx i (-c) z hz
    · rw [ey]
      exact hy i c z hz
    · rw [xPar_neg, ey]
      exact hy i (-c) z hz
  have htop : Stab = ⊤ := by
    set S : Set (ModGL τ K) := {g | ∃ (i : Fin τ.rank) (c : K),
      (g : Module.End K (RootModule τ K)) = xOp τ K i c ∨
        (g : Module.End K (RootModule τ K)) = yOp τ K i c} with hS
    have hcl : Subgroup.closure (((↑) : ↥(adjointGroup τ K) → ModGL τ K) ⁻¹' S) = ⊤ :=
      Subgroup.closure_closure_coe_preimage
    rw [eq_top_iff, ← hcl, Subgroup.closure_le]
    rintro g ⟨i, c, hg | hg⟩
    · have e : g = xPar (rootOperatorFamily τ) (Pi.single i 1) c := endHom_injective (by
        rw [xPar_simple, endHom_eltElement, (rootOperatorFamily τ).elt_simple]
        exact hg)
      rw [e]
      exact (hinvgen i c).1
    · have e : g = xPar (rootOperatorFamily τ) (-Pi.single i 1) c := endHom_injective (by
        rw [xPar_neg_simple, endHom_eltElement, (rootOperatorFamily τ).elt_neg_simple]
        exact hg)
      rw [e]
      exact (hinvgen i c).2
  have hg : g ∈ Stab := by
    rw [htop]
    exact Subgroup.mem_top g
  exact hg.1 z hz

private theorem f4Ideal_stable (h2 : (2 : K) = 0) (g : ↥(adjointGroup Tag.F4 K))
    {z : RootModule Tag.F4 K} (hz : z ∈ f4Ideal K) : endHom K g z ∈ f4Ideal K :=
  stable_of_generators (f4Ideal K) (fun i c _ hz => f4Ideal_xOp h2 i c hz)
    (fun i c _ hz => f4Ideal_yOp h2 i c hz) g hz

theorem vanishSub_le_top_f2_F4 {k : Subfield K} (hk : Nat.card k = 2)
    {R : Subgroup ↥(adjointGroup Tag.F4 K)}
    (hrat : ∀ γ : Fin Tag.F4.rank → ℤ, IsRoot Tag.F4 γ → ∀ c ∈ k,
      xPar (rootOperatorFamily Tag.F4) γ c ∈ R)
    {θ : Fin Tag.F4.rank → ℤ} (hθ : IsMaxHeightRoot Tag.F4 θ) :
    vanishSub R (negLabel hθ.1) ≤ vanishSub (⊤ : Subgroup ↥(adjointGroup Tag.F4 K)) (negLabel hθ.1) := by
  have h2 : (2 : K) = 0 := f4_two_eq_zero hk
  intro z hz
  have hzT : z ∈ f4Ideal K := f4_vanishSub_le_ideal h2 hrat hθ hz
  rw [mem_vanishSub]
  intro g _
  exact f4Ideal_negLabel hθ (f4Ideal_stable h2 g hzT)

theorem vanishSub_le_top_f2 (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) {k : Subfield K}
    (hk : Nat.card k = 2) {R : Subgroup ↥(adjointGroup τ K)}
    (hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) :
    vanishSub R (negLabel hθ.1) ≤ vanishSub (⊤ : Subgroup ↥(adjointGroup τ K)) (negLabel hθ.1) := by
  rcases hτ with rfl | rfl | rfl | rfl
  · exact vanishSub_le_top_f2_E (Or.inl rfl) hk hrat hθ
  · exact vanishSub_le_top_f2_E (Or.inr (Or.inl rfl)) hk hrat hθ
  · exact vanishSub_le_top_f2_E (Or.inr (Or.inr rfl)) hk hrat hθ
  · exact vanishSub_le_top_f2_F4 hk hrat hθ

theorem mem_subfieldGroup_of_entries_f2 (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) [Finite K]
    (σ : K ≃+* K) (hk : Nat.card (fixSubfield σ) = 2) (hK3 : 3 ≤ Nat.card K)
    {θ : Fin τ.rank → ℤ} (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K))
    (hall : ∀ r ∈ subfieldGroup τ σ, ∀ r' ∈ subfieldGroup τ σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∈ fixSubfield σ) :
    g ∈ subfieldGroup τ σ := by
  classical
  set k := fixSubfield σ with hk'
  set R := subfieldGroup τ σ with hR
  have hrat : ∀ γ : Fin τ.rank → ℤ, IsRoot τ γ → ∀ c ∈ k, xPar (rootOperatorFamily τ) γ c ∈ R :=
    fun γ _ c hc => xPar_mem_subfieldGroup τ σ γ hc
  set g₂ : ↥(adjointGroup τ K) := entrywiseAdjointAut τ σ g with hg₂
  have hRfix : ∀ r ∈ R, entrywiseAdjointAut τ σ r = r := fun r hr => mem_fixedSubgroup.1 hr
  have hent : ∀ r ∈ R, ∀ r' ∈ R, entry (r * g₂ * r') (negLabel hθ.1) (rootLabel hθ.1) =
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) := by
    intro r hr r' hr'
    have e : r * g₂ * r' = entrywiseAdjointAut τ σ (r * g * r') := by
      rw [map_mul, map_mul, hRfix r hr, hRfix r' hr']
    rw [e, entry_entrywiseAdjointAut]
    exact (mem_fixSubfield σ).1 (hall r hr r' hr')
  set Z := vanishSub R (negLabel hθ.1) with hZ
  have hDmem : ∀ r' ∈ R, (endHom K g₂ - endHom K g) (endHom K r' (rootVec τ K θ)) ∈ Z := by
    intro r' hr'
    refine mem_vanishSub.2 fun r hr => ?_
    have hv : rootVec τ K θ = Finsupp.single (rootLabel hθ.1) 1 := rootVec_of_isRoot' hθ.1
    have h1 := hent r hr r' hr'
    unfold entry at h1
    rw [hv]
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply, ← Module.End.mul_apply, ← map_mul] at h1 ⊢
    rw [sub_eq_zero]
    simpa [mul_assoc, Module.End.mul_apply] using h1
  have hspan := span_orbit_eq_top_f2 hτ hk hrat hθ
  have hle : Submodule.span K {x | ∃ r ∈ R, x = endHom K r (rootVec τ K θ)} ≤
      Z.comap (endHom K g₂ - endHom K g) := by
    refine Submodule.span_le.2 ?_
    rintro x ⟨r', hr', rfl⟩
    exact hDmem r' hr'
  rw [hspan] at hle
  have hDV : ∀ v, (endHom K g₂ - endHom K g) v ∈ Z := fun v => hle (Submodule.mem_top (x := v))
  have hx : ∀ v : RootModule τ K, endHom K (g₂ * g⁻¹) v - v ∈ Z := by
    intro v
    have h1 := hDV (endHom K g⁻¹ v)
    have e1 : endHom K g (endHom K g⁻¹ v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    rw [LinearMap.sub_apply, e1] at h1
    rw [map_mul, Module.End.mul_apply]
    exact h1
  have hx' : ∀ v : RootModule τ K, endHom K (g₂ * g⁻¹) v - v ∈
      vanishSub (⊤ : Subgroup ↥(adjointGroup τ K)) (negLabel hθ.1) :=
    fun v => vanishSub_le_top_f2 hτ hk hrat hθ (hx v)
  have h3 : 3 ≤ Nat.card (⊤ : Subfield K) := by
    rw [Nat.card_congr (Subfield.topEquiv : (⊤ : Subfield K) ≃+* K).toEquiv]
    exact hK3
  have h1 := eq_one_of_sub_mem_vanishSub hτ h3 (R := (⊤ : Subgroup ↥(adjointGroup τ K)))
    (fun γ _ c _ => Subgroup.mem_top _) hθ (g₂ * g⁻¹) hx'
  have h2 : g₂ = g := mul_inv_eq_one.1 h1
  rw [hR, subfieldGroup, mem_fixedSubgroup]
  exact h2

theorem exists_bad_entry_f2 (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8 ∨ τ = .F4) [Finite K] (σ : K ≃+* K)
    (hk : Nat.card (fixSubfield σ) = 2) (hK3 : 3 ≤ Nat.card K) {θ : Fin τ.rank → ℤ}
    (hθ : IsMaxHeightRoot τ θ) (g : ↥(adjointGroup τ K)) (hg : g ∉ subfieldGroup τ σ) :
    ∃ r ∈ subfieldGroup τ σ, ∃ r' ∈ subfieldGroup τ σ,
      entry (r * g * r') (negLabel hθ.1) (rootLabel hθ.1) ∉ fixSubfield σ := by
  by_contra h
  push Not at h
  exact hg (mem_subfieldGroup_of_entries_f2 hτ σ hk hK3 hθ g h)

end EntryF2

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
