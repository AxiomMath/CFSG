module

public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightOrthPlusFour
public import CFSG.LocalAnalysis.SeitzReduction.OmegaPilotEightCommFour

public section

namespace CFSG.SeitzReduction.OmegaPilot

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear (matrixProjectiveDerived)
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (plusIndexEquiv coordinateQuadPlus coordinateQuadPlus_apply regular_coordinateQuadPlus)

section LeviConj

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem inW_map_iff {A : V ≃ₗ[K] V} (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {P₁ P₂ P₁' P₂' : HypPair Q} (h1e : A P₁.e = P₁'.e) (h1f : A P₁.f = P₁'.f)
    (h2e : A P₂.e = P₂'.e) (h2f : A P₂.f = P₂'.f) (x : V) :
    InW P₁' P₂' (A x) ↔ InW P₁ P₂ x := by
  simp only [InW, ← h1e, ← h1f, ← h2e, ← h2f, polar_map_of_mem hA]

theorem conj_mem_leviFix {A : V ≃ₗ[K] V} (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : ∀ g ∈ H, A * g * A⁻¹ ∈ H)
    {P₁ P₂ P₁' P₂' : HypPair Q} (h1e : A P₁.e = P₁'.e) (h1f : A P₁.f = P₁'.f)
    (h2e : A P₂.e = P₂'.e) (h2f : A P₂.f = P₂'.f) {g : V ≃ₗ[K] V} (hg : g ∈ leviFix H P₁ P₂) :
    A * g * A⁻¹ ∈ leviFix H P₁' P₂' := by
  obtain ⟨hgH, ⟨⟨hgO, hge⟩, hgf⟩, hgW⟩ := mem_leviFix.mp hg
  have hcomm : ∀ {u w : V}, g ∈ centralizer {eichler Q u w} →
      A * g * A⁻¹ ∈ centralizer {eichler Q (A u) (A w)} := by
    intro u w hc
    rw [mem_centralizer_singleton_iff] at hc ⊢
    rw [← eichler_conj hA]
    calc A * g * A⁻¹ * (A * eichler Q u w * A⁻¹) = A * (g * eichler Q u w) * A⁻¹ := by group
      _ = A * (eichler Q u w * g) * A⁻¹ := by rw [hc]
      _ = A * eichler Q u w * A⁻¹ * (A * g * A⁻¹) := by group
  have hAgO : A * g * A⁻¹ ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    mul_mem (mul_mem hA hgO) (inv_mem hA)
  refine mem_leviFix.mpr ⟨hH g hgH, ⟨⟨hAgO, ?_⟩, ?_⟩, ?_⟩
  · rw [← h1e, ← h2e]
    exact hcomm hge
  · rw [← h1f, ← h2f]
    exact hcomm hgf
  · intro x hx
    have hx' : InW P₁ P₂ (A⁻¹ x) := by
      rw [← inW_map_iff hA h1e h1f h2e h2f, LinearEquiv.apply_inv_apply']
      exact hx
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hgW _ hx', LinearEquiv.apply_inv_apply']

theorem map_conj_leviFix {A : V ≃ₗ[K] V} (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    {H : Subgroup (V ≃ₗ[K] V)} (hH : H.map (MulAut.conj A).toMonoidHom = H)
    {P₁ P₂ P₁' P₂' : HypPair Q} (h1e : A P₁.e = P₁'.e) (h1f : A P₁.f = P₁'.f)
    (h2e : A P₂.e = P₂'.e) (h2f : A P₂.f = P₂'.f) :
    (leviFix H P₁ P₂).map (MulAut.conj A).toMonoidHom = leviFix H P₁' P₂' := by
  have hH₁ : ∀ g ∈ H, A * g * A⁻¹ ∈ H := fun g hg => by
    rw [← hH]
    exact ⟨g, hg, rfl⟩
  have hH₂ : ∀ g ∈ H, A⁻¹ * g * A⁻¹⁻¹ ∈ H := fun g hg => by
    rw [← hH] at hg
    obtain ⟨h, hh, rfl⟩ := hg
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [show A⁻¹ * (A * h * A⁻¹) * A = h by group]
    exact hh
  have hinv : ∀ {v w : V}, A v = w → A⁻¹ w = v := fun h => by
    rw [← h, LinearEquiv.inv_apply_apply']
  apply le_antisymm
  · rintro _ ⟨g, hg, rfl⟩
    exact conj_mem_leviFix hA hH₁ h1e h1f h2e h2f hg
  · intro g hg
    refine ⟨A⁻¹ * g * A⁻¹⁻¹, conj_mem_leviFix (inv_mem hA) hH₂ (hinv h1e) (hinv h1f) (hinv h2e)
      (hinv h2f) hg, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    group

end LeviConj

section StabConj

variable {K : Type*} [Field K] {ι : Type*} [DecidableEq ι]

theorem map_conj_stabSub {A : (ι → K) ≃ₗ[K] (ι → K)} {a b a' b' : ι}
    (ha : A (Pi.single a 1) = Pi.single a' 1) (hb : A (Pi.single b 1) = Pi.single b' 1) :
    (stabSub (K := K) a b).map (MulAut.conj A).toMonoidHom = stabSub a' b' := by
  have ha' : A⁻¹ (Pi.single a' 1) = Pi.single a 1 := by rw [← ha, LinearEquiv.inv_apply_apply']
  have hb' : A⁻¹ (Pi.single b' 1) = Pi.single b 1 := by rw [← hb, LinearEquiv.inv_apply_apply']
  ext g
  constructor
  · rintro ⟨h, hh, rfl⟩
    obtain ⟨h1, h2⟩ := mem_stabSub.1 hh
    refine mem_stabSub.2 ⟨?_, ?_⟩
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearEquiv.mul_apply, ha', h1, ha]
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, LinearEquiv.mul_apply, hb', h2, hb]
  · intro hg
    obtain ⟨g1, g2⟩ := mem_stabSub.1 hg
    refine ⟨A⁻¹ * g * A, mem_stabSub.2 ⟨?_, ?_⟩, ?_⟩
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, ha, g1, ha']
    · rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hb, g2, hb']
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group

end StabConj

section ProjConj

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem map_conjProj_map_projHom (hQ : ∃ v, Q v ≠ 0) {A : (Fin d → K) ≃ₗ[K] (Fin d → K)}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (X : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K))) :
    ((X.subgroupOf (orthDerived Q)).map (projHom Q)).map (conjProj hQ hA).toMonoidHom =
      ((X.map (MulAut.conj A).toMonoidHom).subgroupOf (orthDerived Q)).map (projHom Q) := by
  ext y
  constructor
  · rintro ⟨_, ⟨Y, hY, rfl⟩, rfl⟩
    refine ⟨conjOrthDerived hA Y, mem_subgroupOf.mpr ?_, ?_⟩
    · rw [coe_conjOrthDerived]
      exact ⟨Y, mem_subgroupOf.mp hY, rfl⟩
    · rw [MulEquiv.coe_toMonoidHom, conjProj_projHom]
  · rintro ⟨Z, hZ, rfl⟩
    obtain ⟨Y', hY', hY'Z⟩ := mem_subgroupOf.mp hZ
    set Y := (conjOrthDerived hA).symm Z with hYdef
    have hYZ : conjOrthDerived hA Y = Z := MulEquiv.apply_symm_apply _ _
    have hYc : (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) = Y' := by
      have h1 := congrArg Subtype.val hYZ
      rw [coe_conjOrthDerived] at h1
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hY'Z
      have h2 : A * (Y : (Fin d → K) ≃ₗ[K] (Fin d → K)) * A⁻¹ = A * Y' * A⁻¹ := h1.trans hY'Z.symm
      simpa using h2
    refine ⟨projHom Q Y, ⟨Y, mem_subgroupOf.mpr (hYc ▸ hY'), rfl⟩, ?_⟩
    rw [MulEquiv.coe_toMonoidHom, conjProj_projHom, hYZ]

end ProjConj

section PlanePerm

variable {K : Type*} [Field K] {n : ℕ}

variable (n) in
@[expose] noncomputable def planePermEquiv (π : Equiv.Perm (Fin n)) : Equiv.Perm (Fin (2 * n)) :=
  (plusIndexEquiv n).symm.trans ((Equiv.sumCongr π π).trans (plusIndexEquiv n))

theorem planePermEquiv_inl (π : Equiv.Perm (Fin n)) (k : Fin n) :
    planePermEquiv n π (plusIndexEquiv n (.inl k)) = plusIndexEquiv n (.inl (π k)) := by
  simp [planePermEquiv]

theorem planePermEquiv_inr (π : Equiv.Perm (Fin n)) (k : Fin n) :
    planePermEquiv n π (plusIndexEquiv n (.inr k)) = plusIndexEquiv n (.inr (π k)) := by
  simp [planePermEquiv]

theorem planePermEquiv_symm_inl (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (planePermEquiv n π).symm (plusIndexEquiv n (.inl k)) = plusIndexEquiv n (.inl (π.symm k)) := by
  rw [Equiv.symm_apply_eq, planePermEquiv_inl, Equiv.apply_symm_apply]

theorem planePermEquiv_symm_inr (π : Equiv.Perm (Fin n)) (k : Fin n) :
    (planePermEquiv n π).symm (plusIndexEquiv n (.inr k)) = plusIndexEquiv n (.inr (π.symm k)) := by
  rw [Equiv.symm_apply_eq, planePermEquiv_inr, Equiv.apply_symm_apply]

@[expose] noncomputable def planePermLin (π : Equiv.Perm (Fin n)) :
    (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K) :=
  LinearEquiv.funCongrLeft K K (planePermEquiv n π).symm

theorem planePermLin_apply (π : Equiv.Perm (Fin n)) (v : Fin (2 * n) → K) (i : Fin (2 * n)) :
    planePermLin π v i = v ((planePermEquiv n π).symm i) := rfl

theorem planePermLin_single (π : Equiv.Perm (Fin n)) (i : Fin (2 * n)) :
    planePermLin (K := K) π (Pi.single i 1) = Pi.single (planePermEquiv n π i) 1 := by
  funext j
  rw [planePermLin_apply]
  simp only [Pi.single_apply, Equiv.symm_apply_eq]

theorem planePermLin_mem_orthogonalGroup (π : Equiv.Perm (Fin n)) :
    planePermLin (K := K) π ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  intro v
  rw [coordinateQuadPlus_apply, coordinateQuadPlus_apply]
  simp only [planePermLin_apply, planePermEquiv_symm_inl, planePermEquiv_symm_inr]
  exact Equiv.sum_comp π.symm
    (fun i => v (plusIndexEquiv n (.inl i)) * v (plusIndexEquiv n (.inr i)))

end PlanePerm

section StabTwoBar

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

theorem map_conjProj_stabTwoBar (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    {A : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K)}
    (hA : A ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K)) {i j i' j' : Fin n}
    (hi : (A (Pi.single (plusIndexEquiv n (.inl i)) 1) = Pi.single (plusIndexEquiv n (.inl i')) 1 ∧
        A (Pi.single (plusIndexEquiv n (.inr i)) 1) = Pi.single (plusIndexEquiv n (.inr i')) 1) ∨
      (A (Pi.single (plusIndexEquiv n (.inl i)) 1) = Pi.single (plusIndexEquiv n (.inr i')) 1 ∧
        A (Pi.single (plusIndexEquiv n (.inr i)) 1) = Pi.single (plusIndexEquiv n (.inl i')) 1))
    (hj : (A (Pi.single (plusIndexEquiv n (.inl j)) 1) = Pi.single (plusIndexEquiv n (.inl j')) 1 ∧
        A (Pi.single (plusIndexEquiv n (.inr j)) 1) = Pi.single (plusIndexEquiv n (.inr j')) 1) ∨
      (A (Pi.single (plusIndexEquiv n (.inl j)) 1) = Pi.single (plusIndexEquiv n (.inr j')) 1 ∧
        A (Pi.single (plusIndexEquiv n (.inr j)) 1) = Pi.single (plusIndexEquiv n (.inl j')) 1)) :
    (stabTwoBar K i j).map (conjProj hQ hA).toMonoidHom = stabTwoBar K i' j' := by
  have hplane : ∀ {k k' : Fin n},
      (A (Pi.single (plusIndexEquiv n (.inl k)) 1) = Pi.single (plusIndexEquiv n (.inl k')) 1 ∧
        A (Pi.single (plusIndexEquiv n (.inr k)) 1) = Pi.single (plusIndexEquiv n (.inr k')) 1) ∨
      (A (Pi.single (plusIndexEquiv n (.inl k)) 1) = Pi.single (plusIndexEquiv n (.inr k')) 1 ∧
        A (Pi.single (plusIndexEquiv n (.inr k)) 1) = Pi.single (plusIndexEquiv n (.inl k')) 1) →
      (stabSub (K := K) (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))).map
        (MulAut.conj A).toMonoidHom =
        stabSub (plusIndexEquiv n (.inl k')) (plusIndexEquiv n (.inr k')) := by
    intro k k' hk
    rcases hk with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact map_conj_stabSub h1 h2
    · rw [map_conj_stabSub h1 h2, stabSub_comm]
  rw [stabTwoBar, stabTwoBar, map_conjProj_map_projHom, stabTwo, stabTwo,
    Subgroup.map_inf_eq _ _ _ (MulAut.conj A).injective, hplane hi, hplane hj]

theorem map_conjProj_planePermLin_stabTwoBar (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (π : Equiv.Perm (Fin n)) (i j : Fin n) :
    (stabTwoBar K i j).map (conjProj hQ (planePermLin_mem_orthogonalGroup π)).toMonoidHom =
      stabTwoBar K (π i) (π j) := by
  refine map_conjProj_stabTwoBar hQ _ (Or.inl ⟨?_, ?_⟩) (Or.inl ⟨?_, ?_⟩) <;>
    rw [planePermLin_single] <;> simp only [planePermEquiv_inl, planePermEquiv_inr]

end StabTwoBar

section Flip

variable {K : Type} [Field K] {n : ℕ}

variable (K) in
@[expose] noncomputable def plusFlipLin (k : Fin n) : (Fin (2 * n) → K) ≃ₗ[K] (Fin (2 * n) → K) :=
  swapLin (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k))

theorem plusFlipLin_mem_orthogonalGroup (k : Fin n) :
    plusFlipLin K k ∈ TauCeti.QuadraticMap.orthogonalGroup (coordinateQuadPlus n K) :=
  (isHypCoord_coordinateQuadPlus k).swapLin_mem_orthogonalGroup

theorem plusFlipLin_single (k : Fin n) (j : Fin (2 * n)) :
    plusFlipLin K k (Pi.single j 1) =
      Pi.single (Equiv.swap (plusIndexEquiv n (.inl k)) (plusIndexEquiv n (.inr k)) j) 1 := by
  funext i
  rw [plusFlipLin, swapLin_apply]
  simp only [Pi.single_apply, Equiv.swap_apply_eq_iff]

theorem plusFlipLin_inl_self (k : Fin n) :
    plusFlipLin K k (Pi.single (plusIndexEquiv n (.inl k)) 1) =
      Pi.single (plusIndexEquiv n (.inr k)) 1 := by
  rw [plusFlipLin_single, Equiv.swap_apply_left]

theorem plusFlipLin_inr_self (k : Fin n) :
    plusFlipLin K k (Pi.single (plusIndexEquiv n (.inr k)) 1) =
      Pi.single (plusIndexEquiv n (.inl k)) 1 := by
  rw [plusFlipLin_single, Equiv.swap_apply_right]

theorem plusFlipLin_inl_of_ne {k j : Fin n} (hjk : j ≠ k) :
    plusFlipLin K k (Pi.single (plusIndexEquiv n (.inl j)) 1) =
      Pi.single (plusIndexEquiv n (.inl j)) 1 := by
  rw [plusFlipLin_single, Equiv.swap_apply_of_ne_of_ne]
  · intro h
    exact hjk (Sum.inl_injective ((plusIndexEquiv n).injective h))
  · intro h
    exact Sum.inl_ne_inr ((plusIndexEquiv n).injective h)

theorem plusFlipLin_inr_of_ne {k j : Fin n} (hjk : j ≠ k) :
    plusFlipLin K k (Pi.single (plusIndexEquiv n (.inr j)) 1) =
      Pi.single (plusIndexEquiv n (.inr j)) 1 := by
  rw [plusFlipLin_single, Equiv.swap_apply_of_ne_of_ne]
  · intro h
    exact Sum.inr_ne_inl ((plusIndexEquiv n).injective h)
  · intro h
    exact hjk (Sum.inr_injective ((plusIndexEquiv n).injective h))

variable [CharP K 2]

theorem map_conjProj_plusFlipLin_stabTwoBar (hQ : ∃ v, coordinateQuadPlus n K v ≠ 0)
    (k i j : Fin n) :
    (stabTwoBar K i j).map (conjProj hQ (plusFlipLin_mem_orthogonalGroup k)).toMonoidHom =
      stabTwoBar K i j := by
  have hplane : ∀ l : Fin n,
      (plusFlipLin K k (Pi.single (plusIndexEquiv n (.inl l)) 1) =
          Pi.single (plusIndexEquiv n (.inl l)) 1 ∧
        plusFlipLin K k (Pi.single (plusIndexEquiv n (.inr l)) 1) =
          Pi.single (plusIndexEquiv n (.inr l)) 1) ∨
      (plusFlipLin K k (Pi.single (plusIndexEquiv n (.inl l)) 1) =
          Pi.single (plusIndexEquiv n (.inr l)) 1 ∧
        plusFlipLin K k (Pi.single (plusIndexEquiv n (.inr l)) 1) =
          Pi.single (plusIndexEquiv n (.inl l)) 1) := by
    intro l
    by_cases hl : l = k
    · subst hl
      exact Or.inr ⟨plusFlipLin_inl_self l, plusFlipLin_inr_self l⟩
    · exact Or.inl ⟨plusFlipLin_inl_of_ne hl, plusFlipLin_inr_of_ne hl⟩
  exact map_conjProj_stabTwoBar hQ _ (hplane i) (hplane j)

theorem map_conjProj_plusFlipLin_leviFixBar (hQ : ∃ v, coordinateQuadPlus 4 K v ≠ 0) :
    (leviFixBar (plusPair K 0) (plusPair K 1)).map
        (conjProj hQ (plusFlipLin_mem_orthogonalGroup (1 : Fin 4))).toMonoidHom =
      leviFixBar (plusPair K 0) (flipPair (plusPair K 1)) := by
  rw [leviFixBar, leviFixBar, map_conjProj_map_projHom,
    map_conj_leviFix (plusFlipLin_mem_orthogonalGroup (1 : Fin 4))
      (map_conj_orthDerived (plusFlipLin_mem_orthogonalGroup (1 : Fin 4)))]
  · exact plusFlipLin_inl_of_ne (by decide)
  · exact plusFlipLin_inr_of_ne (by decide)
  · exact plusFlipLin_inl_self 1
  · exact plusFlipLin_inr_self 1

end Flip

end CFSG.SeitzReduction.OmegaPilot
