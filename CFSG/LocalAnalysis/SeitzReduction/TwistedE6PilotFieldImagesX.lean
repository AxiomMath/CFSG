module

public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotFieldYRigid

public section

set_option linter.unusedSectionVars false

namespace CFSG.SeitzReduction.TwistedE6Pilot

open Subgroup CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.C2E6Std CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.LieType.Steinberg.Adjoint (iform iform_smul_left iform_smul_right)
open CFSG.Quasithin (perfectCore)
open CFSG.SeitzReduction.F4Pilot (centralizerPerfectCore)

local instance twistedE6PilotFieldImagesXNeZero : NeZero TwistTag.E6.tag.rank := ⟨by decide⟩

local instance twistedE6PilotFieldImagesXNeZeroF4 : NeZero Tag.F4.rank := ⟨by decide⟩

local instance twistedE6PilotFieldImagesXNeZeroE6 : NeZero Tag.E6.rank := ⟨by decide⟩

variable {K : Type} [Field K]

@[expose] def xPrimeWTuple (B : Fin Tag.F4.rank → Kˣ) : Fin Tag.F4.rank → Kˣ :=
  ![B 1, (B 0)⁻¹ * (B 1)⁻¹, B 0 * B 1 * B 2, B 3]

theorem relTuple_eq_vec (B : Fin Tag.F4.rank → Kˣ) :
    relTuple B = (![B 3, B 0, B 2, B 1, B 2, B 3] : Fin 6 → Kˣ) := by
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := e6IndexToF4_values
  funext j
  revert j
  change ∀ j : Fin 6, B (e6IndexToF4 j) = (![B 3, B 0, B 2, B 1, B 2, B 3] : Fin 6 → Kˣ) j
  intro j
  fin_cases j
  · exact congrArg B h0
  · exact congrArg B h1
  · exact congrArg B h2
  · exact congrArg B h3
  · exact congrArg B h4
  · exact congrArg B h5

section XPrime

theorem relWordXPrime_conj_rootDiagUnit_relTuple (B : Fin Tag.F4.rank → Kˣ) :
    twistedE6RelWeyl K relWordXPrime * rootDiagUnit TwistTag.E6.tag (relTuple B) *
        (twistedE6RelWeyl K relWordXPrime)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (relTuple (xPrimeWTuple B)) := by
  rw [twistedE6RelWeyl_relWordXPrime]
  calc weylElt TwistTag.E6.tag K 3 1 * weylElt TwistTag.E6.tag K 1 1 *
        rootDiagUnit TwistTag.E6.tag (relTuple B) *
        (weylElt TwistTag.E6.tag K 3 1 * weylElt TwistTag.E6.tag K 1 1)⁻¹ =
      weylElt TwistTag.E6.tag K 3 1 * (weylElt TwistTag.E6.tag K 1 1 *
        rootDiagUnit TwistTag.E6.tag (relTuple B) *
        (weylElt TwistTag.E6.tag K 1 1)⁻¹) * (weylElt TwistTag.E6.tag K 3 1)⁻¹ := by group
    _ = _ := by
      rw [E6Pilot.weylElt_one_conj_rootDiagUnit_eq, E6Pilot.weylElt_one_conj_rootDiagUnit_eq,
        relTuple_eq_vec, relTuple_eq_vec]
      congr 1
      funext j
      revert j
      change ∀ j : Fin 6, (![B 3, B 0, B 2, B 1, B 2, B 3] : Fin 6 → Kˣ) j *
          (![B 3, B 0, B 2, B 1, B 2, B 3] : Fin 6 → Kˣ) 1 ^ (-Tag.E6.cartan 1 j) *
          ((![B 3, B 0, B 2, B 1, B 2, B 3] : Fin 6 → Kˣ) 3 *
            (![B 3, B 0, B 2, B 1, B 2, B 3] : Fin 6 → Kˣ) 1 ^ (-Tag.E6.cartan 1 3)) ^
            (-Tag.E6.cartan 3 j) =
          (![xPrimeWTuple B 3, xPrimeWTuple B 0, xPrimeWTuple B 2, xPrimeWTuple B 1,
            xPrimeWTuple B 2, xPrimeWTuple B 3] : Fin 6 → Kˣ) j
      intro j
      fin_cases j
      · show B 3 * B 0 ^ (-(0 : ℤ)) * (B 1 * B 0 ^ (-(-1 : ℤ))) ^ (-(0 : ℤ)) = B 3
        simp
      · show B 0 * B 0 ^ (-(2 : ℤ)) * (B 1 * B 0 ^ (-(-1 : ℤ))) ^ (-(-1 : ℤ)) = B 1
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow]
        abel
      · show B 2 * B 0 ^ (-(0 : ℤ)) * (B 1 * B 0 ^ (-(-1 : ℤ))) ^ (-(-1 : ℤ)) =
          B 0 * B 1 * B 2
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow]
        abel
      · show B 1 * B 0 ^ (-(-1 : ℤ)) * (B 1 * B 0 ^ (-(-1 : ℤ))) ^ (-(2 : ℤ)) =
          (B 0)⁻¹ * (B 1)⁻¹
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow, ofMul_inv]
        abel
      · show B 2 * B 0 ^ (-(0 : ℤ)) * (B 1 * B 0 ^ (-(-1 : ℤ))) ^ (-(-1 : ℤ)) =
          B 0 * B 1 * B 2
        apply Additive.ofMul.injective
        simp only [ofMul_mul, ofMul_zpow]
        abel
      · show B 3 * B 0 ^ (-(0 : ℤ)) * (B 1 * B 0 ^ (-(-1 : ℤ))) ^ (-(0 : ℤ)) = B 3
        simp

end XPrime

@[expose] def xPrimeWInvTuple (C : Fin Tag.F4.rank → Kˣ) : Fin Tag.F4.rank → Kˣ :=
  ![(C 1)⁻¹ * (C 0)⁻¹, C 0, C 2 * C 1, C 3]

theorem xPrimeWTuple_xPrimeWInvTuple (C : Fin Tag.F4.rank → Kˣ) :
    xPrimeWTuple (xPrimeWInvTuple C) = C := by
  funext i
  revert i
  change ∀ i : Fin 4, xPrimeWTuple (xPrimeWInvTuple C) i = C i
  intro i
  fin_cases i <;> simp [xPrimeWTuple, xPrimeWInvTuple, mul_comm, mul_left_comm] <;> rfl

theorem xPrimeWTuple_mem {A : Subgroup Kˣ} {B : Fin Tag.F4.rank → Kˣ} (hB : ∀ i, B i ∈ A) :
    ∀ i, xPrimeWTuple B i ∈ A := by
  change ∀ i : Fin 4, xPrimeWTuple B i ∈ A
  intro i
  fin_cases i
  · exact hB 1
  · exact mul_mem (inv_mem (hB 0)) (inv_mem (hB 1))
  · exact mul_mem (mul_mem (hB 0) (hB 1)) (hB 2)
  · exact hB 3

theorem xPrimeWInvTuple_mem {A : Subgroup Kˣ} {C : Fin Tag.F4.rank → Kˣ} (hC : ∀ i, C i ∈ A) :
    ∀ i, xPrimeWInvTuple C i ∈ A := by
  change ∀ i : Fin 4, xPrimeWInvTuple C i ∈ A
  intro i
  fin_cases i
  · exact mul_mem (inv_mem (hC 1)) (inv_mem (hC 0))
  · exact hC 0
  · exact mul_mem (hC 2) (hC 1)
  · exact hC 3

section Tori

theorem map_conj_relWordXPrime_relLeviTorus_of {A : Subgroup Kˣ}
    {I I' : Finset (Fin Tag.F4.rank)}
    (h : ∀ B : Fin Tag.F4.rank → Kˣ, (∀ j ∈ I, B j = 1) → ∀ j ∈ I', xPrimeWTuple B j = 1)
    (h' : ∀ C : Fin Tag.F4.rank → Kˣ, (∀ j ∈ I', C j = 1) → ∀ j ∈ I,
      xPrimeWInvTuple C j = 1) :
    (relLeviTorus K A I).map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom =
      relLeviTorus K A I' := by
  ext g
  simp only [mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨_, hx, rfl⟩
    obtain ⟨B, ⟨hB1, hBA⟩, rfl⟩ := mem_relLeviTorus.1 hx
    rw [relWordXPrime_conj_rootDiagUnit_relTuple]
    exact rootDiagUnit_relTuple_mem_relLeviTorus ⟨h B hB1, xPrimeWTuple_mem hBA⟩
  · intro hg
    obtain ⟨C, ⟨hC1, hCA⟩, rfl⟩ := mem_relLeviTorus.1 hg
    refine ⟨_, rootDiagUnit_relTuple_mem_relLeviTorus ⟨h' C hC1, xPrimeWInvTuple_mem hCA⟩, ?_⟩
    rw [relWordXPrime_conj_rootDiagUnit_relTuple, xPrimeWTuple_xPrimeWInvTuple]

theorem map_conj_relWordXPrime_relLeviTorus_a2 (A : Subgroup Kˣ) :
    (relLeviTorus K A {1}).map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom =
      relLeviTorus K A {0} := by
  refine map_conj_relWordXPrime_relLeviTorus_of (fun B hB j hj => ?_) fun C hC j hj => ?_
  · rw [Finset.mem_singleton.1 hj]
    exact hB 1 (Finset.mem_singleton_self _)
  · rw [Finset.mem_singleton.1 hj]
    exact hC 0 (Finset.mem_singleton_self _)

theorem map_conj_relWordXPrime_relLeviTorus_a4 (A : Subgroup Kˣ) :
    (relLeviTorus K A {3}).map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom =
      relLeviTorus K A {3} := by
  refine map_conj_relWordXPrime_relLeviTorus_of (fun B hB j hj => ?_) fun C hC j hj => ?_
  · rw [Finset.mem_singleton.1 hj]
    exact hB 3 (Finset.mem_singleton_self _)
  · rw [Finset.mem_singleton.1 hj]
    exact hC 3 (Finset.mem_singleton_self _)

end Tori

section Commuting

theorem forall_commute_rootSpan_of_iform {S₁ S₂ : Set (Fin TwistTag.E6.tag.rank → ℤ)}
    (h : ∀ α ∈ S₁, ∀ β ∈ S₂, IsRoot TwistTag.E6.tag α ∧ IsRoot TwistTag.E6.tag β ∧
      iform α β = 0) :
    ∀ x ∈ rootSpan TwistTag.E6.tag K S₁, ∀ y ∈ rootSpan TwistTag.E6.tag K S₂, Commute x y := by
  have hle : rootSpan TwistTag.E6.tag K S₁ ≤
      centralizer (rootSpan TwistTag.E6.tag K S₂ : Set (ModGL TwistTag.E6.tag K)) := by
    refine iSup₂_le fun α hα => le_centralizer_iff.2 (iSup₂_le fun β hβ => ?_)
    intro y hy
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨hα', hβ', h0⟩ := h α hα β hβ
    exact (EPilot.commute_of_iform_eq_zero (Or.inl rfl) hα' hβ' h0 hx hy).eq
  intro x hx y hy
  exact (mem_centralizer_iff.1 (hle hx) y hy).symm

theorem forall_commute_relLevi_of_check {I I' : Finset (Fin Tag.F4.rank)}
    (hII' : ∀ i j : Fin Tag.E6.rank, e6IndexToF4 i ∈ I → e6IndexToF4 j ∈ I' →
      iform (Pi.single i 1 : Fin Tag.E6.rank → ℤ) (Pi.single j 1) = 0) :
    ∀ x ∈ relLevi K I, ∀ y ∈ relLevi K I', Commute x y := by
  refine forall_commute_rootSpan_of_iform fun α hα β hβ => ?_
  obtain ⟨i, hi, hαi⟩ := hα
  obtain ⟨j, hj, hβj⟩ := hβ
  refine ⟨F4Pilot.isRoot_of_mem_signedSimpleRoots ⟨i, hi, hαi⟩,
    F4Pilot.isRoot_of_mem_signedSimpleRoots ⟨j, hj, hβj⟩, ?_⟩
  have h0 : iform (Pi.single i 1 : Fin TwistTag.E6.tag.rank → ℤ) (Pi.single j 1) = 0 :=
    hII' i j (mem_relNodeSet.1 hi) (mem_relNodeSet.1 hj)
  have hneg : ∀ v : Fin TwistTag.E6.tag.rank → ℤ, -v = (-1 : ℤ) • v :=
    fun v => (neg_one_smul ℤ v).symm
  rcases hαi with rfl | rfl <;> rcases hβj with rfl | rfl
  · exact h0
  · rw [hneg, iform_smul_right, h0, mul_zero]
  · rw [hneg, iform_smul_left, h0, mul_zero]
  · rw [hneg, hneg, iform_smul_left, iform_smul_right, h0, mul_zero, mul_zero]

theorem forall_commute_relLevi_a2_a4 : ∀ x ∈ relLevi K {1}, ∀ y ∈ relLevi K {3}, Commute x y :=
  forall_commute_relLevi_of_check (by decide)

theorem forall_commute_relLevi_a1_a3 : ∀ x ∈ relLevi K {0}, ∀ y ∈ relLevi K {2}, Commute x y :=
  forall_commute_relLevi_of_check (by decide)

end Commuting

section Pieces

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {σ : K →+* K}

@[expose] noncomputable def xPrimeWeyl (σ : K →+* K) : graphFixedRootGroup TwistTag.E6 K σ :=
  ⟨twistedE6RelWeyl K relWordXPrime, twistedE6RelWeyl_mem σ relWordXPrime⟩

theorem pieceCore_eq_map_conj_of (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ) (A : Subgroup Kˣ)
    {I I' : Finset (Fin Tag.F4.rank)}
    (h : (relLeviTorus K A I).map (MulAut.conj (twistedE6RelWeyl K relWordXPrime)).toMonoidHom =
      relLeviTorus K A I') :
    pieceCore e A I' = (pieceCore e A I).map
      (MulAut.conj ((e.symm (xPrimeWeyl σ) : L) : G)).toMonoidHom := by
  rw [pieceCore, pieceCore, F4Pilot.map_centralizerPerfectCore, ← modelToG_map_conj, ← h]
  rfl

theorem pieceCore_a1_eq_map_conj (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (A : Subgroup Kˣ) :
    pieceCore e A {0} = (pieceCore e A {1}).map
      (MulAut.conj ((e.symm (xPrimeWeyl σ) : L) : G)).toMonoidHom :=
  pieceCore_eq_map_conj_of e A (map_conj_relWordXPrime_relLeviTorus_a2 A)

theorem pieceCore_a4_eq_map_conj (e : L ≃* graphFixedRootGroup TwistTag.E6 K σ)
    (A : Subgroup Kˣ) :
    pieceCore e A {3} = (pieceCore e A {3}).map
      (MulAut.conj ((e.symm (xPrimeWeyl σ) : L) : G)).toMonoidHom :=
  pieceCore_eq_map_conj_of e A (map_conj_relWordXPrime_relLeviTorus_a4 A)

end Pieces

section Neighbours

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ}

theorem forall_commute_map_map {M : Subgroup (ModGL TwistTag.E6.tag K)} {E : Subgroup G}
    (Φ : M ≃* E) {H₁ H₂ : Subgroup (ModGL TwistTag.E6.tag K)}
    (h : ∀ x ∈ H₁, ∀ y ∈ H₂, Commute x y) :
    ∀ x ∈ ((H₁.subgroupOf M).map Φ.toMonoidHom).map E.subtype,
      ∀ y ∈ ((H₂.subgroupOf M).map Φ.toMonoidHom).map E.subtype, Commute x y := by
  rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩ _ ⟨_, ⟨v, hv, rfl⟩, rfl⟩
  have huv : Commute u v := Subtype.ext (h _ (mem_subgroupOf.1 hu) _ (mem_subgroupOf.1 hv)).eq
  exact (huv.map Φ.toMonoidHom).map E.subtype

theorem commute_pieceCore_a1_a3 (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {σ : K →+* K}
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {e : L ≃* graphFixedRootGroup TwistTag.E6 K σ} {t : G}
    (htL : t ∈ centralizer (L : Set G)) {A : Subgroup Kˣ}
    (hY : FieldNeighbourIso2E6 e t (modelToG e (neighbourTorus K A .Y))
      (subsystemGroup TwistTag.E6.tag K setD) (d4LeviTwist (apply_apply_eq hK hσ))
        (omegaMinusLevi σ))
    (hA3 : 3 ≤ Nat.card A) (hAσ : ∀ c ∈ A, Units.map σ.toMonoidHom c = c) {m : ℕ} (hm : Odd m)
    (hAm : ∀ c ∈ A, c ^ m = 1) :
    ∀ x ∈ pieceCore e A {0}, ∀ y ∈ pieceCore e A {2}, Commute x y := by
  rw [hY.pieceCore_eq_map_relLevi_Y' hf hK hσ htL hA3 hAσ hm hAm (by decide) (by decide)
      (modelToG_mono e (neighbourTorus_le_relLeviTorus A .Y (by decide))),
    hY.pieceCore_eq_map_relLevi_Y' hf hK hσ htL hA3 hAσ hm hAm (by decide) (by decide)
      (modelToG_mono e (neighbourTorus_le_relLeviTorus A .Y (by decide)))]
  exact forall_commute_map_map hY.Φ forall_commute_relLevi_a1_a3

end Neighbours

end CFSG.SeitzReduction.TwistedE6Pilot
