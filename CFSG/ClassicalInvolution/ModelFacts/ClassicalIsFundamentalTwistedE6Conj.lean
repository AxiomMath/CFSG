module

public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalTwistedE6Model

public section

namespace CFSG.ClassicalInvolution.ModelFacts

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.Exceptional
  CFSG.LieType.Steinberg.Twist CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Abstract

variable {M : Type*} [Group M]

theorem map_conj_fixedPointsIn_of_fixed (A : Subgroup M) (F : M →* M) {u : M} (hFu : F u = u)
    (hA : A.map (MulAut.conj u).toMonoidHom = A) :
    (fixedPointsIn A F).map (MulAut.conj u).toMonoidHom = fixedPointsIn A F := by
  ext z
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨hyA, hyF⟩ := mem_fixedPointsIn.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine mem_fixedPointsIn.2 ⟨?_, ?_⟩
    · rw [← hA]
      exact Subgroup.mem_map_of_mem _ hyA
    · rw [map_mul, map_mul, map_inv, hyF, hFu]
  · intro hz
    obtain ⟨hzA, hzF⟩ := mem_fixedPointsIn.1 hz
    rw [← hA] at hzA
    obtain ⟨y, hyA, rfl⟩ := hzA
    refine ⟨y, mem_fixedPointsIn.2 ⟨hyA, ?_⟩, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hzF
    rw [map_mul, map_mul, map_inv, hFu] at hzF
    exact mul_left_cancel (mul_right_cancel hzF)

end Abstract

section Torus

variable {τ : Tag} {k : Type} [Field k]

theorem map_conj_rootSubgroup_of_torus {u : ModGL τ k} (hu : u ∈ torusGroup τ k)
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (rootSubgroup τ k γ).map (MulAut.conj u).toMonoidHom = rootSubgroup τ k γ := by
  obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hu
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [rootDiagUnit_conj_pinnedX a hγ]
    exact mem_rootSubgroup.2 ⟨_, rfl⟩
  · intro z hz
    obtain ⟨c, rfl⟩ := mem_rootSubgroup.1 hz
    refine ⟨pinnedX τ k γ ((((rootChar a γ)⁻¹ : kˣ) : k) * c), mem_rootSubgroup.2 ⟨_, rfl⟩, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [rootDiagUnit_conj_pinnedX a hγ, ← mul_assoc, Units.mul_inv, one_mul]

theorem map_conj_fixedPointsIn_rootSubgroup_of_torus (F : ModGL τ k →* ModGL τ k) {u : ModGL τ k}
    (hu : u ∈ torusGroup τ k) (hFu : F u = u) {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) :
    (fixedPointsIn (rootSubgroup τ k γ) F).map (MulAut.conj u).toMonoidHom =
      fixedPointsIn (rootSubgroup τ k γ) F :=
  map_conj_fixedPointsIn_of_fixed _ F hFu (map_conj_rootSubgroup_of_torus hu hγ)

end Torus

section Component

variable {M : Type*} [Group M]

theorem isPComponent_inf_centralizer_of_isPComponent (H : Subgroup M) (y : ↥H) {L' : Subgroup ↥H}
    (hL' : L' ≤ Subgroup.centralizer ({y} : Set ↥H)) {p : ℕ}
    (h : CFSG.IsPComponent p (L'.subgroupOf (Subgroup.centralizer ({y} : Set ↥H)))) :
    CFSG.IsPComponent p
      ((L'.map H.subtype).subgroupOf (H ⊓ Subgroup.centralizer ({(y : M)} : Set M))) := by
  have hmap : (Subgroup.centralizer ({y} : Set ↥H)).map H.subtype =
      H ⊓ Subgroup.centralizer ({(y : M)} : Set M) := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.2, congrArg Subtype.val hc⟩
    · rintro ⟨hwH, hwy⟩
      exact ⟨⟨w, hwH⟩, Subtype.ext hwy, rfl⟩
  let e : ↥(Subgroup.centralizer ({y} : Set ↥H)) ≃*
      ↥(H ⊓ Subgroup.centralizer ({(y : M)} : Set M)) :=
    (Subgroup.equivMapOfInjective _ H.subtype H.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have h1 := isPComponent_map_of_isPComponent p e h
  have h2 : (L'.subgroupOf (Subgroup.centralizer ({y} : Set ↥H))).map e.toMonoidHom =
      (L'.map H.subtype).subgroupOf (H ⊓ Subgroup.centralizer ({(y : M)} : Set M)) := by
    ext w
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨c, hc, rfl⟩
      exact ⟨c.1, hc, rfl⟩
    · rintro ⟨v, hv, hvw⟩
      exact ⟨⟨v, hL' hv⟩, hv, Subtype.ext hvw⟩
  rwa [h2] at h1

end Component

section Decomposition

variable (p f : ℕ) [Fact p.Prime]

theorem twistedE6Phi_mem_fixedPointsIn (hp2 : p ≠ 2) (hf : 1 ≤ f) (x : twistedE6Group p f) :
    twistedE6Phi p f (AlgebraicClosure (GaloisField p (2 * f))) x ∈
      fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))))
        (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
          (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f))))) := by
  have h1 : twistedE6Phi p f (AlgebraicClosure (GaloisField p (2 * f))) x ∈
      (twistedE6Phi p f (AlgebraicClosure (GaloisField p (2 * f)))).range := ⟨x, rfl⟩
  rw [range_twistedE6Phi p f hp2 hf] at h1
  refine Subgroup.commutator_le.2 (fun a ha b hb => ?_) h1
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem exists_torus_mul_of_mem_fixedPointsIn (hp2 : p ≠ 2) (hf : 1 ≤ f)
    {g : ModGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f)))}
    (hg : g ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))))
      (frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
        (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f)))))) :
    ∃ u ∈ torusGroup TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))),
      frobTwistGL TwistTag.E6.tag (AlgebraicClosure (GaloisField p (2 * f))) p f
        (diagramMap TwistTag.E6 (AlgebraicClosure (GaloisField p (2 * f)))) u = u ∧
      ∃ x : twistedE6Group p f,
        g = u * twistedE6Phi p f (AlgebraicClosure (GaloisField p (2 * f))) x := by
  classical
  set K0 := GaloisField p (2 * f) with hK0
  set k := AlgebraicClosure K0 with hk
  have hodd : Odd (p ^ f) := (Nat.Prime.eq_two_or_odd' Fact.out |>.resolve_left hp2).pow
  have hK : Nat.card K0 = (p ^ f) ^ TwistTag.E6.order := card_galoisField_two_mul' p f hf
  have hChark : CharP k p := charP_of_injective_algebraMap (algebraMap K0 k).injective p
  have hFr : ∀ c : k, iterateFrobenius k p f c = c ^ (p ^ f) := fun c => iterateFrobenius_def p f c
  have hσ : ∀ c : K0, frobQ p f c = c ^ (p ^ f) := fun c => frobQ_apply p f c
  obtain ⟨-, -, -, -, hmul, -, hder⟩ := odd_diagram_Frobenius_fixed_derived_root_group
    TwistTag.E6 (Fact.out : p.Prime) hf hodd K0 hK (frobQ p f) hσ k (iterateFrobenius k p f) hFr
  have hg' : g ∈ (twistedFixedGroup TwistTag.E6 k (iterateFrobenius k p f) :
      Set (ModGL TwistTag.E6.tag k)) := hg
  rw [hmul] at hg'
  obtain ⟨u, hu, h', hh', rfl⟩ := hg'
  have hrange := range_twistedE6Phi p f hp2 hf
  have hh'R : h' ∈ (twistedE6Phi p f k).range := by
    rw [hrange]
    exact hder ▸ hh'
  obtain ⟨x, hx⟩ := hh'R
  obtain ⟨huT, huF⟩ := Subgroup.mem_inf.1 hu
  exact ⟨u, huT, huF.2, x, by rw [hx]⟩

end Decomposition

end CFSG.ClassicalInvolution.ModelFacts
