module

public import CFSG.ClassicalInvolution.Q3.Q3ExcE6Conj
public import CFSG.ClassicalInvolution.Q3.Q3ExcTwoOrbit
public import CFSG.ClassicalInvolution.Q3.Q3ExcE6
public import CFSG.ClassicalInvolution.Q3.Q3ExcE6Data

public section

namespace CFSG.ClassicalInvolution.Q3

open CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.ToralSign
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.ClassicalInvolution.ModelFacts
open scoped MatrixGroups

section Group

variable {G : Type*} [Group G] {R H : Subgroup G}

theorem exc3_pow_three_mem (hHn : ∀ g ∈ R, ∀ a ∈ H, g * a * g⁻¹ ∈ H)
    (hdec : ∀ g ∈ R, ∃ u ∈ R, u ^ 8 = 1 ∧ ∃ a ∈ H, g = u * a) {z : G} (hz : z ∈ R)
    (hz3 : z ^ 3 = 1) : z ∈ H := by
  obtain ⟨u, hu, hu8, a, ha, rfl⟩ := hdec z hz
  have hu1 : u⁻¹ ∈ R := R.inv_mem hu
  have hc1 : u⁻¹ * a * u ∈ H := by simpa using hHn u⁻¹ hu1 a ha
  have hc2 : u⁻¹ * u⁻¹ * a * (u * u) ∈ H := by
    have := hHn (u⁻¹ * u⁻¹) (R.mul_mem hu1 hu1) a ha
    simpa [mul_assoc] using this
  have hu3 : u ^ 3 = (u⁻¹ * u⁻¹ * a * (u * u) * (u⁻¹ * a * u) * a)⁻¹ := by
    have h : u ^ 3 * (u⁻¹ * u⁻¹ * a * (u * u) * (u⁻¹ * a * u) * a) = 1 := by
      calc u ^ 3 * (u⁻¹ * u⁻¹ * a * (u * u) * (u⁻¹ * a * u) * a) =
          (u * a) * (u * a) * (u * a) := by group
        _ = (u * a) ^ 3 := (pow_three' _).symm
        _ = 1 := hz3
    exact eq_inv_of_mul_eq_one_left h
  have hu3H : u ^ 3 ∈ H := by
    rw [hu3]
    exact H.inv_mem (H.mul_mem (H.mul_mem hc2 hc1) ha)
  have huH : u ∈ H := by
    have : u = (u ^ 3) ^ 3 := by
      calc u = u ^ 8 * u := by rw [hu8, one_mul]
        _ = (u ^ 3) ^ 3 := by group
    rw [this]
    exact H.pow_mem hu3H 3
  exact H.mul_mem huH ha

end Group

section Small

variable {τ : Tag} {p₀ : ℕ} [Fact p₀.Prime] {k : Type} [Field k] [CharP k p₀] [IsAlgClosed k]

theorem exc3_small_orbit_data (D : OrthogonalSemilinearFixedRootDatum τ p₀ k)
    {β : Fin τ.rank → ℤ} (hO : D.orbits = {{β}}) :
    β ∈ kernelRoots D.χ ∧ D.θ (toReal β) = toReal β ∧ Nat.card (D.orbitField {β}) = D.q ∧
      ∀ y : ModGL τ k, y ∈ D.orbitGroup ↔ ∃ A : SL2 (D.orbitField {β}),
        y = rootSL2 τ k β (Matrix.SpecialLinearGroup.map (D.orbitField {β}).subtype A) := by
  have hOm : ({β} : Set (Fin τ.rank → ℤ)) ∈ D.orbits := by rw [hO]; exact Set.mem_singleton _
  have hOm' := hOm
  obtain ⟨β', hβ', hββ'⟩ := hOm'
  obtain rfl : β' = β := by
    have : β' ∈ ({β} : Set (Fin τ.rank → ℤ)) := by
      rw [hββ']
      exact self_mem_thetaOrbit _ _
    exact this
  have hβK := D.mem_kernelRoots_of_mem_simpleRootsJ hβ'
  have hcard1 : OrthogonalSemilinearFixedRootDatum.orbitCard ({β'} : Set (Fin τ.rank → ℤ)) = 1 :=
    Set.ncard_singleton β'
  refine ⟨hβK, ?_, ?_, ?_⟩
  · obtain ⟨he, hmemO, -⟩ := D.thetaPowVec_spec hβK 1
    rw [← hββ', Set.mem_singleton_iff] at hmemO
    rw [pow_one] at he
    rw [← he, hmemO]
  · have h := D.card_orbitField hOm
    rwa [hcard1, pow_one] at h
  · intro y
    have hroot : OrthogonalSemilinearFixedRootDatum.orbitRoot ({β'} : Set (Fin τ.rank → ℤ)) =
        β' := Set.mem_singleton_iff.1 (D.orbitRoot_mem hOm)
    rw [← SetLike.mem_coe, ← D.range_orbitMap_eq_of_orbits_eq hO]
    constructor
    · rintro ⟨A, rfl⟩
      refine ⟨A, ?_⟩
      rw [orbitMap_of_orbitCard_eq_one D hcard1, hroot]
    · rintro ⟨A, rfl⟩
      refine ⟨A, ?_⟩
      rw [orbitMap_of_orbitCard_eq_one D hcard1, hroot]

end Small

section Core

variable {p : ℕ} [Fact p.Prime] {k : Type} [Field k] [IsAlgClosed k] [CharP k p]

theorem e6tw_core (hp2 : p ≠ 2) {e : ℕ} (he : 1 ≤ e) (hq3 : p ^ e = 3)
    (hk : letI := ZMod.algebra k p; Algebra.IsAlgebraic (ZMod p) k)
    (hdec : ∀ g ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
        (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
      ∃ u ∈ torusGroup TwistTag.E6.tag k,
        frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) u = u ∧
        ∃ a ∈ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
            fixedPointsIn (adjointGroup TwistTag.E6.tag k)
              (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆, g = u * a)
    {x : ModGL TwistTag.E6.tag k}
    (hxR : x ∈ fixedPointsIn (adjointGroup TwistTag.E6.tag k)
      (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)))
    (hx2 : x ^ 2 = 1) (hx1 : x ≠ 1) :
    ∃ g₁ ∈ adjointGroup TwistTag.E6.tag k,
      frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) g₁ = g₁ ∧
      (∀ N : Subgroup (ModGL TwistTag.E6.tag k),
        N ≤ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
            fixedPointsIn (adjointGroup TwistTag.E6.tag k)
              (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
          Subgroup.centralizer {x} →
        (∀ y ∈ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
            (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
              fixedPointsIn (adjointGroup TwistTag.E6.tag k)
                (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
            Subgroup.centralizer {x}, ∀ n ∈ N, y * n * y⁻¹ ∈ N) →
        Odd (Nat.card N) → N = ⊥) ∧
      (∀ L : Subgroup (ModGL TwistTag.E6.tag k),
        L ≤ ⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
            fixedPointsIn (adjointGroup TwistTag.E6.tag k)
              (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
          Subgroup.centralizer {x} →
        Nonempty (SL(2, ZMod 3) ≃* L) →
        IsSubnormal L (⁅fixedPointsIn (adjointGroup TwistTag.E6.tag k)
          (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)),
            fixedPointsIn (adjointGroup TwistTag.E6.tag k)
              (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))⁆ ⊓
          Subgroup.centralizer {x}) →
        ∃ β : Fin TwistTag.E6.tag.rank → ℤ, IsRoot TwistTag.E6.tag β ∧
          permLattice TwistTag.E6.perm β = β ∧
          L = (fixedPointsIn (rootSubgroup TwistTag.E6.tag k β)
              (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k)) ⊔
            fixedPointsIn (rootSubgroup TwistTag.E6.tag k (-β))
              (frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k))).map
                (MulAut.conj g₁⁻¹).toMonoidHom) := by
  classical
  have hk2 : ringChar k ≠ 2 := by
    rw [ringChar.eq k p]
    exact hp2
  obtain ⟨r, hr, D, h, g₁, s, hg₁G, hhT, hFg₁, hFs, hg₁x, hDχ, hDe, hDθ, hDF, hcent⟩ :=
    exc3_e6_datum_conj p hp2 hk he hxR hx2
  set F := frobTwistGL TwistTag.E6.tag k p e (diagramMap TwistTag.E6 k) with hF
  set R := fixedPointsIn (adjointGroup TwistTag.E6.tag k) F with hR
  set u := rootDiagUnit TwistTag.E6.tag s with hu
  set w := u * g₁ with hw
  set c := h * diagramMap TwistTag.E6 k with hc_def
  have hRfin : Finite R := finite_fixedPointsIn_frobTwistGL p he (by decide)
    (units_map_entrywiseHom_diagramMap (t := TwistTag.E6) (iterateFrobenius k p e))
    (diagramMap_pow_order TwistTag.E6 k)
  have hdn : diagramMap TwistTag.E6 k ∈
      Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL TwistTag.E6.tag k)) :=
    diagramMap_mem_normalizer TwistTag.E6
  have hd2 : diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k ∈
      torusGroup TwistTag.E6.tag k := by
    have h1 := diagramMap_pow_order TwistTag.E6 k
    rw [show TwistTag.E6.order = 2 from rfl, pow_two] at h1
    rw [h1]
    exact one_mem _
  have hcT : c ∈ Subgroup.normalizer (torusGroup TwistTag.E6.tag k : Set (ModGL _ k)) :=
    mul_mem (Subgroup.le_normalizer hhT) hdn
  have hc2 : c * c ∈ torusGroup TwistTag.E6.tag k := by
    have e : c * c = h * (diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹) *
        (diagramMap TwistTag.E6 k * diagramMap TwistTag.E6 k) := by
      rw [hc_def]
      group
    rw [e]
    exact mul_mem (mul_mem hhT ((Subgroup.mem_normalizer_iff.1 hdn h).1 hhT)) hd2
  have hfrob : Exc3Frob D c := ⟨fun y => by rw [hDe]; exact hDF y, hcT, hc2⟩
  have hcJ : ∀ J' : Set.range D.classOrbit, Exc3Frob (D.withOrbit J') c := fun J' =>
    ⟨hfrob.frob, hfrob.normalizes, hfrob.sq_mem⟩
  have hq3D : p ^ D.e = 3 := by rw [hDe]; exact hq3
  have hRsub : ⁅R, R⁆ ≤ R := Subgroup.commutator_le_of_le le_rfl le_rfl
  have hRconj : ∀ g ∈ R, R.map (MulAut.conj g).toMonoidHom = R := by
    intro g hg
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact R.mul_mem (R.mul_mem hg hz) (R.inv_mem hg)
    · intro hy
      refine ⟨g⁻¹ * y * g, R.mul_mem (R.mul_mem (R.inv_mem hg) hy) hg, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have hHn : ∀ g ∈ R, ∀ a ∈ ⁅R, R⁆, g * a * g⁻¹ ∈ ⁅R, R⁆ := by
    intro g hg a ha
    have := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom ha
    rwa [Subgroup.map_commutator, hRconj g hg] at this
  have hdec' : ∀ g ∈ R, ∃ u' ∈ R, u' ^ 8 = 1 ∧ ∃ a ∈ ⁅R, R⁆, g = u' * a := by
    intro g hg
    obtain ⟨u', hu'T, hu'F, a, ha, rfl⟩ := hdec g hg
    refine ⟨u', mem_fixedPointsIn.2 ⟨torusGroup_le_adjointGroup hu'T, hu'F⟩, ?_, a, ha, rfl⟩
    have := exc3_pow_eq_one_of_fixed_torus e hdn hd2 hu'T hu'F
    rw [hq3] at this
    simpa using this
  set G := ⁅R, R⁆ ⊓ Subgroup.centralizer {x} with hG
  set Y := G.map (MulAut.conj w).toMonoidHom with hY
  set Xh := D.totalFixedGroup.map (adjointGroup TwistTag.E6.tag k).subtype with hXh
  have hGfin : Finite G := Finite.of_injective
    (fun y : G => (⟨y.1, hRsub (Subgroup.mem_inf.1 y.2).1⟩ : R))
    (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
  have hYfin : Finite Y :=
    Finite.of_equiv _ (G.equivMapOfInjective _ (MulAut.conj w).injective).toEquiv
  have hYX : Y ≤ Xh := by
    rw [← hcent]
    exact Subgroup.map_mono (inf_le_inf_right _ hRsub)
  have hY2 : ∀ y ∈ Y, y ^ 2 ∈ Xh := fun y hy => Xh.pow_mem (hYX hy) 2
  have hYn : ∀ y ∈ Y, ∀ v ∈ Xh, y * v * y⁻¹ ∈ Xh := fun y hy v hv =>
    Xh.mul_mem (Xh.mul_mem (hYX hy) hv) (Xh.inv_mem (hYX hy))
  have hpull : ∀ y ∈ Xh, ∃ z ∈ R ⊓ Subgroup.centralizer ({x} : Set (ModGL _ k)),
      y = w * z * w⁻¹ := by
    intro y hy
    rw [← hcent] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    exact ⟨z, hz, rfl⟩
  have hCY : ∀ J' : Set.range D.classOrbit, (D.withOrbit J').orbitGroup ≤ Y := by
    intro J'
    set C := (D.withOrbit J').orbitGroup with hC
    have hCX : ∀ y ∈ C, y ∈ Xh := by
      intro y hy
      have h1 := (D.withOrbit J').orbitGroupC_le_fixedGroup
        ((D.withOrbit J').mk_mem_orbitGroupC hy)
      have h2 := D.kernelFixedGroup_le_totalFixedGroup
        (D.fixedGroup_withOrbit_le_kernelFixedGroup J' h1)
      exact ⟨_, h2, rfl⟩
    have hCHw : C ≤ (⁅R, R⁆).map (MulAut.conj w).toMonoidHom := by
      rcases exc3_orbitGroup_big_or_small (hcJ J') hq3D with hBig | ⟨hSm, -⟩
      · have hperf : ⁅C, C⁆ = C := Subgroup.isPerfect_iff.1 hBig.1.1
        set P := C.map (MulAut.conj w⁻¹).toMonoidHom with hP
        have hPR : P ≤ R := by
          rintro _ ⟨y', hy', rfl⟩
          obtain ⟨z', hz', hyz'⟩ := hpull y' (hCX y' hy')
          have e : (MulAut.conj w⁻¹).toMonoidHom y' = z' := by
            rw [hyz']
            simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
            group
          rw [e]
          exact (Subgroup.mem_inf.1 hz').1
        have hPperf : ⁅P, P⁆ = P := by rw [hP, ← Subgroup.map_commutator, hperf]
        have hPH : P ≤ ⁅R, R⁆ := by
          rw [← hPperf]
          exact Subgroup.commutator_mono hPR hPR
        intro y hy
        refine ⟨w⁻¹ * y * w, hPH ⟨y, hy, rfl⟩, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · obtain ⟨e⟩ := hSm
        have hgen := exc3_closure_pow_three_of_equiv e
        have hle : Subgroup.closure {y : C | y ^ 3 = 1} ≤
            ((⁅R, R⁆).map (MulAut.conj w).toMonoidHom).subgroupOf C := by
          refine (Subgroup.closure_le _).2 fun y hy => Subgroup.mem_subgroupOf.2 ?_
          have hy3 : (y : ModGL TwistTag.E6.tag k) ^ 3 = 1 := by
            have := congrArg Subtype.val hy
            simpa using this
          obtain ⟨z, hz, hyz⟩ := hpull y.1 (hCX y.1 y.2)
          have hz3 : z ^ 3 = 1 := by
            have h1 : w * z ^ 3 * w⁻¹ = 1 := by
              rw [← conj_pow, ← hyz]
              exact hy3
            calc z ^ 3 = w⁻¹ * (w * z ^ 3 * w⁻¹) * w := by group
              _ = 1 := by rw [h1]; group
          exact ⟨z, exc3_pow_three_mem hHn hdec' (Subgroup.mem_inf.1 hz).1 hz3, hyz.symm⟩
        intro y hy
        exact Subgroup.mem_subgroupOf.1 (hle (hgen ▸ Subgroup.mem_top (⟨y, hy⟩ : C)))
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hpull y (hCX y hy)
    obtain ⟨a, ha, hay⟩ := hCHw hy
    have haz : a = z := by
      have h1 : w * a * w⁻¹ = w * z * w⁻¹ := hay.trans hyz
      exact (MulAut.conj w).injective h1
    refine ⟨z, ⟨haz ▸ ha, (Subgroup.mem_inf.1 hz).2⟩, ?_⟩
    rw [hyz]
    rfl
  have hrmask : r.mask = 0 ∨ r.mask = 20 ∨ r.mask = 2 := by
    simp only [e6SignDiagramReps, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hmain : (∀ N : Subgroup (ModGL TwistTag.E6.tag k), N ≤ Y →
        (∀ y ∈ Y, ∀ n ∈ N, y * n * y⁻¹ ∈ N) → Odd (Nat.card N) → N = ⊥) ∧
      (∀ L : Subgroup (ModGL TwistTag.E6.tag k), L ≤ Y →
        Nonempty (SL(2, ZMod 3) ≃* L) → IsSubnormal L Y →
        ∃ J' : Set.range D.classOrbit, Exc3Small (D.withOrbit J').orbitGroup ∧
          L = (D.withOrbit J').orbitGroup) := by
    rcases hrmask with h0 | h20 | h2
    · exfalso
      apply hx1
      have e1 : rootDiagUnit TwistTag.E6.tag
          (signCharTuple (k := k) (signMaskChar TwistTag.E6.tag r.mask)) = 1 := by
        have e0 : signCharTuple (k := k) (signMaskChar TwistTag.E6.tag 0) = 1 := by
          funext j
          rw [signCharTuple, signMaskChar_single]
          simp
        rw [h0, e0]
        exact rootDiagUnit_one
      rw [e1] at hg₁x
      calc x = g₁⁻¹ * (g₁ * x * g₁⁻¹) * g₁ := by group
        _ = 1 := by rw [hg₁x]; group
    · have hχ : D.χ = signMaskChar TwistTag.E6.tag 20 := by rw [hDχ, h20]
      have : Subsingleton (KernelComponent (signMaskChar TwistTag.E6.tag 20)) :=
        e6_subsingleton_twenty
      obtain ⟨hA, hB⟩ := exc3_single_class_structure (τ := TwistTag.E6.tag) (Y := Y)
        (Or.inr (Or.inl rfl)) hfrob hq3D hχ
        e6_forall_exists_iform_twenty hCY hY2 hYn
      exact ⟨hA, fun L hL hS hLs => (hB L hL hS hLs).elim⟩
    · have hχ : D.χ = signMaskChar TwistTag.E6.tag 2 := by rw [hDχ, h2]
      obtain ⟨β₀, γ₁, hβ₀, hγ₁, hfix, hiso, hne1, hne2, hrest, hns⟩ := e6_twoClass_two
      have hθβ₀ : D.θ (toReal β₀) = toReal β₀ := (hDθ β₀).trans (congrArg toReal hfix)
      exact exc3_two_orbit_structure (τ := TwistTag.E6.tag) (Y := Y) (Or.inr (Or.inl rfl))
        hfrob hq3D hχ hβ₀ hγ₁ hiso hθβ₀ ⟨hne1, hne2⟩
        (fun γ hγ h1 h2 => ⟨0, γ₁, hγ₁, by simp, hrest γ hγ h1 h2⟩) (Or.inl hns) hCY hY2 hYn
  have hconjmap : ∀ H' : Subgroup (ModGL TwistTag.E6.tag k),
      (H'.map (MulAut.conj g₁).toMonoidHom).map (MulAut.conj u).toMonoidHom =
        H'.map (MulAut.conj w).toMonoidHom := by
    intro H'
    rw [Subgroup.map_map]
    congr 1
  refine ⟨g₁, hg₁G, hFg₁, ?_, ?_⟩
  · intro N hNG hNn hodd
    have hN' : N.map (MulAut.conj w).toMonoidHom = ⊥ := by
      refine hmain.1 _ (Subgroup.map_mono hNG) ?_ ?_
      · rintro _ ⟨y, hy, rfl⟩ _ ⟨n, hn, rfl⟩
        refine ⟨y * n * y⁻¹, hNn y (by simpa [hY] using hy) n hn, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_inv_rev]
        group
      · rw [← Nat.card_congr (N.equivMapOfInjective _ (MulAut.conj w).injective).toEquiv]
        exact hodd
    exact (Subgroup.map_eq_bot_iff_of_injective N (MulAut.conj w).injective).1 hN'
  · intro L hLG ⟨eL⟩ hLs
    have hLY : L.map (MulAut.conj w).toMonoidHom ≤ Y := Subgroup.map_mono hLG
    have hsub : IsSubnormal (L.map (MulAut.conj w).toMonoidHom) Y :=
      isSubnormal_map_conj hLs w
    obtain ⟨J', hS, hLeq⟩ := hmain.2 _ hLY
      ⟨eL.trans (L.equivMapOfInjective _ (MulAut.conj w).injective)⟩ hsub
    obtain ⟨β, hβ⟩ := exc3_small_orbits (hcJ J') hq3D hS
    obtain ⟨hβK, hθβ, hFq, hmemC⟩ := exc3_small_orbit_data (D.withOrbit J') hβ
    have hβroot : IsRoot TwistTag.E6.tag β := hβK.1
    have hfixβ : permLattice TwistTag.E6.perm β = β := by
      have h1 : D.θ (toReal β) = toReal β := hθβ
      have h2 := hDθ β
      rw [h1] at h2
      exact (toReal_injective h2).symm
    set J := L.map (MulAut.conj g₁).toMonoidHom with hJdef
    have hJF : ∀ y ∈ J, F y = y := by
      rintro _ ⟨l, hl, rfl⟩
      have hlR := (Subgroup.mem_inf.1 (hLG hl)).1
      have hlF : F l = l := (mem_fixedPointsIn.1 (hRsub hlR)).2
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [map_mul, map_mul, map_inv, hFg₁, hlF]
    have hFq' : Nat.card ((D.withOrbit J').orbitField {β}) = p ^ e := by
      rw [hFq]
      change p ^ D.e = p ^ e
      rw [hDe]
    have hJS : J = fixedPointsIn (rootSubgroup TwistTag.E6.tag k β) F ⊔
        fixedPointsIn (rootSubgroup TwistTag.E6.tag k (-β)) F := by
      refine eq_fixed_rootSubgroup_sup_of_conj p TwistTag.E6 he hβroot hfixβ s hJF
        (Fq := (D.withOrbit J').orbitField {β}) hFq' fun y => ?_
      rw [hu] at hconjmap
      rw [hconjmap L, hLeq]
      exact hmemC y
    refine ⟨β, hβroot, hfixβ, ?_⟩
    rw [← hJS, hJdef, Subgroup.map_map]
    have hid : (MulAut.conj g₁⁻¹).toMonoidHom.comp (MulAut.conj g₁).toMonoidHom =
        MonoidHom.id (ModGL TwistTag.E6.tag k) := by
      ext y
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv,
        MonoidHom.id_apply]
      group
    rw [hid, Subgroup.map_id]

end Core

end CFSG.ClassicalInvolution.Q3
