module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265BSClTwo
public import CFSG.HardMathSupport.Dickson.Bal207.LocalBalClassicalOrthTwoLocal
public import CFSG.HardMathSupport.Dickson.I271.Support.EngineKL

public section

namespace CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

open Module QuadraticMap CFSG.Open CFSG.RankThree.Classical2 CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Dickson.Bal207.OrthRow.Two

variable {F V : Type} [Field F] [Finite F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {Q : QuadraticForm F V}

private theorem glaPLayer_ne_bot_of_normal {G : Type} [Group G] [Finite G] {C J : Subgroup G}
    (hJC : J ≤ C) (hJn : ∀ g ∈ C, ∀ f ∈ J, g * f * g⁻¹ ∈ J) (hq : CFSG.IsQuasisimple ↥J)
    (hN : NoNormalPPrime 3 J) : GLAPLayer 3 C ≠ ⊥ := by
  have hne : J ≠ ⊥ := by
    intro hbot
    obtain ⟨u, w, huw⟩ := hq.2.2
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective u
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
    have h1 : ∀ z : ↥J, z = 1 := fun z =>
      Subtype.ext ((Subgroup.eq_bot_iff_forall _).1 hbot _ z.2)
    exact huw (by rw [h1 u, h1 w])
  have h3 : 3 ∣ Nat.card ↥J := by
    by_contra hnd
    exact hne (hN J le_rfl (fun y hy x hx => J.mul_mem (J.mul_mem hy hx) (J.inv_mem hy))
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hnd))
  have hJn' : (J.subgroupOf C).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hJn _ g.2 _ hn⟩
  have hJq : CFSG.Open.IsQuasisimple ↥J :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq)
  have hcomp : GLAPComponent 3 C J :=
    CFSG.HardMathSupport.Dickson.I271.glaPComponent_of_normal Nat.prime_three hJq h3 hJC hJn'
  intro hL
  have hle : J ≤ GLAPLayer 3 C := le_sSup hcomp
  rw [hL, le_bot_iff] at hle
  exact hne hle

theorem glaPLayer_inf_ne_bot_of_specialBlock (hF : Nat.card F = 2)
    (hQ : (polarBilin Q).Nondegenerate) {a e : V ≃ₗ[F] V} (haQ : ∀ v, Q (a v) = Q v)
    (ha3 : a ^ 3 = 1) (hae : a * e = e * a)
    (hdim : finrank F ↥(fixedSpace a) + 8 ≤ finrank F V)
    (he : ∀ v ∈ primaryComponent a.toLinearMap (cyc3 F), e v = v)
    {X : Subgroup (V ≃ₗ[F] V)} (hX : specialBlock Q a (cyc3 F) ≤ X)
    (hXQ : ∀ g ∈ X, g * a = a * g → g * e = e * g → ∀ v, Q (g v) = Q v) :
    GLAPLayer 3 (X ⊓ Subgroup.centralizer ({a} : Set (V ≃ₗ[F] V)) ⊓
      Subgroup.centralizer ({e} : Set (V ≃ₗ[F] V))) ≠ ⊥ := by
  classical
  haveI := charP_two hF
  haveI : Finite V := Module.finite_of_finite F
  haveI : Finite (V ≃ₗ[F] V) := Finite.of_injective (fun g : V ≃ₗ[F] V => (g : V → V))
    fun g g' h => LinearEquiv.ext (congrFun h)
  have hx : OddOrderIsometry Q 3 a :=
    ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 haQ, ha3, cast_three_ne_zero_of_card_two hF,
      fun v hv => hQ.1 v hv⟩
  haveI : Fact (Irreducible (cyc3 F)) := ⟨irreducible_cyc3 hF⟩
  have hcompl := isCompl_fixedSpace_cyc3 hF hx
  have hc := Submodule.finrank_add_eq_of_isCompl hcompl
  have hm := finrank_cyc3 (x := a) hF
  have hm4 : 4 ≤ primaryMultiplicity a.toLinearMap (cyc3 F) := by omega
  have hh := cyc3_mem_primaryFactors (x := a) hF (by omega)
  have hJc := specialBlock_le_isometryCentralizer (Q := Q) (x := a) (cyc3 F)
  have hWe : ∀ w ∈ fixedSpace a, e w ∈ fixedSpace a := fun w hw => by
    rw [mem_fixedSpace] at hw ⊢
    have h := LinearEquiv.congr_fun hae w
    simp only [LinearEquiv.mul_apply, hw] at h
    exact h
  have hJe : ∀ j ∈ specialBlock Q a (cyc3 F), j * e = e * j := fun j hj => by
    have hjW := fixes_fixedSpace_of_mem_supportedBlock_cyc3
      (specialBlock_le_supportedBlock (Q := Q) (x := a) (cyc3 F) hj)
    have hja : j * a = a * j :=
      Subgroup.mem_centralizer_singleton_iff.1 (Subgroup.mem_inf.1 (hJc hj)).2
    have hcomm : Commute (j : V →ₗ[F] V) (a : V →ₗ[F] V) :=
      LinearMap.ext fun v => LinearEquiv.congr_fun hja v
    ext v
    obtain ⟨w, hw, r, hr, rfl⟩ := exists_add_of_isCompl hcompl v
    simp only [LinearEquiv.mul_apply, map_add]
    rw [he r hr, hjW w hw, hjW (e w) (hWe w hw), he (j r) (apply_mem_primaryComponent hcomm hr)]
  refine glaPLayer_ne_bot_of_normal (J := specialBlock Q a (cyc3 F)) (fun j hj => ?_)
    (fun g hg f hf => ?_) (orth2_isQuasisimple_specialBlock_selfDual hx (by decide) hh
      (cyc3_ne_X_sub_one F) (reciprocal_cyc3 F).symm hm4)
    (noNormalPPrime_specialBlock_cyc3 hF hx hh)
  · exact ⟨⟨hX hj, (Subgroup.mem_inf.1 (hJc hj)).2⟩,
      Subgroup.mem_centralizer_singleton_iff.2 (hJe j hj)⟩
  · obtain ⟨⟨hgX, hga⟩, hge⟩ := hg
    exact conj_mem_specialBlock (Subgroup.mem_inf.2 ⟨TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2
      (hXQ g hgX (Subgroup.mem_centralizer_singleton_iff.1 hga)
        (Subgroup.mem_centralizer_singleton_iff.1 hge)), hga⟩) hf

end CFSG.LocalAnalysis.GLTheoremA.S265.BSCl

end
