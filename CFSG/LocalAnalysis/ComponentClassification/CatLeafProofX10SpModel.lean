module

public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofOddInnerModels
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinearBranches

public noncomputable section

namespace CFSG.ComponentClassification.CatLeafProof.X10Sp

open CFSG Subgroup Module CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.ComponentClassification.CatalogueBSymplecticB
open LinearMap (BilinForm)

@[expose] def CentralModel (ℓ : ℕ) (t : StatedLieTag) (n f : ℕ) (L : Type) [Group L] : Prop :=
  StatedLieAdmissible t n ℓ f ∧ Blueprint.LieModel (L ⧸ center L) t n ℓ f

theorem CentralModel.of_mulEquiv {ℓ : ℕ} {t : StatedLieTag} {n f : ℕ} {L M : Type} [Group L]
    [Group M] (e : L ≃* M) (h : CentralModel ℓ t n f M) : CentralModel ℓ t n f L :=
  ⟨h.1, LieType.CurtisTits.lieModel_of_mulEquiv
    (QuotientGroup.congr _ _ e.symm (Subgroup.map_center_eq e.symm)) h.2⟩

theorem CentralModel.of_centerQuotient_equiv {ℓ : ℕ} {t : StatedLieTag} {n f : ℕ} {L M : Type}
    [Group L] [Group M] (e : L ⧸ center L ≃* M ⧸ center M) (h : CentralModel ℓ t n f M) :
    CentralModel ℓ t n f L :=
  ⟨h.1, LieType.CurtisTits.lieModel_of_mulEquiv e.symm h.2⟩

theorem centralModel_of_component_equiv {ℓ : ℕ} {t : StatedLieTag} {n f : ℕ} {G H : Type}
    [Group G] [Group H] (e : G ≃* H)
    (h : ∀ N : Subgroup H, IsComponent N → CentralModel ℓ t n f N) {M : Subgroup G}
    (hM : IsComponent M) : CentralModel ℓ t n f M :=
  (h _ (LocalCores.isComponent_map_mulEquiv e hM)).of_mulEquiv
    (M.equivMapOfInjective e.toMonoidHom e.injective)

theorem centralModel_statedSp {k : Type} [Field k] [Finite k] {ℓ j m : ℕ}
    (hadm : StatedLieAdmissible .PSp m ℓ j) (hk : Nat.card k = ℓ ^ j) :
    CentralModel ℓ .PSp m j (StatedSp m k) :=
  ⟨hadm, Or.inl ⟨by decide,
    LieType.Universal.Symplectic.statedClassicalModel_center_quotient m k hadm hk⟩⟩

theorem centralModel_SL {k : Type} [Field k] [Finite k] {ℓ j n : ℕ}
    (hadm : StatedLieAdmissible .PSL n ℓ j) (hk : Nat.card k = ℓ ^ j) :
    CentralModel ℓ .PSL n j (Matrix.SpecialLinearGroup (Fin n) k) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  exact ⟨hadm, Or.inl ⟨by decide,
    LieType.Universal.SpecialLinear.statedClassicalModel_center_quotient m k hadm hk⟩⟩

theorem centralModel_statedSp_component {k : Type} [Field k] [Finite k] {ℓ j m : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j) (hk : Nat.card k = ℓ ^ j) (hm : 2 ≤ m)
    {L : Subgroup (StatedSp m k)} (hL : IsComponent L) : CentralModel ℓ .PSp m j L := by
  have hadm := OddInner.admissible_PSp hℓ hℓ2 hj hm
  obtain rfl := OddClassSelector.eq_top_of_isComponent_of_quasisimple
    (LieType.Universal.Symplectic.isQuasisimple_of_admissible m k hadm hk) hL
  exact (centralModel_statedSp hadm hk).of_mulEquiv Subgroup.topEquiv

theorem centralModel_isometryGroup_component {k W : Type} [Field k] [Finite k] [AddCommGroup W]
    [Module k W] [FiniteDimensional k W] {ℓ j m : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j)
    (hk : Nat.card k = ℓ ^ j) (B : BilinForm k W) (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hdim : Module.finrank k W = 2 * m) (hm : 2 ≤ m)
    {L : Subgroup (CatalogueBAlternatingIsometry.isometryGroup B)} (hL : IsComponent L) :
    CentralModel ℓ .PSp m j L := by
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdim
  exact centralModel_of_component_equiv e
    (fun N hN => centralModel_statedSp_component hℓ hℓ2 hj hk hm hN) hL

theorem centralModel_GL_component {k : Type} [Field k] [Finite k] {ℓ j n : ℕ} (hℓ : ℓ.Prime)
    (hj : 1 ≤ j) (hk : Nat.card k = ℓ ^ j) (hn : 3 ≤ n) {L : Subgroup (GL (Fin n) k)}
    (hL : IsComponent L) : CentralModel ℓ .PSL n j L := by
  have : Group.IsPerfect L := hL.1.1
  have : Nontrivial L := LocalCores.isQuasisimple_nontrivial hL.1
  obtain rfl := CatalogueBGeneralLinear.perfect_subnormal_eq_specialLinearRange n k (by omega)
    (Or.inl (by omega)) (Or.inl (by omega)) L hL.2
  have hadm : StatedLieAdmissible .PSL n ℓ j :=
    OddInner.admissible_PSL hℓ hj (by omega) (Or.inl (by omega)) (Or.inl (by omega))
  exact (centralModel_SL hadm hk).of_mulEquiv
    (MonoidHom.ofInjective Matrix.SpecialLinearGroup.toGL_injective).symm

theorem centralModel_unitary_component {E W : Type} [Field E] [Finite E] [AddCommGroup W]
    [Module E W] [FiniteDimensional E W] {sigma : E ≃+* E} {ℓ e : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (he : 1 ≤ e) (hE : Nat.card E = (ℓ ^ e) ^ 2) (hW : 3 ≤ Module.finrank E W)
    (h : W →ₛₗ[sigma.toRingHom] W →ₗ[E] E) (hsym : h.IsSymm) (hnd : h.Nondegenerate)
    (hsigma : sigma ^ 2 = 1) (hne : sigma ≠ 1) (hsig : ∀ z, sigma z = z ^ (ℓ ^ e))
    {L : Subgroup (CatalogueBUnitaryIsometry.isometryGroup h)} (hL : IsComponent L) :
    CentralModel ℓ .PSU (Module.finrank E W) e L := by
  have hq3 := OddInner.three_le_pow hℓ hℓ2 he
  have hadm : StatedLieAdmissible .PSU (Module.finrank E W) ℓ e :=
    ⟨hℓ, he, hW, fun h' => by have := (Prod.mk.inj h').2; omega⟩
  obtain ⟨eX⟩ := OddClassSelector.nonempty_quotient_psu hℓ hℓ2 he hE hW h hsym hnd hsigma
    hne hsig hL (MonoidHom.id L) Function.surjective_id (fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.id_apply] at hx
      rw [hx]
      exact one_mem _)
  exact ⟨hadm, Or.inl ⟨by decide, hadm, E, inferInstance, inferInstance, hE, ⟨eX⟩⟩⟩

theorem eq_top_of_isComponent_sesqUnitaryGroup {k W : Type} [Field k] [Finite k]
    [AddCommGroup W] [Module k W] [FiniteDimensional k W] {ℓ j : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (hj : 1 ≤ j) (hk : Nat.card k = ℓ ^ j) (B : BilinForm k W) (hB : B.IsAlt)
    (hnd : B.Nondegenerate) (hW : 0 < Module.finrank k W)
    {N : Subgroup (LocalAnalysis.ComponentInitial.sesqUnitaryGroup B)} (hN : IsComponent N) :
    N = ⊤ := by
  obtain ⟨m, hdm, -⟩ := CatalogueBAlternatingIsometry.exists_isometryEquiv_symplectic B hB hnd
  obtain ⟨e⟩ := OutcomeLocal.nonempty_altIsometry_mulEquiv_statedSp B hB hnd hdm
  let e' := (sesqUnitaryIsometryEquiv B).trans e
  have hq : IsQuasisimple (StatedSp m k) := by
    rcases Nat.lt_or_ge m 2 with hm2 | hm2
    · obtain rfl : m = 1 := by omega
      let eS := ClassicalInvolution.Models.SymplecticPairs.longBlockEquivOne k
      by_cases h3 : ℓ ^ j = 3
      · exfalso
        have : Group.IsSolvable (StatedSp 1 k) :=
          LieType.HighestRoot.isSolvable_of_mulEquiv (hk.trans h3) eS.symm
        have : Group.IsSolvable (LocalAnalysis.ComponentInitial.sesqUnitaryGroup B) :=
          Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
        exact OddInner.not_isComponent_of_isSolvable N hN
      · have hq5 := OddInner.five_le_pow hℓ hℓ2 hj h3
        have hSL := CatalogueBGeneralLinear.specialLinear_quasisimple 2 k le_rfl
          (Or.inr (by rw [hk]; omega)) (Or.inr (by rw [hk]; exact h3))
        exact LocalCores.isQuasisimple_of_mulEquiv eS hSL
    · exact LieType.Universal.Symplectic.isQuasisimple_of_admissible m k
        (OddInner.admissible_PSp hℓ hℓ2 hj hm2) hk
  exact OddClassSelector.eq_top_of_isComponent_of_quasisimple
    (LocalCores.isQuasisimple_of_mulEquiv e'.symm hq) hN

end CFSG.ComponentClassification.CatLeafProof.X10Sp
