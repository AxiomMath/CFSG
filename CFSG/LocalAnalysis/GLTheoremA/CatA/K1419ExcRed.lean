module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K1419ExcDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1419Trans
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K1419E

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup
  glaPComponent_map_fixSubgroup)
open CFSG.LocalAnalysis.GLTheoremA.K1419 (PQ I1419Nontriv I1419Inn I1419Rel)
open CFSG.LocalAnalysis.GLTheoremA.H1419 (betaBar betaBar_mk centerBar centerBar_mk
  betaBar_pow_three centerBar_pow_three map_fixSubgroup_eq)

theorem centerBar_ne_one {K : Type} [Group K] (hK : commutator K = ⊤) {σ : MulAut K}
    (hσ : σ ≠ 1) : centerBar σ ≠ 1 := by
  intro h1
  apply hσ
  have hc : ∀ k : K, k⁻¹ * σ k ∈ Subgroup.center K := by
    intro k
    have h := DFunLike.congr_fun h1 (QuotientGroup.mk k)
    rw [centerBar_mk, MulAut.one_apply] at h
    exact QuotientGroup.eq.1 h.symm
  let φ : K →* ↥(Subgroup.center K) :=
    { toFun := fun k => ⟨k⁻¹ * σ k, hc k⟩
      map_one' := by ext; simp
      map_mul' := by
        intro x y
        ext
        have hx := Subgroup.mem_center_iff.1 (hc x)
        simp only [Subgroup.coe_mul, map_mul, mul_inv_rev]
        calc y⁻¹ * x⁻¹ * (σ x * σ y) = y⁻¹ * (x⁻¹ * σ x) * σ y := by group
          _ = (x⁻¹ * σ x) * y⁻¹ * σ y := by rw [hx y⁻¹]
          _ = x⁻¹ * σ x * (y⁻¹ * σ y) := by group }
  have hcomm : commutator K ≤ φ.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact Subtype.ext (Subgroup.mem_center_iff.1 (φ b).2 (φ a))
  ext k
  have hk : k ∈ φ.ker := hcomm (hK ▸ Subgroup.mem_top k)
  rw [MonoidHom.mem_ker] at hk
  have h2 : k⁻¹ * σ k = 1 := congrArg Subtype.val hk
  rw [MulAut.one_apply]
  calc σ k = k * (k⁻¹ * σ k) := by group
    _ = k := by rw [h2, mul_one]

theorem centerBar_betaBar_ne_one {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple (PQ Q)) {β : MulAut Q} (hNt : I1419Nontriv β) :
    centerBar (betaBar β) ≠ 1 := by
  refine centerBar_ne_one hQ.1 fun h => ?_
  obtain ⟨l, hl⟩ := hNt
  apply hl
  have := DFunLike.congr_fun h (QuotientGroup.mk l)
  rwa [betaBar_mk, MulAut.one_apply] at this

theorem pQuot_equiv_of_center_eq_bot {A B : Type} [Group A] [Group B] [Finite A] (f : A →* B)
    (hf : Function.Surjective f) (hA : CFSG.Open.IsQuasisimple (A ⧸ GLAPPrimeCore 3 A))
    (hB : Nontrivial (B ⧸ GLAPPrimeCore 3 B))
    (hZ : Subgroup.center (A ⧸ GLAPPrimeCore 3 A) = ⊥) :
    Nonempty ((A ⧸ GLAPPrimeCore 3 A) ≃* (B ⧸ GLAPPrimeCore 3 B)) := by
  have hp : Nat.Prime 3 := Nat.prime_three
  have hker := CFSG.LocalAnalysis.GLTheoremA.ker_pQuotMapOfSurjective_le_center hp f hf hA hB
  rw [hZ] at hker
  have hinj : Function.Injective (CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective hp f hf) :=
    (MonoidHom.ker_eq_bot_iff _).1 (le_bot_iff.1 hker)
  exact ⟨MulEquiv.ofBijective _
    ⟨hinj, CFSG.LocalAnalysis.GLTheoremA.pQuotMapOfSurjective_surjective hp f hf⟩⟩

theorem nonempty_quotCenter_equiv_of_bot {X : Type} [Group X] (h : Subgroup.center X = ⊥) :
    Nonempty ((X ⧸ Subgroup.center X) ≃* X) :=
  ⟨(QuotientGroup.quotientMulEquivOfEq h).trans QuotientGroup.quotientBot⟩

theorem innDiagKind_of_i1419Inn {Q : Type} [Group Q] [Finite Q]
    (hQ : CFSG.Open.IsQuasisimple (PQ Q)) {β : MulAut Q} (h : I1419Inn β) :
    ∃ labK : GLALabel, CFSG.LocalAnalysis.GLTheoremA.Y10GField.InnDiagKind
      (PQ Q ⧸ Subgroup.center (PQ Q)) labK (centerBar (betaBar β)) := by
  have hcen : Subgroup.center (PQ Q ⧸ Subgroup.center (PQ Q)) = ⊥ :=
    CFSG.LocalAnalysis.GLTheoremA.Y10F.center_centerQuot_eq_bot hQ
  haveI : Group.IsPerfect (PQ Q) := ⟨hQ.1⟩
  have hS : commutator (PQ Q ⧸ Subgroup.center (PQ Q)) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQ Q)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨-, labK, hlam, hraw⟩ := h
  refine ⟨labK, hS, labK, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hall⟩
  obtain ⟨φ, hφ, hind⟩ := hall 1
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl, φ, hφ, ?_⟩
  intro s s' hss'
  subst hss'
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk,
    CanonInn.quotCenterEquivOfBot_mk, centerBar_mk, betaBar_mk]
  exact hind (QuotientGroup.mk l) (QuotientGroup.mk (β l)) ⟨l, β l, rfl, rfl, by rw [zpow_one]⟩

theorem i1419ExcFact_of_S (h : I1419ExcS) : CFSG.LocalAnalysis.GLTheoremA.K1419.I1419ExcFact := by
  intro Q _ _ β J hQ hβ3 hNt hInn hJ hcat hZ hch hncl
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp⟩
  set S := PQ Q ⧸ Subgroup.center (PQ Q) with hSdef
  haveI : IsSimpleGroup S := hQ.2
  have hnab : ∃ a b : S, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian (PQ Q) hQ
  have hker : Nat.Coprime 3
      (Nat.card ↥(fixSubgroup β ⊓ (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q).ker)) := by
    rw [QuotientGroup.ker_mk']
    exact Nat.Coprime.coprime_dvd_right (Subgroup.card_dvd_of_le inf_le_right)
      CFSG.pPrimeCore_coprime_card
  have hJ1 := glaPComponent_map hp (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q) hker hJ
  rw [map_fixSubgroup_eq β hβ3] at hJ1
  have hker2 : (QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* S).ker ≤
      Subgroup.center (PQ Q) := (QuotientGroup.ker_mk' _).le
  have hJ2 := glaPComponent_map_fixSubgroup (QuotientGroup.mk' (Subgroup.center (PQ Q)) :
    PQ Q →* S) hker2 (betaBar β) (centerBar (betaBar β)) (fun y => (centerBar_mk _ y).symm)
    (QuotientGroup.mk'_surjective _) hp hJ1
  set π : Q →* S := (QuotientGroup.mk' (Subgroup.center (PQ Q)) : PQ Q →* S).comp
    (QuotientGroup.mk' (GLAPPrimeCore 3 Q) : Q →* PQ Q) with hπ
  have hJπ : GLAPComponent 3 (fixSubgroup (centerBar (betaBar β))) (J.map π) := by
    rw [hπ, ← Subgroup.map_map]
    exact hJ2
  have hqJ := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hqJ' := CFSG.LocalAnalysis.GLTheoremA.isQuasisimple_pQuot_of_glaPComponent hp hJπ
  haveI : Nontrivial (PQuot 3 (J.map π)) := by
    obtain ⟨a, b, hab⟩ :=
      CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian _ hqJ'
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    apply hab
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [Subsingleton.elim a b]
  obtain ⟨eJ⟩ := pQuot_equiv_of_center_eq_bot (π.subgroupMap J) (π.subgroupMap_surjective J) hqJ
    inferInstance hZ
  obtain ⟨eZ⟩ := nonempty_quotCenter_equiv_of_bot hZ
  have hL : L3U3 (PQuot 3 (J.map π)) := (catalogIs_congr (eJ.symm.trans eZ.symm)).2 hcat
  obtain ⟨labK, hInnS⟩ := innDiagKind_of_i1419Inn hQ hInn
  exact h S inferInstance hnab hch hncl labK _ hInnS
    ⟨centerBar_pow_three _ (betaBar_pow_three β hβ3), centerBar_betaBar_ne_one hQ hNt,
      J.map π, hJπ, hL⟩

end CFSG.LocalAnalysis.GLTheoremA.K1419E

end
