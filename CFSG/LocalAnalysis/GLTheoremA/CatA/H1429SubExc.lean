module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubCore
public import CFSG.HardMathSupport.Dickson.DefCharOuter.Export.ExcUntwisted
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedG2
public import CFSG.HardMathSupport.Lang.E6Descent.OuterDescentE
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H1429SubRed

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1429Sub

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.Yardstones.Md0ec50421ce4
open CFSG.HardMathSupport.Dickson.DefCharOuter.Export
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped commutatorElement


theorem exists_pSimple_equiv_entrywise (τ : Tag) {K : Type} [Field K] [Finite K]
    (hK2 : ringChar K ≠ 2) (σ : K ≃+* K) {S : Type} [Group S] [Finite S]
    (ψ : S ≃* adjointGroup τ K) {β : MulAut S} (h : MulAut.congr ψ β = entrywiseAdjointAut τ σ)
    (hdvd : 3 ∣ Nat.card ↥(adjointGroup τ (fixSubfield σ))) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) :
    Nonempty (PSimple 3 I ≃* adjointGroup τ (fixSubfield σ)) := by
  classical
  have : Finite (ModGL τ K) := finite_modGL
  set a := entrywiseAdjointAut τ σ with ha
  have hk2 : ringChar (fixSubfield σ) ≠ 2 := by
    intro h
    have h0 : ((2 : ℕ) : fixSubfield σ) = 0 := by
      rw [← h]
      exact ringChar.Nat.cast_ringChar
    apply Ring.two_ne_zero hK2
    have := congrArg (fixSubfield σ).subtype h0
    rw [map_natCast, map_zero] at this
    exact_mod_cast this
  obtain ⟨hs, hnc, -⟩ := odd_pinned_Chevalley_p_components τ (fixSubfield σ) hk2
  obtain ⟨-, -, -, hJΓ, -, hnormal, -, hder⟩ :=
    Chevalley_coordinate_field_fixed_structure τ K hK2 σ
  have hJA : fixedFieldImage τ σ ≤ adjointGroup τ K := hJΓ.trans inf_le_left
  have hΓ : ∀ n : ↥(fixSubgroup a), ((n : ↥(adjointGroup τ K)) : ModGL τ K) ∈
      entrywiseFixedGroup τ σ := fun n =>
    ⟨(n : ↥(adjointGroup τ K)).2, by
      have h1 : a n = n := n.2
      have := congrArg Subtype.val h1
      rwa [coe_entrywiseAdjointAut] at this⟩
  set J : Subgroup ↥(adjointGroup τ K) := (fixedFieldImage τ σ).subgroupOf (adjointGroup τ K)
    with hJ
  have hmemJ : ∀ x : ↥(adjointGroup τ K), x ∈ J ↔ (x : ModGL τ K) ∈ fixedFieldImage τ σ :=
    fun x => Iff.rfl
  have hJC : J ≤ fixSubgroup a := fun x hx => by
    rw [mem_fixSubgroup]
    refine Subtype.ext ?_
    rw [coe_entrywiseAdjointAut]
    exact (hJΓ ((hmemJ x).1 hx)).2
  haveI hJn : (J.subgroupOf (fixSubgroup a)).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf, hmemJ] at hn ⊢
    have h1 := hnormal.conj_mem ⟨((n : ↥(adjointGroup τ K)) : ModGL τ K), hΓ n⟩
      (Subgroup.mem_subgroupOf.2 hn) ⟨((g : ↥(adjointGroup τ K)) : ModGL τ K), hΓ g⟩
    simpa using Subgroup.mem_subgroupOf.1 h1
  let eJ : ↥J ≃* adjointGroup τ (fixSubfield σ) :=
    (Subgroup.subgroupOfEquivOfLe hJA).trans (fixedFieldImageEquiv σ).symm
  haveI := hs
  have hsJ : IsSimpleGroup ↥J := eJ.isSimpleGroup
  have hncJ : ∃ x y : ↥J, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨eJ.symm x, eJ.symm y, fun h => hxy (by simpa using congrArg eJ h)⟩
  have hsol : Group.IsSolvable (↥(fixSubgroup a) ⧸ J.subgroupOf (fixSubgroup a)) := by
    refine Group.isSolvable_of_comm fun x y => ?_
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h1 : (x * y)⁻¹ * (y * x) = ⁅y⁻¹, x⁻¹⁆ := by simp [commutatorElement_def, mul_assoc]
    rw [h1, Subgroup.mem_subgroupOf, hmemJ]
    have h2 : (((⁅y⁻¹, x⁻¹⁆ : ↥(fixSubgroup a)) : ↥(adjointGroup τ K)) : ModGL τ K) =
        ⁅(((y⁻¹ : ↥(fixSubgroup a)) : ↥(adjointGroup τ K)) : ModGL τ K),
          (((x⁻¹ : ↥(fixSubgroup a)) : ↥(adjointGroup τ K)) : ModGL τ K)⁆ := by
      simp [commutatorElement_def]
    rw [h2, ← hder]
    exact Subgroup.commutator_mem_commutator (hΓ _) (hΓ _)
  have hdvdJ : 3 ∣ Nat.card ↥J := by rw [Nat.card_congr eJ.toEquiv]; exact hdvd
  obtain ⟨e⟩ := exists_equiv_of_conj ψ h hJC hsol hsJ hncJ hdvdJ hI
  exact ⟨e.trans eJ⟩

section Tags


theorem exists_descent_adjoint (τ : Tag)
    (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (α : MulAut (adjointGroup τ K)) (hα : orderOf α = ℓ)
    (hout : α ∉ innerAut (adjointGroup τ K)) :
    ∃ (r j : ℕ) (δ : MulAut (adjointGroup τ K)) (σ : K ≃+* K),
      orderOf σ = ℓ ∧ (α ^ r) ^ j = α ∧ δ * α ^ r * δ⁻¹ = entrywiseAdjointAut τ σ := by
  classical
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have : Finite (ModGL τ K) := finite_modGL
  have hαp : α ^ ℓ = 1 := by rw [← hα]; exact pow_orderOf_eq_one α
  rcases hτ with rfl | rfl | hE
  ·
    obtain ⟨x, σ, hσp, hασ⟩ : ∃ (x : adjointGroup Tag.G2 K) (σ : K ≃+* K),
        orderOf σ = ℓ ∧ α = MulAut.conj x * entrywiseAdjointAut Tag.G2 σ := by
      by_cases hℓ3 : ℓ = 3
      · subst hℓ3
        exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_three hf K hK hℓ hℓ2 α hα hout
      · exact CFSG.HardMathSupport.Lang.E6Descent.G2_form_odd hℓ hℓ2 hℓ3 hf K hK hℓ α hα hout
    obtain ⟨δ, hδ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_conj_eq_entrywiseAdjointAut_of_form
        Tag.G2 hℓ hf K hK hℓ α hα x σ hσp hασ
    exact ⟨1, 1, δ, σ, hσp, by rw [pow_one, pow_one], by rw [pow_one]; exact hδ⟩
  ·
    obtain ⟨x, σ, δ, hσp, -, hδ, -, -⟩ :=
      odd_F4_prime_field_coset_descent hℓ hℓ2 hf K hK hℓ α hα hout
    exact ⟨1, 1, δ, σ, hσp, by rw [pow_one, pow_one], by rw [pow_one]; exact hδ⟩
  ·
    have hnd : ∀ (g : adjointGroup τ K) (a : Fin τ.rank → Kˣ),
        α ≠ MulAut.conj g * rootDiagAut τ K a := by
      intro g a h
      have hdvd :=
        (CFSG.HardMathSupport.Lang.E6Descent.prime_dvd_of_diag_noninner τ hE K hℓ g a α h hαp
          hout).2
      rw [hK] at hdvd
      have h1 : ℓ ∣ ℓ ^ f := dvd_pow_self ℓ (by omega)
      have h2 : ℓ ∣ ℓ ^ f - (ℓ ^ f - 1) := Nat.dvd_sub h1 hdvd
      rw [Nat.sub_sub_self (Nat.one_le_pow _ _ hℓ.pos)] at h2
      exact hℓ.one_lt.ne' (Nat.dvd_one.1 h2)
    obtain ⟨d, T, r, j, ψ, -, hTord, -, -, -, hαβ, hψ⟩ :=
      CFSG.HardMathSupport.Lang.E6Descent.exists_conj_entrywise_of_not_innerDiag τ hE hf K hK
        hℓ hℓ2 α hαp hnd
    exact ⟨r, j, ψ, T, hTord, hαβ, hψ⟩

theorem false_of_adjoint (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {f : ℕ} (hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = 3 ^ f)
    {S : Type} [Group S] [Finite S] (θ : S ≃* adjointGroup τ K) {β : MulAut S} (hβ : orderOf β = 3)
    (hout : β ∉ (MulAut.conj : S →* MulAut S).range) {I : Subgroup S}
    (hI : GLAPComponent 3 (fixSubgroup β) I) (hU : catalogIs (PSimple 3 I) S9.isU4two) : False := by
  classical
  have hℓ : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hℓ⟩
  haveI : CharP K 3 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hℓ hf hK
  have hK2 : ringChar K ≠ 2 := by rw [ringChar.eq K 3]; norm_num
  set α : MulAut (adjointGroup τ K) := MulAut.congr θ β with hαdef
  have hα : orderOf α = 3 := by rw [hαdef, MulEquiv.orderOf_eq]; exact hβ
  have hαout : α ∉ innerAut (adjointGroup τ K) := fun hin =>
    hout ((congr_mem_range_conj_iff θ β).1 hin)
  obtain ⟨r, j, δ, σ, hσ, hrj, hδ⟩ :=
    exists_descent_adjoint τ hτ hℓ (by norm_num) hf K hK α hα hαout
  have hrjβ : (β ^ r) ^ j = β := by
    apply (MulAut.congr θ).injective
    rw [map_pow, map_pow, ← hαdef]
    exact hrj
  have hfix := ExcUntwisted.fixSubgroup_pow_eq hrjβ
  have hI' : GLAPComponent 3 (fixSubgroup (β ^ r)) I := by rw [hfix]; exact hI
  let ψ : S ≃* adjointGroup τ K := θ.trans (δ : adjointGroup τ K ≃* adjointGroup τ K)
  have hψ : MulAut.congr ψ (β ^ r) = entrywiseAdjointAut τ σ := by
    have h1 : MulAut.congr ψ (β ^ r) = δ * α ^ r * δ⁻¹ := by
      rw [hαdef, ← map_pow]
      ext x
      rfl
    rw [h1, hδ]
  obtain ⟨hdvdf, hkcard⟩ := CFSG.RankThree.Chevalley.SteinbergBT.card_fixSubfield hℓ hf hK σ
  rw [hσ] at hdvdf hkcard
  have hd : 1 ≤ f / 3 := Nat.div_pos (Nat.le_of_dvd (by omega) hdvdf) (by norm_num)
  have hsix := ExcUntwisted.card_pow_six_dvd τ hτ (fixSubfield σ)
  rw [hkcard] at hsix
  have hdvd : 3 ∣ Nat.card ↥(adjointGroup τ (fixSubfield σ)) :=
    ((dvd_pow_self 3 (by omega)).trans (dvd_pow_self _ (by norm_num))).trans hsix
  obtain ⟨e⟩ := exists_pSimple_equiv_entrywise τ hK2 σ ψ hψ hdvd hI'
  have hcard : Nat.card (PSimple 3 I) = Nat.card ↥(adjointGroup τ (fixSubfield σ)) :=
    Nat.card_congr e.toEquiv
  rw [I1431Z.card_eq_of_u4two hU] at hcard
  rw [← hcard] at hsix
  have h729 : 3 ^ 6 ∣ 25920 :=
    (pow_dvd_pow_of_dvd (dvd_pow_self 3 (by omega)) 6).trans hsix
  norm_num at h729

end Tags

end CFSG.LocalAnalysis.GLTheoremA.H1429Sub

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.H1429Sub
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem i1429SubExc_holds : I1429SubLieAt SubIsExc := by
  intro S _ _ hS hnc d hchar hP ⟨e⟩ β hβ hout I hI hU
  have hord : orderOf β = 3 := orderOf_three_of_not_inner hβ hout
  obtain ⟨d, hv⟩ := d
  have key : ∀ (q : TauCeti.PrimePower) (τ : Tag),
      (τ = .G2 ∨ τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) →
      UntwistedChevalleyModel S τ (q.p ^ q.exponent) → q.p = 3 → catalogIs S isSp4_27 := by
    intro q τ hτ hmodel hq3
    exfalso
    obtain ⟨K, _, _, hK, ⟨e'⟩⟩ := hmodel
    let θ : S ≃* adjointGroup τ K := e'.trans
      ((QuotientGroup.quotientMulEquivOfEq center_adjointGroup_eq_bot).trans
        QuotientGroup.quotientBot)
    exact false_of_adjoint τ hτ q.exponent_pos K (by rw [hK, hq3]) θ hord hout hI hU
  rcases hP with ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩ | ⟨q, rfl⟩
  · have hq3 : q.p = 3 := by simpa using hchar
    exact key q .E6 (Or.inr (Or.inr (Or.inl rfl)))
      (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E6 q hv
        (by omega) e) hq3
  · have hq3 : q.p = 3 := by simpa using hchar
    exact key q .E7 (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E7 q hv
        (by omega) e) hq3
  · have hq3 : q.p = 3 := by simpa using hchar
    exact key q .E8 (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
      (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_E8 q hv
        (by omega) e) hq3
  · have hq3 : q.p = 3 := by simpa using hchar
    exact key q .F4 (Or.inr (Or.inl rfl))
      (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_F4 q hv
        (by omega) e) hq3
  · have hq3 : q.p = 3 := by simpa using hchar
    exact key q .G2 (Or.inl rfl)
      (CFSG.TauCetiBridge.untwistedModel_of_bridge CFSG.TauCetiBridge.untwistedBridge_G2 q hv
        (by omega) e) hq3

end CFSG.LocalAnalysis.GLTheoremA

end
