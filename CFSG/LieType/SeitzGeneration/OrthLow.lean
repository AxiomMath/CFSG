module

public import CFSG.LieType.SeitzGeneration.OrthThree
public import CFSG.LieType.SeitzGeneration.OrthLift

public section

namespace CFSG.LieType.SeitzGeneration

open Polynomial Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP CFSG.RankThree.PartOne.KCOrthogonal
  CFSG.RankThree.PartOne.KCPrimary CFSG.Open CFSG.RankThree.Classical
open CFSG.RankThree.Classical2 (orthDerived)

@[expose] def OrthSelfDualTwoBlocks : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (Q : QuadraticForm K V), (polarBilin Q).Nondegenerate →
    (∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) → 7 ≤ finrank K V →
    ∀ p : ℕ, p.Prime → 5 ≤ p → p ≠ ringChar K → RankLE2 p (orthDerived Q) →
    ∀ E : Subgroup (orthDerived Q), (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 → (∀ e ∈ planeFixSpace E, Q e = 0 → e = 0) → HasSelfDualFactor Q E →
        Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤

@[expose] def OrthLowGen {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (Q : QuadraticForm K V) (p : ℕ) : Prop :=
  RankLE2 p (orthDerived Q) → ∀ E : Subgroup (orthDerived Q),
    (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x ^ p = 1) → Nat.card E = p ^ 2 →
      Subgroup.closure {h : orthDerived Q | ∃ x ∈ E, x ≠ 1 ∧ h * x = x * h} = ⊤

section Arith

theorem dvd_card_sub_one_of_pow_eq_one {K : Type*} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {ζ : K} (hζ : ζ ^ p = 1) (hζ1 : ζ ≠ 1) : p ∣ Nat.card K - 1 := by
  have hne : ζ ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hζ
    exact zero_ne_one hζ
  have : Fact p.Prime := ⟨hp⟩
  let u : Kˣ := Units.mk0 ζ hne
  have hu : orderOf u = p := orderOf_eq_prime (by ext; simpa [u] using hζ)
    (fun h => hζ1 (by simpa [u] using congrArg Units.val h))
  have := orderOf_dvd_natCard u
  rwa [hu, Nat.card_units] at this

theorem rankLE2_of_coprime_ker {G H : Type*} [Group G] [Group H] [Finite G] {p : ℕ}
    (hp : p.Prime) (π : G →* H) (hker : ¬ p ∣ Nat.card π.ker) (h : RankLE2 p H) :
    RankLE2 p G := by
  have : Fact p.Prime := ⟨hp⟩
  intro F hF
  have hinj : Function.Injective (π.comp F.subtype) := by
    rw [injective_iff_map_eq_one]
    intro f hf
    have hfk : (f : G) ∈ π.ker := hf
    have h1 : orderOf (f : G) ∣ p := orderOf_dvd_of_pow_eq_one (hF.2 f f.2)
    have h2 : orderOf (⟨f, hfk⟩ : π.ker) ∣ Nat.card π.ker := orderOf_dvd_natCard _
    have h3 : orderOf (⟨f, hfk⟩ : π.ker) = orderOf (f : G) := Subgroup.orderOf_mk _ _
    rcases (Nat.dvd_prime hp).mp h1 with h4 | h4
    · exact Subtype.ext (orderOf_eq_one_iff.mp h4)
    · exact absurd (h4 ▸ h3 ▸ h2) hker
  have hF' : IsElemAbelian p (F.map π) :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF π
  have := h _ hF'
  have hrange : (π.comp F.subtype).range = F.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange] at this
  have hc : Nat.card F = Nat.card (π.comp F.subtype).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rwa [hc]

end Arith

section Model

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V}

theorem orthLowGen_of_residual_five (hres : OrthSelfDualTwoBlocks)
    (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpl : p ≠ ringChar K) : OrthLowGen Q p := by
  classical
  intro hrank E hcomm hexp hcard
  by_cases hs : ∃ e ∈ planeFixSpace E, e ≠ 0 ∧ Q e = 0
  · obtain ⟨e, he, he0, heQ⟩ := hs
    have : Nontrivial V := nontrivial_of_three_singular hT
    exact closure_eq_top_of_singular_fixed hQ hT hp (by omega) hpl E hcomm hexp hcard he he0 heQ
  by_cases hroot : ∀ ζ : K, ζ ^ p = 1 → ζ = 1
  · by_cases hsd : HasSelfDualFactor Q E
    · exact hres K V Q hQ hT hdim p hp hp5 hpl hrank E hcomm hexp hcard
        (fun e he heQ => by_contra fun h0 => hs ⟨e, he, h0, heQ⟩) hsd
    · exact closure_eq_top_of_allPaired hQ hT hp (by omega) hpl hroot E hcomm hexp hcard hsd
  · push Not at hroot
    obtain ⟨ζ, hζp, hζ1⟩ := hroot
    exact closure_eq_top_of_split hQ hT hp (by omega) (dvd_card_sub_one_of_pow_eq_one hp hζp hζ1)
      E hcomm hexp hcard

theorem orthLowGen_of_residual (hres : OrthSelfDualTwoBlocks) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hdim : 7 ≤ finrank K V)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpl : p ≠ ringChar K) : OrthLowGen Q p := by
  by_cases h5 : 5 ≤ p
  · exact orthLowGen_of_residual_five hres hQ hT hdim hp h5 hpl
  · have h3 : p = 3 := by
      have := hp.two_le
      rcases (by omega : p = 2 ∨ p = 3 ∨ p = 4) with h | h | h
      · exact absurd h hp2
      · exact h
      · subst h
        exact absurd hp (by norm_num)
    subst h3
    exact fun hrank E hcomm hexp hcard =>
      closure_eq_top_of_low_three hQ hT hdim hpl hrank E hcomm hexp hcard

end Model

section Lift

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem closure_centralizers_statedProj_of_low (hQ : ⇑Q = Q₀)
    (hE : orthDerived Q = elementaryGroup Q) (hnd : (polarBilin Q).Nondegenerate)
    [Nontrivial (ι → K)] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hgen : OrthLowGen Q p)
    (hrank : RankLE2 p (StatedProj (StatedOmega Q₀)))
    (E : Subgroup (StatedProj (StatedOmega Q₀))) (hEab : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega Q₀) | ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (ι → K) := inferInstance
  have : Finite ((ι → K) ≃ₗ[K] (ι → K)) :=
    Finite.of_injective (fun g => (g : (ι → K) → (ι → K))) DFunLike.coe_injective
  let ψ : StatedOmega Q₀ ≃* orthDerived Q :=
    (statedOmegaEquiv hQ hE).trans (MulEquiv.subgroupCongr hE).symm
  have hψ : ∀ y : StatedOmega Q₀,
      ((ψ y : orthDerived Q) : (ι → K) ≃ₗ[K] (ι → K)) =
        toLinEquiv ι K (y : GL ι K) := fun y => rfl
  let π : orthDerived Q →* StatedProj (StatedOmega Q₀) :=
    (QuotientGroup.mk' ((StatedScalars ι K).subgroupOf (StatedOmega Q₀))).comp
      ψ.symm.toMonoidHom
  have hπ : Function.Surjective π := (QuotientGroup.mk'_surjective _).comp ψ.symm.surjective
  have hker : π.ker = (scalars K (ι → K)).subgroupOf (orthDerived Q) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    change QuotientGroup.mk (ψ.symm x) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, mem_statedScalars_iff]
    have := hψ (ψ.symm x)
    rw [MulEquiv.apply_symm_apply] at this
    rw [← this]
  have hker' : ¬ p ∣ Nat.card π.ker := by
    rw [hker]
    have h := (scalarKernel_data hnd hp hp2).2
    rw [QuotientGroup.ker_mk'] at h
    exact (Nat.Prime.coprime_iff_not_dvd hp).1 h.symm
  have : IsMulCommutative E := hEab.1
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E) ⟨y, hy⟩)
  exact closure_centralizers_of_lift π hπ hker' E hcomm hEab.2 fun E' hc he hcd _ =>
    hgen (rankLE2_of_coprime_ker hp π hker' hrank) E' hc he (hcd.trans hcard)

end Lift

section Leaves

theorem orthogonalOddLow_of_residual (hres : OrthSelfDualTwoBlocks) {r p : ℕ} {K : Type}
    [Field K] [Finite K] (hr : 3 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (h2 : (2 : K) ≠ 0) (hrk : RankLE2 p (StatedProj (StatedOmega (StatedQuadOdd r K))))
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadOdd r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadOdd (K := K) h2 hr
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r ⊕ Unit → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_low (coe_quadOdd r K)
    (commutator_orthogonalGroup_quadOdd h2 hr) hreg.1 hp hp2
    (orthLowGen_of_residual hres hreg.1 hreg.2 hdim hp hp2 (ne_ringChar_of_not_dvd_card hpK))
    hrk E hE hcard

theorem orthogonalPlusLow_of_residual (hres : OrthSelfDualTwoBlocks) {r p : ℕ} {K : Type}
    [Field K] [Finite K] (hr : 4 ≤ r) (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hrk : RankLE2 p (StatedProj (StatedOmega (StatedQuadPlus r K))))
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadPlus r K)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadPlus (K := K) (n := r) (by omega)
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_low (coe_quadPlus r K)
    (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1 hp hp2
    (orthLowGen_of_residual hres hreg.1 hreg.2 hdim hp hp2 (ne_ringChar_of_not_dvd_card hpK))
    hrk E hE hcard

theorem orthogonalMinusLow_of_residual (hres : OrthSelfDualTwoBlocks) {r p : ℕ} {K : Type}
    [Field K] [Finite K] (b c : K) (hr : 4 ≤ r) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hrk : RankLE2 p (StatedProj (StatedOmega (StatedQuadMinus r K b c))))
    (E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c)))) (hE : IsElemAbelian p E)
    (hcard : Nat.card E = p ^ 2) :
    Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadMinus r K b c)) |
      ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadMinus (K := K) (n := r) hr hirr
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hdim : 7 ≤ finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact closure_centralizers_statedProj_of_low (coe_quadMinus r K b c)
    (commutator_orthogonalGroup_quadMinus hr hirr) hreg.1 hp hp2
    (orthLowGen_of_residual hres hreg.1 hreg.2 hdim hp hp2 (ne_ringChar_of_not_dvd_card hpK))
    hrk E hE hcard

end Leaves

section Scope

theorem seitzInnerLow_orth (hres : OrthSelfDualTwoBlocks) :
    SeitzPlanes fun d p E =>
      InnerPlane d p E ∧ RankLE2 p (Cat d) ∧ IsOrthogonalIndex d.1 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex E hE hc ⟨hinner, hrk, horth⟩
  rcases horth with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have h2 : (2 : ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)) ≠ 0 := by
      have hring := CFSG.ClassicalGroups.Orthogonal.ringChar_eq_of_card_eq q.prime_p
        q.exponent_pos hcard
      have : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p :=
        ringChar.of_eq hring
      intro h
      have : q.p ∣ 2 := (CharP.cast_eq_zero_iff
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) q.p 2).mp (by exact_mod_cast h)
      exact hq ((Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).mp this)
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadOdd r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadOdd_of_two_ne_zero
        h2 hr3
    have : IsSimpleGroup (Cat ⟨.B r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.B r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthogonalOddLow_of_residual hres hr3 hp hp2
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') h2 (RankLE2.of_mulEquiv e hrk)
      E₁ hE₁ hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadPlus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩)))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadPlus (by omega)
    have : IsSimpleGroup (Cat ⟨.D r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.D r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthogonalPlusLow_of_residual hres hr4 hp hp2
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') (RankLE2.of_mulEquiv e hrk) E₁
      hE₁ hcard₁
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1)
    obtain ⟨b, c, hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    have : IsSimpleGroup (StatedProj (StatedOmega (StatedQuadMinus r
        ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) b c))) :=
      CFSG.ClassicalGroups.Orthogonal.isSimpleGroup_statedProj_statedOmega_quadMinus hr4 hirr
    have : IsSimpleGroup (Cat ⟨.twistedD r q, hv⟩) := MulEquiv.isSimpleGroup e
    have hinj := conj_injective_of_simple_of_range_ne_bot (K := Cat ⟨.twistedD r q, hv⟩)
      (range_conj_ne_bot_of_inner hp hc hinner)
    refine planeGen_of_inner_model hinj e ?_ hE hc hinner
    intro E₁ hE₁ hcard₁
    exact orthogonalMinusLow_of_residual hres b c hr4 hirr hp hp2
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') (RankLE2.of_mulEquiv e hrk) E₁
      hE₁ hcard₁

end Scope

end CFSG.LieType.SeitzGeneration
