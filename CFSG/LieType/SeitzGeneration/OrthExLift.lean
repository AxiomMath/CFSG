module

public import CFSG.LieType.SeitzGeneration.OrthEx
public import CFSG.LieType.SeitzGeneration.OrthLow
public import CFSG.LieType.SeitzGeneration.InnerSymplecticThree
public import CFSG.LieType.SeitzGeneration.RegimesExc

public section

namespace CFSG.LieType.SeitzGeneration

open Module QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP CFSG.Open CFSG.RankThree.Classical
  CFSG.LieType.SeitzGeneration.OrthBlk
open CFSG.RankThree.Classical2 (orthDerived)

section Lift

theorem exists_isElemAbelian_lift' {G H : Type*} [Group G] [Group H] {p : ℕ} [Fact p.Prime]
    (π : G →* H) (hπ : Function.Surjective π) [Finite G] (hker : ¬ p ∣ Nat.card π.ker)
    {F : Subgroup H} (hF : IsElemAbelian p F) :
    ∃ F' : Subgroup G, IsElemAbelian p F' ∧ Nat.card F' = Nat.card F := by
  have hEp : IsPGroup p F := fun x => ⟨1, Subtype.ext (by simpa using hF.2 x x.2)⟩
  obtain ⟨E', hE'map, hE'dis⟩ := SeitzToral.exists_lift_of_coprime_ker π hπ hker F hEp
  have hE'mem : ∀ x ∈ E', π x ∈ F := fun x hx => hE'map ▸ ⟨x, hx, rfl⟩
  have hcommF : ∀ x ∈ F, ∀ y ∈ F, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val ((isMulCommutative_iff.mp hF.1) (⟨x, hx⟩ : F) ⟨y, hy⟩)
  have hE'comm : ∀ a ∈ E', ∀ b ∈ E', a * b = b * a := by
    intro a ha b hb
    have hc : a * b * a⁻¹ * b⁻¹ ∈ E' := E'.mul_mem (E'.mul_mem (E'.mul_mem ha hb) (E'.inv_mem ha))
      (E'.inv_mem hb)
    have hk : a * b * a⁻¹ * b⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      have := hcommF _ (hE'mem a ha) _ (hE'mem b hb)
      rw [this]
      group
    have := Subgroup.disjoint_def.mp hE'dis hc hk
    exact commutatorElement_eq_one_iff_mul_comm.mp this
  have hE'exp : ∀ a ∈ E', a ^ p = 1 := by
    intro a ha
    have hk : a ^ p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hF.2 _ (hE'mem a ha)
    exact Subgroup.disjoint_def.mp hE'dis (E'.pow_mem ha p) hk
  refine ⟨E', ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hE'comm a a.2 b b.2), hE'exp⟩, ?_⟩
  let fπ : E' →* F := (π.comp E'.subtype).codRestrict F (fun x => hE'mem x.1 x.2)
  have hfπsurj : Function.Surjective fπ := by
    intro e
    have : (e : H) ∈ E'.map π := hE'map ▸ e.2
    obtain ⟨x, hx, hxe⟩ := this
    exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
  have hfπinj : Function.Injective fπ := by
    intro x y hxy
    have h1 : π x.1 = π y.1 := congrArg Subtype.val hxy
    have h2 : x.1⁻¹ * y.1 ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h1, inv_mul_cancel]
    have h3 : x.1⁻¹ * y.1 = 1 :=
      Subgroup.disjoint_def.mp hE'dis (E'.mul_mem (E'.inv_mem x.2) y.2) h2
    exact Subtype.ext (inv_mul_eq_one.mp h3)
  exact Nat.card_congr (Equiv.ofBijective fπ ⟨hfπinj, hfπsurj⟩)

theorem exists_map_plane {G H : Type*} [Group G] [Group H] {p : ℕ} (hp : p.Prime) (π : G →* H)
    (hπ : Function.Surjective π) (hker : ¬ p ∣ Nat.card π.ker) {E₀ : Subgroup G}
    (hE₀ : IsElemAbelian p E₀) (hc : Nat.card E₀ = p ^ 2)
    (hgen : Subgroup.closure {g : G | ∃ x ∈ E₀, x ≠ 1 ∧ g * x = x * g} = ⊤) :
    ∃ E₁ : Subgroup H, IsElemAbelian p E₁ ∧ Nat.card E₁ = p ^ 2 ∧
      Subgroup.closure {k : H | ∃ x ∈ E₁, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hEker : ∀ x ∈ E₀, π x = 1 → x = 1 := by
    intro x hx hπx
    have h1 : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hE₀.2 x hx)
    have h2 : orderOf x ∣ Nat.card π.ker := by
      let y : π.ker := ⟨x, hπx⟩
      calc orderOf x = orderOf y := Subgroup.orderOf_coe y
        _ ∣ Nat.card π.ker := orderOf_dvd_natCard y
    rcases (Nat.dvd_prime hp).mp h1 with h | h
    · exact orderOf_eq_one_iff.mp h
    · exact absurd (h ▸ h2) hker
  have hinj : Function.Injective (π.comp E₀.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨x, hx⟩ h
    exact Subtype.ext (hEker x hx (by simpa using h))
  refine ⟨E₀.map π, CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hE₀ _, ?_, ?_⟩
  · have hrange : (π.comp E₀.subtype).range = E₀.map π := by
      rw [MonoidHom.range_comp, Subgroup.range_subtype]
    rw [← hrange, ← hc]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  · rw [eq_top_iff]
    intro k _
    obtain ⟨g, rfl⟩ := hπ k
    have hg : g ∈ Subgroup.closure {g : G | ∃ x ∈ E₀, x ≠ 1 ∧ g * x = x * g} := by
      rw [hgen]
      trivial
    have hle : (Subgroup.closure {g : G | ∃ x ∈ E₀, x ≠ 1 ∧ g * x = x * g}).map π ≤
        Subgroup.closure {k : H | ∃ x ∈ E₀.map π, x ≠ 1 ∧ k * x = x * k} := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨g', ⟨x, hx, hx1, hcomm⟩, rfl⟩
      refine Subgroup.subset_closure ⟨π x, Subgroup.mem_map_of_mem _ hx, ?_, ?_⟩
      · intro h
        exact hx1 (hEker x hx h)
      · rw [← map_mul, ← map_mul, hcomm]
    exact hle ⟨g, hg, rfl⟩

end Lift

section Model

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K] [Finite K]
  {Q : QuadraticForm K (ι → K)} {Q₀ : (ι → K) → K}

theorem exists_plane_gen_statedProj (hQ : ⇑Q = Q₀) (hE : orthDerived Q = elementaryGroup Q)
    (hnd : (polarBilin Q).Nondegenerate) [Nontrivial (ι → K)] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hgen : OrthHighGen Q p)
    (hrk : ¬ RankLE2 p (StatedProj (StatedOmega Q₀))) :
    ∃ E : Subgroup (StatedProj (StatedOmega Q₀)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
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
  have hrkΩ : ¬ RankLE2 p (orthDerived Q) := by
    intro hΩ
    apply hrk
    intro F hF
    obtain ⟨F', hF', hcard⟩ := exists_isElemAbelian_lift' π hπ hker' hF
    rw [← hcard]
    exact hΩ F' hF'
  obtain ⟨E₀, hcomm, hexp, hcard, hgen'⟩ := hgen hrkΩ
  have hE₀ : IsElemAbelian p E₀ :=
    ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a a.2 b b.2), hexp⟩
  exact exists_map_plane hp π hπ hker' hE₀ hcard hgen'

end Model

section Leaves

theorem orthogonalOddHigh {r p : ℕ} {K : Type} [Field K] [Finite K] (hr : 3 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K) (h2 : (2 : K) ≠ 0)
    (hrk : ¬ RankLE2 p (StatedProj (StatedOmega (StatedQuadOdd r K)))) :
    ∃ E : Subgroup (StatedProj (StatedOmega (StatedQuadOdd r K))), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧ Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadOdd r K)) |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadOdd (K := K) h2 hr
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r ⊕ Unit → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact exists_plane_gen_statedProj (coe_quadOdd r K) (commutator_orthogonalGroup_quadOdd h2 hr)
    hreg.1 hp hp2 (orthHighGen hreg.1 hreg.2 hdim hp hp2 (ne_ringChar_of_not_dvd_card hpK)) hrk

theorem orthogonalPlusHigh {r p : ℕ} {K : Type} [Field K] [Finite K] (hr : 4 ≤ r) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K)
    (hrk : ¬ RankLE2 p (StatedProj (StatedOmega (StatedQuadPlus r K)))) :
    ∃ E : Subgroup (StatedProj (StatedOmega (StatedQuadPlus r K))), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧ Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadPlus r K)) |
        ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadPlus (K := K) (n := r) (by omega)
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have hdim : 7 ≤ finrank K (Fin r ⊕ Fin r → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact exists_plane_gen_statedProj (coe_quadPlus r K)
    (commutator_orthogonalGroup_quadPlus (by omega)) hreg.1 hp hp2
    (orthHighGen hreg.1 hreg.2 hdim hp hp2 (ne_ringChar_of_not_dvd_card hpK)) hrk

theorem orthogonalMinusHigh {r p : ℕ} {K : Type} [Field K] [Finite K] (b c : K) (hr : 4 ≤ r)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : ¬ p ∣ Nat.card K)
    (hrk : ¬ RankLE2 p (StatedProj (StatedOmega (StatedQuadMinus r K b c)))) :
    ∃ E : Subgroup (StatedProj (StatedOmega (StatedQuadMinus r K b c))), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧
        Subgroup.closure {k : StatedProj (StatedOmega (StatedQuadMinus r K b c)) |
          ∃ x ∈ E, x ≠ 1 ∧ k * x = x * k} = ⊤ := by
  have hreg := regular_quadMinus (K := K) (n := r) hr hirr
  have : Nonempty (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hdim : 7 ≤ finrank K (Fin (r - 1) ⊕ Fin (r - 1) ⊕ Fin 2 → K) := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp
    omega
  exact exists_plane_gen_statedProj (coe_quadMinus r K b c)
    (commutator_orthogonalGroup_quadMinus hr hirr) hreg.1 hp hp2
    (orthHighGen hreg.1 hreg.2 hdim hp hp2 (ne_ringChar_of_not_dvd_card hpK)) hrk

end Leaves

section Scope

theorem seitzInnerEx_orth_high (d : TauCeti.ValidLieTypeIndex) (hd : IsOrthogonalIndex d.1)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hrk : ¬ RankLE2 p (Cat d))
    (hex : ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E) :
    ∃ E : Subgroup (MulAut (Cat d)), IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      InnerPlane d p E ∧ PlaneGen E := by
  obtain ⟨E, hE, hc, hinner⟩ := hex
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
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
    obtain ⟨E₁, hE₁, hc₁, hgen⟩ := orthogonalOddHigh hr3 hp hp2
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq') h2
      (fun h => hrk (RankLE2.of_mulEquiv e.symm h))
    obtain ⟨E', hE', hc', hinn, hPG⟩ := exists_planeGen_of_model hinj e hE₁ hc₁ hgen
    exact ⟨E', hE', hc', hinn, hPG⟩
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
    obtain ⟨E₁, hE₁, hc₁, hgen⟩ := orthogonalPlusHigh hr4 hp hp2
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
      (fun h => hrk (RankLE2.of_mulEquiv e.symm h))
    obtain ⟨E', hE', hc', hinn, hPG⟩ := exists_planeGen_of_model hinj e hE₁ hc₁ hgen
    exact ⟨E', hE', hc', hinn, hPG⟩
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
    obtain ⟨E₁, hE₁, hc₁, hgen⟩ := orthogonalMinusHigh b c hr4 hirr hp hp2
      (by rw [hcard]; exact not_dvd_pow_of_ne hp q.prime_p hq')
      (fun h => hrk (RankLE2.of_mulEquiv e.symm h))
    obtain ⟨E', hE', hc', hinn, hPG⟩ := exists_planeGen_of_model hinj e hE₁ hc₁ hgen
    exact ⟨E', hE', hc', hinn, hPG⟩

theorem seitzInnerEx_orth (hres : OrthSelfDualTwoBlocks) :
    InnerExFor fun d => IsOrthogonalIndex d.1 := by
  intro d hd p hp hp2 hpd hex ⟨E, hE, hc, hi⟩
  by_cases hr : RankLE2 p (Cat d)
  · exact ⟨E, hE, hc, hi, seitzInnerLow_orth hres d p hp hp2 hpd hex E hE hc ⟨hi, hr, hd⟩⟩
  · exact seitzInnerEx_orth_high d hd p hp hp2 hpd hr ⟨E, hE, hc, hi⟩

end Scope

end CFSG.LieType.SeitzGeneration
