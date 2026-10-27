module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHighField
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.PSLnL4
public import CFSG.LieType.SeitzGeneration.InnerSymplecticThreeAll
public import CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter.OuterCubeOrthogonal
public import CFSG.LieType.SeitzGeneration.OuterOrthThreeData
public import CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube.OrthFixedLeDerivedProof
public import CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.SUOddTwoBig
public import CFSG.LieType.SeitzGeneration.FixPlaneGenUnitary
public import CFSG.LieType.SeitzGeneration.RootPairOrthOmega

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

open CFSG.Open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.AGLEmbedding
  CFSG.AGLEmbeddingD2 CFSG.RankThree.PartOne CFSG.RankThree.PartOne.CTP
  CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
  CFSG.HardMathSupport.Curtis.Coordinator.SeitzOuter
open CFSG.GroupTheory.SteinbergBK (semilinearFixedSubfield)

@[expose] def SeitzGoodOuterHighClassicalDiag : Prop :=
  SeitzGoodOuterHighAt fun d p =>
    (∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .A m q ∧ p ∣ Nat.gcd (m + 1) (q.card - 1)) ∨
    (∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧
      p ∣ Nat.gcd (m + 1) (q.card + 1)) ∨
    (p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q)

section Linear

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag

theorem planeCentGen_projectiveSL_kfact (hS : KFactSeitzRankTwo) {m : ℕ} (hm : 2 ≤ m)
    {k : Type} [Field k] [Finite k] {ℓ e : ℕ} (hℓ : ℓ.Prime) (he : 0 < e)
    (hkc : Nat.card k = ℓ ^ e) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ)
    (hdup : ¬ (ℓ ^ e = 2 ∧ (m = 2 ∨ m = 3)))
    (hexc : ¬ (p = 3 ∧ ℓ = 2 ∧ e = 2 ∧ m = 2)) : PlaneCentGen (projectiveSL (m + 1) k) p := by
  have hv : (TauCeti.LieTypeIndex.A m ⟨ℓ, e, hℓ, he⟩).Valid := by
    rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
      TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
    refine ⟨⟨by omega, fun h => by omega⟩, ?_⟩
    simp only [TauCeti.PrimePower.card_def]
    rintro (⟨h, _⟩ | ⟨_, h⟩ | ⟨_, h⟩)
    · omega
    · exact hdup ⟨h, Or.inl (by omega)⟩
    · exact hdup ⟨h, Or.inr (by omega)⟩
  set d₀ : TauCeti.ValidLieTypeIndex := ⟨.A m ⟨ℓ, e, hℓ, he⟩, hv⟩ with hd₀
  let e₁ := catEquivProjectiveSL hℓ he hkc hv
  refine PlaneCentGen.of_mulEquiv e₁ ?_
  intro A hA hAc
  have hn3 : 3 ≤ m + 1 := by omega
  have hinj : Function.Injective (MulAut.conj : Cat d₀ →* MulAut (Cat d₀)) := by
    intro x y hxy
    have hz : ∀ z, y⁻¹ * x * z = z * (y⁻¹ * x) := by
      intro z
      have h1 := congrArg (fun φ : MulAut (Cat d₀) => φ (x⁻¹ * y * z * y⁻¹ * x)) hxy
      simp only [MulAut.conj_apply] at h1
      have h2 : x * (x⁻¹ * y * z * y⁻¹ * x) * x⁻¹ = y * (x⁻¹ * y * z * y⁻¹ * x) * y⁻¹ := h1
      have h3 : y * (x⁻¹ * y * z * y⁻¹ * x) * y⁻¹ = y * x⁻¹ * y * z * y⁻¹ * x * y⁻¹ := by group
      have h4 : x * (x⁻¹ * y * z * y⁻¹ * x) * x⁻¹ = y * z * y⁻¹ := by group
      rw [h3, h4] at h2
      calc y⁻¹ * x * z = y⁻¹ * x * (y⁻¹ * (y * z * y⁻¹) * y) := by group
        _ = y⁻¹ * x * (y⁻¹ * (y * x⁻¹ * y * z * y⁻¹ * x * y⁻¹) * y) := by rw [h2]
        _ = z * (y⁻¹ * x) := by group
    have hc : e₁ (y⁻¹ * x) ∈ Subgroup.center (projectiveSL (m + 1) k) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := hz (e₁.symm g)
      have h5 := congrArg e₁ this
      simpa using h5.symm
    rw [CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot hn3, Subgroup.mem_bot] at hc
    have : y⁻¹ * x = 1 := e₁.injective (by rw [hc, map_one])
    exact (inv_mul_eq_one.mp this).symm
  have hpd : p ≠ d₀.1.characteristic := by simpa [hd₀] using hpℓ
  have hex : ¬ IsD2SeitzException p d₀.1 := by
    rintro (⟨hp3, ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ | ⟨q, hq1, hq2, hd⟩ |
        ⟨q, hq1, hq2, hd | hd⟩ | hd⟩ | ⟨h5, hd | hd⟩)
    · have := (TauCeti.LieTypeIndex.A.inj hd).1
      omega
    · obtain ⟨hm2, hq⟩ := TauCeti.LieTypeIndex.A.inj hd
      have h1 : ℓ = 2 := by
        have := congrArg TauCeti.PrimePower.p hq
        simpa [hq1] using this
      have h2 : e = 2 := by
        have := congrArg TauCeti.PrimePower.exponent hq
        simpa [hq2] using this
      exact hexc ⟨hp3, h1, h2, by omega⟩
    all_goals cases hd
  exact closure_centralizers_cat_of_kfact hS hp hp2 hpd hex hinj A hA hAc

theorem fixPlaneGen_projectiveSL_kfact (hS : KFactSeitzRankTwo) {m : ℕ} (hm : 2 ≤ m) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hpℓ : p ≠ ℓ) [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card K - 1))) :
    FixPlaneGen (projectiveSL (m + 1) K) p := by
  have hn3 : 3 ≤ m + 1 := by omega
  intro σ hσ A hA hAa hAc
  obtain ⟨d, -, g, ⟨τ, hτ, rfl⟩, rfl⟩ := outer_descent_gen hn3 hp hp2 hℓ hpℓ hf hK hcop σ hσ
  set k := semilinearFixedSubfield τ with hk
  have hpf : p ∣ f ∧ Nat.card k = ℓ ^ (f / p) := card_semilinearFixedSubfield hℓ hf hK hτ
  have he : 0 < f / p := Nat.div_pos (Nat.le_of_dvd (by omega) hpf.1) hp.pos
  let j := linearSubfieldInclusion (m + 1) k
  have hj : Function.Injective j := linearSubfieldInclusion_injective (by omega) k
  let φ : projectiveSL (m + 1) k →* projectiveSL (m + 1) K :=
    (d : projectiveSL (m + 1) K →* _).comp j
  have hφ : Function.Injective φ := d.injective.comp hj
  have hrange : φ.range = fixedSubgroup (d * fieldAut (m + 1) K τ * d⁻¹) := by
    rw [fixedSubgroup_conj, fixedSubgroup_fieldAut_eq_range_gen hn3 hp hcop hτ,
      MonoidHom.range_comp]
    rfl
  have hX : PlaneCentGen (projectiveSL (m + 1) k) p := by
    by_cases h2 : Nat.card k = 2
    · rcases (by omega : m = 2 ∨ m = 3 ∨ 4 ≤ m) with rfl | rfl | hm4
      · exact planeCentGen_L3_two h2 hp hp2
      · exact l4TwoPlanes k h2 p hp hp2
      · refine planeCentGen_projectiveSL_kfact hS hm hℓ he hpf.2 hp hp2 hpℓ ?_ ?_
        · rintro ⟨-, h | h⟩ <;> omega
        · rintro ⟨-, -, -, h⟩
          omega
    · refine planeCentGen_projectiveSL_kfact hS hm hℓ he hpf.2 hp hp2 hpℓ ?_ ?_
      · rintro ⟨h, -⟩
        exact h2 (hpf.2.trans h)
      · rintro ⟨hp3, hℓ2, he2, hm2⟩
        subst hm2 hp3 hℓ2
        have hf6 : f = 3 * 2 := by
          rw [← he2]
          exact (Nat.mul_div_cancel' hpf.1).symm
        rw [hf6] at hK
        have h63 : Nat.card K - 1 = 63 := by rw [hK]; norm_num
        rw [h63] at hcop
        norm_num at hcop
  rw [← hrange]
  exact fixPlane_of_hom φ hφ hX (hrange ▸ hA) hAa hAc

theorem pair_A (hS : KFactSeitzRankTwo) {m : ℕ} (hm : 2 ≤ m) {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.A m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hg : ¬ p ∣ Nat.gcd (m + 1) (q.card - 1)) :
    FieldAutData (Cat ⟨.A m q, hv⟩) p ∧ FixPlaneGen (Cat ⟨.A m q, hv⟩) p := by
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : Cat ⟨.A m q, hv⟩ ≃* LinearFlag.projectiveSL (m + 1) (GaloisField q.p q.exponent) :=
    (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL m q hv).trans
      (LinearCover.projectiveSpecialLinearEquivProjectiveSL (m + 1) _)
  have hcardF : Nat.card (GaloisField q.p q.exponent) = q.card := by
    rw [GaloisField.card _ _ q.exponent_pos.ne', TauCeti.PrimePower.card_def]
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have hcop : Nat.Coprime p (Nat.gcd (m + 1) (Nat.card (GaloisField q.p q.exponent) - 1)) := by
    rw [hcardF]
    exact (Nat.Prime.coprime_iff_not_dvd hp).mpr hg
  exact ⟨(fieldAutData_projectiveSL_of_cop (by omega) hp hp2 q.prime_p hpq q.exponent_pos hKq
      hcop).of_mulEquiv e hp,
    (fixPlaneGen_projectiveSL_kfact hS hm hp hp2 q.prime_p hpq q.exponent_pos hKq
      hcop).of_mulEquiv e hp⟩

theorem not_exists_cube_A_one {q : TauCeti.PrimePower} (hv : (TauCeti.LieTypeIndex.A 1 q).Valid)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ≠ q.p) :
    ¬ ∃ F : Subgroup (Cat ⟨.A 1 q, hv⟩), IsElemAbelian p F ∧ Nat.card F = p ^ 3 := by
  rintro ⟨F, hFa, hFc⟩
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.p.Prime := ⟨q.prime_p⟩
  let e : Cat ⟨.A 1 q, hv⟩ ≃* CFSG.GorensteinWalter.PSL2 (GaloisField q.p q.exponent) :=
    CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv
  have hKq : Nat.card (GaloisField q.p q.exponent) = q.p ^ q.exponent :=
    GaloisField.card _ _ q.exponent_pos.ne'
  have h7 : 7 ≤ Nat.card (GaloisField q.p q.exponent) := by
    rw [hKq, ← TauCeti.PrimePower.card_def]
    exact seven_le_card_of_valid_A_one hv
  haveI : Finite F := Nat.finite_of_card_ne_zero (by rw [hFc]; exact pow_ne_zero _ hp.ne_zero)
  obtain ⟨F₀, hF₀⟩ := Sylow.exists_subgroup_card_pow_prime (G := F) p
    (show p ^ 2 ∣ Nat.card F from hFc ▸ pow_dvd_pow p (by norm_num))
  have hF₁F : F₀.map F.subtype ≤ F := Subgroup.map_subtype_le F₀
  have hF₀a : IsElemAbelian p (F₀.map F.subtype) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hFa.2 x (hF₁F hx)⟩
    have h1 := congrArg Subtype.val (hFa.1.is_comm.comm (⟨a, hF₁F a.2⟩ : F) ⟨b, hF₁F b.2⟩)
    exact h1
  exact not_exists_plane_psl2 hKq h7 hp2 hpq ((F₀.map F.subtype).map e.toMonoidHom)
    (CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map p hF₀a _)
    (by rw [Subgroup.card_map_of_injective e.injective,
      Subgroup.card_map_of_injective F.subtype_injective, hF₀])

end Linear

section Unitary

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.Assembly.LowTwoRank

theorem pair_twistedA {m : ℕ} {q : TauCeti.PrimePower}
    (hv : (TauCeti.LieTypeIndex.twistedA m q).Valid) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ≠ q.p) (hg : ¬ p ∣ Nat.gcd (m + 1) (q.card + 1)) (h8 : ¬ (p = 3 ∧ q.card = 8)) :
    FieldAutData (Cat ⟨.twistedA m q, hv⟩) p ∧ FixPlaneGen (Cat ⟨.twistedA m q, hv⟩) p := by
  obtain ⟨-, -, hn3, hne, K, _, h, ⟨θ⟩⟩ := exists_primeFormP_of_statedClassicalModel_PSU
    (CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv (MulEquiv.refl _))
  have hcard : q.p ^ q.exponent = q.card := by rw [TauCeti.PrimePower.card_def]
  have hg' : ¬ p ∣ Nat.gcd (m + 1) (q.p ^ q.exponent + 1) := by rw [hcard]; exact hg
  have h8' : ¬ (p = 3 ∧ q.p ^ q.exponent = 8) := by rw [hcard]; exact h8
  have hpair : SubfieldPairSUOdd :=
    subfieldPairSUOdd
      CFSG.HardMathSupport.Malle.Coordinator.SubfieldPairs.subfieldPairSUOddTwo_holds
  exact ⟨(fieldAutData_primeFormP_odd hpair hn3 h hne hp hp2 hpq hg').of_mulEquiv θ hp,
    (fixPlaneGen_primeFormP h hn3 hne hp hp2 hpq hg' h8').of_mulEquiv θ hp⟩

end Unitary

section Symplectic

open CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne.KCSpFull (coprime_card_ker_proj)

theorem eq_two_three_of_card_eight {q : TauCeti.PrimePower} (hq : q.p ^ q.exponent = 8) :
    q.p = 2 ∧ q.exponent = 3 := by
  have h8 : q.p ^ q.exponent = 2 ^ 3 := by rw [hq]; norm_num
  have hp2 : q.p = 2 := by
    have hd : q.p ∣ 2 ^ 3 := h8 ▸ dvd_pow_self q.p q.exponent_pos.ne'
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 (q.prime_p.dvd_of_dvd_pow hd)
  refine ⟨hp2, ?_⟩
  rw [hp2] at h8
  exact Nat.pow_right_injective le_rfl h8

theorem fixPlaneGen_projectiveSp_three {r : ℕ} (hr : 2 ≤ r) {K : Type} [Field K] {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hℓ3 : ℓ ≠ 3) (h8 : ℓ ^ f ≠ 8) :
    FixPlaneGen (StatedProj (StatedSp r K)) 3 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact pow_ne_zero f hℓ.ne_zero)
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine fixPlaneGen_projectiveSp_of_inner hr hℓ hf hK Nat.prime_three (by norm_num) ?_
  intro σ hσ E₁ hE₁ hcard₁
  have hpf : 3 ∣ f ∧ Nat.card (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) =
      ℓ ^ (f / 3) := CFSG.RankThree.PartOne.card_semilinearFixedSubfield hℓ hf hK hσ
  obtain ⟨h3f, hk⟩ := hpf
  have hf3 : f / 3 ≠ 0 := (Nat.div_pos (Nat.le_of_dvd (by omega) h3f) (by norm_num)).ne'
  have h3k : (3 : CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) ≠ 0 :=
    three_ne_zero_of_card_prime_pow hℓ hℓ3 hf3 hk
  have hk3 : 3 ≤ Nat.card (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) := by
    have h2 : 1 < Nat.card (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) :=
      Finite.one_lt_card
    by_contra hlt
    have hk2 : ℓ ^ (f / 3) = 2 := by rw [← hk]; omega
    obtain ⟨hl2, he1⟩ := (Nat.Prime.pow_eq_iff Nat.prime_two).mp hk2
    apply h8
    have hf' : f = 3 := by omega
    rw [hl2, hf']
    norm_num
  have hcomm₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := by
    intro x hx y hy
    haveI := hE₁.1
    exact congrArg Subtype.val (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : E₁) ⟨y, hy⟩)
  refine CFSG.RankThree.PartOne.CTP.closure_centralizers_of_lift
    (proj r (CFSG.ComponentClassification.UnbalancedCatalog.descentField σ))
    (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := r)
      (K := CFSG.ComponentClassification.UnbalancedCatalog.descentField σ))
    ?_ E₁ hcomm₁ (fun x hx => hE₁.2 x hx) ?_
  · intro hd
    have h1 := coprime_card_ker_proj (r := r)
      (K := CFSG.ComponentClassification.UnbalancedCatalog.descentField σ) (by omega)
      Nat.prime_three (by norm_num)
    exact Nat.prime_three.one_lt.ne' (Nat.eq_one_of_dvd_coprimes h1 hd (dvd_refl 3))
  · intro E' hc' he' hcd' _
    have hcard9 : Nat.card E' = 9 := hcd'.trans (hcard₁.trans (by norm_num))
    exact closure_centralizers_spPlane_three h3k (exists_ne_zero_ne_one_of_card_three_le hk3) hr
      hc' he' hcard9

theorem excIndex_B_eight {r : ℕ} (hr : 2 ≤ r) {q : TauCeti.PrimePower}
    (hq : q.p ^ q.exponent = 8) : ExcIndex 3 (.B r q) := by
  obtain ⟨hp2, he3⟩ := eq_two_three_of_card_eight hq
  exact Or.inl ⟨rfl, Or.inr ⟨⟨hp2, he3⟩, hr⟩⟩

theorem fixPlaneGen_symplectic_index_three {d : TauCeti.ValidLieTypeIndex}
    (hd : IsSymplecticIndex d.1) (hpd : 3 ≠ d.1.characteristic) (hx : ¬ ExcIndex 3 d.1) :
    FixPlaneGen (Cat d) 3 := by
  obtain ⟨d, hv⟩ := d
  rcases hd with ⟨q, rfl⟩ | ⟨r, q, rfl, hr3, hq2⟩ | ⟨r, q, rfl⟩
  · have hq : q.p ≠ 3 := fun h => hpd (by simp [h])
    exact FixPlaneGen.of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeB2GroupEquivStatedProj q hv)
      Nat.prime_three (fixPlaneGen_projectiveSp_three le_rfl q.prime_p q.exponent_pos
        (CFSG.RankThree.PartOne.CTP.card_fixedField_B 2 q hv) hq
        (fun h8 => hx (excIndex_B_eight le_rfl h8)))
  · have hq : q.p ≠ 3 := fun h => hpd (by simp [h])
    exact FixPlaneGen.of_mulEquiv
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj r q hv hq2 hr3)
      Nat.prime_three (fixPlaneGen_projectiveSp_three (by omega) q.prime_p q.exponent_pos
        (CFSG.RankThree.PartOne.CTP.card_fixedField_B r q hv) hq
        (fun h8 => hx (excIndex_B_eight (by omega) h8)))
  · have hq : q.p ≠ 3 := fun h => hpd (by simp [h])
    have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
    have hr3 : 3 ≤ r := hrange.1
    have hq2 : q.p ≠ 2 := hrange.2
    exact FixPlaneGen.of_mulEquiv (CFSG.QuasithinUnique.SQTK.typeCGroupEquivStatedProj r q hv)
      Nat.prime_three (fixPlaneGen_projectiveSp_three (by omega) q.prime_p q.exponent_pos
        (card_fixedField_C r q hv) hq (fun h8 => hq2 (eq_two_three_of_card_eight h8).1))

end Symplectic

section Orthogonal

open Matrix CFSG.RankThree.PartOne.KCOrthogonalSubfield CFSG.RankThree.Classical.SteinbergBY
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBHigherLinearField
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadOdd StatedQuadPlus StatedQuadMinus
  StatedLieAdmissible StatedLieTag StatedClassicalModel)
open CFSG.HardMathSupport.Lang.Proving (orthogonal_prime_semilinear_actual_fixed_form_descent')
open CFSG.RankThree.PartOne.KCOrthogonalAut
  (matrixProjectiveImage_eq_top_odd matrixProjectiveImage_eq_top_plus
    matrixProjectiveImage_eq_top_minus)
open CFSG.ClassicalGroups.Orthogonal (ringChar_eq_of_card_eq)
open CFSG.HardMathSupport.Solomon.Coordinator.SeitzOuterCube
  (subfieldFixedGroup_le_derivedImage_of_odd_finrank)

theorem not_isD2SeitzException_B_of_odd {p r : ℕ} {q : TauCeti.PrimePower} (hq : q.p ≠ 2) :
    ¬ IsD2SeitzException p (.B r q) := by
  rintro (⟨-, ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', hq2, -, hd | hd⟩ | hd⟩ |
      ⟨-, hd | hd⟩)
  all_goals cases hd
  all_goals exact hq ‹_›

theorem not_isD2SeitzException_D {p r : ℕ} {q : TauCeti.PrimePower} :
    ¬ IsD2SeitzException p (.D r q) := by
  rintro (⟨-, ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', -, -, hd | hd⟩ | hd⟩ |
      ⟨-, hd | hd⟩) <;> cases hd

theorem not_isD2SeitzException_twistedD {p r : ℕ} {q : TauCeti.PrimePower} :
    ¬ IsD2SeitzException p (.twistedD r q) := by
  rintro (⟨-, ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', -, -, hd⟩ | ⟨q', -, -, hd | hd⟩ | hd⟩ |
      ⟨-, hd | hd⟩) <;> cases hd

theorem subfieldFixedGroup_le_odd {n ℓ e p : ℕ} (hadm : StatedLieAdmissible .POmegaOdd n ℓ e)
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) (σ : K ≃+* K)
    (hσ : orderOf σ = p) (hσk : ∀ x, x ∈ k ↔ σ x = x) :
    subfieldFixedGroup k (coordinateQuadOdd n k) (coordinateQuadOdd n K) ≤
      subfieldDerivedImage k (coordinateQuadOdd_isExtension k n) := by
  obtain ⟨hℓ, he, hn3, hℓ2⟩ := hadm
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have h2K : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card_eq hℓ hf hK]
    exact hℓ2
  have S := subfieldSetup_odd k hσk hp hp2 hσ hn3 (Ring.two_ne_zero h2K)
  have hdeg := finrank_subfield_eq k hℓ he hk hK
  exact subfieldFixedGroup_le_derivedImage_of_odd_finrank k
    (by rw [hdeg]; exact hp.odd_of_ne_two hp2) S.hext S.hnd₀ S.hT₀ S.hnd

theorem subfieldFixedGroup_le_plus {n ℓ e p : ℕ} (hadm : StatedLieAdmissible .POmegaPlus n ℓ e)
    (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) (σ : K ≃+* K)
    (hσ : orderOf σ = p) (hσk : ∀ x, x ∈ k ↔ σ x = x) :
    subfieldFixedGroup k (coordinateQuadPlus n k) (coordinateQuadPlus n K) ≤
      subfieldDerivedImage k (coordinateQuadPlus_isExtension k n) := by
  obtain ⟨hℓ, he, hn4⟩ := hadm
  have S := subfieldSetup_plus k hσk hp hp2 hσ (by omega : 3 ≤ n)
  have hdeg := finrank_subfield_eq k hℓ he hk hK
  exact subfieldFixedGroup_le_derivedImage_of_odd_finrank k
    (by rw [hdeg]; exact hp.odd_of_ne_two hp2) S.hext S.hnd₀ S.hT₀ S.hnd

theorem subfieldFixedGroup_le_minus {n ℓ e p : ℕ} (hadm : StatedLieAdmissible .POmegaMinus n ℓ e)
    (hp : p.Prime) (hp2 : p ≠ 2) (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (k : Subfield K)
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) (σ : K ≃+* K)
    (hσ : orderOf σ = p) (hσk : ∀ x, x ∈ k ↔ σ x = x) (b c' : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c' ≠ 0) :
    subfieldFixedGroup k (coordinateQuadMinus n k hn b c')
        (coordinateQuadMinus n K hn (b : K) (c' : K)) ≤
      subfieldDerivedImage k (coordinateQuadMinus_isExtension k n hn b c') := by
  obtain ⟨hℓ, he, hn4⟩ := hadm
  have hdeg := finrank_subfield_eq k hℓ he hk hK
  have S := subfieldSetup_minus k hσk hp hp2 hσ hn4 hdeg b c' hirr
  exact subfieldFixedGroup_le_derivedImage_of_odd_finrank k
    (by rw [hdeg]; exact hp.odd_of_ne_two hp2) S.hext S.hnd₀ S.hT₀ S.hnd

theorem fixPlaneGen_orthOdd_kfact (hS : KFactSeitzRankTwo) {n ℓ f p : ℕ} {K : Type} [Field K]
    [Finite K] (hadm : StatedLieAdmissible .POmegaOdd n ℓ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) :
    FixPlaneGen (matrixProjectiveDerived (coordinateQuadOdd n K)) p := by
  classical
  obtain ⟨hℓ, hf, hn3, hℓ2⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n K))) .POmegaOdd n ℓ f :=
    ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadOdd n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaOdd (Or.inl rfl) n ℓ f hM
      K hK (MulEquiv.refl _)
  have h2K : ringChar K ≠ 2 := by
    rw [ringChar_eq_of_card_eq hℓ hf hK]
    exact hℓ2
  have htop := matrixProjectiveImage_eq_top_odd K n hn3 h2K
  refine fixPlaneGen_matrixProjectiveDerived _ hℓ hf hK hp
    (fun σ _ => coordinateQuadOdd_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaOdd (Or.inl rfl)
      n ℓ f p hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadOdd_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ A hA hAa hAc
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    have hadm0 : StatedLieAdmissible .POmegaOdd n ℓ e := ⟨hℓ, he, hn3, hℓ2⟩
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaOdd
        (Or.inl rfl) n ℓ e p hadm0 hp hp2 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ hσ hσk
    have hNJ' := subfieldFixedGroup_le_odd hadm0 hp hp2 (semilinearFixedSubfield σ) hcardk hK' σ
      hσ hσk
    obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
    have hrange : fixedSubgroup (fieldAutT (coordinateQuadOdd n K) σ
        (coordinateQuadOdd_fieldAut n σ)) =
        (incl (semilinearFixedSubfield σ) (coordinateQuadOdd_isExtension _ n)).range :=
      (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
    set k := semilinearFixedSubfield σ with hk
    let q0 : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
    have hv : (TauCeti.LieTypeIndex.B n q0).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨⟨by omega, fun h => by omega⟩, fun h => by omega⟩
    let d0 : TauCeti.ValidLieTypeIndex := ⟨.B n q0, hv⟩
    have hF0 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d0) = ℓ ^ e :=
      CFSG.RankThree.PartOne.CTP.card_fixedField_B n q0 hv
    have hF0fin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d0) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hM1 : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadOdd n
        ↥(TauCeti.ValidLieTypeIndex.fixedField d0)))) .POmegaOdd n ℓ e :=
      ⟨hadm0, _, inferInstance, inferInstance, hF0, ⟨MulEquiv.refl _⟩⟩
    have hkfin : Finite k := inferInstance
    have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadOdd n k))
        .POmegaOdd n ℓ e :=
      ⟨hadm0, k, inferInstance, inferInstance, hcardk,
        ⟨(coordinateOddWitnessEquiv (n := n) k (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨ε₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hM1 hM0
    let ε : Cat d0 ≃* matrixProjectiveDerived (coordinateQuadOdd n k) :=
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd n q0 hv hℓ2
        hn3).trans ε₁
    obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inl rfl) hM0
    have := hsimp0
    have hnab0 : ∃ a b : matrixProjectiveDerived (coordinateQuadOdd n k), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcon a b⟩⟩
    have hpd : p ≠ d0.1.characteristic := by
      have : d0.1.characteristic = ℓ := by simp [d0, q0]
      rw [this]; exact hpℓ
    have hexc : ¬ IsD2SeitzException p d0.1 := not_isD2SeitzException_B_of_odd hℓ2
    have hM' := closure_comm_planes_of_simple_kfact hS hnab0 ε hp hp2 hpd hexc
    rw [hrange] at hA ⊢
    exact planeGenIn_range _ hinj hM' A hA hAa hAc

theorem fixPlaneGen_orthPlus_kfact (hS : KFactSeitzRankTwo) {n ℓ f p : ℕ} {K : Type} [Field K]
    [Finite K] (hadm : StatedLieAdmissible .POmegaPlus n ℓ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) (h5 : 5 ≤ n ∨ 3 < p) :
    FixPlaneGen (matrixProjectiveDerived (coordinateQuadPlus n K)) p := by
  classical
  obtain ⟨hℓ, hf, hn4⟩ := id hadm
  have hM : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n K))) .POmegaPlus n ℓ
      f := ⟨hadm, K, inferInstance, inferInstance, hK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadPlus n K) f :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaPlus (Or.inr (Or.inl rfl))
      n ℓ f hM K hK (MulEquiv.refl _)
  refine fixPlaneGen_matrixProjectiveDerived _ hℓ hf hK hp
    (fun σ _ => coordinateQuadPlus_fieldAut n σ) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ : α ∈ matrixProjectiveImage (coordinateQuadPlus n K) ∧
        α ∉ (linearConjugationHom (coordinateQuadPlus n K)).range := by
      rcases h5 with hn5 | hp3
      · exact outer_mem_E_not_D_of_top hg (matrixProjectiveImage_eq_top_plus K n hn5) hp hp2 hα
      · exact outer_mem_E_not_D hg hp hp3 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaPlus
      (Or.inr (Or.inl rfl)) n ℓ f p hM hp hp2 K hK (MulEquiv.refl _) α hE hD hα.1
    exact exists_conj_fieldAutT_of_descent _ hE hdesc (fun σ _ => coordinateQuadPlus_fieldAut n σ)
      (fun U Q₀ _ hdisp => by
        obtain ⟨ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
        exact ⟨S, ν', hSQ, hSA⟩)
  · intro σ hσ A hA hAa hAc
    obtain ⟨hpf, hcardk⟩ := card_semilinearFixedSubfield hℓ hf hK hσ
    obtain ⟨e, rfl⟩ := hpf
    have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with h0 | h0
      · rw [h0, mul_zero] at hf
        omega
      · exact h0
    rw [Nat.mul_div_cancel_left e hp.pos] at hcardk
    have hK' : Nat.card K = ℓ ^ (e * p) := by rw [hK, mul_comm]
    have hσk : ∀ x, x ∈ semilinearFixedSubfield σ ↔ σ x = x := fun x => RingHom.mem_eqLocusField
    have hadm0 : StatedLieAdmissible .POmegaPlus n ℓ e := ⟨hℓ, he, hn4⟩
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaPlus
        (Or.inr (Or.inl rfl)) n ℓ e p hadm0 hp hp2 hpℓ K (semilinearFixedSubfield σ) hcardk hK' σ
        hσ hσk
    have hNJ' := subfieldFixedGroup_le_plus hadm0 hp hp2 (semilinearFixedSubfield σ) hcardk hK' σ
      hσ hσk
    obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
    have hrange : fixedSubgroup (fieldAutT (coordinateQuadPlus n K) σ
        (coordinateQuadPlus_fieldAut n σ)) =
        (incl (semilinearFixedSubfield σ) (coordinateQuadPlus_isExtension _ n)).range :=
      (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
    set k := semilinearFixedSubfield σ with hk
    let q0 : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
    have hv : (TauCeti.LieTypeIndex.D n q0).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hn4, fun h => h⟩
    let d0 : TauCeti.ValidLieTypeIndex := ⟨.D n q0, hv⟩
    have hF0 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d0) = ℓ ^ e := by
      rw [card_fixedField_eq]
      simp [d0, q0, TauCeti.ValidLieTypeIndex.characteristic,
        TauCeti.ValidLieTypeIndex.fieldExponent]
    have hF0fin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d0) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hM1 : StatedClassicalModel (StatedProj (StatedOmega (StatedQuadPlus n
        ↥(TauCeti.ValidLieTypeIndex.fixedField d0)))) .POmegaPlus n ℓ e :=
      ⟨hadm0, _, inferInstance, inferInstance, hF0, ⟨MulEquiv.refl _⟩⟩
    have hkfin : Finite k := inferInstance
    have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadPlus n k))
        .POmegaPlus n ℓ e :=
      ⟨hadm0, k, inferInstance, inferInstance, hcardk,
        ⟨(coordinatePlusWitnessEquiv (n := n) k (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨ε₁⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hM1 hM0
    let ε : Cat d0 ≃* matrixProjectiveDerived (coordinateQuadPlus n k) :=
      (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid n q0
        hv).trans ε₁
    obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inr (Or.inl rfl)) hM0
    have := hsimp0
    have hnab0 : ∃ a b : matrixProjectiveDerived (coordinateQuadPlus n k), a * b ≠ b * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b => hcon a b⟩⟩
    have hpd : p ≠ d0.1.characteristic := by
      have : d0.1.characteristic = ℓ := by simp [d0, q0]
      rw [this]; exact hpℓ
    have hM' := closure_comm_planes_of_simple_kfact hS hnab0 ε hp hp2 hpd not_isD2SeitzException_D
    rw [hrange] at hA ⊢
    exact planeGenIn_range _ hinj hM' A hA hAa hAc

theorem fixPlaneGen_minus_rational_kfact (hS : KFactSeitzRankTwo)
    {n ℓ e p : ℕ} {K : Type} [Field K] [Finite K] (hn : 4 ≤ n) (hn1 : 1 ≤ n)
    (hℓ : ℓ.Prime) (he : 1 ≤ e) (hp : p.Prime) (hp2 : p ≠ 2) (hpℓ : p ≠ ℓ) {k : Subfield K}
    (hk : Nat.card k = ℓ ^ e) (hK : Nat.card K = ℓ ^ (e * p)) {σ₀ : K ≃+* K}
    (hσ₀ : orderOf σ₀ = p) (hfix : ∀ x, x ∈ k ↔ σ₀ x = x) (b c : k)
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) :
    FixPlaneGen (matrixProjectiveDerived (coordinateQuadMinus n K hn1 (b : K) (c : K))) p := by
  classical
  have hf : 1 ≤ e * p := Nat.mul_pos he hp.pos
  have hfixall := fun σ (h : orderOf σ = p) => fixed_of_orderOf_orth hℓ he hp hK hσ₀ hfix h
  have hirrK : ∀ s : K, s ^ 2 + (b : K) * s + (c : K) ≠ 0 :=
    rootFree_of_odd_degree k hp hp2 (finrank_subfield_eq k hℓ he hk hK) b c hirr
  have hM : StatedClassicalModel
      (StatedProj (StatedOmega (StatedQuadMinus n K (b : K) (c : K)))) .POmegaMinus n ℓ (e * p) :=
    ⟨⟨hℓ, hf, hn⟩, K, inferInstance, inferInstance, hK, b, c, hirrK, ⟨MulEquiv.refl _⟩⟩
  have hg : OrthogonalGates (coordinateQuadMinus n K hn1 (b : K) (c : K)) (e * p) :=
    orthogonal_large_prime_semilinear_field_and_diagonal_gates _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) hM hn1 K hK b c hirrK (MulEquiv.refl _)
  have htop := matrixProjectiveImage_eq_top_minus K n hn (b : K) (c : K) hirrK
  refine fixPlaneGen_matrixProjectiveDerived _ hℓ hf hK hp
    (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_ ?_
  · intro α hα
    obtain ⟨hE, hD⟩ := outer_mem_E_not_D_of_top hg htop hp hp2 hα
    have hdesc := orthogonal_prime_semilinear_actual_fixed_form_descent' _ .POmegaMinus
      (Or.inr (Or.inr rfl)) n ℓ (e * p) p hM hp hp2 hn1 K hK b c hirrK (MulEquiv.refl _) α hE hD
      hα.1
    refine exists_conj_fieldAutT_of_descent _ hE hdesc
      (fun σ h v => coordinateQuadMinus_fieldAut k n hn1 (hfixall σ h) b c v) ?_
    intro U Q₀ hord hdisp
    obtain ⟨b', c', hirr', ν, S₀, -, -, S, ν', hSQ, -, hSA, -⟩ := hdisp
    have hfixV := hfixall U.val.right hord
    have hσk' : ∀ x, x ∈ semilinearFixedSubfield U.val.right ↔ U.val.right x = x :=
      fun x => RingHom.mem_eqLocusField
    have hb'k : (b' : K) ∈ k := (hfixV _).2 ((hσk' _).1 b'.2)
    have hc'k : (c' : K) ∈ k := (hfixV _).2 ((hσk' _).1 c'.2)
    have hirrkK : ∀ s ∈ k, s ^ 2 + (b : K) * s + (c : K) ≠ 0 := fun s hs hz =>
      hirr ⟨s, hs⟩ (Subtype.ext (by simpa using hz))
    have hirr'kK : ∀ s ∈ k, s ^ 2 + (b' : K) * s + (c' : K) ≠ 0 := by
      intro s hs hz
      have hsV : s ∈ KCOrthogonalDescent.fixedField U.val := (hσk' s).2 ((hfixV s).1 hs)
      exact hirr' ⟨s, hsV⟩ (Subtype.ext (by simpa using hz))
    obtain ⟨μ, hμk, hμQ⟩ :=
      SEITZ2.exists_tail_isometry k hn1 b.2 c.2 hb'k hc'k hirrkK hirr'kK
    have hμσ : glFieldAut (Fin (2 * n)) K U.val.right μ = μ :=
      Units.ext (Matrix.ext fun i j => (hfixV _).1 (hμk i j))
    refine ⟨μ * S, ν', fun v => ?_, ?_⟩
    · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
      exact (hμQ _).trans (hSQ v)
    · rw [mul_assoc, hSA, map_mul, hμσ]
  · intro σ hσ A hA hAa hAc
    obtain ⟨-, hconc⟩ :=
      orthogonal_prime_subfield_fixed_group_and_full_centralizer_odd .POmegaMinus
        (Or.inr (Or.inr rfl)) n ℓ e p ⟨hℓ, he, hn⟩ hp hp2 hpℓ hn1 K k hk hK σ hσ (hfixall σ hσ)
        b c hirr
    have hNJ' := subfieldFixedGroup_le_minus ⟨hℓ, he, hn⟩ hp hp2 hn1 k hk hK σ hσ (hfixall σ hσ)
      b c hirr
    obtain ⟨⟨hinj, -, -⟩, -, hfixiff, hJN, -⟩ := hconc
    have hrange : fixedSubgroup (fieldAutT (coordinateQuadMinus n K hn1 (b : K) (c : K)) σ
        (coordinateQuadMinus_fieldAut k n hn1 (hfixall σ hσ) b c)) =
        (incl k (coordinateQuadMinus_isExtension k n hn1 b c)).range :=
      (Subgroup.ext hfixiff).trans (le_antisymm hNJ' hJN)
    have hadm0 : StatedLieAdmissible .POmegaMinus n ℓ e := ⟨hℓ, he, hn⟩
    let q0 : TauCeti.PrimePower := ⟨ℓ, e, hℓ, he⟩
    have hv : (TauCeti.LieTypeIndex.twistedD n q0).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      exact ⟨hn, fun h => h⟩
    let d0 : TauCeti.ValidLieTypeIndex := ⟨.twistedD n q0, hv⟩
    have hF0 : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField d0) = ℓ ^ e := by
      rw [card_fixedField_eq]
      simp [d0, q0, TauCeti.ValidLieTypeIndex.characteristic,
        TauCeti.ValidLieTypeIndex.fieldExponent]
    have hF0fin : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField d0) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    obtain ⟨b0, c0, hirr0, ⟨eD⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        n q0 hv
    have hMcat : StatedClassicalModel (Cat d0) .POmegaMinus n ℓ e :=
      ⟨hadm0, _, inferInstance, inferInstance, hF0, b0, c0, hirr0, ⟨eD⟩⟩
    have hkfin : Finite k := inferInstance
    have hM0 : StatedClassicalModel (matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c))
        .POmegaMinus n ℓ e :=
      ⟨hadm0, k, inferInstance, inferInstance, hk, b, c, hirr,
        ⟨(coordinateMinusWitnessEquiv k hn1 b c (MulEquiv.refl _)).symm⟩⟩
    obtain ⟨ε⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hMcat hM0
    obtain ⟨-, hnt, hsimp0, hperf0⟩ := orth_facts_of_model (Or.inr (Or.inr rfl)) hM0
    have := hsimp0
    have hnab0 : ∃ a b' : matrixProjectiveDerived (coordinateQuadMinus n k hn1 b c),
        a * b' ≠ b' * a := by
      by_contra hcon
      push Not at hcon
      exact Group.IsPerfect.not_isMulCommutative _ ⟨⟨fun a b' => hcon a b'⟩⟩
    have hpd : p ≠ d0.1.characteristic := by
      have : d0.1.characteristic = ℓ := by simp [d0, q0]
      rw [this]; exact hpℓ
    have hM' := closure_comm_planes_of_simple_kfact hS hnab0 ε hp hp2 hpd
      not_isD2SeitzException_twistedD
    rw [hrange] at hA ⊢
    exact planeGenIn_range _ hinj hM' A hA hAa hAc

theorem fixPlaneGen_minus_of_model_kfact (hS : KFactSeitzRankTwo) {G : Type} [Group G]
    {n ℓ f p : ℕ} (hM : StatedClassicalModel G .POmegaMinus n ℓ f) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpℓ : p ≠ ℓ) : FixPlaneGen G p := by
  obtain ⟨hℓ, hf, hn⟩ := id hM.1
  have hn1 : 1 ≤ n := by omega
  by_cases hex : ∃ α : MulAut G, IsOuterOfOrder p α
  · obtain ⟨α, hα⟩ := hex
    obtain ⟨e, K, _, _, k, σ, b, c, he, -, hk, hK, hσ, hfix, hirr, ⟨ψ⟩⟩ :
        ∃ (e : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (k : Subfield K) (σ : K ≃+* K)
          (b c : k), 1 ≤ e ∧ f = p * e ∧ Nat.card k = ℓ ^ e ∧ Nat.card K = ℓ ^ (e * p) ∧
          orderOf σ = p ∧ (∀ x, x ∈ k ↔ σ x = x) ∧ (∀ s : k, s ^ 2 + b * s + c ≠ 0) ∧
          Nonempty (G ≃* matrixProjectiveDerived
            (coordinateQuadMinus n K hn1 (b : K) (c : K))) := by
      by_cases hp3 : p = 3
      · exact exists_rational_model_minus_three hn1 hM hp hp3 hα
      · have hp5 : 3 < p := by
          obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
          have := hp.two_le
          omega
        exact exists_rational_model_minus hn1 hM hp hp5 hpℓ hα
    exact FixPlaneGen.of_mulEquiv ψ hp
      (fixPlaneGen_minus_rational_kfact hS hn hn1 hℓ he hp hp2 hpℓ hk hK hσ hfix b c hirr)
  · intro σ hσ
    exact absurd ⟨σ, hσ⟩ hex

theorem fixPlaneGen_orthogonal_index_kfact (hS : KFactSeitzRankTwo)
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hpd : p ≠ d.1.characteristic)
    (hD4 : ¬ (p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q)) :
    FixPlaneGen (Cat d) p := by
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
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
    let e' := coordinateOddWitnessEquiv (n := r)
      ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) e
    exact FixPlaneGen.of_mulEquiv e' hp
      (fixPlaneGen_orthOdd_kfact hS ⟨q.prime_p, q.exponent_pos, hr3, hq⟩ hcard hp hp2 hq')
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := hrange
    have h5 : 5 ≤ r ∨ 3 < p := by
      by_cases hr : r = 4
      · subst hr
        right
        have hp3 : p ≠ 3 := fun h => hD4 ⟨h, q, rfl⟩
        obtain ⟨j, hj⟩ := hp.odd_of_ne_two hp2
        have := hp.two_le
        omega
      · left; omega
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    let e' := coordinatePlusWitnessEquiv (n := r)
      ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) e
    exact FixPlaneGen.of_mulEquiv e' hp
      (fixPlaneGen_orthPlus_kfact hS ⟨q.prime_p, q.exponent_pos, hr4⟩ hcard hp hp2 hq' h5)
  ·
    have hq' : p ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := hrange
    obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact fixPlaneGen_minus_of_model_kfact hS
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcard, b, c', hirr,
        ⟨e⟩⟩ hp hp2 hq'

theorem fieldAutData_orthogonal_index_three
    {d : TauCeti.ValidLieTypeIndex} (hd : IsOrthogonalIndex d.1)
    (hpd : 3 ≠ d.1.characteristic) (hD4 : ¬ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q) :
    FieldAutData (Cat d) 3 := by
  have := finite_cat_orthogonal hd
  obtain ⟨d, hv⟩ := d
  have hrange := (TauCeti.LieTypeIndex.inStandardRange_iff _).1
    ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases hd with ⟨r, q, rfl, hr3, hq⟩ | ⟨r, q, rfl⟩ | ⟨r, q, rfl⟩
  · have hq' : 3 ≠ q.p := by simpa using hpd
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinB.typeBGroupEquivStatedProj_odd r q hv hq
      hr3
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.B r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact fieldAutData_of_model_three subfieldPairOmegaThree_holds (Or.inl rfl) (n := r)
      (ℓ := q.p) (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr3, hq⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩
      (fun h => by cases h) Nat.prime_three rfl hq'
  · have hq' : 3 ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := hrange
    let e := CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact fieldAutData_of_model_three subfieldPairOmegaThree_holds (Or.inr (Or.inl rfl)) (n := r)
      (ℓ := q.p) (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, ⟨e⟩⟩
      (fun _ h4 => hD4 ⟨q, by subst h4; rfl⟩) Nat.prime_three rfl hq'
  · have hq' : 3 ≠ q.p := by simpa using hpd
    have hr4 : 4 ≤ r := hrange
    obtain ⟨b, c', hirr, ⟨e⟩⟩ :=
      CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
        r q hv
    have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) :=
      CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
    have hcardK : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.twistedD r q, hv⟩) =
        q.p ^ q.exponent := by
      rw [card_fixedField_eq]
      simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent]
    exact fieldAutData_of_model_three subfieldPairOmegaThree_holds (Or.inr (Or.inr rfl)) (n := r)
      (ℓ := q.p) (f := q.exponent)
      ⟨⟨q.prime_p, q.exponent_pos, hr4⟩, _, inferInstance, inferInstance, hcardK, b, c', hirr,
        ⟨e⟩⟩ (fun h => by cases h) Nat.prime_three rfl hq'

end Orthogonal

section Assembly

theorem excIndex_twistedA_eight {m : ℕ} {q : TauCeti.PrimePower} (hq : q.card = 8)
    (hm : ¬ 3 ∣ m + 1) : ExcIndex 3 (.twistedA m q) := by
  obtain ⟨hp2, he3⟩ := eq_two_three_of_card_eight (by rw [← TauCeti.PrimePower.card_def, hq])
  exact Or.inl ⟨rfl, Or.inl ⟨Or.inr ⟨hp2, he3⟩, hm⟩⟩

theorem seitzGoodOuterHighAt_linearUnitary (hS : KFactSeitzRankTwo) :
    SeitzGoodOuterHighAt fun d p =>
      ((∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .A m q ∧ ¬ p ∣ Nat.gcd (m + 1) (q.card - 1)) ∨
      (∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧
        ¬ p ∣ Nat.gcd (m + 1) (q.card + 1))) := by
  refine SeitzGoodOuterHighAt.of_pair ?_
  rintro ⟨d, hv⟩ p hd hp hp2 hpd - hx - hcube
  rcases hd with ⟨m, q, rfl, hg⟩ | ⟨m, q, rfl, hg⟩
  · have hpq : p ≠ q.p := by simpa using hpd
    have hm1 : 1 ≤ m := ((TauCeti.LieTypeIndex.inStandardRange_iff _).1
      ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1).1
    rcases (by omega : m = 1 ∨ 2 ≤ m) with rfl | hm2
    · exact (not_exists_cube_A_one hv hp hp2 hpq hcube).elim
    · exact pair_A hS hm2 hv hp hp2 hpq hg
  · have hpq : p ≠ q.p := by simpa using hpd
    refine pair_twistedA hv hp hp2 hpq hg ?_
    rintro ⟨hp3, hq8⟩
    subst hp3
    refine hg ?_
    by_cases h3 : 3 ∣ m + 1
    · exact Nat.dvd_gcd h3 (by rw [hq8]; norm_num)
    · exact absurd (excIndex_twistedA_eight hq8 h3) hx

theorem seitzGoodOuterHighAt_symplectic :
    SeitzGoodOuterHighAt fun d _ => IsSymplecticIndex d.1 := by
  refine SeitzGoodOuterHighAt.of_pair ?_
  rintro d p hd hp hp2 hpd - hx - -
  refine ⟨fieldAutData_symplectic_index hd hp hp2, ?_⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact fixPlaneGen_symplectic_index_three hd hpd hx
  · have hp5 : 5 ≤ p := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      have := hp.two_le
      omega
    exact fixPlaneGen_symplectic_index_five hd hp hp5 hpd

theorem seitzGoodOuterHighAt_orthogonal (hS : KFactSeitzRankTwo) :
    SeitzGoodOuterHighAt fun d p => IsOrthogonalIndex d.1 ∧
      ¬ (p = 3 ∧ ∃ q : TauCeti.PrimePower, d.1 = .D 4 q) := by
  refine SeitzGoodOuterHighAt.of_pair ?_
  rintro d p ⟨hd, hD4⟩ hp hp2 hpd - - - -
  refine ⟨?_, fixPlaneGen_orthogonal_index_kfact hS hd hp hp2 hpd hD4⟩
  by_cases hp3 : p = 3
  · subst hp3
    exact fieldAutData_orthogonal_index_three hd hpd (fun h => hD4 ⟨rfl, h⟩)
  · have hp5 : 3 < p := by
      obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
      have := hp.two_le
      omega
    exact fieldAutData_orthogonal_index (subfieldPairOmega_of_char2
        (subfieldPairOmegaPlusChar2_of_F2 subfieldPairOmegaPlusF2_holds)
        (subfieldPairOmegaMinusChar2_of_F2 subfieldPairOmegaMinusF2_holds)) hd hp hp5 hpd

theorem seitzGoodOuterHighClassical_of_diag (hS : KFactSeitzRankTwo)
    (hD : SeitzGoodOuterHighClassicalDiag) : SeitzGoodOuterHighClassical := by
  refine seitzGoodOuterHighFor_of_at (SeitzGoodOuterHighAt.of_cover (Q := fun d p =>
      ((∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .A m q ∧ ¬ p ∣ Nat.gcd (m + 1) (q.card - 1)) ∨
      (∃ (m : ℕ) (q : TauCeti.PrimePower), d.1 = .twistedA m q ∧
        ¬ p ∣ Nat.gcd (m + 1) (q.card + 1))) ∨ IsSymplecticIndex d.1)
    ?_ (SeitzGoodOuterHighAt.of_cover (fun _ _ h => h) (seitzGoodOuterHighAt_linearUnitary hS)
      seitzGoodOuterHighAt_symplectic)
    (SeitzGoodOuterHighAt.of_cover (fun _ _ h => h) hD (seitzGoodOuterHighAt_orthogonal hS)))
  rintro ⟨d, hv⟩ p hc
  have hrange := ((TauCeti.LieTypeIndex.valid_iff _).1 hv).1
  rcases (isClassicalIndex_iff hrange).1 hc with ⟨m, q, rfl⟩ | ⟨m, q, rfl⟩ | hsp | hor
  · by_cases hg : p ∣ Nat.gcd (m + 1) (q.card - 1)
    · exact Or.inr (Or.inl (Or.inl ⟨m, q, rfl, hg⟩))
    · exact Or.inl (Or.inl (Or.inl ⟨m, q, rfl, hg⟩))
  · by_cases hg : p ∣ Nat.gcd (m + 1) (q.card + 1)
    · exact Or.inr (Or.inl (Or.inr (Or.inl ⟨m, q, rfl, hg⟩)))
    · exact Or.inl (Or.inl (Or.inr ⟨m, q, rfl, hg⟩))
  · exact Or.inl (Or.inr hsp)
  · by_cases hD4 : p = 3 ∧ ∃ q : TauCeti.PrimePower, d = .D 4 q
    · exact Or.inr (Or.inl (Or.inr (Or.inr hD4)))
    · exact Or.inr (Or.inr ⟨hor, hD4⟩)

end Assembly

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterHigh

end
