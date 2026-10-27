module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Claims1110l
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1419b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110l

open CFSG.Open

section D4Field

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.RankThree.Classical.SteinbergBY
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalOuter (linearConjugationHom)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem card_eq_card_map_mul_card_inf_ker_d4up {X Y : Type*} [Group X] [Group Y] (f : X →* Y)
    (H : Subgroup X) : Nat.card ↥H = Nat.card ↥(H.map f) * Nat.card ↥(H ⊓ f.ker) := by
  have h := Subgroup.card_ker_mul_card_range (f.comp H.subtype)
  rw [MonoidHom.range_comp, Subgroup.range_subtype] at h
  have hk : Nat.card ↥(f.comp H.subtype).ker = Nat.card ↥(H ⊓ f.ker) := by
    have e1 : (f.comp H.subtype).ker = (H ⊓ f.ker).subgroupOf H := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rw [e1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hk] at h
  rw [← h, mul_comm]

theorem card_le_five_cube_of_D4_32 {K : Type} [Group K] [Finite K]
    (hK : StatedClassicalModel K .POmegaPlus 4 2 5) (A : Subgroup (MulAut K))
    (hA : IsElemAbelian 5 A) : Nat.card ↥A ≤ 5 ^ 3 := by
  classical
  have hp5 : Nat.Prime 5 := by norm_num
  haveI : Fact (Nat.Prime 5) := ⟨hp5⟩
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hK.2
  have hg := orthogonal_large_prime_semilinear_field_and_diagonal_gates K .POmegaPlus
    (Or.inr (Or.inl rfl)) 4 2 5 hK F hF e
  obtain ⟨hchar, hnd, hT, -⟩ := coordinate_model_witness_plus hK F hF e
  set Q := coordinateQuadPlus 4 F with hQ
  set Θ := coordinatePlusWitnessEquiv F e with hΘ
  set A' : Subgroup (MulAut (matrixProjectiveDerived Q)) := A.map (MulAut.congr Θ).toMonoidHom
    with hA'
  have hA'ea : IsElemAbelian 5 A' := CFSG.SectionRank.isElemAbelian_map hA _
  have hA'c : Nat.card ↥A' = Nat.card ↥A :=
    Subgroup.card_map_of_injective (MulAut.congr Θ).injective
  have hA'K0 : A' ≤ familyOrbitKernel Q := hg.2.2.2.2.2.2.1 5 hp5 (by norm_num) A' hA'ea.isPGroup
  have hA'E : A' ≤ matrixProjectiveImage Q := fun a ha => by
    have h1 := hg.2.2.2.2.1 (hA'K0 ha)
    rwa [hg.2.2.2.2.2.1] at h1
  obtain ⟨ψ, -, hψker, hψcyc⟩ := hg.2.1
  obtain ⟨-, k, hk⟩ := hg.2.2.1
  set B : Subgroup ↥(matrixProjectiveImage Q) := A'.subgroupOf (matrixProjectiveImage Q) with hB
  have hBc : Nat.card ↥B = Nat.card ↥A' :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA'E).toEquiv
  have hBea : IsElemAbelian 5 B := OmegaFacts2.isElemAbelian_comap Subtype.val_injective hA'ea
  have hψB : Nat.card ↥(B.map ψ) ≤ 5 := by
    haveI := hψcyc
    have hle : B.map ψ ≤ ψ.range := Subgroup.map_le_range ψ B
    set C : Subgroup ↥ψ.range := (B.map ψ).subgroupOf ψ.range with hC
    have hCc : Nat.card ↥C = Nat.card ↥(B.map ψ) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
    have hBψea := CFSG.SectionRank.isElemAbelian_map hBea ψ
    have hexp : Monoid.exponent ↥C ∣ 5 := Monoid.exponent_dvd_of_forall_pow_eq_one fun c => by
      have hc : ((c : ↥ψ.range) : (F ≃+* F)) ∈ B.map ψ := c.2
      have h5 := hBψea.2 _ hc
      apply Subtype.ext
      apply Subtype.ext
      simpa using h5
    rw [← hCc, ← IsCyclic.exponent_eq_card]
    exact Nat.le_of_dvd (by norm_num) hexp
  set N : Subgroup ↥(matrixProjectiveImage Q) := B ⊓ ψ.ker with hN
  have hsplit : Nat.card ↥B = Nat.card ↥(B.map ψ) * Nat.card ↥N :=
    card_eq_card_map_mul_card_inf_ker_d4up ψ B
  have hNinn : ∀ b ∈ N, (b : MulAut (matrixProjectiveDerived Q)) ∈ inner (matrixProjectiveDerived Q) := by
    intro b hb
    obtain ⟨hbB, hbk⟩ := Subgroup.mem_inf.1 hb
    have hbD : (b : MulAut (matrixProjectiveDerived Q)) ∈ (linearConjugationHom Q).range := by
      rw [hψker] at hbk
      exact hbk
    have hb5 : (b : MulAut (matrixProjectiveDerived Q)) ^ 5 = 1 := by
      have h1 := hBea.2 b hbB
      exact congrArg Subtype.val h1
    exact CFSG.RankThree.PartOne.KCOrthogonalNoninner.mem_of_pow_eq_one_of_relIndex_eq_two_pow hk
      hp5 (by norm_num) hbD hb5
  have hNea : IsElemAbelian 5 N := hBea.mono inf_le_left
  set S : Subgroup (MulAut (matrixProjectiveDerived Q)) := N.map (matrixProjectiveImage Q).subtype
    with hS
  have hSc : Nat.card ↥S = Nat.card ↥N := Subgroup.card_map_of_injective Subtype.val_injective
  have hSea : IsElemAbelian 5 S := CFSG.SectionRank.isElemAbelian_map hNea _
  have hSinn : S ≤ (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)).range := by
    rintro _ ⟨b, hb, rfl⟩
    exact hNinn b hb
  have hcen : Subgroup.center (matrixProjectiveDerived Q) = ⊥ :=
    CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot (by norm_num : 0 < 2 * 4) hnd hT
  have hinj : Function.Injective
      (MulAut.conj : matrixProjectiveDerived Q →* MulAut (matrixProjectiveDerived Q)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hcen]
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    refine Subgroup.mem_center_iff.2 fun g => ?_
    have h1 : a * g * a⁻¹ = g := by
      have := congrArg (fun φ : MulAut (matrixProjectiveDerived Q) => φ g) ha
      simpa [MulAut.conj_apply] using this
    calc g * a = a * g * a⁻¹ * a := by rw [h1]
      _ = a * g := by group
  set S₀ : Subgroup (matrixProjectiveDerived Q) := S.comap MulAut.conj with hS₀
  have hS₀ea : IsElemAbelian 5 S₀ := OmegaFacts2.isElemAbelian_comap hinj hSea
  have hS₀c : Nat.card ↥S₀ = Nat.card ↥S := by
    conv_rhs => rw [← Subgroup.map_comap_eq_self hSinn]
    exact (Subgroup.card_map_of_injective hinj).symm
  haveI : CharP F 2 := ringChar.of_eq hchar
  have hZ : matrixDerivedScalars Q = ⊥ :=
    CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.matrixDerivedScalars_eq_bot_of_charTwo Q
      (CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.exists_ne_zero_of_polar_nondegenerate
        (by norm_num) hnd)
  let ι : matrixProjectiveDerived Q →* GL (Fin (2 * 4)) F :=
    (matrixDerived Q).subtype.comp
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).toMonoidHom
  have hιinj : Function.Injective ι :=
    Subtype.val_injective.comp
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).injective
  set S₃ : Subgroup (GL (Fin (2 * 4)) F) := S₀.map ι with hS₃
  have hS₃c : Nat.card ↥S₃ = Nat.card ↥S₀ := Subgroup.card_map_of_injective hιinj
  have hS₃ea : IsElemAbelian 5 S₃ := CFSG.SectionRank.isElemAbelian_map hS₀ea ι
  have h5F : ((5 : ℕ) : F) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff F 2 5).1 h
    omega
  have hdiv : ∀ i : ℕ, 0 < i → i < 4 → ¬ 5 ∣ Nat.card F ^ i - 1 := by
    intro i hi0 hi4
    rw [hF]
    interval_cases i <;> norm_num
  have hS₃le := CFSG.RankThree.PartOne.LIT.card_le_pow_div_gl hp5 h5F (by norm_num : 0 < 4) hdiv
    S₃ (fun g hg h hh => hS₃ea.comm hg hh) (fun g hg => hS₃ea.2 g hg)
  rw [Fintype.card_fin] at hS₃le
  have hN25 : Nat.card ↥N ≤ 25 := by
    rw [← hSc, ← hS₀c, ← hS₃c]
    exact hS₃le
  calc Nat.card ↥A = Nat.card ↥(B.map ψ) * Nat.card ↥N := by rw [← hA'c, ← hBc, hsplit]
    _ ≤ 5 * 25 := Nat.mul_le_mul hψB hN25
    _ = 5 ^ 3 := by norm_num

end D4Field

section Narrow

open CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf)
open CFSG.Yardstones.Md0ec50421ce4 (IsChevSimple)

theorem statedClassicalModel_of_lieModel_D4 {D : Type} [Group D] {f : ℕ}
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 f) : StatedClassicalModel D .POmegaPlus 4 2 f :=
  hD.2.elim id fun h0 => absurd h0.1 (by norm_num)

theorem card_of_lieModel_D4_two {D : Type} [Group D] (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) :
    Nat.card D = 174182400 := by
  rw [(CFSG.Timmesfeld.card_statedClassicalModel_two (statedClassicalModel_of_lieModel_D4 hD)).2.2.2.1
    rfl]
  decide

theorem center_eq_bot_of_lieModel_D4 {D : Type} [Group D] {f : ℕ}
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 f) : Subgroup.center D = ⊥ := by
  have hSCM := statedClassicalModel_of_lieModel_D4 hD
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := hSCM.2
  obtain ⟨-, hnd, hT, -⟩ := coordinate_model_witness_plus hSCM F hF e
  exact center_eq_bot_of_mulEquiv_d4up (coordinatePlusWitnessEquiv F e)
    (CFSG.RankThree.PartOne.KCOrthogonalSubfield.center_matrix_eq_bot (by norm_num : 0 < 2 * 4) hnd hT)

theorem not_mulEquiv_alt_of_lieModel_D4 {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) (m : ℕ) :
    ¬ Nonempty (D ≃* alternatingGroup (Fin m)) := by
  rintro ⟨f⟩
  have hc := Nat.card_congr f.toEquiv
  rw [card_of_lieModel_D4_two hD] at hc
  rcases Nat.lt_or_ge m 5 with h5 | h5
  · have hle : Nat.card (alternatingGroup (Fin m)) ≤ 24 := by
      have h1 := Subgroup.card_le_card_group (alternatingGroup (Fin m))
      rw [Nat.card_perm, Nat.card_fin] at h1
      have h2 : m.factorial ≤ (4 : ℕ).factorial := Nat.factorial_le (by omega)
      have h3 : (4 : ℕ).factorial = 24 := by decide
      omega
    omega
  · have h2 := CFSG.HardMathSupport.Curtis.Coordinator.PLType.two_mul_card_alt_fin m h5
    rw [← hc] at h2
    rcases Nat.lt_or_ge m 12 with h12 | h12
    · have h3 : m.factorial ≤ (11 : ℕ).factorial := Nat.factorial_le (by omega)
      have h4 : (11 : ℕ).factorial = 39916800 := by decide
      omega
    · have h3 : (12 : ℕ).factorial ≤ m.factorial := Nat.factorial_le h12
      have h4 : (12 : ℕ).factorial = 479001600 := by decide
      omega

theorem not_pumpup_alt_of_lieModel_D4 {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) (hO : GLAPPrimeCore 5 K = ⊥) {N : ℕ} (hN : 5 ≤ N)
    (f : (K ⧸ Subgroup.center K) ≃* alternatingGroup (Fin N)) (x : MulAut K)
    (hx : Lemma1314.PumpupVia 5 D K x) : False := by
  obtain ⟨hxo, J1, hJ1, ⟨eJ⟩⟩ := hx
  have hp : Nat.Prime 5 := by norm_num
  have hA : ∀ a ∈ Subgroup.zpowers x, a ^ 5 = 1 := by
    rintro a ⟨k, rfl⟩
    simp only
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hxo, pow_orderOf_eq_one,
      one_zpow]
  obtain ⟨τ, -, hτ⟩ := AltFacts5.exists_tau (by decide : Odd 5) hN hK.1 f hA
  set σ : Equiv.Perm (Fin N) := τ ⟨x, Subgroup.mem_zpowers x⟩ with hσ
  have hσp : σ ^ 5 = 1 := by
    rw [hσ, ← map_pow]
    have h1 : (⟨x, Subgroup.mem_zpowers x⟩ : ↥(Subgroup.zpowers x)) ^ 5 = 1 :=
      Subtype.ext (hA x (Subgroup.mem_zpowers x))
    rw [h1, map_one]
  have hJ1' : GLAPComponent 5 (CFSG.LocalAnalysis.GLTheoremB.MovingAround.fixSub x) J1 := by
    rw [← Inputs1419.lemma1314_fixSub_eq]
    exact hJ1
  obtain ⟨-, ⟨g⟩⟩ := AltFacts5.component_alt hp (by norm_num) (AltFacts5.isAltRep_of_equiv f)
    (Inputs1419.isPGroup_center hp hO) (fun y => hτ ⟨x, Subgroup.mem_zpowers x⟩ y) hσp hJ1'
  have hZ : Subgroup.center (barOf 5 J1) = ⊥ :=
    center_eq_bot_of_mulEquiv_d4up eJ (center_eq_bot_of_lieModel_D4 hD)
  exact not_mulEquiv_alt_of_lieModel_D4 hD _
    ⟨eJ.symm.trans ((Inputs1419.quotCenterEquivOfBot hZ).symm.trans g)⟩

theorem spor_cases_of_lieModel_D4 (hOrd : CFSG.HardMathSupport.Solomon.Coordinator.SporadicOrdersTable)
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K) {name : TauCeti.SporadicName}
    (f : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.sporadic name).Group) {x : MulAut K}
    (hx : Lemma1314.PumpupVia 5 D K x) :
    name = .Co1 ∨ name = .Co2 ∨ name = .Th ∨ name = .HN ∨ name = .B ∨ name = .M := by
  obtain ⟨hxo, J1, hJ1, ⟨eJ⟩⟩ := hx
  have hJ1' : GLAPComponent 5 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x) J1 := by
    rw [show CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x = Lemma1314.fixSub x from
      Subgroup.ext fun _ => Iff.rfl]
    exact hJ1
  obtain ⟨s, hs, I, hI, ⟨eI⟩⟩ :=
    Inputs1419b.exists_spor_comp hOut (by norm_num) (by norm_num) hK f hxo hJ1'
  have hZD : Subgroup.center D = ⊥ := center_eq_bot_of_lieModel_D4 hD
  have e1 : CFSG.Yardstones.Md0ec50421ce4.PSimple 5 J1 ≃* D :=
    (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).trans
      (Inputs1419.quotCenterEquivOfBot hZD)
  have hcard : Nat.card (CFSG.Yardstones.Md0ec50421ce4.PSimple 5 I) = 174182400 := by
    rw [← Nat.card_congr (e1.symm.trans eI).toEquiv, card_of_lieModel_D4_two hD]
  have hdvd : 5 * 174182400 ∣ CFSG.HardMathSupport.Solomon.Coordinator.sporOrd name := by
    rw [← hcard, ← hOrd name, ← Nat.card_congr f.toEquiv]
    exact (Inputs1419b.mul_card_pSimple_dvd (by norm_num) hs hI).trans
      (Subgroup.card_subgroup_dvd_card _)
  revert hdvd
  cases name <;> decide +kernel

section ChevOdd

theorem not_isChevSimple_odd_of_lieModel_D4 {S : Type} [Group S] [Finite S]
    (hX : CFSG.Blueprint.LieModel S .POmegaPlus 4 2 1) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (h : IsChevSimple r S) : False := by
  have h2 : (Nat.card S).factorization 2 = 12 := by
    rw [Inputs1419.factorization_two_of_lieModel hX]
    simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent]
  have hbig : 2 ^ 12 ≤ Nat.card S := by
    have hdvd : 2 ^ (Nat.card S).factorization 2 ∣ Nat.card S := Nat.ordProj_dvd _ _
    have hle := Nat.le_of_dvd Nat.card_pos hdvd
    rwa [h2] at hle
  rcases h with hq | ha
  · obtain ⟨-, -, t', n', f', hY⟩ := CrossCharOdd.lie_cases hq
    have hodd : CFSG.Blueprint.OddLieType S := ⟨t', n', r, f', hr, hr2, hY.admissible, hY⟩
    rcases CFSG.SeitzReduction.CrossChar.eq_of_lieModel_two_of_oddLieType
        CFSG.ComponentClassification.CatLeafProof.lieOrderFormulasInput hX hodd with
      ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ <;> exact absurd h1 (by decide)
  · rcases CrossCharOdd.ambig_cases hr2 ha with ⟨⟨a⟩, -⟩ | ⟨⟨a⟩, -⟩ | ⟨-, -, -, hY | hY⟩
    · have hc : Nat.card S = 60 := by
        rw [Nat.card_congr a.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
    · have hc : Nat.card S = 360 := by
        rw [Nat.card_congr a.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
        simp [Nat.factorial]
      omega
    · have h3 := Inputs1419.factorization_two_of_lieModel hY
      simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h3
      omega
    · have h6 := Inputs1419.factorization_two_of_lieModel hY
      simp [CFSG.ComponentClassification.CatLeaf.lieSylowExponent] at h6
      omega

theorem not_pumpup_lie_odd_of_lieModel_D4 (h1441 : Lemma1315b.Input14_4_1) {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hK : CFSG.LocalAnalysis.GLTheoremA.IsKHat K) (hO : GLAPPrimeCore 5 K = ⊥) {x : MulAut K}
    (hx : Lemma1314.PumpupVia 5 D K x) {d : TauCeti.ValidLieTypeIndex}
    (hd2 : d.1.characteristic ≠ 2)
    (e : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.lie d).Group) : False := by
  have hr : d.1.characteristic.Prime := d.characteristic_prime
  have hchev : IsChevSimple d.1.characteristic (K ⧸ Subgroup.center K) := Or.inl ⟨.lie d, rfl, ⟨e⟩⟩
  obtain ⟨hJr, -⟩ := h1441 5 _ (by norm_num) le_rfl hr K hK hO hchev D x hx
  have hSCM := statedClassicalModel_of_lieModel_D4 hD
  obtain ⟨F, _, _, hF, ⟨eD⟩⟩ := hSCM.2
  have hZ := center_eq_bot_of_lieModel_D4 hD
  haveI : Finite D := by
    have := card_of_lieModel_D4_two hD
    exact Nat.finite_of_card_ne_zero (by omega)
  have hX : CFSG.Blueprint.LieModel (D ⧸ Subgroup.center D) .POmegaPlus 4 2 1 :=
    Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
      ⟨hSCM.1, F, inferInstance, inferInstance, hF, ⟨(Inputs1419.quotCenterEquivOfBot hZ).trans eD⟩⟩⟩
  exact not_isChevSimple_odd_of_lieModel_D4 hX hr hd2 hJr

end ChevOdd

section Co2

open CFSG.RankThree.Native CFSG.Sporadic.Co2Cert

theorem not_pumpup_co2_of_lieModel_D4
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo)
    (hbr : CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicBridges) {D : Type} [Group D]
    (hD : CFSG.Models.LieModel D .POmegaPlus 4 2 1) {K : Type} [Group K] [Finite K]
    (hK : CFSG.Open.IsQuasisimple K)
    (f : (K ⧸ Subgroup.center K) ≃* (TauCeti.CFSGIndex.sporadic .Co2).Group) {x : MulAut K}
    (hx : Lemma1314.PumpupVia 5 D K x) : False := by
  obtain ⟨hxo, J1, hJ1, ⟨eJ⟩⟩ := hx
  have hJ1' : GLAPComponent 5 (CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x) J1 := by
    rw [show CFSG.HardMathSupport.Solomon.Coordinator.fixSubgroup x = Lemma1314.fixSub x from
      Subgroup.ext fun _ => Iff.rfl]
    exact hJ1
  obtain ⟨s, hs, I, hI, ⟨eI⟩⟩ :=
    Inputs1419b.exists_spor_comp hOut (by norm_num) (by norm_num) hK f hxo hJ1'
  have hZD : Subgroup.center D = ⊥ := center_eq_bot_of_lieModel_D4 hD
  have e1 : CFSG.Yardstones.Md0ec50421ce4.PSimple 5 J1 ≃* D :=
    (QuotientGroup.congr _ _ eJ (Subgroup.map_center_eq eJ)).trans
      (Inputs1419.quotCenterEquivOfBot hZD)
  have hcard : Nat.card (CFSG.Yardstones.Md0ec50421ce4.PSimple 5 I) = 174182400 := by
    rw [← Nat.card_congr (e1.symm.trans eI).toEquiv, card_of_lieModel_D4_two hD]
  have h1 := Inputs1419b.mul_card_pSimple_dvd (by norm_num) hs hI
  rw [hcard] at h1
  let e : (K ⧸ Subgroup.center K) ≃* ↥co2P := f.trans (co2PermEquiv.symm.trans (hbr .Co2).some).symm
  have hC : Nat.card (Subgroup.centralizer ({s} : Set (K ⧸ Subgroup.center K))) =
      Nat.card (Subgroup.centralizer ({e s} : Set ↥co2P)) := by
    rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_mulEquiv e s,
      Subgroup.card_map_of_injective e.injective]
  have hes : orderOf (e s) = 5 := by rw [MulEquiv.orderOf_eq, hs]
  have h2 := Inputs1419b.card_centralizer_co2P_le (e s) (e s).2
    (by rw [Subgroup.orderOf_coe]; exact hes)
  rw [← CFSG.HardMathSupport.Solomon.Coordinator.map_centralizer_subtype co2P (e s),
    Subgroup.card_map_of_injective co2P.subtype_injective] at h2
  have h3 := Nat.le_of_dvd Nat.card_pos h1
  omega

end Co2

@[expose] def InputD4UpClassChev2Spor : Prop :=
  ∀ (K : Type) [Group K] [Finite K], CFSG.LocalAnalysis.GLTheoremA.IsKHat K → GLAPPrimeCore 5 K = ⊥ →
    ((∃ s : TauCeti.SporadicName, (s = .Co1 ∨ s = .Th ∨ s = .HN ∨ s = .B ∨ s = .M) ∧
        IsSporType s (K ⧸ Subgroup.center K)) ∨ IsLieChar (· = 2) K) →
    ∀ (D : Type) [Group D], CFSG.Models.LieModel D .POmegaPlus 4 2 1 →
    ∀ x : MulAut K, Lemma1314.PumpupVia 5 D K x →
      (∃ (ε : Bool) (m : ℕ), 4 ≤ m ∧ IsOmegaTwo ε m K) ∨ CFSG.Models.LieModel K .POmegaPlus 4 2 5

end Narrow

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Claims1110l
