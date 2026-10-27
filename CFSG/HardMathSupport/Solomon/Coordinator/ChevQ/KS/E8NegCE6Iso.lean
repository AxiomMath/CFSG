module

public import CFSG.RankThree.PartOne.KE6.E6LLayer
public import CFSG.HardMathSupport.Curtis.UnitaryLevi.ExcWeylWords
public import CFSG.LieType.SeitzGeneration.ExcParabolicTw

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8NegC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.RankThree.PartOne.KE6 CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge
  CFSG.HardMathSupport.Curtis.UnitaryLevi CFSG.RankThree.PartOne.KD4T
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)

set_option linter.unusedSectionVars false


section Std

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem psi2_injective : Function.Injective (psi2 τ L ℓ f) := by
  intro x y hxy
  apply Subtype.ext
  have h1 := baseChangeGL_injective _ hxy
  exact (m27Equiv τ (K2 L ℓ f)).symm.injective (Subtype.ext h1)

theorem theta2_eq_pow (c : K2 L ℓ f) : theta2 L ℓ f c = c ^ (ℓ ^ f) :=
  Subtype.ext (by rw [theta2_apply, SubmonoidClass.coe_pow])

theorem four_le_card_K2 (hf : 1 ≤ f) : 4 ≤ Nat.card (K2 L ℓ f) := by
  rw [card_K2 hf]
  have h2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left h2 2
    _ ≤ ℓ ^ (2 * f) := Nat.pow_le_pow_right (by omega) (by omega)

theorem card_K2_eq_pow_order (hf : 1 ≤ f) :
    Nat.card (K2 L ℓ f) = (ℓ ^ f) ^ TwistTag.E6.order := by
  rw [card_K2 hf, ← pow_mul]
  congr 1
  change 2 * f = f * 2
  ring

theorem range_e6IsogenyFixed_theta2 (hf : 1 ≤ f) :
    haveI : Finite (K2 L ℓ f) := finite_frobeniusFixedField (by omega)
    (Isogeny.e6IsogenyFixed (theta2 L ℓ f)).range =
      graphFixedRootGroup TwistTag.E6 (K2 L ℓ f) (theta2 L ℓ f) := by
  haveI : Finite (K2 L ℓ f) := finite_frobeniusFixedField (by omega)
  rw [Isogeny.range_e6IsogenyFixed (theta2 L ℓ f) theta2_theta2 (four_le_card_K2 hf)]
  exact (finite_fixed_root_group_perfect TwistTag.E6 (Fact.out : ℓ.Prime) hf (K2 L ℓ f)
    (card_K2_eq_pow_order hf) (theta2 L ℓ f) theta2_eq_pow).2.2.1

theorem exists_surj_stdLayer (hf : 1 ≤ f) {n₁ : ModGL τ L} (hstd : StdTwist6 n₁ (rhoτ τ)) :
    ∃ ρ : stdLayer τ ℓ f n₁ →* graphFixedRootGroup TwistTag.E6 (K2 L ℓ f) (theta2 L ℓ f),
      Function.Surjective ρ ∧ ∀ z ∈ ρ.ker, ∀ u, z * u = u * z := by
  classical
  haveI : Finite (K2 L ℓ f) := finite_frobeniusFixedField (by omega)
  have hrange := range_e6IsogenyFixed_theta2 (L := L) (ℓ := ℓ) hf
  have hP1 := hstd.stdLayer_eq_range_of_rho (ℓ := ℓ) (f := f) rfl
  set ι : TwistedE6.fixedGroup (K2 L ℓ f) (theta2 L ℓ f) ≃* stdLayer τ ℓ f n₁ :=
    (MonoidHom.ofInjective (psi2_injective (τ := τ))).trans (MulEquiv.subgroupCongr hP1.symm)
    with hι
  set φ : TwistedE6.fixedGroup (K2 L ℓ f) (theta2 L ℓ f) →*
      graphFixedRootGroup TwistTag.E6 (K2 L ℓ f) (theta2 L ℓ f) :=
    (Isogeny.e6IsogenyFixed (theta2 L ℓ f)).codRestrict _ (fun g => by
      rw [← hrange]
      exact ⟨g, rfl⟩) with hφ
  refine ⟨φ.comp ι.symm.toMonoidHom, ?_, ?_⟩
  · intro y
    have hy : (y : ModGL TwistTag.E6.tag (K2 L ℓ f)) ∈
        (Isogeny.e6IsogenyFixed (theta2 L ℓ f)).range := by
      rw [hrange]
      exact y.2
    obtain ⟨g, hg⟩ := hy
    refine ⟨ι g, ?_⟩
    apply Subtype.ext
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply, hφ,
      MonoidHom.codRestrict_apply]
    exact hg
  · intro z hz u
    have hz' : Isogeny.e6IsogenyFixed (theta2 L ℓ f) (ι.symm z) = 1 := by
      have h1 := congrArg Subtype.val ((MonoidHom.mem_ker).1 hz)
      simpa [hφ] using h1
    have hker : ((ι.symm z : TwistedE6.fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :
        CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (K2 L ℓ f)) ∈
          (Isogeny.e6IsogenyT (K2 L ℓ f)).ker := by
      rw [MonoidHom.mem_ker]
      apply Subtype.ext
      rw [Isogeny.e6IsogenyFixed_apply] at hz'
      exact hz'
    have hc := Isogeny.ker_e6IsogenyT_le_center (K2 L ℓ f) hker
    have hcomm : ι.symm z * ι.symm u = ι.symm u * ι.symm z := by
      apply Subtype.ext
      exact (Subgroup.mem_center_iff.1 hc
        ((ι.symm u : TwistedE6.fixedGroup (K2 L ℓ f) (theta2 L ℓ f)) :
          CFSG.LieType.Steinberg.Minuscule.e6Data_valid.minGroup (K2 L ℓ f))).symm
    have h2 := congrArg ι hcomm
    simpa only [map_mul, MulEquiv.apply_symm_apply] using h2

end Std

section Layer

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem ker_eq_center_of_surjective {P C : Type*} [Group P] [Group C] (ρ : P →* C)
    (hρ : Function.Surjective ρ) (hkc : ∀ z ∈ ρ.ker, ∀ u : P, z * u = u * z)
    (hC : Subgroup.center C = ⊥) : ρ.ker = Subgroup.center P := by
  ext z
  constructor
  · intro hz
    rw [Subgroup.mem_center_iff]
    intro u
    exact (hkc z hz u).symm
  · intro hz
    have h : ρ z ∈ Subgroup.center C := by
      rw [Subgroup.mem_center_iff]
      intro c
      obtain ⟨u, rfl⟩ := hρ c
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hz u]
    rw [hC, Subgroup.mem_bot] at h
    exact h

theorem nonempty_layer_quotient_equiv_cat (hf : 1 ≤ f) {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (e6Set τ))
    (hact : ∀ j ∈ e6Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (rhoτ τ j) 1 : Fin τ.rank → ℤ))
    (P : Subgroup (ModGL τ L)) (hP : P = rootSpan τ L (parabolicRoots τ (e6Nodes τ)) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))))
    {q : TauCeti.PrimePower} (hq : q.card = ℓ ^ f)
    (hv : (TauCeti.LieTypeIndex.twistedE6 q).Valid) :
    Nonempty (P ⧸ Subgroup.center P ≃* Cat ⟨.twistedE6 q, hv⟩) := by
  classical
  haveI : Finite (K2 L ℓ f) := finite_frobeniusFixedField (by omega)
  have hP' : P = subsystemGroup τ L (e6Set τ) ⊓
      twistedFixedPoints n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) := by
    rw [hP, subsystemGroup_eq_rootSpan, e6Nodes_eq_e6Set]
  obtain ⟨n₁, h, -, hh, hgen, hlang⟩ := exists_conj_twistedFixed hf hn
    (fun _ hi => rhoτ_mem hi) (fun _ hi => rhoτ_symm_mem hi) hu hact
  have hstd : StdTwist6 n₁ (rhoτ τ) := ⟨Or.inr rfl, hgen⟩
  obtain ⟨ρ₁, hρ₁s, hρ₁c⟩ := exists_surj_stdLayer hf hstd
  have hPP1 : P.map (MulAut.conj h).toMonoidHom = stdLayer τ ℓ f n₁ := by
    ext g
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [hP'] at hx
      obtain ⟨hxQ, hxR⟩ := Subgroup.mem_inf.1 hx
      have e : (MulAut.conj h).toMonoidHom x = h * x * h⁻¹ := rfl
      rw [e]
      exact mem_stdLayer.2 ⟨mul_mem (mul_mem hh hxQ) (inv_mem hh),
        (hlang x).1 (mem_twistedFixedPoints.1 hxR)⟩
    · intro hg
      obtain ⟨hgQ, hgR⟩ := mem_stdLayer.1 hg
      refine ⟨h⁻¹ * g * h, ?_, ?_⟩
      · rw [hP']
        refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem (inv_mem hh) hgQ) hh,
          mem_twistedFixedPoints.2 ((hlang _).2 ?_)⟩
        have e : h * (h⁻¹ * g * h) * h⁻¹ = g := by group
        rw [e]
        exact hgR
      · change h * (h⁻¹ * g * h) * h⁻¹ = g
        group
  set e₁ : P ≃* stdLayer τ ℓ f n₁ :=
    (P.equivMapOfInjective _ (MulAut.conj h).injective).trans (MulEquiv.subgroupCongr hPP1)
    with he₁
  set ρ : P →* graphFixedRootGroup TwistTag.E6 (K2 L ℓ f) (theta2 L ℓ f) :=
    ρ₁.comp e₁.toMonoidHom with hρdef
  have hρs : Function.Surjective ρ := hρ₁s.comp e₁.surjective
  have hkc : ∀ z ∈ ρ.ker, ∀ v : P, z * v = v * z := by
    intro z hz v
    apply e₁.injective
    rw [map_mul, map_mul]
    exact hρ₁c _ hz _
  have hZ : Subgroup.center (graphFixedRootGroup TwistTag.E6 (K2 L ℓ f) (theta2 L ℓ f)) = ⊥ :=
    center_graphFixedRootGroup_eq_bot (Finite.surjective_of_injective (theta2 L ℓ f).injective)
  have hker := ker_eq_center_of_surjective ρ hρs hkc hZ
  have e₂ : P ⧸ Subgroup.center P ≃* graphFixedRootGroup TwistTag.E6 (K2 L ℓ f) (theta2 L ℓ f) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ρ hρs)
  have hK : Nat.card (K2 L ℓ f) = q.card ^ TwistTag.E6.order := by
    rw [hq]
    exact card_K2_eq_pow_order hf
  have hσ : ∀ x, theta2 L ℓ f x = x ^ q.card := fun x => by
    rw [hq]
    exact theta2_eq_pow x
  obtain ⟨φ⟩ := Even.chevalleyBridgesAll.twistedE6 q hv (K2 L ℓ f) hK (theta2 L ℓ f) hσ
  have hperf := finite_fixed_root_group_perfect TwistTag.E6 (Fact.out : ℓ.Prime) hf (K2 L ℓ f)
    (card_K2_eq_pow_order hf) (theta2 L ℓ f) theta2_eq_pow
  obtain ⟨ψ⟩ := nonempty_derivedCentralQuotient_equiv _ _ hperf.2.2.1 hZ
  exact ⟨e₂.trans (ψ.symm.trans φ)⟩

end Layer

section W0

@[expose] def w0E6Word : List (Fin Tag.E8.rank) :=
  ([0, 1, 2, 0, 3, 1, 2, 0, 3, 2, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5, 4, 3, 1, 2, 0, 3, 2, 4, 3, 1, 5,
    4, 3, 2, 0] : List (Fin 8))

theorem w0E6_check : ∀ k : Fin Tag.E6.rank,
    w0E6Word.foldr (reflect Tag.E8) (Pi.single (e6Idx (τ := Tag.E8) (rho6 k)) 1) =
      -Pi.single (e6Idx (τ := Tag.E8) k) 1 := by
  decide +kernel

theorem wordW_smul_foldr_E8' (l : List (Fin Tag.E8.rank)) (v : Fin Tag.E8.rank → ℤ) :
    wordW Tag.E8 l • v = l.foldr (reflect Tag.E8) v := by
  induction l with
  | nil => simp [wordW]
  | cons i l ih =>
    have e : wordW Tag.E8 (i :: l) = simple Tag.E8 i * wordW Tag.E8 l := by
      simp [wordW, List.prod_cons]
    rw [e, mul_smul, ih, simple_smul, List.foldr_cons]

theorem wordW_mem_parabolicWeylGroup {τ : Tag} {J : Set (Fin τ.rank)} :
    ∀ l : List (Fin τ.rank), (∀ i ∈ l, i ∈ J) → wordW τ l ∈ parabolicWeylGroup τ J
  | [], _ => by simp [wordW, one_mem]
  | i :: l, hl => by
    have e : wordW τ (i :: l) = simple τ i * wordW τ l := by simp [wordW, List.prod_cons]
    rw [e]
    exact mul_mem (Subgroup.subset_closure ⟨i, hl i List.mem_cons_self, rfl⟩)
      (wordW_mem_parabolicWeylGroup l fun j hj => hl j (List.mem_cons_of_mem i hj))

theorem w0E6_mem : wordW Tag.E8 w0E6Word ∈ parabolicWeylGroup Tag.E8 (e6Set Tag.E8) :=
  wordW_mem_parabolicWeylGroup w0E6Word fun i hi =>
    (show ∀ i ∈ w0E6Word, i.val < Tag.E6.rank by decide) i hi

theorem act_rho_of_act_neg {L : Type} [Field L] {n : ModGL Tag.E8 L}
    (hn : n ∈ monomialSubgroup Tag.E8 L) {u : WeylGroup Tag.E8}
    (hact : ∀ α ∈ parabolicRoots Tag.E8 (e6Nodes Tag.E8),
      weylQuotientHom Tag.E8 L ⟨n, hn⟩ • α = u • ((-1 : ℤ) • α)) :
    ∀ j ∈ e6Set Tag.E8, weylQuotientHom Tag.E8 L ⟨n, hn⟩ • (Pi.single j 1 : Fin Tag.E8.rank → ℤ) =
      (u * wordW Tag.E8 w0E6Word) • (Pi.single (rhoτ Tag.E8 j) 1 : Fin Tag.E8.rank → ℤ) := by
  intro j hj
  obtain ⟨k, rfl⟩ := exists_e6Idx_eq (τ := Tag.E8) (e6Set_lt hj)
  have hmem : (Pi.single (e6Idx (τ := Tag.E8) k) 1 : Fin Tag.E8.rank → ℤ) ∈
      parabolicRoots Tag.E8 (e6Nodes Tag.E8) := by
    refine ⟨IsRoot.basis _, fun i hi => ?_⟩
    rw [e6Nodes_eq_e6Set] at hi
    have hne : i ≠ e6Idx (τ := Tag.E8) k := fun h => hi (h ▸ e6Idx_mem_e6Set k)
    exact Pi.single_eq_of_ne hne 1
  rw [hact _ hmem, mul_smul, wordW_smul_foldr_E8', rhoτ_e6Idx, w0E6_check k, neg_one_smul]

end W0

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.KSE8NegC
