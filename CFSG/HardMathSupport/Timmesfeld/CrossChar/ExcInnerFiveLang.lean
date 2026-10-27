module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFive

public section

namespace CFSG.HardMathSupport.Timmesfeld.CrossChar

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.SeitzGeneration
  CFSG.RankThree.PartOne.KE CFSG.RankThree.Classical2 Polynomial
open scoped Matrix

theorem localDeltaIn_eq_bot_of_conj_sub {C : Type*} [Group C] {p : ℕ}
    {H : Subgroup (MulAut C)} (hH : innerAut C ≤ H) {D : Subgroup (MulAut C)} {E : Subgroup C}
    (hED : E.map (MulAut.conj : C →* MulAut C) ≤ D) (c₀ : C)
    (h : localDeltaIn p H ((E.map (MulAut.conj c₀).toMonoidHom).map
      (MulAut.conj : C →* MulAut C)) = ⊥) :
    localDeltaIn p H D = ⊥ := by
  refine le_bot_iff.1 ((localDeltaIn_antitone H hED).trans (le_of_eq ?_))
  refine localDeltaIn_eq_bot_of_map_conj (c := MulAut.conj c₀) (hH ⟨c₀, rfl⟩) ?_
  have hmap : (E.map (MulAut.conj : C →* MulAut C)).map
      (MulAut.conj (MulAut.conj c₀)).toMonoidHom =
      (E.map (MulAut.conj c₀).toMonoidHom).map (MulAut.conj : C →* MulAut C) := by
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
    ext x y
    simp [MulAut.conj_apply]
  rw [hmap]
  exact h

section Lang


theorem exists_large_conj_into_langTorus {τ : Tag} {C : Type} [Group C] [Finite C] {L : Type}
    [Field L] (ι : C →* ModGL τ L) (hι : Function.Injective ι) (Φ : ModGL τ L →* ModGL τ L)
    (n g0 : ModGL τ L) (hg0C : g0 ∈ adjointGroup τ L) (hg0 : Φ g0 = g0 * n) {p : ℕ}
    (hp : p.Prime) [Finite (twistedTorusOf n Φ)]
    (hrat : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Φ x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X → IsPGroup p P → P ≤ ι.range)
    (hord : (Nat.card C).factorization p ≤ (Nat.card (twistedTorusOf n Φ)).factorization p + 1)
    {A : Subgroup C} (hA : IsPGroup p A) :
    ∃ c : C, ∃ E ≤ A, Nat.card A ≤ p * Nat.card E ∧
      ∀ x ∈ E, ι (c * x * c⁻¹) ∈ (twistedTorusOf n Φ).map (MulAut.conj g0).toMonoidHom := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set X : Subgroup (ModGL τ L) := (twistedTorusOf n Φ).map (MulAut.conj g0).toMonoidHom with hX
  have hXfin : Finite X :=
    Finite.of_surjective ((MulAut.conj g0).toMonoidHom.subgroupMap (twistedTorusOf n Φ))
      ((MulAut.conj g0).toMonoidHom.subgroupMap_surjective (twistedTorusOf n Φ))
  have hT0C := twistedTorusOf_le_adjointGroup n Φ
  have hXC : X ≤ adjointGroup τ L := by
    rintro _ ⟨x, hx, rfl⟩
    exact mul_mem (mul_mem hg0C (hT0C hx)) (inv_mem hg0C)
  have hXF : ∀ x ∈ X, Φ x = x := by
    rintro _ ⟨x, hx, rfl⟩
    have hxfix := (mem_twistedTorusOf.1 hx).2
    change Φ (g0 * x * g0⁻¹) = g0 * x * g0⁻¹
    rw [map_mul, map_mul, map_inv, hg0]
    calc g0 * n * Φ x * (g0 * n)⁻¹ = g0 * (n * Φ x * n⁻¹) * g0⁻¹ := by group
      _ = g0 * x * g0⁻¹ := by rw [hxfix]
  have hpg := hrat X hXC hXF
  set T : Subgroup C := X.comap ι with hT
  have hXcard : Nat.card X = Nat.card (twistedTorusOf n Φ) :=
    Subgroup.card_map_of_injective (MulAut.conj g0).injective
  have hXT : (Nat.card (twistedTorusOf n Φ)).factorization p ≤ (Nat.card T).factorization p := by
    obtain ⟨P0⟩ : Nonempty (Sylow p X) := inferInstance
    set P1 : Subgroup (ModGL τ L) := (P0 : Subgroup X).map X.subtype with hP1
    have hP1X : P1 ≤ X := Subgroup.map_subtype_le _
    have hP1p : IsPGroup p P1 := P0.isPGroup'.map _
    have hP1range : P1 ≤ ι.range := hpg P1 hP1X hP1p
    have hcard1 : Nat.card (P1.comap ι) = p ^ (Nat.card X).factorization p := by
      have hmap : (P1.comap ι).map ι = P1 := by
        rw [Subgroup.map_comap_eq, inf_eq_right.2 hP1range]
      rw [← Subgroup.card_map_of_injective hι, hmap, hP1,
        Subgroup.card_map_of_injective X.subtype_injective, Sylow.card_eq_multiplicity]
    have hdvd : p ^ (Nat.card X).factorization p ∣ Nat.card T :=
      hcard1 ▸ Subgroup.card_dvd_of_le (Subgroup.comap_mono hP1X)
    rw [← hXcard]
    exact (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').1 hdvd
  have hord' : (Nat.card (⊤ : Subgroup C)).factorization p ≤ (Nat.card T).factorization p + 1 := by
    rw [Subgroup.card_top]
    omega
  obtain ⟨g, -, E, hEA, hEcard, hEH⟩ :=
    exists_large_conj_le_of_sylow (le_top : T ≤ ⊤) (le_top : A ≤ ⊤) hA hord'
  exact ⟨g, E, hEA, hEcard, fun x hx => hEH x hx⟩

end Lang

section Frames


theorem exists_langFrame_untwisted {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (w : WeylGroup τ)
    (hw : ∀ u, w • u = M *ᵥ u) {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1)
    (hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0)
    (hord : (Nat.card (adjointGroup τ K)).factorization p ≤
      ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p + 1) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) ∧
      ∃ g0 ∈ adjointGroup τ (AlgebraicClosure K),
        Units.map (entrywiseHom Fr) g0 =
          g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w ∧
        ∀ A : Subgroup (adjointGroup τ K), IsPGroup p A → ∃ c : adjointGroup τ K, ∃ E ≤ A,
          Nat.card A ≤ p * Nat.card E ∧ ∀ x ∈ E,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : adjointGroup τ K) : ModGL τ K) ∈
              (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
                (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL τ K) := finite_modGL
  obtain ⟨f, hℓ, hf⟩ := FiniteField.card K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  have hq : Nat.card K = ringChar K ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hf
  have : CharP K (ringChar K) := ringChar.charP K
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L (ringChar K) (f : ℕ)
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hq]
    exact iterateFrobenius_def (ringChar K) (f : ℕ) c
  have hℓq : ringChar K ∣ Nat.card K := by
    rw [hq]
    exact dvd_pow_self _ f.ne_zero
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator τ K (ℓ := ringChar K) (f := (f : ℕ)) f.pos L w
  let ι : adjointGroup τ K →* ModGL τ L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype
  have hrange : ι.range = (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup τ K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hT0 : twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr =
      (fixedCharTuples M Fr).map (rootDiagUnitHom τ L) := by
    ext x
    constructor
    · intro hx
      obtain ⟨a, rfl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorus.1 hx).1
      refine ⟨a, ?_, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr]
      exact mem_twistedFixedTuples_iff_conj.2 (mem_twistedTorus.1 hx).2
    · rintro ⟨a, ha, rfl⟩
      rw [← twistedFixedTuples_eq_fixedCharTuples hw Fr] at ha
      exact mem_twistedTorus.2 ⟨rootDiagUnit_mem_torusGroup a,
        mem_twistedFixedTuples_iff_conj.1 ha⟩
  set B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ :=
    M - (Nat.card K : ℤ) • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval (Nat.card K : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ hℓq M hn0 hpow
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) = (M.charpoly.eval (Nat.card K : ℤ)).natAbs := by
    show Nat.card (twistedTorus (canonicalRep (coxeterSystem τ) L w) Fr) = _
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have : Finite (twistedTorusOf (canonicalRep (coxeterSystem τ) L w)
      (Units.map (entrywiseHom Fr))) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.2 hev)
  have hrat' : ∀ (X : Subgroup (ModGL τ L)) [Finite X], X ≤ adjointGroup τ L →
      (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) → ∀ P : Subgroup (ModGL τ L), P ≤ X →
        IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hPp
    rw [hrange]
    exact (finite_fixed_subgroup_rational d hτ Fr hFr X hXC hXF).2 p hp hp3 P hPX hPp
  refine ⟨Fr, hFr, g0, hg0C, hg0, fun A hA => ?_⟩
  rw [← hcard] at hord
  exact exists_large_conj_into_langTorus ι hι (Units.map (entrywiseHom Fr)) _ g0 hg0C hg0 hp
    hrat' hord hA

theorem exists_langFrame_twistedE6 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) (K : Type) [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ}
    (hp : p.Prime) (hp3 : 3 < p)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    (v : WeylGroup TwistTag.E6.tag) (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1) (hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0)
    (hord : (Nat.card (twistedE6RootGroup K σ)).factorization p ≤
      ((M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization p + 1) :
    ∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) ∧
      ∃ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
        twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
          g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v ∧
        ∀ A : Subgroup (twistedE6RootGroup K σ), IsPGroup p A →
          ∃ c : twistedE6RootGroup K σ, ∃ E ≤ A, Nat.card A ≤ p * Nat.card E ∧ ∀ x ∈ E,
            baseChangeGL (algebraMap K (AlgebraicClosure K))
              ((c * x * c⁻¹ : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) ∈
              (twistedTorusOf
                (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
                (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map
                  (MulAut.conj g0).toMonoidHom := by
  classical
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Fact p.Prime := ⟨hp⟩
  have hK0 : Nat.card K ≠ 0 := by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero)
  have : Finite K := Nat.finite_of_card_ne_zero hK0
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  let L := AlgebraicClosure K
  have : CharP L ℓ := charP_of_injective_algebraMap (algebraMap K L).injective ℓ
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  let Fr : L →+* L := iterateFrobenius L ℓ f
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_twisted K (ℓ := ℓ) (f := f) hf L v
  obtain ⟨-, -, hder, ⟨k, hk⟩, -, -, -⟩ :=
    twisted_E6_full_rational_fixed_group_order hℓ hf K hK σ.toRingHom hσ L Fr hFr
  set R' := twistedFixedGroup TwistTag.E6 L Fr with hR'
  set C' := (graphFixedRootGroup TwistTag.E6 K σ.toRingHom).map
    (baseChangeGL (algebraMap K L)) with hC'
  have hle : C' ≤ R' := by
    rw [← hder]
    refine Subgroup.commutator_le.2 fun a ha b hb => ?_
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  have hnormal : (C'.subgroupOf R').Normal := by
    have e : C'.subgroupOf R' = ⁅(⊤ : Subgroup R'), ⊤⁆ := by
      have h1 : ⁅R', R'⁆ = Subgroup.map R'.subtype ⁅(⊤ : Subgroup R'), ⊤⁆ := by
        rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map R'.subtype, Subgroup.range_subtype]
      rw [← hder, h1]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _) _
    rw [e]
    infer_instance
  let ι : twistedE6RootGroup K σ →* ModGL TwistTag.E6.tag L :=
    (baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype
  have hrange : ι.range = C' := by
    change ((baseChangeGL (algebraMap K L)).comp (twistedE6RootGroup K σ).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hι : Function.Injective ι :=
    (baseChangeGL_injective _).comp (Subgroup.subtype_injective _)
  have hrat : ∀ (X : Subgroup (ModGL TwistTag.E6.tag L)) [Finite X],
      X ≤ adjointGroup TwistTag.E6.tag L → (∀ x ∈ X, twistHom TwistTag.E6 L Fr x = x) →
      ∀ P : Subgroup (ModGL TwistTag.E6.tag L), P ≤ X → IsPGroup p P → P ≤ ι.range := by
    intro X _ hXC hXF P hPX hP
    have hXR : X ≤ R' := fun x hx =>
      (mem_twistedFixedGroup_iff_twistHom _ _ _).2 ⟨hXC hx, hXF x hx⟩
    rw [hrange]
    have : Finite P :=
      Finite.of_injective (Subgroup.inclusion hPX) (Subgroup.inclusion_injective hPX)
    exact le_of_isPGroup_of_index_eq_pow (hPX.trans hXR) hp Nat.prime_three (by omega) hk hP
  have hT0 := twistedTorus_E6_eq_map (L := L) Fr v M hv
  set B : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ :=
    M - ((ℓ ^ f : ℕ) : ℤ) • (1 : Matrix _ _ ℤ) with hB
  have hdetB : B.det.natAbs = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs :=
    (natAbs_eval_charpoly M _).symm
  have hBne : B.det ≠ 0 := fun h => hev (Int.natAbs_eq_zero.1 (hdetB ▸ by rw [h]; rfl))
  have hcop := not_dvd_natAbs_det_sub hℓ (dvd_pow_self ℓ (by omega) : ℓ ∣ ℓ ^ f) M hn0 hpow
  have hcard : Nat.card (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) = (M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs := by
    rw [hT0, Subgroup.card_map_of_injective rootDiagUnit_injective,
      natCard_fixedCharTuples M Fr hFr hBne hcop, hdetB]
  have : Finite (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
      (twistHom TwistTag.E6 L Fr)) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact Int.natAbs_ne_zero.2 hev)
  refine ⟨Fr, hFr, g0, hg0C, hg0, fun A hA => ?_⟩
  rw [← hcard] at hord
  exact exists_large_conj_into_langTorus ι hι (twistHom TwistTag.E6 L Fr) _ g0 hg0C hg0 hp hrat
    hord hA

end Frames

section Residual


@[expose] def LangTorusPlaneBalance (τ : Tag) (w : WeylGroup τ) (p : ℕ) (Q : ℕ → Prop) : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Q (Nat.card K) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
    ∀ g0 ∈ adjointGroup τ (AlgebraicClosure K),
      Units.map (entrywiseHom Fr) g0 =
        g0 * canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w →
    ∀ D₀ : Subgroup (adjointGroup τ K), (∀ x ∈ D₀, x ^ p = 1) → p < Nat.card D₀ →
      (∀ x ∈ D₀, baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
          (Units.map (entrywiseHom Fr))).map (MulAut.conj g0).toMonoidHom) →
    ∀ H : Subgroup (MulAut (adjointGroup τ K)), innerAut (adjointGroup τ K) ≤ H →
      localDeltaIn p H
        (D₀.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))) = ⊥

@[expose] def TwistedE6LangTorusPlaneBalance (v : WeylGroup TwistTag.E6.tag) (p : ℕ)
    (Q : ℕ → Prop) : Prop :=
  ∀ ℓ f : ℕ, ℓ.Prime → 1 ≤ f → Q (ℓ ^ f) → ∀ (K : Type) [Field K], Nat.card K = (ℓ ^ f) ^ 2 →
    ∀ σ : K ≃+* K, (∀ c, σ c = c ^ (ℓ ^ f)) →
    ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ (ℓ ^ f)) →
    ∀ g0 ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K),
      twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 =
        g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v →
    ∀ D₀ : Subgroup (twistedE6RootGroup K σ), (∀ x ∈ D₀, x ^ p = 1) → p < Nat.card D₀ →
      (∀ x ∈ D₀, baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) ∈
        (twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) v)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)).map (MulAut.conj g0).toMonoidHom) →
    ∀ H : Subgroup (MulAut (twistedE6RootGroup K σ)), innerAut (twistedE6RootGroup K σ) ≤ H →
      localDeltaIn p H
        (D₀.map (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ))) = ⊥

end Residual

theorem lt_card_of_cube_le {p : ℕ} (hp : p.Prime) {a b : ℕ} (ha : a = p ^ 3) (h : a ≤ p * b) :
    p < b := by
  subst ha
  have h1 : p ^ 2 ≤ b := by
    have h3 : p * p ^ 2 ≤ p * b := by
      rw [← pow_succ']
      exact h
    exact Nat.le_of_mul_le_mul_left h3 hp.pos
  have h2 : p < p ^ 2 := by
    have := hp.two_le
    nlinarith
  omega

theorem isInnerLocallyBalanced_of_large_conj {C : Type*} [Group C] {p : ℕ} (hp : p.Prime)
    (hinj : Function.Injective (MulAut.conj : C →* MulAut C)) (P : C → Prop)
    (hconj : ∀ A : Subgroup C, IsPGroup p A → ∃ c : C, ∃ E ≤ A, Nat.card A ≤ p * Nat.card E ∧
      ∀ x ∈ E, P (c * x * c⁻¹))
    (hres : ∀ D₁ : Subgroup C, (∀ x ∈ D₁, x ^ p = 1) → p < Nat.card D₁ → (∀ x ∈ D₁, P x) →
      ∀ H : Subgroup (MulAut C), innerAut C ≤ H →
        localDeltaIn p H (D₁.map (MulAut.conj : C →* MulAut C)) = ⊥) :
    IsInnerLocallyBalanced p C := by
  intro D hD hcard hDin H hH _
  set D₀ := D.comap (MulAut.conj : C →* MulAut C) with hD₀
  have hDD : D₀.map MulAut.conj = D := Subgroup.map_comap_eq_self hDin
  have hD₀card : Nat.card D₀ = p ^ 3 := by
    rw [← hcard, ← hDD, Subgroup.card_map_of_injective hinj]
  have hpow₀ : ∀ x ∈ D₀, x ^ p = 1 := fun x hx => by
    have hx' : (MulAut.conj x) ^ p = 1 := hD.2 _ hx
    exact hinj (by rw [map_pow, hx', map_one])
  have hA : IsPGroup p D₀ := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, hpow₀ x x.2, Subgroup.coe_one])⟩
  obtain ⟨c, E, hED₀, hEcard, hEP⟩ := hconj D₀ hA
  refine localDeltaIn_eq_bot_of_conj_sub hH (E := E) ?_ c ?_
  · rw [← hDD]
    exact Subgroup.map_mono hED₀
  · refine hres _ ?_ ?_ ?_ H hH
    · rintro _ ⟨x, hx, rfl⟩
      change (c * x * c⁻¹) ^ p = 1
      rw [conj_pow, hpow₀ x (hED₀ hx), mul_one, mul_inv_cancel]
    · rw [Subgroup.card_map_of_injective (MulAut.conj c).injective]
      exact lt_card_of_cube_le hp hD₀card hEcard
    · rintro _ ⟨x, hx, rfl⟩
      exact hEP x hx

section Reduction

theorem isInnerLocallyBalanced_adjoint_of_langTorus {τ : Tag} (d : ℕ)
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1))
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {w : WeylGroup τ} (hw : ∀ u, w • u = M *ᵥ u)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {Q : ℕ → Prop} (hres : LangTorusPlaneBalance τ w p Q) (K : Type) [Field K] [Finite K]
    (hQ : Q (Nat.card K)) (hev : M.charpoly.eval (Nat.card K : ℤ) ≠ 0)
    (hord : (Nat.card (adjointGroup τ K)).factorization p ≤
      ((M.charpoly.eval (Nat.card K : ℤ)).natAbs).factorization p + 1) :
    IsInnerLocallyBalanced p (adjointGroup τ K) := by
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
    exists_langFrame_untwisted d hτ K hp hp3 w hw hn0 hpow hev hord
  exact isInnerLocallyBalanced_of_large_conj hp
    (mulAut_conj_injective_adjointGroup (τ := τ) (K := K)) _ hconj
    fun D₁ hpow₁ hcard₁ hP₁ H hH => hres K hQ Fr hFr g0 hg0C hg0 D₁ hpow₁ hcard₁ hP₁ H hH

theorem isInnerLocallyBalanced_twistedE6_of_langTorus {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    {M : Matrix (Fin TwistTag.E6.tag.rank) (Fin TwistTag.E6.tag.rank) ℤ}
    {v : WeylGroup TwistTag.E6.tag} (hv : ∀ x, v • x = M *ᵥ permLattice TwistTag.E6.perm x)
    {n : ℕ} (hn0 : n ≠ 0) (hpow : M ^ n = 1) {Q : ℕ → Prop}
    (hres : TwistedE6LangTorusPlaneBalance v p Q) (hQ : Q (ℓ ^ f))
    (hev : M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ) ≠ 0)
    (hord : (Nat.card (twistedE6RootGroup K σ)).factorization p ≤
      ((M.charpoly.eval ((ℓ ^ f : ℕ) : ℤ)).natAbs).factorization p + 1) :
    IsInnerLocallyBalanced p (twistedE6RootGroup K σ) := by
  obtain ⟨Fr, hFr, g0, hg0C, hg0, hconj⟩ :=
    exists_langFrame_twistedE6 hℓ hf K hK σ hσ hp hp3 v hv hn0 hpow hev hord
  exact isInnerLocallyBalanced_of_large_conj hp
    (CFSG.LieType.Chevalley.mulAut_conj_injective_of_center_eq_bot
      (CFSG.LieType.Chevalley.center_graphFixedRootGroup_eq_bot σ.surjective)) _ hconj
    fun D₁ hpow₁ hcard₁ hP₁ H hH =>
      hres ℓ f hℓ hf hQ K hK σ hσ Fr hFr g0 hg0C hg0 D₁ hpow₁ hcard₁ hP₁ H hH

end Reduction

end CFSG.HardMathSupport.Timmesfeld.CrossChar
