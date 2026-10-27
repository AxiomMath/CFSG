module

public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.TwE6FourRank
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.Gen2318

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator.ChevQ

open CFSG.Open
open scoped MatrixGroups

namespace CartanConjAux

section Sylow

variable {X : Type} [Group X]

theorem mem_smul_sylow_iff {p : ℕ} {P Q : Sylow p X} {g : X} (h : g • P = Q) (x : X) :
    x ∈ (Q : Subgroup X) ↔ ∃ s ∈ (P : Subgroup X), g * s * g⁻¹ = x := by
  subst h
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, hs, by simpa [MulAut.conj_apply] using hsx⟩
  · rintro ⟨s, hs, hsx⟩
    exact ⟨s, hs, by simpa [MulAut.conj_apply] using hsx⟩

theorem isElemAbelian_map {Y : Type} [Group Y] {p : ℕ} {E : Subgroup X} (f : X →* Y)
    (hE : IsElemAbelian p E) : IsElemAbelian p (E.map f) := by
  refine ⟨?_, ?_⟩
  · haveI := hE.1
    infer_instance
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

theorem conj_eq_of_sylow_unique {p n : ℕ} [Fact p.Prime] [Finite X] (N : Subgroup X) [N.Normal]
    (huniq : ∀ P : Sylow p X, ∀ E' F' : Subgroup X, E' ≤ (P : Subgroup X) → F' ≤ (P : Subgroup X) →
      IsElemAbelian p E' → IsElemAbelian p F' → Nat.card E' = p ^ n → Nat.card F' = p ^ n →
      E' ≤ N → F' ≤ N → E' = F')
    {E F : Subgroup X} (hE : IsElemAbelian p E) (hF : IsElemAbelian p F)
    (hEc : Nat.card E = p ^ n) (hFc : Nat.card F = p ^ n) (hEN : E ≤ N) (hFN : F ≤ N) :
    ∃ g : X, F = E.map (MulAut.conj g).toMonoidHom := by
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card hEc)
  obtain ⟨Q, hFQ⟩ := IsPGroup.exists_le_sylow (IsPGroup.of_card hFc)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P Q
  have hinj : Function.Injective (MulAut.conj g⁻¹).toMonoidHom := (MulAut.conj g⁻¹).injective
  have hE'P : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ (P : Subgroup X) := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    obtain ⟨s, hs, hsx⟩ := (mem_smul_sylow_iff hg x).1 (hFQ hx)
    have hconj : (MulAut.conj g⁻¹).toMonoidHom x = s := by
      rw [← hsx]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [hconj]
    exact hs
  have hE'N : F.map (MulAut.conj g⁻¹).toMonoidHom ≤ N := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    have hc := (inferInstance : N.Normal).conj_mem x (hFN hx) g⁻¹
    simpa [MulAut.conj_apply] using hc
  have hE'c : Nat.card (F.map (MulAut.conj g⁻¹).toMonoidHom) = p ^ n := by
    rw [Subgroup.card_map_of_injective hinj]
    exact hFc
  have hEE' : E = F.map (MulAut.conj g⁻¹).toMonoidHom :=
    huniq P E _ hEP hE'P hE (isElemAbelian_map _ hF) hEc hE'c hEN hE'N
  refine ⟨g, ?_⟩
  ext x
  constructor
  · intro hx
    refine Subgroup.mem_map.2 ⟨g⁻¹ * x * g⁻¹⁻¹, ?_, ?_⟩
    · rw [hEE']
      exact Subgroup.mem_map.2 ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · simp [MulAut.conj_apply, mul_assoc]
  · intro hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    rw [hEE'] at hy
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hy
    have key : (MulAut.conj g).toMonoidHom ((MulAut.conj g⁻¹).toMonoidHom z) = z := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rw [← hzy, key]
    exact hz

end Sylow

theorem finite_mulAut (S : Type) [Group S] [Finite S] : Finite (MulAut S) :=
  inferInstanceAs (Finite (S ≃* S))

theorem inn_normal (S : Type) [Group S] : ((MulAut.conj : S →* MulAut S).range).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hn
  refine MonoidHom.mem_range.2 ⟨g a, ?_⟩
  ext x
  simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply, mul_assoc]

theorem cartan_of_four_sl2 {F : Type} [Field F] [Finite F] {S : Type} [Group S] (h4 : Nat.card F = 4)
    (ψ : Fin 4 → SL(2, F) →* S) (hψ : ∀ i, Function.Injective (ψ i))
    (hc : ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)) :
    ∃ A : Subgroup (MulAut S), IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧
      A ≤ (MulAut.conj : S →* MulAut S).range ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ A, ∀ u ∈ U, φ u ∈ U := by
  obtain ⟨w, hw0, hw⟩ := TwE6FourRankAux.exists_sq_add_add_one h4
  obtain ⟨A, U, hA, hAcard, hU0, hU2, hAN, hcen⟩ :=
    TwE6FourRankAux.partI_of_four (TwE6FourRankAux.two_eq_zero_of_natCard h4) hw0 hw ψ hψ hc
  haveI : IsMulCommutative A := hA.1
  let κ : A →* MulAut S := (MulAut.conj : S →* MulAut S).comp A.subtype
  have hκinj : Function.Injective κ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    apply Subtype.ext
    apply hcen (a : S) a.2
    intro x
    have hx := congrArg (fun φ : MulAut S => φ x) ha
    simp only [κ, MonoidHom.comp_apply, MulAut.conj_apply, MulAut.one_apply] at hx
    exact (mul_inv_eq_iff_eq_mul).1 hx
  have hκcard : Nat.card κ.range = 3 ^ 4 := by
    rw [← hAcard]
    exact (Nat.card_congr (MonoidHom.ofInjective hκinj).toEquiv).symm
  have hκel : IsElemAbelian 3 κ.range := by
    refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 x.2
      obtain ⟨b, hb⟩ := MonoidHom.mem_range.1 y.2
      apply Subtype.ext
      show (x : MulAut S) * (y : MulAut S) = (y : MulAut S) * (x : MulAut S)
      rw [← ha, ← hb]
      change κ a * κ b = κ b * κ a
      rw [← map_mul, ← map_mul, IsMulCommutative.is_comm.comm a b]
    · obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 hx
      have h3 : a ^ 3 = 1 := Subtype.ext (by simpa using hA.2 (a : S) a.2)
      rw [← ha, ← map_pow, h3, map_one]
  refine ⟨κ.range, hκel, hκcard, ?_, U, hU0, hU2, ?_⟩
  · rintro x ⟨a, rfl⟩
    exact ⟨(a : S), rfl⟩
  · rintro φ hφ u hu
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.1 hφ
    show MulAut.conj (a : S) u ∈ U
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hAN a.2) u).1 hu

end CartanConjAux

@[expose] def TwE6FourSylowRankUnique : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsTwistedE6FourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ (P : Sylow 3 (MulAut S)) (E F : Subgroup (MulAut S)),
      E ≤ (P : Subgroup (MulAut S)) → F ≤ (P : Subgroup (MulAut S)) →
      IsElemAbelian 3 E → IsElemAbelian 3 F → Nat.card E = 3 ^ 4 → Nat.card F = 3 ^ 4 →
      E ≤ (MulAut.conj : S →* MulAut S).range → F ≤ (MulAut.conj : S →* MulAut S).range → E = F

@[expose] def Gen2318RankFourSylowUniq : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsRankFourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∀ (P : Sylow 3 (MulAut S)) (E F : Subgroup (MulAut S)),
      E ≤ (P : Subgroup (MulAut S)) → F ≤ (P : Subgroup (MulAut S)) →
      IsElemAbelian 3 E → IsElemAbelian 3 F → Nat.card E = 3 ^ 4 → Nat.card F = 3 ^ 4 →
      E ≤ (MulAut.conj : S →* MulAut S).range → F ≤ (MulAut.conj : S →* MulAut S).range → E = F

@[expose] def Gen2318RankFourCartan : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex), IsRankFourIndex d.1 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
    ∃ A : Subgroup (MulAut S), IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧
      A ≤ (MulAut.conj : S →* MulAut S).range ∧
      ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ A, ∀ u ∈ U, φ u ∈ U

@[expose] def F4FourSL2 : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    d.1 = TauCeti.LieTypeIndex.F4 q → IsTwoPow q 2 →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 4 ∧
        ∃ ψ : Fin 4 → SL(2, F) →* S, (∀ i, Function.Injective (ψ i)) ∧
          ∀ i j, i ≠ j → ∀ A B, Commute (ψ i A) (ψ j B)

@[expose] def E6CartanRankFour : Prop :=
  ∀ (S : Type) [Group S] [Finite S] (d : TauCeti.ValidLieTypeIndex) (q : TauCeti.PrimePower),
    d.1 = TauCeti.LieTypeIndex.E6 q → (IsTwoPow q 1 ∨ IsTwoPow q 3) →
    Nonempty (S ≃* (TauCeti.CFSGIndex.lie d).Group) →
      ∃ A : Subgroup (MulAut S), IsElemAbelian 3 A ∧ Nat.card A = 3 ^ 4 ∧
        A ≤ (MulAut.conj : S →* MulAut S).range ∧
        ∃ U : Subgroup S, U ≠ ⊥ ∧ IsPGroup 2 ↥U ∧ ∀ φ ∈ A, ∀ u ∈ U, φ u ∈ U

theorem twE6FourRankInnerConj_of_sylow (h : TwE6FourSylowRankUnique) : TwE6FourRankInnerConj := by
  intro S _ _ d hd hiso E F hEi hFi hEc hFc hEn hFn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut S) := CartanConjAux.finite_mulAut S
  haveI := CartanConjAux.inn_normal S
  exact CartanConjAux.conj_eq_of_sylow_unique (p := 3) (n := 4)
    (N := (MulAut.conj : S →* MulAut S).range)
    (fun P E' F' hE' hF' hEi' hFi' hEc' hFc' hEn' hFn' =>
      h S d hd hiso P E' F' hE' hF' hEi' hFi' hEc' hFc' hEn' hFn')
    hEi hFi hEc hFc hEn hFn

section Final

theorem twE6FourRank_of_sylow (h : TwE6FourSylowRankUnique) : TwE6FourRank :=
  twE6FourRank_of_inner_conj (twE6FourRankInnerConj_of_sylow h)

end Final

theorem gen2318RankFour_of_sylow (hU : Gen2318RankFourSylowUniq) (hC : Gen2318RankFourCartan) :
    Gen2318RankFour := by
  intro S _ _ d hd hiso E hEi hEc hEn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite (MulAut S) := CartanConjAux.finite_mulAut S
  haveI := CartanConjAux.inn_normal S
  obtain ⟨A, hAi, hAc, hAn, U, hU0, hU2, hUn⟩ := hC S d hd hiso
  obtain ⟨g, hg⟩ := CartanConjAux.conj_eq_of_sylow_unique (p := 3) (n := 4)
    (N := (MulAut.conj : S →* MulAut S).range)
    (fun P E' F' hE' hF' hEi' hFi' hEc' hFc' hEn' hFn' =>
      hU S d hd hiso P E' F' hE' hF' hEi' hFi' hEc' hFc' hEn' hFn')
    hAi hEi hAc hEc hAn hEn
  refine ⟨U.map g.toMonoidHom, ?_, hU2.map _, ?_⟩
  · intro hbot
    apply hU0
    rw [eq_bot_iff]
    intro u hu
    have hmem : g.toMonoidHom u ∈ U.map g.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    rw [Subgroup.mem_bot]
    exact g.injective (hmem.trans (map_one g.toMonoidHom).symm)
  · intro φ hφ y hy
    rw [hg] at hφ
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hφ
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    exact Subgroup.mem_map.2 ⟨a u, hUn a ha u hu, by
      simp [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply_self]⟩

theorem gen2318RankFourCartan_of_parts (hF4 : F4FourSL2) (hE6 : E6CartanRankFour) :
    Gen2318RankFourCartan := by
  intro S _ _ d hd hiso
  obtain ⟨d, hv⟩ := d
  cases d with
  | F4 q =>
    obtain ⟨F, hF, hFfin, h4, ψ, hψ, hc⟩ := hF4 S ⟨.F4 q, hv⟩ q rfl hd hiso
    exact CartanConjAux.cartan_of_four_sl2 h4 ψ hψ hc
  | E6 q => exact hE6 S ⟨.E6 q, hv⟩ q rfl hd hiso
  | _ => exact absurd hd (by simp [IsRankFourIndex])

theorem gen2318RankFour_of_parts (hU : Gen2318RankFourSylowUniq) (hF4 : F4FourSL2)
    (hE6 : E6CartanRankFour) : Gen2318RankFour :=
  gen2318RankFour_of_sylow hU (gen2318RankFourCartan_of_parts hF4 hE6)

end CFSG.HardMathSupport.Solomon.Coordinator.ChevQ
