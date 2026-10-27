module

public import CFSG.LieType.ChevTwo.Defs
public import CFSG.HardMathSupport.Cooperstein.StructureLie.OutTwoRank
public import CFSG.Quasithin.Vol2.GoldschmidtTDOutAbs

public section

namespace CFSG.LieType.ChevTwo

open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)
open CFSG.Quasithin.H13.Ch838 (TwoNilpotent)
open CFSG.Quasithin.H13.OutTwoNilp (outTwoNilpotent_of_twoNilpotent_outer twoNilpotent_of_comm)
open CFSG.HardMathSupport.Cooperstein.StructureLie (OutTwoRank InnAut TwoRankAt outTwoRank_iff)

@[expose] def OutOddAbelian (Y : Type) [Group Y] : Prop :=
  ∃ (C : Type) (_ : Group C) (Φ : Outer Y →* C), (∀ a b : C, a * b = b * a) ∧
    Odd (Nat.card Φ.ker) ∧ ∀ S : Subgroup C, (∀ y ∈ S, y ^ 2 = 1) → Nat.card S ≤ 4

theorem finite_mulAut_of_finite (Y : Type) [Group Y] [Finite Y] : Finite (MulAut Y) :=
  Finite.of_injective (fun α : MulAut Y => (α : Y → Y)) fun _ _ h => MulEquiv.ext (congrFun h)

theorem finite_outer_of_finite (Y : Type) [Group Y] [Finite Y] : Finite (Outer Y) :=
  haveI := finite_mulAut_of_finite Y
  Quotient.finite _

theorem card_le_two_of_isCyclic_of_sq {C : Type} [Group C] [Finite C] [IsCyclic C]
    (S : Subgroup C) (hS : ∀ y ∈ S, y ^ 2 = 1) : Nat.card S ≤ 2 := by
  classical
  have := Fintype.ofFinite C
  have hle := IsCyclic.card_pow_eq_one_le (α := C) (n := 2) two_pos
  have hS' : Nat.card S ≤ Nat.card {a : C // a ^ 2 = 1} := by
    refine Nat.card_le_card_of_injective (fun s : S => (⟨(s : C), hS s s.2⟩ : {a : C // a ^ 2 = 1}))
      ?_
    intro a b hab
    have := congrArg (fun x : {a : C // a ^ 2 = 1} => (x : C)) hab
    exact Subtype.ext (by simpa using this)
  refine hS'.trans ?_
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  exact hle

theorem card_le_four_of_prod {C₁ C₂ : Type} [Group C₁] [Group C₂] [Finite C₁] [Finite C₂]
    [IsCyclic C₁] (h2 : Nat.card C₂ ≤ 2) (S : Subgroup (C₁ × C₂)) (hS : ∀ y ∈ S, y ^ 2 = 1) :
    Nat.card S ≤ 4 := by
  set S₁ : Subgroup C₁ := S.map (MonoidHom.fst C₁ C₂) with hS₁
  have hS₁2 : ∀ y ∈ S₁, y ^ 2 = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    have := hS s hs
    simpa [Prod.ext_iff] using congrArg Prod.fst this
  have h1 : Nat.card S₁ ≤ 2 := card_le_two_of_isCyclic_of_sq S₁ hS₁2
  have hinj : Function.Injective
      (fun s : S => ((⟨(s : C₁ × C₂).1, ⟨s, s.2, rfl⟩⟩ : S₁), (s : C₁ × C₂).2)) := by
    intro a b hab
    have h1 := congrArg (fun p => (p.1 : C₁)) hab
    have h2 := congrArg Prod.snd hab
    exact Subtype.ext (Prod.ext (by simpa using h1) (by simpa using h2))
  have := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod] at this
  exact this.trans (by nlinarith)

theorem OutOddAbelian.twoNilpotent {Y : Type} [Group Y] [Finite Y] (h : OutOddAbelian Y) :
    TwoNilpotent (Outer Y) := by
  obtain ⟨C, _, Φ, hC, hodd, -⟩ := h
  have := finite_outer_of_finite Y
  refine TwoNilpotent.of_normal_odd Φ.ker hodd (fun a b => ?_)
  apply QuotientGroup.kerLift_injective Φ
  rw [map_mul, map_mul]
  exact hC _ _

theorem twoNilpotent_outer_of_commutator_mem_inner {Y : Type} [Group Y] [Finite Y]
    (h : ∀ γ α : MulAut Y, γ * α * γ⁻¹ * α⁻¹ ∈ inner Y) : TwoNilpotent (Outer Y) := by
  have := finite_outer_of_finite Y
  refine twoNilpotent_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H γ =>
    induction b using QuotientGroup.induction_on with
    | H α =>
      have h1 : (QuotientGroup.mk (γ * α * γ⁻¹ * α⁻¹) : Outer Y) = 1 :=
        (QuotientGroup.eq_one_iff _).mpr (h γ α)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
        QuotientGroup.mk_inv, QuotientGroup.mk_inv] at h1
      exact (commutatorElement_eq_one_iff_commute.mp (by
        simpa [commutatorElement_def] using h1)).eq

theorem OutOddAbelian.outTwoNilpConcl {Y : Type} [Group Y] [Finite Y] (h : OutOddAbelian Y) :
    OutTwoNilpConcl Y :=
  outTwoNilpotent_of_twoNilpotent_outer h.twoNilpotent

theorem OutOddAbelian.outTwoRank {Y : Type} [Group Y] [Finite Y] (h : OutOddAbelian Y) :
    OutTwoRank Y := by
  obtain ⟨C, _, Φ, hC, hodd, h4⟩ := h
  have hfin : Finite Φ.ker := Nat.finite_of_card_ne_zero (Nat.pos_of_ne_zero fun h0 => by
    rw [h0] at hodd; exact absurd hodd (by decide)).ne'
  refine outTwoRank_iff.mpr (TwoRankAt.of_hom (I := InnAut Y) (H := ⊤)
    (Φ.comp (QuotientGroup.mk' (inner Y))) (fun a _ b _ => ?_) (fun x hx => ?_)
    (fun x _ hx hk => ?_) (fun S _ hS => h4 S hS))
  · simp only [MonoidHom.comp_apply]
    exact hC _ _
  · have : QuotientGroup.mk' (inner Y) x = 1 := (QuotientGroup.eq_one_iff x).mpr hx
    simp only [MonoidHom.comp_apply, this, map_one]
  · obtain ⟨k, hk⟩ := hk
    have hmem : QuotientGroup.mk' (inner Y) x ∈ Φ.ker := by
      rw [MonoidHom.mem_ker]; exact hx
    set z : Φ.ker := ⟨_, hmem⟩ with hz
    have hzk : z ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      show (QuotientGroup.mk' (inner Y) x) ^ (2 ^ k) = 1
      rw [← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hk
    have h1 : orderOf z ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hzk
    have h2 : orderOf z ∣ Nat.card Φ.ker := orderOf_dvd_natCard z
    have hcop : Nat.Coprime (2 ^ k) (Nat.card Φ.ker) :=
      Nat.Coprime.pow_left k ((Nat.coprime_two_left).mpr hodd)
    have h3 : orderOf z = 1 := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    have h4 : z = 1 := orderOf_eq_one_iff.mp h3
    exact (QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h4)

theorem OutOddAbelian.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : OutOddAbelian X) : OutOddAbelian Y := by
  obtain ⟨C, _, Φ, hC, hodd, h4⟩ := h
  refine ⟨C, inferInstance, Φ.comp (equivalence e).symm.toMonoidHom, hC, ?_, h4⟩
  have hker : (Φ.comp (equivalence e).symm.toMonoidHom).ker =
      Φ.ker.map (equivalence e).toMonoidHom := by
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_map]
    constructor
    · intro hy
      exact ⟨(equivalence e).symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  rw [hker, ← Nat.card_congr (Subgroup.equivMapOfInjective Φ.ker (equivalence e).toMonoidHom
    (equivalence e).injective).toEquiv]
  exact hodd

theorem OutOddAbelian.of_isCyclic {Y : Type} [Group Y] [Finite Y] (h : IsCyclic (Outer Y)) :
    OutOddAbelian Y := by
  have := finite_outer_of_finite Y
  refine ⟨Outer Y, inferInstance, MonoidHom.id _, fun a b => (IsCyclic.commGroup).mul_comm a b,
    ?_, fun S hS => ?_⟩
  · rw [MonoidHom.ker_id, Subgroup.card_bot]; exact odd_one
  · exact (card_le_two_of_isCyclic_of_sq S hS).trans (by norm_num)

theorem OutOddAbelian.of_card_eq_two {Y : Type} [Group Y] [Finite Y]
    (h : Nat.card (Outer Y) = 2) : OutOddAbelian Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact OutOddAbelian.of_isCyclic (isCyclic_of_prime_card h)

theorem OutOddAbelian.of_ker_eq_inner {Y F : Type} [Group Y] [Finite Y] [Group F] [IsCyclic F]
    (Θ : MulAut Y →* F) (hker : Θ.ker = inner Y) : OutOddAbelian Y := by
  refine OutOddAbelian.of_isCyclic ?_
  exact isCyclic_of_injective ((QuotientGroup.kerLift Θ).comp
      (QuotientGroup.quotientMulEquivOfEq hker.symm).toMonoidHom)
    ((QuotientGroup.kerLift_injective Θ).comp
      (QuotientGroup.quotientMulEquivOfEq hker.symm).injective)

end CFSG.LieType.ChevTwo
