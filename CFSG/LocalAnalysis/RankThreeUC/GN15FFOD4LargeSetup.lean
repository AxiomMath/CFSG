module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesFields
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerActorBinary
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1Basic
public import CFSG.Quasithin.Background.SmithCurtisBasic
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.OffenderUnits
import CFSG.RankThree.PartOne.S11d.OrthRankBase
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.BinRep
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesCollapse

set_option linter.unusedSectionVars false

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open CFSG.Quasithin CFSG.Quasithin.SmithCurtis CFSG.QuasithinUnique.Setup
open CFSG.QuasithinUnique.Setup.SL2Modules
open CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc

private theorem repOfSubgroup_map_isIrreducible_aux
    {V : Type} [CommGroup V] {V' : Type} [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    (θ : V ≃* Multiplicative V') {L : Subgroup (MulAut V)} (hirr : X1.IsIrrOn L)
    (Ψ : MulAut V ≃* (Module.End (ZMod 2) V')ˣ)
    (hΨact : ∀ (g : MulAut V) (v : V), (Ψ g).val (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ (g v))) :
    (repOfSubgroup (L.map Ψ.toMonoidHom)).IsIrreducible := by
  have hVnt : Nontrivial V := hirr.1
  rw [isIrreducible_iff]
  have hV'nt : Nontrivial V' := by
    obtain ⟨x, hx⟩ := exists_ne (1 : V)
    exact ⟨⟨Multiplicative.toAdd (θ x), 0, fun h => hx (θ.injective (by simpa using h))⟩⟩
  refine ⟨hV'nt, fun U hU => ?_⟩
  set U₀ : Subgroup V :=
    { carrier := {x | Multiplicative.toAdd (θ x) ∈ U}
      one_mem' := by simp
      mul_mem' := fun {x y} hx hy => by
        have : Multiplicative.toAdd (θ (x * y)) =
            Multiplicative.toAdd (θ x) + Multiplicative.toAdd (θ y) := by simp
        show Multiplicative.toAdd (θ (x * y)) ∈ U
        rw [this]; exact U.add_mem hx hy
      inv_mem' := fun {x} hx => by
        have : Multiplicative.toAdd (θ x⁻¹) = - Multiplicative.toAdd (θ x) := by simp
        show Multiplicative.toAdd (θ x⁻¹) ∈ U
        rw [this]; exact U.neg_mem hx } with hU₀
  have hU₀inv : ∀ g ∈ L, ∀ u ∈ U₀, g u ∈ U₀ := by
    intro g hg u hu
    have h1 := hU ⟨Ψ g, g, hg, rfl⟩ (Multiplicative.toAdd (θ u)) hu
    show Multiplicative.toAdd (θ (g u)) ∈ U
    have e : (Ψ g).val (Multiplicative.toAdd (θ u)) = Multiplicative.toAdd (θ (g u)) :=
      hΨact g u
    rw [repOfSubgroup_apply] at h1
    rwa [show ((⟨Ψ g, g, hg, rfl⟩ : ↥(L.map Ψ.toMonoidHom)) : (Module.End (ZMod 2) V')ˣ).val
        (Multiplicative.toAdd (θ u)) = _ from e] at h1
  rcases hirr.2 U₀ hU₀inv with h0 | h0
  · left
    rw [eq_bot_iff]
    intro w hw
    have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by
      show Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U
      simpa using hw
    rw [h0, Subgroup.mem_bot] at hx
    rw [Submodule.mem_bot]
    have := congrArg (fun x => Multiplicative.toAdd (θ x)) hx
    simpa using this
  · right
    rw [eq_top_iff]
    intro w _
    have hx : θ.symm (Multiplicative.ofAdd w) ∈ U₀ := by rw [h0]; exact Subgroup.mem_top _
    have hx' : Multiplicative.toAdd (θ (θ.symm (Multiplicative.ofAdd w))) ∈ U := hx
    simpa using hx'

private theorem exists_equivariant_embedding_aux
    {V : Type} [CommGroup V] [Finite V]
    {V' : Type} [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    (θ : V ≃* Multiplicative V')
    {G : Type} [Group G] {L : Subgroup (MulAut V)} (ι : G ≃* L)
    (Ψ : MulAut V ≃* (Module.End (ZMod 2) V')ˣ)
    (hΨact : ∀ (g : MulAut V) (v : V), (Ψ g).val (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ (g v)))
    {L' : Subgroup (Module.End (ZMod 2) V')ˣ}
    [Fact (repOfSubgroup L').IsIrreducible]
    (φS : G ≃* ↥L')
    (hφS : ∀ s, ((φS s : ↥L') : (Module.End (ZMod 2) V')ˣ) = Ψ ((ι s : ↥L) : MulAut V))
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing (repOfSubgroup L')) V')
    {k : Type} [Field k] (ιD : EndRing (repOfSubgroup L') →+* k)
    (hDinj : Function.Injective ιD)
    (ρ : Representation k G (Fin m → k))
    (hρ : ρ = (matRepE b ιD).comp φS.toMonoidHom) :
    ∃ ν : Additive V →+ (Fin m → k),
      Function.Injective ν ∧
      ∀ (g : G) (v : V), ν (Additive.ofMul ((ι g : MulAut V) v)) = ρ g (ν (Additive.ofMul v)) := by
  classical
  let c : V → V' := fun v => Multiplicative.toAdd (θ v)
  have hc_inj : Function.Injective c := fun v w h =>
    θ.injective (Multiplicative.toAdd.injective h)
  have hc_add : ∀ v w : V, c (v * w) = c v + c w := fun v w => by simp [c]
  have hc_act : ∀ (g : G) (v : V),
      c ((ι g : MulAut V) v) = (Ψ ((ι g : ↥L) : MulAut V)).val (c v) :=
    fun g v => (hΨact ((ι g : ↥L) : MulAut V) v).symm
  let ν : Additive V →+ (Fin m → k) :=
    { toFun := fun v => fun i => ιD (b.repr (c (Additive.toMul v)) i)
      map_zero' := by
        funext i
        simp [c]
      map_add' := by
        intro v w
        funext i
        have h : c (Additive.toMul (v + w)) = c (Additive.toMul v) + c (Additive.toMul w) := by
          simp [c, hc_add]
        rw [h, b.repr.map_add, Finsupp.add_apply, ιD.map_add, Pi.add_apply] }
  have hνinj : Function.Injective ν := by
    intro v w h
    have h1 : b.repr (c (Additive.toMul v)) = b.repr (c (Additive.toMul w)) := by
      ext1 i
      exact hDinj (congrFun h i)
    have h2 : c (Additive.toMul v) = c (Additive.toMul w) := b.repr.injective h1
    exact Additive.toMul.injective (hc_inj h2)
  have hνeq : ∀ (g : G) (v : V),
      ν (Additive.ofMul ((ι g : MulAut V) v)) = ρ g (ν (Additive.ofMul v)) := by
    intro g v
    funext i
    have hmatrix : b.repr (((φS g : ↥L') : (Module.End (ZMod 2) V')ˣ).val (c v)) =
        (matRep b (φS g)).mulVec (b.repr (c v)) := by
      change b.repr ((repD (repOfSubgroup L') (φS g)) (c v)) =
        (matRep b (φS g)).mulVec (b.repr (c v))
      rw [← LinearMap.toMatrix_mulVec_repr b b (repD (repOfSubgroup L') (φS g)) (c v)]
      rfl
    rw [hρ]
    show ιD (b.repr (c ((ι g : MulAut V) v)) i) = (matRepE b ιD (φS g)) (ν (Additive.ofMul v)) i
    rw [hc_act g v, ← hφS g]
    rw [hmatrix, RingHom.map_mulVec, matRepE_apply]
    congr 1
  exact ⟨ν, hνinj, hνeq⟩

private theorem rank_formula_aux
    {V : Type} [CommGroup V] [Finite V]
    {V' : Type} [AddCommGroup V'] [Module (ZMod 2) V'] [Finite V']
    (θ : V ≃* Multiplicative V')
    {G : Type} [Group G] {L : Subgroup (MulAut V)} (ι : G ≃* L)
    (Ψ : MulAut V ≃* (Module.End (ZMod 2) V')ˣ)
    (hΨact : ∀ (g : MulAut V) (v : V), (Ψ g).val (Multiplicative.toAdd (θ v)) =
      Multiplicative.toAdd (θ (g v)))
    {L' : Subgroup (Module.End (ZMod 2) V')ˣ}
    [Fact (repOfSubgroup L').IsIrreducible]
    (φS : G ≃* ↥L')
    (hφS : ∀ s, ((φS s : ↥L') : (Module.End (ZMod 2) V')ˣ) = Ψ ((ι s : ↥L) : MulAut V))
    {m : ℕ} (b : Module.Basis (Fin m) (EndRing (repOfSubgroup L')) V')
    {k : Type} [Field k] (ιD : EndRing (repOfSubgroup L') →+* k)
    (ρ : Representation k G (Fin m → k))
    (hρfun : ∀ g, ρ g = Matrix.toLin' ((matRep b (φS g)).map ιD))
    {δ : ℕ} (hDcard : Nat.card (EndRing (repOfSubgroup L')) = 2 ^ δ) :
    ∀ g : G, Nat.card V =
      2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) *
        Nat.card {v : V // (ι g : MulAut V) v = v} := by
  classical
  intro g
  let c : V → V' := fun v => Multiplicative.toAdd (θ v)
  have hc_inj : Function.Injective c := fun v w h =>
    θ.injective (Multiplicative.toAdd.injective h)
  have hc_act : ∀ (g : G) (v : V),
      c ((ι g : MulAut V) v) = (Ψ ((ι g : ↥L) : MulAut V)).val (c v) :=
    fun g v => (hΨact ((ι g : ↥L) : MulAut V) v).symm
  let f : V' →ₗ[EndRing (repOfSubgroup L')] V' := repD (repOfSubgroup L') (φS g) - 1
  have hfix : Nat.card {v : V // (ι g : MulAut V) v = v} =
      Nat.card {w : V' // f w = 0} := by
    refine Nat.card_congr ?_
    refine Equiv.subtypeEquiv (θ.toEquiv.trans Multiplicative.toAdd) ?_
    intro v
    constructor
    · intro hv
      have h1 : c ((ι g : MulAut V) v) = repD (repOfSubgroup L') (φS g) (c v) := by
        rw [hc_act g v, ← hφS g]
        rfl
      rw [hv] at h1
      exact sub_eq_zero.mpr h1.symm
    · intro hv
      have h1 : repD (repOfSubgroup L') (φS g) (c v) = c v := sub_eq_zero.mp hv
      apply hc_inj
      rw [hc_act g v, ← hφS g]
      exact h1
  have hker : Nat.card {w : V' // f w = 0} = Nat.card f.toAddMonoidHom.ker := rfl
  have hrange : Nat.card f.toAddMonoidHom.range =
      2 ^ (δ * Module.finrank (EndRing (repOfSubgroup L')) (LinearMap.range f)) := by
    have : Finite (LinearMap.range f) := Finite.of_injective _ Subtype.coe_injective
    have : Module.Finite (EndRing (repOfSubgroup L')) (LinearMap.range f) :=
      Module.Finite.of_finite
    have hcard : Nat.card f.toAddMonoidHom.range = Nat.card (LinearMap.range f) := rfl
    rw [hcard, Module.natCard_eq_pow_finrank (K := EndRing (repOfSubgroup L'))
      (V := LinearMap.range f), hDcard, pow_mul]
  have htoMatrix : (LinearMap.toMatrix b b) f = matRep b (φS g) - 1 := by
    show (LinearMap.toMatrix b b) (repD (repOfSubgroup L') (φS g) - 1) = _
    rw [map_sub, LinearMap.toMatrix_one]
    rfl
  have htoLin : Matrix.toLin b b (matRep b (φS g) - 1) = f := by
    rw [← htoMatrix, Matrix.toLin_toMatrix]
  have hfinD : Module.finrank (EndRing (repOfSubgroup L')) (LinearMap.range f) =
      (matRep b (φS g) - 1).rank := by
    rw [← htoLin]
    exact (Matrix.rank_eq_finrank_range_toLin (matRep b (φS g) - 1) b b).symm
  have hρsub : ρ g - 1 = Matrix.toLin' ((matRep b (φS g) - 1).map ιD) := by
    rw [hρfun g,
      show (1 : Module.End k (Fin m → k)) = Matrix.toLin' 1 from Matrix.toLin'_one.symm]
    rw [← map_sub]
    congr 1
    rw [Matrix.map_sub ιD (fun a b => map_sub ιD a b) ((matRep b (φS g))) 1,
      Matrix.map_one ιD (map_zero ιD) (map_one ιD)]
  have hfink : Module.finrank k (LinearMap.range (ρ g - 1)) =
      ((matRep b (φS g) - 1).map ιD).rank := by
    rw [hρsub, Matrix.rank]
    congr 1
  have hfinrank_eq : Module.finrank (EndRing (repOfSubgroup L')) (LinearMap.range f) =
      Module.finrank k (LinearMap.range (ρ g - 1)) := by
    rw [hfinD, hfink]
    exact (CFSG.RankThree.PartOne.FieldFix.rank_map_eq ιD (matRep b (φS g) - 1)).symm
  calc
    Nat.card V = Nat.card V' := Layer.Actor.natCard_eq θ
    _ = Nat.card f.toAddMonoidHom.ker * Nat.card f.toAddMonoidHom.range :=
        (AddSubgroup.card_ker_mul_card_range f.toAddMonoidHom).symm
    _ = Nat.card {v : V // (ι g : MulAut V) v = v} *
          2 ^ (δ * Module.finrank (EndRing (repOfSubgroup L')) (LinearMap.range f)) := by
        rw [← hker, ← hfix, hrange]
    _ = 2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) *
          Nat.card {v : V // (ι g : MulAut V) v = v} := by
        rw [hfinrank_eq, Nat.mul_comm]

theorem exists_periodic_rep {G : Type} [Group G] {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v * v = 1) {L : Subgroup (MulAut V)} (hirr : X1.IsIrrOn L) (ι : G ≃* L)
    {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) :
    ∃ (δ m : ℕ) (k : Type) (_ : Field k) (_ : Finite k) (_ : CharP k 2) (_ : Algebra K k)
      (ρ : Representation k G (Fin m → k)) (ν : Additive V →+ (Fin m → k)),
      1 ≤ δ ∧ 1 ≤ m ∧ IsSimpleRep ρ ∧ Function.Injective ρ ∧ Function.Injective ν ∧
      Nat.card V = 2 ^ (δ * m) ∧
      (∀ (g : G) (v : V),
        ν (Additive.ofMul ((ι g : MulAut V) v)) = ρ g (ν (Additive.ofMul v))) ∧
      (∀ g : G, Nat.card V =
        2 ^ (δ * Module.finrank k (LinearMap.range (ρ g - 1))) *
          Nat.card {v : V // (ι g : MulAut V) v = v}) ∧
      (∀ (g : G) (i j : Fin m), (ρ g (Pi.single j 1)) i ^ (2 ^ δ) = ρ g (Pi.single j 1) i) := by
  classical
  have hVnt : Nontrivial V := hirr.1
  obtain ⟨V', _, _, _, ⟨θ⟩⟩ := Layer.Actor.exists_binModel_of_binary hV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite V' := Finite.of_equiv V (θ.toEquiv.trans Multiplicative.toAdd)
  let c : V → V' := fun v => Multiplicative.toAdd (θ v)
  set Ψ : MulAut V ≃* (Module.End (ZMod 2) V')ˣ := binUnits θ with hΨ
  have hΨact : ∀ (g : MulAut V) (v : V), (Ψ g).val (c v) = c (g v) := by
    intro g v
    rw [hΨ]
    rw [binUnits_val]
    simp [c]
  set L' : Subgroup (Module.End (ZMod 2) V')ˣ := L.map Ψ.toMonoidHom with hL'
  have hirrL : (repOfSubgroup L').IsIrreducible := by
    simpa only [hL'] using repOfSubgroup_map_isIrreducible_aux θ hirr Ψ hΨact
  have : Fact (repOfSubgroup L').IsIrreducible := ⟨hirrL⟩
  let eL : ↥L ≃* ↥L' := Subgroup.equivMapOfInjective L Ψ.toMonoidHom Ψ.injective
  let φS : G ≃* ↥L' := ι.trans eL
  have hφS : ∀ s, ((φS s : ↥L') : (Module.End (ZMod 2) V')ˣ) = Ψ ((ι s : ↥L) : MulAut V) :=
    fun s => rfl
  have hDchar : CharP (EndRing (repOfSubgroup L')) 2 :=
    charP_of_injective_algebraMap (algebraMap (ZMod 2) (EndRing (repOfSubgroup L'))).injective 2
  have hDfin : Finite (EndRing (repOfSubgroup L')) := finite_endRing (repOfSubgroup L')
  have : Fintype (EndRing (repOfSubgroup L')) := Fintype.ofFinite _
  obtain ⟨δp, -, hδp⟩ := FiniteField.card (EndRing (repOfSubgroup L')) 2
  set δ : ℕ := (δp : ℕ) with hδdef
  have hDcard : Nat.card (EndRing (repOfSubgroup L')) = 2 ^ δ := by
    rw [Nat.card_eq_fintype_card, hδp]
  have hδ : 1 ≤ δ := δp.pos
  have : Module.Finite (EndRing (repOfSubgroup L')) V' := Module.Finite.of_finite
  have hV'nt : Nontrivial V' := by
    obtain ⟨x, hx⟩ := exists_ne (1 : V)
    exact ⟨⟨Multiplicative.toAdd (θ x), 0, fun h => hx (θ.injective (by simpa using h))⟩⟩
  set m : ℕ := Module.finrank (EndRing (repOfSubgroup L')) V' with hm
  let b : Module.Basis (Fin m) (EndRing (repOfSubgroup L')) V' := Module.finBasis _ V'
  have hm1 : 1 ≤ m := Module.finrank_pos
  have hV'card : Nat.card V' = 2 ^ (δ * m) := by
    rw [natCard_eq_pow_finrank (ρ := repOfSubgroup L'), hDcard, pow_mul]
  obtain ⟨-, k, _, _, _, ιK, ιD, -, -, -, -, hKinj, hDinj, -, hDfrob, -⟩ :=
    SL2Modules.finite_fields_common_extension 2 hn hδ hK hDcard
  let ρ : Representation k G (Fin m → k) := (matRepE b ιD).comp φS.toMonoidHom
  have hρ : ρ = (matRepE b ιD).comp φS.toMonoidHom := rfl
  have hρfun : ∀ g, ρ g = Matrix.toLin' ((matRep b (φS g)).map ιD) := fun g => rfl
  have hρirr : ρ.IsIrreducible := by
    have h0 := matRepE_isIrreducible b ιD
    rw [isIrreducible_iff] at h0 ⊢
    refine ⟨h0.1, fun U hU => h0.2 U fun g u hu => ?_⟩
    obtain ⟨s, rfl⟩ := φS.surjective g
    exact hU s u hu
  have hρsimple : IsSimpleRep ρ := (SL2Modules.isIrreducible_iff ρ).1 hρirr
  have hρinj : Function.Injective ρ := by
    intro s s' h
    have h1 : (matRep b (φS s)).map ιD = (matRep b (φS s')).map ιD :=
      Matrix.toLin'.injective h
    have h2 : matRep b (φS s) = matRep b (φS s') :=
      Matrix.ext fun i j => hDinj (congrFun (congrFun h1 i) j)
    have h3 : repD (repOfSubgroup L') (φS s) = repD (repOfSubgroup L') (φS s') :=
      (LinearMap.toMatrix b b).injective h2
    exact φS.injective (repD_repOfSubgroup_injective L' h3)
  have hentry : ∀ (s : G) (i j : Fin m), ρ s (Pi.single j 1) i = ιD (matRep b (φS s) i j) := by
    intro s i j
    show matRepE b ιD (φS s) (Pi.single j 1) i = _
    rw [matRepE_apply]
    simp
  obtain ⟨ν, hνinj, hνeq⟩ :=
    exists_equivariant_embedding_aux θ ι Ψ hΨact φS hφS b ιD hDinj ρ hρ
  have hrank := rank_formula_aux θ ι Ψ hΨact φS hφS b ιD ρ hρfun hDcard
  refine ⟨δ, m, k, inferInstance, inferInstance, inferInstance, ιK.toAlgebra, ρ, ν, hδ, hm1,
    hρsimple, hρinj, hνinj, ?_, hνeq, hrank, ?_⟩
  · rw [Layer.Actor.natCard_eq θ, hV'card]
  · intro g i j
    rw [hentry]
    exact hDfrob _

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

end
