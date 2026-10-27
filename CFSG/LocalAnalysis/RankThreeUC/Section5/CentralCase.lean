module

public import CFSG.LocalAnalysis.RankThreeUC.BinaryRepresentations.BinaryHyperplaneSourceCorrect
public import CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialCenterFaithfulness
public import CFSG.LinearAlgebra.CoprimeActions.IrreducibleNormalFixedSpace

public section

namespace CFSG.LocalAnalysis.RankThreeUC

namespace Section5

namespace CentralCase

open scoped MonoidAlgebra in
theorem finiteDimensional {F G V : Type*} [Field F] [Group G] [Finite G]
    [AddCommGroup V] [Module F V] (ρ : Representation F G V) (h : ρ.IsIrreducible) :
    FiniteDimensional F V := by
  have : IsSimpleModule F[G] ρ.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule ρ).mp h
  have : Module.Finite F[G] ρ.asModule := inferInstance
  have : Module.Finite F ρ.asModule := Module.Finite.trans F[G] ρ.asModule
  exact this

private theorem center_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (Subgroup.center G).map e.toMonoidHom = Subgroup.center H := by
  ext y
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, Subgroup.mem_center_iff,
    Subgroup.mem_center_iff]
  constructor
  · intro hx g
    obtain ⟨g, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx]
  · intro hx g
    apply e.injective
    rw [map_mul, map_mul, hx]

private theorem frattini_map_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H) :
    (frattini G).map e.toMonoidHom = frattini H :=
  OrderIso.map_radical (MulEquiv.mapSubgroup e)

private theorem isExtraspecial_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : CFSG.IsExtraspecialPGroup p G) : CFSG.IsExtraspecialPGroup p H := by
  obtain ⟨hp, hcomm, hfrat, hcard⟩ := h
  have hc : (commutator G).map e.toMonoidHom = commutator H := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
  refine ⟨hp.of_equiv e, ?_, ?_, ?_⟩
  · rw [← hc, hcomm, center_map_mulEquiv]
  · rw [← frattini_map_mulEquiv e, hfrat, center_map_mulEquiv]
  · rw [← center_map_mulEquiv e, Subgroup.card_map_of_injective e.injective, hcard]

theorem bound {G : Type} [Group G] [Finite G] {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : CFSG.IsExtraspecialPGroup p ↥P) (hexp : Monoid.exponent ↥P = p)
    (hcard : Nat.card ↥P = p ^ (1 + 2 * n)) (hPn : P.Normal)
    {V : Type} [AddCommGroup V] [Module (ZMod 2) V] (ρ : Representation (ZMod 2) G V)
    (hρ : Function.Injective ρ) (hirr : ρ.IsIrreducible) {t : G} (ht : orderOf t = 2)
    (htc : t ∈ Subgroup.centralizer (P : Set G)) :
    p ^ (n - 1) * WeakClosure.dOfPrime p * (p - 1) ≤
      2 * Module.finrank (ZMod 2) ↥(BinaryRepresentations.commSpace ρ (Subgroup.zpowers t)) := by
  classical
  haveI := finiteDimensional ρ hirr
  set W : Submodule (ZMod 2) V := BinaryRepresentations.commSpace ρ (Subgroup.zpowers t) with hW
  have hzc : Subgroup.zpowers t ≤ Subgroup.centralizer (P : Set G) :=
    (Subgroup.zpowers_le).2 htc
  have hpres : ∀ g ∈ P, ∀ w ∈ W, ρ g w ∈ W := by
    intro g hg w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨x, hx, v, rfl⟩ := hw
      have hgx : g * x = x * g := Subgroup.mem_centralizer_iff.1 (hzc hx) g hg
      have : ρ g (ρ x v - v) = ρ x (ρ g v) - ρ g v := by
        rw [map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hgx]
      rw [this]
      exact Submodule.subset_span ⟨x, hx, ρ g v, rfl⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact W.add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact W.smul_mem c ha
  let σ : Representation (ZMod 2) P W :=
    { toFun := fun g => (ρ g).restrict (fun w hw => hpres g g.2 w hw)
      map_one' := by ext; simp
      map_mul' := by intro a b; ext; simp }
  have hσ : ∀ (g : P) (w : W), ((σ g w : W) : V) = ρ g (w : V) := fun _ _ => rfl
  have hWnt : Nontrivial W := by
    have ht1 : ρ t ≠ 1 := by
      intro h
      have : t = 1 := hρ (by rw [h, map_one])
      rw [this, orderOf_one] at ht
      omega
    obtain ⟨v, hv⟩ : ∃ v, ρ t v ≠ v := by
      by_contra hcon
      push Not at hcon
      exact ht1 (LinearMap.ext fun v => hcon v)
    refine ⟨⟨⟨ρ t v - v, Submodule.subset_span ⟨t, Subgroup.mem_zpowers t, v, rfl⟩⟩, 0, ?_⟩⟩
    intro h
    apply hv
    have := congrArg Subtype.val h
    simpa [sub_eq_zero] using this
  have hNnorm : (centerP P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨⟨g * (z : G) * g⁻¹, hPn.conj_mem _ z.2 g⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    apply Subtype.ext
    have hq : g⁻¹ * (q : G) * g ∈ P := by
      simpa using hPn.conj_mem (q : G) q.2 g⁻¹
    have hc := Subgroup.mem_center_iff.1 hz ⟨_, hq⟩
    have hc' : (g⁻¹ * (q : G) * g) * (z : G) = (z : G) * (g⁻¹ * (q : G) * g) :=
      congrArg Subtype.val hc
    show (q : G) * (g * (z : G) * g⁻¹) = (g * (z : G) * g⁻¹) * (q : G)
    calc (q : G) * (g * (z : G) * g⁻¹) = g * (g⁻¹ * (q : G) * g * (z : G)) * g⁻¹ := by group
      _ = g * ((z : G) * (g⁻¹ * (q : G) * g)) * g⁻¹ := by rw [hc']
      _ = (g * (z : G) * g⁻¹) * (q : G) := by group
  have hNbot : centerP P ≠ ⊥ := by
    intro h
    have h1 : Subgroup.center ↥P = ⊥ := by
      exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective P)).1 h
    have := hP.2.2.2
    rw [h1, Subgroup.card_bot] at this
    exact hp.one_lt.ne this
  have hinvV := CFSG.LinearAlgebra.CoprimeActions.IrreducibleNormalFixedSpace.fixedSpace_eq_bot ρ hρ hirr (centerP P) hNbot
  have hinv : Representation.invariants (σ.comp (Subgroup.center ↥P).subtype) = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    rw [Representation.mem_invariants] at hw
    have hwV : (w : V) ∈ Representation.invariants (ρ.comp (centerP P).subtype) := by
      rw [Representation.mem_invariants]
      rintro ⟨n, hn⟩
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hn
      have := congrArg Subtype.val (hw ⟨z, hz⟩)
      simpa [hσ] using this
    rw [hinvV] at hwV
    have : (w : V) = 0 := by simpa using hwV
    simp [Subtype.ext_iff, this]
  have hfaith : Function.Injective σ :=
    CFSG.LargeExtraspecial.RepresentationSupport.ExtraspecialCenterFaithfulness.injective_of_center_invariants_eq_bot hp hP σ hinv
  have hHtop : CFSG.IsExtraspecialPGroup p ↥(⊤ : Subgroup ↥P) :=
    isExtraspecial_of_mulEquiv Subgroup.topEquiv.symm hP
  have hexpTop : Monoid.exponent ↥(⊤ : Subgroup ↥P) = p := by
    rw [← hexp]; exact Monoid.exponent_eq_of_mulEquiv Subgroup.topEquiv
  have hcardTop : Nat.card ↥(⊤ : Subgroup ↥P) = p ^ (1 + 2 * n) := by
    rw [Subgroup.card_top]; exact hcard
  have hcen : BinaryRepresentations.centerIn (⊤ : Subgroup ↥P) = Subgroup.center ↥P := by
    unfold BinaryRepresentations.centerIn
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_center_iff.2 fun g =>
        congrArg Subtype.val (Subgroup.mem_center_iff.1 hy ⟨g, trivial⟩)
    · intro hx
      exact ⟨⟨x, trivial⟩, Subgroup.mem_center_iff.2 fun g =>
        Subtype.ext (Subgroup.mem_center_iff.1 hx g.1), rfl⟩
  obtain ⟨X0, hX0P, hX0c, hX0n⟩ := NoncentralOrderP.exists_subgroup hp hP hexp
  set X : Subgroup ↥P := X0.comap P.subtype with hX
  have hmapX : X.map P.subtype = X0 := by
    rw [hX, Subgroup.map_comap_eq_self]
    simpa using hX0P
  have hXcard : Nat.card X = p := by
    rw [← hX0c, ← hmapX, Subgroup.card_map_of_injective (Subgroup.subtype_injective P)]
  have hXZ : X ≠ BinaryRepresentations.centerIn (⊤ : Subgroup ↥P) := by
    intro h
    apply hX0n
    rw [← hmapX, h, hcen]
    rfl
  obtain ⟨-, h2, -, -, h5⟩ :=
    BinaryRepresentations.extraspecial_center_commutator_decomposition_and_dimension_bounds σ hfaith hp hp2 (⊤ : Subgroup ↥P) hHtop hexpTop hcardTop X le_top hXcard hXZ
  set U : Submodule (ZMod 2) W := BinaryRepresentations.commSpace σ (BinaryRepresentations.centerIn (⊤ : Subgroup ↥P)) with hU
  set m : ℕ := Module.finrank (ZMod 2) ↥(U ⊓ BinaryRepresentations.fixedSpace σ X) with hm
  have hUne : U ≠ ⊥ := by
    intro hUb
    obtain ⟨w, hw⟩ := exists_ne (0 : W)
    apply hw
    have : w ∈ Representation.invariants (σ.comp (Subgroup.center ↥P).subtype) := by
      rw [Representation.mem_invariants]
      rintro ⟨z, hz⟩
      have hzc : z ∈ BinaryRepresentations.centerIn (⊤ : Subgroup ↥P) := by rw [hcen]; exact hz
      have : σ z w - w ∈ U := Submodule.subset_span ⟨z, hzc, w, rfl⟩
      rw [hUb, Submodule.mem_bot, sub_eq_zero] at this
      exact this
    rw [hinv] at this
    simpa using this
  have hUpos : 0 < Module.finrank (ZMod 2) U := Submodule.one_le_finrank_iff.2 hUne
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h2, h] at hUpos; simp at hUpos
    · exact h
  have hdvd : p ^ (n - 1) * WeakClosure.dOfPrime p ≤ m := Nat.le_of_dvd hmpos h5
  have hle : Module.finrank (ZMod 2) U ≤ Module.finrank (ZMod 2) W := Submodule.finrank_le U
  calc p ^ (n - 1) * WeakClosure.dOfPrime p * (p - 1) ≤ m * (p - 1) := Nat.mul_le_mul_right _ hdvd
    _ ≤ m * p := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
    _ = Module.finrank (ZMod 2) U := h2.symm
    _ ≤ 2 * Module.finrank (ZMod 2) W := by omega

end CentralCase
end Section5
end CFSG.LocalAnalysis.RankThreeUC
