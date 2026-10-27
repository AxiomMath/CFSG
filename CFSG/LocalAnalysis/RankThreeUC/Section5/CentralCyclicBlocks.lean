module

public import CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBlockDimensionOne

public section

namespace CFSG.LocalAnalysis.RankThreeUC.Section5.CentralCyclicBlocks

open CFSG.LocalAnalysis.RankThreeUC.Section5 CFSG.LocalAnalysis.RankThreeUC.Section5.FaithfulPImageVocabulary
  CFSG.LocalAnalysis.RankThreeUC.Section5.CentralBinaryBlocks CFSG.LocalAnalysis.RankThreeUC

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P T B : Subgroup G} {e : ℕ}
  {V : Type} [AddCommGroup V] [Module (ZMod 2) V] {ρ : Representation (ZMod 2) G V}

@[expose] def toSubgroup (hc : BinaryActionRankCounterexample G p P T B e ρ) (W : Submodule (ZMod p) (Space hc)) :
    Subgroup ↥P where
  carrier := {x | Space.mk hc x ∈ W}
  mul_mem' := fun {a b} ha hb => W.add_mem ha hb
  one_mem' := W.zero_mem
  inv_mem' := fun {a} ha => W.neg_mem ha

theorem mem_toSubgroup (hc : BinaryActionRankCounterexample G p P T B e ρ) (W : Submodule (ZMod p) (Space hc))
    (x : ↥P) : x ∈ toSubgroup hc W ↔ Space.mk hc x ∈ W := Iff.rfl

theorem toSubgroup_map (hc : BinaryActionRankCounterexample G p P T B e ρ) (W : Submodule (ZMod p) (Space hc))
    (φ : MulAut ↥P) : (toSubgroup hc W).map φ.toMonoidHom = toSubgroup hc (W.map (sigma hc φ)) := by
  ext x
  rw [Subgroup.mem_map, mem_toSubgroup, Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨Space.mk hc y, hy, rfl⟩
  · rintro ⟨w, hw, h⟩
    refine ⟨w.val, hw, ?_⟩
    have := congrArg Space.val h
    rw [sigma_apply] at this
    exact this

theorem isCyclic_toSubgroup (hc : BinaryActionRankCounterexample G p P T B e ρ)
    (W : Submodule (ZMod p) (Space hc)) (hW : Module.finrank (ZMod p) W ≤ 1) :
    IsCyclic (toSubgroup hc W) := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hW with h0 | h1
  · have : W = ⊥ := Submodule.finrank_eq_zero.mp h0
    subst this
    haveI : Subsingleton (toSubgroup hc (⊥ : Submodule (ZMod p) (Space hc))) := by
      refine ⟨fun a b => Subtype.ext ?_⟩
      have ha : Space.mk hc a.1 = 0 := (Submodule.mem_bot (ZMod p)).mp a.2
      have hb : Space.mk hc b.1 = 0 := (Submodule.mem_bot (ZMod p)).mp b.2
      exact congrArg Space.val (ha.trans hb.symm)
    infer_instance
  · have hcard : Nat.card W = p := by
      rw [Module.natCard_eq_pow_finrank (K := ZMod p) (V := W), h1]; simp
    have : Nat.card (toSubgroup hc W) = p :=
      (Nat.card_congr (Equiv.refl _)).trans hcard
    exact isCyclic_of_prime_card (p := p) this

theorem closure_eq_top (hc : BinaryActionRankCounterexample G p P T B e ρ) {I : Type}
    (W : I → Submodule (ZMod p) (Space hc)) (hW : (⨆ i, W i) = ⊤) :
    Subgroup.closure {x : ↥P | ∃ i, x ∈ toSubgroup hc (W i)} = ⊤ := by
  haveI : Fact p.Prime := ⟨prime hc⟩
  set S := Subgroup.closure {x : ↥P | ∃ i, x ∈ toSubgroup hc (W i)} with hS
  let S' : AddSubgroup (Space hc) :=
    { carrier := {v | v.val ∈ S}
      add_mem' := fun {a b} ha hb => S.mul_mem ha hb
      zero_mem' := S.one_mem
      neg_mem' := fun {a} ha => S.inv_mem ha }
  have hle : (⨆ i, W i) ≤ AddSubgroup.toZModSubmodule p S' :=
    iSup_le fun i v hv =>
      (show v.val ∈ S from Subgroup.subset_closure (⟨i, hv⟩ : ∃ j, v.val ∈ toSubgroup hc (W j)))
  rw [hW, top_le_iff] at hle
  refine eq_top_iff.mpr fun x _ => ?_
  have : Space.mk hc x ∈ AddSubgroup.toZModSubmodule p S' := by rw [hle]; trivial
  exact this

theorem blocks (hc : BinaryActionRankCounterexample G p P T B e ρ) (hr : IsPrimePow (2 ^ e - 1))
    (hXne : X hc ≠ ⊥) :
    ∃ (I : Type) (_ : Finite I) (E : I → Subgroup ↥P), (∀ i, IsCyclic (E i)) ∧
      Subgroup.closure {x : ↥P | ∃ i, x ∈ E i} = ⊤ ∧
      ∀ φ ∈ T.map (conjOnP P hc.faithfulBinaryIrreducibleAction.normal), ∀ i, (E i).map φ.toMonoidHom = E i := by
  have he : Odd e := (PrimeB.prime_order hc hr).2.2.1
  haveI : Fact p.Prime := ⟨prime hc⟩
  have hdec := CentralBinaryDecomposition.decomposition hc he hXne
  haveI : Finite (BinaryRepresentations.hyperplanes 2 (X hc)) := by
    haveI : Finite (MulAut ↥P) := inferInstance
    infer_instance
  refine ⟨BinaryRepresentations.hyperplanes 2 (X hc), inferInstance, fun K => toSubgroup hc (E hc K.val), ?_,
    closure_eq_top hc _ hdec.2, ?_⟩
  · intro K
    refine isCyclic_toSubgroup hc _ ?_
    by_cases hE : E hc K.val = ⊥
    · rw [hE]; simp
    · exact (CentralBlockDimensionOne.finrank_eq_one hc hr hXne K hE).le
  · intro φ hφ K
    rw [toSubgroup_map, CentralBlockCovariance.stability hc he K φ hφ]

end CFSG.LocalAnalysis.RankThreeUC.Section5.CentralCyclicBlocks
