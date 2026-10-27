module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.G3NoProper
public import CFSG.Quasithin.Background.A3Structure314Radical

public section

namespace CFSG.QuasithinUnique.A5.G3

open Equiv CFSG.QuasithinUnique CFSG.Quasithin CFSG.Open
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem fixed_vector_of_order_three : ∀ σ : Perm (Fin 5), Perm.sign σ = 1 → σ ≠ 1 → σ ^ 3 = 1 →
    ∃ w : Fin 5 → ZMod 2, (∑ i, w i = 0) ∧ w ≠ 0 ∧ ∀ i, w (σ⁻¹ i) = w i := by
  decide +kernel

theorem exists_moving_perm : ∀ w : Fin 5 → ZMod 2, (∑ i, w i = 0) → w ≠ 0 →
    ∃ τ : Perm (Fin 5), Perm.sign τ = 1 ∧ ∃ i, w (τ⁻¹ i) ≠ w i := by
  decide +kernel

theorem exists_commutator_decomp : ∀ w : Fin 5 → ZMod 2, (∑ i, w i = 0) →
    ∃ v : Fin 5 → ZMod 2, (∑ i, v i = 0) ∧ ∃ τ : Perm (Fin 5), Perm.sign τ = 1 ∧
      ∀ i, w i = v i + v (τ⁻¹ i) := by
  decide +kernel

theorem card_evenWeight_five : Nat.card (evenWeight 5) = 16 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeEquivRight (fun x : Fin 5 → ZMod 2 =>
    Delta5.mem_evenWeight_iff x))]
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  decide +kernel

@[expose] def IsDelta5Group (X : Type) [Group X] : Prop :=
  ∃ (α : X →* alternatingGroup (Fin 5)) (β : ↥(CFSG.pCore 2 X) →* Multiplicative (evenWeight 5)),
    Function.Surjective α ∧ α.ker = CFSG.pCore 2 X ∧ Function.Bijective β ∧
    ∀ (x : X) (u v : ↥(CFSG.pCore 2 X)), (v : X) = x * u * x⁻¹ → ∀ i : Fin 5,
      ((Multiplicative.toAdd (β v) : evenWeight 5) : Fin 5 → ZMod 2) i =
        ((Multiplicative.toAdd (β u) : evenWeight 5) : Fin 5 → ZMod 2)
          (((α x : alternatingGroup (Fin 5)) : Perm (Fin 5))⁻¹ i)

section Basic

variable {X : Type} [Group X]

theorem evenWeight_add_self (w : evenWeight 5) : w + w = 0 := by
  apply Subtype.ext
  funext i
  simp [CharTwo.add_self_eq_zero]

theorem IsDelta5Group.card_pCore [Finite X] (h : IsDelta5Group X) :
    Nat.card (CFSG.pCore 2 X) = 16 := by
  obtain ⟨α, β, -, -, hβ, -⟩ := h
  rw [Nat.card_congr (Equiv.ofBijective β hβ),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (evenWeight 5) ≃ evenWeight 5)]
  exact card_evenWeight_five

theorem IsDelta5Group.card [Finite X] (h : IsDelta5Group X) : Nat.card X = 960 := by
  have hc := h.card_pCore
  obtain ⟨α, β, hαs, hαk, -, -⟩ := h
  have h1 := Subgroup.card_mul_index α.ker
  rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hαs, Subgroup.card_top, Delta5.a5_card,
    hαk, hc] at h1
  omega

theorem IsDelta5Group.mul_self_eq_one (h : IsDelta5Group X) (u : ↥(CFSG.pCore 2 X)) :
    u * u = 1 := by
  obtain ⟨α, β, -, -, hβ, -⟩ := h
  apply hβ.1
  rw [map_mul, map_one]
  apply Multiplicative.toAdd.injective
  simp [evenWeight_add_self]

theorem IsDelta5Group.isAlt_modO2 (h : IsDelta5Group X) :
    IsAlt 5 (X ⧸ CFSG.pCore 2 X) := by
  obtain ⟨α, β, hαs, hαk, -, -⟩ := h
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hαs)⟩

theorem IsDelta5Group.solvable_pCore [Finite X] : Group.IsSolvable ↥(CFSG.pCore 2 X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnil : Group.IsNilpotent ↥(CFSG.pCore 2 X) := CFSG.pCore_isPGroup.isNilpotent
  infer_instance

theorem IsDelta5Group.solvableRadical_eq [Finite X] (h : IsDelta5Group X) :
    CFSG.solvableRadical X = CFSG.pCore 2 X := by
  obtain ⟨α, β, hαs, hαk, -, -⟩ := h
  let e : (X ⧸ CFSG.pCore 2 X) ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq hαk.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs : IsSimpleGroup (X ⧸ CFSG.pCore 2 X) := e.isSimpleGroup
  have hna : ∃ a b : X ⧸ CFSG.pCore 2 X, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    apply not_solvable_alt5
    apply Group.isSolvable_of_comm
    intro a b
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hcon _ _
  exact A314.solvableRadical_eq_of_simple IsDelta5Group.solvable_pCore hs hna

theorem IsDelta5Group.isAlt_modRadical [Finite X] (h : IsDelta5Group X) :
    IsAlt 5 (X ⧸ CFSG.solvableRadical X) := by
  obtain ⟨e⟩ := h.isAlt_modO2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq h.solvableRadical_eq).trans e⟩

theorem IsDelta5Group.of_equiv {Y : Type} [Group Y] (e : X ≃* Y) (h : IsDelta5Group X) :
    IsDelta5Group Y := by
  obtain ⟨α, β, hαs, hαk, hβb, hβe⟩ := h
  have hP : (CFSG.pCore 2 X).map e.toMonoidHom = CFSG.pCore 2 Y := CFSG.pCore_map_iso 2 e
  let E : ↥(CFSG.pCore 2 X) ≃* ↥(CFSG.pCore 2 Y) :=
    (e.subgroupMap (CFSG.pCore 2 X)).trans (MulEquiv.subgroupCongr hP)
  have hE : ∀ u, ((E u : ↥(CFSG.pCore 2 Y)) : Y) = e (u : X) := fun u => rfl
  refine ⟨α.comp e.symm.toMonoidHom, β.comp E.symm.toMonoidHom, hαs.comp e.symm.surjective,
    ?_, hβb.comp E.symm.bijective, ?_⟩
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hαk, ← hP]
    constructor
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  · intro y u v huv i
    have hxu : ((E.symm u : ↥(CFSG.pCore 2 X)) : X) = e.symm (u : Y) := by
      apply e.injective
      rw [← hE, E.apply_symm_apply]
      simp
    have hxv : ((E.symm v : ↥(CFSG.pCore 2 X)) : X) = e.symm (v : Y) := by
      apply e.injective
      rw [← hE, E.apply_symm_apply]
      simp
    have := hβe (e.symm y) (E.symm u) (E.symm v) (by
      rw [hxu, hxv, huv]
      simp) i
    simpa using this

omit [Finite G] in
theorem isDelta5Group_of_block {L : Subgroup G} (hLa : IsAltType L 5) (hZ : blockZ L = ⊥)
    (hQ : blockQ L = blockU L) : IsDelta5Group ↥L := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβe⟩ := hLa
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, hZ, Subgroup.bot_subgroupOf]
  have hmem : ∀ x : ↥L, x ∈ CFSG.pCore 2 ↥L ↔ (x : G) ∈ blockU L := fun x =>
    (mem_pCore_iff_mem_pCoreOf x).trans (by rw [← hQ]; rfl)
  have hUL : blockU L ≤ L := by
    rw [← hQ]
    exact CFSG.LieType.BorelTits.pCoreOf_le 2 L
  let ε : ↥(CFSG.pCore 2 ↥L) ≃* ↥(blockU L) :=
    { toFun := fun x => ⟨(x : ↥L), (hmem x).1 x.2⟩
      invFun := fun u => ⟨⟨u, hUL u.2⟩, (hmem ⟨u, hUL u.2⟩).2 u.2⟩
      left_inv := fun x => rfl
      right_inv := fun u => rfl
      map_mul' := fun x y => rfl }
  refine ⟨α, β.comp ε.toMonoidHom, hαs, hαk, ⟨hβinj.comp ε.injective, hβs.comp ε.surjective⟩, ?_⟩
  intro x u v huv i
  have h' : (((v : ↥L)) : G) = (x : G) * ((u : ↥L) : G) * (x : G)⁻¹ := by
    have := congrArg Subtype.val huv
    simpa using this
  exact hβe x (ε u) (ε v) h' i

theorem IsDelta5Group.not_pCore_le_center (h : IsDelta5Group X) :
    ¬ CFSG.pCore 2 X ≤ Subgroup.center X := by
  intro hc
  obtain ⟨α, β, hαs, hαk, hβb, hβe⟩ := h
  have hw1e : ∑ i, (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) i = 0 := by decide
  have hw1n : (![1, 1, 0, 0, 0] : Fin 5 → ZMod 2) ≠ 0 := by decide
  obtain ⟨τ, hτs, i0, hi0⟩ := exists_moving_perm _ hw1e hw1n
  obtain ⟨u, hu⟩ := hβb.2 (Multiplicative.ofAdd
    (⟨![1, 1, 0, 0, 0], (Delta5.mem_evenWeight_iff _).2 hw1e⟩ : evenWeight 5))
  obtain ⟨x, hx⟩ := hαs ⟨τ, Equiv.Perm.mem_alternatingGroup.mpr hτs⟩
  have hcomm : (u : X) = x * (u : X) * x⁻¹ := by
    have := Subgroup.mem_center_iff.mp (hc u.2) x
    rw [this]
    simp
  have h1 := hβe x u u hcomm i0
  rw [hu, hx] at h1
  exact hi0 h1.symm

theorem IsDelta5Group.not_isQuasisimple (h : IsDelta5Group X) : ¬ CFSG.IsQuasisimple X := by
  intro hq
  obtain ⟨-, hsimple, -⟩ := hq
  have hnc := h.not_pCore_le_center
  obtain ⟨α, β, hαs, hαk, hβb, hβe⟩ := h
  have hN : ((CFSG.pCore 2 X).map (QuotientGroup.mk' (Subgroup.center X))).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective _)
  rcases hsimple.eq_bot_or_eq_top_of_normal
    ((CFSG.pCore 2 X).map (QuotientGroup.mk' (Subgroup.center X))) with h0 | h1
  · apply hnc
    intro x hx
    have : QuotientGroup.mk' (Subgroup.center X) x ∈
        (CFSG.pCore 2 X).map (QuotientGroup.mk' (Subgroup.center X)) := ⟨x, hx, rfl⟩
    rw [h0] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · apply not_solvable_alt5
    apply Group.isSolvable_of_comm
    have hrep : ∀ σ : alternatingGroup (Fin 5), ∃ z ∈ Subgroup.center X, α z = σ := by
      intro σ
      obtain ⟨x, rfl⟩ := hαs σ
      have : QuotientGroup.mk' (Subgroup.center X) x ∈
          (CFSG.pCore 2 X).map (QuotientGroup.mk' (Subgroup.center X)) := by
        rw [h1]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := this
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hnx
      refine ⟨n⁻¹ * x, ?_, ?_⟩
      · exact hnx
      · have : α n = 1 := by
          rw [← MonoidHom.mem_ker, hαk]
          exact hn
        rw [map_mul, map_inv, this]
        simp
    intro σ τ
    obtain ⟨z, hz, rfl⟩ := hrep σ
    obtain ⟨z', hz', rfl⟩ := hrep τ
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz' z)]

end Basic

end CFSG.QuasithinUnique.A5.G3
