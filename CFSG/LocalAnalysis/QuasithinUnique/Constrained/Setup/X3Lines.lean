module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderBasic
public import Mathlib.RingTheory.Coalgebra.CoassocSimps
public import Mathlib.Tactic.Basify
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.QuasithinUnique.Setup.X3

variable {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]

structure OrderThree (T : U ≃ₗ[ZMod 2] U) : Prop where
  sq : ∀ m, T (T m) = m + T m
  fix : ∀ m, T m = m → m = 0

@[expose] def IsLine (T : U ≃ₗ[ZMod 2] U) (W : Submodule (ZMod 2) U) : Prop :=
  Nat.card W = 4 ∧ ∀ w ∈ W, T w ∈ W

@[expose] def Lines (T : U ≃ₗ[ZMod 2] U) : Type _ := {W : Submodule (ZMod 2) U // IsLine T W}

instance finite_lines [Finite U] (T : U ≃ₗ[ZMod 2] U) : Finite (Lines T) := by
  refine Finite.of_injective (fun W : Lines T => (W.1 : Set U)) (fun a b h => ?_)
  exact Subtype.ext (SetLike.coe_injective h)

section Basic

variable {T : U ≃ₗ[ZMod 2] U}

theorem OrderThree.add_self (x : U) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := rfl
  rw [← two_smul (ZMod 2) x, h2, zero_smul]

theorem OrderThree.ne_of_ne_zero (hT : OrderThree T) {m : U} (hm : m ≠ 0) : T m ≠ m :=
  fun h => hm (hT.fix m h)

@[expose] def lineSpan (T : U ≃ₗ[ZMod 2] U) (m : U) : Submodule (ZMod 2) U :=
  Submodule.span (ZMod 2) {m, T m}

theorem mem_lineSpan_iff (m x : U) :
    x ∈ lineSpan T m ↔ x = 0 ∨ x = m ∨ x = T m ∨ x = m + T m := by
  unfold lineSpan
  rw [Submodule.mem_span_pair]
  constructor
  · rintro ⟨a, b, rfl⟩
    have h01 : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide
    rcases h01 a with rfl | rfl <;> rcases h01 b with rfl | rfl <;> simp
  · rintro (rfl | rfl | rfl | rfl)
    · exact ⟨0, 0, by simp⟩
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
    · exact ⟨1, 1, by simp⟩

theorem card_ne_zero_subtype {V : Type*} [AddCommGroup V] [Finite V] :
    Nat.card {v : V // v ≠ 0} + 1 = Nat.card V := by
  have := Fintype.ofFinite V
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  have h1 : Fintype.card {v : V // v = 0} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨0, rfl⟩, fun x => Subtype.ext x.2⟩
  rw [h1]
  have : 0 < Fintype.card V := Fintype.card_pos
  omega

theorem lineSpan_coe_eq (m : U) :
    (lineSpan T m : Set U) = {x | x = 0 ∨ x = m ∨ x = T m ∨ x = m + T m} := by
  ext x
  exact mem_lineSpan_iff m x

theorem card_lineSpan [Finite U] (hT : OrderThree T) {m : U} (hm : m ≠ 0) :
    Nat.card ↥(lineSpan T m) = 4 := by
  have h1 : Nat.card ↥(lineSpan T m) = (lineSpan T m : Set U).ncard := by
    rw [← Nat.card_coe_set_eq]; rfl
  rw [h1, lineSpan_coe_eq]
  have hTm : T m ≠ m := hT.ne_of_ne_zero hm
  have hTm0 : T m ≠ 0 := fun h => hm (T.injective (by rw [h, map_zero]))
  have hsum0 : m + T m ≠ 0 := by
    intro h
    apply hTm
    have h2 : T m = -m := eq_neg_of_add_eq_zero_right h
    rw [h2]
    have := OrderThree.add_self m
    exact (neg_eq_of_add_eq_zero_right this)
  have hset : {x : U | x = 0 ∨ x = m ∨ x = T m ∨ x = m + T m} = {0, m, T m, m + T m} := by
    ext x; simp
  rw [hset]
  have hc : T m ≠ m + T m := by
    intro h
    apply hm
    have h' : m + T m = 0 + T m := by rw [zero_add]; exact h.symm
    exact add_right_cancel h'
  have hb : m ∉ ({T m, m + T m} : Set U) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨hTm.symm, fun h => hTm0 ?_⟩
    have h' : m + T m = m + 0 := by rw [add_zero]; exact h.symm
    exact add_left_cancel h'
  have ha : (0 : U) ∉ ({m, T m, m + T m} : Set U) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hm.symm, hTm0.symm, hsum0.symm⟩
  rw [Set.ncard_insert_of_notMem ha, Set.ncard_insert_of_notMem hb, Set.ncard_pair hc]

theorem isLine_lineSpan [Finite U] (hT : OrderThree T) {m : U} (hm : m ≠ 0) :
    IsLine T (lineSpan T m) := by
  refine ⟨card_lineSpan hT hm, ?_⟩
  intro w hw
  rw [mem_lineSpan_iff] at hw ⊢
  rcases hw with rfl | rfl | rfl | rfl
  · left; simp
  · right; right; left; rfl
  · right; right; right; exact hT.sq m
  · right; left
    rw [map_add, hT.sq m]
    have := OrderThree.add_self (T m)
    calc T m + (m + T m) = m + (T m + T m) := by abel
      _ = m := by rw [this, add_zero]

theorem eq_lineSpan_of_mem [Finite U] (hT : OrderThree T) {W : Submodule (ZMod 2) U}
    (hW : IsLine T W) {m : U} (hm : m ∈ W) (hm0 : m ≠ 0) : W = lineSpan T m := by
  have hle : lineSpan T m ≤ W := by
    refine Submodule.span_le.2 ?_
    rintro x (rfl | rfl)
    · exact hm
    · exact hW.2 m hm
  have hcard : Nat.card ↥W ≤ Nat.card ↥(lineSpan T m) := by
    rw [hW.1, card_lineSpan hT hm0]
  exact (CFSG.QuasithinUnique.Setup.Offender.submodule_eq_of_le_of_card_ge hle hcard).symm

theorem card_lines [Finite U] (hT : OrderThree T) : 3 * Nat.card (Lines T) + 1 = Nat.card U := by
  classical
  have : Fintype U := Fintype.ofFinite U
  have hLfin : Finite (Lines T) := by
    refine Finite.of_injective (fun W : Lines T => (W.1 : Set U)) (fun a b h => ?_)
    exact Subtype.ext (SetLike.coe_injective h)
  have : Fintype (Lines T) := Fintype.ofFinite _
  let f : {m : U // m ≠ 0} → Lines T := fun m => ⟨lineSpan T m.1, isLine_lineSpan hT m.2⟩
  have hfib : ∀ W : Lines T, Nat.card {x : {m : U // m ≠ 0} // f x = W} = 3 := by
    intro W
    have hequiv : {x : {m : U // m ≠ 0} // f x = W} ≃ {w : ↥W.1 // w ≠ 0} :=
      { toFun := fun x => ⟨⟨x.1.1, by
            have hW : W.1 = lineSpan T x.1.1 := (congrArg Subtype.val x.2).symm
            have hmem : x.1.1 ∈ lineSpan T x.1.1 := Submodule.subset_span (Or.inl rfl)
            rw [hW]
            exact hmem⟩, fun h => x.1.2 (congrArg Subtype.val h)⟩
        invFun := fun w => ⟨⟨w.1.1, fun h => w.2 (Subtype.ext h)⟩,
          Subtype.ext (by
            show lineSpan T w.1.1 = W.1
            exact (eq_lineSpan_of_mem hT W.2 w.1.2 (fun h => w.2 (Subtype.ext h))).symm)⟩
        left_inv := fun x => rfl
        right_inv := fun w => rfl }
    rw [Nat.card_congr hequiv]
    have h1 := card_ne_zero_subtype (V := ↥W.1)
    rw [W.2.1] at h1
    omega
  have hsum : Nat.card {m : U // m ≠ 0} = ∑ W : Lines T, Nat.card {x : {m : U // m ≠ 0} // f x = W} := by
    rw [← Nat.card_sigma, Nat.card_congr (Equiv.sigmaFiberEquiv f).symm]
  have hX := card_ne_zero_subtype (V := U)
  rw [hsum, Finset.sum_congr rfl (fun W _ => hfib W), Finset.sum_const, Finset.card_univ,
    ← Nat.card_eq_fintype_card, smul_eq_mul, mul_comm] at hX
  exact hX

@[expose] def NormT (T g : U ≃ₗ[ZMod 2] U) : Prop :=
  (∀ m, T (g m) = g (T m)) ∨ (∀ m, T (g m) = g (T (T m)))

theorem NormT.isLine_map [Finite U] {g : U ≃ₗ[ZMod 2] U} (hg : NormT T g)
    {W : Submodule (ZMod 2) U} (hW : IsLine T W) : IsLine T (W.map (g : U →ₗ[ZMod 2] U)) := by
  refine ⟨?_, ?_⟩
  · rw [← hW.1]
    exact Nat.card_congr (Submodule.equivMapOfInjective (g : U →ₗ[ZMod 2] U) g.injective W).toEquiv.symm
  · rintro _ ⟨w, hw, rfl⟩
    rcases hg with h | h
    · exact ⟨T w, hW.2 w hw, (h w).symm⟩
    · refine ⟨T (T w), hW.2 _ (hW.2 w hw), (h w).symm⟩

theorem map_map_symm (W : Submodule (ZMod 2) U) (g : U ≃ₗ[ZMod 2] U) :
    (W.map (g : U →ₗ[ZMod 2] U)).map (g.symm : U →ₗ[ZMod 2] U) = W := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    simpa using hy
  · intro hx
    exact ⟨g x, ⟨x, hx, rfl⟩, by simp⟩

theorem map_symm_map (W : Submodule (ZMod 2) U) (g : U ≃ₗ[ZMod 2] U) :
    (W.map (g.symm : U →ₗ[ZMod 2] U)).map (g : U →ₗ[ZMod 2] U) = W := by
  simpa using map_map_symm W g.symm

theorem map_map_comp (W : Submodule (ZMod 2) U) (g h : U ≃ₗ[ZMod 2] U) :
    (W.map (h : U →ₗ[ZMod 2] U)).map (g : U →ₗ[ZMod 2] U) = W.map ((g * h : U ≃ₗ[ZMod 2] U) : U →ₗ[ZMod 2] U) := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨h y, ⟨y, hy, rfl⟩, rfl⟩

@[expose] noncomputable def linesAct {H : Type*} [Group H] [Finite U]
    (σ : H →* (U ≃ₗ[ZMod 2] U)) (hσ : ∀ g, NormT T (σ g)) : H →* Equiv.Perm (Lines T) where
  toFun g :=
    { toFun := fun W => ⟨W.1.map (σ g : U →ₗ[ZMod 2] U), (hσ g).isLine_map W.2⟩
      invFun := fun W => ⟨W.1.map (σ g⁻¹ : U →ₗ[ZMod 2] U), (hσ g⁻¹).isLine_map W.2⟩
      left_inv := fun W => Subtype.ext (by
        show (W.1.map (σ g : U →ₗ[ZMod 2] U)).map (σ g⁻¹ : U →ₗ[ZMod 2] U) = W.1
        rw [map_inv]
        exact map_map_symm W.1 (σ g))
      right_inv := fun W => Subtype.ext (by
        show (W.1.map (σ g⁻¹ : U →ₗ[ZMod 2] U)).map (σ g : U →ₗ[ZMod 2] U) = W.1
        rw [map_inv]
        exact map_symm_map W.1 (σ g)) }
  map_one' := Equiv.ext fun W => Subtype.ext (by
    show W.1.map ((σ 1 : U ≃ₗ[ZMod 2] U) : U →ₗ[ZMod 2] U) = W.1
    rw [map_one]
    ext x
    simp)
  map_mul' a b := Equiv.ext fun W => Subtype.ext (by
    show W.1.map ((σ (a * b) : U ≃ₗ[ZMod 2] U) : U →ₗ[ZMod 2] U) =
      (W.1.map (σ b : U →ₗ[ZMod 2] U)).map (σ a : U →ₗ[ZMod 2] U)
    rw [map_map_comp, map_mul])

end Basic

end CFSG.QuasithinUnique.Setup.X3
