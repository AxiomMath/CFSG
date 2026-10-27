module

public import CFSG.ClassicalInvolution.SmallCases.SmallWeyl
public import CFSG.ClassicalInvolution.Balance.FrameIndex.RootFamily

public section

namespace CFSG.ClassicalInvolution.Balance

open CFSG.ClassicalInvolution.SmallWeyl

variable {ι V : Type*} [AddCommGroup V] [Module (ZMod 2) V]

namespace RootFamily

variable (T : RootFamily ι V)

structure Nondegenerate : Prop where
  z_ne : ∀ i, T.z i ≠ 0
  χ_ne : ∀ i, T.χ i ≠ 0
  χ_z : ∀ i, T.χ i (T.z i) = 0

variable {T}

private theorem zmod_two_cases (x : ZMod 2) : x = 0 ∨ x = 1 := by
  revert x
  decide

private theorem zmod_two_smul_eq_ite {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (c : ZMod 2) (v : M) : c • v = if c = 1 then v else 0 := by
  rcases zmod_two_cases c with rfl | rfl <;> simp

theorem add_self_eq_zero (x : V) : x + x = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) x, h2, zero_smul]

@[expose] def datum (hT : T.Nondegenerate) (i : ι) : Datum V where
  vec := T.z i
  form := (T.χ i).toAddMonoidHom
  vec_ne_zero := hT.z_ne i
  form_ne_zero := fun h => hT.χ_ne i (LinearMap.ext fun x => by
    simpa using congrArg (fun f : V →+ ZMod 2 => f x) h)
  form_vec := hT.χ_z i

@[simp] theorem datum_vec (hT : T.Nondegenerate) (i : ι) : (T.datum hT i).vec = T.z i := rfl

@[simp] theorem datum_form_apply (hT : T.Nondegenerate) (i : ι) (x : V) :
    (T.datum hT i).form x = T.χ i x := rfl

theorem datum_eq_iff (hT : T.Nondegenerate) {i j : ι} :
    T.datum hT i = T.datum hT j ↔ T.z i = T.z j ∧ T.χ i = T.χ j := by
  constructor
  · intro h
    refine ⟨congrArg Datum.vec h, LinearMap.ext fun x => ?_⟩
    have := congrArg (fun p : Datum V => p.form x) h
    simpa using this
  · rintro ⟨h1, h2⟩
    refine Datum.ext h1 ?_
    ext x
    simp [h2]

theorem datum_adj_iff (hT : T.Nondegenerate) {i j : ι} :
    (T.datum hT i).Adj (T.datum hT j) ↔ T.χ i (T.z j) = 1 := by
  refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
  show T.χ j (T.z i) = 1
  rw [T.symm j i]
  exact h

theorem datum_pair (hT : T.Nondegenerate) (i j : ι) :
    (T.datum hT i).pair (T.datum hT j) = T.χ i (T.z j) := rfl

theorem datum_conj (hT : T.Nondegenerate) (i j : ι) :
    ∃ k, (T.datum hT i).conj (T.datum hT j) = T.datum hT k := by
  obtain ⟨k, hz, hχ⟩ := T.closed i j
  refine ⟨k, Datum.ext ?_ ?_⟩
  · simp only [Datum.conj, datum, Datum.pair, hz, zmod_two_smul_eq_ite]
    rfl
  · ext x
    simp only [Datum.conj, datum, Datum.pair, hχ, LinearMap.add_apply, LinearMap.smul_apply,
      smul_eq_mul, AddMonoidHom.add_apply, LinearMap.toAddMonoidHom_coe]
    rcases zmod_two_cases (T.χ j (T.z i)) with h | h <;> simp [h]

instance [Finite V] : Finite (Datum V) := by
  have : Finite (V →+ ZMod 2) :=
    Finite.of_injective (fun f : V →+ ZMod 2 => (f : V → ZMod 2)) DFunLike.coe_injective
  exact Finite.of_injective (fun p : Datum V => (p.vec, p.form))
    fun p q h => Datum.ext (congrArg Prod.fst h) (congrArg Prod.snd h)

noncomputable def dataFinset [Finite V] (hT : T.Nondegenerate) : Finset (Datum V) :=
  (Set.toFinite (Set.range (T.datum hT))).toFinset

theorem mem_dataFinset [Finite V] (hT : T.Nondegenerate) {p : Datum V} :
    p ∈ T.dataFinset hT ↔ ∃ i, T.datum hT i = p := by
  simp [dataFinset]

theorem dataFinset_nonempty [Finite V] [Nonempty ι] (hT : T.Nondegenerate) :
    (T.dataFinset hT).Nonempty := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨T.datum hT i, (T.mem_dataFinset hT).mpr ⟨i, rfl⟩⟩

theorem dataFinset_isSymm [Finite V] (hT : T.Nondegenerate) : IsSymm (T.dataFinset hT) := by
  intro p hp q hq
  obtain ⟨i, rfl⟩ := (T.mem_dataFinset hT).mp hp
  obtain ⟨j, rfl⟩ := (T.mem_dataFinset hT).mp hq
  exact T.symm i j

theorem dataFinset_isClosed [Finite V] (hT : T.Nondegenerate) : IsClosed (T.dataFinset hT) := by
  intro p hp q hq
  obtain ⟨i, rfl⟩ := (T.mem_dataFinset hT).mp hp
  obtain ⟨j, rfl⟩ := (T.mem_dataFinset hT).mp hq
  obtain ⟨k, hk⟩ := T.datum_conj hT i j
  rw [hk]
  exact (T.mem_dataFinset hT).mpr ⟨k, rfl⟩

theorem dataFinset_isConn [Finite V] (hT : T.Nondegenerate) : IsConn (T.dataFinset hT) := by
  intro p hp q hq
  obtain ⟨i, rfl⟩ := (T.mem_dataFinset hT).mp hp
  obtain ⟨j, rfl⟩ := (T.mem_dataFinset hT).mp hq
  refine (T.conn i j).lift (T.datum hT) fun a b hab => ?_
  exact ⟨(T.mem_dataFinset hT).mpr ⟨a, rfl⟩, (T.mem_dataFinset hT).mpr ⟨b, rfl⟩,
    (T.datum_adj_iff hT).mpr hab⟩

theorem dataFinset_classification_two [Finite V] [Nonempty ι] (hT : T.Nondegenerate)
    (hV : Nat.card V = 4) :
    (T.dataFinset hT).card = 1 ∨ ((T.dataFinset hT).card = 3 ∧
      ∀ i j, T.datum hT i ≠ T.datum hT j → T.χ i (T.z j) = 1) := by
  rcases rootSet_classification_two add_self_eq_zero hV (T.dataFinset hT)
    (T.dataFinset_nonempty hT) (T.dataFinset_isSymm hT) (T.dataFinset_isClosed hT)
    (T.dataFinset_isConn hT) with h | ⟨h3, hadj⟩
  · exact Or.inl h
  · refine Or.inr ⟨h3, fun i j hij => ?_⟩
    exact (T.datum_adj_iff hT).mp (hadj _ ((T.mem_dataFinset hT).mpr ⟨i, rfl⟩) _
      ((T.mem_dataFinset hT).mpr ⟨j, rfl⟩) hij)

theorem dataFinset_classification_three [Finite V] [Nonempty ι] (hT : T.Nondegenerate)
    (hV : Nat.card V = 8) :
    (T.dataFinset hT).card = 1 ∨ ((T.dataFinset hT).card = 3 ∧
      ∀ i j, T.datum hT i ≠ T.datum hT j → T.χ i (T.z j) = 1) ∨
      ((T.dataFinset hT).card = 6 ∧ ∀ i, ∃! q, q ∈ T.dataFinset hT ∧ q ≠ T.datum hT i ∧
        ¬ (T.datum hT i).Adj q) := by
  rcases rootSet_classification_three add_self_eq_zero hV (T.dataFinset hT)
    (T.dataFinset_nonempty hT) (T.dataFinset_isSymm hT) (T.dataFinset_isClosed hT)
    (T.dataFinset_isConn hT) with h | ⟨h3, hadj⟩ | ⟨h6, hu⟩
  · exact Or.inl h
  · refine Or.inr (Or.inl ⟨h3, fun i j hij => ?_⟩)
    exact (T.datum_adj_iff hT).mp (hadj _ ((T.mem_dataFinset hT).mpr ⟨i, rfl⟩) _
      ((T.mem_dataFinset hT).mpr ⟨j, rfl⟩) hij)
  · exact Or.inr (Or.inr ⟨h6, fun i => hu _ ((T.mem_dataFinset hT).mpr ⟨i, rfl⟩)⟩)

end RootFamily

end CFSG.ClassicalInvolution.Balance
