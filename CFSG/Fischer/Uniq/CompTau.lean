module

public import CFSG.Fischer.Uniq.Assemble
public import CFSG.Fischer.Uniq.YSize

public section

namespace CFSG.Fischer

open CFSG.Blueprint.Fischer

variable {X Y : Type} [Group X] [Group Y] {E : Set X} {F : Set Y}

theorem Pair.mem_compSet_of_adj (hP : Pair X E) {d : X} (hd : d ∈ E) {a b : E}
    (ha : a ∈ compSet E d) (hab : (commGraph E).Adj a b) : b ∈ compSet E d := by
  rw [Pair.mem_compSet_iff_reachable hP hd] at ha ⊢
  exact ha.trans hab.reachable

theorem Pair.tauE_mem_compSet (hP : Pair X E) {d : X} (hd : d ∈ E) {e f : E}
    (he : e ∈ compSet E d) (hf : f ∈ compSet E d) : tauE hP e f ∈ compSet E d := by
  rw [Pair.mem_compSet_iff_reachable hP hd] at he hf ⊢
  have hef : (commGraph E).Reachable e f := he.symm.trans hf
  have h := (SimpleGraph.Iso.reachable_iff (φ := Pair.tauAut hP e)).2 hef
  rw [Pair.tauAut_apply, Pair.tauAut_apply, Pair.tauE_self] at h
  exact he.trans h

theorem Pair.tau_of_compGraphIso (hE : Pair X E) (hF : Pair Y F) {d : X} {d' : Y}
    (hd : d ∈ E) (hd' : d' ∈ F) (β : compGraph E d ≃g compGraph F d')
    (hY : ∀ e x : Y, e ∈ F → x ∈ F → e * x ≠ x * e → ySet F e x ⊆ {e, x, e * x * e})
    (e f : compSet E d) :
    (((β ⟨tauE hE e f, Pair.tauE_mem_compSet hE hd e.2 f.2⟩ : compSet F d') : F) : Y) =
      ((β e : F) : Y) * (β f : F) * (β e : F) := by
  set t : compSet E d := ⟨tauE hE e f, Pair.tauE_mem_compSet hE hd e.2 f.2⟩
  have hadj : ∀ a b : compSet E d, (commGraph E).Adj a b ↔ (commGraph F).Adj (β a : F) (β b) :=
    fun a b => (β.map_adj_iff (v := a) (w := b)).symm
  by_cases hef : ((e : E) : X) * f = f * e
  · have ht : t = f := Subtype.ext ((Pair.tauE_eq_self_iff hE e f).2 hef)
    rw [ht]
    have hcomm : (((β e : compSet F d') : F) : Y) * (β f : F) = (β f : F) * (β e : F) := by
      rcases commGraph_eq_or_adj hef with h | h
      · rw [show e = f from Subtype.ext h]
      · exact ((hadj e f).1 h).2
    rw [hcomm, mul_assoc, Pair.mul_self hF (β e : F).2, mul_one]
  · have hne : (β e : F) ≠ β f := fun h => hef (by
      have := β.injective (Subtype.ext h)
      rw [this])
    have hβef : (((β e : compSet F d') : F) : Y) * (β f : F) ≠ (β f : F) * (β e : F) :=
      fun h => hef ((hadj e f).2 ⟨hne, h⟩).2
    have hmem : (((β t : compSet F d') : F) : Y) ∈ ySet F (β e : F) (β f : F) := by
      refine ⟨(β t : F).2, fun s hs => ?_⟩
      have hsF : s ∈ F := hs.1.1
      have hs1 : (commGraph F).Adj ⟨s, hsF⟩ (β e : F) := mem_localClass_iff_adj.1 hs.1
      have hs2 : (commGraph F).Adj ⟨s, hsF⟩ (β f : F) := mem_localClass_iff_adj.1 hs.2
      have hsc : (⟨s, hsF⟩ : F) ∈ compSet F d' :=
        Pair.mem_compSet_of_adj hF hd' (β e).2 ((commGraph F).adj_symm hs1)
      obtain ⟨s₀, hs₀⟩ := β.surjective ⟨⟨s, hsF⟩, hsc⟩
      have h1 : (commGraph E).Adj (s₀ : E) e := by
        rw [hadj, hs₀]; exact hs1
      have h2 : (commGraph E).Adj (s₀ : E) f := by
        rw [hadj, hs₀]; exact hs2
      have h3 : ((s₀ : E) : X) ∈ muSet E e f :=
        ⟨mem_localClass_iff_adj.2 h1, mem_localClass_iff_adj.2 h2⟩
      have h4 : ((s₀ : E) : X) ∈ LocalClass E (tauE hE e f : X) :=
        (Pair.subset_ySet hE (e : E).2 (f : E).2 hef (by simp)).2 h3
      have h5 : (commGraph E).Adj (s₀ : E) (t : E) := mem_localClass_iff_adj.1 h4
      rw [hadj, hs₀] at h5
      exact mem_localClass_iff_adj.2 h5
    rcases hY _ _ (β e : F).2 (β f : F).2 hβef hmem with h | h | h
    · have h' := congrArg (fun x : compSet E d => ((x : E) : X))
        (β.injective (Subtype.ext (Subtype.ext h)))
      exact absurd h' (Pair.mul_mul_ne_left hE (e : E).2 hef)
    · have h' := congrArg (fun x : compSet E d => ((x : E) : X))
        (β.injective (Subtype.ext (Subtype.ext h)))
      exact absurd h' (Pair.mul_mul_ne_right hE (e : E).2 hef)
    · exact h

end CFSG.Fischer
