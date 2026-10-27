module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndBIdx3

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.EndB

open CFSG Subgroup
open scoped commutatorElement

theorem card_subtype_mem_countP {α : Type*} [DecidableEq α] {l : List α} (hl : l.Nodup)
    (p : α → Bool) : Nat.card {x : α // x ∈ l ∧ p x = true} = l.countP p := by
  have e1 : {x : α // x ∈ l ∧ p x = true} ≃ {x : α // x ∈ (l.filter p).toFinset} :=
    Equiv.subtypeEquivRight fun x => by simp
  rw [Nat.card_congr e1, Nat.card_eq_fintype_card, Fintype.card_coe,
    List.toFinset_card_of_nodup (hl.filter p), List.countP_eq_length_filter]

namespace IdxModel

variable {G : Type*} [Group G] {m : ℕ} {e : ℕ → G} {T : ℕ → ℕ → ℕ} {I : ℕ → ℕ} {o : ℕ}
  (h : IdxModel m e T I o)
include h

theorem card_sig {K : Subgroup G} {L : List ℕ} (hLm : ∀ i ∈ L, i < m)
    (hK : ∀ x, x ∈ K ↔ ∃ i ∈ L, e i = x) {z : ℕ} (hzm : z < m) {sq : Fin 4 → Bool}
    {cm : Fin 4 → Fin 4 → Bool} (Lk : Fin 4 → List ℕ) (hLk : ∀ k, ∀ i ∈ Lk k, i ∈ L)
    (hLk' : ∀ k, (Lk k).Nodup)
    (hLk2 : ∀ k, ∀ i ∈ L, T i i = (if sq k then z else o) → i ∈ Lk k) :
    Nat.card {a : Fin 4 → ↥K // SigRel (e z) sq cm (fun k => (a k : G))} =
      (quads (Lk 0) (Lk 1) (Lk 2) (Lk 3)).countP (sigIdx T I o z sq cm) := by
  classical
  set Q := quads (Lk 0) (Lk 1) (Lk 2) (Lk 3) with hQ
  have hQnd : Q.Nodup := nodup_quads (hLk' 0) (hLk' 1) (hLk' 2) (hLk' 3)
  rw [← card_subtype_mem_countP hQnd]
  have hqL : ∀ q ∈ Q, ∀ k, quadFun q k ∈ L := by
    intro q hq k
    obtain ⟨h0, h1, h2, h3⟩ := mem_quads.mp hq
    fin_cases k
    · exact hLk 0 _ h0
    · exact hLk 1 _ h1
    · exact hLk 2 _ h2
    · exact hLk 3 _ h3
  let f : {q // q ∈ Q ∧ sigIdx T I o z sq cm q = true} →
      {a : Fin 4 → ↥K // SigRel (e z) sq cm (fun k => (a k : G))} := fun q =>
    ⟨fun k => ⟨e (quadFun q.1 k), (hK _).mpr ⟨_, hqL q.1 q.2.1 k, rfl⟩⟩,
      (h.sigIdx_iff hzm fun k => hLm _ (hqL q.1 q.2.1 k)).mp q.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨q, hq, hq'⟩ ⟨q', hq₁, hq₁'⟩ hqq
      have hk : ∀ k, quadFun q k = quadFun q' k := fun k => by
        have := congrArg (fun a => ((a.1 k : ↥K) : G)) hqq
        exact h.inj _ (hLm _ (hqL q hq k)) _ (hLm _ (hqL q' hq₁ k)) this
      apply Subtype.ext
      obtain ⟨a₀, a₁, a₂, a₃⟩ := q
      obtain ⟨b₀, b₁, b₂, b₃⟩ := q'
      have e0 : a₀ = b₀ := hk 0
      have e1 : a₁ = b₁ := hk 1
      have e2 : a₂ = b₂ := hk 2
      have e3 : a₃ = b₃ := hk 3
      show (a₀, a₁, a₂, a₃) = (b₀, b₁, b₂, b₃)
      rw [e0, e1, e2, e3]
    · rintro ⟨a, ha⟩
      have hidx : ∀ k, ∃ i ∈ L, e i = (a k : G) := fun k => (hK _).mp (a k).2
      choose idx hidxL hidxe using hidx
      set q : ℕ × ℕ × ℕ × ℕ := (idx 0, idx 1, idx 2, idx 3) with hq
      have hqk : ∀ k, quadFun q k = idx k := by
        intro k
        fin_cases k <;> rfl
      have hrel : SigRel (e z) sq cm (fun k => e (quadFun q k)) := by
        have : (fun k => e (quadFun q k)) = fun k => ((a k : ↥K) : G) := by
          funext k
          rw [hqk, hidxe]
        rw [this]
        exact ha
      have hsq : ∀ k, idx k ∈ Lk k := by
        intro k
        refine hLk2 k _ (hidxL k) (h.inj _ (h.T_lt _ (hLm _ (hidxL k)) _ (hLm _ (hidxL k))) _ ?_ ?_)
        · cases sq k
          · exact h.o_lt
          · exact hzm
        · rw [h.e_T _ (hLm _ (hidxL k)) _ (hLm _ (hidxL k)), ← pow_two, hidxe, ha.1 k]
          cases sq k
          · simp [h.e_o]
          · simp
      have hqQ : q ∈ Q := mem_quads.mpr ⟨hsq 0, hsq 1, hsq 2, hsq 3⟩
      refine ⟨⟨q, hqQ, (h.sigIdx_iff hzm fun k => hLm _ (hqL q hqQ k)).mpr hrel⟩, ?_⟩
      apply Subtype.ext
      funext k
      apply Subtype.ext
      change e (quadFun q k) = _
      rw [hqk, hidxe]
  exact (Nat.card_eq_of_bijective f hf).symm

end IdxModel

end CFSG.ComponentClassification.HarrisLit.EndB
