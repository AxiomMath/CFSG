module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.Clique
public import CFSG.LocalAnalysis.ComponentClassification.PresentationLocalCarmichael

public section

namespace CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

open CFSG.ComponentClassification.PresentationLocal Equiv.Perm

variable {J : Type*} [Group J] [DecidableEq J] {D : J → Prop}

omit [DecidableEq J] in
theorem exists_alt_iso_of_clique (hD : OrderThreeClass D) {F : Finset J} (hF : IsClique D F)
    (hcard : 3 ≤ F.card) (htop : Subgroup.closure (F : Set J) = ⊤) :
    ∃ n : ℕ, 5 ≤ n ∧ ∃ e : J ≃* alternatingGroup (Fin n),
      ∀ p ∈ F, ((e p : alternatingGroup (Fin n)) : Equiv.Perm (Fin n)).IsThreeCycle := by
  set n := F.card + 2 with hn
  have hn5 : 5 ≤ n := by omega
  have hn3 : 3 ≤ n := by omega
  have hcardIdx : Fintype.card (CarmichaelIndex n) = Fintype.card F := by
    rw [← Fintype.card_congr (carmichaelIndexEquiv n), Fintype.card_fin, Fintype.card_coe]
    omega
  let eqv : CarmichaelIndex n ≃ F := Fintype.equivOfCardEq hcardIdx
  let x : CarmichaelIndex n → J := fun i => (eqv i : J)
  have hxD : ∀ i, D (x i) := fun i => hF.mem _ (eqv i).2
  have hx : ∀ i, x i ^ 3 = 1 := fun i => hD.cube _ (hxD i)
  have hxx : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := by
    intro i j hij
    refine hF.adj _ (eqv i).2 _ (eqv j).2 ?_
    intro h
    exact hij (eqv.injective (Subtype.ext h))
  obtain ⟨-, ⟨φ, hφ, -⟩, hrange⟩ := alternating_carmichael_presentation_universal_map hn3 x hx hxx
  have hrange' : φ.range = ⊤ := by
    rw [hrange φ hφ, ← htop]
    congr 1
    ext y
    simp only [Set.mem_range, Finset.mem_coe]
    constructor
    · rintro ⟨i, rfl⟩
      exact (eqv i).2
    · intro hy
      exact ⟨eqv.symm ⟨y, hy⟩, by simp [x]⟩
  have hsurj : Function.Surjective φ := MonoidHom.range_eq_top.1 hrange'
  have hsimple : IsSimpleGroup (alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_fin]; exact hn5)
  have hinj : Function.Injective φ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal φ.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ).1 h
    · exfalso
      obtain ⟨k⟩ : Nonempty (CarmichaelIndex n) := ⟨⟨⟨2, by omega⟩, le_rfl⟩⟩
      have hmem : carmichaelCycle k ∈ φ.ker := h ▸ Subgroup.mem_top _
      rw [MonoidHom.mem_ker, hφ k] at hmem
      exact hD.ne_one _ (hxD k) hmem
  let ψ : alternatingGroup (Fin n) ≃* J := MulEquiv.ofBijective φ ⟨hinj, hsurj⟩
  refine ⟨n, hn5, ψ.symm, ?_⟩
  intro p hp
  have hpx : x (eqv.symm ⟨p, hp⟩) = p := by simp [x]
  have : ψ.symm p = carmichaelCycle (eqv.symm ⟨p, hp⟩) := by
    rw [MulEquiv.symm_apply_eq]
    show p = φ _
    rw [hφ, hpx]
  rw [this]
  exact carmichaelPerm_isThreeCycle _

end CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation

end
