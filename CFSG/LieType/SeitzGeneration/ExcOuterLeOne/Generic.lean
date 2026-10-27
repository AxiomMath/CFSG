module

public import CFSG.RankThree.PartOne.SEITZ6.G2Big

open CFSG.LieType.Chevalley

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

theorem closure_pair_eq_top_of_maximal {P : Type} [Group P] [Finite P] {R : Subgroup P}
    (hmax : ∀ M : Subgroup P, R ≤ M → M = R ∨ M = ⊤) (d : MulAut P)
    (hne : R.map d.toMonoidHom ≠ R) :
    Subgroup.closure ((R : Set P) ∪ (R.map d.toMonoidHom : Set P)) = ⊤ := by
  have hRle : R ≤ Subgroup.closure ((R : Set P) ∪ (R.map d.toMonoidHom : Set P)) :=
    fun x hx => Subgroup.subset_closure (Or.inl hx)
  rcases hmax _ hRle with h | h
  · exfalso
    apply hne
    have h2 : R.map d.toMonoidHom ≤ R := by
      intro x hx
      rw [← SetLike.mem_coe]
      have : x ∈ Subgroup.closure ((R : Set P) ∪ (R.map d.toMonoidHom : Set P)) :=
        Subgroup.subset_closure (Or.inr hx)
      rwa [h] at this
    exact Subgroup.eq_of_le_of_card_ge h2 (by
      rw [Subgroup.card_map_of_injective d.injective])
  · exact h

theorem subfield_eq_or_top {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {p : ℕ} (hp : p.Prime)
    (hσ : orderOf σ = p) (F : Subfield K) (hF : fixSubfield σ ≤ F) :
    F = fixSubfield σ ∨ F = ⊤ := by
  classical
  set k := fixSubfield σ with hk
  have hcard : Nat.card K = Nat.card k ^ p := by
    have := CFSG.RankThree.PartOne.SEITZ6.card_eq_card_fixSubfield_pow σ
    rwa [hσ] at this
  haveI : Finite k := inferInstance
  let F' : IntermediateField k K :=
    F.toIntermediateField (fun x => hF x.2)
  have hrank : Module.finrank k K = p := by
    haveI : Module.Finite k K := inferInstance
    have h1 := Module.natCard_eq_pow_finrank (K := k) (V := K)
    have hk2 : 2 ≤ Nat.card k := by
      have : Nontrivial k := inferInstance
      exact (Finite.one_lt_card (α := k))
    exact Nat.pow_right_injective hk2 (h1.symm.trans hcard)
  have hmul := Module.finrank_mul_finrank k F' K
  rw [hrank] at hmul
  have hdvd : Module.finrank k F' ∣ p := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · left
    have : F' = ⊥ := IntermediateField.finrank_eq_one_iff.1 h1
    ext x
    constructor
    · intro hx
      have hx' : x ∈ F' := hx
      rw [this, IntermediateField.mem_bot] at hx'
      obtain ⟨y, rfl⟩ := hx'
      exact y.2
    · intro hx
      exact hF hx
  · right
    rw [h1] at hmul
    have hfr : Module.finrank F' K = 1 := by
      have hp0 : 0 < p := hp.pos
      nlinarith
    have : F' = ⊤ := IntermediateField.finrank_eq_one_iff_eq_top.1 hfr
    ext x
    simp only [Subfield.mem_top, iff_true]
    have hx : x ∈ (⊤ : IntermediateField k K) := IntermediateField.mem_top
    rw [← this] at hx
    exact hx

theorem card_fixSubfield_eq_two_or_four_dvd {K : Type} [Field K] [Finite K] (σ : K ≃+* K)
    (h2 : ringChar K = 2) : Nat.card (fixSubfield σ) = 2 ∨ 4 ∣ Nat.card (fixSubfield σ) := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by rw [← h2]; exact ringChar.charP K
  haveI : CharP (fixSubfield σ) 2 :=
    ((fixSubfield σ).subtype.charP_iff Subtype.val_injective 2).2 inferInstance
  haveI : Fintype (fixSubfield σ) := Fintype.ofFinite _
  obtain ⟨n, -, hn⟩ := FiniteField.card (fixSubfield σ) 2
  rw [Nat.card_eq_fintype_card, hn]
  rcases Nat.lt_or_ge (n : ℕ) 2 with h | h
  · left
    have h1 : (n : ℕ) = 1 := by have := n.pos; omega
    rw [h1]
    norm_num
  · right
    exact (show (4 : ℕ) ∣ 2 ^ 2 by norm_num).trans (pow_dvd_pow 2 h)

end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
