module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.InClauses1

public section

namespace CFSG.QuasithinUnique.Lin2

open CFSG.Open CFSG.Quasithin
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {T M H S L D : Subgroup G} {n : ℕ}

section Clauses3

variable (h : Lin2Cfg G T M H S L n D) (dat : Lin2Data T M H S L n)
include h dat

theorem Lin2Data.clause4 : ∀ x ∈ T, x ∉ S → conjR D x ≤ Subgroup.normalizer (L : Set G) ∧
    (centerOf L = ⊥ ∨ (IsElemAbelian 2 (centerOf L) ∧ Nat.card (centerOf L) = 2 ^ n ∧
      ActsRegularlyOn (conjR D x) (nonIdentity (centerOf L)))) := by
  intro x hx hxS
  refine ⟨dat.conjR_D_le_normalizer_L h hx hxS, ?_⟩
  have hZc : blockZ L = centerOf L := blockZ_eq_centerOf h.charTwo_L dat.pCore_eq
  by_cases hZ : blockZ L = ⊥
  · left
    rw [← hZc]
    exact hZ
  · right
    obtain ⟨hZD, hcard⟩ := dat.blockZ_eq_D₀ h hZ
    rw [← hZc]
    have hY : ∀ a ∈ conjR D x, ∀ y ∈ blockZ L, a⁻¹ * y * a ∈ blockZ L := by
      intro a ha y hy
      have hn := mem_normalizer_blockZ_of (dat.conjR_D_le_normalizer_L h hx hxS ha)
      have := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) y).1 hy
      simpa using this
    have hfree : ∀ a ∈ conjR D x, a ≠ 1 → ∀ y ∈ blockZ L, a⁻¹ * y * a = y → y = 1 :=
      fun a ha ha1 y hy hay => dat.conjR_D_free h hx hxS ha ha1 (dat.Z_le_D₀ h hy) hay
    have hcard' : Nat.card (blockZ L) = Nat.card (conjR D x) + 1 := by
      rw [hZD, hcard, card_conjR, h.card_D]
      have : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hZD]
      exact dat.D₀_elem
    · rw [hZD]
      exact hcard
    · rintro b hb z ⟨hz, hz1⟩
      refine ⟨hY b hb z hz, fun e => hz1 ?_⟩
      have := congrArg (fun w => b * w * b⁻¹) e
      simpa [mul_assoc] using this
    · rintro z ⟨hz, hz1⟩ z' ⟨hz', hz1'⟩
      exact transitive_of_free_of_card hY hfree hcard' hz hz1 hz' hz1'
    · rintro z ⟨hz, hz1⟩ b hb hbz
      by_contra hb1
      exact hz1 (hfree b hb hb1 z hz hbz)

theorem Lin2Data.clause7 : ∀ x ∈ T, x ∉ S → IsElemAbelian 2 (blockU L) ∧
    IsElemAbelian 2 (conjR (blockU L) x) ∧
    ∀ E : Subgroup G, E ≤ thompsonJ S → IsElemAbelian 2 E →
      E ≤ blockU L ∨ E ≤ conjR (blockU L) x := by
  intro x hx hxS
  have hEU := (isElemAbelian_conjR_iff (blockU L) x).2 (dat.U_elem h)
  refine ⟨dat.U_elem h, hEU, fun E hER hE => ?_⟩
  obtain ⟨W, hWeq, hW3, -, -⟩ := dat.exists_W h hx hxS
  have hsq : ∀ u ∈ blockU L, u * u = 1 := fun u hu => by
    have := (dat.U_elem h).2 u hu
    rwa [pow_two] at this
  have hsq' : ∀ u ∈ conjR (blockU L) x, u * u = 1 := fun u hu => by
    have := hEU.2 u hu
    rwa [pow_two] at this
  have hinv : ∀ r ∈ thompsonJ S, r * r = 1 → r ∈ blockU L ∨ r ∈ conjR (blockU L) x := by
    intro r hr hr2
    rw [dat.R_eq_U_sup h hx hxS, sup_comm] at hr
    obtain ⟨u', hu', u, hu, rfl⟩ := (mem_sup_iff_of_le_normalizer
      (dat.U_le_normalizer_conjU h hx)).1 hr
    have hcomm : u' * u = u * u' := by
      have h1 : u' * u = (u' * u)⁻¹ := (inv_eq_of_mul_eq_one_right hr2).symm
      rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq u hu),
        inv_eq_of_mul_eq_one_right (hsq' u' hu')]
    by_cases hu'U : u' ∈ blockU L
    · left
      exact (blockU L).mul_mem hu'U hu
    · right
      have hu'R : u' ∈ thompsonJ S := dat.conjU_le_R h hx hu'
      have huW : u ∈ W := (hW3 u' hu'R hu'U u hu).2 hcomm.symm
      rw [hWeq] at huW
      exact (conjR (blockU L) x).mul_mem hu' huW.2
  have hEinv : ∀ e ∈ E, e ∈ blockU L ∨ e ∈ conjR (blockU L) x := fun e he => by
    refine hinv e (hER he) ?_
    have := hE.2 e he
    rwa [pow_two] at this
  by_cases hEU' : E ≤ blockU L
  · exact Or.inl hEU'
  · right
    have hex1 : ∃ e₁ ∈ E, e₁ ∉ blockU L := by
      by_contra hcon
      push Not at hcon
      exact hEU' hcon
    obtain ⟨e₁, he₁, he₁U⟩ := hex1
    have he₁x : e₁ ∈ conjR (blockU L) x := (hEinv e₁ he₁).resolve_left he₁U
    intro e he
    by_contra hex
    have heU : e ∈ blockU L := (hEinv e he).resolve_right hex
    rcases hEinv (e₁ * e) (E.mul_mem he₁ he) with h1 | h1
    · apply he₁U
      have := (blockU L).mul_mem h1 ((blockU L).inv_mem heU)
      simpa using this
    · apply hex
      have := (conjR (blockU L) x).mul_mem ((conjR (blockU L) x).inv_mem he₁x) h1
      simpa using this

omit dat in
theorem Lin2Data.clause8 : IsCyclic D ∧ Nat.card D = 2 ^ n - 1 := ⟨h.isCyclic_D, h.card_D⟩

end Clauses3

end CFSG.QuasithinUnique.Lin2
