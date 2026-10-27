module

public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.Sp
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinusDefs

public section

namespace CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.AGLEmbedding.LieOut
open CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb

section Core

variable {J : Type*} [Group J] {p : ℕ}

theorem FlagBlocks.false_of_nonsplit' (B : FlagBlocks p J) (hp : p.Prime) [∀ i, Finite (B.H i)]
    (top : B.ι → Prop) (htop : ∀ i j, top i → top j → i = j)
    (hH : ∀ i, ¬ top i → ¬ p ^ 2 ∣ Nat.card (B.H i)) {V E : Subgroup J} [Finite E]
    (hV : ⁅V, V⁆ = V) (hEV : E ≤ V) (hE : ∀ e ∈ E, e ^ p = 1) (hEc : p ^ 2 ≤ Nat.card E)
    {x : J} (hx : x ^ p = 1) (hxV : ∀ v ∈ V, v * x = x * v)
    (hcyc : ∀ i, top i → IsCyclic ↥(E.map (B.ρ i)))
    (hesc : ∀ i, ¬ top i → B.ρ i x = 1 → p ∣ Nat.card (V.map (B.ρ i)) → False) : False := by
  have hbot : ∀ i, ¬ top i → E.map (B.ρ i) = ⊥ := fun i hi =>
    map_eq_bot_of_transfer (B.ρ i) hp (hH i hi) hV hEV hE hx hxV (hesc i hi)
  have hcyc' : ∀ i, IsCyclic ↥(E.map (B.ρ i)) := by
    intro i
    by_cases hi : top i
    · exact hcyc i hi
    · rw [hbot i hi]
      infer_instance
  obtain ⟨i, j, hij, hi, hj⟩ := B.exists_two_ne_bot_map hp hE hEc hcyc'
  have hti : top i := by_contra fun h => hi (hbot i h)
  have htj : top j := by_contra fun h => hj (hbot j h)
  exact hij (htop i j hti htj)

end Core

theorem isCyclic_of_le_of_not_sq_dvd {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {H : Subgroup G} (hH : ¬ p ^ 2 ∣ Nat.card H) {Q : Subgroup G} (hQH : Q ≤ H)
    (hQ : IsPGroup p Q) : IsCyclic Q := by
  have hQ' : IsPGroup p (Q.subgroupOf H) := by
    intro g
    obtain ⟨n, hn⟩ := hQ (⟨(g.1 : G), g.2⟩ : Q)
    exact ⟨n, Subtype.ext (Subtype.ext (by simpa using congrArg Subtype.val hn))⟩
  have hc := isCyclic_of_isPGroup_of_not_sq_dvd hp hH hQ'
  exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hQH).toMonoidHom
    (Subgroup.subgroupOfEquivOfLe hQH).surjective

section GLTwo

variable {F : Type} [Field F] [Finite F]

theorem card_GL_two_of_card_two {κ : Type} [Fintype κ] [DecidableEq κ] (hk : Fintype.card κ = 2)
    (hF : Nat.card F = 2) : Nat.card (GL κ F) = 6 := by
  have : Fintype F := Fintype.ofFinite F
  rw [SpCell.card_GL_congr (K := F) (Fintype.equivFinOfCardEq hk), Matrix.card_GL_field,
    ← Nat.card_eq_fintype_card, hF]
  simp [Fin.prod_univ_two]

theorem isCyclic_of_perfect_gl_two [CharP F 2] (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) {κ : Type} [Fintype κ] [DecidableEq κ] (hk : Fintype.card κ ≤ 2)
    {P : Subgroup (GL κ F)} (hP : ⁅P, P⁆ = P) {Q : Subgroup (GL κ F)} (hQP : Q ≤ P)
    (hQ : IsPGroup p Q) : IsCyclic Q := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  have hp2 : p ≠ 2 := by rcases hp57 with rfl | rfl <;> norm_num
  rcases hK with hK2 | hK4
  · rcases Nat.lt_or_ge (Fintype.card κ) 2 with hlt | hge
    · have hPbot := SpCell.perfect_eq_bot_of_card_le_one (K := F) (by omega) hP
      have : Q = ⊥ := eq_bot_iff.2 (hPbot ▸ hQP)
      rw [this]
      infer_instance
    · have h2 : Fintype.card κ = 2 := by omega
      refine isCyclic_of_le_of_not_sq_dvd hp (H := ⊤) ?_ le_top hQ
      rw [Subgroup.card_top, card_GL_two_of_card_two h2 hK2]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      rcases hp57 with rfl | rfl <;> omega
  · exact SpCell.isCyclic_of_perfect_gl hk hK4 hp hp2 hP hQP hQ

end GLTwo

section Orders

variable {F : Type} [Field F] [Finite F]

theorem not_sq_dvd_card_SL_of_lift {G : Type*} [Group G] {J : Subgroup G} {p : ℕ}
    (hp57 : p = 5 ∨ p = 7) (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F)
    (hA1 : ∀ X : Subgroup G, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X) {k : ℕ}
    (φ : Matrix.SpecialLinearGroup (Fin k) F →* G) (hφ : Function.Injective φ)
    (hφJ : ¬ (k = 2 ∧ Nat.card F = 2) → ∀ A, φ A ∈ J) :
    ¬ p ^ 2 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) F) := by
  by_cases hc : k = 2 ∧ Nat.card F = 2
  · obtain ⟨rfl, hF⟩ := hc
    rw [SpCell.card_SL2_eq, hF]
    intro hd
    have := Nat.le_of_dvd (by norm_num) hd
    rcases hp57 with rfl | rfl <;> omega
  · exact SpCell.not_sq_dvd_card_SL hp57 hK hA1 φ hφ (hφJ hc)

theorem isCyclic_of_perfect_top [CharP F 2] {b c : F} {p : ℕ} (hp57 : p = 5 ∨ p = 7)
    (hK : Nat.card F = 2 ∨ 4 ≤ Nat.card F) {m : ℕ}
    (hm : m = 0 ∨ ¬ p ^ 2 ∣ Nat.card ↥(Ωm m F b c))
    {P : Subgroup (GL (Idx m) F)} (hPO : P ≤ CFSG.LieType.BorelTits.orthGroup (Qm m F b c))
    (hP : ⁅P, P⁆ = P) {Q : Subgroup (GL (Idx m) F)} (hQP : Q ≤ P) (hQ : IsPGroup p Q) :
    IsCyclic Q := by
  have hp : p.Prime := by rcases hp57 with rfl | rfl <;> norm_num
  rcases hm with rfl | hm
  · refine isCyclic_of_perfect_gl_two hK hp57 (κ := Idx 0) ?_ hP hQP hQ
    simp [Idx]
  · have hPΩ : P ≤ Ωm m F b c := by
      rw [← hP]
      exact Subgroup.commutator_mono hPO hPO
    exact isCyclic_of_le_of_not_sq_dvd hp hm (hQP.trans hPΩ) hQ

end Orders

section Top

variable {F : Type} [Field F] [Finite F]

theorem isQuasisimple_top {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    [CharP F 2] (hSQ : OmegaMinusSmallQS) {m : ℕ} (hm : 1 ≤ m) :
    CFSG.Open.IsQuasisimple ↥(Ωm m F b c) := by
  rcases Nat.lt_or_ge m 3 with hlt | hge
  · have := hSQ (m + 1) F b c hirr (by omega) (by omega)
    exact this
  · exact SpCell.open_of_isQuasisimple
      (CFSG.LieType.Universal.Spin.isQuasisimple_statedOmega_quadMinus (n := m + 1) (K := F)
        (b := b) (c := c) (by omega) hirr)

theorem not_sq_dvd_card_top_of_lift {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0)
    [CharP F 2] (hSQ : OmegaMinusSmallQS) {m : ℕ} (hm : 1 ≤ m) {G : Type*} [Group G]
    {J : Subgroup G} {p : ℕ}
    (hA1 : ∀ X : Subgroup G, X ≤ J → CFSG.Open.IsQuasisimple ↥X → ¬ p ^ 2 ∣ Nat.card X)
    (φ : ↥(Ωm m F b c) →* G) (hφ : Function.Injective φ) (hφJ : ∀ A, φ A ∈ J) :
    ¬ p ^ 2 ∣ Nat.card ↥(Ωm m F b c) := by
  intro hd
  have hX : CFSG.Open.IsQuasisimple ↥φ.range :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv
      (MonoidHom.ofInjective hφ).symm (isQuasisimple_top hirr hSQ hm)
  exact hA1 φ.range (by rintro _ ⟨A, rfl⟩; exact hφJ A) hX
    (by rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]; exact hd)

end Top

end CFSG.HardMathSupport.Curtis.NaturalModuleCensus.AltIb.OmegaMinus
