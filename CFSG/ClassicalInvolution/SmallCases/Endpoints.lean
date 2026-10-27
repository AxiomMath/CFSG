module

public import CFSG.ClassicalInvolution.SmallCases.FrameChain
public import CFSG.ClassicalInvolution.SmallCases.GenerationSmall
public import CFSG.ClassicalInvolution.WeakCT.Main
public import CFSG.ClassicalInvolution.WeakCT.Spin
public import CFSG.ClassicalInvolution.Phan.Main
public import CFSG.ClassicalInvolution.Phan.Standard

public section

namespace CFSG.ClassicalInvolution

open scoped IsMulCommutative MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.WeakCT CFSG.ClassicalInvolution.Phan CFSG.Assembly.LowTwoRank
  CFSG.LieType.Steinberg CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Pairs

variable {G : Type} [Group G]

theorem linearBlockStandardPair_symm {F : Type} [Field F] {W K L : Subgroup G}
    (h : LinearBlockStandardPair F W K L) : LinearBlockStandardPair F W L K := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := h
  exact ⟨θ, c, hrange, hker, hcases.symm⟩

theorem exists_linearBlockStandardPair {F : Type} [Field F] {A K L : Subgroup G}
    (h : Commutes K L ∨ LinearA2Pair F A K L ∨ LinearA2Pair F A L K) (hnc : ¬ Commutes K L) :
    ∃ W, LinearBlockStandardPair F W K L := by
  rcases h with h | h | h
  · exact absurd h hnc
  · exact h.linearBlockStandardPair
  · obtain ⟨W, hW⟩ := h.linearBlockStandardPair
    exact ⟨W, linearBlockStandardPair_symm hW⟩

variable {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ} [Fact p.Prime] [CharP K₀ p]

theorem unitaryBlockStandardPair_symm {W K L : Subgroup G}
    (h : UnitaryBlockStandardPair K₀ p f W K L) : UnitaryBlockStandardPair K₀ p f W L K := by
  obtain ⟨θ, c, hrange, hker, hcases⟩ := h
  exact ⟨θ, c, hrange, hker, hcases.symm⟩

theorem unitaryBlockStandardPair_sup_of_a2Pair (hK : Nat.card K₀ = (p ^ f) ^ 2)
    (hq : p ^ f ≠ 2) {E P Q : Subgroup G} (h : UnitaryA2Pair K₀ p f E P Q) :
    UnitaryBlockStandardPair K₀ p f (P ⊔ Q) P Q := by
  obtain ⟨θ, hker, hP, hQ, -, -⟩ := h
  have e : ∀ B : Subgroup (Su K₀ p f 3),
      B.map (MulAut.conj (1 : Su K₀ p f 3)⁻¹).toMonoidHom = B := fun B => by
    rw [inv_one]
    exact conjSub_one B
  refine ⟨θ, 1, ?_, hker, Or.inl ⟨?_, ?_⟩⟩
  · rw [MonoidHom.range_eq_map, ← CFSG.ClassicalInvolution.Phan.B12_sup_B23 hK hq,
      Subgroup.map_sup, hP, hQ]
  · rw [e, hP]
  · rw [e, hQ]

theorem exists_unitaryBlockStandardPair_sup (hK : Nat.card K₀ = (p ^ f) ^ 2) (hq : p ^ f ≠ 2)
    {A P Q : Subgroup G}
    (h : Commutes P Q ∨ UnitaryA2Pair K₀ p f A P Q ∨ UnitaryA2Pair K₀ p f A Q P)
    (hnc : ¬ Commutes P Q) : UnitaryBlockStandardPair K₀ p f (P ⊔ Q) P Q := by
  rcases h with h | h | h
  · exact absurd h hnc
  · exact unitaryBlockStandardPair_sup_of_a2Pair hK hq h
  · rw [sup_comm]
    exact unitaryBlockStandardPair_symm (unitaryBlockStandardPair_sup_of_a2Pair hK hq h)

theorem nonempty_equiv_left_of_a2Pair (hK : Nat.card K₀ = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryA2Pair K₀ p f E P Q) : Nonempty (Su K₀ p f 2 ≃* P) := by
  obtain ⟨θ, hker, hP, -, -, -⟩ := h
  have hinj : Function.Injective (θ.comp (embSUid (unitaryInvolution K₀ p f) 2)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact eq_one_of_embSUid_mem_center hK 2 (hker hg)
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [← hP]
  exact MonoidHom.range_comp _ _

theorem nonempty_equiv_right_of_a2Pair (hK : Nat.card K₀ = (p ^ f) ^ 2) {E P Q : Subgroup G}
    (h : UnitaryA2Pair K₀ p f E P Q) : Nonempty (Su K₀ p f 2 ≃* Q) := by
  obtain ⟨θ, hker, -, hQ, -, -⟩ := h
  have hinj : Function.Injective (θ.comp (embSUid (unitaryInvolution K₀ p f) 0)) := by
    rw [injective_iff_map_eq_one]
    intro g hg
    exact eq_one_of_embSUid_mem_center hK 0 (hker hg)
  refine ⟨(MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr ?_)⟩
  rw [← hQ]
  exact MonoidHom.range_comp _ _

end Pairs

section Three

variable {F : Type} [Field F] {G : Type} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

theorem weakCT_recognition_of_frame_three {p f : ℕ} (hp : p.Prime) (hF : Nat.card F = p ^ f)
    (hq : 4 ≤ p ^ f) (Fr : RankFrame F Ω A S) [Finite ↥A] [IsMulCommutative ↥A]
    (hcard : Nat.card A = 8) (hS : S.Nonempty) (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) (hd : Fr.dataFinset.card = 6)
    (hstd : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L → ∃ W, LinearBlockStandardPair F W K L)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) :
    ∃ ψ : SL(4, F) →* G, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center SL(4, F) ∧
      CFSG.IsQuasisimple G ∧
      CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) StatedLieTag.PSL 4 p f := by
  have := Fr.finite
  obtain ⟨K₀, K₁, K₂, h⟩ := Fr.exists_isChainThree hcard hS hA2 hfib hconn hd
  have n10 : ¬ Commutes (K₁ : Subgroup G) K₀ :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (Fr.ne_of_adj h.adj₀)).mp h.adj₀
  have n12 : ¬ Commutes (K₁ : Subgroup G) K₂ :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (Fr.ne_of_adj h.adj₂)).mp h.adj₂
  have ne02 : K₀ ≠ K₂ := fun e => h.ne (congrArg Fr.datum e)
  have c02 : Commutes (K₀ : Subgroup G) K₂ := Fr.commutes_of_not_adj hA2 hfib ne02 h.nadj
  let U : Fin 3 → Subgroup G := ![K₀, K₁, K₂]
  have hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x := by
    have key : ∀ i j : Fin 3, (i : ℕ) + 1 < j → i = 0 ∧ j = 2 := by decide
    intro i j hij
    obtain ⟨rfl, rfl⟩ := key i j hij
    exact c02
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 → ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    have key : ∀ i j : Fin 3, (j : ℕ) = i + 1 → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by decide
    intro i j hij
    rcases key i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hstd K₀ K₀.2 K₁ K₁.2 (Fr.coe_ne_of_adj h.adj₀).symm (fun hc => n10 hc.symm)
    · exact hstd K₁ K₁.2 K₂ K₂.2 (Fr.coe_ne_of_adj h.adj₂) n12
  have hgen : ⨆ i, U i = ⊤ := by
    have hle := Fr.le_of_isChainThree hcard hA2 hinj hd h (V := ⨆ i, U i) (le_iSup U 0)
      (le_iSup U 1) (le_iSup U 2)
    rw [eq_top_iff, ← hspan]
    exact iSup₂_le fun K hK => hle K hK
  obtain ⟨ψ, hsurj, hker, hqs, hmodel⟩ :=
    weakCT_recognition_of_pairs F p f hp hF hq (n := 3) (by norm_num) hcomm hpair hgen
  exact ⟨ψ, hsurj, hker, hqs, hmodel⟩

theorem weakCT_recognition_of_frame_three_of_linear {p f : ℕ} (hp : p.Prime)
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ p ^ f) (Fr : RankFrame F Ω A S) [Finite ↥A]
    [IsMulCommutative ↥A] (hcard : Nat.card A = 8) (hS : S.Nonempty) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) (hd : Fr.dataFinset.card = 6)
    (hlin : ∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Commutes K L ∨ LinearA2Pair F A K L ∨ LinearA2Pair F A L K)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) :
    ∃ ψ : SL(4, F) →* G, Function.Surjective ψ ∧ ψ.ker ≤ Subgroup.center SL(4, F) ∧
      CFSG.IsQuasisimple G ∧
      CFSG.Blueprint.LieModel (G ⧸ Subgroup.center G) StatedLieTag.PSL 4 p f :=
  weakCT_recognition_of_frame_three hp hF hq Fr hcard hS (a2Dichotomy_of_rankFrame_linear Fr hlin)
    hfib hconn hd (fun K hK L hL hne hnc => exists_linearBlockStandardPair (hlin K hK L hL hne) hnc)
    hinj hspan

theorem exists_weakPhanA_of_frame_three {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ}
    [Fact p.Prime] [CharP K₀ p]
    (Fr : RankFrame F Ω A S) [Finite ↥A] [IsMulCommutative ↥A] (hcard : Nat.card A = 8)
    (hS : S.Nonempty) (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S)
    (hd : Fr.dataFinset.card = 6) (hiso : ∀ P ∈ S, Nonempty (Su K₀ p f 2 ≃* P))
    (hstd : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ¬ Commutes P Q →
      UnitaryBlockStandardPair K₀ p f (P ⊔ Q) P Q)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) :
    ∃ U : Fin 3 → Subgroup G, WeakPhanA K₀ p f 3 U (fun i j => U i ⊔ U j) := by
  have := Fr.finite
  obtain ⟨K₁, K₂, K₃, h⟩ := Fr.exists_isChainThree hcard hS hA2 hfib hconn hd
  have n10 : ¬ Commutes (K₂ : Subgroup G) K₁ :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (Fr.ne_of_adj h.adj₀)).mp h.adj₀
  have n12 : ¬ Commutes (K₂ : Subgroup G) K₃ :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (Fr.ne_of_adj h.adj₂)).mp h.adj₂
  have ne02 : K₁ ≠ K₃ := fun e => h.ne (congrArg Fr.datum e)
  have c02 : Commutes (K₁ : Subgroup G) K₃ := Fr.commutes_of_not_adj hA2 hfib ne02 h.nadj
  let U : Fin 3 → Subgroup G := ![K₁, K₂, K₃]
  have hcomm : ∀ i j : Fin 3, (i : ℕ) + 1 < j → ∀ x ∈ U i, ∀ y ∈ U j, x * y = y * x := by
    have key : ∀ i j : Fin 3, (i : ℕ) + 1 < j → i = 0 ∧ j = 2 := by decide
    intro i j hij
    obtain ⟨rfl, rfl⟩ := key i j hij
    exact c02
  have hpair : ∀ i j : Fin 3, (j : ℕ) = i + 1 →
      UnitaryBlockStandardPair K₀ p f ((fun i j => U i ⊔ U j) i j) (U i) (U j) := by
    have key : ∀ i j : Fin 3, (j : ℕ) = i + 1 → (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) := by decide
    intro i j hij
    rcases key i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hstd K₁ K₁.2 K₂ K₂.2 (Fr.coe_ne_of_adj h.adj₀).symm (fun hc => n10 hc.symm)
    · exact hstd K₂ K₂.2 K₃ K₃.2 (Fr.coe_ne_of_adj h.adj₂) n12
  have hgen : ⨆ i, U i = ⊤ := by
    have hle := Fr.le_of_isChainThree hcard hA2 hinj hd h (V := ⨆ i, U i) (le_iSup U 0)
      (le_iSup U 1) (le_iSup U 2)
    rw [eq_top_iff, ← hspan]
    exact iSup₂_le fun K hK => hle K hK
  exact ⟨U, fun i => by fin_cases i <;> exact hiso _ (by simp [U]), fun _ _ _ => rfl, hcomm,
    hpair, hgen⟩

theorem weakPhan_recognition_of_frame_three {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ}
    [Fact p.Prime] [CharP K₀ p] (hK : Nat.card K₀ = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (Fr : RankFrame F Ω A S) [Finite ↥A] [IsMulCommutative ↥A] (hcard : Nat.card A = 8)
    (hS : S.Nonempty) (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S)
    (hd : Fr.dataFinset.card = 6) (hiso : ∀ P ∈ S, Nonempty (Su K₀ p f 2 ≃* P))
    (hstd : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ¬ Commutes P Q →
      UnitaryBlockStandardPair K₀ p f (P ⊔ Q) P Q)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) :
    ∃ θ : Su K₀ p f 4 →* G, Function.Surjective θ ∧ θ.ker ≤ Subgroup.center (Su K₀ p f 4) := by
  obtain ⟨U, hW⟩ := exists_weakPhanA_of_frame_three (K₀ := K₀) (p := p) (f := f) Fr hcard hS hA2
    hfib hconn hd hiso hstd hinj hspan
  obtain ⟨θ, hsurj, hker⟩ := weakPhan_recognition K₀ p f hK hq (n := 3) (by norm_num) hW
  exact ⟨θ, hsurj, hker⟩

theorem weakPhan_simple_recognition_of_frame_three {K₀ : Type} [Field K₀] [Finite K₀] {p f : ℕ}
    [Fact p.Prime] [CharP K₀ p] (hK : Nat.card K₀ = (p ^ f) ^ 2) (hp : p ≠ 2) (hq : 5 ≤ p ^ f)
    (Fr : RankFrame F Ω A S) [Finite ↥A] [IsMulCommutative ↥A] (hcard : Nat.card A = 8)
    (hS : S.Nonempty) (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S) (hconn : NonCommConnected S)
    (hd : Fr.dataFinset.card = 6) (hiso : ∀ P ∈ S, Nonempty (Su K₀ p f 2 ≃* P))
    (hstd : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → ¬ Commutes P Q →
      UnitaryBlockStandardPair K₀ p f (P ⊔ Q) P Q)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) [IsSimpleGroup G]
    (hG : ∃ a b : G, a * b ≠ b * a) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 4 p f ∧ CFSG.Blueprint.OddLieType G := by
  obtain ⟨U, hW⟩ := exists_weakPhanA_of_frame_three (K₀ := K₀) (p := p) (f := f) Fr hcard hS hA2
    hfib hconn hd hiso hstd hinj hspan
  exact weakPhan_simple_native_recognition K₀ p f hK hp hq (n := 3) (by norm_num) hG hW

theorem weakPhan_recognition_of_frame_three_of_unitary {K₀ : Type} [Field K₀] [Finite K₀]
    {p f : ℕ} [Fact p.Prime] [CharP K₀ p] (hK : Nat.card K₀ = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    (Fr : RankFrame F Ω A S) [Finite ↥A] [IsMulCommutative ↥A] (hcard : Nat.card A = 8)
    (hS : S.Nonempty) (hfib : FibreLE2 S) (hconn : NonCommConnected S)
    (hd : Fr.dataFinset.card = 6)
    (hlin : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q →
      Commutes P Q ∨ UnitaryA2Pair K₀ p f A P Q ∨ UnitaryA2Pair K₀ p f A Q P)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) :
    ∃ θ : Su K₀ p f 4 →* G, Function.Surjective θ ∧ θ.ker ≤ Subgroup.center (Su K₀ p f 4) := by
  have hq2 : p ^ f ≠ 2 := by omega
  refine weakPhan_recognition_of_frame_three hK hq Fr hcard hS
    (a2Dichotomy_of_rankFrame_unitary Fr hK hlin) hfib hconn hd (fun P hP => ?_)
    (fun P hP Q hQ hne hnc => exists_unitaryBlockStandardPair_sup hK hq2 (hlin P hP Q hQ hne) hnc)
    hinj hspan
  obtain ⟨L, hL, hne, hnc⟩ := Fr.exists_not_commutes hconn hP
  rcases hlin P hP L hL hne with h | h | h
  · exact absurd h hnc
  · exact nonempty_equiv_left_of_a2Pair hK h
  · exact nonempty_equiv_right_of_a2Pair hK h

end Three

section Four

open CFSG.LieType CFSG.LieType.Universal CFSG.Timmesfeld CFSG.Blueprint

variable {F : Type} [Field F] {G : Type} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

theorem weakCT_recognition_of_frame_four {p f : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 4 p f)
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) (Fr : RankFrame F Ω A S) [Finite ↥A]
    [IsMulCommutative ↥A] (hcard : Nat.card A = 16) (hS : S.Nonempty) (hA2 : A2Dichotomy A S)
    (hfib : FibreLE2 S) (hconn : NonCommConnected S) (hd : Fr.dataFinset.card = 12)
    (hstd : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L → ∃ W, LinearBlockStandardPair F W K L)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) :
    ∃ Ψ : spinGroup (Spin.quadPlus 4 F) →* G, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G ∧
      LieModel (G ⧸ Subgroup.center G) .POmegaPlus 4 p f := by
  have := Fr.finite
  obtain ⟨K₀, K₁, K₂, K₃, h⟩ := Fr.exists_isStarFour hcard hS hA2 hfib hconn hd
  have n10 : ¬ Commutes (K₁ : Subgroup G) K₀ :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (Fr.ne_of_adj h.adj₀)).mp h.adj₀
  have n12 : ¬ Commutes (K₁ : Subgroup G) K₂ :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (Fr.ne_of_adj h.adj₂)).mp h.adj₂
  have n13 : ¬ Commutes (K₁ : Subgroup G) K₃ :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (Fr.ne_of_adj h.adj₃)).mp h.adj₃
  have c02 : Commutes (K₀ : Subgroup G) K₂ :=
    Fr.commutes_of_not_adj hA2 hfib (fun e => h.ne₀₂ (congrArg Fr.datum e)) h.nadj₀₂
  have c03 : Commutes (K₀ : Subgroup G) K₃ :=
    Fr.commutes_of_not_adj hA2 hfib (fun e => h.ne₀₃ (congrArg Fr.datum e)) h.nadj₀₃
  have c23 : Commutes (K₂ : Subgroup G) K₃ :=
    Fr.commutes_of_not_adj hA2 hfib (fun e => h.ne₂₃ (congrArg Fr.datum e)) h.nadj₂₃
  let U : Fin 4 → Subgroup G := ![K₀, K₁, K₂, K₃]
  have hcomm : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
      ∀ a ∈ U i, ∀ b ∈ U j, a * b = b * a := by
    have key : ∀ i j : Fin 4, i ≠ j → ¬ edgeD 4 i j → ¬ edgeD 4 j i →
        (i = 0 ∧ j = 2) ∨ (i = 0 ∧ j = 3) ∨ (i = 2 ∧ j = 0) ∨ (i = 2 ∧ j = 3) ∨
          (i = 3 ∧ j = 0) ∨ (i = 3 ∧ j = 2) := by decide
    intro i j hij h1 h2
    rcases key i j hij h1 h2 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
      ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    exacts [c02, c03, c02.symm, c23, c03.symm, c23.symm]
  have hpair : ∀ i j : Fin 4, edgeD 4 i j → ∃ W, LinearBlockStandardPair F W (U i) (U j) := by
    have key : ∀ i j : Fin 4, edgeD 4 i j →
        (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 2) ∨ (i = 1 ∧ j = 3) := by decide
    intro i j hij
    rcases key i j hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hstd K₀ K₀.2 K₁ K₁.2 (Fr.coe_ne_of_adj h.adj₀).symm (fun hc => n10 hc.symm)
    · exact hstd K₁ K₁.2 K₂ K₂.2 (Fr.coe_ne_of_adj h.adj₂) n12
    · exact hstd K₁ K₁.2 K₃ K₃.2 (Fr.coe_ne_of_adj h.adj₃) n13
  have hgen : ⨆ i, U i = ⊤ := by
    have hle := Fr.le_of_isStarFour hcard hA2 hinj hd h (V := ⨆ i, U i) (le_iSup U 0)
      (le_iSup U 1) (le_iSup U 2) (le_iSup U 3)
    rw [eq_top_iff, ← hspan]
    exact iSup₂_le fun K hK => hle K hK
  obtain ⟨Ψ, hsurj, hker, hqs, -, hmodel, -⟩ :=
    weakCT_spinPlus hadm (by norm_num) hF hq U hgen hcomm hpair
  exact ⟨Ψ, hsurj, hker, hqs, hmodel⟩

theorem weakCT_recognition_of_frame_four_of_linear {p f : ℕ}
    (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible .POmegaPlus 4 p f)
    (hF : Nat.card F = p ^ f) (hq : 4 ≤ Nat.card F) (Fr : RankFrame F Ω A S) [Finite ↥A]
    [IsMulCommutative ↥A] (hcard : Nat.card A = 16) (hS : S.Nonempty) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) (hd : Fr.dataFinset.card = 12)
    (hlin : ∀ K ∈ S, ∀ L ∈ S, K ≠ L →
      Commutes K L ∨ LinearA2Pair F A K L ∨ LinearA2Pair F A L K)
    (hinj : Fr.DatumInjective) (hspan : frameSpan S = ⊤) :
    ∃ Ψ : spinGroup (Spin.quadPlus 4 F) →* G, Function.Surjective Ψ ∧
      Ψ.ker ≤ Subgroup.center _ ∧ CFSG.IsQuasisimple G ∧
      LieModel (G ⧸ Subgroup.center G) .POmegaPlus 4 p f :=
  weakCT_recognition_of_frame_four hadm hF hq Fr hcard hS (a2Dichotomy_of_rankFrame_linear Fr hlin)
    hfib hconn hd (fun K hK L hL hne hnc => exists_linearBlockStandardPair (hlin K hK L hL hne) hnc)
    hinj hspan

end Four

end CFSG.ClassicalInvolution
