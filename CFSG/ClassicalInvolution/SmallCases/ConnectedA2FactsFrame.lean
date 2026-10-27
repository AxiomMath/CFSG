module

public import CFSG.ClassicalInvolution.SmallCases.ConnectedA2FactsFibre
public import CFSG.ClassicalInvolution.Generic.Sign

public section

namespace CFSG.ClassicalInvolution.ConnectedA2

open scoped IsMulCommutative MatrixGroups
open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.SmallWeyl CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Generic.DeltaClosure

section Sign

variable {F : Type} [Field F] [Finite F] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  {A : Subgroup G} {S : Set (Subgroup G)}

theorem rankFrame_sign_constant (Fr : RankFrame F Ω A S) (hconn : NonCommConnected S)
    (hadj : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L →
      Nat.card (centPart K A) = Nat.card (centPart L A)) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ K ∈ S, (Nat.card (centPart K A) : ℤ) = Nat.card F - ε := by
  have hall : ∀ K L : ↥S, Nat.card (centPart (K : Subgroup G) A) =
      Nat.card (centPart (L : Subgroup G) A) := by
    intro K L
    obtain ⟨p⟩ := hconn.preconnected K L
    induction p with
    | nil => rfl
    | cons h _ ih =>
      obtain ⟨h1, h2⟩ := nonCommGraph_adj.mp h
      exact (hadj _ (Subtype.prop _) _ (Subtype.prop _) (fun h => h1 (Subtype.ext h)) h2).trans ih
  obtain ⟨K₀, hK₀, -⟩ := Fr.two_le
  obtain ⟨-, η, hη, hcard⟩ := (Fr.inSigma hK₀).isCyclic_and_card_centPart Fr.odd
  refine ⟨η, hη, fun K hK => ?_⟩
  rw [← hcard]
  exact_mod_cast hall ⟨K, hK⟩ ⟨K₀, hK₀⟩

theorem rankFrame_sign_constant_pairs (Fr : RankFrame F Ω A S) (hconn : NonCommConnected S)
    {K' : Type} [Field K'] [Finite K'] {p f : ℕ} [Fact p.Prime] [CharP K' p]
    (hK : Nat.card K' = (p ^ f) ^ 2) (hF : Nat.card F = p ^ f)
    (h : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L →
      LinearPair F A K L ∨ UnitaryPair K' p f A K L) :
    (∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L → LinearPair F A K L) ∨
      (∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L → UnitaryPair K' p f A K L) := by
  have hq : 1 ≤ Nat.card F := Nat.card_pos
  have hadj : ∀ K ∈ S, ∀ L ∈ S, K ≠ L → ¬ Commutes K L →
      Nat.card (centPart K A) = Nat.card (centPart L A) := by
    intro K hK' L hL hKL hc
    rcases h K hK' L hL hKL hc with h1 | h1
    · exact h1.card_centPart.1.trans h1.card_centPart.2.symm
    · exact (h1.card_centPart hK).1.trans (h1.card_centPart hK).2.symm
  obtain ⟨ε, hε, hεK⟩ := rankFrame_sign_constant Fr hconn hadj
  rcases hε with rfl | rfl
  · left
    have hcard : ∀ K ∈ S, Nat.card (centPart K A) = Nat.card F - 1 := by
      intro K hK'
      have := hεK K hK'
      omega
    intro K hK' L hL hKL hc
    rcases h K hK' L hL hKL hc with h1 | h1
    · exact h1
    · exfalso
      have := (h1.card_centPart hK).1
      have h2 := hcard K hK'
      omega
  · right
    have hcard : ∀ K ∈ S, Nat.card (centPart K A) = Nat.card F + 1 := by
      intro K hK'
      have := hεK K hK'
      omega
    intro K hK' L hL hKL hc
    rcases h K hK' L hL hKL hc with h1 | h1
    · exfalso
      have := h1.card_centPart.1
      have h2 := hcard K hK'
      omega
    · exact h1

end Sign

section Datum

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G] {F : Type}
  [Field F] {A : Subgroup G} {S : Set (Subgroup G)}

theorem datumInjective_of_branch {K : Subgroup G} {z : G} (hb : Branch p f K z)
    (hex : ExactMembers (conjClass K)) (Fr : RankFrame F (conjClass K) A S)
    (hP1 : FrameP1 (conjClass K) A) [Finite ↥A] [IsMulCommutative ↥A]
    (hcard : Nat.card A = 8) (hS : S.Nonempty) (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) (hd : Fr.dataFinset.card = 6) : Fr.DatumInjective := by
  intro K₁ K₂ hK
  by_contra hne
  have hne' : (K₁ : Subgroup G) ≠ K₂ := fun h => hne (Subtype.ext h)
  have hz : Fr.zOf K₁ = Fr.zOf K₂ :=
    congrArg (fun d : Datum (Additive ↥A) => ((Additive.toMul d.vec : ↥A) : G)) hK
  rcases Fr.datum_classification_three hcard hS hA2 hfib hconn with h1 | ⟨h3, -⟩ | ⟨h6, hval⟩
  · exact absurd (h1.symm.trans hd) (by norm_num)
  · exact absurd (h3.symm.trans hd) (by norm_num)
  · obtain ⟨q, ⟨hqR, hqne, hqna⟩, -⟩ := hval _ (Fr.mem_dataFinset.mpr ⟨K₁, rfl⟩)
    obtain ⟨M, rfl⟩ := Fr.mem_dataFinset.mp hqR
    have hK₁M : K₁ ≠ M := fun h => hqne (by rw [← h])
    have hK₂M : K₂ ≠ M := fun h => hqne (by rw [← h, ← hK])
    have c₁ : Commutes (K₁ : Subgroup G) M := Fr.commutes_of_not_adj hA2 hfib hK₁M hqna
    have c₂ : Commutes (K₂ : Subgroup G) M :=
      Fr.commutes_of_not_adj hA2 hfib hK₂M (by rw [← hK]; exact hqna)
    have hw₁ := Fr.isUniqueInvolution_zOf K₁
    have hw₂ : IsUniqueInvolution (K₂ : Subgroup G) (Fr.zOf K₁) := by
      rw [hz]
      exact Fr.isUniqueInvolution_zOf K₂
    exact hb.noBoot (bootData_of_twins hb hex Fr hP1 K₁.2 K₂.2 M.2 hw₁ hw₂ hne' c₁.symm c₂.symm)

end Datum

section DatumFacts

variable {F : Type} [Field F] {G : Type} [Group G] {Ω : Set (Subgroup G)} {A : Subgroup G}
  {S : Set (Subgroup G)}

theorem dataFinset_card_three_or_six [Finite ↥A] [IsMulCommutative ↥A] (Fr : RankFrame F Ω A S)
    (hcard : Nat.card A = 8) (hS : S.Nonempty) (hA2 : A2Dichotomy A S) (hfib : FibreLE2 S)
    (hconn : NonCommConnected S) {K L : Subgroup G} (hK : K ∈ S) (hL : L ∈ S) (hne : K ≠ L)
    (hnc : ¬ Commutes K L) : Fr.dataFinset.card = 3 ∨ Fr.dataFinset.card = 6 := by
  have hadj : (Fr.datum ⟨K, hK⟩).Adj (Fr.datum ⟨L, hL⟩) :=
    (Fr.datum_adj_iff_not_commutes hA2 hfib (fun h => hne (congrArg Subtype.val h))).mpr hnc
  rcases Fr.datum_classification_three hcard hS hA2 hfib hconn with h1 | ⟨h3, -⟩ | ⟨h6, -⟩
  · exfalso
    have h := Finset.card_le_one.mp h1.le
    have e : Fr.datum ⟨K, hK⟩ = Fr.datum ⟨L, hL⟩ :=
      h _ (Fr.mem_dataFinset.mpr ⟨_, rfl⟩) _ (Fr.mem_dataFinset.mpr ⟨_, rfl⟩)
    have h' := hadj.1
    rw [e, Datum.pair_self] at h'
    exact zero_ne_one h'
  · exact Or.inl h3
  · exact Or.inr h6

theorem eq_of_datumInjective [Finite ↥A] [IsMulCommutative ↥A] (Fr : RankFrame F Ω A S)
    (hinj : Fr.DatumInjective) :
    ∀ K ∈ S, ∀ L ∈ S, (∃ w, IsUniqueInvolution K w ∧ IsUniqueInvolution L w) →
      axisSub A K = axisSub A L → K = L := by
  rintro K hK L hL ⟨w, hwK, hwL⟩ hax
  have h1 : Fr.zOf ⟨K, hK⟩ = w := (Fr.isUniqueInvolution_zOf ⟨K, hK⟩).eq hwK
  have h2 : Fr.zOf ⟨L, hL⟩ = w := (Fr.isUniqueInvolution_zOf ⟨L, hL⟩).eq hwL
  have hd : Fr.datum ⟨K, hK⟩ = Fr.datum ⟨L, hL⟩ := by
    apply Datum.ext
    · have hz : (⟨Fr.zOf ⟨K, hK⟩, Fr.zOf_mem ⟨K, hK⟩⟩ : ↥A) =
          ⟨Fr.zOf ⟨L, hL⟩, Fr.zOf_mem ⟨L, hL⟩⟩ := Subtype.ext (h1.trans h2.symm)
      show Additive.ofMul (⟨Fr.zOf ⟨K, hK⟩, Fr.zOf_mem ⟨K, hK⟩⟩ : ↥A) =
        Additive.ofMul (⟨Fr.zOf ⟨L, hL⟩, Fr.zOf_mem ⟨L, hL⟩⟩ : ↥A)
      rw [hz]
    · ext x
      show axisChar A K ((Additive.toMul x : ↥A) : G) = axisChar A L ((Additive.toMul x : ↥A) : G)
      unfold axisChar
      rw [hax]
  exact congrArg Subtype.val (hinj _ _ hd)

end DatumFacts

end CFSG.ClassicalInvolution.ConnectedA2
