module

public import CFSG.ClassicalInvolution.RouteD.TypeF4Recognition
public import CFSG.ClassicalInvolution.RouteD.GapsLocal
public import CFSG.ClassicalInvolution.RouteD.TypeCLocal
public import CFSG.ClassicalInvolution.Balance.PassTwoConj

public section

namespace CFSG.ClassicalInvolution.RouteD

open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Models
open CFSG.ClassicalInvolution.Models.SymplecticPairs (SymplecticBlockStandardPair)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped MatrixGroups

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G]

theorem card_typeCTransport_eq {X X' : Type} [Group X] [Group X'] {Φ : Set (Subgroup X)}
    (e : X ≃* X') (D : LieSystemData p f X Φ) : (typeCTransport e D).card = D.card := rfl

theorem exists_lieSystem_card_le_conj {Ω : Set (Subgroup G)} (hΩ : ConjInvariant Ω) {z : G}
    {c : ℕ} (h : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ c) (g : G) :
    ∃ D : LieSystemData p f (locQuot Ω (g * z * g⁻¹)) (locFamily Ω (g * z * g⁻¹)), D.card ≤ c := by
  obtain ⟨D, hD⟩ := h
  have H : ∀ Φ' : Set (Subgroup (locQuot Ω (g * z * g⁻¹))),
      Φ' = Subgroup.map (locConj hΩ g z).toMonoidHom '' locFamily Ω z →
      ∃ D' : LieSystemData p f (locQuot Ω (g * z * g⁻¹)) Φ', D'.card ≤ c := by
    intro Φ' hΦ'
    subst hΦ'
    exact ⟨typeCTransport (locConj hΩ g z) D, (card_typeCTransport_eq _ D).le.trans hD⟩
  exact H _ (locFamily_conj hΩ g z)

theorem commutes_partner_of_perfect [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) {z : G} (hz : IsClassicalMember p f K z)
    (hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G}
    (hβ : β ∈ Ω) {t : G} (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) {S : Subgroup G} (hS : ⁅S, S⁆ = S)
    (hSt : S ≤ Subgroup.centralizer ({t} : Set G)) (hSK : S ≤ Subgroup.centralizer (K : Set G)) :
    Commutes β S := by
  have hf : 0 < f := by
    rcases Nat.eq_zero_or_pos f with rfl | h
    · simp at hq
    · exact h
  obtain ⟨g, hg⟩ := hsingle β hβ
  have hzg : IsClassicalMember p f β (g * z * g⁻¹) := by
    rw [hg]
    exact hz.conj g
  have htg : t = g * z * g⁻¹ :=
    (hzg.eq_of_isCentralInvolution hp2 hf ht.isCentralInvolution)
  have hP1t : LocalOddCentral Ω {t} :=
    CFSG.ClassicalInvolution.Balance.localOddCentral_of_classicalMember hp2 hf hΩ ⟨K, hK, hsingle⟩
      hK hz hP1 β hβ t ht
  have hD4t : ∃ D : LieSystemData p f (locQuot Ω t) (locFamily Ω t), D.card ≤ 4 :=
    htg ▸ exists_lieSystem_card_le_conj hΩ.conjInvariant hD4 g
  obtain ⟨Dt, hcard⟩ := hD4t
  obtain ⟨W, hW⟩ := hKβ
  have := Gaps.perfect_le_centralizer_of_partner hMFZ hS3 hΩ hP1t Dt hcard hβ ht hW hS hSt hSK
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (this hy) x hx)

theorem routeD_typeF4 [Finite G] (hp2 : p ≠ 2) (hq : 5 ≤ p ^ f)
    (hMFZ : Gaps.FundNoncentral p) (hS3 : Gaps.StandardPairAutAbelian (GaloisField p f))
    {Ω : Set (Subgroup G)} (hΩ : InClass p f Ω) {K : Subgroup G} (hK : K ∈ Ω)
    (hsingle : ∀ L ∈ Ω, ∃ g : G, L = conjSub g K) (hconn : DeltaConnected Ω) {z : G}
    (hz : IsClassicalMember p f K z) (hshape : LocalShapeC p f 3 Ω z)
    (hP1 : LocalOddCentral Ω {z}) {β : Subgroup G} (hβ : β ∈ Ω) {t : G}
    (ht : IsClassicalMember p f β t)
    (hKβ : ∃ W, LinearBlockStandardPair (GaloisField p f) W K β) (j : Fin 3 → Subgroup G)
    (hjK : ∀ i, Commutes K (j i)) (hj₁ : ⁅j 1, j 1⁆ = j 1)
    (hj₂ : ⁅j 2, j 2⁆ = j 2) (hjt₁ : j 1 ≤ Subgroup.centralizer ({t} : Set G))
    (hjt₂ : j 2 ≤ Subgroup.centralizer ({t} : Set G)) (hj₀₂ : Commutes (j 0) (j 2))
    (hj₁₂ : ∃ W, LinearBlockStandardPair (GaloisField p f) W (j 1) (j 2))
    (hj₀₁ : ∃ W, SymplecticBlockStandardPair (GaloisField p f) W (j 0) (j 1))
    (hβj₀ : ∃ W, LinearBlockStandardPair (GaloisField p f) W β (j 0)) :
    ∃ D : LieSystemData p f G Ω, D.card = 1 ∧ ∃ i, D.tag i = .F4 := by
  have hD4 : ∃ D : LieSystemData p f (locQuot Ω z) (locFamily Ω z), D.card ≤ 4 := by
    obtain ⟨D, hcard, -⟩ := hshape
    exact ⟨D, by omega⟩
  have hβ1 : Commutes β (j 1) :=
    commutes_partner_of_perfect hp2 hq hMFZ hS3 hΩ hK hsingle hz hD4 hP1 hβ ht hKβ hj₁ hjt₁
      (fun y hy x hx => hjK 1 x hx y hy)
  have hβ2 : Commutes β (j 2) :=
    commutes_partner_of_perfect hp2 hq hMFZ hS3 hΩ hK hsingle hz hD4 hP1 hβ ht hKβ hj₂ hjt₂
      (fun y hy x hx => hjK 2 x hx y hy)
  refine routeD_typeF4_of_chain hp2 hq hΩ hK hsingle hconn hz hshape hP1 ![β, j 0, j 1, j 2]
    hβ ?_ ?_ ?_
  · intro i k hik a ha b hb
    fin_cases i <;> fin_cases k <;> first | (exfalso; revert hik; simp; done) | skip
    · exact hβ1 a ha b hb
    · exact hβ2 a ha b hb
    · exact hj₀₂ a ha b hb
  · intro i k hik hi1
    fin_cases i <;> fin_cases k <;> first | (exfalso; revert hik; simp; done) | skip
    · exact hβj₀
    · exact (hi1 rfl).elim
    · exact hj₁₂
  · exact hj₀₁

end CFSG.ClassicalInvolution.RouteD
