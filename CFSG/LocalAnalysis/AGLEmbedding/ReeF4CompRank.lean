module

public import CFSG.LocalAnalysis.AGLEmbedding.ReeF4Defs
public import CFSG.LocalAnalysis.AGLEmbedding.ComponentRank
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBSAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Index

variable {G : Type} [Group G] [Finite G]

theorem relIndex_le_of_forall_fin {B Y₁ : Subgroup G} (n : ℕ)
    (h : ∀ g : Fin (n + 1) → B, ∃ i j, i ≠ j ∧ ((g i)⁻¹ * g j : B) ∈ Y₁.subgroupOf B) :
    Y₁.relIndex B ≤ n := by
  by_contra hlt
  push Not at hlt
  set Q := B ⧸ Y₁.subgroupOf B
  have hcard : n + 1 ≤ Nat.card Q := by
    rw [Subgroup.relIndex, Subgroup.index] at hlt
    exact hlt
  have : Finite Q := inferInstance
  obtain ⟨e⟩ : Nonempty (Q ≃ Fin (Nat.card Q)) := ⟨Finite.equivFin Q⟩
  let g : Fin (n + 1) → B := fun j => Quotient.out (e.symm (Fin.castLE hcard j))
  obtain ⟨i, j, hij, hY⟩ := h g
  apply hij
  have h1 : (QuotientGroup.mk (g i) : Q) = QuotientGroup.mk (g j) :=
    QuotientGroup.eq.mpr hY
  have h2 : e.symm (Fin.castLE hcard i) = e.symm (Fin.castLE hcard j) := by
    have hi : (QuotientGroup.mk (g i) : Q) = e.symm (Fin.castLE hcard i) := Quotient.out_eq _
    have hj : (QuotientGroup.mk (g j) : Q) = e.symm (Fin.castLE hcard j) := Quotient.out_eq _
    rw [← hi, ← hj, h1]
  exact Fin.castLE_injective hcard (e.symm.injective h2)

end Index

end CFSG.AGLEmbedding

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.PreuniquenessRankFour.Helpers
open CFSG.RankThreeCoreUniqueness.Helpers

section Orbit

variable {G : Type} [Group G] [Finite G]

theorem le_pRank_of_injective_conj' (hRank : StmtComponentRank) (hLift : StmtBarPRankLift)
    {M A : Subgroup G} (hAM : A ≤ M) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)} (hLb : IsComponentOf Lb ⊤)
    {y l : ↥M ⧸ CFSG.pCore 2 ↥M} (hyA : y ∈ barM M A) (hyL : y ∈ Lb)
    (hyq : IsPGroup q (Subgroup.zpowers y))
    (hlL : l ∈ Lb) (hyl : y * l ≠ l * y) {m : ℕ} (g : Fin m → ↥M ⧸ CFSG.pCore 2 ↥M)
    (hg : ∀ j, g j ∈ barM M A)
    (hinj : Function.Injective fun j => Lb.map (MulAut.conj (g j)).toMonoidHom) :
    m ≤ Open.pRank q A := by
  have h1 := hRank hq (fun j => Lb.map (MulAut.conj (g j)).toMonoidHom)
    (fun j => (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (g j))
      Lb).mpr hLb) hinj (barM M A) (fun j => g j * y * (g j)⁻¹)
    (fun j => (barM M A).mul_mem ((barM M A).mul_mem (hg j) hyA) ((barM M A).inv_mem (hg j)))
    (fun j => ⟨y, hyL, rfl⟩)
    (fun j => by
      obtain ⟨k, hk⟩ := hyq ⟨y, Subgroup.mem_zpowers y⟩
      have hk' : y ^ q ^ k = 1 := by simpa using congrArg Subtype.val hk
      exact isPGroup_zpowers_of_pow_eq_one (by rw [conj_pow, hk']; group))
    (fun j => ⟨g j * l * (g j)⁻¹, ⟨l, hlL, rfl⟩, fun he => hyl (by
      have := congrArg (fun z => (g j)⁻¹ * z * g j) he
      simpa [mul_assoc] using this)⟩)
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at h1
  exact h1.trans (hLift hq hq2 M A hAM)

theorem D1ReeF4Data.pRank_three_le {P : Sylow 5 G} {M H R X : Subgroup G}
    (h : D1ReeF4Data P M H R X) (hind : ∀ q ∈ GLBBetaFour G, q < 5 → D1At G q) :
    Open.pRank 3 (H ⊓ M) ≤ 3 := by
  by_contra h4
  push Not at h4
  have h3 := h.surv.ph3
  have hβ : 3 ∈ GLBBetaFour G := mem_glbBetaFour_of_le_pRank (A := H ⊓ M) Nat.prime_three
    (by norm_num) h3.maxTwoLocal_M.1 inf_le_right (by omega)
  have h3' : 3 ≤ Open.pRank 3 (H ⊓ M) := by omega
  exact false_of_guestPrime h3.glob.pre hβ (hind 3 hβ (by norm_num)) h3.maxTwoLocal_M
    h3.maxTwoLocal_H h3.not_le h3'

end Orbit

end CFSG.AGLEmbedding
