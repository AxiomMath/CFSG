module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Sp4Cent
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3B57N
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3BDefs
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LSp
public import CFSG.RankThree.Classical.SteinbergBJOddSymplecticOuterOrder

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open Matrix CFSG Subgroup CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl (statedSp_ext)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.Burgoyne.Sp (lrInv)
open scoped MatrixGroups

namespace P58b3

theorem oddAutInner_of_sp_three {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X) {r : ℕ}
    (hr : 2 ≤ r) (hm : Blueprint.LieModel (X ⧸ center X) .PSp r 3 1) : OddAutInner X := by
  intro α k hk hα
  have : Group.IsPerfect X := hX.1
  rcases hm with ⟨-, hcl⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩ | ⟨-, htag, -⟩
  rotate_left
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  · exact absurd htag (by decide)
  obtain ⟨-, F, _, _, hFc, ⟨θ⟩⟩ := hcl
  have hidx : (inner (StatedProj (StatedSp r F))).index ∣ 2 := by
    have h := (RankThree.Classical.odd_symplectic_outer_order_divides_field_multiplier_bound
      Nat.prime_three (by norm_num) le_rfl hr hFc).1
    norm_num at h
    exact h
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (inner (StatedProj (StatedSp r F))).index = 2 ^ m := by
    rcases (Nat.dvd_prime Nat.prime_two).mp hidx with h | h
    · exact ⟨0, by rw [h, pow_zero]⟩
    · exact ⟨1, by rw [h, pow_one]⟩
  let Φ : MulAut X →* MulAut (StatedProj (StatedSp r F)) :=
    (MulAut.congr θ).toMonoidHom.comp (PerfectAutomorphisms.centerQuotientHom X)
  have hΦconj : ∀ x : X, Φ (MulAut.conj x) = MulAut.conj (θ (QuotientGroup.mk' (center X) x)) :=
    fun x => by
      change MulAut.congr θ (PerfectAutomorphisms.onCenterQuotient (MulAut.conj x)) = _
      rw [onCenterQuotient_conj, OuterAutomorphisms.congr_conj]
  have hconjΦ : ∀ y, ∃ x : X, MulAut.conj y = Φ (MulAut.conj x) := fun y => by
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (center X) (θ.symm y)
    exact ⟨x, by rw [hΦconj, hx, MulEquiv.apply_symm_apply]⟩
  have hΦ : Function.Injective Φ :=
    (MulAut.congr θ).injective.comp (PerfectAutomorphisms.centerQuotientHom_injective X)
  have hI : (inner (StatedProj (StatedSp r F))).comap Φ =
      (MulAut.conj : X →* MulAut X).range := by
    ext β
    rw [mem_comap]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨x, hx⟩ := hconjΦ y
      exact ⟨x, hΦ (hx.symm.trans hy)⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, (hΦconj x).symm⟩
  rw [← hI] at hα ⊢
  rw [mem_comap, map_pow] at hα
  exact mem_of_pow_mem_of_index_eq_two_pow hm hk hα

theorem harris82Lemma58bThreeRowAt_PSp_two : Harris82Lemma58bThreeRowAt .PSp 2 1 := by
  intro G _ _ z₁ z₂ hz₁ hz₂ _ _ L₁ _ K hL₁ _ hz₁L _ _ hKc hO₁ _ hN hz₂K hz₂Z hm
  exfalso
  have hz₁K : z₁ ∈ K := hO₁ (F3.mem_oPrimeResidualOf hz₁L hz₁)
  obtain ⟨hX, hO, hmX, -⟩ := setting_facts hz₁ hz₂ hz₁L hKc hO₁ hz₂K hz₂Z hm
  have hQ := lemma57_fourGroup_map_of_aut hz₂ hL₁ hKc.1 hO₁ hN hz₂K hz₁K
    (oddAutInner_of_sp_three hX le_rfl hmX)
  have hcQ : QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩ ∈
      ((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) :=
    ⟨⟨z₁, hz₁K⟩, mem_subgroupOf.mpr ⟨hz₁L, hz₁K⟩, rfl⟩
  obtain ⟨F, _, _, α, hF, hαi, hαs, hαc⟩ := P58b3L.exists_sp_iso hX hO hmX
    (P58b3L.mk_ne_one hz₁ hz₁K) (P58b3L.mk_mem_center hKc.1 hz₁K)
  obtain ⟨g, hg⟩ := hαs (QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₂, hz₂K⟩)
  have hgg : g * g = 1 := hαi (by rw [map_mul, hg, P58b3L.mk_mul_self hz₂ hz₂K, map_one])
  have hgs : ∀ c' : Fˣ,
      (g : GL (Fin 2 ⊕ Fin 2) F) ≠ GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c' := by
    intro c' hc'
    have hsc : ∀ Z : GL (Fin 2 ⊕ Fin 2) F,
        GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c' * Z =
          Z * GeneralLinearGroup.scalar (Fin 2 ⊕ Fin 2) c' := fun Z => by
      ext i j
      simp [GeneralLinearGroup.scalar, mul_comm]
    have hcen : α g ∈ center (↥K ⧸ pPrimeCore 2 ↥K) := by
      rw [mem_center_iff]
      intro x
      obtain ⟨y, rfl⟩ := hαs x
      rw [← map_mul, ← map_mul]
      congr 1
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hc']
      exact (hsc _).symm
    rw [hg] at hcen
    exact hz₂Z hcen
  obtain ⟨y₀, hy₀⟩ := hαs (QuotientGroup.mk' (pPrimeCore 2 ↥K) ⟨z₁, hz₁K⟩)
  have hy₀' : y₀ = lrInv F 0 * lrInv F 1 :=
    statedSp_ext ((hαc y₀ hy₀).trans (Burgoyne.B.lrInv_zero_mul_lrInv_one (K := F)).symm)
  have hQ' : IsSolvableTwoComponentIn
      (((L₁ ⊓ K).subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)))
      (centralizer {α g}) := by
    rw [hg]
    exact hQ
  exact false_of_sp4 hF α hαi hαs hgg hgs hQ' (by rw [← hy₀', hy₀]; exact hcQ)

end P58b3

end CFSG.ComponentClassification.HarrisLit.T1
