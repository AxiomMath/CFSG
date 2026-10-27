module

public import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.CentralCover.SteinbergBNCoverPairingCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank

open CFSG.RankThree.CentralCover CFSG.RankThree.Classical2

@[expose] def CentralCoverFour (L : Type*) [Group L] : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (φ : Y →* L), Function.Surjective φ →
    φ.ker ≤ Subgroup.center Y → ∃ U : Subgroup Y, Open.IsElemAbelian 3 U ∧ Nat.card U = 3 ^ 4

theorem CentralCoverFour.of_mulEquiv {L L' : Type*} [Group L] [Group L'] (e : L ≃* L')
    (h : CentralCoverFour L) : CentralCoverFour L' := by
  intro Y _ _ φ hφ hker
  refine h Y (e.symm.toMonoidHom.comp φ) (e.symm.surjective.comp hφ) fun y hy => hker ?_
  simpa using hy

theorem exists_elemAbelian_four_of_comm {Y L : Type*} [Group Y] [Finite Y] [Group L]
    (φ : Y →* L) (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    {D : Subgroup L} (hDp : ∀ x ∈ D, x ^ 3 = 1)
    (hF : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x) (hD : 3 ^ 4 ≤ Nat.card D) :
    ∃ U : Subgroup Y, Open.IsElemAbelian 3 U ∧ Nat.card U = 3 ^ 4 := by
  obtain ⟨V, -, hV, hcard, -⟩ := exists_elemAbelian_le_centralizer hφ hker Nat.prime_three
    (by norm_num) hDp hF hD (u := 1) (by simp) (fun x _ => by rw [map_one]; exact .one_left _)
  exact ⟨V, hV, hcard⟩

theorem centralCoverFour_of_inverters {L : Type*} [Group L] (h w : Fin 4 → L)
    (hcomm : ∀ i j, Commute (h i) (h j)) (hord : ∀ i, orderOf (h i) = 3)
    (hinv : ∀ i, w i * h i * (w i)⁻¹ = (h i)⁻¹)
    (hfix : ∀ i j, i ≠ j → w i * h j * (w i)⁻¹ = h j) : CentralCoverFour L := by
  intro Y _ _ φ hφ hker
  obtain ⟨hDab, hDcard, hF⟩ := inversion_basis_package hφ hker Nat.prime_three (by norm_num) h w
    hcomm hord hinv hfix
  exact exists_elemAbelian_four_of_comm φ hφ hker hDab.2 hF (by rw [hDcard, Fintype.card_fin])

theorem centralCoverFour_of_swaps {L : Type*} [Group L]
    (θ : Multiplicative (Fin 4 → ZMod 3) →* L) (hθ : Function.Injective θ)
    (g : Fin 4 → Fin 4 → L)
    (hg₁ : ∀ i j, i ≠ j → g i j * θ (Multiplicative.ofAdd (Pi.single i 1)) * (g i j)⁻¹ =
      θ (Multiplicative.ofAdd (Pi.single j 1)))
    (hg₂ : ∀ i j, i ≠ j → g i j * θ (Multiplicative.ofAdd (Pi.single j 1)) * (g i j)⁻¹ =
      θ (Multiplicative.ofAdd (Pi.single i 1))) : CentralCoverFour L := by
  intro Y _ _ φ hφ hker
  have hcomm : ∀ x y : Multiplicative (Fin 4 → ZMod 3), Commute (θ x) (θ y) := fun x y => by
    rw [Commute, SemiconjBy, ← map_mul, ← map_mul, mul_comm]
  have hpow : ∀ x : Multiplicative (Fin 4 → ZMod 3), θ x ^ 3 = 1 := fun x => by
    rw [← map_pow]
    have : x ^ 3 = 1 := by
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      have h3 : (3 : ZMod 3) = 0 := by decide
      simp [h3]
    rw [this, map_one]
  have hone : ∀ a a' : Multiplicative (Fin 4 → ZMod 3), liftComm φ hφ (θ a) (θ a') = 1 := by
    refine liftComm_eq_one_of_closure hφ hker θ
      (S := Set.range fun j : Fin 4 => Pi.single j (1 : ZMod 3)) closure_range_single_eq_top ?_
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    by_cases hij : i = j
    · subst hij
      exact liftComm_self hφ _
    · exact liftComm_eq_one_of_conj_swap hφ hker (p := 3) (by decide) (hcomm _ _) (hpow _)
        (g i j) (hg₁ i j hij) (hg₂ i j hij)
  refine exists_elemAbelian_four_of_comm φ hφ hker (D := θ.range) ?_ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    exact hpow x
  · exact fun x hx y hy => mul_comm_of_liftComm_eq_one hφ hker (U := θ.range)
      (fun s hs t ht => by
        obtain ⟨a, rfl⟩ := hs
        obtain ⟨b, rfl⟩ := ht
        exact hone a b) hx hy
  · rw [← Nat.card_congr (MonoidHom.ofInjective hθ).toEquiv, Nat.card_congr Multiplicative.toAdd]
    simp

theorem four_le_pRank_sylow_of_elemAbelian {K : Type} [Group K] [Finite K] {U : Subgroup K}
    (hU : Open.IsElemAbelian 3 U) (hcard : Nat.card U = 3 ^ 4) (T : Sylow 3 K) :
    4 ≤ Open.pRank 3 (T : Subgroup K) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hUp : IsPGroup 3 U := IsPGroup.of_card hcard
  obtain ⟨P, hP⟩ := hUp.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq K P T
  let c := (MulAut.conj g).toMonoidHom
  have hT : (T : Subgroup K) = (P : Subgroup K).map c := by
    rw [← hg, Sylow.coe_subgroup_smul]
    rfl
  refine SectionRank.le_pRank Nat.prime_three.one_lt (E := U.map c) ?_
    (SectionRank.isElemAbelian_map hU c) ?_
  · rw [hT]
    exact Subgroup.map_mono hP
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard]

theorem four_le_pRank_sylow_of_centralCoverFour {L : Type*} [Group L] (hL : CentralCoverFour L)
    {K : Type} [Group K] [Finite K] (e : K ⧸ Subgroup.center K ≃* L) (T : Sylow 3 K) :
    4 ≤ Open.pRank 3 (T : Subgroup K) := by
  obtain ⟨U, hU, hcard⟩ := hL K (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K)))
    (e.surjective.comp (QuotientGroup.mk'_surjective _)) (fun y hy => by simpa using hy)
  exact four_le_pRank_sylow_of_elemAbelian hU hcard T

end CFSG.LocalAnalysis.RankThreeTheoremC.ChevTwoInnerRank
