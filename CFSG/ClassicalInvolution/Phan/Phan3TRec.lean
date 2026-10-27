module

public import CFSG.ClassicalInvolution.Phan.Phan3TPara
public import CFSG.ClassicalInvolution.Phan.Coherent

public section

namespace CFSG.ClassicalInvolution.Phan.Q3G

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime] [CharP K p]

theorem weakPhan3_recognition_of_extension (hK : Nat.card K = (p ^ f) ^ 2) (hq : p ^ f = 3)
    {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W)
    (hnorm : ∀ F : PhanFamily K p f X n, (∀ i, (F.ι i).range = U i) →
      (∀ i, Function.Injective (F.ι i)) →
      (∀ (i : Fin n) (h : (i : ℕ) + 1 < n), (F.θ i).range = W i ⟨i + 1, h⟩ ∧
        (F.θ i).ker ≤ Subgroup.center (Su K p f 3)) →
      ∀ (a : ℕ) (ha : a + 2 < n), ∃ Θ : Su K p f 4 →* X,
        ∀ k : Fin 3, Θ.comp (blockEmb2 K p f 3 k) = F.ι ⟨a + k, by omega⟩) :
    ∃ ψ : Su K p f (n + 1) →* X, Function.Surjective ψ ∧
      ψ.ker ≤ Subgroup.center (Su K p f (n + 1)) ∧
      ∀ i : Fin n, (blockEmb2 K p f n i).range.map ψ = U i := by
  have hq2 : p ^ f ≠ 2 := by omega
  obtain ⟨F, hFι, hFinj, hFθ⟩ := coherent_family hK (by omega) hW
  obtain ⟨ψ, hψ2, -⟩ := phanUniversalAt3_of_blocks hK hq F (hnorm F hFι hFinj hFθ)
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hW.gen]
    refine iSup_le fun i => ?_
    rw [← hFι i, ← hψ2 i, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hquasi : CFSG.IsQuasisimple (Su K p f (n + 1)) := by
    have h := (isQuasisimple_statedSU_of_card hK (n := n + 1) (by omega) (by
        intro h
        have : p ^ f = 2 := (Prod.mk.inj h).2
        omega)).1
    exact isQuasisimple_of_mulEquiv (MulEquiv.subgroupCongr (SUid_eq_statedSU hK (n + 1))).symm h
  have hnontriv : ∃ k, ψ k ≠ 1 := by
    obtain ⟨i⟩ : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    by_contra hall
    simp only [ne_eq, not_exists, not_not] at hall
    have hsub : Subsingleton (Su K p f 2) := by
      refine ⟨fun a b => hFinj i ?_⟩
      rw [← hψ2 i, MonoidHom.comp_apply, MonoidHom.comp_apply, hall, hall]
    have hcard : Nat.card (Su K p f 2) ≤ 1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have h1 : (1 : ℕ) < Nat.card (Su K p f 2) := by
      obtain ⟨P, hP⟩ := exists_wittMatrix hK 2
      rw [← Nat.card_congr (conjEquiv P hP).toEquiv, CFSG.LieType.Steinberg.card_SU_two hK, hq]
      norm_num
    omega
  refine ⟨ψ, hsurj, ker_le_center_of_isQuasisimple hquasi hnontriv, fun i => ?_⟩
  rw [← MonoidHom.range_comp, hψ2 i, hFι i]

end CFSG.ClassicalInvolution.Phan.Q3G
