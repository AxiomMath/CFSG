module

public import CFSG.ClassicalInvolution.Phan.Coherent

public section

namespace CFSG.ClassicalInvolution.Phan

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank

theorem weakPhan_of_phanUniversal (hU : PhanUniversal) (K : Type) [Field K] [Finite K]
    (p f : ℕ) [Fact p.Prime] [CharP K p] (hK : Nat.card K = (p ^ f) ^ 2) (hq : 5 ≤ p ^ f)
    {n : ℕ} (hn : 3 ≤ n) {X : Type} [Group X] {U : Fin n → Subgroup X}
    {W : Fin n → Fin n → Subgroup X} (hW : WeakPhanA K p f n U W) :
    ∃ θ : Su K p f (n + 1) →* X, Function.Surjective θ ∧
      θ.ker ≤ Subgroup.center (Su K p f (n + 1)) := by
  obtain ⟨F, hFι, hFinj, -⟩ := coherent_family hK (by omega) hW
  obtain ⟨ψ, hψ2, -⟩ := hU K p f hK hq hn F
  have hsurj : Function.Surjective ψ := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hW.gen]
    refine iSup_le fun i => ?_
    rw [← hFι i, ← hψ2 i, MonoidHom.range_comp]
    exact Subgroup.map_le_range _ _
  have hquasi : IsQuasisimple (Su K p f (n + 1)) := by
    have h := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hK
      (n := n + 1) (by omega) (by
        intro h
        have : n + 1 = 3 := (Prod.mk.inj h).1
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
      rw [← Nat.card_congr (conjEquiv P hP).toEquiv,
        CFSG.LieType.Steinberg.card_SU_two hK]
      have h24 : 24 ≤ (p ^ f) ^ 2 - 1 := by
        have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
        omega
      nlinarith
    omega
  exact ⟨ψ, hsurj, ker_le_center_of_isQuasisimple hquasi hnontriv⟩

end CFSG.ClassicalInvolution.Phan
