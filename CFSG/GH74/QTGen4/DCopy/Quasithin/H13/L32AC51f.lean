module

public import CFSG.GH74.QTGen4.DCopy.Quasithin.H13.L32ASk1
public import CFSG.Quasithin.H13.L32AC51e

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique
open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {G : Type} [Group G] [CFSG.GH74.QTGen4.Finite4 G] {T L V H : Subgroup G}

theorem preimG_adj_le_F4 (h11 : Lemma14_7_11_F4) (S : Setting147 G T L V H) {n : ℕ}
    {ψ : ↥H →* Lin.SLn n} (hψ : Function.Surjective ψ) (hker : ψ.ker = CFSG.Open.pCore 2 ↥H)
    {i : ℕ} (hi : 1 ≤ i) (hin : i + 2 ≤ n)
    (hLT : L32A.l1 T L V ⊔ T ≤ preimG ψ (Lin.par2 n i (i + 1))) :
    preimG ψ (Lin.par2 n i (i + 1)) ≤ Subgroup.normalizer (L : Set G) := by
  by_contra hM
  have hO2 : pCoreOf 2 (preimG ψ (Lin.par2 n i (i + 1))) ≠ ⊥ := by
    intro hbot
    apply S.hz.1.2
    rw [eq_bot_iff, ← hbot]
    exact (le_inf le_rfl (pCoreOf_le_preimG hker _)).trans
      (pCoreOf_inf_le_of_le (preimG_le ψ (Lin.par2 n i (i + 1))))
  have S' : Setting147 G T L V (preimG ψ (Lin.par2 n i (i + 1))) :=
    ⟨S.hyp, ⟨⟨hLT, hO2⟩, (preimG_le ψ _).trans S.hz.2.1, hM⟩⟩
  exact (h11 _ T L V _ S').1 (quotIso_preimG_blk3 hψ hker hi hin)

theorem false_of_inner_F4 (h11 : Lemma14_7_11_F4) (h29 : Thm14_7_29_F4) (S : Setting147 G T L V H)
    {n : ℕ} (hn : 3 ≤ n) {ψ : ↥H →* Lin.SLn n} (hψ : Function.Surjective ψ)
    (hker : ψ.ker = CFSG.Open.pCore 2 ↥H) {i₀ : ℕ} (hi₀ : 1 ≤ i₀) (hi₀n : i₀ < n)
    (hLT : L32A.l1 T L V ⊔ T ≤ preimG ψ (Lin.par n i₀)) : False := by

  have hj : ∀ j, 1 ≤ j → j < n → j ≠ i₀ →
      preimG ψ (Lin.par2 n i₀ j) ≤ Subgroup.normalizer (L : Set G) := by
    intro j hj hjn hji
    have hLTj : L32A.l1 T L V ⊔ T ≤ preimG ψ (Lin.par2 n i₀ j) :=
      hLT.trans (preimG_mono ψ (Lin.par_le_par2 i₀ j))
    rcases (by omega : j = i₀ + 1 ∨ i₀ = j + 1 ∨ (i₀ + 2 ≤ j ∨ j + 2 ≤ i₀)) with h | h | hfar
    · subst h
      exact preimG_adj_le_F4 h11 S hψ hker hi₀ (by omega) hLTj
    · subst h
      have e : Lin.par2 n (j + 1) j = Lin.par2 n j (j + 1) := by
        rw [Lin.par2, Lin.par2, Set.pair_comm]
      rw [e] at hLTj ⊢
      exact preimG_adj_le_F4 h11 S hψ hker hj (by omega) hLTj
    · exact h29 G T L V S.hyp _ hLTj ((preimG_le ψ _).trans S.hz.2.1)
        (isSolvable_preimG hker _ (Lin.isSolvable_par2 (by omega) hfar))

  set Y := ((H ⊓ Subgroup.normalizer (L : Set G)).subgroupOf H).map ψ with hY
  have hXY : ∀ j, 1 ≤ j → j < n → j ≠ i₀ → Lin.par2 n i₀ j ≤ Y := by
    intro j hj' hjn hji x hx
    obtain ⟨h, rfl⟩ := hψ x
    exact ⟨h, Subgroup.mem_subgroupOf.mpr ⟨h.2, hj j hj' hjn hji (mem_preimG.mpr ⟨h.2, hx⟩)⟩,
      rfl⟩
  obtain ⟨j₀, hj₀, hj₀n, hj₀i⟩ : ∃ j, 1 ≤ j ∧ j < n ∧ j ≠ i₀ := by
    rcases (by omega : i₀ = 1 ∨ 2 ≤ i₀) with h | h
    · exact ⟨2, by omega, by omega, by omega⟩
    · exact ⟨1, le_rfl, by omega, by omega⟩

  have hYtop : Y = ⊤ := by
    refine Lin.eq_top_of_refl ?_ fun j hj' hjn => ?_
    · exact (BinaryParabolic.unitriangular_le_flagStabilizer _).trans (hXY j₀ hj₀ hj₀n hj₀i)
    · by_cases hji : j = i₀
      · subst hji
        exact hXY j₀ hj₀ hj₀n hj₀i (Lin.par_le_par2 j j₀
          (BinaryParabolic.reflection_mem_parabolic hj' hjn))
      · exact hXY j hj' hjn hji (Lin.refl_mem_par2 i₀ hj' hjn)

  apply S.hz.2.2
  intro h hh
  have hY' : ψ ⟨h, hh⟩ ∈ Y := hYtop ▸ Subgroup.mem_top _
  obtain ⟨m, hm', hme⟩ := hY'
  have hm := Subgroup.mem_subgroupOf.mp hm'
  have hk : (⟨h, hh⟩ : ↥H) * m⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hme, mul_inv_cancel]
  rw [hker] at hk
  have hkM : (((⟨h, hh⟩ : ↥H) * m⁻¹ : ↥H) : G) ∈ Subgroup.normalizer (L : Set G) :=
    hj j₀ hj₀ hj₀n hj₀i (pCoreOf_le_preimG hker _ ⟨_, hk, rfl⟩)
  have := Subgroup.mul_mem _ hkM hm.2
  simpa using this

end CFSG.Quasithin.H13.L32A.C
