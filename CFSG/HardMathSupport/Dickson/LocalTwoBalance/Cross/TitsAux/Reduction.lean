module

public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Basic
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.Families

public section

namespace CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux

open CFSG.Open CFSG.HardMathSupport.Solomon.LocalBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.CrossChar

theorem isLocallyBalancedAbs_two_of_inner_faithful {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hinj : Function.Injective (MulAut.conj : K →* MulAut K))
    (hinner : ∀ D : Subgroup (MulAut K), IsElemAbelian p D → Nat.card D = p ^ 2 →
      D ≤ (MulAut.conj : K →* MulAut K).range)
    (hfaith : ∀ P : Subgroup K, IsElemAbelian p P → Nat.card P = p ^ 2 →
      ∀ g : MulAut K, Nat.Coprime p (orderOf g) → (∀ x ∈ P, g x = x) → g = 1) :
    IsLocallyBalancedAbs p 2 K := by
  intro D hD hcard _ _ _
  have hDin : D ≤ (MulAut.conj : K →* MulAut K).range := hinner D hD hcard
  set P : Subgroup K := D.comap (MulAut.conj : K →* MulAut K) with hP
  have hPD : P.map (MulAut.conj : K →* MulAut K) = D := Subgroup.map_comap_eq_self hDin
  have hPcard : Nat.card P = p ^ 2 := by
    have h1 : Nat.card (P.map (MulAut.conj : K →* MulAut K)) = Nat.card P :=
      Subgroup.card_map_of_injective hinj
    rw [hPD, hcard] at h1
    exact h1.symm
  have hPe : IsElemAbelian p P := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
    · apply Subtype.ext
      apply hinj
      have := congrArg Subtype.val
        (hD.1.is_comm.comm ⟨MulAut.conj a.1, a.2⟩ ⟨MulAut.conj b.1, b.2⟩)
      simpa using this
    · apply hinj
      rw [map_pow, hD.2 _ hx, map_one]
  have hne : ∃ d ∈ D, d ≠ 1 := by
    by_contra hall
    push Not at hall
    have : D = ⊥ := (Subgroup.eq_bot_iff_forall D).2 hall
    rw [this, Subgroup.card_bot] at hcard
    have h1 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  obtain ⟨d, hdD, hd1⟩ := hne
  refine eq_bot_iff.2 fun g hg => ?_
  rw [Subgroup.mem_bot]
  refine hfaith P hPe hPcard g (coprime_orderOf_of_mem_localDeltaIn hp hg hdD hd1) fun x hx => ?_
  exact mem_fixSub.1 (mem_fixSub_of_commute hinj
    (commute_of_mem_localDeltaIn hg (show MulAut.conj x ∈ D from hx)))

theorem faithful_of_forall_normalizer {K : Type*} [Group K] {p : ℕ} (hp : p.Prime)
    {P : Subgroup K}
    (h : ∀ Y : Subgroup (MulAut K), ¬ p ∣ Nat.card Y →
      P.map (MulAut.conj : K →* MulAut K) ≤ Subgroup.normalizer (Y : Set (MulAut K)) → Y = ⊥)
    (g : MulAut K) (hg : Nat.Coprime p (orderOf g)) (hfix : ∀ x ∈ P, g x = x) : g = 1 := by
  have hY : Subgroup.zpowers g = ⊥ := by
    refine h _ ?_ ?_
    · rw [Nat.card_zpowers]
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hg
    · rintro _ ⟨x, hx, rfl⟩
      have hcomm : g * MulAut.conj x = MulAut.conj x * g := by
        have := mul_conj_mul_inv g x
        rw [hfix x hx, mul_inv_eq_iff_eq_mul] at this
        exact this
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
      exact (Commute.zpow_left (show Commute g (MulAut.conj x) from hcomm) k).eq
  exact Subgroup.zpowers_eq_bot.1 hY

end CFSG.HardMathSupport.Dickson.LocalTwoBalance.Cross.TitsAux
