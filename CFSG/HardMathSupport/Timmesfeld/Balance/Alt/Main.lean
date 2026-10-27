module

public import CFSG.HardMathSupport.Timmesfeld.Coordinator.LocalThreeDefs
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Assembly
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Upper
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Lower
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Construct
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutTransfer
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.AutSix
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
public import CFSG.HardMathSupport.Timmesfeld.Coordinator.Input19DeltaReduction

public section

namespace CFSG.HardMathSupport.Timmesfeld.Balance.Alt

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.Coordinator CFSG.HardMathSupport.Timmesfeld.Coordinator

theorem localThreeBalanceAlt_proved : LocalThreeBalanceAlt := by
  intro G _ _ _ p hp hp2 X _ B hBX hB hrank _ L hL n hn
  obtain ⟨e⟩ := hn
  intro D hD H hH _
  by_contra hΔ
  obtain ⟨hDA, hDe, hD3⟩ := hD
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hperf : Group.IsPerfect (barOf p L) := isPerfect_barOf hL
  have hAe := isElemAbelian_autBar hB L
  have hDne : D ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hD3
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  by_cases hn4 : n ≤ 4
  · have h1 : Group.IsSolvable (alternatingGroup (Fin n)) :=
      alternatingGroup.isSolvable (by simpa using hn4)
    have h2 : Group.IsSolvable (barOf p L ⧸ Subgroup.center (barOf p L)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    have h3 : Group.IsSolvable (barOf p L) :=
      Group.isSolvable_of_subgroup_quotient (Subgroup.center _)
    have h4 : Subsingleton (barOf p L) := by
      by_contra h
      rw [not_subsingleton_iff_nontrivial] at h
      exact Group.IsPerfect.not_isSolvable (barOf p L) h3
    have h5 : Subsingleton (MulAut (barOf p L)) :=
      ⟨fun a b => MulEquiv.ext fun x => Subsingleton.elim _ _⟩
    have h6 : Subsingleton D := ⟨fun a b => Subtype.ext (Subsingleton.elim _ _)⟩
    have := Finite.card_le_one_iff_subsingleton.2 h6
    have : 1 < p ^ 3 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  by_cases hn6 : n = 6
  · subst hn6
    let φ : MulAut (barOf p L) →* MulAut (alternatingGroup (Fin 6)) :=
      (MulAut.congr e).toMonoidHom.comp (autCenterQuot (barOf p L))
    have hφ : Function.Injective φ :=
      (MulAut.congr e).injective.comp (autCenterQuot_injective _)
    refine no_elemAbelian_cube_mulAut_alternating_six hp hp2 (D.map φ) ⟨?_, ?_, ?_⟩
    · exact isMulCommutative_map φ D hDe.1
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow, hDe.2 x hx, map_one]
    · rw [Subgroup.card_map_of_injective hφ]; exact hD3
  have hn5 : 5 ≤ n := by omega
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6
  obtain ⟨ι, hιinj, hιinner⟩ := exists_embedding_perm e hbij
  obtain ⟨hpn, β, hβ, hβn⟩ := upper_bound_of_delta hp hp2 ι hιinj (innerAut (barOf p L))
    hιinner (autBar p B L) D H hDA hAe hDe hD3 hH hΔ
  have hp27 : 27 ≤ p ^ 3 :=
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ p ^ 3 := Nat.pow_le_pow_left hp3 3
  have hn8 : 8 ≤ n := by omega
  have hZ0 : Subgroup.center (barOf p L) = ⊥ :=
    center_eq_bot_of_odd hn8 e (odd_card_center_barOf hp hp2 L)
  have hZ : ∀ x : barOf p L, (∀ y, x * y = y * x) → x = 1 := by
    intro x hx
    have : x ∈ Subgroup.center (barOf p L) := Subgroup.mem_center_iff.2 fun g => (hx g).symm
    rw [hZ0] at this
    exact this
  let η : barOf p L →* alternatingGroup (Fin n) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (barOf p L)))
  have hηinj : Function.Injective η := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : QuotientGroup.mk' (Subgroup.center (barOf p L)) x = 1 := by
      apply e.injective
      rw [map_one]; exact hx
    have h2 : x ∈ Subgroup.center (barOf p L) := (QuotientGroup.eq_one_iff x).1 h1
    rw [hZ0] at h2
    exact h2
  have hηsurj : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ψ : barOf p L ≃* alternatingGroup (Fin n) := MulEquiv.ofBijective η ⟨hηinj, hηsurj⟩
  obtain ⟨E, T, hEc, hEe, hEcard, hT1, hT2, hET⟩ :=
    exists_elemAbelian_centralizing_two hp hp2 (show 4 ≤ n by omega)
  set q := (n - 4) / p with hq
  have hψinj := ψ.symm.injective
  obtain ⟨P, S, hPc, hPe, hPcard, hS, hS2, hPS⟩ := exists_twoLocal_lower hp hp2 hBX hB hL hZ
    (E.map ψ.symm.toMonoidHom) (T.map ψ.symm.toMonoidHom) q
    ⟨isMulCommutative_map _ E hEc, by rintro _ ⟨x, hx, rfl⟩; rw [← map_pow, hEe x hx, map_one],
      by rw [Subgroup.card_map_of_injective hψinj]; exact hEcard⟩
    ⟨fun h => hT1 ((Subgroup.map_eq_bot_iff_of_injective T hψinj).1 h), hT2.map _⟩
    (by
      rintro _ ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨t, ht, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 (hET hx) t ht
      rw [← map_mul, ← map_mul, this])
  have hpgB : IsPGroup p B := fun g => ⟨1, by
    rw [pow_one]; exact Subtype.ext (hB.2 _ g.2)⟩
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨m, hm⟩ : ∃ m, Nat.card B = p ^ m := IsPGroup.iff_card.1 hpgB
  have hCle : ∀ x, x ∈ centB p B L → x ∈ B := fun x hx => centB_le p B L hx
  have hpgC : IsPGroup p (centB p B L) := hpgB.to_le (centB_le p B L)
  obtain ⟨γ, hγ⟩ : ∃ γ, Nat.card (centB p B L) = p ^ γ := IsPGroup.iff_card.1 hpgC
  have hcardB := card_B_eq p B L
  rw [hm, hβ, hγ] at hcardB
  have hdvd : (B ⊓ Subgroup.normalizer (L : Set G)).relIndex B ∣ p ^ m :=
    ⟨p ^ β * p ^ γ, hcardB.trans rfl⟩
  obtain ⟨a, ha⟩ := (Nat.dvd_prime_pow hp).1 hdvd |>.imp fun a h => h.2
  have hmaβγ : m = a + (β + γ) := by
    rw [ha, ← pow_add, ← pow_add] at hcardB
    exact Nat.pow_right_injective hp.two_le hcardB
  have hPcard' : Nat.card P = p ^ (γ + q * p ^ a) := by
    rw [hPcard, hγ, ha, ← pow_add]
  have hrkP : CFSG.Open.pRank p P = γ + q * p ^ a :=
    pRank_eq_of_card hp ⟨hPc, hPe⟩ hPcard'
  have hrkB : CFSG.Open.pRank p B = m := pRank_eq_of_card hp hB hm
  have h1 : CFSG.Open.pRank p P ≤ GLATwoLocalRank p ↥X :=
    pRank_le_glaTwoLocalRank_of_normalizes hp hS hS2 hPS
  have h2 : γ + q * p ^ a ≤ a + (β + γ) := by
    rw [← hrkP, ← hmaβγ, ← hrkB]
    exact h1.trans hrank
  exact arith_contra (a := a) hp3 hpn hβn hq (by omega)

end CFSG.HardMathSupport.Timmesfeld.Balance.Alt
