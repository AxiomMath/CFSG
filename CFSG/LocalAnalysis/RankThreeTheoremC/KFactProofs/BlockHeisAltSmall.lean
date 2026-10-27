module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockHeisCoreDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.BlockFactsGlue
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBXAlternatingThreeCycles
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
public import CFSG.HardMathSupport.Malle.E27Lie.Cross.Index
public import CFSG.GH74.KGroups.L27
public import CFSG.GH74.KGroups.U33
public import CFSG.GH74.KGH

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs

open Equiv Equiv.Perm

theorem exists_four_disjoint_threeCycles {n : ℕ} (hn : 12 ≤ n) :
    ∃ c : Fin 4 → alternatingGroup (Fin n), (∀ i, (c i : Perm (Fin n)).IsThreeCycle) ∧
      Pairwise fun i j => (c i : Perm (Fin n)).Disjoint (c j) := by
  classical
  let p : ℕ → Fin n := fun i => if h : i < n then ⟨i, h⟩ else ⟨0, by omega⟩
  have hp : ∀ i, i < n → (p i : ℕ) = i := fun i hi => by simp [p, hi]
  have hne : ∀ i j, i < 12 → j < 12 → i ≠ j → p i ≠ p j := by
    intro i j hi hj hij h
    have := congrArg (fun z : Fin n => (z : ℕ)) h
    simp only [hp i (by omega), hp j (by omega)] at this
    exact hij this
  let σ : Fin 4 → Perm (Fin n) := fun i =>
    swap (p (3 * i)) (p (3 * i + 1)) * swap (p (3 * i + 1)) (p (3 * i + 2))
  have hnd : ∀ l : Fin 4, [p (3 * l), p (3 * l + 1), p (3 * l + 2)].Nodup := fun l => by
    simp only [List.nodup_cons, List.mem_cons, List.mem_singleton, not_or, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    exact ⟨⟨hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega)⟩,
      hne _ _ (by omega) (by omega) (by omega)⟩
  have h3 : ∀ i : Fin 4, (σ i).IsThreeCycle := fun i => by
    refine card_support_eq_three_iff.1 ?_
    simp only [σ]
    rw [support_swap_mul_swap (hnd i)]
    exact Finset.card_eq_three.2 ⟨_, _, _, hne _ _ (by omega) (by omega) (by omega),
      hne _ _ (by omega) (by omega) (by omega), hne _ _ (by omega) (by omega) (by omega), rfl⟩
  refine ⟨fun i => ⟨σ i, (h3 i).mem_alternatingGroup⟩, h3, fun i j hij => ?_⟩
  have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
  dsimp only
  rw [disjoint_iff_disjoint_support]
  change Disjoint (σ i).support (σ j).support
  simp only [σ]
  rw [support_swap_mul_swap (hnd i), support_swap_mul_swap (hnd j), Finset.disjoint_left]
  intro v hv hv'
  simp only [Finset.mem_insert, Finset.mem_singleton] at hv hv'
  rcases hv with rfl | rfl | rfl <;> rcases hv' with h | h | h <;>
    exact hne _ _ (by omega) (by omega) (by omega) h

theorem le_eleven_of_oddRankLeThree {L : Type} [Group L] [Finite L] (hrank : OddRankLeThree L)
    {k : ℕ} (e : L ⧸ Subgroup.center L ≃* alternatingGroup (Fin k)) : k ≤ 11 := by
  by_contra hk
  push Not at hk
  let π : L →* alternatingGroup (Fin k) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hπ : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker ≤ Subgroup.center L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : QuotientGroup.mk' (Subgroup.center L) x = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff x).1 h1
  obtain ⟨c, hc, hdisj⟩ := exists_four_disjoint_threeCycles (n := k) (by omega)
  obtain ⟨-, ⟨V, hVel, hVcard, -⟩, -⟩ :=
    GorensteinLyons.alternating_central_cover_injective_disjoint_three_cycles.{0, 0} (k := 4)
      (by norm_num) (by omega) π hπ hker c hc hdisj
  have := hVel
  have hle := hrank 3 Nat.prime_three (by norm_num) V inferInstance
    (fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx)
  rw [hVcard] at hle
  norm_num at hle

theorem twelve_le_of_pow_three_dvd_factorial {p k : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (h : p ^ 3 ∣ k.factorial) : 12 ≤ k := by
  by_contra hk
  push Not at hk
  have h11 : p ^ 3 ∣ Nat.factorial 11 := h.trans (Nat.factorial_dvd_factorial (by omega))
  have hp11 : p ≤ 11 := (hp.dvd_factorial).1 ((dvd_pow_self p (by norm_num)).trans h11)
  rw [show Nat.factorial 11 = 39916800 by decide] at h11
  interval_cases p <;> revert hp h11 <;> decide

theorem not_pow_three_dvd_of_le {p m : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hm : m = 336 ∨ m = 1440 ∨ m = 12096) : ¬ p ^ 3 ∣ m := by
  intro h
  have hpos : 0 < m := by rcases hm with rfl | rfl | rfl <;> norm_num
  have hle : p ^ 3 ≤ 12096 :=
    (Nat.le_of_dvd hpos h).trans (by rcases hm with rfl | rfl | rfl <;> norm_num)
  have hp22 : p ≤ 22 := by
    by_contra hp'
    push Not at hp'
    have : 23 ^ 3 ≤ p ^ 3 := Nat.pow_le_pow_left hp' 3
    omega
  interval_cases p <;> rcases hm with rfl | rfl | rfl <;> revert hp h <;> decide

theorem noHeisAut_of_not_dvd {p : ℕ} {X : Type*} [Group X] [Finite (MulAut X)]
    (h : ¬ p ^ 3 ∣ Nat.card (MulAut X)) : NoHeisAut p X := by
  intro E hE _
  exact absurd (hE ▸ Subgroup.card_subgroup_dvd_card E) h

theorem heisCoreAlt_holds : HeisCoreAlt := by
  intro L _ _ _ hrank k hk5 e p hp hp5
  have hk11 := le_eleven_of_oddRankLeThree hrank e
  have hfin : Finite (MulAut (L ⧸ Subgroup.center L)) := inferInstance
  have hcard : Nat.card (MulAut (L ⧸ Subgroup.center L)) =
      Nat.card (MulAut (alternatingGroup (Fin k))) := Nat.card_congr (MulAut.congr e).toEquiv
  refine noHeisAut_of_not_dvd fun h => ?_
  rw [hcard] at h
  by_cases hk6 : k = 6
  · subst hk6
    rw [CFSG.QuasithinUnique.Setup.X3Aut.card_mulAut_alt6] at h
    exact not_pow_three_dvd_of_le hp hp5 (Or.inr (Or.inl rfl)) h
  · rw [card_mulAut_alternatingGroup_eq hk5 hk6] at h
    have := twelve_le_of_pow_three_dvd_factorial hp hp5 h
    omega

theorem heisCoreSmall_holds :
    HeisCoreSmall := by
  intro L _ _ _ d hd e p hp hp5
  rcases d with ⟨i, hi⟩
  rcases hd with ⟨q, hq, hiq⟩ | ⟨q, hq, hiq⟩
  ·
    simp only at hiq
    subst hiq
    have hqp : q.p = 7 ∧ q.exponent = 1 := by
      have h7 : q.p ^ q.exponent = 7 := by rw [← TauCeti.PrimePower.card_def]; exact hq
      have hpd : q.p ∣ 7 := h7 ▸ dvd_pow_self _ q.exponent_pos.ne'
      have hp7 : q.p = 7 := (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 hpd
      refine ⟨hp7, ?_⟩
      rw [hp7] at h7
      exact Nat.pow_eq_self_iff (by norm_num) |>.1 h7
    have hm := CFSG.HardMathSupport.Malle.E27Lie.statedClassicalModel_typeA' hi e
    rw [hqp.1, hqp.2] at hm
    obtain ⟨e₁⟩ := CFSG.GH74.KGroups.L27.equiv_of_stated hm
    refine noHeisAut_of_not_dvd (X := L ⧸ Subgroup.center L) ?_
    · rw [CFSG.GH74.KGroups.L27.card_mulAut e₁]
      exact not_pow_three_dvd_of_le hp hp5 (Or.inl rfl)
  ·
    simp only at hiq
    subst hiq
    have hqp : q.p = 3 ∧ q.exponent = 1 := by
      have h3 : q.p ^ q.exponent = 3 := by rw [← TauCeti.PrimePower.card_def]; exact hq
      have hpd : q.p ∣ 3 := h3 ▸ dvd_pow_self _ q.exponent_pos.ne'
      have hp3 : q.p = 3 := (Nat.prime_dvd_prime_iff_eq q.prime_p (by norm_num)).1 hpd
      refine ⟨hp3, ?_⟩
      rw [hp3] at h3
      exact Nat.pow_eq_self_iff (by norm_num) |>.1 h3
    have hm := CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA 2 q hi e
    rw [hqp.1, hqp.2] at hm
    obtain ⟨e₁⟩ := CFSG.GH74.KGroups.U33.equiv_of_lieModel
      (CFSG.GH74.lieModel_of_statedClassicalModel (by decide) hm)
    refine noHeisAut_of_not_dvd (X := L ⧸ Subgroup.center L) ?_
    · rw [CFSG.GH74.KGroups.U33.card_mulAut e₁]
      exact not_pow_three_dvd_of_le hp hp5 (Or.inr (Or.inr rfl))

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs
