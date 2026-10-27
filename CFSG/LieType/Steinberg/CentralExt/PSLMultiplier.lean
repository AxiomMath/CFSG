module

public import CFSG.LieType.Steinberg.CentralExt.SLThree
public import CFSG.LieType.Steinberg.CentralExt.PSL2Multiplier

public section

open Matrix
open scoped MatrixGroups

namespace CFSG.LieType.Steinberg.CentralExt.SLClosed

theorem card_rootsOfUnity_eq_gcd {k : Type} [Field k] [Fintype k] (n : ℕ) [NeZero n] :
    Nat.card (rootsOfUnity n k) = Nat.gcd n (Fintype.card k - 1) := by
  have hq1 : 0 < Fintype.card k - 1 := by
    have := Fintype.one_lt_card (α := k)
    omega
  have hd0 : 0 < Nat.gcd n (Fintype.card k - 1) := Nat.gcd_pos_of_pos_left _ (NeZero.pos n)
  have htop : rootsOfUnity (Fintype.card k - 1) k = ⊤ := by
    ext u
    simp only [mem_rootsOfUnity, Subgroup.mem_top, iff_true]
    exact Units.ext (by
      rw [Units.val_pow_eq_pow_val, Units.val_one, FiniteField.pow_card_sub_one_eq_one _ u.ne_zero])
  have heq : rootsOfUnity n k = rootsOfUnity (Nat.gcd n (Fintype.card k - 1)) k := by
    rw [← rootsOfUnity_inf_rootsOfUnity, htop, inf_top_eq]
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := kˣ)
  have hgprim : IsPrimitiveRoot g (Fintype.card k - 1) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units,
      Nat.card_eq_fintype_card]
  have hdvd : Nat.gcd n (Fintype.card k - 1) ∣ Fintype.card k - 1 := Nat.gcd_dvd_right _ _
  have hp : (Fintype.card k - 1) / Nat.gcd n (Fintype.card k - 1) ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hq1 hdvd) hd0).ne'
  have hprim := hgprim.pow_of_dvd hp (Nat.div_dvd_of_dvd hdvd)
  rw [Nat.div_div_self hdvd hq1.ne'] at hprim
  have : NeZero (Nat.gcd n (Fintype.card k - 1)) := ⟨hd0.ne'⟩
  rw [heq, hprim.card_rootsOfUnity']

theorem psl_hopfMultiplier_of_split {k : Type} [Field k] [Fintype k] {m : ℕ} (hm : 2 ≤ m)
    (hsplit : ∀ (E : Type) [Group E] (π : E →* SpecialLinearGroup (Fin (m + 1)) k),
      Function.Surjective π → π.ker ≤ Subgroup.center E →
        ∃ σ : SpecialLinearGroup (Fin (m + 1)) k →* E, ∀ g, π (σ g) = g) :
    commutator PSL(m + 1, k) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(m + 1, k) ≃*
        Multiplicative (ZMod (Nat.gcd (m + 1) (Fintype.card k - 1)))) := by
  set q : SpecialLinearGroup (Fin (m + 1)) k →* PSL(m + 1, k) :=
    QuotientGroup.mk' (Subgroup.center (SpecialLinearGroup (Fin (m + 1)) k))
  have hq : Function.Surjective q := QuotientGroup.mk'_surjective _
  have hker : q.ker = Subgroup.center (SpecialLinearGroup (Fin (m + 1)) k) :=
    QuotientGroup.ker_mk' _
  have : Group.IsPerfect (SpecialLinearGroup (Fin (m + 1)) k) :=
    LinearGroups.special_linear_isPerfect (by omega) (Or.inl (by omega))
  have hperf : Group.IsPerfect PSL(m + 1, k) := Group.IsPerfect.ofSurjective hq
  refine ⟨Group.IsPerfect.commutator_eq_top, ?_⟩
  obtain ⟨e⟩ := sl_hopfMultiplier_mulEquiv_ker_of_split hm hsplit q hq hker.le
  have hroots : rootsOfUnity (max (Fintype.card (Fin (m + 1))) 1) k = rootsOfUnity (m + 1) k := by
    simp
  let e2 : q.ker ≃* rootsOfUnity (m + 1) k :=
    (MulEquiv.subgroupCongr hker).trans ((SpecialLinearGroup.center_equiv_rootsOfUnity).trans
      (MulEquiv.subgroupCongr hroots))
  have hcyc : IsCyclic (rootsOfUnity (m + 1) k) := inferInstance
  rw [← card_rootsOfUnity_eq_gcd]
  exact ⟨(CFSG.RankThree.PerfectCover.hopfMultiplierEquivGriess _).trans
    (e.trans (e2.trans (zmodCyclicMulEquiv hcyc).symm))⟩

theorem psl_hopfMultiplier_of_separating {k : Type} [Field k] [Fintype k] {m : ℕ} (hm : 2 ≤ m)
    (hsep : Separating m k) :
    commutator PSL(m + 1, k) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(m + 1, k) ≃*
        Multiplicative (ZMod (Nat.gcd (m + 1) (Fintype.card k - 1)))) :=
  psl_hopfMultiplier_of_split hm fun _ _ _ hπ hcen =>
    sl_exists_section_of_separating hm hsep hπ hcen

theorem psl_hopfMultiplier_of_five_le {k : Type} [Field k] [Fintype k] {n : ℕ} (hn : 5 ≤ n) :
    commutator PSL(n, k) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, k) ≃*
        Multiplicative (ZMod (Nat.gcd n (Fintype.card k - 1)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  exact psl_hopfMultiplier_of_split (by omega)
    fun _ _ _ hπ hcen => sl_exists_section_of_four_le (by omega) hπ hcen

theorem psl_hopfMultiplier_of_three_le {k : Type} [Field k] [Fintype k] {n : ℕ} (hn : 3 ≤ n)
    (hk : 3 ≤ Fintype.card k) (h34 : ¬(n = 3 ∧ Fintype.card k = 4)) :
    commutator PSL(n, k) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, k) ≃*
        Multiplicative (ZMod (Nat.gcd n (Fintype.card k - 1)))) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [Fintype.card_eq_nat_card] at hk h34
  by_cases h43 : m = 3 ∧ Nat.card k = 3
  · exact psl_hopfMultiplier_of_split (by omega)
      fun _ _ _ hπ hcen => sl_exists_section_of_card_three (by omega) h43.2 hπ hcen
  exact psl_hopfMultiplier_of_separating (by omega)
    (separating_of_card (by omega) (by omega) (by omega) h43)

theorem psl_hopfMultiplier {k : Type} [Field k] [Fintype k] {n : ℕ} (hn : 3 ≤ n)
    (hk : 5 ≤ Fintype.card k) :
    commutator PSL(n, k) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, k) ≃*
        Multiplicative (ZMod (Nat.gcd n (Fintype.card k - 1)))) :=
  psl_hopfMultiplier_of_three_le hn (by omega) (by omega)

theorem griessPSLExceptional_eq_one {n q : ℕ} (h24 : ¬(n = 2 ∧ q = 4)) (h29 : ¬(n = 2 ∧ q = 9))
    (h32 : ¬(n = 3 ∧ q = 2)) (h34 : ¬(n = 3 ∧ q = 4)) (h42 : ¬(n = 4 ∧ q = 2)) :
    CFSG.Open.griessPSLExceptional n q = (1, 1) := by
  unfold CFSG.Open.griessPSLExceptional
  rw [ite_eq_right_iff.2 (fun h => absurd h (by omega)), ite_eq_right_iff.2
    (fun h => absurd h h29), ite_eq_right_iff.2 (fun h => absurd h h34)]

theorem griess_psl_generic
    (p f n : ℕ) [Fact p.Prime] (hf : 0 < f) (hn : 2 ≤ n)
    (hgen : (n = 2 ∧ 5 ≤ p ^ f ∧ p ^ f ≠ 9) ∨
      (3 ≤ n ∧ 3 ≤ p ^ f ∧ ¬(n = 3 ∧ p ^ f = 4)) ∨ 5 ≤ n) :
    commutator PSL(n, GaloisField p f) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, GaloisField p f) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f - 1)) ×
          ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).1 ×
            ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).2)) := by
  have : Fintype (GaloisField p f) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p f) = p ^ f := by
    rw [Fintype.card_eq_nat_card, GaloisField.card p f hf.ne']
  have hgen' : commutator PSL(n, GaloisField p f) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, GaloisField p f) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f - 1)))) := by
    rw [← hcard]
    rcases hgen with ⟨rfl, h5, h9⟩ | ⟨hn3, h3, h34⟩ | hn5
    · exact SL2Closed.psl_two_hopfMultiplier (by omega) (by omega)
    · exact psl_hopfMultiplier_of_three_le hn3 (by omega) (by omega)
    · exact psl_hopfMultiplier_of_five_le hn5
  refine ⟨hgen'.1, ?_⟩
  obtain ⟨e⟩ := hgen'.2
  rw [griessPSLExceptional_eq_one (by omega) (by omega) (by omega) (by omega) (by omega)]
  dsimp only
  let : Unique (ZMod 1 × ZMod 1) := Unique.mk' _
  exact ⟨e.trans (AddEquiv.toMultiplicative
    ((AddEquiv.prodUnique (M := ZMod (Nat.gcd n (p ^ f - 1))) (N := ZMod 1 × ZMod 1)).symm))⟩

theorem griess_psl_of_five_le
    (p f n : ℕ) [Fact p.Prime] (hf : 0 < f) (hn : 2 ≤ n)
    (hq : 5 ≤ p ^ f) (h9 : n = 2 → p ^ f ≠ 9) :
    commutator PSL(n, GaloisField p f) = ⊤ ∧
      Nonempty (CFSG.Open.griessHopfMultiplier PSL(n, GaloisField p f) ≃*
        Multiplicative (ZMod (Nat.gcd n (p ^ f - 1)) ×
          ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).1 ×
            ZMod (CFSG.Open.griessPSLExceptional n (p ^ f)).2)) :=
  griess_psl_generic p f n hf hn (by
    rcases (show n = 2 ∨ 3 ≤ n by omega) with rfl | hn3
    · exact Or.inl ⟨rfl, hq, h9 rfl⟩
    · exact Or.inr (Or.inl ⟨hn3, by omega, by omega⟩))

end CFSG.LieType.Steinberg.CentralExt.SLClosed
