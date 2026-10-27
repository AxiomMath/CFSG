module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ThompsonGenGL
public import CFSG.LocalAnalysis.PreuniquenessRankFour.BinaryUnits
public import CFSG.LocalAnalysis.PreuniquenessRankFour.MaximalAbelian

public section

namespace CFSG.GroupTheory

open scoped IsMulCommutative

theorem rank_le_of_jointly_injective_characters {k : ℕ} {A K : Type*} [Group A] [Finite A]
    [Field K] (χ : Fin k → (A →* Kˣ))
    (h : ∀ a : A, (∀ i, χ i a = 1) → a = 1) :
    Group.rank A ≤ k := by
  induction k generalizing A K with
  | zero =>
    have hsub : Subsingleton A := by
      refine ⟨fun a b => ?_⟩
      have ha : a = 1 := h a (fun i => i.elim0)
      have hb : b = 1 := h b (fun i => i.elim0)
      rw [ha, hb]
    haveI := hsub
    rw [Group.rank_eq_zero A]
  | succ k ih =>
    let B : Subgroup A := (χ 0).ker
    have hB : Group.rank B ≤ k := by
      refine ih (A := B) (K := K) (fun i : Fin k => (χ i.succ).comp B.subtype) ?_
      intro b hb
      apply Subtype.ext
      apply h (b : A)
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact MonoidHom.mem_ker.mp b.2
      · exact hb j
    have hQ : Group.rank (A ⧸ B) ≤ 1 := by
      haveI : Finite ↥(χ 0).range := Finite.of_surjective _ (χ 0).rangeRestrict_surjective
      haveI : IsCyclic (A ⧸ B) := by
        have hrange : IsCyclic ↥(χ 0).range := isCyclic_subgroup_units (χ 0).range
        exact (MulEquiv.isCyclic (QuotientGroup.quotientKerEquivRange (χ 0))).2 hrange
      exact CFSG.PreuniquenessRankFour.Helpers.cyclic_group_rank_at_most_one
    have hsub := CFSG.PreuniquenessRankFour.Helpers.subgroup_rank_le_rank_add_quotient_rank
      (source := A) B
    omega

theorem exists_normal_commutative_centralizer_le {P : Type*} [Group P] [Finite P]
    {p : ℕ} [Fact p.Prime] (hP : IsPGroup p P) :
    ∃ A : Subgroup P, A.Normal ∧ IsMulCommutative A ∧
      Subgroup.centralizer (A : Set P) ≤ A := by
  classical
  obtain ⟨A, -, hAn, hAc, hAmax⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.exists_maximal_normal_abelian_overgroup
      (source := P) (abelian := ⊥) (by infer_instance)
  haveI : A.Normal := hAn
  exact ⟨A, hAn, hAc,
    (CFSG.PreuniquenessRankFour.Helpers.maximal_normal_abelian_pSubgroup_centralizer_eq
      p hP A hAc hAmax).le⟩

theorem card_le_pow_pred_of_injective_perm {H : Type*} [Group H] [Finite H]
    {p k : ℕ} [Fact p.Prime] (hH : IsPGroup p H) (hk : 1 ≤ k)
    (f : H →* Equiv.Perm (Fin k)) (hf : Function.Injective f) :
    Nat.card H ≤ p ^ (k - 1) := by
  classical
  have hdvd : Nat.card H ∣ k.factorial := by
    have hcardrange : Nat.card f.range = Nat.card H :=
      (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm
    have h := f.range.card_subgroup_dvd_card
    rw [hcardrange, Nat.card_perm, Nat.card_fin] at h
    exact h
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  have hpdvd : p ^ n ∣ k.factorial := by simpa [hn] using hdvd
  have hne : k.factorial ≠ 0 := Nat.factorial_ne_zero k
  have hnle : n ≤ padicValNat p k.factorial :=
    (padicValNat_dvd_iff_le (p := p) (a := k.factorial) (n := n) hne).mp hpdvd
  have hklt : padicValNat p k.factorial < k :=
    padicValNat_factorial_lt_of_ne_zero p (by omega : k ≠ 0)
  have hnle' : n ≤ k - 1 := by omega
  calc Nat.card H = p ^ n := hn
    _ ≤ p ^ (k - 1) := Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle'

theorem rank_le_pred_of_injective_perm {H : Type*} [Group H] [Finite H]
    {p k : ℕ} [Fact p.Prime] (hH : IsPGroup p H) (hk : 1 ≤ k)
    (f : H →* Equiv.Perm (Fin k)) (hf : Function.Injective f) :
    Group.rank H ≤ k - 1 := by
  have hcard := card_le_pow_pred_of_injective_perm hH hk f hf
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.1 hH
  have ha_le : a ≤ k - 1 := by
    rw [ha] at hcard
    exact (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).1 hcard
  exact (CFSG.AGLEmbedding.ThompsonGen.rank_le_of_card_eq_pow hH ha).trans ha_le

end CFSG.GroupTheory

end
