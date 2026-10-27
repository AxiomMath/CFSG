module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

private lemma eq_univ_of_nonempty_of_forall_smul_mem {n : ℕ}
    (Q : Subgroup (Equiv.Perm (Fin n))) (T : Set (Fin n)) (hne : T.Nonempty)
    (hinv : ∀ q ∈ Q, ∀ x ∈ T, q • x ∈ T)
    (htrans : ∀ i j : Fin n, ∃ q ∈ Q, q i = j) : T = Set.univ := by
  ext y
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  obtain ⟨x, hx⟩ := hne
  obtain ⟨q, hq, hqx⟩ := htrans x y
  have h : q • x ∈ T := hinv q hq x hx
  rwa [show q • x = y by simpa using hqx] at h

private lemma smul_mem_fixedPoints_of_forall_conj_mem {n : ℕ}
    {Q N : Subgroup (Equiv.Perm (Fin n))}
    (hN : ∀ q ∈ Q, ∀ m ∈ N, q * m * q⁻¹ ∈ N) {q : Equiv.Perm (Fin n)} (hq : q ∈ Q)
    {x : Fin n} (hx : x ∈ MulAction.fixedPoints N (Fin n)) :
    q • x ∈ MulAction.fixedPoints N (Fin n) := by
  rw [MulAction.mem_fixedPoints] at hx ⊢
  intro nn
  rw [Subgroup.smul_def]
  have hmem : q⁻¹ * (nn : Equiv.Perm (Fin n)) * q ∈ N := by
    simpa using hN q⁻¹ (Q.inv_mem hq) (nn : Equiv.Perm (Fin n)) nn.2
  have hx' : (q⁻¹ * (nn : Equiv.Perm (Fin n)) * q) • x = x := by
    simpa using hx ⟨_, hmem⟩
  calc (nn : Equiv.Perm (Fin n)) • (q • x)
      = ((nn : Equiv.Perm (Fin n)) * q) • x := smul_smul _ _ _
    _ = (q * (q⁻¹ * (nn : Equiv.Perm (Fin n)) * q)) • x := by
          rw [show (nn : Equiv.Perm (Fin n)) * q
              = q * (q⁻¹ * (nn : Equiv.Perm (Fin n)) * q) by group]
    _ = q • ((q⁻¹ * (nn : Equiv.Perm (Fin n)) * q) • x) := (smul_smul q _ x).symm
    _ = q • x := by rw [hx']

theorem y7a_normal_pgroup_trivial {n p : ℕ} [Fact p.Prime] (hp : ¬ p ∣ n)
    (Q N : Subgroup (Equiv.Perm (Fin n))) (hNQ : N ≤ Q)
    (hN : ∀ q ∈ Q, ∀ m ∈ N, q * m * q⁻¹ ∈ N)
    (htrans : ∀ i j : Fin n, ∃ q ∈ Q, q i = j) (hpN : IsPGroup p N) : N = ⊥ := by
  obtain ⟨x₀, hx₀⟩ :=
    hpN.nonempty_fixed_point_of_prime_not_dvd_card (Fin n) (by simpa [Nat.card_fin] using hp)
  have hfix : MulAction.fixedPoints N (Fin n) = Set.univ :=
    eq_univ_of_nonempty_of_forall_smul_mem Q (MulAction.fixedPoints N (Fin n)) ⟨x₀, hx₀⟩
      (fun q hq _ hx => smul_mem_fixedPoints_of_forall_conj_mem hN hq hx) htrans
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  refine Equiv.ext (fun y => ?_)
  have hy : y ∈ MulAction.fixedPoints N (Fin n) := by rw [hfix]; trivial
  rw [MulAction.mem_fixedPoints] at hy
  simpa using hy ⟨m, hm⟩

end CFSG.OddStandard.HigherRank.YamadaG23
