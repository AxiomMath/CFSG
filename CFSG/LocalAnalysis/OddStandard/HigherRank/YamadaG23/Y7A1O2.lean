module

public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.OddStandard.HigherRank.YamadaG23

theorem y7a_O2_trivial (Q : Subgroup (Equiv.Perm (Fin 16))) (D : Set (Fin 16))
    (hD0 : (0 : Fin 16) ∉ D) (hDodd : Odd (Nat.card ↥D))
    (hDinv : ∀ q ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
      ∀ i ∈ D, q i ∈ D)
    (hDtr : ∀ i ∈ D, ∀ j ∈ D,
      ∃ q ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16), q i = j)
    (hfix : ∀ q ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
      (∀ i ∈ D, q i = i) → q = 1) :
    ∀ N : Subgroup (Equiv.Perm (Fin 16)),
      N ≤ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16) →
      (∀ s ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
        ∀ m ∈ N, s * m * s⁻¹ ∈ N) →
      IsPGroup 2 N → N = ⊥ := by
  intro N hN hnorm h2
  classical
  have hDinvN : ∀ m : N, ∀ i ∈ D, (m : Equiv.Perm (Fin 16)) i ∈ D :=
    fun m i hi => hDinv (m : Equiv.Perm (Fin 16)) (hN m.2) i hi
  letI : MulAction N (Fin 16) := MulAction.compHom (Fin 16) N.subtype
  let p : SubMulAction N (Fin 16) :=
    { carrier := D
      smul_mem' := fun m x hx => by
        simpa [MulAction.compHom_smul_def, Equiv.Perm.smul_def] using hDinvN m x hx }
  letI : MulAction N p := SubMulAction.mulAction p
  have hoddD : ¬ 2 ∣ Nat.card ↥D := by
    rintro ⟨k, hk⟩
    obtain ⟨j, hj⟩ := hDodd
    omega
  obtain ⟨i, hi⟩ := h2.nonempty_fixed_point_of_prime_not_dvd_card p hoddD
  rw [MulAction.mem_fixedPoints] at hi
  have hifixed : ∀ m : N, (m : Equiv.Perm (Fin 16)) (i : Fin 16) = i := by
    intro m
    have h := congrArg Subtype.val (hi m)
    simpa [MulAction.compHom_smul_def, Equiv.Perm.smul_def] using h
  have hFixInv : ∀ q ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16),
      ∀ x ∈ D, (∀ m : N, (m : Equiv.Perm (Fin 16)) x = x) →
      ∀ m : N, (m : Equiv.Perm (Fin 16)) (q x) = q x := by
    intro q hq x _ hxfix m
    have hqinv : q⁻¹ ∈ Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16) :=
      (Q ⊓ MulAction.stabilizer (Equiv.Perm (Fin 16)) (0 : Fin 16)).inv_mem hq
    have hmN : q⁻¹ * (m : Equiv.Perm (Fin 16)) * q ∈ N := by
      simpa using hnorm q⁻¹ hqinv (m : Equiv.Perm (Fin 16)) m.2
    have hfixm : (q⁻¹ * (m : Equiv.Perm (Fin 16)) * q) x = x := hxfix ⟨_, hmN⟩
    calc (m : Equiv.Perm (Fin 16)) (q x)
        = q ((q⁻¹ * (m : Equiv.Perm (Fin 16)) * q) x) := by
          simp [Equiv.Perm.mul_apply]
      _ = q x := by rw [hfixm]
  rw [Subgroup.eq_bot_iff_forall]
  intro m hm
  exact hfix m (hN hm) fun j hj => by
    obtain ⟨q, hq, hqi⟩ := hDtr (i : Fin 16) i.2 j hj
    have hfixq := hFixInv q hq (i : Fin 16) i.2 (fun m' => hifixed m') ⟨m, hm⟩
    rwa [hqi] at hfixq

end CFSG.OddStandard.HigherRank.YamadaG23
