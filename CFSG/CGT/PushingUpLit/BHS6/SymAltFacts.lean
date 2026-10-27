module

public import CFSG.CGT.PushingUpLit.BHS.SymNatSplit
public import CFSG.CGT.PushingUpLit.Glue.NaturalIrred

public section

namespace CFSG.CGT.PushingUpLit.BHS6

open CFSG.Quasithin CFSG.Quasithin.G6 CFSG.CGT.PushingUpLit.BHS

variable {n : ℕ}

theorem not_isPGroup_two_alternating (h3 : 3 ≤ n) :
    ¬ IsPGroup 2 ↥(alternatingGroup (Fin n)) := by
  intro h
  have hij : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hik : (⟨0, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hjk : (⟨1, by omega⟩ : Fin n) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have h3c := cyc_isThreeCycle hij hik hjk
  have hσ : cyc (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨2, by omega⟩ ∈ alternatingGroup (Fin n) :=
    Equiv.Perm.mem_alternatingGroup.2 h3c.sign
  obtain ⟨k, hk⟩ := h ⟨_, hσ⟩
  have hk' : (cyc (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨2, by omega⟩) ^ (2 ^ k) = 1 := by
    have := congrArg (fun x : ↥(alternatingGroup (Fin n)) => (x : Equiv.Perm (Fin n))) hk
    simpa using this
  have h1 : orderOf (cyc (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ ⟨2, by omega⟩) ∣ 2 ^ k :=
    orderOf_dvd_of_pow_eq_one hk'
  rw [h3c.orderOf] at h1
  have h2 : 3 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h1
  omega

theorem eq_bot_of_normal_isPGroup_alternating (h5 : 5 ≤ n)
    {N : Subgroup ↥(alternatingGroup (Fin n))} (hN : N.Normal) (h2 : IsPGroup 2 ↥N) : N = ⊥ := by
  have := hN
  rcases alternatingGroup.normal_subgroup_eq_bot_or_eq_top (α := Fin n) (by simpa using h5)
    (N := N) with h | h
  · exact h
  · exfalso
    apply not_isPGroup_two_alternating (by omega : 3 ≤ n)
    intro x
    obtain ⟨k, hk⟩ := h2 ⟨x, by rw [h]; trivial⟩
    exact ⟨k, congrArg Subtype.val hk⟩

theorem eq_top_of_invariant_ne_bot (hodd : Odd n) (h3 : 3 ≤ n) (X : Subgroup ↥(coreMod n))
    (hX : ∀ σ ∈ alternatingGroup (Fin n), ∀ x ∈ X, coreAct n σ x ∈ X) (hne : X ≠ ⊥) :
    X = ⊤ := by
  let N : AddSubgroup (Fin n → ZMod 2) :=
    { carrier := {v | ∃ x ∈ X, Multiplicative.toAdd (x : PermMod n) = v}
      zero_mem' := ⟨1, X.one_mem, rfl⟩
      add_mem' := by
        rintro _ _ ⟨x, hx, rfl⟩ ⟨y, hy, rfl⟩
        exact ⟨x * y, X.mul_mem hx hy, rfl⟩
      neg_mem' := by
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x⁻¹, X.inv_mem hx, by simp⟩ }
  have hNΔ : N ≤ CFSG.CGT.PushingUpLit.Glue.evenWeight n := by
    rintro _ ⟨x, hx, rfl⟩
    rw [CFSG.CGT.PushingUpLit.Glue.mem_evenWeight_iff]
    exact x.2
  have hNinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ v ∈ N,
      CFSG.CGT.PushingUpLit.Glue.permVec σ v ∈ N := by
    rintro σ hσ _ ⟨x, hx, rfl⟩
    exact ⟨coreAct n σ x, hX σ hσ x hx, rfl⟩
  rcases CFSG.CGT.PushingUpLit.Glue.altInvariant_eq_bot_or_evenWeight hodd h3 N hNΔ hNinv with
    hb | hT
  · exfalso
    apply hne
    rw [eq_bot_iff]
    intro x hx
    have : Multiplicative.toAdd (x : PermMod n) ∈ N := ⟨x, hx, rfl⟩
    rw [hb, AddSubgroup.mem_bot] at this
    have h1 : (x : PermMod n) = 1 := Multiplicative.toAdd.injective this
    exact Subgroup.mem_bot.2 (Subtype.ext h1)
  · rw [eq_top_iff]
    intro y _
    have hy : Multiplicative.toAdd (y : PermMod n) ∈ N := by
      rw [hT, CFSG.CGT.PushingUpLit.Glue.mem_evenWeight_iff]
      exact y.2
    obtain ⟨x, hx, hxy⟩ := hy
    have : x = y := Subtype.ext (Multiplicative.toAdd.injective hxy)
    rw [← this]
    exact hx

theorem eq_one_of_fixed_alt (hodd : Odd n) (h3 : 3 ≤ n) (v : ↥(coreMod n))
    (hv : ∀ σ ∈ alternatingGroup (Fin n), coreAct n σ v = v) : v = 1 := by
  have hconst : ∀ i j : Fin n, vcoord v i = vcoord v j := by
    intro i j
    by_cases hij : i = j
    · rw [hij]
    · obtain ⟨k, hki, hkj⟩ := exists_ne_ne h3 i j
      have hσ : cyc i j k ∈ alternatingGroup (Fin n) :=
        Equiv.Perm.mem_alternatingGroup.2
          (cyc_isThreeCycle hij (Ne.symm hki) (Ne.symm hkj)).sign
      have h1 := congrArg (fun w => vcoord w i) (hv _ hσ)
      simp only [vcoord_coreAct] at h1
      have h2 : (cyc i j k)⁻¹ i = j :=
        Equiv.Perm.inv_eq_iff_eq.2 (cyc_apply_second hij (Ne.symm hkj)).symm
      rw [h2] at h1
      exact h1.symm
  have hn : 0 < n := by omega
  have h0 := sum_vcoord v
  have h1 : ∑ i, vcoord v i = (n : ZMod 2) * vcoord v ⟨0, hn⟩ := by
    rw [Finset.sum_congr rfl fun i _ => hconst i ⟨0, hn⟩]
    simp
  have hn1 : (n : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.2 hodd
  rw [h1, hn1, one_mul] at h0
  refine vcoord_ext fun i => ?_
  rw [hconst i ⟨0, hn⟩, h0]
  rfl

end CFSG.CGT.PushingUpLit.BHS6
