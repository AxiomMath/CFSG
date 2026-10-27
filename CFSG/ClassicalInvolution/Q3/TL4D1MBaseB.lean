module

public import CFSG.ClassicalInvolution.Q3.TL4D1MBase
public import CFSG.ClassicalInvolution.Q3.AE.E64
public import CFSG.ClassicalInvolution.Q3.TL4D1Facts

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG.ClassicalInvolution.Q3.AE Wr

variable {n : ℕ}

@[expose] def PairTrans (P : Subgroup (Equiv.Perm (Fin n))) : Prop :=
  ∀ j k : Fin n, j ≠ k → ∃ g ∈ P, ∃ i : Fin n, i ≠ k ∧ g i = i ∧ g k = j

theorem pairVec_comp_symm (g : Equiv.Perm (Fin n)) (i k : Fin n) :
    (fun x => pairVec i k (g.symm x)) = pairVec (g i) (g k) := by
  funext x
  simp only [pairVec, Pi.add_apply, Pi.single_apply, Equiv.symm_apply_eq]

theorem pairVec_add (i j k : Fin n) : pairVec i j + pairVec i k = pairVec j k := by
  funext x
  simp only [pairVec, Pi.add_apply]
  generalize (Pi.single i 1 : Fin n → ZMod 2) x = a
  generalize (Pi.single j 1 : Fin n → ZMod 2) x = b
  generalize (Pi.single k 1 : Fin n → ZMod 2) x = c
  revert a b c
  decide

theorem sum_pairVec (j k : Fin n) : ∑ x, pairVec j k x = 0 := by
  simp only [pairVec, Pi.add_apply, Finset.sum_add_distrib, Finset.sum_pi_single',
    Finset.mem_univ, ite_true]
  decide

theorem ofVec_mul_self (u : Fin n → ZMod 2) : ofVec u * ofVec u = 1 := by
  rw [ofVec_mul_ofVec]
  exact Wr.ext (funext fun x => zmod_two_add_self (u x)) rfl

theorem comm_pairVec (a : Wr n) {i j k : Fin n} (hi : a.perm i = i) (hk : a.perm k = j) :
    a * ofVec (pairVec i k) * a⁻¹ * (ofVec (pairVec i k))⁻¹ = ofVec (pairVec j k) := by
  rw [conj_ofVec, pairVec_comp_symm, hi, hk, inv_eq_of_mul_eq_one_right (ofVec_mul_self _),
    ofVec_mul_ofVec, pairVec_add]

theorem mkQ_mem_aeBarOver {P : Subgroup (Equiv.Perm (Fin n))} {a : Wr n} (ha : a ∈ aeSubOver P) :
    mkQ n a ∈ aeBarOver P :=
  ⟨a, ha, rfl⟩

theorem aeBarOver_perfect {P : Subgroup (Equiv.Perm (Fin n))}
    (hPA : ∀ σ ∈ P, Equiv.Perm.sign σ = 1) (hPp : ⁅P, P⁆ = P) (htr : PairTrans P) :
    ModelPerfect (aeBarOver P) := by
  set M := aeBarOver P with hM
  refine le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => ?_) ?_
  · rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)) (M.inv_mem hb)
  let ψ : Equiv.Perm (Fin n) →* AEQ n :=
    { toFun := fun σ => mkQ n (ofPerm σ)
      map_one' := by rw [ofPerm_one, map_one]
      map_mul' := fun σ τ => by rw [← ofPerm_mul, map_mul] }
  have hψM : P.map ψ ≤ M := by
    rintro _ ⟨σ, hσ, rfl⟩
    exact mkQ_mem_aeBarOver (ofPerm_mem_aeSubOver hσ (hPA σ hσ))
  have hperm : ∀ σ ∈ P, mkQ n (ofPerm σ) ∈ ⁅M, M⁆ := by
    intro σ hσ
    have h1 : ψ σ ∈ (⁅P, P⁆).map ψ := ⟨σ, hPp.symm ▸ hσ, rfl⟩
    rw [Subgroup.map_commutator] at h1
    exact Subgroup.commutator_mono hψM hψM h1
  have hpair : ∀ j k : Fin n, j ≠ k → mkQ n (ofVec (pairVec j k)) ∈ ⁅M, M⁆ := by
    intro j k hjk
    obtain ⟨g, hg, i, -, hgi, hgk⟩ := htr j k hjk
    have hc := Subgroup.commutator_mem_commutator
      (mkQ_mem_aeBarOver (ofPerm_mem_aeSubOver hg (hPA g hg)))
      (mkQ_mem_aeBarOver (ofVec_mem_aeSubOver (P := P) (sum_pairVec i k)))
    rwa [commutatorElement_def, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
      comm_pairVec (ofPerm g) hgi hgk] at hc
  rintro _ ⟨a, ha, rfl⟩
  rw [eq_ofVec_mul_ofPerm a, map_mul]
  exact Subgroup.mul_mem _ (mem_of_pairVec hpair ha.1.1) (hperm _ ha.2)

theorem mul_self_of_permBar_eq_one {x : AEQ n} (hx : permBar n x = 1) : x * x = 1 := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective x
  have hb : b.perm = 1 := by rw [← permBar_mkQ]; exact hx
  show mkQ n b * mkQ n b = 1
  rw [← map_mul, vecSub_mul_self hb, map_one]

theorem exists_odd_of_not_isPGroup {G : Type} [Group G] [Finite G] {N : Subgroup G}
    (h : ¬ IsPGroup 2 N) : ∃ y ∈ N, Odd (orderOf y) ∧ y ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf] at h
  push Not at h
  obtain ⟨g, hg⟩ := h
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨((g ^ 2 ^ k : N) : G), (g ^ 2 ^ k).2, ?_, fun h1 => ?_⟩
  · rw [Subgroup.orderOf_coe]
    refine hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one ?_)
    rw [← pow_mul, ← hkm, pow_orderOf_eq_one]
  · have h1' : g ^ 2 ^ k = 1 := Subtype.ext h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one h1')
    exact hg j hj

end CFSG.ClassicalInvolution.Q3.TL4
