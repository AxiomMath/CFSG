module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSp
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.RankOne
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L238BridgeAlt57Sp4
public import CFSG.LieType.Steinberg.Classical.Symplectic

public section

namespace CFSG.AGLEmbedding.ParabPrime

open CFSG.AGLEmbedding.ParabHub CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Sp
  CFSG.LieType.RootSystem CFSG.LieType.CurtisTits
open CFSG.ClassicalInvolution.Models.SymplecticPairs
open scoped commutatorElement

theorem exists_perfect_of_equiv_perm_six {G : Type*} [Group G] {S : Subgroup G}
    (Φ : S ≃* Equiv.Perm (Fin 6)) :
    ∃ V : Subgroup G, V ≤ S ∧ ⁅V, V⁆ = V ∧ Nat.card V = 360 ∧ Nat.card S = 720 := by
  have h5 : 5 ≤ Nat.card (Fin 6) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
    omega
  set C : Subgroup S := commutator S with hC
  have hCA : C.map Φ.toMonoidHom = alternatingGroup (Fin 6) := by
    rw [hC, commutator_def, Subgroup.map_commutator, Subgroup.map_top_of_surjective _ Φ.surjective,
      ← commutator_def, alternatingGroup.commutator_perm_eq h5]
  have hCperf : ⁅C, C⁆ = C := by
    apply Subgroup.map_injective (f := Φ.toMonoidHom) Φ.injective
    show (⁅C, C⁆).map Φ.toMonoidHom = C.map Φ.toMonoidHom
    rw [Subgroup.map_commutator, hCA, commutator_alternatingGroup_eq_self h5]
  refine ⟨C.map S.subtype, Subgroup.map_subtype_le C, ?_, ?_, ?_⟩
  · rw [← Subgroup.map_commutator, hCperf]
  · rw [Subgroup.card_map_of_injective S.subtype_injective]
    calc Nat.card C = Nat.card (C.map Φ.toMonoidHom) :=
          (Subgroup.card_map_of_injective Φ.injective).symm
      _ = 360 := by
        rw [hCA, nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
        decide
  · rw [Nat.card_congr Φ.toEquiv, Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide

section Tail

open CFSG.ClassicalInvolution.Models.SymplecticPairs CFSG.LieType.Universal.Symplectic
  CFSG.LieType.CurtisTits CFSG.Assembly.LowTwoRank
open CFSG.LieType.Universal.Symplectic.SpExtras (ne_succ')

variable {K : Type} [Field K] {n : ℕ}

theorem sp_tail_exc [Finite K] (hK : Nat.card K = 2) {k : Fin n} (hk2 : k.val + 2 = n) :
    ∃ V : Subgroup (StatedSp n K),
      V ≤ rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, by omega⟩ ∧
        ⁅V, V⁆ = V ∧ ∀ p : ℕ, p.Prime → 5 ≤ p →
          p ∣ Nat.card ↥(rankOne (rootGroup n K) k ⊔
            rankOne (rootGroup n K) ⟨k.val + 1, by omega⟩) → p ∣ Nat.card V := by
  have hk : k.val + 1 < n := by omega
  have hlong : ¬(⟨k.val + 1, hk⟩ : Fin n).val + 1 < n := by
    simp only
    omega
  have hsup : rankOne (rootGroup n K) k ⊔ rankOne (rootGroup n K) ⟨k.val + 1, hk⟩ =
      (spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk))).range := by
    rw [← range_shortBlock_eq_rankOne hk, ← range_longBlock_eq_rankOne hlong]
    exact shortBlock_sup_longBlock (ne_succ' hk)
  have := Fintype.ofFinite K
  have hK2 : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  set θ := spEmbed (K := K) (pairMap k ⟨k.val + 1, hk⟩) (pairMap_injective (ne_succ' hk)) with hθ
  have hθinj : Function.Injective θ := spEmbed_injective (pairMap_injective (ne_succ' hk))
  let Φ : θ.range ≃* Equiv.Perm (Fin 6) :=
    (MonoidHom.ofInjective hθinj).symm.trans
      (CFSG.QuasithinUnique.Bridge.Alt57Model.spEquivPerm K hK2)
  obtain ⟨V, hVS, hV, h360, h720⟩ := exists_perfect_of_equiv_perm_six Φ
  refine ⟨V, hsup ▸ hVS, hV, fun p hp hp5 hpS => ?_⟩
  rw [hsup, h720] at hpS
  rw [h360]
  have h720' : (720 : ℕ) = 2 * 360 := by norm_num
  rw [h720'] at hpS
  rcases hp.dvd_mul.1 hpS with h | h
  · have := Nat.le_of_dvd (by norm_num) h
    omega
  · exact h

end Tail

section Pairs

variable {K : Type} [Field K] {n : ℕ}

theorem single_add_single_mem_roots {K : Type*} [Group K] {D : UniversalRootDatum K}
    {i j : Fin D.rank} (hAji : D.cartan j i = -1) :
    (Pi.single i 1 : Fin D.rank → ℤ) + Pi.single j 1 ∈ D.roots := by
  have := pair_one_one_mem_roots (D := D) (i := i) (j := j) hAji
  simpa [pair_apply] using this

theorem cartanC_succ {i j : Fin n} (hij : i.val + 1 = j.val) (hj : j.val + 1 < n) :
    cartanC n i j = -1 ∧ cartanC n j i = -1 := by
  have hv : i.val ≠ j.val := by omega
  constructor
  · simp [cartanC, Fin.ext_iff, hv]
    omega
  · simp [cartanC, Fin.ext_iff, Ne.symm hv]
    omega

theorem sp_commutator_ne_one {i j : Fin n} (hij : i.val + 1 = j.val) (hj : j.val + 1 < n) :
    ⁅Sp.x n K (Pi.single i 1) 1, Sp.x n K (Pi.single j 1) 1⁆ ≠ 1 := by
  intro h
  have hne : i ≠ j := Fin.ne_of_val_ne (by omega)
  have hi : i.val + 1 < n := by omega
  obtain ⟨hA1, hA2⟩ := cartanC_succ hij hj
  have hα : (Pi.single i 1 : Fin n → ℤ) ∈ (rootDatum n K).roots :=
    (RootSystem.ofCartan (rootDatum n K).isFiniteType (rootDatum n K).divisible).single_mem i
  have hβ : (Pi.single j 1 : Fin n → ℤ) ∈ (rootDatum n K).roots :=
    (RootSystem.ofCartan (rootDatum n K).isFiniteType (rootDatum n K).divisible).single_mem j
  have hαβ : (Pi.single i 1 : Fin n → ℤ) + Pi.single j 1 ≠ 0 := by
    intro h0
    have := congrFun h0 i
    simp [hne] at this
  have hr : (Pi.single i 1 : Fin n → ℤ) + Pi.single j 1 ∈ (rootDatum n K).roots :=
    single_add_single_mem_roots (D := rootDatum n K) (i := i) (j := j) hA2
  have h2 : toStd n ((Pi.single i 1 : Fin n → ℤ) + Pi.single j 1) ⬝ᵥ
      toStd n ((Pi.single i 1 : Fin n → ℤ) + Pi.single j 1) = 2 := by
    rw [toStd_add', toStd_single_of_lt' hi, toStd_single_of_lt' hj]
    have hjeq : (⟨i.val + 1, hi⟩ : Fin n) = j := Fin.ext hij
    rw [hjeq]
    have e : (Pi.single i 1 - Pi.single j 1 + (Pi.single j 1 - Pi.single ⟨j.val + 1, hj⟩ 1) :
        Fin n → ℤ) = Pi.single i 1 - Pi.single ⟨j.val + 1, hj⟩ 1 := by abel
    rw [e]
    have hne2 : i ≠ ⟨j.val + 1, hj⟩ := Fin.ne_of_val_ne (by simp; omega)
    simp [dotProduct_sub, hne2]
  have hc1 := natAbs_commC_one_one hα hβ hαβ hr h2
  have hcomm : Ex K (Pi.single i 1 : Fin n → ℤ) * Ex K (Pi.single j 1 : Fin n → ℤ) =
      Ex K (Pi.single j 1 : Fin n → ℤ) * Ex K (Pi.single i 1 : Fin n → ℤ) := by
    have hg := commutatorElement_eq_one_iff_mul_comm.1 h
    have hm := congrArg (mat n K) hg
    rw [map_mul, map_mul, mat_x, mat_x] at hm
    simp only [one_smul, mul_add, add_mul, one_mul, mul_one] at hm
    refine sub_eq_zero.1 ?_
    calc Ex K (Pi.single i 1 : Fin n → ℤ) * Ex K (Pi.single j 1 : Fin n → ℤ) -
          Ex K (Pi.single j 1 : Fin n → ℤ) * Ex K (Pi.single i 1 : Fin n → ℤ)
        = (1 + Ex K (Pi.single i 1 : Fin n → ℤ) + (Ex K (Pi.single j 1 : Fin n → ℤ) +
          Ex K (Pi.single i 1 : Fin n → ℤ) * Ex K (Pi.single j 1 : Fin n → ℤ))) -
          (1 + Ex K (Pi.single j 1 : Fin n → ℤ) + (Ex K (Pi.single i 1 : Fin n → ℤ) +
          Ex K (Pi.single j 1 : Fin n → ℤ) * Ex K (Pi.single i 1 : Fin n → ℤ))) := by abel
      _ = 0 := sub_eq_zero.2 hm
  have hlie := Ex_lie (F := K) hα hβ hαβ
  rw [hcomm, sub_self] at hlie
  have hEne : Ex K ((Pi.single i 1 : Fin n → ℤ) + Pi.single j 1) ≠ 0 := by
    intro h0
    have h1 : Sp.x n K ((Pi.single i 1 : Fin n → ℤ) + Pi.single j 1) 1 =
        Sp.x n K ((Pi.single i 1 : Fin n → ℤ) + Pi.single j 1) 0 := by
      apply mat_injective
      rw [mat_x, mat_x, h0]
      simp
    exact one_ne_zero ((Sp.isParametrization (n := n) (F := K) _ hr).2.2 h1)
  have hcne : ((commC (Pi.single i 1 : Fin n → ℤ) (Pi.single j 1 : Fin n → ℤ) (1, 1) : ℤ) : K) ≠
      0 := by
    rcases Int.natAbs_eq_iff.1 hc1 with h | h <;> rw [h] <;> simp
  rcases smul_eq_zero.1 hlie.symm with h0 | h0
  · exact hcne h0
  · exact hEne h0

end Pairs

section Model

variable {K : Type} [Field K] {n : ℕ}

@[expose] def spTail (n : ℕ) (i j : Fin n) : Prop :=
  (i.val + 2 = n ∧ j.val + 1 = n) ∨ (j.val + 2 = n ∧ i.val + 1 = n)

theorem twoLevi_sp [Finite K] (hK : Nat.card K = 2) : TwoLevi (rootDatum n K) (spTail n) := by
  refine TwoLevi.of_param hK Sp.isParametrization (isCTGroupDatum n K) (steinbergExtras n K)
    (fun (i : Fin n) => ?_) (fun (i j : Fin n) h => h.symm)
    (fun (i j l : Fin n) hij hil => ?_) (fun (i j : Fin n) hij => ?_)
    (fun (i j : Fin n) hne hA hnt => ?_)
  · obtain ⟨φ, -, hx, hy⟩ := Sp.rankOne (F := K) i
    exact ⟨φ, hx, hy⟩
  · rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> rcases hil with ⟨h3, h4⟩ | ⟨h3, h4⟩ <;>
      exact Fin.ext (by omega)
  · rcases hij with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hi1 : i.val + 1 < n := by omega
      have hk : j = ⟨i.val + 1, hi1⟩ := Fin.ext (by simp; omega)
      subst hk
      exact sp_tail_exc hK h1
    · have hj1 : j.val + 1 < n := by omega
      have hk : i = ⟨j.val + 1, hj1⟩ := Fin.ext (by simp; omega)
      subst hk
      rw [sup_comm]
      exact sp_tail_exc hK h1
  · have hA' : cartanC n i j ≠ 0 := hA
    have hv : i.val ≠ j.val := fun e => hne (Fin.ext e)
    have hadj : i.val + 1 = j.val ∨ j.val + 1 = i.val := by
      by_contra hn
      apply hA'
      simp [cartanC, Fin.ext_iff, hv]
      omega
    unfold spTail at hnt
    rcases hadj with h | h
    · have hj : j.val + 1 < n := by omega
      obtain ⟨h1, h2⟩ := cartanC_succ h hj
      exact ⟨h1, h2, 1, 1, sp_commutator_ne_one (K := K) h hj⟩
    · have hi : i.val + 1 < n := by omega
      obtain ⟨h1, h2⟩ := cartanC_succ h hi
      refine ⟨h2, h1, 1, 1, fun hc => sp_commutator_ne_one (K := K) h hi ?_⟩
      rw [← commutatorElement_inv]
      exact inv_eq_one.2 hc

theorem parabCore_of_model_psp_two {Y : Type} [Group Y] [Finite Y] {n : ℕ}
    (h : StatedClassicalModel Y .PSp n 2 1) : ParabCore Y 2 := by
  obtain ⟨-, K, hK, hKfin, hcard, ⟨e⟩⟩ := h
  have hK2 : Nat.card K = 2 := by simpa using hcard
  have := Fintype.ofFinite K
  have : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; simpa using hcard)
  exact (borelQuotient_sp e).parabCore_two (by rw [hK2]; norm_num) (twoLevi_sp hK2)

end Model

end CFSG.AGLEmbedding.ParabPrime
