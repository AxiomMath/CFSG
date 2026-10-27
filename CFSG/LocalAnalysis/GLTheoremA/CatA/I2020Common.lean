module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2020Defs
public import CFSG.GroupTheory.GroupAction.CoprimeSeriesTrivial
public import CFSG.GroupTheory.InnerNormalizedAutomorphisms
public import CFSG.Fischer.Aut.TwoPower
public import CFSG.GH74.KGroups.L3EpsOrder

public section

namespace CFSG.LocalAnalysis.GLTheoremA.I2020

open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {β : MulAut X}

theorem i2020FixCentAt_of_sylow (hZ : Subgroup.center X = ⊥)
    (D : Subgroup (MulAut X)) [D.Normal] (hD : ∀ α : MulAut X, ⁅α, β⁆ ∈ D)
    (hDβ : ∀ d ∈ D, ⁅d, β⁆ ∈ (MulAut.conj : X →* MulAut X).range)
    {J : Subgroup X} (hJβ : J ≤ fixSubgroup β)
    (hsyl : (Nat.card J).factorization 2 = (Nat.card X).factorization 2) :
    I2020FixCentAt β J := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : ((MulAut.conj : X →* MulAut X).range).Normal := CFSG.Fischer.innerAut_normal
  intro T hTsyl S hSp hST hSβ hScomm
  have hβD : β ∈ Subgroup.normalizer (D : Set (MulAut X)) := by
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top β
  have hSD : S ≤ D := by
    have h := CFSG.commutator_zpowers_le_of_mem_commutator hβD (a := β) (M := S) (W := D)
      fun m _ => by
        have h' := D.inv_mem (hD m)
        rwa [commutatorElement_inv, commutatorElement_def] at h'
    have hle : ⁅Subgroup.zpowers β, S⁆ ≤ D := Subgroup.commutator_le.mpr h
    rw [Subgroup.commutator_comm] at hle
    exact hScomm ▸ hle
  have hSInn : S ≤ (MulAut.conj : X →* MulAut X).range := by
    have h := CFSG.commutator_zpowers_le_of_mem_commutator (a := β) (M := D)
      (W := (MulAut.conj : X →* MulAut X).range) (by
        rw [Subgroup.normalizer_eq_top]
        exact Subgroup.mem_top β) fun m hm => by
      have h' := (MulAut.conj : X →* MulAut X).range.inv_mem (hDβ m hm)
      rwa [commutatorElement_inv, commutatorElement_def] at h'
    have hle : ⁅Subgroup.zpowers β, D⁆ ≤ (MulAut.conj : X →* MulAut X).range :=
      Subgroup.commutator_le.mpr h
    rw [Subgroup.commutator_comm] at hle
    exact hScomm ▸ (Subgroup.commutator_mono hSD le_rfl).trans hle
  have hcardT : Nat.card T = ordProj[2] (Nat.card X) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    let T' : Subgroup J := T.subgroupOf J
    have hT'p : IsPGroup 2 T' := hTsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTsyl.1).symm
    have hmax : ∀ Q : Subgroup J, IsPGroup 2 Q → T' ≤ Q → Q = T' := by
      intro Q hQ hle
      have hQmap : Q.map J.subtype = T := by
        apply hTsyl.2.2 (Q.map J.subtype)
        · intro x hx
          obtain ⟨q, hq, rfl⟩ := hx
          exact q.2
        · exact hQ.map J.subtype
        · rintro t ht
          exact ⟨⟨t, hTsyl.1 ht⟩, hle ht, rfl⟩
      apply le_antisymm ?_ hle
      intro q hq
      rw [Subgroup.mem_subgroupOf]
      have : (q : X) ∈ Q.map J.subtype := ⟨q, hq, rfl⟩
      rwa [hQmap] at this
    let T₀ : Sylow 2 J :=
      { toSubgroup := T'
        isPGroup' := hT'p
        is_maximal' := fun {Q} hQ hle => hmax Q hQ hle }
    have hcard := T₀.card_eq_multiplicity
    have hcard' : Nat.card T' = Nat.card T :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTsyl.1).toEquiv
    rw [← hcard', hcard]
    exact congrArg (fun k => 2 ^ k) hsyl
  have hmaxT : ∀ P : Subgroup X, IsPGroup 2 P → T ≤ P → P = T := by
    intro P hP hTP
    exact le_antisymm
      (CFSG.GH74.KGroups.L3Eps.isMax_of_card (S := T) hcardT P hP hTP) hTP
  have hSc2 : IsPGroup 2 (S.comap (MulAut.conj : X →* MulAut X)) :=
    CFSG.InnerNormalizedAutomorphisms.isPGroup_comap_conj hZ hSp
  have hmemT : ∀ s ∈ S, ∃ x ∈ T, MulAut.conj x = s := by
    intro s hs
    obtain ⟨x, hx⟩ := hSInn hs
    have hxmem : x ∈ S.comap (MulAut.conj : X →* MulAut X) := by
      show MulAut.conj x ∈ S
      rw [hx]
      exact hs
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
      obtain ⟨k, hk⟩ := hSc2.exists_orderOf_eq_pow ⟨x, hxmem⟩
      refine IsPGroup.of_card (n := k) ?_
      rw [Nat.card_zpowers, ← Subgroup.orderOf_mk x hxmem, hk]
    have hxC : x ∈ Subgroup.centralizer (T : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have h' : MulAut.conj x t = t := by
        rw [hx]
        exact hST s hs t ht
      rw [MulAut.conj_apply] at h'
      simpa [mul_assoc] using (congrArg (· * x) h').symm
    have hTcent : T ≤ Subgroup.centralizer ({x} : Set X) := by
      intro t ht
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      exact (Subgroup.mem_centralizer_iff.mp hxC t ht).symm
    have hnorm : T ≤ Subgroup.normalizer (Subgroup.zpowers x : Set X) := by
      rw [Subgroup.zpowers_eq_closure]
      exact hTcent.trans ((Subgroup.centralizer_le_normalizer {x}).trans
        (Subgroup.normalizer_le_normalizer_closure {x}))
    have hxT : x ∈ T := by
      have hsup : IsPGroup 2 (T ⊔ Subgroup.zpowers x : Subgroup X) :=
        IsPGroup.to_sup_of_normal_right' (p := 2) hTsyl.2.1 hx2 hnorm
      have hle : Subgroup.zpowers x ≤ T := (hmaxT _ hsup le_sup_left) ▸ le_sup_right
      exact hle (Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩)
    exact ⟨x, hxT, hx⟩
  have hβs : ∀ s ∈ S, β * s * β⁻¹ = s := by
    intro s hs
    obtain ⟨x, hxT, rfl⟩ := hmemT s hs
    rw [CFSG.InnerNormalizedAutomorphisms.mul_conj_mul_inv_eq,
      mem_fixSubgroup.mp (hJβ (hTsyl.1 hxT))]
  have hSc : ⁅S, Subgroup.zpowers β⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : Commute β s := by
      show β * s = s * β
      calc β * s = (β * s * β⁻¹) * β := by group
        _ = s * β := by rw [hβs s hs]
    exact (hcomm.zpow_left n).eq
  have hSbot : S = ⊥ := hScomm ▸ hSc
  intro s hs j hj
  have hs1 : s = 1 := Subgroup.mem_bot.mp (hSbot ▸ hs)
  rw [hs1, MulAut.one_apply]

end CFSG.LocalAnalysis.GLTheoremA.I2020

end