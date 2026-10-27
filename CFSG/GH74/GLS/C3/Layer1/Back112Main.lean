module

public import CFSG.GH74.GLS.C3.Layer1.Back112Top
public import CFSG.GH74.GLS.C3.Layer1.Back112Glue

public section

namespace CFSG.GH74.GLS

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS.C3.Layer1.Back

theorem s_lemma112_of
    (h81 : B_iv2_8_1) (h92 : B_lemma92) (h102a : B_ivk_10_2a) : S_lemma112 := by
  intro G _ _ hG x K L M T Q hh p91 hKL hQZ
  subst hKL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hA : Hyp9A x K K M T Q := hh.a
  have hTp : IsPGroup 2 ↥T := hA.sylowT.isPGroup
  have hQT : Q ≤ T := Setup91.Q_le_T hA
  have hTM : T ≤ M := hA.sylowTM.le
  have hcases := kBar_cases p91
  have hlist := hlist_of_cases hcases
  have hs : IsSimpleGroup (kBar K) := by
    rcases hlist with h | h
    · exact isSimpleGroup_of_hasL2Model h
    · exact isSimpleGroup_of_alt7 h
  have hn : ∃ a b : kBar K, a * b ≠ b * a :=
    nonab_of_quasisimple (TwoThin.isQuasisimple_hat hA.twoTerminal.1.2.2)
  have hconj : ∀ a b : kBar K, orderOf a = 2 → orderOf b = 2 → IsConj a b :=
    fun a b ha hb => involutions_conj_of_model hlist a b ha hb
  obtain ⟨hQe, ⟨g, -, hgR, hgQ⟩, -, -⟩ := p91
  obtain ⟨-, hcomm, hPQ⟩ := hA.R_eq hs hn
  obtain ⟨z, hzP, hz2, hzc⟩ := exists_z hA (exists_involution_of_model hlist)
  have hz2' : z * z = 1 := by
    have := pow_orderOf_eq_one z
    rwa [hz2, sq] at this
  have hrk := card_le_sixteen hG
  obtain ⟨hQab, hQsq⟩ := forall_of_isElementaryAbelian hQe.1
  have hQE₁ : Q ≤ omegaZ (omegaOneT T) := fun q hq =>
    ⟨mem_omegaOneT (hQT hq) (hQsq q hq), fun w hw => hQZ q hq w hw, hQsq q hq⟩
  have hzE₁ : z ∈ omegaZ (omegaOneT T) :=
    ⟨mem_omegaOneT hzP.1 hz2', fun w hw => hzc w (omegaOneT_le T hw), hz2'⟩
  have hbig : 8 < Nat.card ↥(omegaZ (omegaOneT T)) := by
    by_contra hle
    push Not at hle
    exact claim112 hA hG.kproper h81 h92 hlist hs hn hconj hQe hgR hgQ hzP hz2
      (omegaOneT_le T) (omegaOneT_weakly_closed T) hQE₁ hzE₁ hle
  obtain ⟨hE16, hEinv⟩ := omegaZ_structure (T := T) (W := omegaOneT T)
    (fun u hu hu2 => mem_omegaOneT hu hu2) hrk hbig
  have hnc : ∀ a ∈ T ⊓ K, ∀ b ∈ T ⊓ K, a * a = 1 → b * b = 1 → a * b = b * a :=
    fun a ha b hb ha2 hb2 =>
      (hEinv a ha.1 ha2).2.1 b (omegaZ_le _ (hEinv b hb.1 hb2))
  have hK5 : HasL2Model (kBar K) (fun r => r = 5) := by
    rcases hcases with h | h | h | h
    · exact h
    · obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ :=
        exists_noncomm_in_P hA (Or.inl (hasL2Model_mono (fun r hr => Or.inl hr) h))
      exact absurd (hnc a ha b hb ha2 hb2) hab
    · obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ :=
        exists_noncomm_in_P hA (Or.inl (hasL2Model_mono (fun r hr => Or.inr hr) h))
      exact absurd (hnc a ha b hb ha2 hb2) hab
    · obtain ⟨a, ha, b, hb, ha2, hb2, hab⟩ := exists_noncomm_in_P hA (Or.inr h)
      exact absurd (hnc a ha b hb ha2 hb2) hab
  obtain ⟨e5⟩ := nonempty_alt5_of_hasL2Model5 hK5
  have hP4 : Nat.card ↥(T ⊓ K) = 4 := card_P_five hA e5
  have hQ4 : Nat.card ↥Q = 4 := hQe.2
  have hPsq : ∀ p ∈ T ⊓ K, p * p = 1 := by
    intro p hp
    have hp4 : p ^ 4 = 1 := by
      have h1 : (⟨p, hp⟩ : ↥(T ⊓ K)) ^ Nat.card ↥(T ⊓ K) = 1 := pow_card_eq_one'
      rw [hP4] at h1
      have h2 := congrArg (fun y : ↥(T ⊓ K) => (y : G)) h1
      simpa using h2
    have hpK : p ∈ K := hp.2
    have h3 : (QuotientGroup.mk (⟨p, hpK⟩ : ↥K) : kBar K) ^ 4 = 1 := by
      rw [← QuotientGroup.mk_pow]
      have : (⟨p, hpK⟩ : ↥K) ^ 4 = 1 := Subtype.ext (by simpa using hp4)
      rw [this]; rfl
    have h4 := a5_no_order_four e5 _ h3
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h4
    have hO : p ^ 2 ∈ pPrimeCoreOf 2 K := by
      refine Setup91.mem_pPrimeCoreOf_iff.2 ⟨K.pow_mem hpK 2, ?_⟩
      exact h4
    have hmem : p ^ 2 ∈ T ⊓ pPrimeCoreOf 2 K := ⟨T.pow_mem hp.1 2, hO⟩
    rw [Setup91.inf_pPrimeCoreOf_eq_bot K hTp, Subgroup.mem_bot] at hmem
    rw [← sq]; exact hmem
  have hPE : T ⊓ K ≤ omegaZ (omegaOneT T) := fun p hp => hEinv p hp.1 (hPsq p hp)
  have hRE : (T ⊓ K) ⊔ Q = omegaZ (omegaOneT T) :=
    Subgroup.eq_of_le_of_card_ge (sup_le hPE hQE₁)
      (Nat.le_of_eq (by
        have hc := Setup91.card_sup_Q hA hs hn
        rw [hE16, hc, hP4, hQ4]))
  have hR16 : Nat.card ↥((T ⊓ K) ⊔ Q) = 16 := by rw [hRE, hE16]
  have hRab : ∀ a ∈ (T ⊓ K) ⊔ Q, ∀ b ∈ (T ⊓ K) ⊔ Q, a * b = b * a := by
    rw [hRE]; exact (forall_of_isElementaryAbelian (omegaZ_isElementaryAbelian _)).1
  have hR2 : ∀ a ∈ (T ⊓ K) ⊔ Q, a * a = 1 := by
    rw [hRE]; exact (forall_of_isElementaryAbelian (omegaZ_isElementaryAbelian _)).2
  have hno : ∀ u ∈ T, u * u = 1 → u ∈ (T ⊓ K) ⊔ Q := fun u hu hu2 => by
    rw [hRE]; exact hEinv u hu hu2
  have hRT : (T ⊓ K) ⊔ Q = T := by
    by_contra hne
    have hlt : (T ⊓ K) ⊔ Q < T := lt_of_le_of_ne (sup_le inf_le_left hQT) hne
    obtain ⟨ψ, hψ⟩ := lemma113d_ne6 (K := K) (M := M) hA.L_normal.1 hA.L_normal.2
      (n := 5) (by norm_num) (by norm_num) e5
    have hidx : Nat.card ↥T ≤ 2 * Nat.card ↥((T ⊓ K) ⊔ Q) := by
      have := card_T_le hA ψ hψ
      rw [hR16]; rw [hQ4] at this; omega
    have hPn : ∀ t ∈ T, ∀ p ∈ T ⊓ K, t * p * t⁻¹ ∈ T ⊓ K := fun t ht p hp =>
      ⟨T.mul_mem (T.mul_mem ht hp.1) (T.inv_mem ht), hA.L_normal.2 t (hTM ht) p hp.2⟩
    have hQn : ∀ t ∈ T, ∀ q ∈ Q, t * q * t⁻¹ ∈ Q := fun t ht q hq => by
      have h1 : t * q * t⁻¹ ∈ T ⊓ CMK M K :=
        ⟨T.mul_mem (T.mul_mem ht (hQT hq)) (T.inv_mem ht),
          conj_mem_CMK hA.L_normal.2 (hTM ht) (hA.sylowQ.le hq)⟩
      rwa [T_inf_CMK hA] at h1
    obtain ⟨hQZT, hcardT⟩ := omegaZ_T_of_ne inf_le_left hQT hPn hQn hPQ hcomm hP4 hQ4 hRab hR2
      hR16 hno hidx (fun y hyT hyR => not_centralizes_P hA hs hn e5 hyT hyR) hlt
    have hzET : z ∈ omegaZ T := ⟨hzP.1, hzc, hz2'⟩
    exact claim112 hA hG.kproper h81 h92 hlist hs hn hconj hQe hgR hgQ hzP hz2 le_rfl
      (weakly_closed_self T) hQZT hzET hcardT
  refine Or.inr ⟨⟨e5⟩, hRT, ?_⟩
  have h5FM : IsFM9 5 := Or.inr ⟨by norm_num, Or.inl ⟨1, by norm_num⟩⟩
  rcases hh.b with hB1 | hB2
  · by_cases hterm : IsTerminalPair 2 x K
    · exfalso
      obtain ⟨y, hy⟩ := hB1.v2star
      exact not_v2_of_T_eq_R hA hcomm hRT h102a hG
        (hasL2Model_mono (fun r hr => by rw [hr]; exact h5FM) hK5) hy.1.1.1.1
    · exact hB1.nonTerminal hterm hQ4 (Or.inl ⟨e5⟩)
  · obtain ⟨eK⟩ := K_equiv_kBar_of_B2 hA hB2
    exact hB2.five ⟨eK.trans e5⟩ hRT.symm

end CFSG.GH74.GLS
