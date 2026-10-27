module

public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3Wreathed
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SmallIndex
public import CFSG.LieType.BorelTits.Basic
public import CFSG.Walter.PSL2Facts.Even

public section

namespace CFSG.ComponentClassification.AschbacherTheorem3

open CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ABGLocalTools
open CFSG.Open
open CFSG.SignalizerFunctor.Helpers
open scoped Pointwise MatrixGroups commutatorElement

variable {X : Type} [Group X] [Finite X]

namespace Hyp3

variable {Q T P S : Subgroup X}

theorem hyp43 (h : Hyp3 Q T P S) :
    Hyp43 Q T P ((Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X)) where
  le := le_inf h.le_sup Subgroup.le_normalizer
  le_normalizer := inf_le_right
  le_sup := inf_le_left
  sylow := h.sylow_P
  inf_eq_bot := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    intro g hg hgH
    set L := Q ⊔ T with hLdef
    have hgL : g ∈ L := Subgroup.mem_sup_left hg
    have hgN : g ∉ Subgroup.normalizer (P : Set X) := fun hgN => hgH ⟨hgL, hgN⟩
    have hPL : P ≤ L := h.le_sup
    have hnot : (⟨g, hgL⟩ : L) ∉
        Subgroup.normalizer ((P.subgroupOf L : Subgroup L) : Set L) := by
      rw [← Subgroup.subgroupOf_normalizer_eq hPL, Subgroup.mem_subgroupOf]
      exact hgN
    have hodd := h.tightlyEmbedded.2 ⟨g, hgL⟩ hnot
    have hmapP : (P.subgroupOf L).map L.subtype = P := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPL]
    have hmap : ((P.subgroupOf L) ⊓ rightConjugate (P.subgroupOf L) ⟨g, hgL⟩).map L.subtype =
        P ⊓ rightConjugate P g := by
      rw [Subgroup.map_inf_eq _ _ _ L.subtype_injective, map_rightConjugate, hmapP]
      rfl
    have hodd' : Odd (Nat.card (P ⊓ rightConjugate P g : Subgroup X)) := by
      rw [← hmap, Subgroup.card_map_of_injective L.subtype_injective]
      exact hodd
    have hle : T ⊓ rightConjugate T g ≤ P ⊓ rightConjugate P g :=
      inf_le_inf h.sylow_P.le (rightConjugate_le_rightConjugate h.sylow_P.le g)
    have h2 : IsPGroup 2 (T ⊓ rightConjugate T g : Subgroup X) :=
      h.sylowFrame.isPGroup.to_le inf_le_left
    obtain ⟨k, hk⟩ := h2.exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le hle
    rcases k with _ | k
    · exact Subgroup.card_eq_one.mp (by simpa using hk)
    · exfalso
      rw [hk, pow_succ] at hdvd
      exact Nat.not_even_iff_odd.mpr hodd'
        (even_iff_two_dvd.mpr ((dvd_mul_left 2 _).trans hdvd))

theorem inf_H (h : Hyp3 Q T P S) :
    S ⊓ ((Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X)) = S ⊓ Subgroup.normalizer (T : Set X) := by
  have h43 := h.hyp43
  apply le_antisymm
  · exact le_inf inf_le_left (h43.le_normalizer_of_le h.sylowFrame.sylow.isPGroup.to_inf_left
      (le_inf h.sylowFrame.le h43.le_H) inf_le_right)
  · exact le_inf inf_le_left ((inf_le_inf_right _ h.sylowFrame.sylow.le).trans
      (h43.normalizer_le h.sylowFrame.toFrame h.ne_bot))

end Hyp3

theorem pCoreOf_le_of_isSylowOf {S K : Subgroup X} (hS : IsSylowOf 2 S K) :
    pCoreOf 2 K ≤ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 (pCoreOf 2 K) := LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hSN : S ≤ Subgroup.normalizer (pCoreOf 2 K : Set X) :=
    hS.le.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hsup : IsPGroup 2 (S ⊔ pCoreOf 2 K : Subgroup X) :=
    IsPGroup.to_sup_of_normal_right' hS.isPGroup hO2 hSN
  have heq := hS.eq_of_le le_sup_left (sup_le hS.le (LieType.BorelTits.pCoreOf_le 2 K)) hsup
  exact le_sup_right.trans heq.le

omit [Finite X] in
theorem sup_inf_le_of_inf_eq_bot {N K Q : Subgroup X} (hKQ : K ≤ Q)
    (hKN : K ≤ Subgroup.normalizer (N : Set X)) (hNQ : N ⊓ Q = ⊥) : (N ⊔ K) ⊓ Q ≤ K := by
  rintro x ⟨hx, hxQ⟩
  have hx' : x ∈ (N : Set X) * (K : Set X) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left N K hKN]
    exact hx
  obtain ⟨o, ho, k, hk, rfl⟩ := Set.mem_mul.mp hx'
  have hoQ : o ∈ Q := by simpa using Q.mul_mem hxQ (Q.inv_mem (hKQ hk))
  have ho1 : o = 1 := by
    have hmem : o ∈ N ⊓ Q := ⟨ho, hoQ⟩
    rwa [hNQ, Subgroup.mem_bot] at hmem
  rw [ho1, one_mul]
  exact hk

theorem oTwoPrime_eq_commutator {Q T S : Subgroup X} {g : X} (hF : Frame Q T)
    (hS : IsSylowOf 2 S (Q ⊔ T)) (hg : g ∈ Q)
    (hN : S ⊓ Subgroup.normalizer (T : Set X) = T ⊔ rightConjugate T g)
    (hTK : T ≤ Subgroup.centralizer (rightConjugate T g : Set X))
    (h2 : oTwoPrime (Q ⊔ T) = pCoreOf 2 (Q ⊔ T) ⊔ ⁅T, Q⁆)
    (hinf : pCoreOf 2 (Q ⊔ T) ⊓ ⁅T, Q⁆ = ⊥) (hcomm : ⁅pCoreOf 2 (Q ⊔ T), ⁅T, Q⁆⁆ = ⊥) :
    oTwoPrime Q = ⁅T, Q⁆ := by
  set O₂ := pCoreOf 2 (Q ⊔ T) with hO₂def
  set L := ⁅T, Q⁆ with hLdef
  have hLQ : L ≤ Q := by
    rw [hLdef, Subgroup.commutator_comm]
    exact hF.commutator_le
  have hO₂N : Q ⊔ T ≤ Subgroup.normalizer (O₂ : Set X) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 (Q ⊔ T)
  have hQN : Q ≤ Subgroup.normalizer (O₂ : Set X) := le_sup_left.trans hO₂N
  have hO₂S : O₂ ≤ S := pCoreOf_le_of_isSylowOf hS
  have hWQ : (T ⊔ rightConjugate T g) ⊓ Q ≤ L := by
    rintro w ⟨hw, hwQ⟩
    have hTN : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
      hTK.trans (Subgroup.centralizer_le_normalizer _)
    have hw' : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTN]
      exact hw
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hw'
    set t' := g * b * g⁻¹ with ht'def
    have ht' : t' ∈ T := (mem_rightConjugate_iff T g b).mp hb
    have hcomm' : t'⁻¹ * b ∈ L := by
      have hmem := Subgroup.commutator_mem_commutator (T.inv_mem ht') (Q.inv_mem hg)
      rw [commutatorElement_def] at hmem
      simpa [ht'def, mul_assoc] using hmem
    have hat : a * t' ∈ T ⊓ Q := by
      refine ⟨T.mul_mem ha ht', ?_⟩
      have := Q.mul_mem hwQ (Q.inv_mem (hLQ hcomm'))
      simpa [mul_assoc] using this
    rw [hF.inf_eq_bot, Subgroup.mem_bot] at hat
    have hb' : a * b = (a * t') * (t'⁻¹ * b) := by group
    rw [hb', hat, one_mul]
    exact hcomm'
  have hO₂Q : O₂ ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    rintro r ⟨hrO, hrQ⟩
    have hrC : r ∈ Subgroup.centralizer (T : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      have hc : ⁅r, t⁆ ∈ O₂ ⊓ L := by
        refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          have h1 : t * r⁻¹ * t⁻¹ ∈ O₂ :=
            (Subgroup.mem_normalizer_iff.mp (hO₂N (Subgroup.mem_sup_right ht)) _).mp
              (O₂.inv_mem hrO)
          simpa [mul_assoc] using O₂.mul_mem hrO h1
        · rw [hLdef, Subgroup.commutator_comm]
          exact Subgroup.commutator_mem_commutator hrQ ht
      rw [hinf, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
      exact hc.symm
    have hrW : r ∈ T ⊔ rightConjugate T g := by
      rw [← hN]
      exact ⟨hO₂S hrO, Subgroup.centralizer_le_normalizer _ hrC⟩
    have hrL : r ∈ O₂ ⊓ L := ⟨hrO, hWQ ⟨hrW, hrQ⟩⟩
    rwa [hinf] at hrL
  apply le_antisymm
  ·
    have hle : oTwoPrime Q ≤ (O₂ ⊔ L) ⊓ Q := by
      refine le_inf ?_ ((Subgroup.closure_le Q).mpr fun x hx => hx.1)
      rw [← h2]
      exact Subgroup.closure_mono fun x hx => ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
    exact hle.trans (sup_inf_le_of_inf_eq_bot hLQ (hLQ.trans hQN) hO₂Q)
  ·
    have hOQ : oTwoPrime Q ≤ Q := (Subgroup.closure_le Q).mpr fun x hx => hx.1
    have hle : L ≤ (O₂ ⊔ oTwoPrime Q) ⊓ Q := by
      refine le_inf ?_ hLQ
      refine le_sup_right.trans (h2.symm.le.trans ?_)
      rw [oTwoPrime, Subgroup.closure_le]
      rintro x ⟨hxL, k, hxk⟩
      have hx2 : x ∈ O₂ ⊔ L := by
        rw [← h2]
        exact Subgroup.subset_closure ⟨hxL, k, hxk⟩
      have hx' : x ∈ (O₂ : Set X) * (L : Set X) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left O₂ L (hLQ.trans hQN)]
        exact hx2
      obtain ⟨o, ho, l, hl, rfl⟩ := Set.mem_mul.mp hx'
      have hol : o * l = l * o := by
        have hc := Subgroup.commutator_mem_commutator ho hl
        rw [hcomm, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hc
        exact hc
      have hlk : l ^ (2 ^ k) = 1 := by
        have h1 : o ^ (2 ^ k) * l ^ (2 ^ k) = 1 := by
          rw [← (Commute.mul_pow hol), hxk]
        have hmem : l ^ (2 ^ k) ∈ O₂ ⊓ L := by
          refine ⟨?_, L.pow_mem hl _⟩
          rw [eq_inv_of_mul_eq_one_right h1]
          exact O₂.inv_mem (O₂.pow_mem ho _)
        rwa [hinf, Subgroup.mem_bot] at hmem
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho)
        (Subgroup.mem_sup_right (Subgroup.subset_closure ⟨hLQ hl, k, hlk⟩))
    exact hle.trans (sup_inf_le_of_inf_eq_bot hOQ (hOQ.trans hQN) hO₂Q)

theorem isMulCommutative_of_psl {Q T S : Subgroup X} {n : ℕ} (hF : Frame Q T) (hn : 2 ≤ n)
    (hS : IsSylowOf 2 S (Q ⊔ T)) (h2 : oTwoPrime (Q ⊔ T) = pCoreOf 2 (Q ⊔ T) ⊔ ⁅T, Q⁆)
    (hcomm : ⁅pCoreOf 2 (Q ⊔ T), ⁅T, Q⁆⁆ = ⊥) (hel : IsElemAbelian 2 (pCoreOf 2 (Q ⊔ T)))
    (e : (⁅T, Q⁆ : Subgroup X) ≃* PSL(2, GaloisField 2 n)) : IsMulCommutative S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O₂ := pCoreOf 2 (Q ⊔ T) with hO₂def
  set L := ⁅T, Q⁆ with hLdef
  have hLQ : L ≤ Q := by
    rw [hLdef, Subgroup.commutator_comm]
    exact hF.commutator_le
  have hLN : L ≤ Subgroup.normalizer (O₂ : Set X) :=
    (hLQ.trans le_sup_left).trans (LieType.BorelTits.le_normalizer_pCoreOf 2 (Q ⊔ T))
  have hO₂S : O₂ ≤ S := pCoreOf_le_of_isSylowOf hS
  have hSO : S ≤ oTwoPrime (Q ⊔ T) := by
    intro s hs
    obtain ⟨k, hk⟩ := hS.isPGroup ⟨s, hs⟩
    exact Subgroup.subset_closure ⟨hS.le hs, k, congrArg Subtype.val hk⟩
  have hSL : ∀ x ∈ S ⊓ L, ∀ y ∈ S ⊓ L, x * y = y * x := by
    intro x hx y hy
    have hP : IsPGroup 2 (((S ⊓ L).subgroupOf L).map e.toMonoidHom) :=
      ((hS.isPGroup.to_le inf_le_left).comap_subtype).map _
    obtain ⟨U, hU⟩ := hP.exists_le_sylow
    have hUab := (CFSG.Walter.psl2_even_sylow_two hn U).1
    have hx' : e ⟨x, hx.2⟩ ∈ (U : Subgroup _) :=
      hU ⟨⟨x, hx.2⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    have hy' : e ⟨y, hy.2⟩ ∈ (U : Subgroup _) :=
      hU ⟨⟨y, hy.2⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
    have hc : e ⟨x, hx.2⟩ * e ⟨y, hy.2⟩ = e ⟨y, hy.2⟩ * e ⟨x, hx.2⟩ :=
      congrArg Subtype.val (hUab.toIsMulCommutative.is_comm.comm ⟨_, hx'⟩ ⟨_, hy'⟩)
    rw [← map_mul, ← map_mul] at hc
    exact congrArg Subtype.val (e.injective hc)
  have hSLab : IsMulCommutative (S ⊓ L : Subgroup X) :=
    ⟨⟨fun a b => Subtype.ext (hSL a a.2 b b.2)⟩⟩
  have hO₂C : O₂ ≤ Subgroup.centralizer ((S ⊓ L : Subgroup X) : Set X) :=
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_right))
  have hSsub : S ≤ O₂ ⊔ (S ⊓ L) := by
    intro s hs
    have hs2 : s ∈ O₂ ⊔ L := h2 ▸ hSO hs
    have hs' : s ∈ (O₂ : Set X) * (L : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left O₂ L hLN]
      exact hs2
    obtain ⟨o, ho, l, hl, rfl⟩ := Set.mem_mul.mp hs'
    have hlS : l ∈ S := by simpa using S.mul_mem (S.inv_mem (hO₂S ho)) hs
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ho) (Subgroup.mem_sup_right ⟨hlS, hl⟩)
  exact isMulCommutative_of_le hSsub (isMulCommutative_sup hel.1 hSLab hO₂C)

theorem isCyclic_of_pRank_le_one {T : Subgroup X} (hT : IsPGroup 2 T) (hab : IsMulCommutative T)
    (hr : ¬ 1 < pRank 2 T) : IsCyclic T := by
  have hone : AschbacherToolkit.AtMostOneInvolution T := by
    intro s t hs ht
    by_contra hst
    have hs2 : (s : X) ^ 2 = 1 := by rw [← Subgroup.coe_pow, ← hs, pow_orderOf_eq_one]; rfl
    have ht2 : (t : X) ^ 2 = 1 := by rw [← Subgroup.coe_pow, ← ht, pow_orderOf_eq_one]; rfl
    have hs1 : (s : X) ≠ 1 := fun h1 => by
      rw [show s = 1 from Subtype.ext h1, orderOf_one] at hs
      omega
    have ht1 : (t : X) ≠ 1 := fun h1 => by
      rw [show t = 1 from Subtype.ext h1, orderOf_one] at ht
      omega
    have hst' : (s : X) ≠ t := fun h1 => hst (Subtype.ext h1)
    have hc : (s : X) * t = t * s := congrArg Subtype.val (hab.is_comm.comm s t)
    have := two_le_pRank_of_involutions s.2 t.2 hs2 ht2 hs1 ht1 hst' hc
    omega
  rcases isCyclic_or_isQuaternion_of_atMostOneInvolution hT hone with h | ⟨n, hn, ⟨e⟩⟩
  · exact h
  · exfalso
    set m := 2 ^ (n - 2) with hmdef
    have hm2 : 2 ≤ m := by
      rw [hmdef]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (n - 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hc := congrArg e (hab.is_comm.comm (e.symm (QuaternionGroup.a 1))
      (e.symm (QuaternionGroup.xa 0)))
    rw [map_mul, map_mul, e.apply_symm_apply, e.apply_symm_apply, QuaternionGroup.a_mul_xa,
      QuaternionGroup.xa_mul_a, QuaternionGroup.xa.injEq] at hc
    have h2 : ((2 : ℕ) : ZMod (2 * m)) = 0 := by
      have : (2 : ZMod (2 * m)) = 0 := by
        calc (2 : ZMod (2 * m)) = (0 + 1) - (0 - 1) := by ring
          _ = 0 := by rw [hc]; ring
      exact_mod_cast this
    rw [ZMod.natCast_eq_zero_iff] at h2
    have := Nat.le_of_dvd two_pos h2
    omega

theorem Hyp45.exists_conj_not_le {G T S Q H : Subgroup X} {g : X} (h : Hyp45 G T S Q H g)
    (hHS : H ⊓ S = T ⊔ rightConjugate T g)
    (hWM : relativeWeakClosure G T S ≠ T ⊔ rightConjugate T g) :
    ∃ y ∈ G, rightConjugate T y ≤
        S ⊓ Subgroup.normalizer ((T ⊔ rightConjugate T g : Subgroup X) : Set X) ∧
      ¬ rightConjugate T y ≤ T ⊔ rightConjugate T g := by
  have hMeq : relativeWeakClosure G T (T ⊔ rightConjugate T g) = T ⊔ rightConjugate T g :=
    le_antisymm (relative_weak_closure_le _ _ _)
      (sup_le (subgroup_le_relative_weak_closure _ _ _ le_sup_left)
        (rightConjugate_le_relativeWeakClosure h.mem le_sup_right))
  by_contra hcon
  push Not at hcon
  apply hWM
  refine le_antisymm (relativeWeakClosure_le_of_normalizer h.frame h.isPGroup_S h.le_sup
    (hHS ▸ inf_le_right) hMeq fun c hc hle => hcon c hc hle) ?_
  exact sup_le (subgroup_le_relative_weak_closure _ _ _ h.le_S)
    (rightConjugate_le_relativeWeakClosure h.mem (h.conj_le.trans inf_le_right))

theorem theorem_3_of_theorem_4_8 (h48 : Theorem48Statement) : Theorem3Statement := by
  intro X _ _ Q T P S h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := (Q ⊔ T) ⊓ Subgroup.normalizer (P : Set X) with hHdef
  have h43 := h.hyp43
  have hsf := h.sylowFrame
  have hF := hsf.toFrame
  have hT := h.ne_bot
  have hO := h.oddCore_eq_bot
  have hTS := hsf.le
  have hS2 := hsf.sylow.isPGroup
  have hSGT := hsf.sylow.le
  have hsize : T.relIndex (S ⊓ H) ≤ Nat.card T := by
    rw [h.inf_H]
    exact h.index_le
  unfold Thm3Conclusion
  by_cases hW : relativeWeakClosure Q T S = T
  ·
    right; left
    have hwc : ∀ g ∈ Q, rightConjugate T g ≤ S → rightConjugate T g = T := by
      intro g hg hle
      have h1 := rightConjugate_le_relativeWeakClosure hg hle
      rw [hW] at h1
      exact Subgroup.eq_of_le_of_card_ge h1 (rightConjugate_card T g).ge
    refine sup_le ?_ Subgroup.le_normalizer
    exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (lemma_4_2 hsf hwc hO)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨g, hg, hgN, hne⟩ := exists_conj_le_normalizer hF hS2 hSGT hTS hW
  have hNH : S ⊓ Subgroup.normalizer (T : Set X) ≤ H :=
    (inf_le_inf_right _ hSGT).trans (h43.normalizer_le hF hT)
  have hgSH : rightConjugate T g ≤ S ⊓ H := le_inf (hgN.trans inf_le_left) (hgN.trans hNH)
  obtain ⟨-, hinf, hcomm, habel⟩ := lemma_4_4_two hF h43 hS2 hTS hg hgSH hne
  have hKN : rightConjugate T g ≤ Subgroup.normalizer (T : Set X) := hgN.trans inf_le_right
  have hcardM : Nat.card (T ⊔ rightConjugate T g : Subgroup X) = Nat.card T * Nat.card T := by
    rw [card_sup_of_le_normalizer hKN hinf, rightConjugate_card]
  have hMle : T ⊔ rightConjugate T g ≤ H ⊓ S :=
    le_inf (sup_le h43.le_H (hgSH.trans inf_le_right)) (sup_le hTS (hgSH.trans inf_le_left))
  have hcardHS : Nat.card (H ⊓ S : Subgroup X) ≤ Nat.card T * Nat.card T := by
    have h1 := Subgroup.relIndex_mul_card T (S ⊓ H)
    rw [inf_eq_left.mpr (le_inf hTS h43.le_H)] at h1
    rw [inf_comm, ← h1]
    exact Nat.mul_le_mul_right _ hsize
  have hHS : H ⊓ S = T ⊔ rightConjugate T g :=
    (Subgroup.eq_of_le_of_card_ge hMle (hcardHS.trans hcardM.ge)).symm
  have h45 : Hyp45 Q T S P H g :=
    { sylowFrame := hsf
      hyp43 := h43
      mem := hg
      ne := hne
      weakClosure := le_antisymm (by rw [← hHS]; exact relative_weak_closure_le _ _ _)
        (sup_le (subgroup_le_relative_weak_closure _ _ _ (hHS ▸ le_sup_left))
          (rightConjugate_le_relativeWeakClosure hg (hHS ▸ le_sup_right))) }
  have hTab : IsMulCommutative T := isMulCommutative_of_le le_sup_left habel
  have hSNW : S ≤ Subgroup.normalizer (relativeWeakClosure Q T S : Set X) :=
    le_normalizer_relativeWeakClosure hF hSGT hTS
  have hTW : T ≤ Subgroup.normalizer (relativeWeakClosure Q T S : Set X) :=
    (subgroup_le_relative_weak_closure _ _ _ hTS).trans Subgroup.le_normalizer
  by_cases hm : 1 < pRank 2 T
  · by_cases hWM : relativeWeakClosure Q T S = T ⊔ rightConjugate T g
    ·
      rcases h48 X Q T S P H hsf h43 hsize hO hm with
        hN | ⟨n, hn, h2, hinf2, hcomm2, hel, hcard, ⟨e⟩⟩
      · right; right; right; left
        refine ⟨g, hg, hWM, hinf, hcomm, ?_, sup_le hN hTW, hTab, ?_⟩
        · rw [hWM, ← hHS, h45.inf_eq_normalizer]
        · intro hq
          have hq' : QuotientRankTwo (S ⊓ Subgroup.normalizer ((H ⊓ S : Subgroup X) : Set X))
              (H ⊓ S) := by
            rw [hHS, ← hWM, inf_eq_left.mpr hSNW]
            exact hq
          exact le_antisymm (omegaOne_le T) (le_omegaOne (lemma_4_5_three h45 hq').2)
      · right; right; left
        have hNT : S ⊓ Subgroup.normalizer (T : Set X) = T ⊔ rightConjugate T g := by
          rw [← h45.inf_eq_normalizer, hHS]
        have hO2 := oTwoPrime_eq_commutator hF hsf.sylow hg hNT
          (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) h2 hinf2 hcomm2
        refine ⟨n, hn, ?_, ?_, ?_, hel, hcard, ⟨?_⟩⟩
        · rw [hO2]; exact h2
        · rw [hO2]; exact hinf2
        · rw [hO2]; exact hcomm2
        · rw [hO2]; exact e
    ·
      obtain ⟨y, hy, hyN, hyM⟩ := h45.exists_conj_not_le hHS hWM
      have e47 : Elem47 Q T S P H g y := ⟨h45, hHS, hm, hy, hyN, hyM⟩
      obtain ⟨hel, hcardW, hZ1, hZ2, hidx⟩ := e47.conclusion
      rcases h48 X Q T S P H hsf h43 hsize hO hm with
        hN | ⟨n, hn, h2, -, hcomm2, hel2, -, ⟨e⟩⟩
      · right; right; right; right
        refine ⟨sup_le hN hTW, hcardW, hZ1, hZ2, ?_,
          le_antisymm (omegaOne_le T) (le_omegaOne hel.2), hidx⟩
        rw [e47.weakClosure_eq, e47.center_eq]
        obtain ⟨φ⟩ := h45.nonempty_mulEquiv_inf
        exact ⟨φ.symm⟩
      · exfalso
        have hSab := isMulCommutative_of_psl hF hn hsf.sylow h2 hcomm2 hel2 e
        have hWab : IsMulCommutative (relativeWeakClosure Q T S) :=
          isMulCommutative_of_le (relative_weak_closure_le _ _ _) hSab
        have hbot : ⁅relativeWeakClosure Q T S, relativeWeakClosure Q T S⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
            (Subgroup.le_centralizer_iff_isMulCommutative.mpr hWab)
        rw [← hZ1, e47.weakClosure_eq, e47.center_eq] at hbot
        exact h45.W_inf_G_ne_bot hbot
  ·
    left
    have hcyc : IsCyclic T := isCyclic_of_pRank_le_one hsf.isPGroup hTab hm
    by_cases hT2 : Nat.card T = 2
    ·
      obtain ⟨t₀, ht₀, ht₀2, -⟩ := exists_center_involution hsf.isPGroup hT
      have ht₀1 : t₀ ≠ 1 := by
        rintro rfl
        rw [orderOf_one] at ht₀2
        omega
      have hsqT : ∀ t ∈ T, t ^ 2 = 1 := by
        intro t ht
        have h1 : (⟨t, ht⟩ : T) ^ Nat.card T = 1 := pow_card_eq_one'
        rw [hT2] at h1
        exact congrArg Subtype.val h1
      have hTK : T ≤ Subgroup.normalizer (rightConjugate T g : Set X) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
          (Subgroup.centralizer_le_normalizer _)
      have hsqM : ∀ w ∈ T ⊔ rightConjugate T g, w ^ 2 = 1 := by
        intro w hw
        have hwmem : w ∈ (T : Set X) * (rightConjugate T g : Set X) := by
          rw [← Subgroup.coe_mul_of_left_le_normalizer_right T _ hTK]
          exact hw
        obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hwmem
        have hab : a * b = b * a :=
          (Subgroup.mem_centralizer_iff.mp
            (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm ha) b hb).symm
        have hb2 : b ^ 2 = 1 := by
          have hb' : g * b * g⁻¹ ∈ T := (mem_rightConjugate_iff T g b).mp hb
          rw [show b ^ 2 = g⁻¹ * (g * b * g⁻¹) ^ 2 * g by simp only [pow_two]; group,
            hsqT _ hb']
          group
        calc (a * b) ^ 2 = a * (b * a) * b := by simp only [pow_two, mul_assoc]
          _ = a * (a * b) * b := by rw [hab]
          _ = a ^ 2 * b ^ 2 := by simp only [pow_two, mul_assoc]
          _ = 1 := by rw [hsqT a ha, hb2, one_mul]
      have hC := lemma_4_5_one h45 ht₀ ht₀1
      have hcardC : Nat.card (Subgroup.centralizer ({⟨t₀, hTS ht₀⟩} : Set S)) = 4 := by
        rw [card_centralizer_subtype, ← hC, hHS, hcardM, hT2]
      have hexpC : ∀ x ∈ Subgroup.centralizer ({⟨t₀, hTS ht₀⟩} : Set S), x ^ 2 = 1 := by
        intro x hx
        have hxC : (x : X) ∈ S ⊓ Subgroup.centralizer {t₀} := by
          refine Subgroup.mem_inf.mpr ⟨x.2, ?_⟩
          rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
          exact congrArg Subtype.val hx
        rw [← hC, hHS] at hxC
        exact Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hsqM _ hxC)
      have hSQ : IsCyclic (S ⊓ Q : Subgroup X) ∨ IsQuaternionTwoGroup (S ⊓ Q) ∨
          IsDihedralTwoGroup (S ⊓ Q) := by
        apply shape_of_index_two hS2 inf_le_left _ (hTS ht₀) _ ht₀2
        · have heq : (S ⊓ Q) ⊓ Subgroup.centralizer {t₀} = (T ⊔ rightConjugate T g) ⊓ Q := by
            rw [← hHS, hC, inf_right_comm]
          rw [heq, h45.card_W_inf_G, hT2]
        · have h1 := hF.card_eq_mul hSGT hTS
          have h2 := Subgroup.relIndex_mul_card (S ⊓ Q) S
          rw [inf_eq_left.mpr inf_le_left, h1, hT2] at h2
          exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
        · intro hmem
          have hmem' : t₀ ∈ T ⊓ Q := ⟨ht₀, hmem.2⟩
          rw [hF.inf_eq_bot, Subgroup.mem_bot] at hmem'
          exact ht₀1 hmem'
      refine ⟨hcyc, hSQ, ?_⟩
      rcases AschbacherToolkit.suzuki_two_group (P := S) hS2 hcardC hexpC with hD | hSD
      · exact Or.inl hD
      · exact Or.inr (Or.inl hSD)
    ·
      have hWM : relativeWeakClosure Q T S = T ⊔ rightConjugate T g := by
        by_contra hWM
        obtain ⟨y, hy, hyN, hyM⟩ := h45.exists_conj_not_le hHS hWM
        exact hT2 (card_eq_two_of_pRank_le_one h45 hm hy hyN hyM)
      have hT4 : 2 < Nat.card T := by
        have h1 : Nat.card T ≠ 1 := fun h1 => hT (Subgroup.card_eq_one.mp h1)
        have h0 : 0 < Nat.card T := Nat.card_pos
        omega
      obtain ⟨hwr, hshape⟩ := h45.wreathed_case hHS hWM hcyc hT4 hO
      exact ⟨hcyc, hshape, Or.inr (Or.inr hwr)⟩

end CFSG.ComponentClassification.AschbacherTheorem3
