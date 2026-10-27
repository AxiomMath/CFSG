
module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHSBase

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutLocal
public import CFSG.Sporadic.Schreier.PairHSPairs
public import CFSG.Sporadic.Schreier.PairHSCertInputs
public import CFSG.Sporadic.Schreier.PairHSCheckInputs
public meta import CFSG.Sporadic.Schreier.PairHSCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairHSFaithfulInputs
public meta import CFSG.Sporadic.Schreier.PairF2Sep
public meta import Certificates.Data.CFSGNative.HS.Data
public meta import Certificates.Data.CFSGNative.HS.SmallF2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.SporAutHSInputs
public import Certificates.Certificate4052
public import Certificates.Data.CFSGNative.HS.Data
import CFSG.Sporadic.Schreier.Co3ChainUtil

public noncomputable section

namespace CFSG.QuasithinUnique.Ch1

open CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
  CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Blueprint

namespace SporAutHS

theorem s0_card : Nat.card s0Chain.originalSubgroup = 512 :=
  Certificates.certificate4052.1

theorem ltr_mem : ∀ k < 4, hsLtr k ∈ hsChain.originalSubgroup :=
  Certificates.certificate4052.2.1

theorem ltr_comm : ∀ k < 4, hsLtr 0 * hsLtr k = hsLtr k * hsLtr 0 :=
  Certificates.certificate4052.2.2.1

theorem b_conj :
    wordElt bWord * hsLtr 0 = wordElt yWord * wordElt bWord :=
  Certificates.certificate4052.2.2.2.1

theorem a1_word :
    hsGen 1 = wordElt t0Word * wordElt bWord ^ 2 * wordElt t1Word * wordElt bWord ^ 4 *
      wordElt t2Word :=
  Certificates.certificate4052.2.2.2.2.1

theorem b_orders :
    orderOf (wordElt bWord) = 15 ∧ orderOf (wordElt l1Word * wordElt bWord) = 5 ∧
      orderOf (wordElt l2Word * wordElt bWord) = 12 :=
  Certificates.certificate4052.2.2.2.2.2.1

theorem cnt_card :
    Nat.card {g : hsChain.originalSubgroup // CntPr g} = 2 :=
  Certificates.certificate4052.2.2.2.2.2.2

theorem s0_isPGroup : IsPGroup 2 s0Chain.originalSubgroup :=
  IsPGroup.of_card (n := 9) (by rw [s0_card]; norm_num)

theorem ltr_memP (k : ℕ) : hsLtr k ∈ hsChain.originalSubgroup := by
  by_cases hk : k < 4
  · exact ltr_mem k hk
  · rw [hsLtr, if_neg hk]
    exact hsGen_mem 1 (by norm_num)

theorem wordElt_mem :
    ∀ w : List ℕ, wordElt w ∈ hsChain.originalSubgroup
  | [] => by rw [wordElt_nil]; exact Subgroup.one_mem _
  | k :: w => by
    rw [wordElt_cons]
    exact Subgroup.mul_mem _ (ltr_memP k) (wordElt_mem w)

theorem s0_le_hs :
    s0Chain.originalSubgroup ≤ hsChain.originalSubgroup := by
  rw [s0Chain, CFSG.Sporadic.Schreier.Co3.ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  dsimp only
  rw [← ltr_lt hi]
  exact ltr_mem i hi

theorem s0_le_centralizer :
    s0Chain.originalSubgroup ≤ Subgroup.centralizer {hsGen 0} := by
  rw [s0Chain, CFSG.Sporadic.Schreier.Co3.ofArrays_originalSubgroup, Subgroup.closure_le]
  rintro _ ⟨⟨i, hi⟩, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  intro h hh
  rw [Set.mem_singleton_iff] at hh
  subst hh
  dsimp only
  rw [← ltr_lt hi, ← ltr_zero]
  exact ltr_comm i hi

theorem comm_A0 {s : Equiv.Perm (Fin 3850)}
    (hs : s ∈ s0Chain.originalSubgroup) : hsGen 0 * s = s * hsGen 0 :=
  Subgroup.mem_centralizer_iff.1 (s0_le_centralizer hs) _ (Set.mem_singleton _)

@[expose] def el (w : List ℕ) : hsChain.originalSubgroup :=
  ⟨wordElt w, wordElt_mem w⟩

theorem cntPr_conj_of {g : Equiv.Perm (Fin 3850)} (hg : CntPr g) :
    CntPr (hsGen 0 * g * (hsGen 0)⁻¹) := by
  obtain ⟨h1, h2, h3, h4⟩ := hg
  have cY := comm_A0 (wordElt_memS0 (w := yWord) (by decide))
  have c1 := comm_A0 (wordElt_memS0 (w := l1Word) (by decide))
  have c2 := comm_A0 (wordElt_memS0 (w := l2Word) (by decide))
  rw [ltr_zero] at h1
  have e : ∀ s : Equiv.Perm (Fin 3850), hsGen 0 * s = s * hsGen 0 →
      s * (hsGen 0 * g * (hsGen 0)⁻¹) = hsGen 0 * (s * g) * (hsGen 0)⁻¹ := fun s hs => by
    calc s * (hsGen 0 * g * (hsGen 0)⁻¹) = s * hsGen 0 * g * (hsGen 0)⁻¹ := by group
      _ = hsGen 0 * s * g * (hsGen 0)⁻¹ := by rw [hs]
      _ = hsGen 0 * (s * g) * (hsGen 0)⁻¹ := by group
  refine ⟨?_, by rw [orderOf_conj']; exact h2, by rw [e _ c1, orderOf_conj']; exact h3,
    by rw [e _ c2, orderOf_conj']; exact h4⟩
  rw [ltr_zero, e _ cY, ← h1]
  group

theorem hs_fixing_A1
    (α : MulAut hsChain.originalSubgroup)
    (hα : ∀ s : hsChain.originalSubgroup, (s : Equiv.Perm (Fin 3850)) ∈ s0Chain.originalSubgroup →
      α s = s) :
    α A0 = A0 ∧ (α A1 = A1 ∨ α A1 = A0 * A1 * A0⁻¹) := by
  have hS : ∀ w : List ℕ, (∀ k ∈ w, k < 4) → α (el w) = el w := fun w hw =>
    hα _ (wordElt_memS0 hw)
  have hc : ∀ w : List ℕ, (∀ k ∈ w, k < 4) → MulAut.conj A0 (el w) = el w := fun w hw => by
    have h : A0 * el w = el w * A0 := Subtype.ext (comm_A0 (wordElt_memS0 hw))
    rw [MulAut.conj_apply, h, mul_inv_cancel_right]
  have hA0 : α A0 = A0 := hα A0 hsGen_zero_memS0
  have hY := hS yWord (by decide)
  have hL1 := hS l1Word (by decide)
  have hL2 := hS l2Word (by decide)
  have hPrα : ∀ g : hsChain.originalSubgroup, CntPr g → CntPr (α g) := by
    intro g ⟨h1, h2, h3, h4⟩
    have ho : ∀ {w : List ℕ}, α (el w) = el w → ∀ {m : ℕ},
        orderOf (wordElt w * (g : Equiv.Perm (Fin 3850))) = m →
        orderOf (wordElt w * ((α g : hsChain.originalSubgroup) : Equiv.Perm (Fin 3850))) = m := by
      intro w hw m hm
      have e1 : (el w * α g : hsChain.originalSubgroup) = α (el w * g) := by rw [map_mul, hw]
      have e2 : wordElt w * ((α g : hsChain.originalSubgroup) : Equiv.Perm (Fin 3850)) =
          ((el w * α g : hsChain.originalSubgroup) : Equiv.Perm (Fin 3850)) := rfl
      rw [e2, Subgroup.orderOf_coe, e1, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact hm
    refine ⟨?_, ?_, ho hL1 h3, ho hL2 h4⟩
    · have h1' : (g : Equiv.Perm (Fin 3850)) * hsGen 0 = wordElt yWord * g := by
        rw [← ltr_zero]
        exact h1
      have e : g * A0 = el yWord * g := Subtype.ext h1'
      have := congrArg (fun x => ((x : hsChain.originalSubgroup) : Equiv.Perm (Fin 3850)))
        (congrArg α e)
      simp only [map_mul, hA0, hY] at this
      rw [ltr_zero]
      exact this
    · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe]
      exact h2
  have hPrB : CntPr (el bWord) := ⟨b_conj, b_orders.1, b_orders.2.1, b_orders.2.2⟩
  have hPrC : CntPr (A0 * el bWord * A0⁻¹ : hsChain.originalSubgroup) := cntPr_conj_of hPrB
  have hne : (⟨el bWord, hPrB⟩ : {g : hsChain.originalSubgroup // CntPr g}) ≠
      ⟨A0 * el bWord * A0⁻¹, hPrC⟩ := by
    intro h
    have hb : el bWord = A0 * el bWord * A0⁻¹ := congrArg Subtype.val h
    have hb' : el bWord * A0 = A0 * el bWord := by
      conv_lhs => rw [hb]
      group
    have cb : Commute (hsGen 0) (wordElt bWord) := (congrArg Subtype.val hb').symm
    have ct : ∀ w : List ℕ, (∀ k ∈ w, k < 4) → Commute (hsGen 0) (wordElt w) := fun w hw =>
      comm_A0 (wordElt_memS0 hw)
    have c1 : Commute (hsGen 0) (hsGen 1) := by
      rw [a1_word]
      exact ((((ct t0Word (by decide)).mul_right (cb.pow_right 2)).mul_right
        (ct t1Word (by decide))).mul_right (cb.pow_right 4)).mul_right
        (ct t2Word (by decide))
    refine A1_ne_conj (Subtype.ext ?_)
    change hsGen 1 = hsGen 0 * hsGen 1 * (hsGen 0)⁻¹
    rw [c1.eq, mul_inv_cancel_right]
  have hall := SporAut.eq_or_eq_of_card_two cnt_card _ _ hne ⟨α (el bWord), hPrα _ hPrB⟩
  have hA1 : A1 = el t0Word * el bWord ^ 2 * el t1Word * el bWord ^ 4 * el t2Word :=
    Subtype.ext a1_word
  have hT0 := hS t0Word (by decide)
  have hT1 := hS t1Word (by decide)
  have hT2 := hS t2Word (by decide)
  refine ⟨hA0, ?_⟩
  rcases hall with h | h
  · left
    have hB : α (el bWord) = el bWord := congrArg Subtype.val h
    rw [hA1]
    simp only [map_mul, map_pow, hT0, hT1, hT2, hB]
  · right
    have hB : α (el bWord) = MulAut.conj A0 (el bWord) := by
      rw [MulAut.conj_apply]
      exact congrArg Subtype.val h
    have e : α A1 = MulAut.conj A0 A1 := by
      rw [hA1]
      simp only [map_mul, map_pow, hT0, hT1, hT2, hB, hc t0Word (by decide),
        hc t1Word (by decide), hc t2Word (by decide)]
    rwa [MulAut.conj_apply] at e

theorem hs_fixing_inner (α : MulAut hsChain.originalSubgroup)
    (hα : ∀ s : hsChain.originalSubgroup, (s : Equiv.Perm (Fin 3850)) ∈ s0Chain.originalSubgroup →
      α s = s) :
    ∃ c : hsChain.originalSubgroup, ∀ x, α x = c * x * c⁻¹ := by
  obtain ⟨hA0, hA1⟩ := hs_fixing_A1 α hα
  exact SporAut.exists_conj_of_pair A0 A1 closure_A0_A1 α hA0 hA1

end SporAutHS

theorem hsAutInner (K : Type) [Group K] [Finite K] (hK : Nonempty (K ≃* NativeSporadic.HS))
    (β : K ≃* K) (hP : ∃ P : Sylow 2 K, ∀ t ∈ (P : Subgroup K), β t = t) : IsInnerAut β := by
  obtain ⟨e⟩ := hK
  let ψ : K ≃* hsChain.originalSubgroup :=
    e.trans (hsPermEquiv.trans (MulEquiv.subgroupCongr hsP_eq_original))
  let T : Subgroup hsChain.originalSubgroup :=
    SporAutHS.s0Chain.originalSubgroup.subgroupOf hsChain.originalSubgroup
  have hT : IsPGroup 2 T := SporAutHS.s0_isPGroup.comap_subtype
  obtain ⟨S₁, hS₁⟩ := hT.exists_le_sylow
  exact SporAut.isInnerAut_of_fixing_sylow ψ S₁
    (fun α hα => SporAutHS.hs_fixing_inner α fun s hs =>
      hα s (hS₁ (Subgroup.mem_subgroupOf.2 hs))) β hP

end CFSG.QuasithinUnique.Ch1
