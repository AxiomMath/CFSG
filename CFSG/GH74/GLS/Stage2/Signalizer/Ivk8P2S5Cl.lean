module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5ClAux
public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Xd
public import CFSG.GH74.GLS.Stage2.Final.Thm4.Stmt17
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Lemma27Infra

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Main

theorem claim18Xd_of (hB12 : Bender12) (h171 : Prop17_1) (hAB : IG_11_7) (h178 : Prop17_8) :
    Claim18Xd := by
  intro G _ _ z k S M p E t hctx d hdE hd1 hdM hXd
  classical
  have hF := S5Facts.of_ctx h171 hctx
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.odd
  obtain ⟨hzC, hVC, hF1, hF2⟩ := centralizer_facts hB12 h171 hctx hdE
  set C : Subgroup G := centralizer ({d} : Set G) with hCdef
  set N : Subgroup G := normalizer ((zpowers d : Subgroup G) : Set G) with hNdef
  have hCN : C ≤ N := centralizer_le_normalizer_zpowers d
  have hNC : N ≤ normalizer (C : Set G) := normalizer_zpowers_le_normalizer_centralizer d
  have hdP : d ∈ Op p M := hctx.E_le hdE
  have hdFm : d ∈ Fm M := (Op_le_Fm p hp M) hdP
  have hFmFs : ∀ L : Subgroup G, Fm L ≤ Fs L := fun L => by
    rw [Fs_eq_sup]
    exact le_sup_left
  have hY : zpowers d ≤ Fm M := Subgroup.zpowers_le.2 hdFm
  have hben := bender_apply hB12 hF.hkps hF.hMc hF.hnq (Y := zpowers d) (N := N) hY inf_le_right
  have hFmC : Fm C ≤ M := by
    refine (Fm_le_Fpi_sup (fun r => r ∣ Nat.card ↥(Fm M)) C).trans (sup_le hF2 ?_)
    exact (le_sup_right : Fpi (piF' M) C ≤ XdR M d).trans hXd
  have hEmC : Em C ≤ M := (le_sup_left : Em C ≤ XdR M d).trans hXd
  have hFsC : Fs C ≤ M := by
    rw [Fs_eq_sup C]
    exact sup_le hFmC hEmC
  have hFsz : Fs C ≤ centralizer ({z} : Set G) := by
    rw [← hF.hMz]
    exact hFsC
  have hzOp : z ∈ Op 2 C := z_mem_Op_two_of_cent hzC hF.hz2 hFsz
  have h2prime : ∀ q ∈ ({2} : Set ℕ), q.Prime := fun q hq => by
    rw [Set.mem_singleton_iff.1 hq]
    exact Nat.prime_two
  have hz_N : z ∈ Op 2 N := by
    have h1 : Op 2 C ≤ Fpi {2} C := by
      rw [← Op_Fm_eq Nat.prime_two C]
      exact le_iSup₂_of_le 2 (Set.mem_singleton 2) le_rfl
    have h2 : Fpi {2} C ≤ Fpi {2} N := Fpi_le_Fpi_of_normal h2prime hCN hNC
    have h3 : Fpi {2} N ≤ Op 2 N := by
      refine iSup₂_le fun q hq => ?_
      rw [Set.mem_singleton_iff.1 hq, Op_Fm_eq Nat.prime_two N]
    exact h3 (h2 (h1 hzOp))
  have hRM : Op 2 N ≤ M := by
    have : Op 2 N ≤ Fpi (piF M) N := by
      rw [← Op_Fm_eq Nat.prime_two N]
      exact le_iSup₂_of_le 2 hF.h2pi le_rfl
    exact this.trans hben.2
  have hcomm2 : ⁅inSubgroup (oResidual 2)
      (Fs M ⊓ normalizer ((zpowers d : Subgroup G) : Set G)), Op 2 N⁆ = ⊥ :=
    (hB12 G hF.hkps M N hF.hMc (zpowers d) hY inf_le_right).2.2 2 Nat.prime_two hF.h2pi.2
  have hK : ∀ x ∈ Fs M, x * d = d * x → Odd (orderOf x) → ∀ r ∈ Op 2 N, x * r = r * x := by
    intro x hx hxd hodd r hr
    have hxN : x ∈ normalizer ((zpowers d : Subgroup G) : Set G) :=
      centralizer_le_normalizer_zpowers d (Subgroup.mem_centralizer_singleton_iff.2 hxd)
    exact commute_of_oResidual_cl hcomm2 ⟨hx, hxN⟩ hodd r hr
  have hOq : ∀ q, q.Prime → q ≠ 2 → q ≠ p →
      Op q M ≤ centralizer ((Op 2 N : Subgroup G) : Set G) := by
    intro q hq hq2 hqp x hx
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hxFs : x ∈ Fs M := hFmFs M ((Op_le_Fm q hq M) hx)
    have hxd : x * d = d * x := Op_commute_Op_cl hp hq (Ne.symm hqp) M hx hdP
    exact (hK x hxFs hxd (odd_orderOf_of_mem_Op_cl hq hq2 hx) r hr).symm
  have hEp : IsPGroup p ↥E := by
    have := hctx.E_elem
    exact IsElementaryAbelian.isPGroup p ↥E
  have hcop2 : Nat.Coprime p (Nat.card ↥(Op 2 N)) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_Op 2 Nat.prime_two N)
    rw [hn]
    exact Nat.Coprime.pow_right n ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hEcomm : ∀ b ∈ E, b * d = d * b := fun b hb => by
    have := congrArg Subtype.val
      ((hctx.E_elem.toIsMulCommutative.is_comm).comm (⟨b, hb⟩ : ↥E) ⟨d, hdE⟩)
    exact this
  have hEodd : ∀ b ∈ E, Odd (orderOf b) := fun b hb =>
    odd_orderOf_of_mem_Op_cl hp hp2 (hctx.E_le hb)
  have hRP : Op 2 N ≤ centralizer ((Op p M : Subgroup G) : Set G) := by
    refine hAB G p hp (Op 2 N) E (Op p M) (isPGroup_Op p hp M) hEp hcop2
      (hRM.trans (le_normalizer_Op p M)) (hctx.E_le.trans Subgroup.le_normalizer) ?_ ?_
    · intro a ha b hb
      exact (hK b (hFmFs M ((Op_le_Fm p hp M) (hctx.E_le hb))) (hEcomm b hb) (hEodd b hb) a ha).symm
    · intro a ha y hy
      have hyP : y ∈ Op p M := hy.1
      have hyE : ∀ e ∈ E, e * y = y * e := fun e he => Subgroup.mem_centralizer_iff.1 hy.2 e he
      have hyd : y * d = d * y := (hyE d hdE).symm
      exact (hK y (hFmFs M ((Op_le_Fm p hp M) hyP)) hyd
        (odd_orderOf_of_mem_Op_cl hp hp2 hyP) a ha)
  have hOodd : ∀ q, q.Prime → q ≠ 2 → Op q M ≤ centralizer ((Op 2 N : Subgroup G) : Set G) := by
    intro q hq hq2
    by_cases hqp : q = p
    · subst hqp
      exact Subgroup.le_centralizer_iff.1 hRP
    · exact hOq q hq hq2 hqp
  set D : Subgroup G := pPrimeCoreOf 2 M with hDdef
  have hDodd : Odd (Nat.card ↥D) := odd_card_pPrimeCoreOf_cl M
  have hDsolv : Group.IsSolvable ↥D := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hDodd
  have hDM : D ≤ M := Subgroup.map_subtype_le _
  have hMD : M ≤ normalizer (D : Set G) := le_normalizer_pPrimeCoreOf_cl M
  have hprimes : ∀ q ∈ {q : ℕ | q.Prime ∧ q ≠ 2}, q.Prime := fun q hq => hq.1
  have hFmD : Fm D ≤ centralizer ((Op 2 N : Subgroup G) : Set G) := by
    have h1 : Fm D ≤ Fpi {q | q.Prime ∧ q ≠ 2} D ⊔ Fpi {q | q.Prime ∧ ¬ q ≠ 2} D :=
      Fm_le_Fpi_sup (fun q => q ≠ 2) D
    have h2 : Fpi {q | q.Prime ∧ ¬ q ≠ 2} D = ⊥ := by
      rw [eq_bot_iff]
      refine iSup₂_le fun q hq => ?_
      have hq2 : q = 2 := not_not.1 hq.2
      subst hq2
      rw [Op_Fm_eq Nat.prime_two D, Op_two_eq_bot_of_odd hDodd]
    have h3 : Fpi {q | q.Prime ∧ q ≠ 2} D ≤ Fpi {q | q.Prime ∧ q ≠ 2} M :=
      Fpi_le_Fpi_of_normal hprimes hDM hMD
    have h4 : Fpi {q | q.Prime ∧ q ≠ 2} M ≤ centralizer ((Op 2 N : Subgroup G) : Set G) := by
      refine iSup₂_le fun q hq => ?_
      rw [Op_Fm_eq hq.1 M]
      exact hOodd q hq.1 hq.2
    rw [h2, sup_bot_eq] at h1
    exact h1.trans (h3.trans h4)
  have hselfC : D ⊓ centralizer ((Fm D : Subgroup G) : Set G) ≤ Fm D :=
    GorensteinWalter.fact_1_2_centralizer_fitting_le_fitting D hDsolv
  have hFmDsub : ((Fm D).subgroupOf D).IsSubnormal := by
    have hn : ((Fm D).subgroupOf D).Normal := by
      have : (Fm D).subgroupOf D = fittingSubgroup ↥D := by
        exact Subgroup.comap_map_eq_self_of_injective D.subtype_injective _
      rw [this]
      infer_instance
    exact hn.isSubnormal
  have hcopD : Nat.Coprime (Nat.card ↥(Op 2 N)) (Nat.card ↥D) := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (isPGroup_Op 2 Nat.prime_two N)
    rw [hn]
    exact Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hDodd)
  have hRD : Op 2 N ≤ centralizer (D : Set G) :=
    GorensteinWalter.centralizes_of_subnormal_selfCentralizing_coprime (Op 2 N) D (Fm D)
      (hRM.trans hMD) (Fm_le D) hFmDsub (Subgroup.le_centralizer_iff.1 hFmD) hselfC hcopD hDsolv
  obtain ⟨c, hcC, hcM⟩ := IsConcreteLE.not_le_iff_exists.1 hdM
  have hcN : c ∈ N := hCN hcC
  have huR : c * z * c⁻¹ ∈ Op 2 N :=
    (mem_normalizer_iff.1 (le_normalizer_Op 2 N hcN) z).1 hz_N
  have huD : c * z * c⁻¹ ∈ centralizer ((pPrimeCoreOf 2 M : Subgroup G) : Set G) := hRD huR
  have huz : c * z * c⁻¹ = z :=
    h178 G z k S M hctx.base (c * z * c⁻¹) (isConj_iff.2 ⟨c, rfl⟩) huD
  apply hcM
  rw [hF.hMz]
  exact Subgroup.mem_centralizer_singleton_iff.2 (mul_inv_eq_iff_eq_mul.1 huz)

end Main

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
