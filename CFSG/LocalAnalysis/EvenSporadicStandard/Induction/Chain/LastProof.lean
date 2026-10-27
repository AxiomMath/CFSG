module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Last
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.TArg
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Quasi
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Transfer
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.DiagDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.CyclicNormal
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBAlternatingInclusion
public import CFSG.LocalAnalysis.EvenSporadicStandard.Common
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Composite
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.ClosingAt
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.Step
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Hyp.TypeMax
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Chain
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.GlobSetting

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

variable {H : Type} [Group H] [Finite H]

theorem exists_involution_of_inL {L : Subgroup H} (hL : InL L) :
    ∃ t : H, orderOf t = 2 ∧ t ∈ centralizer (L : Set H) := by
  obtain ⟨T, hT, hT2, hLc⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) 2 (two_dvd_card_of_isPGroup hT2 hT)
  refine ⟨(x : H), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe]
    exact hx
  · refine Subgroup.mem_centralizer_iff.2 fun l hl => ?_
    exact (Subgroup.mem_centralizer_iff.1 (hLc.1 hl) (x : H) x.2).symm

omit [Finite H] in
theorem even_card_of_isK {IsK IsL : GroupClass} {K : Subgroup H} (hyp : Hyp31Row IsK IsL)
    (h : IsK (↥K ⧸ CFSG.oddCore ↥K)) : Even (Nat.card ↥K) := by
  have h1 := even_card_of_three_le_pRank (hyp.quasi_K _ h).2
  exact even_iff_two_dvd.2 ((even_iff_two_dvd.1 h1).trans (Subgroup.card_quotient_dvd_card _))

theorem noFiveAAbove_of_diag (IsK IsL : GroupClass) (hdiag : DiagData H) (N : Subgroup H) :
    NoFiveAAbove IsK IsL H N := by
  intro lit hH hkp hyp h4a K L J hK hmax hL hstd hlt hle hIsK hJ
  have hN := hyp.fstar
  have hO : CFSG.oddCore H = ⊥ := hN.oddCore_eq_bot
  obtain ⟨T₀, s₀, hT₀, hT₀2, hKc, -, hsN, -, -, -, -, hKne, -⟩ := hJ
  set K' : Subgroup H := K.map (MulAut.conj s₀).toMonoidHom with hK'def
  have hK'c : IsCompIn K' (centralizer (T₀ : Set H)) :=
    isCompIn_map_conj_of_mem_normalizer hKc (mem_normalizer_centralizer_of_mem_normalizer hsN)
  have hK'q : CFSG.IsQuasisimple ↥K' := hK'c.isQuasisimple
  have hcomm : ∀ a ∈ K, ∀ b ∈ K', a * b = b * a := hKc.commute_of_ne hK'c hKne
  let eK : ↥K ≃* ↥K' :=
    Subgroup.equivMapOfInjective K (MulAut.conj s₀).toMonoidHom (MulAut.conj s₀).injective
  have hIsK' : IsK (↥K' ⧸ CFSG.oddCore ↥K') := isK_quot_of_equiv hyp.isK_inv eK hIsK
  have hK'inL : InL K' := ⟨T₀, hT₀, hT₀2, hK'c⟩
  have hK'like : KLike IsK K' := klike_of_isK_quot hK'q hIsK'
  obtain ⟨t, ht2, htL⟩ := exists_involution_of_inL hmax.1
  have htt : t * t = 1 := by
    rw [← pow_two]
    exact orderOf_dvd_iff_pow_eq_one.1 (by rw [ht2])
  have hCt := centralizer_le_normalizer_of_order_two hstd htL ht2
  obtain ⟨N₀, hcan⟩ := exists_canLoc K (even_card_of_isK hyp.toHyp31Row hIsK)
  have hN₀K : N₀ ≤ K := hcan.le
  obtain ⟨R, hR0, hR2, hRK, hN₀R⟩ := hcan.isTwoLocalIn
  have h4 : FourAConcl K L N₀ := h4a.four_a K L hK hmax hlt hle hIsK N₀ hcan
  have hN₀t : t ∈ centralizer (N₀ : Set H) :=
    Subgroup.centralizer_le (fun x hx => hle (hN₀K hx)) htL
  have htR : t ∈ centralizer (R : Set H) :=
    Subgroup.centralizer_le (fun x hx => hle (hRK hx)) htL
  have hK'T₀ : K' ≤ centralizer (T₀ : Set H) := hK'c.1
  have hN₀K' : N₀ ≤ centralizer (K' : Set H) := fun n hn =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm n (hN₀K hn) b hb).symm
  have hN₀N : N₀ ≤ normalizer (R : Set H) := by
    rw [hN₀R]
    exact inf_le_left
  have hT₀R : T₀ ≤ centralizer (R : Set H) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun r hr =>
      (Subgroup.mem_centralizer_iff.1 (hKc.1 (hRK hr)) x hx).symm
  have hRK' : R ≤ centralizer (K' : Set H) := fun r hr =>
    Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm r (hRK hr) b hb).symm
  have hTR : ⁅T₀, R⁆ ≤ T₀ ⊓ R := by
    rw [(Subgroup.commutator_eq_bot_iff_le_centralizer).2 hT₀R]
    exact bot_le
  have hiso : Nonempty ((↥K' ⧸ center ↥K') ≃* (↥K ⧸ center ↥K)) := ⟨(cqEquivOfEquiv eK).symm⟩
  obtain ⟨-, hLB⟩ := lit.thm21 H hH hkp hO T₀ R hT₀2 hR2 hTR K' hK'c
  obtain ⟨M₀, hM₀c, hK'M₀⟩ := hLB hRK'
  have hK'cc : K' ≤ conjClosure M₀ T₀ := fun x hx => (hK'M₀.1 hx).2
  have hM₀inL : InL M₀ := ⟨R, hR0, hR2, hM₀c⟩
  have hltK'M : Lt K' M₀ := ⟨T₀, R, hT₀, hR0, hT₀2, hR2, hTR, hK'c, hM₀c, hK'cc⟩
  rcases hyp.desc K' M₀ hK'inL hK'like hM₀inL (ReflTransGen.single hltK'M) with
    ⟨π, hπ, -⟩ | ⟨hM₀L, -⟩
  ·
    obtain ⟨D, hDperf, hDN, hDiso, hdich⟩ := hdiag R T₀ K' M₀ N₀ t hK'q hT₀R hK'T₀ hM₀c hK'cc
      ⟨π, hπ⟩ hN₀N hN₀K' htR hN₀t htt
    obtain ⟨e₁⟩ := hDiso
    obtain ⟨e₂⟩ := hiso
    exact false_of_diag h4 hCt htt hN₀t hDN ⟨e₁.trans e₂⟩ hdich
  ·
    have hMtype := hyp.type_max M₀ hM₀inL hM₀L
    have hmaxM : Maximal M₀ := hMtype.1
    have hnorm : T₀ ≤ normalizer (M₀ : Set H) :=
      le_normalizer_of_cyclic_centralizer hM₀c hT₀R
        (fun y => (hyp.quasi_L _ (hyp.isL_inv _ _ (Subgroup.equivMapOfInjective M₀
          (MulAut.conj y).toMonoidHom (MulAut.conj y).injective) hM₀L)).2.2) hMtype.2
    have hK'M : K' ≤ M₀ := fun x hx => conjClosure_le_of_le_normalizer hnorm (hK'cc hx)
    have hcan' : CanLoc K' (N₀.map (MulAut.conj s₀).toMonoidHom) :=
      hcan.map (MulAut.conj s₀)
    have h4' := (h4a.four_a K' M₀ hK'inL hmaxM hltK'M hK'M hIsK' _ hcan').1
    refine h4' (isSectionOf_of_le_range (E := N₀) ?_
      (((QuotientGroup.mk' (center ↥K')).comp eK.toMonoidHom).comp
        (Subgroup.inclusion hN₀K)) _ ?_)
    · intro n hn
      refine ⟨mem_normalizer_of_fixes hM₀c hK'M hK'q (hN₀N hn) (hN₀K' hn), ?_⟩
      refine Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      obtain ⟨m, hm, rfl⟩ := hy
      exact (hcomm n (hN₀K hn) _ ⟨m, hN₀K hm, rfl⟩).symm
    · rintro _ ⟨z, hz, rfl⟩
      obtain ⟨m, hm, hmz⟩ := hz
      refine ⟨⟨m, hm⟩, ?_⟩
      show QuotientGroup.mk' (center ↥K') (eK (Subgroup.inclusion hN₀K ⟨m, hm⟩)) =
        QuotientGroup.mk' (center ↥K') z
      congr 1
      apply Subtype.ext
      exact hmz

end CFSG.EvenSporadicStandard.Induction
