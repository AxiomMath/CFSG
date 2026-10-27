module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Last
import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Junction.Final
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Composite
public import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Chain.Cover

public section

namespace CFSG.EvenSporadicStandard.Induction

open Subgroup Relation CFSG.EvenSporadicStandard.Solomon78

theorem lemma33_two_of_last (IsK IsL : GroupClass) (H : Type) [Group H] [Finite H]
    (hlast : ∀ N : Subgroup H, NoFiveAAbove IsK IsL H N) : Lemma33Two IsK IsL H := by
  intro lit hH hkp N n L T s hyp h4a h h0 hn hmax M hinM hlt hne
  by_contra hM
  have hN := hyp.fstar
  obtain ⟨hL1, hK1, hle, hlt1, hmaxL, hstdL, -, -, -⟩ :=
    lemma33_pair hyp (lit.thm22 H hH) hkp h h0 hn
  have hK1inL : InL (L (n - 2)) := h.inL hN (by omega)
  have hK1q : CFSG.IsQuasisimple ↥(L (n - 2)) := hK1inL.isQuasisimple
  have hMq : CFSG.IsQuasisimple ↥M := hinM.isQuasisimple
  have hKlike : KLike IsK (L (n - 2)) := klike_of_isK_quot hK1q hK1
  obtain ⟨π, hπ, hker⟩ : ∃ π : ↥M →* ↥(L (n - 2)), Function.Surjective π ∧ π.ker ≤ center ↥M := by
    rcases hyp.desc (L (n - 2)) M hK1inL hKlike hinM (ReflTransGen.single hlt) with h1 | ⟨hLM, -⟩
    · exact h1
    · exact absurd hLM hM
  have hMperf : Group.IsPerfect ↥M := hMq.1
  obtain ⟨T₀, hT₀, hT₀2, hMc⟩ := hinM
  have hexc := not_exc_of_central_cover hyp.toHyp31Row hK1q hMq hK1 π hπ hker
  obtain ⟨r, U, TU, sU, hU, hU0⟩ :=
    lit.cor23 H hH hkp N hN (perfect_subgroups_le_of_index_le_two hN.normal hyp.index_le_two)
      T₀ M hT₀2 hMc hexc.1 hexc.2
  have hr2 : 2 ≤ r := by
    by_contra hr
    rcases Nat.lt_or_ge r 1 with hr0 | hr1
    · have hr0' : r = 0 := by omega
      have hMN : M = N := by rw [← hU0, ← hU.last, hr0']
      rw [hMN] at hMc
      exact hT₀ (hN.eq_bot_of_isCompIn hMc)
    · have hr1' : r = 1 := by omega
      subst hr1'
      refine not_klike_last hyp hU le_rfl ?_
      have : (1 : ℕ) - 1 = 0 := rfl
      rw [this, hU0]
      exact KLike.of_central_cover hKlike hMperf π hπ hker
  have hexcK := not_exc_of_central_cover hyp.toHyp31Row hK1q hK1q hK1
    (MonoidHom.id ↥(L (n - 2))) Function.surjective_id (by rw [MonoidHom.ker_id]; exact bot_le)
  obtain ⟨m, P, TP, sP, hm, hP, hP0, hTP, -⟩ :=
    Junction.sol78JunctionAt_of_cor23SSec (lit.cor23.sec hH) hkp N hN (L (n - 2)) M hK1inL
      ⟨T₀, hT₀, hT₀2, hMc⟩ hlt (Ne.symm hne)
      hexcK.1 hexcK.2
  have hPm : P m = M := hP.last
  have hcqM : cqOrd M = cqOrd (L (n - 2)) := cqOrd_eq_of_central_cover π hπ hker
  have hcqU : cqOrd (U 0) = cqOrd (L (n - 2)) := by rw [hU0]; exact hcqM
  have hcqP : ∀ i ≤ m, cqOrd (P i) = cqOrd (L (n - 2)) := by
    intro i hi
    have h1 : cqOrd (P 0) ≤ cqOrd (P i) := hP.toLinks.cqOrd_mono (Nat.zero_le _) hi
    have h2 : cqOrd (P i) ≤ cqOrd (P m) := hP.toLinks.cqOrd_mono hi le_rfl
    rw [hP0] at h1
    rw [hPm] at h2
    omega
  have hjoin : U 0 = P m := hU0.trans hPm.symm
  have hfive : ∀ J : Subgroup H, FiveALink (L (n - 2)) J → False := fun J hJ =>
    hlast N lit hH hkp hyp h4a (L (n - 2)) (L (n - 1)) J hK1inL hmaxL hL1 hstdL hlt1 hle hK1 hJ
  by_cases hLcol : (∃ a ≤ n - 2, ∃ j < r, L a = U j) ∨
      (∃ a < n - 2, ∃ b, 1 ≤ b ∧ b ≤ m ∧ L a = P b)
  ·
    rcases hLcol with hcol | ⟨a, ha, b, -, hbm, hab⟩
    · obtain ⟨J, hJ⟩ := exists_fiveALink hN h hU hcqU (by rw [hU0]; exact hne) hcol
      exact hfive J hJ
    · obtain ⟨J, hJ⟩ := fiveALink_of_cqOrd_L hN h ha (by rw [hab, hcqP _ hbm])
      exact hfive J hJ
  push Not at hLcol
  obtain ⟨hnLU, hnLP⟩ := hLcol
  by_cases hPU : ∃ b, 1 ≤ b ∧ b < m ∧ ∃ j, 1 ≤ j ∧ j < r ∧ P b = U j
  ·
    classical
    obtain ⟨hb₁, hbm, j₀, hj₁, hjr, hPj⟩ := Nat.find_spec hPU
    have hbound := compChain_length_bound hN hn h h0 hmax hP hP0 hTP hU (b := Nat.find hPU)
      (j₀ := j₀) hb₁ hbm.le hjr hPj.symm (fun a ha j _ hj => hnLU a ha j hj)
      (fun a ha b' hb1' hb' => hnLP a ha b' hb1' (hb'.trans hbm.le))
      (fun b' hb1' hb' j hj hjr' hPb' => Nat.find_min hPU hb'
        ⟨hb1', hb'.trans hbm, j, by omega, hjr', hPb'⟩)
    have hb1 : Nat.find hPU = 1 := by omega
    have hj0 : j₀ = r - 1 := by omega
    rw [hb1, hj0] at hPj
    have hP1inL : InL (P 1) := ⟨TP 1, hTP 1 le_rfl hm, (hP.comp 1 hm).1, (hP.comp 1 hm).2⟩
    have hP1q : CFSG.IsQuasisimple ↥(P 1) := hP1inL.isQuasisimple
    have hlt01 : Lt (L (n - 2)) (P 1) := by
      have := hP.lt (i := 1) le_rfl hm (hTP 1 le_rfl hm)
      rwa [show (1 : ℕ) - 1 = 0 from rfl, hP0] at this
    have hKP1 : KLike IsK (P 1) := by
      rcases hyp.desc (L (n - 2)) (P 1) hK1inL hKlike hP1inL (ReflTransGen.single hlt01) with
        ⟨π₁, hπ₁, hker₁⟩ | ⟨hP1L, -⟩
      · have : Group.IsPerfect ↥(P 1) := hP1q.1
        exact KLike.of_central_cover hKlike this π₁ hπ₁ hker₁
      · exfalso
        have hne01 : P 0 ≠ P 1 := fun hh => absurd (hP.inj 0 (Nat.zero_le _) 1 hm hh) (by omega)
        have heq01 : cqOrd (P (1 - 1)) = cqOrd (P 1) := by
          rw [show (1 : ℕ) - 1 = 0 from rfl, hcqP 0 (Nat.zero_le _), hcqP 1 hm]
        have h5a := hP.toLinks.link5a_of_cqOrd_eq (i := 1) le_rfl hm heq01 hne01
        have e := h5a.2
        rw [show (1 : ℕ) - 1 = 0 from rfl, hP0] at e
        exact hyp.K_ne_L _ _ hP1L hK1 e
    refine not_klike_last hyp hU (by omega : 1 ≤ r) ?_
    rw [← hPj]
    exact hKP1
  ·
    push Not at hPU
    have hbound := compChain_length_bound hN hn h h0 hmax hP hP0 hTP hU (b := m) (j₀ := 0) hm
      le_rfl (by omega) hjoin (fun a ha j _ hj => hnLU a ha j hj) hnLP
      (fun b' hb1' hb' j hj hjr => hPU b' hb1' hb' j (by omega) hjr)
    omega

end CFSG.EvenSporadicStandard.Induction
