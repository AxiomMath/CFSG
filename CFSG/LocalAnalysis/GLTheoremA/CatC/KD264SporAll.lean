module

public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264Parts
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporGen
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LocalAnalysis.GLTheoremA.CatC.KD264GenCore
public import CFSG.Quasithin.Vol2.Ch10SecKGA318

public section

namespace CFSG.LocalAnalysis.GLTheoremA.KD264Gen

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open scoped commutatorElement

@[expose] def KD264SporAt (p : ℕ) (s : TauCeti.SporadicName) : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y] (K B : Subgroup Y), K.Normal →
    Nonempty (↥K ≃* (TauCeti.CFSGIndex.sporadic s).Group) →
    GLAPPrimeCore p ↥K = ⊥ → fullCoverLevel p ↥K = 4 →
    IsElemAbelian p B → p ^ 4 ≤ Nat.card B → IsMaxRankIn p B ⊤ →
    B ⊓ Subgroup.centralizer (K : Set Y) ≠ ⊥ →
    ∃ E : Subgroup Y, E ≤ B ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧
      GLAPLayer p (K ⊓ Subgroup.centralizer (E : Set Y)) ≠ ⊥

theorem kd264SporS_of_at {p : ℕ} (h : ∀ s, KD264SporAt p s) : KD264SporS p := fun s => h s

theorem kd264RowData_of_not_sq_dvd {p : ℕ} (hp : p.Prime) {T : Type} [Group T] [Finite T]
    (h : ¬ p ^ 2 ∣ Nat.card T) : KD264RowData p T := by
  intro A hA _ k hk1 _ hAk
  exfalso
  apply h
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨n, hn⟩ := (isPGroup_of_isElemAbelian hA).exists_card_eq
  have hkn : k + 1 ≤ n := (Nat.pow_le_pow_iff_right hp.one_lt).1 (hn ▸ hAk)
  exact (pow_dvd_pow p (by omega)).trans (hn ▸ Subgroup.card_subgroup_dvd_card A)

theorem isQuasisimple_of_simple {Q : Type} [Group Q] [IsSimpleGroup Q]
    (hnc : ∃ a b : Q, a * b ≠ b * a) : CFSG.Open.IsQuasisimple Q := by
  have hZ : Subgroup.center Q = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnc
  refine ⟨?_, ((QuotientGroup.quotientMulEquivOfEq hZ).trans
    QuotientGroup.quotientBot).isSimpleGroup⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator Q) with h | h
  · exfalso
    obtain ⟨a, b, hab⟩ := hnc
    have h1 : ⁅a, b⁆ = 1 := by
      rw [← Subgroup.mem_bot, ← h]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
  · exact h

theorem fullCoverLevel_ne_four_of_k2 {p : ℕ} {s : TauCeti.SporadicName} {K : Type} [Group K]
    (hq : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥)
    (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) (h2 : k2Spor p s) :
    fullCoverLevel p K ≠ 4 := by
  have hK2 : K2Cover p K := ⟨hq, Or.inl ⟨hZ, ⟨TauCeti.CFSGIndex.sporadic s, (show k2 p (TauCeti.CFSGIndex.sporadic s) from h2), ⟨e⟩⟩⟩⟩
  unfold fullCoverLevel
  split_ifs <;> first | omega | contradiction

theorem fullCoverLevel_ne_four_of_k3 {s : TauCeti.SporadicName} {K : Type} [Group K]
    (hq : CFSG.Open.IsQuasisimple K) (hZ : Subgroup.center K = ⊥)
    (e : K ≃* (TauCeti.CFSGIndex.sporadic s).Group) (h3 : s = .M12 ∨ s = .M22) :
    fullCoverLevel 3 K ≠ 4 := by
  have hK3 : K3Cover 3 K := ⟨hq, Or.inl ⟨hZ, ⟨TauCeti.CFSGIndex.sporadic s, (show k3 3 (TauCeti.CFSGIndex.sporadic s) from ⟨rfl, h3⟩), ⟨e⟩⟩⟩⟩
  unfold fullCoverLevel
  split_ifs <;> first | omega | contradiction

theorem kd264SporAt_of_model
    (hOut : CFSG.HardMathSupport.Timmesfeld.Coordinator.SporadicOuterLeTwo) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) {s : TauCeti.SporadicName} {Q : Type} [Group Q] [Finite Q]
    [IsSimpleGroup Q] (hnc : ∃ a b : Q, a * b ≠ b * a)
    (b : Q ≃* (TauCeti.CFSGIndex.sporadic s).Group)
    (hrow : ¬ k2Spor p s → ¬ (p = 3 ∧ (s = .M12 ∨ s = .M22)) → p ^ 2 ∣ Nat.card Q →
      KD264RowData p Q) :
    KD264SporAt p s := by
  intro Y _ _ K B hKn ⟨e⟩ hcore hlev hB hcard hmax hC
  set e' : ↥K ≃* Q := e.trans b.symm
  have hZQ : Subgroup.center Q = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hnc
  have hinQ : InnerAt p Q := fun α hα => by
    obtain ⟨x, hx, -⟩ := CFSG.HardMathSupport.Solomon.Coordinator.exists_conj_of_pow hp hp2 hZQ
      (hOut Q inferInstance hnc s ⟨b⟩) α hα
    exact ⟨x, hx.symm⟩
  haveI : IsSimpleGroup ↥K := (MulEquiv.isSimpleGroup_congr e').2 inferInstance
  have hncK : ∃ a c : ↥K, a * c ≠ c * a := by
    obtain ⟨a, c, hac⟩ := hnc
    exact ⟨e'.symm a, e'.symm c, fun h => hac (by simpa using congrArg e' h)⟩
  have hq : CFSG.Open.IsQuasisimple ↥K := isQuasisimple_of_simple hncK
  have hZK : Subgroup.center ↥K = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Coordinator.center_eq_bot_of_isSimpleGroup hncK
  have hrow' : KD264RowData p Q := by
    by_cases hk2 : k2Spor p s
    · exact absurd hlev (fullCoverLevel_ne_four_of_k2 hq hZK e hk2)
    by_cases hk3 : p = 3 ∧ (s = .M12 ∨ s = .M22)
    · obtain ⟨rfl, h3⟩ := hk3
      exact absurd hlev (fullCoverLevel_ne_four_of_k3 hq hZK e h3)
    by_cases hsq : p ^ 2 ∣ Nat.card Q
    · exact hrow hk2 hk3 hsq
    · exact kd264RowData_of_not_sq_dvd hp hsq
  exact kd264_gen_core hp hp2 hZQ hinQ hrow' K B hKn e' hq hcore hB hcard hmax hC

end CFSG.LocalAnalysis.GLTheoremA.KD264Gen
