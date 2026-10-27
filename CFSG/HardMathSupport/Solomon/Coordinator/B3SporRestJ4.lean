module

public import CFSG.HardMathSupport.Solomon.Coordinator.B3Spor3J4
public import CFSG.HardMathSupport.Solomon.Coordinator.B3SporFiveKit
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4CentCEQuasisimple
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4ThreeClass
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.J4Fusion
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic

public section

set_option linter.unusedSectionVars false
set_option maxRecDepth 100000

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Proving CFSG.HardMathSupport.Timmesfeld.SporadicBalance
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
  CFSG.Sporadic.J4 CFSG.Sporadic.J4Schreier

section Conj

variable {G : Type*} [Group G]

theorem orderOf_conj_eq' (k x : G) : orderOf (k * x * k⁻¹) = orderOf x := by
  simpa [MulAut.conj_apply] using (MulAut.conj k).orderOf_eq x

theorem b3Phi_centralizer_conj [Finite G] {p : ℕ} (hp : p.Prime) (k x : G)
    (h : B3Phi p (Subgroup.centralizer ({x} : Set G))) :
    B3Phi p (Subgroup.centralizer ({k * x * k⁻¹} : Set G)) := by
  have h1 := (b3Phi_map_iff hp (MulAut.conj k).toMonoidHom (MulAut.conj k).injective).2 h
  rwa [map_centralizer_mulEquiv, MulAut.conj_apply] at h1

theorem commute_of_mem_gLAPPrimeCoreOf_of_conj {S : Type*} [Group S] [Finite S] {G₀ : Type*}
    [Group G₀] {H : Subgroup G₀} {p : ℕ} (hp : p.Prime) (e : S ≃* ↥H) {c : ↥H}
    (hconj : ∀ y : ↥H, orderOf y = p → ∃ k : ↥H, k * y * k⁻¹ = c)
    (hq : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({c} : Set ↥H))) {s : S}
    (hs : orderOf s = p) :
    ∀ o ∈ GLAPPrimeCoreOf p (Subgroup.centralizer ({s} : Set S)),
      ∀ d ∈ Subgroup.centralizer ({s} : Set S), o * d = d * o := by
  obtain ⟨k, hk⟩ := hconj (e s) (by rw [MulEquiv.orderOf_eq]; exact hs)
  let φ : S ≃* ↥H := (MulAut.conj (e.symm k)).trans e
  have hφ : φ s = c := by
    rw [← hk]
    simp only [φ, MulEquiv.trans_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply]
  have hqs : CFSG.IsQuasisimple ↥(Subgroup.centralizer ({φ s} : Set ↥H)) := hφ ▸ hq
  let ψ : ↥(Subgroup.centralizer ({s} : Set S)) ≃* ↥(Subgroup.centralizer ({φ s} : Set ↥H)) :=
    (Subgroup.equivMapOfInjective _ φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (map_centralizer_mulEquiv φ s))
  have hqC : CFSG.Open.IsQuasisimple ↥(Subgroup.centralizer ({s} : Set S)) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
      (CFSG.IsQuasisimple.of_mulEquiv ψ hqs)
  have hsC : s ∈ Subgroup.centralizer ({s} : Set S) := Subgroup.mem_centralizer_singleton_iff.2 rfl
  have hpC : p ∣ Nat.card (Subgroup.centralizer ({s} : Set S)) :=
    hs ▸ Subgroup.orderOf_dvd_natCard _ hsC
  intro o ho d hd
  have hod := gLAPPrimeCoreOf_le_inf_centralizer hp le_rfl
    (fun g hg l hl => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hl) (Subgroup.inv_mem _ hg)) hqC hpC ho
  exact (Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hod).2 d hd).symm

theorem b3SporPair_of_subgroup_model {name : TauCeti.SporadicName} {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hOut : SporadicOuterLeTwo) {G₀ : Type} [Group G₀] [Finite G₀]
    (H : Subgroup G₀) (hM : Nonempty (↥H ≃* (TauCeti.CFSGIndex.sporadic name).Group))
    (h : ∀ x : ↥H, orderOf x = p → B3Phi p (Subgroup.centralizer ({x} : Set ↥H))) :
    B3SporPair name p :=
  b3SporPair_of_model_prime hp hp2 hOut ↥H hM h

end Conj

section Three


theorem j4ThreeCentralizerResidual (hbr : SporadicBridges) : J4ThreeCentralizerResidual := by
  unfold J4ThreeCentralizerResidual
  intro S _ _ _ he s hs
  refine commute_of_mem_gLAPPrimeCoreOf_of_conj (H := J) Nat.prime_three
    (he.some.trans ((seedEquiv j4Facts.mat).symm.trans (hbr .J4).some).symm)
    (fun y hy => exists_conj_cE_of_orderThree y (hy ▸ pow_orderOf_eq_one y) ?_)
    (centralizer_cE_quasisimple j4Facts).1 hs
  intro h1
  rw [h1, orderOf_one] at hy
  exact absurd hy (by norm_num)

theorem b3SporPair_J4_three_of_bridges (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .J4 3 :=
  b3SporPair_J4_three hOut (j4ThreeCentralizerResidual hbr)

end Three

section Eleven


theorem gLAPPrimeCoreOf_centralizer_qz_eq_bot :
    GLAPPrimeCoreOf 11 (Subgroup.centralizer ({qz} : Set ↥J)) = ⊥ := by
  have hQC : Q11 ≤ Subgroup.centralizer ({qz} : Set ↥J) := fun q hq =>
    Subgroup.mem_centralizer_singleton_iff.2 (qz_commute_of_mem hq)
  refine gLAPPrimeCoreOf_eq_bot_of_record_pgroup (by norm_num) hQC
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hQC).2 centralizer_qz_le_normalizer_J4)
    (IsPGroup.of_card card_Q11) (inf_le_left.trans centralizer_Q11_le)

theorem not_eleven_pow_four_dvd_card_J : ¬ 11 ^ 4 ∣ Nat.card ↥J := by
  rw [card_J_eq]
  norm_num

theorem b3Phi_eleven_Q11 (u : ↥J) (hu : u ∈ Q11) (huo : orderOf u = 11) :
    B3Phi 11 (Subgroup.centralizer ({u} : Set ↥J)) := by
  by_cases hz : u ∈ Subgroup.zpowers qz
  · have hzp : Subgroup.zpowers u = Subgroup.zpowers qz :=
      Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hz)
        (by rw [Nat.card_zpowers, Nat.card_zpowers, huo, orderOf_qz])
    rw [centralizer_singleton_eq_of_zpowers hzp]
    exact b3Phi_of_oPrime gLAPPrimeCoreOf_centralizer_qz_eq_bot
  · obtain ⟨h121, h242⟩ := card_centralizer_noncentral_le hu hz
    refine b3Phi_of_card_le_two ?_
    have hdvd : Nat.card (GLAPPrimeCoreOf 11 (Subgroup.centralizer ({u} : Set ↥J))) ∣
        Nat.card (Subgroup.centralizer ({u} : Set ↥J)) :=
      Subgroup.card_dvd_of_le (GLAPPrimeCoreOf_le _)
    have hcop : Nat.Coprime (Nat.card (GLAPPrimeCoreOf 11
        (Subgroup.centralizer ({u} : Set ↥J)))) 121 :=
      ((coprime_card_GLAPPrimeCoreOf (by norm_num) _).pow_left 2).symm
    obtain ⟨k, hk⟩ := h121
    have hk2 : k ≤ 2 := by omega
    have hk0 : 0 < k := by
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · rw [h0, mul_zero] at hk
        exact absurd hk Nat.card_pos.ne'
      · exact h0
    rw [hk] at hdvd
    exact (Nat.le_of_dvd hk0 (hcop.dvd_of_dvd_mul_left hdvd)).trans hk2

theorem b3Phi_eleven_J (x : ↥J) (hx : orderOf x = 11) :
    B3Phi 11 (Subgroup.centralizer ({x} : Set ↥J)) := by
  obtain ⟨h, hh⟩ := exists_conj_mem_of_orderOf Q11 card_Q11 not_eleven_pow_four_dvd_card_J hx
  have huo : orderOf (h⁻¹ * x * h) = 11 := by
    have := orderOf_conj_eq' h⁻¹ x
    rw [inv_inv] at this
    rw [this, hx]
  have key := b3Phi_centralizer_conj (by norm_num) h _ (b3Phi_eleven_Q11 _ hh huo)
  rwa [show h * (h⁻¹ * x * h) * h⁻¹ = x by group] at key

theorem b3SporPair_J4_eleven (hbr : SporadicBridges) (hOut : SporadicOuterLeTwo) :
    B3SporPair .J4 11 :=
  b3SporPair_of_subgroup_model (by norm_num) (by norm_num) hOut J
    ⟨(seedEquiv j4Facts.mat).symm.trans (hbr .J4).some⟩ b3Phi_eleven_J

end Eleven

end CFSG.HardMathSupport.Solomon.Coordinator
