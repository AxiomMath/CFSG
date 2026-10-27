module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Setup
public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddDefChar
import CFSG.LocalAnalysis.AGLEmbeddingD2.FiveCover

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.LocalAnalysis.UniquenessCase.UCK (CatGrp)
open CFSG.LocalAnalysis.RankThreeUC.S15.K37 (isPGroup_autIm mem_normalizer_autIm)
open CFSG.RankThree.PartTwo.KFacts (congr_mulAutConj)

theorem not_dvd_card_sub_one {p : ℕ} (hp : p.Prime) {q : TauCeti.PrimePower} (hq : q.p = p) :
    ¬ p ∣ q.card - 1 := by
  intro h
  have hq1 : p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def, hq]
    exact dvd_pow_self p q.exponent_pos.ne'
  have hpos : 1 ≤ q.card := by
    rw [TauCeti.PrimePower.card_def]
    exact Nat.one_le_pow _ _ q.prime_p.pos
  rw [← Nat.sub_add_cancel hpos] at hq1
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right h).mp hq1))

theorem not_dvd_card_add_one {p : ℕ} (hp : p.Prime) {q : TauCeti.PrimePower} (hq : q.p = p) :
    ¬ p ∣ q.card + 1 := by
  intro h
  have hq1 : p ∣ q.card := by
    rw [TauCeti.PrimePower.card_def, hq]
    exact dvd_pow_self p q.exponent_pos.ne'
  exact hp.one_lt.ne' (Nat.dvd_one.mp ((Nat.dvd_add_right hq1).mp h))

variable {X : Type} [Group X] [Finite X] {p : ℕ} {K E S : Subgroup X}

namespace K372Setting

theorem center_eq_bot_of_defChar
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (h : K372Setting X p K E S) (d : TauCeti.ValidLieTypeIndex) (hdp : d.1.characteristic = p)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    Subgroup.center ↥K = ⊥ := by
  have : Fact p.Prime := ⟨h.prime⟩
  rcases h.isPGroup_center.card_eq_or_dvd with h1 | hz
  · exact Subgroup.eq_bot_of_card_eq _ h1
  obtain ⟨e⟩ := hd
  have hci := CFSG.AGLEmbeddingD2.FiveCover.primeCoverLie_of_griess_of_five_le hGA h.prime
    h.five_le d h.quasi e hz
  obtain ⟨dd, hv⟩ := d
  cases dd with
  | A m q => exact absurd hci.2 (not_dvd_card_sub_one h.prime (by simpa using hdp))
  | twistedA m q => exact absurd hci.2 (not_dvd_card_add_one h.prime (by simpa using hdp))
  | _ => exact False.elim hci

theorem false_of_defChar (hODC : CFSG.LocalAnalysis.UniquenessCase.UCK.OddDefCharCentralizer)
    (h : K372Setting X p K E S) (d : TauCeti.ValidLieTypeIndex) (hdp : d.1.characteristic = p)
    (ψ : ↥K ≃* CatGrp d) (hSC : ¬ S ≤ Subgroup.centralizer (K : Set X)) : False := by
  have hN : ∀ x : X, x ∈ Subgroup.normalizer (K : Set X) := fun x => by
    have := h.normal
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨Θ, hΘinj, hΘapp, hΘc⟩ : ∃ Θ : MulAut ↥K →* MulAut (CatGrp d), Function.Injective Θ ∧
      (∀ (α : MulAut ↥K) (y : ↥K), Θ α (ψ y) = ψ (α y)) ∧
      ∀ y : ↥K, Θ (MulAut.conj y) = MulAut.conj (ψ y) :=
    ⟨(MulAut.congr ψ).toMonoidHom, (MulAut.congr ψ).injective,
      fun α y => by simp [MulAut.congr_apply], congr_mulAutConj ψ⟩
  have hker : ∀ x : X, K.normalizerMonoidHom ⟨x, hN x⟩ = 1 →
      x ∈ Subgroup.centralizer (K : Set X) := fun x hx => by
    have hmem : (⟨x, hN x⟩ : ↥(Subgroup.normalizer (K : Set X))) ∈
        K.normalizerMonoidHom.ker := MonoidHom.mem_ker.mpr hx
    rw [Subgroup.normalizerMonoidHom_ker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  obtain ⟨e, he, he1, s, hs, hse, hsK⟩ := h.exists_comm_not_mem hSC
  obtain ⟨ε, hε⟩ : ∃ ε : MulAut (CatGrp d), ε = Θ (K.normalizerMonoidHom ⟨e, hN e⟩) :=
    ⟨_, rfl⟩
  have hεp : ε ^ p = 1 := by
    have h1 : (⟨e, hN e⟩ : ↥(Subgroup.normalizer (K : Set X))) ^ p = 1 :=
      Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact h.elem.2 e he)
    rw [hε, ← map_pow, ← map_pow, h1, map_one, map_one]
  have hε1 : ε ≠ 1 := by
    intro h1
    have h2 := hker e (hΘinj (by rw [map_one, ← hε, h1]))
    have hmem : e ∈ E ⊓ Subgroup.centralizer (K : Set X) := ⟨he, h2⟩
    rw [h.inf_centralizer_eq_bot, Subgroup.mem_bot] at hmem
    exact he1 hmem
  have hfix : ∀ k : CatGrp d, ε k = k → ((ψ.symm k : ↥K) : X) ∈ rankThreeGamma 1 p E := by
    intro k hk
    refine h.centralizer_le he he1 (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
    have h1 : K.normalizerMonoidHom ⟨e, hN e⟩ (ψ.symm k) = ψ.symm k :=
      ψ.injective (by rw [← hΘapp, MulEquiv.apply_symm_apply, ← hε]; exact hk)
    have h2 : e * (ψ.symm k : X) * e⁻¹ = ψ.symm k := by
      have h3 := congrArg Subtype.val h1
      rwa [Subgroup.normalizerMonoidHom_apply_apply_coe] at h3
    calc ((ψ.symm k : ↥K) : X) * e = e * (ψ.symm k : X) * e⁻¹ * e := by rw [h2]
      _ = e * (ψ.symm k : X) := by group
  obtain ⟨R, hR⟩ : ∃ R : Subgroup (MulAut (CatGrp d)),
      R = (autIm S K).map Θ ⊓ Subgroup.centralizer ({ε} : Set (MulAut (CatGrp d))) := ⟨_, rfl⟩
  have hR2 : IsPGroup 2 R := by
    rw [hR]
    exact ((isPGroup_autIm (K := K) h.two).map Θ).to_le inf_le_left
  have hRc : ∀ r ∈ R, r * ε = ε * r := fun r hr => by
    rw [hR] at hr
    exact Subgroup.mem_centralizer_singleton_iff.mp hr.2
  have hRne : R ≠ ⊥ := by
    rw [hR]
    intro hbot
    have hcomm : Commute (⟨s, hN s⟩ : ↥(Subgroup.normalizer (K : Set X))) ⟨e, hN e⟩ :=
      Subtype.ext hse
    have hmem : Θ (K.normalizerMonoidHom ⟨s, hN s⟩) ∈
        (autIm S K).map Θ ⊓ Subgroup.centralizer ({ε} : Set (MulAut (CatGrp d))) := by
      refine Subgroup.mem_inf.mpr
        ⟨Subgroup.mem_map_of_mem Θ ⟨⟨s, hN s⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, hε]
      exact ((hcomm.map K.normalizerMonoidHom).map Θ).eq
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hsK (hker s (hΘinj (by rw [map_one]; exact hmem)))
  have hRn : ∀ k : CatGrp d, ε k = k → ∀ r ∈ R,
      MulAut.conj k * r * (MulAut.conj k)⁻¹ ∈ R := by
    intro k hk r hr
    rw [hR] at hr ⊢
    have hn : MulAut.conj (ψ.symm k) ∈
        Subgroup.normalizer ((autIm S K : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) :=
      h.conj_mem_normalizer_autIm (ψ.symm k).2 (hfix k hk)
    have hn' := Subgroup.le_normalizer_map Θ (Subgroup.mem_map_of_mem Θ hn)
    rw [hΘc, MulEquiv.apply_symm_apply] at hn'
    have hc : Commute ε (MulAut.conj k) :=
      CFSG.LocalAnalysis.UniquenessCase.UCK.Odd.commute_conj_of_fix hk
    have hr' : Commute ε r := (Subgroup.mem_centralizer_singleton_iff.mp hr.2).symm
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp hn' r).mp hr.1, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact ((hc.mul_right hr').mul_right hc.inv_right).symm.eq
  have h5 := h.five_le
  obtain ⟨h3, -⟩ := hODC d (by omega) ε (by rw [hdp]; exact hεp) hε1 R hRne hR2 hRc hRn
  omega

theorem le_centralizer_of_defChar
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hODC : CFSG.LocalAnalysis.UniquenessCase.UCK.OddDefCharCentralizer)
    (h : K372Setting X p K E S) (d : TauCeti.ValidLieTypeIndex) (hdp : d.1.characteristic = p)
    (hd : Nonempty (↥K ⧸ Subgroup.center ↥K ≃* (TauCeti.CFSGIndex.lie d).Group)) :
    S ≤ Subgroup.centralizer (K : Set X) := by
  by_contra hSC
  have hZ := h.center_eq_bot_of_defChar hGA d hdp hd
  obtain ⟨e₁⟩ := hd
  exact h.false_of_defChar hODC d hdp
    (((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans e₁) hSC

end K372Setting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5
