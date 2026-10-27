module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81CK372Ge5Setting
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K37Setup
import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3Central3BInnerQIff
import CFSG.LocalAnalysis.GLTheoremA.S10.Lemma102
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.RankThree.PartOne.HNB.InnerAction

public section

namespace CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5

open CFSG.Open
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3 (autIm)
open CFSG.LocalAnalysis.RankThreeUC.S15.K37 (normalizerMonoidHom_of_mem mem_normalizer_autIm)

variable {X : Type} [Group X] [Finite X]

theorem centGenI_le_rankThreeGamma {p : ℕ} (hp : p.Prime) {E : Subgroup X}
    (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2) (L : Subgroup X) :
    GL83.CompFam.centGenI p E L ≤ rankThreeGamma 1 p E := by
  have : Fact p.Prime := ⟨hp⟩
  change GL83.CompFam.centGenI p E L ≤ CFSG.Open.GLBCore p 1 E
  refine iSup_le fun A => ?_
  obtain ⟨hAE, hAc⟩ := A.2
  have hAel : IsElemAbelian p A.1 := GL83.CompFam.elem_mono hE hAE
  obtain ⟨j, hj⟩ := GL83.CompFam.exists_card_eq_pow hAel
  have hpA : p ^ 2 ≤ p * Nat.card A.1 := by
    rw [← hEc]
    exact hAc
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [hj, h0, pow_zero, mul_one] at hpA
      have h2 := hp.two_le
      nlinarith
    · exact h0
  have hrk : 1 ≤ CFSG.Open.pRank p A.1 :=
    hj1.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hAel hj)
  exact inf_le_right.trans ((Subgroup.centralizer_le_normalizer (A.1 : Set X)).trans
    (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore hAE hrk))

namespace K372Setting

variable {p : ℕ} {K E S : Subgroup X}

theorem le_normalizer_K (h : K372Setting X p K E S) : E ≤ Subgroup.normalizer (K : Set X) := by
  have := h.normal
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem S_le_normalizer_K (h : K372Setting X p K E S) :
    S ≤ Subgroup.normalizer (K : Set X) := by
  have := h.normal
  rw [Subgroup.normalizer_eq_top]
  exact le_top

theorem centralizer_le (h : K372Setting X p K E S) {e : X} (he : e ∈ E) (he1 : e ≠ 1) :
    Subgroup.centralizer {e} ≤ rankThreeGamma 1 p E :=
  CFSG.LocalAnalysis.RankThreeTheoremC.centralizer_le_of_rankThreeGamma_one h.prime h.elem le_rfl
    he he1

theorem exists_ne_one (h : K372Setting X p K E S) : ∃ e ∈ E, e ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
  have hc := h.card
  rw [hbot, Subgroup.card_bot] at hc
  have h2 := h.prime.two_le
  nlinarith

theorem le_gamma (h : K372Setting X p K E S) : E ≤ rankThreeGamma 1 p E := by
  obtain ⟨e, he, he1⟩ := h.exists_ne_one
  refine le_trans ?_ (h.centralizer_le he he1)
  intro x hx
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact congrArg Subtype.val (h.elem.1.is_comm.comm (⟨x, hx⟩ : ↥E) ⟨e, he⟩)

theorem le_normalizer_S (h : K372Setting X p K E S) : E ≤ Subgroup.normalizer (S : Set X) :=
  h.le_gamma.trans h.le_normalizer

theorem inf_centralizer_eq_bot (h : K372Setting X p K E S) :
    E ⊓ Subgroup.centralizer (K : Set X) = ⊥ := by
  by_contra hne
  obtain ⟨⟨e, he⟩, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have he1' : e ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  apply h.not_le
  refine le_trans ?_ (h.centralizer_le he.1 he1')
  intro k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subgroup.mem_centralizer_iff.mp he.2 k hk

theorem card_autIm (h : K372Setting X p K E S) : Nat.card (autIm E K) = p ^ 2 := by
  rw [CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.card_autIm h.le_normalizer_K
    h.inf_centralizer_eq_bot, h.card]

theorem isElemAbelian_autIm (h : K372Setting X p K E S) : IsElemAbelian p (autIm E K) :=
  CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.isElemAbelian_autIm h.elem K

theorem seitzHyperGamma_ne_top (h : K372Setting X p K E S) :
    CFSG.LieType.Seitz.seitzHyperGamma p (autIm E K) ≠ ⊤ := fun htop =>
  h.not_le ((CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsSeitz3.le_centGenI_of_autIm
    h.le_normalizer_K h.inf_centralizer_eq_bot htop).trans
      (centGenI_le_rankThreeGamma h.prime h.elem h.card K))

theorem isPGroup_center (h : K372Setting X p K E S) : IsPGroup p (Subgroup.center ↥K) :=
  CFSG.LocalAnalysis.GLTheoremA.S10.lemma102_isPGroup_of_central h.prime h.core _ le_rfl

theorem conj_mem_normalizer_autIm (h : K372Setting X p K E S) {k : X} (hk : k ∈ K)
    (hkΓ : k ∈ rankThreeGamma 1 p E) :
    MulAut.conj (⟨k, hk⟩ : ↥K) ∈
      Subgroup.normalizer ((autIm S K : Subgroup (MulAut ↥K)) : Set (MulAut ↥K)) := by
  have hkN : k ∈ Subgroup.normalizer (K : Set X) := by
    have := h.normal
    rw [Subgroup.normalizer_eq_top]
    trivial
  rw [← normalizerMonoidHom_of_mem hk hkN]
  exact mem_normalizer_autIm hkN (h.le_normalizer hkΓ)

omit [Finite X] in
theorem exists_of_conj_mem_autIm (hZ : Subgroup.center ↥K = ⊥) {k : ↥K}
    (hk : MulAut.conj k ∈ autIm E K) (hk1 : k ≠ 1) :
    ∃ e ∈ E, e ≠ 1 ∧ ∀ y ∈ K, e * y * e⁻¹ = (k : X) * y * (k : X)⁻¹ := by
  obtain ⟨⟨e, heN⟩, heE, he⟩ := Subgroup.mem_map.mp hk
  refine ⟨e, Subgroup.mem_subgroupOf.mp heE, ?_, fun y hy => ?_⟩
  · rintro rfl
    apply hk1
    apply CFSG.RankThree.PartOne.HNB.conj_injective_of_center_eq_bot hZ
    rw [map_one, ← he]
    exact map_one _
  · have h1 := congrArg (fun φ : MulAut ↥K => ((φ ⟨y, hy⟩ : ↥K) : X)) he
    simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply] at h1
    exact h1

theorem mem_gamma_of_conj_mem_autIm (h : K372Setting X p K E S) (hZ : Subgroup.center ↥K = ⊥)
    {k : ↥K} (hk : MulAut.conj k ∈ autIm E K) (hk1 : k ≠ 1) {y : X} (hy : y ∈ K)
    (hyk : y * k = k * y) : y ∈ rankThreeGamma 1 p E := by
  obtain ⟨e, he, he1, hek⟩ := exists_of_conj_mem_autIm hZ hk hk1
  refine h.centralizer_le he he1 (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  have h1 := hek y hy
  rw [← hyk, mul_inv_cancel_right] at h1
  calc y * e = e * y * e⁻¹ * e := by rw [h1]
    _ = e * y := by group

theorem orderOf_of_conj_mem_autIm (h : K372Setting X p K E S) (hZ : Subgroup.center ↥K = ⊥)
    {k : ↥K} (hk : MulAut.conj k ∈ autIm E K) (hk1 : k ≠ 1) : orderOf k = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine orderOf_eq_prime (CFSG.RankThree.PartOne.HNB.conj_injective_of_center_eq_bot hZ ?_) hk1
  rw [map_pow, map_one]
  exact h.isElemAbelian_autIm.2 _ hk

theorem exists_comm_not_mem (h : K372Setting X p K E S)
    (hSC : ¬ S ≤ Subgroup.centralizer (K : Set X)) :
    ∃ e ∈ E, e ≠ 1 ∧ ∃ s ∈ S, s * e = e * s ∧ s ∉ Subgroup.centralizer (K : Set X) := by
  have hpow : ∀ m : ↥E, m ^ p = 1 := fun m => Subtype.ext (by
    rw [Subgroup.coe_pow, h.elem.2 m m.2, Subgroup.coe_one])
  have hpS : ¬ p ∣ Nat.card S := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨n, hn⟩ := h.two.exists_card_eq
    rw [hn]
    intro hdvd
    have h2 := (Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp
      (h.prime.dvd_of_dvd_pow hdvd)
    have h5 := h.five_le
    omega
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    h.prime E S hpow h.card hpS h.le_normalizer_S
  by_contra hcon
  push Not at hcon
  apply hSC
  rw [hgen]
  refine iSup_le fun m => iSup_le fun hm => ?_
  intro s hs
  have hm1 : (m : X) ≠ 1 := fun h1 => hm (Subtype.ext h1)
  exact hcon m m.2 hm1 s hs.1 (Subgroup.mem_centralizer_singleton_iff.mp hs.2)

end K372Setting

end CFSG.LocalAnalysis.RankThreeUC.AGL81C.K372Ge5
