module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.K144Main
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R166Label
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonInnBridge
public import CFSG.HardMathSupport.Solomon.Coordinator.B3LieRes

public section

namespace CFSG.LocalAnalysis.GLTheoremA.K144I

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 TauCeti
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup PerfectInLayer)
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel hasLabel_of_statedClassicalModel_PSU
  hasLabel_of_statedClassicalModel_PSp centerQuotAut centerQuotAut_mk center_centerQuot_eq_bot)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.LocalAnalysis.GLTheoremA.K144 (I144Cat I144Inner)
open scoped commutatorElement

theorem isQuasisimple_of_openQuasisimple {Q : Type} [Group Q] (h : CFSG.Open.IsQuasisimple Q) :
    CFSG.IsQuasisimple Q := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨⟨h1⟩, h2, ?_⟩
  by_contra hc
  push Not at hc
  have hZ : commutator Q ≤ Subgroup.center Q := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (Subgroup.center Q) ⁅x, y⁆ = 1
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hc _ _
  rw [h1] at hZ
  have hall : ∀ q : Q ⧸ Subgroup.center Q, q = 1 := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    exact (QuotientGroup.eq_one_iff x).mpr (hZ (Subgroup.mem_top x))
  obtain ⟨a, b, hab⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  exact hab ((hall a).trans (hall b).symm)

theorem openQuasisimple_of_simple {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : CFSG.Open.IsQuasisimple S := by
  have hZ : Subgroup.center S = ⊥ := by
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
      exact hab (Subgroup.mem_center_iff.1 ha b).symm
  refine ⟨?_, ?_⟩
  · rcases hs.eq_bot_or_eq_top_of_normal (commutator S) with h | h
    · exfalso
      obtain ⟨a, b, hab⟩ := hnab
      have h1 : ⁅a, b⁆ ∈ commutator S :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [h, Subgroup.mem_bot] at h1
      exact hab (commutatorElement_eq_one_iff_mul_comm.1 h1)
    · exact h
  · have e : S ≃* (S ⧸ Subgroup.center S) :=
      (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    haveI := hs
    exact MulEquiv.isSimpleGroup e.symm

theorem perfectInLayer_one_of_simple {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hnab : ∃ a b : S, a * b ≠ b * a) : PerfectInLayer (1 : MulAut S) := by
  intro P _ _
  have htop : fixSubgroup (1 : MulAut S) = ⊤ := by
    ext s
    simp only [mem_fixSubgroup, MulAut.one_apply, Subgroup.mem_top]
  rw [htop]
  have hc : IsComponentOf (⊤ : Subgroup S) ⊤ :=
    ⟨le_rfl, IsSubnormal.refl _, CFSG.Open.IsQuasisimple.of_mulEquiv Subgroup.topEquiv
      (openQuasisimple_of_simple hs hnab)⟩
  exact le_top.trans (le_sSup hc)

theorem exists_lieIndex_of_catalogIs_onLie {S : Type} [Group S] {P : LieTypeIndex → Prop}
    (h : catalogIs S (onLie P)) :
    ∃ (d : LieTypeIndex) (hv : d.Valid), P d ∧
      Nonempty (S ≃* ValidLieTypeIndex.Group ⟨d, hv⟩) := by
  obtain ⟨i, hi, ⟨e⟩⟩ := h
  cases i with
  | cyclic _ _ => exact hi.elim
  | alternating _ _ => exact hi.elim
  | sporadic _ => exact hi.elim
  | lie j => exact ⟨j.1, j.2, hi, ⟨e⟩⟩

theorem p_eq_two_of_card_eq_two {q : PrimePower} (h : q.card = 2) : q.p = 2 ∧ q.exponent = 1 := by
  rw [PrimePower.card_def q] at h
  exact Nat.prime_two.pow_eq_iff.1 h

theorem statedClassicalModel_psu_two {S : Type} [Group S] {r : ℕ} {q : PrimePower}
    {hv : (LieTypeIndex.twistedA r q).Valid} (hq : q.card = 2)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.twistedA r q, hv⟩) :
    StatedClassicalModel S .PSU (r + 1) 2 1 := by
  obtain ⟨hp, he⟩ := p_eq_two_of_card_eq_two hq
  obtain ⟨-, hm | ⟨h0, -⟩⟩ := CFSG.Models.lieModel_twistedA r q hv e
  · have hc : ValidLieTypeIndex.characteristic ⟨.twistedA r q, hv⟩ = 2 :=
      (LieTypeIndex.characteristic_twistedA r q).trans hp
    have hf : ValidLieTypeIndex.fieldExponent ⟨.twistedA r q, hv⟩ = 1 :=
      (LieTypeIndex.fieldExponent_twistedA r q).trans he
    rwa [hc, hf] at hm
  · omega

theorem statedClassicalModel_psp_two {S : Type} [Group S] {q : PrimePower}
    {hv : (LieTypeIndex.B 3 q).Valid} (hq : q.card = 2)
    (e : S ≃* ValidLieTypeIndex.Group ⟨.B 3 q, hv⟩) :
    StatedClassicalModel S .PSp 3 2 1 := by
  obtain ⟨hp, he⟩ := p_eq_two_of_card_eq_two hq
  rcases CFSG.Models.lieModel_B 3 q hv e with h | h
  · obtain ⟨-, hm | ⟨h0, -⟩⟩ := h
    · rwa [hp, he] at hm
    · omega
  · rw [hp] at h
    exact absurd h.1.2.2.2 (by simp)

theorem i144Cat_hasLabel {X : Type} [Group X] (hX : CFSG.Open.IsQuasisimple X)
    (h : catalogIs (X ⧸ Subgroup.center X) I144Cat) :
    ∃ labJ : GLALabel, (canonLabel labJ).n = 1 ∧ HasLabel X (· = labJ) := by
  have hq := isQuasisimple_of_openQuasisimple hX
  obtain ⟨i, hi, he⟩ := h
  rcases hi with hU4 | hU5 | hSp
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex_of_catalogIs_onLie ⟨i, hU4, he⟩
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨⟨.twA, 3, 1⟩, rfl,
          hasLabel_of_statedClassicalModel_PSU hq (statedClassicalModel_psu_two hP e)⟩
      · exact hP.elim
    | _ => exact hP.elim
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex_of_catalogIs_onLie ⟨i, hU5, he⟩
    cases d with
    | twistedA r q =>
      rcases r with _ | _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨⟨.twA, 4, 1⟩, rfl,
          hasLabel_of_statedClassicalModel_PSU hq (statedClassicalModel_psu_two hP e)⟩
      · exact hP.elim
    | _ => exact hP.elim
  · obtain ⟨d, hv, hP, ⟨e⟩⟩ := exists_lieIndex_of_catalogIs_onLie ⟨i, hSp, he⟩
    cases d with
    | B r q =>
      rcases r with _ | _ | _ | _ | r
      · exact hP.elim
      · exact hP.elim
      · exact hP.elim
      · exact ⟨⟨.B, 3, 1⟩, rfl,
          hasLabel_of_statedClassicalModel_PSp hq (statedClassicalModel_psp_two hP e)⟩
      · exact hP.elim
    | _ => exact hP.elim

theorem innDiagKind_of_i144Inner {K : Type} [Group K] (hK : CFSG.Open.IsQuasisimple K)
    {α : MulAut K} (h : I144Inner K α) :
    ∃ labK : GLALabel, HasLabel K (· = labK) ∧
      InnDiagKind (K ⧸ Subgroup.center K) labK (centerQuotAut K α) := by
  have hcen := center_centerQuot_eq_bot hK
  haveI : Group.IsPerfect K := ⟨hK.1⟩
  have hS : commutator (K ⧸ Subgroup.center K) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center K))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨hX, labK, hlam, hraw⟩ := h
  refine ⟨labK, ⟨hX, labK, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩,
    hS, labK, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, φ, hφ, hind⟩
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl, φ, hφ, ?_⟩
  intro s s' hss'
  subst hss'
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective s
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk,
    CanonInn.quotCenterEquivOfBot_mk, centerQuotAut_mk]
  exact hind k (α k) rfl

end CFSG.LocalAnalysis.GLTheoremA.K144I

end
