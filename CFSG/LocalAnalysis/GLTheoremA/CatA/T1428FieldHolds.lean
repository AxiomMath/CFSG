module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T1428Facts
public import CFSG.LocalAnalysis.GLTheoremA.S12.CanonSubcomp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.AssemblyAll
import CFSG.LocalAnalysis.GLTheoremA.S3.ChevTools
import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10GInnExcLabel

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T1428

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4
open CFSG.LocalAnalysis.GLTheoremA.Y10F (HasLabel hasLabel_congr hasLabel_mono
  hasLabel_of_equiv_centerQuot quotEquiv_of_perfect_central center_centerQuot_eq_bot)
open CFSG.LocalAnalysis.GLTheoremA.Y10GField (InnDiagKind)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open CFSG.StandardType (GGLabelRigidInput GGInndiagCommRestInput)

private theorem exists_label_of_marking {X : Type} [Group X] {S : GLALabel → Prop}
    (h : HasLabel X S) : ∃ lab : GLALabel, S lab ∧ HasLabel X (· = lab) := by
  obtain ⟨hX, lab, hlam, hraw⟩ := h
  obtain ⟨_, _, _, _, -, -, -, hS⟩ := CFSG.StandardType.Canonical.largeEvenRawDatum_exists hraw
  exact ⟨lab, hS, hX, lab, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩

private theorem canonLabel_n_dvd_two_mul (lab : GLALabel) : (canonLabel lab).n ∣ 2 * lab.n := by
  obtain ⟨t, r, n⟩ := lab
  cases t
  case D =>
    simp only [canonLabel]
    split_ifs <;> exact dvd_mul_left n 2
  case twD =>
    simp only [canonLabel]
    split_ifs
    · exact dvd_mul_left n 2
    · exact dvd_rfl
    · exact dvd_mul_left n 2
  case B2der => exact one_dvd _
  case G2der => exact one_dvd _
  case twF4der => exact one_dvd _
  all_goals exact dvd_mul_left n 2

private theorem innDiagKind_chevAut {G : Type} [Group G] {p : ℕ} {K : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (K : Set G)) (hq : CFSG.Open.IsQuasisimple (PQuot p K))
    (hInn : S10.InnDiagOn p (Subgroup.zpowers y) K) :
    ∃ labL : GLALabel, HasLabel (PQuot p K) (· = labL) ∧
      InnDiagKind (PSimple p K) labL (chevAut p K ⟨y, hy⟩) := by
  have hcen := center_centerQuot_eq_bot hq
  haveI : Group.IsPerfect (PQuot p K) := ⟨hq.1⟩
  have hS : commutator (PSimple p K) = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center (PQuot p K)))
      (QuotientGroup.mk'_surjective _)).commutator_eq_top
  obtain ⟨hX, labL, hlam, hraw⟩ := hInn.2
  refine ⟨labL, ⟨hX, labL, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ, _⟩ => ⟨hs, hna, θ, rfl⟩) hraw⟩,
    hS, labL, hlam, CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hall⟩
  obtain ⟨φ, hφ, hind⟩ := hall y⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers y))
  refine ⟨hs, hna, (CanonInn.quotCenterEquivOfBot hcen).trans θ, rfl, φ, hφ, ?_⟩
  intro s s' hss'
  subst hss'
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective s
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply, CanonInn.quotCenterEquivOfBot_mk,
    CanonInn.quotCenterEquivOfBot_mk]
  have hc := chevAut_chevQuotHom p K ⟨y, hy⟩ k
  have hi := hind (QuotientGroup.mk k) (QuotientGroup.mk (K.normalizerMonoidHom ⟨y, hy⟩ k))
    ⟨k, K.normalizerMonoidHom ⟨y, hy⟩ k, rfl, rfl, by rw [chev_coe_normalizerMonoidHom, inv_inv]⟩
  exact hi.trans (congrArg θ hc.symm)

private theorem nonempty_centerQuot_equiv_pSimple {S : Type} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) {X J : Subgroup S} (hJ : GLAPComponent p X J) (hq : CFSG.Open.IsQuasisimple ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* PSimple p J) := by
  have hQ := isQuasisimple_pQuot_of_glaPComponent hp hJ
  have hne : GLAPPrimeCore p ↥J ≠ ⊤ := by
    intro htop
    haveI : Nontrivial (PQuot p J) := isQuasisimple_nontrivial hQ
    haveI : Subsingleton (↥J ⧸ GLAPPrimeCore p ↥J) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    exact not_subsingleton (PQuot p J) ‹_›
  have hle : GLAPPrimeCore p ↥J ≤ Subgroup.center ↥J :=
    le_center_of_normal_of_isQuasisimple hq inferInstance hne
  exact quotEquiv_of_perfect_central (QuotientGroup.mk' (GLAPPrimeCore p ↥J))
    (QuotientGroup.mk'_surjective _) ⟨hq.1⟩ (by rw [QuotientGroup.ker_mk']; exact hle)

section Inputs


theorem t1428FieldFact_of_inputs (hRig : GGLabelRigidInput) (hRest : GGInndiagCommRestInput)
    (hIdx : KD264Lie.LieCompIdx fun _ => True)
    (hLSC : CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimpleCent) : T1428FieldFact := by
  intro p hp hp2 Ω _ _ _ K y hK _ hyp hy hInn h₀ J hJ hJM
  have hq : CFSG.Open.IsQuasisimple (PQuot p K) := isQuasisimple_pQuot_of_glaPComponent hp hK
  have hcen := center_centerQuot_eq_bot hq
  have hap : IsPGroup p (Subgroup.zpowers y) :=
    CFSG.LocalAnalysis.GLTheoremA.isPGroup_zpowers_of_pow_eq_one hyp
  obtain ⟨labL, hXL, hin⟩ := innDiagKind_chevAut hy hq hInn
  have hlamL := CanonSubcomp.lambda2_of_hasLabel hXL
  obtain ⟨lab₀, hp₀, hX₀⟩ := exists_label_of_marking (S := fun lab => p ∣ lab.n) h₀
  have hdvdL : p ∣ (canonLabel labL).n := by
    rw [Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hXL hX₀]
    exact hp₀.trans (CanonSubcomp.n_dvd_canonLabel_n (CanonSubcomp.lambda2_of_hasLabel hX₀))
  have hn2 : 2 ≤ labL.n := by
    by_contra hlt
    have hn1 : labL.n = 1 := by have := hlamL.1; omega
    have h2 := canonLabel_n_dvd_two_mul labL
    rw [hn1, mul_one] at h2
    have := Nat.le_of_dvd two_pos (hdvdL.trans h2)
    have := hp.two_le
    omega
  obtain ⟨labJ, -, hJL⟩ := exists_label_of_marking (S := fun _ => True) hJM
  suffices hcJ : p ∣ (canonLabel labJ).n by
    have h2 : p ∣ 2 * labJ.n := hcJ.trans (canonLabel_n_dvd_two_mul labJ)
    have hpJ : p ∣ labJ.n :=
      Nat.Coprime.dvd_of_dvd_mul_left ((Nat.coprime_primes hp Nat.prime_two).2 hp2) h2
    exact hasLabel_mono (T := fun lab => p ∣ lab.n) (fun l hl => by rw [hl]; exact hpJ) hJL
  have hJs := glaPComponent_chevTransfer hp hy hap hJ
  obtain ⟨eJ⟩ := nonempty_pSimple_equiv_chevTransfer hp hy hap hJ
  by_cases hβ1 : chevAut p K ⟨y, hy⟩ = 1
  ·
    obtain ⟨-, huniq, -, -, -, ⟨e⟩⟩ :=
      glaPLayer_inf_centralizer hp hK hap ((chevAut_eq_one_iff hp hK hy).1 hβ1)
    rw [← huniq J hJ] at e
    have hJL' : HasLabel (PQuot p J) (· = labL) := (hasLabel_congr e _).2 hXL
    rw [Y10GInnExcLabel.canonLabel_eq_of_hasLabel hRig hJL hJL']
    exact hdvdL
  have hβp : chevAut p K ⟨y, hy⟩ ^ p = 1 := chevAut_pow_eq_one p K hy hyp
  have hβD := CanonSubcomp.mem_innAutDerived_of_innDiagKind hRest hcen hn2 hin
  have hc := CanonSubcomp.markChar_eq_two_of_two_le hlamL hn2
  have hLM := CanonSubcomp.markedModel_of_hasLabel hXL
  unfold CFSG.StandardType.MarkedModel at hLM
  rw [hc] at hLM
  obtain ⟨hsimple, hna⟩ := chev_pSimple_simple_nonabelian hp hK
  rcases CanonSubcomp.exists_index_or_small_of_lieModel_two hLM with ⟨d, hd2, ⟨e⟩⟩ | h60 | h1
  ·
    have hpd : p ≠ d.1.characteristic := by rw [hd2]; exact hp2
    have hpil := hLSC (PSimple p K) hsimple hna d ⟨e⟩ p hp hp2 hpd _ hβp hβ1
    have hJle := hpil _ hJs.1 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJs)
    have hJc :=
      (CFSG.HardMathSupport.Solomon.Coordinator.glaPComponent_isComponent_of_le_layer hJs hJle).1
    obtain ⟨i, ⟨φ⟩, hrel⟩ := KD264Lie.compIdxAt_of_mulEquiv e.symm
      (hIdx d p hp hp2 hpd trivial) _ hβD hβp hβ1 _ hJc
    have hfs := CanonSubcomp.two_pow_canonLabel_n_of_lie hRig hXL d hd2 e
    obtain ⟨eA⟩ := nonempty_centerQuot_equiv_pSimple hp hJs hJc.2.2
    have hJsl : HasLabel ↥(chevTransfer p K J) (· = labJ) :=
      hasLabel_of_equiv_centerQuot hJc.2.2.1 (eJ.trans eA.symm) hJL
    exact hdvdL.trans (CanonSubcomp.dvd_canonLabel_n_of_compRelC hRig hJsl hd2 hfs.symm φ hrel)
  ·
    exfalso
    have hfix : fixSubgroup (chevAut p K ⟨y, hy⟩) ≠ ⊤ := by
      intro h
      apply hβ1
      ext s
      have hs : s ∈ fixSubgroup (chevAut p K ⟨y, hy⟩) := by
        rw [h]
        exact Subgroup.mem_top s
      exact mem_fixSubgroup.1 hs
    have hlt : Nat.card ↥(chevTransfer p K J) < 60 := by
      rw [← h60]
      calc Nat.card ↥(chevTransfer p K J)
          ≤ Nat.card ↥(fixSubgroup (chevAut p K ⟨y, hy⟩)) := Subgroup.card_le_of_le hJs.1
        _ < Nat.card ↥(⊤ : Subgroup (PSimple p K)) :=
          Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hfix)
        _ = Nat.card (PSimple p K) := Subgroup.card_top
    haveI := CFSG.GroupTheory.groups_order_below_sixty_solvable hlt
    have hQs := isQuasisimple_pQuot_of_glaPComponent hp hJs
    haveI := hQs.2
    haveI : Nontrivial (PQuot p (chevTransfer p K J)) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p (chevTransfer p K J)))).nontrivial
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial
      (PQuot p (chevTransfer p K J))).ne hQs.1
  ·
    exfalso
    have h1' : (canonLabel labL).n = 1 :=
      (CanonSubcomp.canonLabel_n_eq_markDeg hlamL hc).trans h1
    rw [h1'] at hdvdL
    exact hp.ne_one (Nat.dvd_one.1 hdvdL)

end Inputs

section Holds


theorem t1428FieldFact_holds : T1428FieldFact :=
  t1428FieldFact_of_inputs CFSG.StandardType.ggLabelRigidInput_holds
    CFSG.StandardType.ggInndiagCommRestInput_holds KD264Lie.lieCompIdx_all
    CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.lieSemisimpleCent

end Holds

end CFSG.LocalAnalysis.GLTheoremA.T1428

end
