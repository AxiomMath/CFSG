module

public import CFSG.LocalAnalysis.GLTheoremA.PartI.RankTwoDownAux
public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.SRTReeF4
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.RankThree.PartOne.CTP.SeitzExcModels
import CFSG.LocalAnalysis.GLTheoremA.S4.Lemma49i
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
import CFSG.HardMathSupport.Timmesfeld.Proving.OmegaPiGroup

public section

namespace CFSG.LocalAnalysis.GLTheoremA

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

theorem rf4_kLevel_le_two {p : ℕ} {S : Type} [Group S] (h : catalogIs S (k2 p)) :
    kLevel p S ≤ 2 := by
  unfold kLevel
  split_ifs <;> first | omega | exact absurd h ‹_›

theorem rf4_eq_of_glaPComponent {p : ℕ} {G : Type} [Group G] [Finite G] {X I : Subgroup G}
    (hI : GLAPComponent p X I) (hXq : CFSG.Open.IsQuasisimple ↥X) : I = X :=
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53Ns.eq_of_perfect_subnormal_of_quasisimple
    hXq hI.1 hI.2.1 (glaPComponent_perfect hI) (glaPComponent_ne_bot' hI)

theorem rf4_pSimple_equiv_center {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    {X I : Subgroup G} (hI : GLAPComponent p X I) (hIq : CFSG.Open.IsQuasisimple ↥I) :
    Nonempty (PSimple p I ≃* (↥I ⧸ Subgroup.center ↥I)) := by
  have hQ : CFSG.Open.IsQuasisimple (PQuot p I) := isQuasisimple_pQuot_of_glaPComponent hp hI
  haveI : Nontrivial (PQuot p I ⧸ Subgroup.center (PQuot p I)) := hQ.2.toNontrivial
  have hne : GLAPPrimeCore p ↥I ≠ ⊤ := by
    intro htop
    have hsub : Subsingleton (PQuot p I) := by
      show Subsingleton (↥I ⧸ GLAPPrimeCore p ↥I)
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have hnt : Nontrivial (PQuot p I) :=
      (QuotientGroup.mk'_surjective (Subgroup.center (PQuot p I))).nontrivial
    exact (not_subsingleton_iff_nontrivial.2 hnt) hsub
  have hle : GLAPPrimeCore p ↥I ≤ Subgroup.center ↥I :=
    le_center_of_normal_of_isQuasisimple hIq inferInstance hne
  have hker : (QuotientGroup.mk' (GLAPPrimeCore p ↥I) : ↥I →* PQuot p I).ker ≤
      Subgroup.center ↥I := by
    rw [QuotientGroup.ker_mk']
    exact hle
  obtain ⟨e⟩ := CFSG.HardMathSupport.Solomon.Coordinator.LieComp.nonempty_centralQuotient_mulEquiv
    hIq.1 (QuotientGroup.mk' (GLAPPrimeCore p ↥I)) (QuotientGroup.mk'_surjective _) hker
  exact ⟨e.symm⟩

theorem rf4_pSimple_equiv_of_simple {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    (K : Subgroup G) [IsSimpleGroup ↥K] (hnc : ∃ a b : ↥K, a * b ≠ b * a)
    (hdvd : p ∣ Nat.card ↥K) : Nonempty (PSimple p K ≃* ↥K) := by
  have hO : GLAPPrimeCore p ↥K = ⊥ :=
    CFSG.HardMathSupport.Timmesfeld.Proving.glaPPrimeCore_eq_bot_of_isSimpleGroup hp hdvd
  let pq0 : PQuot p K ≃* ↥K := (QuotientGroup.quotientMulEquivOfEq hO).trans QuotientGroup.quotientBot
  have hZK : Subgroup.center ↥K = ⊥ := CFSG.HardMathSupport.Solomon.Coordinator.b3Lie_center_eq_bot hnc
  have hZP : Subgroup.center (PQuot p K) = ⊥ := by
    have h1 := Subgroup.map_center_eq pq0
    rw [hZK] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ pq0.injective).1 h1
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hZP).trans (QuotientGroup.quotientBot.trans pq0)⟩

theorem rf4_level_of_simple_derived {p : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    {X D : Subgroup G} (hDX : D ≤ X) (hPD : ∀ P : Subgroup G, P ≤ X → ⁅P, P⁆ = P → P ≤ D)
    [IsSimpleGroup ↥D] (hnc : ∃ a b : ↥D, a * b ≠ b * a) (hdvd : p ∣ Nat.card ↥D)
    (hk : kLevel p ↥D ≤ 2) (I : Subgroup G) (hI : GLAPComponent p X I) :
    kLevel p (PSimple p I) ≤ 2 := by
  have hIle : I ≤ D := hPD I hI.1 (glaPComponent_perfect hI)
  have hsub : CFSG.Open.IsSubnormal I D := by
    have h := CFSG.Open.IsSubnormal.inf_of_le hI.2.1 hDX
    rwa [inf_eq_left.2 hIle] at h
  rcases CFSG.Open.IsSubnormal.eq_bot_or_eq_of_isSimpleGroup hsub inferInstance with h | h
  · exact absurd h (glaPComponent_ne_bot' hI)
  · subst h
    obtain ⟨f⟩ := rf4_pSimple_equiv_of_simple hp I hnc hdvd
    rw [kLevel_congr p f]
    exact hk

theorem rf4_congr_self {P : Type} [Group P] (ϕ x : MulAut P) :
    MulAut.congr (ϕ : P ≃* P) x = ϕ * x * ϕ⁻¹ := by
  ext y
  rfl

theorem rf4_claim_congr {p j : ℕ} (hp : p.Prime) {G : Type} [Group G] [Finite G]
    (e : G ≃* G) (α : MulAut G)
    (h : ∀ I : Subgroup G, GLAPComponent p (fixSubgroup α) I → kLevel p (PSimple p I) ≤ j) :
    ∀ I : Subgroup G, GLAPComponent p (fixSubgroup (MulAut.congr e α)) I →
      kLevel p (PSimple p I) ≤ j := by
  intro J hJ
  have hcong : MulAut.congr e.symm (MulAut.congr e α) = α := by
    ext x
    simp [MulAut.congr_apply]
  obtain ⟨hJ', ⟨f⟩⟩ := rtd_exists_pSimple_equiv_map hp e.symm (MulAut.congr e α) hJ
  rw [hcong] at hJ'
  rw [kLevel_congr p f]
  exact h _ hJ'

noncomputable def rf4_commutatorEquiv {A B : Type} [Group A] [Group B] (e : A ≃* B) :
    ↥(commutator A) ≃* ↥(commutator B) :=
  ((commutator A).equivMapOfInjective e.toMonoidHom e.injective).trans
    (MulEquiv.subgroupCongr (by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.surjective]))

theorem rf4_nonab_of_not_prime {S : Type} [Group S] [IsSimpleGroup S]
    (hc : ¬ (Nat.card S).Prime) : ∃ a b : S, a * b ≠ b * a := by
  by_contra h
  simp only [not_exists, ne_eq, not_not] at h
  letI : CommGroup S := { ‹Group S› with mul_comm := fun a b => h a b }
  exact hc ((CommGroup.is_simple_iff_prime_card (α := S)).1 ‹IsSimpleGroup S›)

theorem rf4_card_tits
    {S : Type} [Group S] (he : Nonempty (S ≃* (TauCeti.CFSGIndex.lie
      ⟨.tits, CFSG.HardMathSupport.Solomon.Coordinator.LieComp.tits_valid⟩).Group)) :
    Nat.card S = 17971200 := by
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv S 2 1
    (CFSG.RankThree.PartOne.CTP.reeTitsModel_tits (S := S)
      ⟨CFSG.HardMathSupport.Solomon.Coordinator.LieComp.tits_valid, he⟩)
  rw [Nat.card_congr e.toEquiv, CFSG.Sporadic.Schreier.Tits.card_titsD]

end CFSG.LocalAnalysis.GLTheoremA
