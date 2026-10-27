module

public import CFSG.LieType.SeitzGeneration.ExcHigh.Classes
public import CFSG.LieType.SeitzGeneration.ExcHigh.Product
public import CFSG.LieType.SeitzGeneration.ExcHigh.NativeCond
public import CFSG.HardMathSupport.Lang.AnisoF4.B4Planes
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofE7Frame
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofWeylWord
public import CFSG.ClassicalInvolution.RouteD.MultiModelRoot
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTorus
public import CFSG.LieType.SeitzGeneration.OrthManyMaster

public section

namespace CFSG.LieType.SeitzGeneration.ExcHigh

open scoped MatrixGroups
open CFSG.ComponentClassification
open CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley CFSG.LieType.CurtisTits
  CFSG.ComponentClassification.CatLeafProof CFSG.TauCetiBridge TauCeti CFSG.Open
  CFSG.AGLEmbeddingD2 CFSG.HardMathSupport.Lang.AnisoF4 CFSG.StandardType.TableBExcTwo

@[expose] def e7w (l : List (Fin 7)) : List (Fin (Tag.rank .E7)) := l.map e7Node

@[expose] def e7Word : List (Fin (Tag.rank .E7)) := e7w [0, 2, 3, 1, 4, 3, 2, 0]

@[expose] def e7FramePerm : Fin 7 → Fin 7 := ![1, 0, 2, 3, 6, 5, 4]

theorem e7FramePerm_swap (i : Fin 7) : e7FramePerm (e7FramePerm i) = i := by
  revert i
  decide

theorem wordReflect_e7Word_frame : ∀ i : Fin 7,
    CatLeafProof.wordReflect .E7 e7Word (frameE7Root i) = frameE7Root (e7FramePerm i) := by decide

theorem exists_e7D6Node_eq : ∀ i : Fin (Tag.rank .E7), i ≠ 0 → ∃ k : Fin 6, e7D6Node k = i := by
  decide

section Roots


theorem e7Frame_isRoot : ∀ i, IsRoot .E7 (frameE7Root i) := by
  intro i
  rw [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  revert i
  decide +kernel

theorem e7Frame_facts : ∀ i j : Fin 7, i ≠ j → frameE7Root i ≠ frameE7Root j ∧
    frameE7Root i ≠ -frameE7Root j ∧ iform (frameE7Root i) (frameE7Root j) = 0 ∧
      ¬ IsRoot .E7 (frameE7Root i + frameE7Root j) ∧
        ¬ IsRoot .E7 (frameE7Root i + -frameE7Root j) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

theorem e7Theta_orth : ∀ k : Fin 6, e7Theta ≠ Pi.single (e7D6Node k) 1 ∧
    e7Theta ≠ -Pi.single (e7D6Node k) 1 ∧ iform e7Theta (Pi.single (e7D6Node k) 1) = 0 ∧
      ¬ IsRoot .E7 (e7Theta + Pi.single (e7D6Node k) 1) ∧
        ¬ IsRoot .E7 (e7Theta + -Pi.single (e7D6Node k) 1) := by
  simp only [RootCertificate.isRoot_iff (Tag.rootCertificate_check .E7)]
  decide +kernel

end Roots

section SpinPlane

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem closure_centralizers_spinPlus_plane {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpK : ¬ p ∣ Nat.card K) (hpq1 : ¬ p ∣ Nat.card K - 1) {r : ℕ}
    (hr : 4 ≤ r) (F : Subgroup (spinGroup (Spin.quadPlus r K))) (hF : IsElemAbelian p F)
    (hc : Nat.card F = p ^ 2) :
    Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x} = ⊤ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hn3 : 3 ≤ r := by omega
  haveI : NeZero r := ⟨by omega⟩
  have : Nonempty (Fin r ⊕ Fin r) := ⟨Sum.inl ⟨0, by omega⟩⟩
  have : Finite (spinGroup (quadPlus r K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := r) (K := K) hn3
  set π := spinToStatedProj (quadPlus r K) (range_spinMatrix_quadPlus hn3) with hπdef
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus r K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus r K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hπcop : ¬ p ∣ Nat.card π.ker := by
    intro hd
    apply hcen
    have : Nat.card π.ker ∣ Nat.card (Subgroup.center (spinGroup (quadPlus r K))) := by
      rw [hZ]
    exact hd.trans this
  have hperf : ⁅(⊤ : Subgroup (spinGroup (quadPlus r K))), ⊤⁆ = ⊤ :=
    (isPerfect_spinGroup_quadPlus hn3).commutator_eq_top
  have hEbarea : IsElemAbelian p (F.map π) := hF.map π
  have hcardEbar : Nat.card (F.map π) = p ^ 2 := by
    rw [card_map_eq_of_disjoint_ker π (disjoint_ker_of_exponent π hπcop hF.2), hc]
  have hmodel := orthogonalPlusPlanes r p K hr hp hp5 hpK (F.map π) hEbarea hcardEbar
  exact closure_centralizers_of_quotient π hπsurj hZ.le hπcop hperf F hF.2 hmodel

end SpinPlane

section Frame


noncomputable abbrev rootPairE7 (K : Type) [Field K] (γ : Fin (Tag.rank .E7) → ℤ) :
    Subgroup (adjointGroup .E7 K) :=
  (adjDatum (rootOperatorFamily .E7) K).rootGroup γ ⊔
    (adjDatum (rootOperatorFamily .E7) K).rootGroup (-γ)

@[expose] noncomputable def e7FrameGroup (K : Type) [Field K] : Subgroup (adjointGroup .E7 K) :=
  ⨆ i, rootPairE7 K (frameE7Root i)

@[expose] noncomputable def e7D6Group (K : Type) [Field K] : Subgroup (adjointGroup .E7 K) :=
  ⨆ k : Fin 6, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k)

@[expose] noncomputable def e7A1D6 (K : Type) [Field K] : Subgroup (adjointGroup .E7 K) :=
  e7D6Group K ⊔ rootPairE7 K e7Theta

section Lemmas

variable {K : Type} [Field K]

theorem rankOne_le_e7D6Group (k : Fin 6) :
    rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k) ≤ e7D6Group K :=
  le_iSup (fun k : Fin 6 => rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup (e7D6Node k)) k

theorem rootPairE7_wordReflect_le {M : Subgroup (adjointGroup .E7 K)}
    (ω : List (Fin (Tag.rank .E7))) (hω : ∀ i ∈ ω, weylElement .E7 K i ∈ M)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h : rootPairE7 K γ ≤ M) :
    rootPairE7 K (CatLeafProof.wordReflect .E7 ω γ) ≤ M := by
  have hn : weylWordElt .E7 K ω ∈ M := by
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    exact hω i hi
  have hmap := map_conj_weylWordElt_rootPair (K := K) ω hγ
  change (adjDatum (rootOperatorFamily .E7) K).rootGroup (CatLeafProof.wordReflect .E7 ω γ) ⊔
    (adjDatum (rootOperatorFamily .E7) K).rootGroup (-CatLeafProof.wordReflect .E7 ω γ) ≤ M
  rw [← hmap]
  rintro _ ⟨y, hy, rfl⟩
  exact M.mul_mem (M.mul_mem hn (h hy)) (M.inv_mem hn)

theorem weylElement_mem_e7A1D6 (i : Fin (Tag.rank .E7)) (hi : i ≠ 0) :
    weylElement .E7 K i ∈ e7A1D6 K := by
  obtain ⟨k, rfl⟩ := exists_e7D6Node_eq i hi
  exact Subgroup.mem_sup_left (rankOne_le_e7D6Group k
    (Steinberg.Adjoint.weylElement_mem_rankOne (F := rootOperatorFamily .E7) _))

theorem rootPairE7_theta_le_e7A1D6 : rootPairE7 K e7Theta ≤ e7A1D6 K := le_sup_right

theorem rootPairE7_simple_le_e7A1D6 (j : Fin 7) (hj : j ≠ 0) :
    rootPairE7 K (Pi.single (e7Node j) 1) ≤ e7A1D6 K := by
  obtain ⟨k, hkj⟩ := exists_e7D6Node_eq (e7Node j) (by revert j; decide)
  rw [← hkj]
  exact (rankOne_le_e7D6Group k).trans le_sup_left

theorem rootPairE7_wordReflect_le_e7A1D6 (ω : List (Fin (Tag.rank .E7))) (hω : ∀ i ∈ ω, i ≠ 0)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (h : rootPairE7 K γ ≤ e7A1D6 K) :
    rootPairE7 K (CatLeafProof.wordReflect .E7 ω γ) ≤ e7A1D6 K :=
  rootPairE7_wordReflect_le ω (fun i hi => weylElement_mem_e7A1D6 i (hω i hi)) hγ h

theorem rootPairE7_frame_le_e7A1D6 (i : Fin 7) :
    rootPairE7 K (frameE7Root i) ≤ e7A1D6 K := by
  fin_cases i
  · have e : frameE7Root 0 = e7Theta := by decide
    show rootPairE7 K (frameE7Root 0) ≤ _
    rw [e]
    exact rootPairE7_theta_le_e7A1D6
  · have h := rootPairE7_wordReflect_le_e7A1D6 (K := K)
      (e7w [5, 6, 4, 5, 3, 4, 2, 3]) (by decide) (γ := Pi.single (e7Node 1) 1) (isRoot_single _ _)
      (rootPairE7_simple_le_e7A1D6 1 (by decide))
    have e : CatLeafProof.wordReflect .E7 (e7w [5, 6, 4, 5, 3, 4, 2, 3]) (Pi.single (e7Node 1) 1) =
        frameE7Root 1 := by decide
    rwa [e] at h
  · have h := rootPairE7_wordReflect_le_e7A1D6 (K := K)
      (e7w [3, 4, 2, 3]) (by decide) (γ := Pi.single (e7Node 1) 1) (isRoot_single _ _)
      (rootPairE7_simple_le_e7A1D6 1 (by decide))
    have e : CatLeafProof.wordReflect .E7 (e7w [3, 4, 2, 3]) (Pi.single (e7Node 1) 1) =
        frameE7Root 2 := by decide
    rwa [e] at h
  · have e : frameE7Root 3 = Pi.single (e7Node 6) 1 := by decide
    show rootPairE7 K (frameE7Root 3) ≤ _
    rw [e]
    exact rootPairE7_simple_le_e7A1D6 6 (by decide)
  · have e : frameE7Root 4 = Pi.single (e7Node 4) 1 := by decide
    show rootPairE7 K (frameE7Root 4) ≤ _
    rw [e]
    exact rootPairE7_simple_le_e7A1D6 4 (by decide)
  · have e : frameE7Root 5 = Pi.single (e7Node 2) 1 := by decide
    show rootPairE7 K (frameE7Root 5) ≤ _
    rw [e]
    exact rootPairE7_simple_le_e7A1D6 2 (by decide)
  · have e : frameE7Root 6 = Pi.single (e7Node 1) 1 := by decide
    show rootPairE7 K (frameE7Root 6) ≤ _
    rw [e]
    exact rootPairE7_simple_le_e7A1D6 1 (by decide)

theorem e7FrameGroup_le_e7A1D6 : e7FrameGroup K ≤ e7A1D6 K :=
  iSup_le fun i => rootPairE7_frame_le_e7A1D6 i

theorem e7FrameGroup_le_conj_e7A1D6 : e7FrameGroup K ≤
    (e7A1D6 K).map (MulAut.conj (weylWordElt .E7 K e7Word)).toMonoidHom := by
  refine iSup_le fun i => ?_
  have h := map_conj_weylWordElt_rootPair (K := K) e7Word (e7Frame_isRoot (e7FramePerm i))
  rw [wordReflect_e7Word_frame, e7FramePerm_swap] at h
  change (adjDatum (rootOperatorFamily .E7) K).rootGroup (frameE7Root i) ⊔
    (adjDatum (rootOperatorFamily .E7) K).rootGroup (-frameE7Root i) ≤ _
  rw [← h]
  exact Subgroup.map_mono (rootPairE7_frame_le_e7A1D6 _)

theorem eq_top_of_e7A1D6_le_of_conj_le (M : Subgroup (adjointGroup .E7 K))
    (hX : e7A1D6 K ≤ M)
    (hn : (e7A1D6 K).map (MulAut.conj (weylWordElt .E7 K e7Word)).toMonoidHom ≤ M) :
    M = ⊤ := by
  have hα6 : rootPairE7 K (Pi.single (e7Node 5) 1) ≤ e7A1D6 K :=
    rootPairE7_simple_le_e7A1D6 5 (by decide)
  have hmap := map_conj_weylWordElt_rootPair (K := K) e7Word
    (γ := Pi.single (e7Node 5) 1) (isRoot_single _ _)
  have hγ : rootPairE7 K (CatLeafProof.wordReflect .E7 e7Word (Pi.single (e7Node 5) 1)) ≤ M := by
    change (adjDatum (rootOperatorFamily .E7) K).rootGroup
      (CatLeafProof.wordReflect .E7 e7Word (Pi.single (e7Node 5) 1)) ⊔
      (adjDatum (rootOperatorFamily .E7) K).rootGroup
      (-CatLeafProof.wordReflect .E7 e7Word (Pi.single (e7Node 5) 1)) ≤ M
    rw [← hmap]
    exact (Subgroup.map_mono hα6).trans hn
  have h0 : rootPairE7 K (Pi.single (e7Node 0) 1) ≤ M := by
    have h := rootPairE7_wordReflect_le (K := K) (e7w [2, 3, 4, 5])
      (fun i hi => hX (weylElement_mem_e7A1D6 i (by
        have : ∀ i ∈ e7w [2, 3, 4, 5], i ≠ 0 := by decide
        exact this i hi)))
      (isRoot_wordReflect _ (isRoot_single _ _)) hγ
    have e : CatLeafProof.wordReflect .E7 (e7w [2, 3, 4, 5])
        (CatLeafProof.wordReflect .E7 e7Word (Pi.single (e7Node 5) 1)) =
        Pi.single (e7Node 0) 1 := by decide
    rwa [e] at h
  have hall : ⨆ i, rankOne (adjDatum (rootOperatorFamily .E7) K).rootGroup i ≤ M := by
    refine iSup_le fun i => ?_
    by_cases hi : i = 0
    · subst hi
      exact h0
    · obtain ⟨k, hk⟩ := exists_e7D6Node_eq i hi
      rw [← hk]
      exact ((rankOne_le_e7D6Group k).trans le_sup_left).trans hX
  rw [CFSG.ClassicalInvolution.RouteD.iSup_rankOne_eq_top
    (adjDatum_isCTGroupDatum (rootOperatorFamily .E7) K)] at hall
  exact eq_top_iff.2 hall

end Lemmas

@[expose] def E7TwoSylow : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 11 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K

@[expose] def E7TwoA1D6 : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 11 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E : Subgroup (adjointGroup .E7 K), E ≤ e7A1D6 K → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 →
        e7A1D6 K ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x}

@[expose] def E7TwoNative : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 11 ≤ p → p ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤

theorem closure_centralizers_eq_top_of_conj_frame {K : Type} [Field K] {p : ℕ}
    (hX : ∀ E : Subgroup (adjointGroup .E7 K), E ≤ e7A1D6 K → (∀ x ∈ E, x ^ p = 1) →
      Nat.card E = p ^ 2 →
        e7A1D6 K ≤ Subgroup.closure {g | ∃ x ∈ E, x ≠ 1 ∧ Commute g x})
    (E₀ : Subgroup (adjointGroup .E7 K)) (hE₀p : ∀ x ∈ E₀, x ^ p = 1) (hE₀c : Nat.card E₀ = p ^ 2)
    (hconj : ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K) :
    Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ :=
  closure_centralizers_eq_top_of_two_conj (p := p) (e7A1D6 K) (e7FrameGroup K)
    (weylWordElt .E7 K e7Word) e7FrameGroup_le_e7A1D6 e7FrameGroup_le_conj_e7A1D6
    (fun M hX' hn => eq_top_of_e7A1D6_le_of_conj_le M hX' hn) hX E₀ hE₀p hE₀c hconj

theorem e7TwoNative_of_interfaces (h1 : E7TwoSylow) (h2 : E7TwoA1D6) : E7TwoNative := by
  intro K _ _ p hpF hp11 hpq E₀ hE₀p hE₀c
  exact closure_centralizers_eq_top_of_conj_frame
    (fun E hE hEp hEc => h2 K p hp11 hpq E hE hEp hEc) E₀ hE₀p hE₀c
    (h1 K p hp11 hpq E₀ hE₀p hE₀c)

@[expose] def E7TwoSylowLow : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 5 ≤ p → p < 11 → p ∣ Nat.card K + 1 →
    ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
      ¬ NormalizesRGroup (ringChar K) E₀ →
        ∃ g : adjointGroup .E7 K, E₀.map (MulAut.conj g).toMonoidHom ≤ e7FrameGroup K

end Frame

section Native


section SylowFrame

variable {K : Type} [Field K]

theorem exists_sl2_hom_rootPairE7 {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ∃ ρ : SL(2, K) →* adjointGroup .E7 K, Function.Injective ρ ∧ ρ.range = rootPairE7 K γ := by
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  choose ρF hρFi hρFr _ using exists_rankOne_param hE
  induction hγ with
  | basis j => exact ⟨ρF j, hρFi j, hρFr j⟩
  | reflect i hv ih =>
    obtain ⟨ρ, hρi, hρr⟩ := ih
    refine ⟨(MulAut.conj (weylElement .E7 K i)).toMonoidHom.comp ρ,
      (MulAut.conj _).injective.comp hρi, ?_⟩
    rw [MonoidHom.range_comp, hρr]
    exact map_conj_weylElement_rootPair_adj i hv

theorem e7Frame_hom : ∃ ρ : Fin 7 → SL(2, K) →* adjointGroup .E7 K,
    (∀ i, Function.Injective (ρ i)) ∧ (∀ i, (ρ i).range = rootPairE7 K (frameE7Root i)) ∧
      ∀ i j, i ≠ j → ∀ x y, Commute (ρ i x) (ρ j y) := by
  choose ρ hρi hρr using fun i => exists_sl2_hom_rootPairE7 (K := K) (e7Frame_isRoot i)
  refine ⟨ρ, hρi, hρr, fun i j hij x y => ?_⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := e7Frame_facts i j hij
  have hc := commutes_rootPair_of_noG2 (K := K) noG2_E7 (e7Frame_isRoot i) (e7Frame_isRoot j)
    h1 h2 h3 h4 h5
  have hx : ρ i x ∈ rootPairE7 K (frameE7Root i) := by
    rw [← hρr i]
    exact ⟨x, rfl⟩
  have hy : ρ j y ∈ rootPairE7 K (frameE7Root j) := by
    rw [← hρr j]
    exact ⟨y, rfl⟩
  exact hc _ hx _ hy

section Card

variable [Finite K]

theorem factorization_card_E7_of_dvd_add_one {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    (Nat.card (adjointGroup .E7 K)).factorization p = 7 * (Nat.card K + 1).factorization p := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hq2 : 2 ≤ Nat.card K :=
    Nat.succ_le_of_lt (Finite.one_lt_card_iff_nontrivial.2 inferInstance)
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hsq : ((Nat.card K : ℕ) : ZMod p) ^ 2 = 1 := by
    have h : ((Nat.card K + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 hpq
    push_cast at h
    linear_combination ((Nat.card K : ZMod p) - 1) * h
  have hne1 : ((Nat.card K : ℕ) : ZMod p) ≠ 1 := by
    intro h1
    have h2 : p ∣ Nat.card K - 1 := by
      rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hq1, h1, Nat.cast_one, sub_self]
    exact hpq1 h2
  have hord : orderOf ((Nat.card K : ℕ) : ZMod p) = 2 := by
    have hd : orderOf ((Nat.card K : ℕ) : ZMod p) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
    rcases (Nat.dvd_prime Nat.prime_two).1 hd with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hne1
    · exact h
  have h1 := ordProj_card_adjointGroup_E (τ := .E7) (Or.inr (Or.inl rfl)) (K := K) hp (by omega)
    hpK
  have h2 := prod_ordProj_pow_sub_one hp (by omega) hpK hq2 hord (degreesE .E7) (by
    intro d hd hde
    refine ⟨?_, ?_⟩
    · rintro rfl
      simp [degreesE] at hd
    · simp only [degreesE, List.mem_cons, List.not_mem_nil, or_false] at hd
      intro hdv
      have hle : p ≤ d / 2 := Nat.le_of_dvd (by omega) hdv
      have hd9 : d / 2 ≤ 9 := by
        rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num
      omega)
  rw [h2] at h1
  have h3 : (degreesE .E7).filter (fun d => 2 ∣ d) = degreesE .E7 := by
    simp [degreesE]
  rw [h3] at h1
  have h4 : (degreesE .E7).length = 7 := rfl
  rw [h4, ← pow_mul] at h1
  have h5 := Nat.pow_right_injective hp.two_le h1
  have e2 : Nat.card K ^ 2 - 1 = (Nat.card K - 1) * (Nat.card K + 1) := by
    obtain ⟨m, hm⟩ : ∃ m, Nat.card K = m + 1 := ⟨Nat.card K - 1, by omega⟩
    rw [hm]
    simp only [Nat.add_sub_cancel]
    zify [Nat.one_le_pow 2 (m + 1) (by omega)]
    ring
  have hq21 : Nat.card K - 1 ≠ 0 := by
    intro h
    apply hpq1
    rw [h]
    exact dvd_zero p
  have hq22 : Nat.card K + 1 ≠ 0 := by omega
  rw [h5, show Nat.card K ^ 2 = Nat.card K ^ 2 from rfl, e2,
    Nat.factorization_mul hq21 hq22, Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hpq1,
    zero_add, mul_comm]

end Card

end SylowFrame

section ClassicalA1D6

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin
  CFSG.ClassicalInvolution.ModelFacts.OrthAut

theorem exists_psi_D6_E7 (K : Type) [Field K] [Finite K] :
    ∃ Ψ : spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K,
      Ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadPlus 6 K)) ∧ Ψ.range = e7D6Group K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨n, hℓ, hn⟩ := FiniteField.card K (ringChar K)
  have hK : Nat.card K = ringChar K ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn
  have hadm : StatedLieAdmissible .POmegaPlus 6 (ringChar K) n := ⟨hℓ, n.pos, by norm_num⟩
  obtain ⟨O, C, hE⟩ := exists_e7_chevalleyExtras K
  obtain ⟨ρ, hρ, hcomm, hψ⟩ := exists_levi_frame hE rfl e7D6Node e7D6_adj e7D6_nadj
  obtain ⟨Ψ, h1, h2, -, -⟩ := spinPlus_frame_subgroup hadm (by norm_num) hK hcomm hρ hψ
  exact ⟨Ψ, h1, h2⟩

theorem e7A1D6_le_closure_centralizers_two {K : Type} [Field K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (F : Subgroup (adjointGroup .E7 K)) (hF : F ≤ e7A1D6 K) (hFp : ∀ x ∈ F, x ^ p = 1)
    (hFc : Nat.card F = p ^ 2) :
    e7A1D6 K ≤ Subgroup.closure {g | ∃ x ∈ F, x ≠ 1 ∧ Commute g x} := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hpK : ¬ p ∣ Nat.card K := by
    intro hd
    have h1 : p ∣ 1 := (Nat.dvd_add_right hd).mp hpq
    exact hp.one_lt.ne' (Nat.dvd_one.mp h1)
  have hpq1 : ¬ p ∣ Nat.card K - 1 := by
    intro hd
    have hq1 : 1 ≤ Nat.card K := Nat.card_pos
    have h3 : p ∣ (Nat.card K + 1) - (Nat.card K - 1) := Nat.dvd_sub hpq hd
    have e : (Nat.card K + 1) - (Nat.card K - 1) = 2 := by omega
    rw [e] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  have hpK0 : (p : K) ≠ 0 := natCast_ne_zero_of_not_dvd_card hp hpK
  have hn3 : 3 ≤ 6 := by norm_num
  have : Nonempty (Fin 6 ⊕ Fin 6) := ⟨Sum.inl 0⟩
  have : Finite (spinGroup (quadPlus 6 K)) :=
    CFSG.ClassicalInvolution.ModelFacts.finite_spinGroup_of_ker _ coe_ker_spinMatrix_quadPlus
  obtain ⟨Ψ, hker, hrange⟩ := exists_psi_D6_E7 K
  obtain ⟨ρ, hρi, hρr⟩ := exists_sl2_hom_rootPairE7 (K := K) isRoot_e7Theta
  have hcentr : e7D6Group K ≤
      Subgroup.centralizer (rootPairE7 K e7Theta : Set (adjointGroup .E7 K)) := by
    refine iSup_le fun k => ?_
    intro y hy x hx
    obtain ⟨h1, h2, h3, h4, h5⟩ := e7Theta_orth k
    exact commutes_rootPair_of_noG2 (K := K) noG2_E7 isRoot_e7Theta (isRoot_single _ _)
      h1 h2 h3 h4 h5 x hx y hy
  have hcomm : ∀ (a : SL(2, K)) (t : spinGroup (Spin.quadPlus 6 K)), Commute (ρ a) (Ψ t) := by
    intro a t
    have hx : ρ a ∈ rootPairE7 K e7Theta := hρr ▸ ⟨a, rfl⟩
    have hy : Ψ t ∈ e7D6Group K := hrange ▸ ⟨t, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 (hcentr hy) _ hx
  let ψ : SL(2, K) × spinGroup (Spin.quadPlus 6 K) →* adjointGroup .E7 K :=
    MonoidHom.noncommCoprod ρ Ψ hcomm
  have hrangeψ : ψ.range = e7A1D6 K := by
    rw [MonoidHom.noncommCoprod_range, hρr, hrange, e7A1D6, sup_comm]
  obtain ⟨hπsurj, hcomap, hZ⟩ := spinToStatedProj_quadPlus (n := 6) (K := K) hn3
  have hcen : ¬ p ∣ Nat.card (Subgroup.center (spinGroup (quadPlus 6 K))) :=
    not_dvd_card_center_spin_of_not_dvd_pred (quadPlus 6 K) (range_spinMatrix_quadPlus hn3)
      hZ hcomap
      (fun x hx => spin_mul_self_eq_one ((mem_ker_spinMatrix_quadPlus_iff x).mp hx)) hp2 hpq1
  have hψker : ¬ p ∣ Nat.card ψ.ker := by
    intro hd
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' p hd
    obtain ⟨⟨a, s⟩, hxk⟩ := x
    have hxk' : ρ a * Ψ s = 1 := hxk
    have hxp : (a, s) ^ p = 1 := by
      have := pow_orderOf_eq_one (⟨(a, s), hxk⟩ : ψ.ker)
      rw [hx] at this
      exact congrArg Subtype.val this
    have hap : a ^ p = 1 := congrArg Prod.fst hxp
    have hsp : s ^ p = 1 := congrArg Prod.snd hxp
    have hacent : a ∈ Subgroup.center SL(2, K) := by
      rw [Subgroup.mem_center_iff]
      intro b
      have h1 : ρ a = (Ψ s)⁻¹ := eq_inv_of_mul_eq_one_left hxk'
      have h2 : Commute (ρ b) (ρ a) := by
        rw [h1]
        exact (hcomm b s).inv_right
      apply hρi
      rw [map_mul, map_mul]
      exact h2.eq
    obtain ⟨r, hr, hra⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hacent
    simp only [Fintype.card_fin] at hr
    have ha2 : a * a = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul, ← hra, ← map_mul, ← pow_two, hr, map_one,
        Matrix.SpecialLinearGroup.coe_one]
    have ha1 : a = 1 := by
      have hcop : Nat.Coprime 2 p := (Nat.coprime_primes Nat.prime_two hp).2 (by omega)
      have hd2 : orderOf a ∣ Nat.gcd 2 p :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one (by rwa [pow_two])) (orderOf_dvd_of_pow_eq_one hap)
      rw [hcop] at hd2
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd2)
    have hΨs : Ψ s = 1 := by
      rw [ha1, map_one, one_mul] at hxk'
      exact hxk'
    have hs1 : s = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd hcen (hker (MonoidHom.mem_ker.2 hΨs)) hsp
    have hx1 : (⟨(a, s), hxk⟩ : ψ.ker) = 1 := Subtype.ext (Prod.ext ha1 hs1)
    rw [hx1, orderOf_one] at hx
    exact hp.one_lt.ne hx
  have hH : ∀ F' : Subgroup (SL(2, K) × spinGroup (Spin.quadPlus 6 K)), IsElemAbelian p F' →
      Nat.card F' = p ^ 2 → Subgroup.closure {h | ∃ x ∈ F', x ≠ 1 ∧ Commute h x} = ⊤ :=
    fun F' hF' hc => closure_centralizers_prod_of_plane
      (fun F'' hF'' => card_le_of_isElemAbelian_specialLinear_two hpK0 hF'')
      (fun F'' hF'' hc'' => closure_centralizers_spinPlus_plane hp hp5 hpK hpq1 (by norm_num) F''
        hF'' hc'') F' hF' hc
  have h := closure_in_range_of_cover ψ hψker hH F (hrangeψ ▸ hF) hFp hFc
  rw [hrangeψ] at h
  exact h.trans (Subgroup.closure_mono fun g hg => hg.2)

end ClassicalA1D6

theorem e7TwoSylow : E7TwoSylow := by
  intro K _ _ p hpF hp11 hpq E₀ hE₀p hE₀c
  obtain ⟨ρ, hρi, hρr, hρc⟩ := e7Frame_hom (K := K)
  have hcomm : Pairwise fun i j => ∀ x y : SL(2, K), Commute (ρ i x) (ρ j y) := by
    intro i j hij x y
    exact hρc i j hij x y
  obtain ⟨Q, -, hQ⟩ := exists_conj_le_frame_sylow ρ hρi hcomm (by omega) hpq
    (by rw [factorization_card_E7_of_dvd_add_one hpF.out hp11 hpq])
  obtain ⟨g, hg⟩ := hQ E₀ hE₀p
  refine ⟨g, hg.trans ((map_noncommPiCoprod_le ρ hcomm Q).trans ?_)⟩
  simp only [e7FrameGroup, hρr]
  exact le_rfl

theorem e7TwoA1D6 : E7TwoA1D6 := by
  intro K _ _ p hpF hp11 hpq E hE hEp hEc
  exact e7A1D6_le_closure_centralizers_two hpF.out (by omega) hpq E hE hEp hEc

theorem e7TwoNative : E7TwoNative := e7TwoNative_of_interfaces e7TwoSylow e7TwoA1D6

theorem e7TwoNativeLow_of_sylow (h1 : E7TwoSylowLow) :
    ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 5 ≤ p → p < 11 → p ∣ Nat.card K + 1 →
      ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ p = 1) → Nat.card E₀ = p ^ 2 →
        ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤ := by
  intro K _ _ p hpF hp5 hlt hpq E₀ hE₀p hE₀c hN
  exact closure_centralizers_eq_top_of_conj_frame
    (fun E hE hEp hEc => e7A1D6_le_closure_centralizers_two hpF.out hp5 hpq E hE hEp hEc)
    E₀ hE₀p hE₀c (h1 K p hp5 hlt hpq E₀ hE₀p hE₀c hN)

end Native

section Glue


@[expose] def SeitzExcHighE7TwoGeEleven : Prop :=
  SeitzExcHighForAt IsE7Index fun d p => 11 ≤ p ∧ ClassRange LieTypeIndex.E7 (fun _ => True) 2 d p

theorem seitzExcHighE7Two_of_native_for {R : ℕ → Prop}
    (h : ∀ (K : Type) [Field K] [Finite K] (p : ℕ) [Fact p.Prime], 5 ≤ p → R p →
      p ∣ Nat.card K + 1 → ∀ E₀ : Subgroup (adjointGroup .E7 K), (∀ x ∈ E₀, x ^ p = 1) →
        Nat.card E₀ = p ^ 2 → ¬ NormalizesRGroup (ringChar K) E₀ →
          Subgroup.closure {k | ∃ x ∈ E₀, x ≠ 1 ∧ Commute k x} = ⊤) :
    SeitzExcHighForAt IsE7Index fun d p =>
      R p ∧ ClassRange LieTypeIndex.E7 (fun _ => True) 2 d p := by
  intro d p hp _ _ _ E hE hcard hS
  obtain ⟨hin, -, ⟨hR, hp5, q, hdq, -, hord⟩, -, hn⟩ := hS
  obtain ⟨d₁, hv⟩ := d
  simp only at hdq
  subst hdq
  obtain ⟨K, _, _, hKq, hchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e7 q hv
  have : Fact p.Prime := ⟨hp⟩
  have hpq : p ∣ Nat.card K + 1 := by
    rw [hKq]
    exact dvd_add_one_of_orderOf_eq_two hp hord
  have hr : ringChar K = (LieTypeIndex.E7 q).characteristic := by
    rw [LieTypeIndex.characteristic_E7]
    exact ringChar.eq K q.p
  refine planeGen_of_native_closure_cond (r := ringChar K) e center_adjointGroup_eq_bot
    (fun E₀ hE₀p hE₀c hN => h K p hp5 hR hpq E₀ hE₀p hE₀c hN) hE hcard hin ?_
  rw [hr]
  exact hn

theorem seitzExcHighE7Two_of_native (h : E7TwoNative) : SeitzExcHighE7TwoGeEleven := by
  refine seitzExcHighE7Two_of_native_for (R := fun p => 11 ≤ p) ?_
  intro K _ _ p _ _ hp11 hpq E₀ hE₀p hE₀c _
  exact h K p hp11 hpq E₀ hE₀p hE₀c

theorem seitzExcHighE7Two_of_ge_eleven : SeitzExcHighE7TwoGeEleven :=
  seitzExcHighE7Two_of_native e7TwoNative

@[expose] def SeitzExcHighE7TwoLtEleven : Prop :=
  SeitzExcHighForAt IsE7Index fun d p => p < 11 ∧ ClassRange LieTypeIndex.E7 (fun _ => True) 2 d p

theorem seitzExcHighE7Two_of_ge_eleven_of_lt
    (h : SeitzExcHighE7TwoLtEleven) : SeitzExcHighE7Two :=
  SeitzExcHighForAt.union (fun d p _ _ hQ => (Nat.lt_or_ge p 11).elim (fun h' => Or.inr ⟨h', hQ⟩)
    (fun h' => Or.inl ⟨h', hQ⟩)) seitzExcHighE7Two_of_ge_eleven h

theorem seitzExcHighE7TwoLtEleven_of_sylow (h : E7TwoSylowLow) : SeitzExcHighE7TwoLtEleven :=
  seitzExcHighE7Two_of_native_for (R := fun p => p < 11) (e7TwoNativeLow_of_sylow h)

theorem seitzExcHighE7Two_of_sylow_low (h : E7TwoSylowLow) : SeitzExcHighE7Two :=
  seitzExcHighE7Two_of_ge_eleven_of_lt (seitzExcHighE7TwoLtEleven_of_sylow h)

end Glue

end CFSG.LieType.SeitzGeneration.ExcHigh
