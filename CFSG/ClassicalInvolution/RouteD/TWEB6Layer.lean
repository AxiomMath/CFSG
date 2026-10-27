module

public import CFSG.ClassicalInvolution.RouteD.NonClassicalLocal
public import CFSG.ClassicalInvolution.RouteD.GapsOrthFacts

public section

namespace CFSG.ClassicalInvolution.RouteD.TWE.B6

open CFSG.ClassicalInvolution.Generic CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
  CFSG.ClassicalInvolution.RouteD CFSG.ClassicalInvolution.RouteD.Gaps
open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution.WeakCT (LinearBlockStandardPair)
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)} {x : G}


structure Layer0 (p f : ℕ) [Fact p.Prime] {G : Type} [Group G] (Ω : Set (Subgroup G)) (x : G)
    (t : StatedLieTag) (n : ℕ) where
  φ : (modelUniv t n p f Fact.out).K →* locQuot Ω x
  ker_le : φ.ker ≤ Subgroup.center (modelUniv t n p f Fact.out).K
  mem : ∀ L ∈ centralizingMembers Ω {x}, ∃ R ∈ fundamentalSubgroups t
    (modelUniv t n p f Fact.out).D, locImg Ω x L = R.map φ
  comp : ∀ R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D,
    ∃ L ∈ centralizingMembers Ω {x}, locImg Ω x L = R.map φ

section Of

theorem Layer0.of_shape [Finite G] (hΩ : InClass p f Ω) (hex : ExactMembers Ω) {t : StatedLieTag}
    {n : ℕ} (hG2 : t ≠ .G2) (hD4 : t ≠ .trialityD4) (h : LocalShapeT p f 0 t n Ω x) :
    Nonempty (Layer0 p f Ω x t n) := by
  obtain ⟨D, hD, i₁, ht, hn, -⟩ := h
  have hi : ∀ i : Fin D.card, i = i₁ := fun i => Fin.ext (by
    have := i.2
    have := i₁.2
    omega)
  have hsc := fundamentalSingleClass_of_ne D i₁ (ht ▸ hG2) (ht ▸ hD4)
  have he : D.exp i₁ = f := by
    rcases D.exp_eq i₁ with h | ⟨h, -⟩
    · exact h
    · exact absurd (ht ▸ h) hD4
  have hmem : ∀ L ∈ centralizingMembers Ω {x}, ∃ R ∈ fundamentalSubgroups (D.tag i₁)
      (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).D,
      locImg Ω x L = R.map (D.hom i₁) := by
    intro L hL
    obtain ⟨i, R, hR⟩ := NonClassical.exists_corr_of_mem hΩ hex D hL
    obtain rfl := hi i
    exact ⟨R, hR.2.1, hR.2.2⟩
  have hcomp : ∀ R ∈ fundamentalSubgroups (D.tag i₁)
      (modelUniv (D.tag i₁) (D.rank i₁) p (D.exp i₁) Fact.out).D,
      ∃ L ∈ centralizingMembers Ω {x}, locImg Ω x L = R.map (D.hom i₁) := by
    intro R hR
    obtain ⟨N, hN⟩ := exists_corr_right hΩ D hsc hR
    exact ⟨N, hN.1, hN.2.2⟩
  have key : ∀ (t' : StatedLieTag) (n' e' : ℕ)
      (φ : (modelUniv t' n' p e' Fact.out).K →* locQuot Ω x), t' = t → n' = n → e' = f →
      φ.ker ≤ Subgroup.center (modelUniv t' n' p e' Fact.out).K →
      (∀ L ∈ centralizingMembers Ω {x}, ∃ R ∈ fundamentalSubgroups t'
        (modelUniv t' n' p e' Fact.out).D, locImg Ω x L = R.map φ) →
      (∀ R ∈ fundamentalSubgroups t' (modelUniv t' n' p e' Fact.out).D,
        ∃ L ∈ centralizingMembers Ω {x}, locImg Ω x L = R.map φ) →
      Nonempty (Layer0 p f Ω x t n) := by
    intro t' n' e' φ h1 h2 h3 hk hm hc
    subst h1 h2 h3
    exact ⟨⟨φ, hk, hm, hc⟩⟩
  exact key _ _ _ (D.hom i₁) ht hn he (D.ker_le_center i₁) hmem hcomp

end Of

section Transfer

variable [Finite G] {t : StatedLieTag} {n : ℕ}

theorem Layer0.commutes_iff (e : Layer0 p f Ω x t n) (hY : YData p f t n) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {L L' : Subgroup G}
    {R R' : Subgroup (modelUniv t n p f Fact.out).K} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x})
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) :
    Commutes L L' ↔ Commutes R R' := by
  rw [commutes_iff_locImg hΩ hP1 hL hL', hLR, hLR']
  constructor
  · intro hc
    exact commutes_of_commutes_map e.φ e.ker_le
      (Subgroup.isPerfect_iff.mpr (le_antisymm (Subgroup.commutator_le.mpr fun a ha b hb => by
        rw [commutatorElement_def]
        exact R.mul_mem (R.mul_mem (R.mul_mem ha hb) (R.inv_mem ha)) (R.inv_mem hb))
        (hY.perfR R hR))) hc
  · intro hc
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hc a ha b hb]

theorem Layer0.exists_involution (e : Layer0 p f Ω x t n) (hY : YData p f t n) {L : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) {R : Subgroup (modelUniv t n p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hLR : locImg Ω x L = R.map e.φ) {w : G} (hw : IsClassicalMember p f L w) :
    ∃ r, InvOf R r ∧ e.φ r = locElt Ω x w (le_centralizingLayer hL hw.mem) := by
  have hwx : w ∈ locLayer Ω x := le_centralizingLayer hL hw.mem
  have hmem : locElt Ω x w hwx ∈ R.map e.φ :=
    hLR ▸ locElt_mem_locImg (le_centralizingLayer hL) hw.mem
  obtain ⟨r, hrR, hr⟩ := hmem
  have h2 : orderOf (e.φ r) = 2 := by
    rw [hr]
    exact orderOf_locElt hwx hw.orderOf_eq_two
  have hsq : r * r = 1 := by
    have h1 : e.φ (r * r) = 1 := by
      rw [map_mul]
      have := pow_orderOf_eq_one (e.φ r)
      rwa [h2, pow_two] at this
    exact hY.central R hR (r * r) (R.mul_mem hrR hrR) (e.ker_le h1)
  have hr1 : r ≠ 1 := by
    intro h
    rw [h, map_one] at h2
    simp at h2
  exact ⟨r, ⟨hrR, orderOf_eq_prime (by rw [pow_two]; exact hsq) hr1⟩, hr⟩

theorem Layer0.modelInvComm (e : Layer0 p f Ω x t n) (hY : YData p f t n) {L L' : Subgroup G}
    (hL : L ∈ centralizingMembers Ω {x}) (hL' : L' ∈ centralizingMembers Ω {x})
    {R R' : Subgroup (modelUniv t n p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hc : Commute w w') :
    ∃ r r', InvOf R r ∧ InvOf R' r' ∧ ⁅r, r'⁆ ∈ Subgroup.center (modelUniv t n p f Fact.out).K ∧
      e.φ r = locElt Ω x w (le_centralizingLayer hL hw.mem) ∧
      e.φ r' = locElt Ω x w' (le_centralizingLayer hL' hw'.mem) := by
  obtain ⟨r, hr, hψr⟩ := e.exists_involution hY hL hR hLR hw
  obtain ⟨r', hr', hψr'⟩ := e.exists_involution hY hL' hR' hLR' hw'
  refine ⟨r, r', hr, hr', e.ker_le ?_, hψr, hψr'⟩
  have hcomm : e.φ r * e.φ r' = e.φ r' * e.φ r := by
    rw [hψr, hψr', locElt_mul, locElt_mul]
    congr 1
  rw [MonoidHom.mem_ker, map_commutatorElement]
  exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm

theorem Layer0.normalizes (e : Layer0 p f Ω x t n) (hY : YData p f t n) {L : Subgroup G}
    {R : Subgroup (modelUniv t n p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hLR : locImg Ω x L = R.map e.φ) {w : G} (hwx : w ∈ locLayer Ω x)
    {r : (modelUniv t n p f Fact.out).K} (hr : e.φ r = locElt Ω x w hwx)
    (hN : conjSub w L = L) : ∀ y ∈ R, r * y * r⁻¹ ∈ R := by
  refine conj_mem_of_perfect (hY.perfR R hR) r fun y hy => ?_
  have hmem : e.φ (r * y * r⁻¹) ∈ R.map e.φ := by
    have h1 : e.φ y ∈ locImg Ω x L := by
      rw [hLR]
      exact ⟨y, hy, rfl⟩
    have h2 : e.φ (r * y * r⁻¹) ∈ locImg Ω x (conjSub w L) := by
      have := locImg_conjSub_layer (Ω := Ω) (x := x) L ⟨w, hwx⟩
      rw [this]
      refine ⟨e.φ y, h1, ?_⟩
      simp only [map_mul, map_inv, hr]
      rfl
    rwa [hN, hLR] at h2
  obtain ⟨y', hy', hy'e⟩ := hmem
  refine ⟨y', hy', y'⁻¹ * (r * y * r⁻¹), e.ker_le ?_, by group⟩
  rw [MonoidHom.mem_ker, map_mul, map_inv, hy'e, inv_mul_cancel]

theorem Layer0.modelAdj (e : Layer0 p f Ω x t n) (hY : YData p f t n) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) {R R' : Subgroup (modelUniv t n p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) {w w' : G}
    (hw : IsClassicalMember p f L w) (hw' : IsClassicalMember p f L' w') (hne : L ≠ L')
    (hnc : ¬ Commutes L L') (hc : Commute w w') (hN : conjSub w' L = L) :
    ModelAdj (Subgroup.center (modelUniv t n p f Fact.out).K) R R' := by
  obtain ⟨r, r', hr, hr', hcen, hψr, hψr'⟩ := e.modelInvComm hY hL hL' hR hR' hLR hLR' hw hw' hc
  refine ⟨fun h => hne (locImg_injOn hΩ hP1 hL hL' (by rw [hLR, hLR', h])), ?_, r, r', hr, hr',
    hcen, ?_⟩
  · intro h
    exact hnc ((e.commutes_iff hY hΩ hP1 hL hL' hR hLR hLR').mpr h)
  · exact e.normalizes hY hR hLR (le_centralizingLayer hL' hw'.mem) hψr' hN

theorem Layer0.pair_to_model (e : Layer0 p f Ω x t n)
    (hF : OrthFacts (fundamentalSubgroups t (modelUniv t n p f Fact.out).D) (GaloisField p f))
    (hP1 : LocalOddCentral Ω {x}) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) {R R' : Subgroup (modelUniv t n p f Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hR' : R' ∈ fundamentalSubgroups t (modelUniv t n p f Fact.out).D)
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) {W : Subgroup G}
    (hW : LinearBlockStandardPair (GaloisField p f) W L L') :
    ∃ W' : Subgroup (modelUniv t n p f Fact.out).K,
      LinearBlockStandardPair (GaloisField p f) W' R R' := by
  obtain ⟨W', hW'⟩ := linearBlockStandardPair_locImg_of_members hP1 hL hL' hW
  rw [hLR, hLR'] at hW'
  exact hF.lift e.φ e.ker_le R hR R' hR' ⟨W', hW'⟩

theorem Layer0.pair_of_model (e : Layer0 p f Ω x t n) (hq : 5 ≤ p ^ f) (hΩ : InClass p f Ω)
    (hP1 : LocalOddCentral Ω {x}) {L L' : Subgroup G} (hL : L ∈ centralizingMembers Ω {x})
    (hL' : L' ∈ centralizingMembers Ω {x}) {R R' : Subgroup (modelUniv t n p f Fact.out).K}
    (hLR : locImg Ω x L = R.map e.φ) (hLR' : locImg Ω x L' = R'.map e.φ) {W : Subgroup _}
    (hW : LinearBlockStandardPair (GaloisField p f) W R R') :
    ∃ W' : Subgroup G, LinearBlockStandardPair (GaloisField p f) W' L L' := by
  have h1 := CFSG.ClassicalInvolution.RouteD.linearBlockStandardPair_map_central hW e.φ e.ker_le
  rw [← hLR, ← hLR'] at h1
  exact linearBlockStandardPair_of_locImg (by omega) (NonClassical.oddCoverSL3 hq) hΩ hP1 hL hL' h1

end Transfer

end CFSG.ClassicalInvolution.RouteD.TWE.B6
