module

public import CFSG.ClassicalInvolution.Asc77.AscIHThm2
public import CFSG.ClassicalInvolution.Balance.Q27ThreeD4Model
public import CFSG.ClassicalInvolution.Asc77.AscSixBasic

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ComponentClassification
open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)
open scoped MatrixGroups

section SL2

variable {F : Type} [Field F] [Finite F] {G : Type*} [Group G] [Finite G]

theorem oddCore_range_eq_bot (h4 : 4 ≤ Nat.card F) (ψ : SL(2, F) →* G)
    (hz : 2 ∣ Nat.card ψ.range) : classicalInvolutionOddCore ↥ψ.range = ⊥ := by
  set L : Subgroup G := ψ.range with hL
  let ψ' : SL(2, F) →* ↥L := ψ.rangeRestrict
  have hsurj : Function.Surjective ψ' := ψ.rangeRestrict_surjective
  set M : Subgroup ↥L := classicalInvolutionOddCore ↥L with hM
  have hMn : M.Normal := classicalInvolutionOddCore_normal ↥L
  have hModd : Odd (Nat.card M) := OddCore.odd_card ↥L
  have hcomap : (M.comap ψ').Normal := hMn.comap ψ'
  have hmap : (M.comap ψ').map ψ' = M := Subgroup.map_comap_eq_self_of_surjective hsurj M
  rcases sl2_normal_cases h4 (M.comap ψ') hcomap with h | h | h
  · rw [← hmap, h, Subgroup.map_bot]
  · have hc2 : Nat.card ↥(Subgroup.center SL(2, F)) ≤ 2 :=
      natCard_subgroup_le_two_of_subset (a := 1) (b := -1) fun x hx =>
        (mem_center_sl2_iff x).mp hx
    have hd : Nat.card M ∣ Nat.card ↥(Subgroup.center SL(2, F)) := by
      have := Subgroup.card_map_dvd (M.comap ψ') ψ'
      rwa [hmap, h] at this
    have h1 : Nat.card M ≤ 2 := (Nat.le_of_dvd Nat.card_pos hd).trans hc2
    obtain ⟨m, hm⟩ := hModd
    exact Subgroup.eq_bot_of_card_eq M (by omega)
  · exfalso
    have hMtop : M = ⊤ := by
      rw [← hmap, h, Subgroup.map_top]
      exact MonoidHom.range_eq_top.mpr hsurj
    have hcard : Nat.card ↥L = Nat.card M := by
      rw [hMtop, Subgroup.card_top]
    obtain ⟨c, hc⟩ := hz
    obtain ⟨m, hm⟩ := hModd
    omega

end SL2

section Models

variable {p : ℕ} [Fact p.Prime]

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LieType.CurtisTits in
theorem fundamental_sl2_range_g2Datum {e : ℕ}
    {R : Subgroup ↥(adjointGroup .G2 (GaloisField p e))}
    (hR : R ∈ fundamentalSubgroups .G2 (g2Datum (GaloisField p e))) :
    ∃ ι : SL(2, GaloisField p e) →* ↥(adjointGroup .G2 (GaloisField p e)), ι.range = R := by
  obtain ⟨g, γ, hγ, rfl⟩ := hR
  have hct := g2_isCTGroupDatum (GaloisField p e)
  have hroot : IsRoot .G2 γ := by
    have h : γ ∈ (g2Datum (GaloisField p e)).roots := by
      rcases hγ with h | ⟨-, h⟩ | ⟨h', -⟩
      · exact h.1
      · exact h
      · exact absurd h' (by decide)
    exact mem_adjDatum_roots.mp h
  obtain ⟨w, j, hw⟩ := isRoot_iff_exists_smul_single.1 hroot
  obtain ⟨h, hh⟩ := ModelFacts.exists_map_conj_rankOne hct w
  have hb : (Pi.single j 1 : Fin (Tag.rank .G2) → ℤ) ∈ (g2Datum (GaloisField p e)).roots :=
    mem_adjDatum_roots.mpr (isRoot_single .G2 j)
  have h2 : (g2Datum (GaloisField p e)).rootGroup (w • Pi.single j 1) ⊔
      (g2Datum (GaloisField p e)).rootGroup (-(w • Pi.single j 1)) =
      (rankOne (rootGroup (rootOperatorFamily .G2) (GaloisField p e)) j).map
        (MulAut.conj h).toMonoidHom := (hh _ hb).symm
  obtain ⟨φ⟩ := ModelFacts.g2_rankOne_equiv (K := GaloisField p e) j
  have hrange : ((rankOne (rootGroup (rootOperatorFamily .G2) (GaloisField p e)) j).subtype.comp
      φ.symm.toMonoidHom).range =
        rankOne (rootGroup (rootOperatorFamily .G2) (GaloisField p e)) j := by
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (φ.symm s).2
    · intro hx
      exact ⟨φ ⟨x, hx⟩, by simp⟩
  refine ⟨((MulAut.conj (g * h)).toMonoidHom).comp
    ((rankOne (rootGroup (rootOperatorFamily .G2) (GaloisField p e)) j).subtype.comp
      φ.symm.toMonoidHom), ?_⟩
  have hcomp : (MulAut.conj g).toMonoidHom.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj (g * h)).toMonoidHom := MonoidHom.ext fun y => by simp [mul_assoc]
  subst hw
  rw [MonoidHom.range_comp, hrange]
  unfold conjSub
  rw [h2, Subgroup.map_map _ (MulAut.conj g).toMonoidHom (MulAut.conj h).toMonoidHom, hcomp]

theorem fundamental_sl2_range_G2 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (ht : t = .G2) {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    ∃ ι : SL(2, GaloisField p e) →* (modelUniv t n p e Fact.out).K, ι.range = R := by
  subst ht
  exact fundamental_sl2_range_g2Datum hR

theorem fundamental_sl2_range_trialityD4 {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n e : ℕ}
    (ht : t = .trialityD4) (hadm : StatedLieAdmissible t n p e)
    {R : Subgroup (modelUniv t n p e Fact.out).K}
    (hR : R ∈ fundamentalSubgroups t (modelUniv t n p e Fact.out).D) :
    (∃ ι : SL(2, Models.TwistedPairs.fixedField (iterateFrobenius (GaloisField p (3 * e)) p e)) →*
        (modelUniv t n p e Fact.out).K, ι.range = R) ∨
      ∃ ι : SL(2, GaloisField p (3 * e)) →* (modelUniv t n p e Fact.out).K, ι.range = R := by
  subst ht
  exact Balance.Q27.fundamental_trialityD4_sl2_range hadm R hR

end Models

namespace OmegaLie

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] {Ω : Set (Subgroup G)}
  (D : OmegaLie p f Ω)

theorem exists_sl2_range (hp : p ≠ 2) (i : Fin D.card) {R : Subgroup (D.model i).K}
    (hR : R ∈ fundamentalSubgroups (D.tag i) (D.model i).D) :
    ∃ (F : Type) (_ : Field F), Finite F ∧ ∃ ι : SL(2, F) →* (D.model i).K, ι.range = R := by
  by_cases hG2 : D.tag i = .G2
  · obtain ⟨ι, hι⟩ := fundamental_sl2_range_G2 hG2 hR
    exact ⟨GaloisField p (D.exp i), inferInstance, inferInstance, ι, hι⟩
  by_cases hD4 : D.tag i = .trialityD4
  · rcases fundamental_sl2_range_trialityD4 hD4 (D.admissible i) hR with ⟨ι, hι⟩ | ⟨ι, hι⟩
    · exact ⟨_, inferInstance, inferInstance, ι, hι⟩
    · exact ⟨_, inferInstance, inferInstance, ι, hι⟩
  · obtain ⟨e⟩ := ModelFacts.nonempty_equiv_sl2_of_mem_fundamentalSubgroups (p := p) hp
      (isFundTag_modelFacts (D.isFundTag i)) (D.admissible i) hG2 hD4 hR
    refine ⟨GaloisField p (D.exp i), inferInstance, inferInstance,
      R.subtype.comp e.symm.toMonoidHom, ?_⟩
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact (e.symm s).2
    · intro hx
      exact ⟨e ⟨x, hx⟩, by simp⟩

theorem exactMembers [Finite G] (hp : p ≠ 2) (hq : 5 ≤ p ^ f) (hΩ : HypOmegaMod p f Ω)
    (D : OmegaLie p f Ω) : ExactMembers Ω := by
  intro L hL
  obtain ⟨i, R, hR, hLR⟩ := D.fundamental L hL
  obtain ⟨z, hz⟩ := hΩ.classical L hL
  obtain ⟨F, _, hFin, ι, hι⟩ := D.exists_sl2_range hp i hR
  have hLψ : L = ((D.hom i).comp ι).range := by
    rw [MonoidHom.range_comp, hι, hLR]
  have hzL : 2 ∣ Nat.card L := by
    have := Subgroup.orderOf_dvd_natCard L hz.mem
    rwa [hz.orderOf_eq_two] at this
  by_cases h4 : 4 ≤ Nat.card F
  · subst hLψ
    exact oddCore_range_eq_bot h4 _ hzL
  · exfalso
    obtain ⟨e⟩ := hz.nonempty_equiv
    have hf : f ≠ 0 := by
      rintro rfl
      simp at hq
    have hqcard : Nat.card (GaloisField p f) = p ^ f := GaloisField.card p f hf
    have h1 : Nat.card SL(2, GaloisField p f) ∣ Nat.card L := by
      have := Subgroup.card_quotient_dvd_card (classicalInvolutionOddCore ↥L)
      rwa [Nat.card_congr e.toEquiv] at this
    have h2 : Nat.card L ≤ Nat.card SL(2, F) := by
      rw [hLψ]
      have : Function.Surjective ((D.hom i).comp ι).rangeRestrict :=
        MonoidHom.rangeRestrict_surjective _
      exact Nat.card_le_card_of_surjective _ this
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two] at h1 h2
    have hFpos : 0 < Nat.card F := Nat.card_pos
    have hF3 : Nat.card F ≤ 3 := by omega
    rw [hqcard] at h1
    have h3 : p ^ f * ((p ^ f) ^ 2 - 1) ≤ Nat.card L := Nat.le_of_dvd Nat.card_pos h1
    have h4' : Nat.card F * (Nat.card F ^ 2 - 1) ≤ 24 := by
      interval_cases (Nat.card F) <;> norm_num
    have h5 : 5 * 24 ≤ p ^ f * ((p ^ f) ^ 2 - 1) := by
      refine Nat.mul_le_mul hq ?_
      have : 25 ≤ (p ^ f) ^ 2 := by nlinarith
      omega
    omega

end OmegaLie

end CFSG.ClassicalInvolution.Asc77
