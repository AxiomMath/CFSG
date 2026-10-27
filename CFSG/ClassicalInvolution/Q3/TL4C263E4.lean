module

public import CFSG.ClassicalInvolution.Q3.TL4C264OmDefs
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE3
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4All
public import CFSG.ClassicalInvolution.Q3.TL4MFMuZ2Gold
public import CFSG.ClassicalInvolution.Q3.TL4MF164Fr

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Disconnected (DConnected DEdgeless)
open CFSG.Blueprint

section U3

open Matrix CFSG.ClassicalInvolution.Q3.TA3 CFSG.ClassicalInvolution.Q3.TA3.Q5GL2

theorem false_of_u3_one_mod_four {X : Type} [Group X] [Finite X] {R : Subgroup X}
    {S : Sylow 2 R} {z : X} (hD : TightDatum R S z) {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h41 : p ^ f % 4 = 1) (hL : LieModel X .PSU 3 p f) : False := by
  obtain ⟨-, hf, K, _, _, hK, ⟨e₀⟩⟩ := CFSG.GH74.Generic.lieModel_psu_data hL
  have h : LocalAnalysis.ComponentInitial.UnitaryFieldData p f K :=
    ⟨hp, hf, by rw [hK, ← pow_mul, mul_comm]⟩
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := h.charP
  have hodd : Odd (p ^ f) := (hp.odd_of_ne_two hp2).pow
  have h5 : 5 ≤ p ^ f := by
    have hp3 : 3 ≤ p := by have := hp.two_le; omega
    have hle : p ≤ p ^ f := Nat.le_self_pow (by omega) p
    omega
  have hq := LieType.Steinberg.card_fixedSubfield h.card_eq_sq
  let e : ↥(⊤ : Subgroup X) ≃* Assembly.LowTwoRank.StatedProj
      (Assembly.LowTwoRank.StatedSU 3 (p ^ f) K) := Subgroup.topEquiv.trans e₀
  obtain ⟨π, hrange, hk, -⟩ := Q5U3.exists_frame h hp2 e (Subgroup.mem_top z) hD.order
  obtain ⟨eJ⟩ := Q5U3.nonempty_slPart_equiv h
  exact MF164.false_of_gl2_frame hD le_top hrange hk (Q5U3.slCentScalar_GU2 h)
    (by rw [hq]; exact hodd) (by rw [hq]; omega) eJ

end U3

@[expose] def Out263 (X : Type) [Group X] : Prop :=
  LieModel X .PSL 3 3 1 ∨ NativeSporadic.IsSporadic X .M11 ∨
    (IsSimpleGroup ↥(genFittingFStar X) ∧ (genFittingFStar X).index ≤ 2 ∧
      ∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ Even f ∧ LieModel (FStarQuot X) .PSL 2 p f)

section Out

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem out263_of_e3 (hT : MuZ2Table) (hE3 : SecIdE3MuZ2) (hm : EdgelessMember3 R S t)
    (hmu : MuZ2Member R) (hO2 : ¬ TightInO2 t)
    (hx : (¬ TightActs3 R t ∧ (Thm6Exit Y ∨ TightTwisted Y t)) ∨
      Nonempty (Y ⧸ Subgroup.center Y ≃* NativeSporadic.Carrier .M12)) : Out263 Y := by
  obtain ⟨hFs, hi, hX⟩ := hE3 Y R S t hm hmu hO2 hx
  obtain ⟨hTL3, hTU3, -, -, hTM12⟩ := hT Y R S t hm hmu hFs (index_dvd_six_of_le_two hi)
  rcases hX with ⟨p, f, hp, hp2, ⟨hf, hl⟩ | hl | hl⟩ | hm12
  · exact Or.inr (Or.inr ⟨hFs, hi, p, f, hp, hp2, hf, hl⟩)
  · obtain ⟨-, hl'⟩ := hTL3 p f hl
    by_cases h3 : p ^ f = 3
    · obtain ⟨rfl, rfl⟩ := Nat.prime_three.pow_eq_iff.mp h3
      exact Or.inl hl'
    · exact (MF164.false_of_l3_ne_three hm.datum hp hp2 hl' h3).elim
  · obtain ⟨-, hl', h41⟩ := hTU3 p f hl
    exact (false_of_u3_one_mod_four hm.datum hp hp2 h41 hl').elim
  · exact absurd hm12 hTM12


theorem out263_of_lie (hT : MuZ2Table) (hm : EdgelessMember3 R S t) (hmu : MuZ2Member R)
    (hY : LieModel Y .PSL 3 3 1 ∨ LieModel Y .PSU 3 3 1 ∨ LieModel Y .G2 0 3 1 ∨
      LieModel Y .trialityD4 0 3 1 ∨ NativeSporadic.IsSporadic Y .M11) : Out263 Y := by
  obtain ⟨eQ⟩ : Nonempty (↥(S : Subgroup R) ≃* QuaternionGroup 2) := hm.cls.1
  have hnab := exists_ne_comm_of_quat eQ
  rcases hY with h | h | h | h | h
  · exact Or.inl h
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    have h4 := ((hT Y R S t hm hmu hFs (hi ▸ one_dvd 6)).2.1 3 1 hF).2.2
    norm_num at h4
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    exact absurd hF ((hT Y R S t hm hmu hFs (hi ▸ one_dvd 6)).2.2.1 3 1)
  · obtain ⟨hFs, hi, hF⟩ := fstar_of_lieModel hnab h
    exact absurd hF ((hT Y R S t hm hmu hFs (hi ▸ one_dvd 6)).2.2.2.1 3 1)
  · exact Or.inr (Or.inl h)

end Out

section Sec


theorem out263_of_section_of_facts {n : ℕ} (hT : MuZ2Table) (hE3 : SecIdE3MuZ2)
    (hE4 : SecIdE4Edge) (hP : TightBelowRPlus 3 n) (hA : CIT3Below n) (h4 : Thm4RBelow 3 n)
    {X : Type} [Group X] [Finite X] (hn : Nat.card X < n) {Φ : Set (Subgroup X)}
    (h : TypeRFam 3 Φ) (hO : classicalInvolutionOddCore X = ⊥) (hgen : omegaGen Φ = ⊤)
    (hE : DEdgeless Φ) (htop : (⊤ : Subgroup X) ∉ Φ) {A : Subgroup X} (hAΦ : A ∈ Φ)
    (hmu' : ∃ W' ∈ WSet Φ, MuIsoZ2 Φ W') : Out263 X := by
  have htr := omegaTransitive_of_dEdgeless h4 h hO hn hAΦ hE
  obtain ⟨S, z, hd, hc, hcl⟩ := exists_datum_of_omegaTransitive h hO hgen hAΦ htr
  have hcore : tightCore A = A := h.closure_twoElts hAΦ
  have hE' : TightEdgeless A := by
    show Disconnected.DEdgeless (CoreAssembly.conjClass (tightCore A))
    rw [hcl]
    exact hE
  have hm : EdgelessMember3 A S z := ⟨hd, hc, hE'⟩
  have hmu : MuZ2Member A := by
    obtain ⟨W', hW', hZ⟩ := hmu'
    have hP' : Q3CL.PartIHypG Φ := hcl ▸ hd.partIHypG
    show ∀ W ∈ WSet (CoreAssembly.conjClass (tightCore A)),
      MuIsoZ2 (CoreAssembly.conjClass (tightCore A)) W
    rw [hcl]
    exact muIsoZ2_forall_of_exists hP' hE hW' hZ ⟨A, hAΦ⟩
  by_cases hO2 : TightInO2 z
  · exfalso
    have hW : ∃ W ∈ WSet (CoreAssembly.conjClass (tightCore A)),
        MuIsoZ2 (CoreAssembly.conjClass (tightCore A)) W := by
      rw [hcl]
      exact hmu'
    have hAt := secIdE2EdgelessBelow_of hP.thmD.d2 X hn A S z hd hc hO2 hE' hW
    rw [hcore] at hAt
    exact htop (hAt ▸ hAΦ)
  rcases secIdentDatum3_of hP hA X hn A S z hd hc with h2 | ⟨-, h3, hx⟩ | ⟨-, hx⟩ |
      ⟨hZ, hmod⟩ | hl
  · exact absurd h2 hO2
  · exact out263_of_e3 hT hE3 hm hmu hO2 (Or.inl ⟨h3, hx⟩)
  · exact out263_of_e3 hT hE3 hm hmu hO2 (Or.inr hx)
  · exact absurd hE' (hE4 X A S z hd hc hO2 hZ hmod)
  · exact out263_of_lie hT hm hmu (secIdLieEdgeless3Below_of
      ((Uniform.citBelowT_three_iff (by norm_num) n).mpr hA) X hn A S z hd hc hl hE')

theorem tightC263E4_of_facts {n : ℕ} (h4 : Thm4RBelow 3 n) (hLC : TightLambdaCommR 3 n)
    (hT : MuZ2Table) (hE3 : SecIdE3MuZ2) (hE4 : SecIdE4Edge) : TightC263E4 n := by
  intro hP Y _ _ Rd Sd z J S R T W t hs hKX hE
  have hX : omegaNbrGen (CoreAssembly.conjClass (tightCore Rd)) (tightCore Rd) ≠ ⊤ := by
    intro htop
    apply hKX
    rw [htop]
    exact sup_top_eq _
  have hn := hs.natCard_xQuot_lt_of_ne_top hX
  have hKX' := hs.not_le_omegaNbrGen_of_ne_top (tightSecNbrGenR_of_comm hLC) hX
  have h := TightLargeHypR.typeRFam hs.large
  exact out263_of_section_of_facts hT hE3 hE4 hP hs.large.below h4 hn h.xFam
    xQuot_oddCore_eq_bot omegaGen_xFam (hs.dEdgeless_xFam_E4_of_not_le hKX' hE)
    hs.top_not_mem_xFam ⟨_, ⟨J, hs.hJ.1, le_omegaNbrGen hs.hJ, rfl⟩, rfl⟩
    (hs.exists_muIsoZ2_xFam_E4_of_not_le hKX' hE)

theorem tightC263E4_of {n : ℕ} (h4 : Thm4RBelow 3 n) (hLC : TightLambdaCommR 3 n) :
    TightC263E4 n :=
  tightC263E4_of_facts h4 hLC muZ2Table_proved
    (secIdE3MuZ2_of CFSG.Goldschmidt75.goldschmidtB3 muZ2Table_proved) secIdE4Edge_proved

end Sec

end CFSG.ClassicalInvolution.Q3.TL4
