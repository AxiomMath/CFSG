module

public import CFSG.HardMathSupport.Solomon.Coordinator.GFR2SporComp
public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.J3
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.Sporadic
public import CFSG.RankThree.PartTwo.KFacts.K426J3

public section

namespace CFSG.HardMathSupport.Solomon.Coordinator

open CFSG.Open CFSG.Sporadic.Schreier CFSG.Blueprint CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Timmesfeld.SporadicBalance CFSG.HardMathSupport.Timmesfeld.Coordinator
  CFSG.HardMathSupport.Timmesfeld.Tables.Census CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.PartTwo.KFacts.K426

private theorem no_perfect_1080_of_mulEquiv_J3
    {G : Type*} [Group G]
    (φ : G ≃* j3P) {s : G} (hs : orderOf s = 3) {K : Subgroup G}
    (hK : K ≤ Subgroup.centralizer ({s} : Set G)) [Group.IsPerfect ↥K]
    (hcard : Nat.card ↥K = 1080) : False := by
  let ι : G →* Equiv.Perm (Fin 6156) := j3P.subtype.comp (φ : G →* j3P)
  have hι : Function.Injective ι := j3P.subtype_injective.comp φ.injective
  have hts : orderOf (ι s) = 3 := by rw [orderOf_injective ι hι s]; exact hs
  have htmem : ι s ∈ j3P := (φ s).2
  obtain ⟨k, hkR, c, hc, e, he, hyk⟩ := j3t_fusion htmem hts
  have hc3 : c ^ 3 = 1 := by
    rcases hc with rfl | rfl
    · exact (j3tReps_spec (by norm_num : 0 < 2)).2
    · exact (j3tReps_spec (by norm_num : 1 < 2)).2
  set K₁ : Subgroup (Equiv.Perm (Fin 6156)) :=
    (K.map ι).map (MulAut.conj k⁻¹).toMonoidHom with hK₁
  have hperf₁ : Group.IsPerfect ↥K₁ := by
    have h1 : Group.IsPerfect ↥(K.map ι) := Group.IsPerfect.map ι
    exact Group.IsPerfect.map (MulAut.conj k⁻¹).toMonoidHom
  have hcard₁ : Nat.card ↥K₁ = 1080 := by
    rw [hK₁, Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective,
      Subgroup.card_map_of_injective hι, hcard]
  have hK₁C : K₁ ≤ Subgroup.centralizer {c} ⊓ j3P := by
    rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · have hqs : q * s = s * q := Subgroup.mem_centralizer_singleton_iff.1 (hK hq)
      have hce : ι q * ι s = ι s * ι q := by rw [← map_mul, ← map_mul, hqs]
      have hmem : (MulAut.conj k⁻¹) (ι q) ∈ Subgroup.centralizer {c ^ e} := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [hyk] at hce
        show k⁻¹ * ι q * k⁻¹⁻¹ * c ^ e = c ^ e * (k⁻¹ * ι q * k⁻¹⁻¹)
        calc k⁻¹ * ι q * k⁻¹⁻¹ * c ^ e = k⁻¹ * (ι q * (k * c ^ e * k⁻¹)) * k := by group
          _ = k⁻¹ * ((k * c ^ e * k⁻¹) * ι q) * k := by rw [hce]
          _ = c ^ e * (k⁻¹ * ι q * k⁻¹⁻¹) := by group
      rcases he with rfl | rfl
      · simpa using hmem
      · exact centralizer_pow_two_le hc3 hmem
    · show k⁻¹ * ι q * k⁻¹⁻¹ ∈ j3P
      exact j3P.mul_mem (j3P.mul_mem (j3P.inv_mem hkR) (φ q).2) (by simpa using hkR)
  rcases hc with rfl | rfl
  · have h1 : K₁ ≤ ⁅(Subgroup.centralizer {j3tXA} ⊓ j3P : Subgroup (Equiv.Perm (Fin 6156))),
        Subgroup.centralizer {j3tXA} ⊓ j3P⁆ := le_commutator_of_isPerfect hK₁C
    have h2 := Subgroup.card_le_of_le (h1.trans j3t_derived.1)
    rw [j3t_derived.2, hcard₁] at h2
    omega
  · have h2 := Subgroup.card_le_of_le hK₁C
    rw [hcard₁, ← j3t_caseB.1, j3t_caseB.2] at h2
    omega

private theorem perfect_inf_center_eq_bot_J3
    (hOut : SporadicOuterLeTwo)
    (hbr : SporadicBridges) {Y : Type} [Group Y] [Finite Y] (hq : CFSG.Open.IsQuasisimple Y)
    (hZ : Nat.card (Subgroup.center Y) = 3)
    (e : (Y ⧸ Subgroup.center Y) ≃* (TauCeti.CFSGIndex.sporadic .J3).Group)
    {x : MulAut Y} (hxo : orderOf x = 3) {P : Subgroup Y} (hP : P ≤ Lemma510Ns.fixSub x)
    [Group.IsPerfect ↥P] : P ⊓ Subgroup.center Y = ⊥ := by
  have hx3 : x ^ 3 = 1 := by rw [← hxo]; exact pow_orderOf_eq_one x
  have hperf : commutator Y = ⊤ := hq.1
  have hnab : ∃ a b : Y ⧸ Subgroup.center Y, a * b ≠ b * a :=
    CFSG.ComponentClassification.Helpers.quasisimple_central_quotient_nonabelian Y hq
  have hs := hq.2
  have hcen : Subgroup.center (Y ⧸ Subgroup.center Y) = ⊥ := center_eq_bot_of_isSimpleGroup hnab
  have hout : Nat.card (Outer (Y ⧸ Subgroup.center Y)) ≤ 2 := hOut _ hs hnab .J3 ⟨e⟩
  have hβ3 : (autCenterQuot Y x) ^ 3 = 1 := by rw [← map_pow, hx3, map_one]
  obtain ⟨s, hsβ, hs3⟩ := exists_conj_of_pow Nat.prime_three (by norm_num) hcen hout
    (autCenterQuot Y x) hβ3
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, map_one] at hsβ
    have h2 : x = 1 := autCenterQuot_injective_of_perfect hperf (by rw [← hsβ, map_one])
    rw [h2, orderOf_one] at hxo
    omega
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective s
  have hconj : autCenterQuot Y (MulAut.conj y) = MulAut.conj (y : Y ⧸ Subgroup.center Y) := by
    ext z
    obtain ⟨z, rfl⟩ := QuotientGroup.mk_surjective z
    rw [autCenterQuot_mk]
    simp [MulAut.conj_apply]
  have hxy : x = MulAut.conj y :=
    autCenterQuot_injective_of_perfect hperf (by rw [← hsβ, hconj])
  have hfix : Lemma510Ns.fixSub x = Subgroup.centralizer ({y} : Set Y) := by
    rw [hxy]
    ext a
    rw [Subgroup.mem_centralizer_singleton_iff]
    show (MulAut.conj y) a = a ↔ _
    rw [MulAut.conj_apply]
    constructor
    · intro h
      calc a * y = (y * a * y⁻¹) * y := by rw [h]
        _ = y * a := by group
    · intro h
      calc y * a * y⁻¹ = (a * y) * y⁻¹ := by rw [h]
        _ = a := by group
  have hy : y ∉ Subgroup.center Y := fun h => hs1 ((QuotientGroup.eq_one_iff y).2 h)
  have hy3 : y ^ 3 ∈ Subgroup.center Y := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hs3
  have hq' : CFSG.IsQuasisimple Y := ⟨⟨hq.1⟩, hq.2, hnab⟩
  exact j3CoverCentralizer Y hq' hZ ⟨e.trans (hbr .J3).some.symm⟩ y hy hy3 P (hfix ▸ hP) ‹_›

theorem sporNoPumpup_J3
    (hSpM : SporadicMultipliers)
    (hOG : UniquenessMaximal.InputONGroup) (hOut : SporadicOuterLeTwo) (hbr : SporadicBridges) :
    SporNoPumpup .J3 := by
  refine sporNoPumpup_of_components_cover hSpM hOG hOut ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (hbr .J3).some.toEquiv]
    show Nat.card NativeSporadic.J3 = sporOrd .J3
    rw [CFSG.Sporadic.J3.card_J3]
    norm_num [sporOrd, orderJ3]
  · haveI : Finite (TauCeti.CFSGIndex.sporadic .J3).Group :=
      Finite.of_equiv NativeSporadic.J3 (hbr .J3).some.toEquiv
    exact oPrimeCoreTrivialAt_J3 _ ⟨MulEquiv.refl _⟩
  · intro s hs K hK h
    rcases h with ⟨hperf, hZ, ⟨f⟩⟩ | ⟨hM, _⟩
    · haveI : Group.IsPerfect ↥K := ⟨hperf⟩
      exact no_perfect_1080_of_mulEquiv_J3 ((hbr .J3).some.symm.trans j3PermEquiv) hs hK.1
        (gfr2_card_isHatSix ⟨hperf, hZ, ⟨f⟩⟩)
    · exact absurd hM (by decide)
  · intro Y _ _ hq _ hZ ⟨e⟩ x hxo J₁ hJ₁ _
    haveI : Group.IsPerfect ↥J₁ :=
      Subgroup.isPerfect_iff.2 (CFSG.LocalAnalysis.GLTheoremB.glaPComponent_perfect hJ₁)
    exact perfect_inf_center_eq_bot_J3 hOut hbr hq hZ e hxo hJ₁.1

end CFSG.HardMathSupport.Solomon.Coordinator
