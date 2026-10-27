module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.Omega8Step3
public import CFSG.RankThree.PartTwo.Census.Carrier.SpinDOdd

public section

namespace CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

open CFSG.Assembly.LowTwoRank CFSG.AGLEmbedding.ParabHub CFSG.LieType.Universal
  CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg CFSG.LieType.CurtisTits
  CFSG.LieType.RootSystem CFSG.QuasithinUnique

theorem sylow_normalizer_inf_le {X : Type} [Group X] [Finite X] {Lb S : Subgroup X}
    {K : Type} [Group K] [Finite K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* ↥Lb} {M : ℕ}
    (h : BorelQuotient D n H π M) (hB : borel D H = posUnipotent D)
    (hS : IsSylowTwoOf S Lb) : Lb ⊓ Subgroup.normalizer (S : Set X) ≤ S := by
  obtain ⟨hSL, hP, hidx⟩ := hS
  have hP' : IsPGroup 2 (S.subgroupOf Lb) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hSL).symm
  let T : Sylow 2 ↥Lb := hP'.toSylow hidx
  have hTS : (T : Subgroup ↥Lb) = S.subgroupOf Lb := IsPGroup.toSylow_coe hP' hidx
  obtain ⟨π', hπ', hker, hT⟩ := h.exists_conj_eq T
  have hQ : BorelQuotient D n H π' M :=
    { ct := h.ct, extras := h.extras, pGroup := h.pGroup, surj := hπ', odd := h.odd
      torus_pow := h.torus_pow
      ker_central := fun z hz => h.ker_central z (hker ▸ hz)
      ker_pow := fun z hz => h.ker_pow z (hker ▸ hz) }
  have hN : Subgroup.normalizer (((posUnipotent D).map π' : Subgroup ↥Lb) : Set ↥Lb) =
      (posUnipotent D).map π' := by
    rw [hQ.normalizer_map_posUnipotent, hB]
  intro y hy
  obtain ⟨hyLb, hyN⟩ := Subgroup.mem_inf.1 hy
  have hyY : (⟨y, hyLb⟩ : ↥Lb) ∈
      Subgroup.normalizer (((S.subgroupOf Lb : Subgroup ↥Lb)) : Set ↥Lb) := by
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hg := Subgroup.mem_normalizer_iff.1 hyN (g : X)
    simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul,
      Subgroup.coe_inv] using hg
  have hyP : (⟨y, hyLb⟩ : ↥Lb) ∈ (posUnipotent D).map π' := by
    rw [← hN, ← hT, hTS]
    exact hyY
  rw [← hT, hTS] at hyP
  exact Subgroup.mem_subgroupOf.1 hyP

theorem kFactOmega8Borel_proved : KFactOmega8Borel := by
  intro X _ _ Lb S hLb hS
  obtain ⟨d, ⟨q, hq, hd⟩, ⟨φ⟩⟩ := hLb
  obtain ⟨x, hv⟩ := d
  obtain rfl : x = TauCeti.LieTypeIndex.D 4 q := hd
  have hp : q.p = 2 := by
    have h1 : q.p ∣ q.p ^ q.exponent := dvd_pow_self q.p q.exponent_pos.ne'
    rw [← TauCeti.PrimePower.card_def, hq] at h1
    exact (Nat.prime_dvd_prime_iff_eq q.prime_p Nat.prime_two).1 h1
  have he : q.exponent = 1 := by
    have h2 : 2 ^ q.exponent = 2 ^ 1 := by
      have h3 := hq
      rw [TauCeti.PrimePower.card_def, hp] at h3
      rw [h3]
      norm_num
    exact Nat.pow_right_injective (le_refl 2) h2
  have : Finite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) :=
    CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField _
  have hcard : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) = 2 ^ 1 := by
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow]
    simp [TauCeti.ValidLieTypeIndex.characteristic, TauCeti.ValidLieTypeIndex.fieldExponent, hp,
      he]
  have : CharP ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) 2 := by
    have := Fintype.ofFinite ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)
    exact charP_of_card_eq_prime_pow (f := 1) (by rw [← Nat.card_eq_fintype_card]; exact hcard)
  have hM : Nat.card ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩) - 1 = 1 := by
    rw [hcard]
    norm_num
  let e := φ.trans
    (CFSG.RankThree.PartTwo.Census.Carrier.SpinD.typeDGroupEquivStatedProj_of_valid 4 q hv)
  have : NeZero (4 : ℕ) := ⟨by norm_num⟩
  have : Finite (spinGroup (quadPlus 4 ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩))) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := 4)
      (K := ↥(TauCeti.ValidLieTypeIndex.fixedField ⟨.D 4 q, hv⟩)))
  refine sylow_normalizer_inf_le (borelQuotient_spinPlus (by norm_num : 3 ≤ 4) e) ?_ hS
  unfold CFSG.LieType.Steinberg.borel
  apply sup_eq_right.2
  refine iSup_le fun i g hg => ?_
  have := torusD_pow_eq_one (by norm_num : 3 ≤ 4) i hg
  rw [hM, pow_one] at this
  rw [this]
  exact one_mem _

end CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs

end
