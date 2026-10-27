module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusStdFive
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmMinusStdFour
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmWit
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeOmCent
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T171SmallTypeIso
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CBridge
public import CFSG.ClassicalGroups.Orthogonal.RingEquivTransport
public import CFSG.LargeExtraspecial.O62Basic

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.GLTheoremA.T171S

open QuadraticMap Module CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.LocalAnalysis.GLTheoremA.KD264Lie.OmC CFSG.Open
  CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine
  CFSG.LargeExtraspecial.O62
open scoped CFSG.LocalAnalysis.GLTheoremA.Y10F.HypBlocks

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [FiniteDimensional (ZMod 2) V]
  {Q : QuadraticForm (ZMod 2) V}

theorem noSmallModel_minus_five (hQ : (polarBilin Q).Nondegenerate)
    (hdim : finrank (ZMod 2) V = 2 * 5)
    (hminus : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q) :
    NoSmallModel ↥(orthDerived Q) := by
  classical
  intro Bb h
  haveI : Finite V := Module.finite_of_finite (ZMod 2)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := CFSG.LargeExtraspecial.O62.finite_linearEquiv
  haveI : Fintype ↥(orthImage Bb) := Fintype.ofFinite _
  haveI : DecidableEq (Hyperplane (orthImage Bb) 3) := Classical.decEq _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAe : IsElemAbelian 3 (orthImage Bb) := isElemAbelian_orthImage (Ã := Bb) h.elem
  have hAcard : Nat.card ↥(orthImage Bb) = 3 ^ 4 := by
    change Nat.card ↥(Bb.map (orthDerived Q).subtype) = 3 ^ 4
    rw [Subgroup.card_map_of_injective (orthDerived Q).subtype_injective,
      card_eq_three_pow_four_of_smallModel_minus_five hQ hdim hminus h]
  have hB : ∀ a : ↥(orthImage Bb), ∀ u v : V,
      polarBilin Q ((a : V ≃ₗ[ZMod 2] V) u) ((a : V ≃ₗ[ZMod 2] V) v) = polarBilin Q u v :=
    fun a => polar_orthImage (Ã := Bb) a
  have hfaith : ∀ a : ↥(orthImage Bb), (∀ v : V, (a : V ≃ₗ[ZMod 2] V) v = v) → a = 1 := by
    rintro ⟨a, ha⟩ hfix
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 ha
    have hb1 : b = 1 := Subtype.ext (LinearEquiv.ext fun v => by simpa using hfix v)
    exact Subtype.ext (by simpa using congrArg Subtype.val hb1)
  have hle5 : (blockSet (orthImage Bb)).card ≤ 5 :=
    card_blockSet_le_five hQ hAe hAcard hdim hB
  have hge4 : 4 ≤ (blockSet (orthImage Bb)).card :=
    four_le_card_blockSet hQ hAe hAcard hdim hfaith
  rcases (show (blockSet (orthImage Bb)).card = 4 ∨
      (blockSet (orthImage Bb)).card = 5 by omega) with h4 | h5
  · exact four_blocks_impossible hQ hdim hminus h h4
  · exact five_blocks_impossible hQ hdim hAe h5 h.twoLocal

theorem nonempty_orthDerived_equiv_of_ringEquiv {F V : Type} [Field F] [Finite F]
    [AddCommGroup V] [Module F V] [Module (ZMod 2) V] (e : ZMod 2 ≃+* F)
    (hsmul : ∀ (c : ZMod 2) (v : V), c • v = e c • v) (Q : QuadraticForm F V) :
    Nonempty (↥(orthDerived (formOfRingEquiv e hsmul Q)) ≃* ↥(orthDerived Q)) := by
  have hφinj : Function.Injective (restrictScalarsHom e hsmul) := restrictScalarsHom_injective
  have hOmap : (TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q)).map
      (restrictScalarsHom e hsmul) = TauCeti.QuadraticMap.orthogonalGroup Q := by
    apply le_antisymm
    · rintro _ ⟨g, hg, rfl⟩
      exact mem_orthogonalGroup_restrictScalarsHom hg
    · intro g hg
      let g' : V ≃ₗ[ZMod 2] V :=
        { toFun := g
          map_add' := g.map_add
          map_smul' := fun c v => by
            show g (c • v) = c • g v
            rw [hsmul, hsmul]
            exact g.map_smul (e c) v
          invFun := g.symm
          left_inv := g.left_inv
          right_inv := g.right_inv }
      have hg' : g' ∈ TauCeti.QuadraticMap.orthogonalGroup (formOfRingEquiv e hsmul Q) := by
        rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff] at hg ⊢
        intro x
        rw [formOfRingEquiv_apply, formOfRingEquiv_apply]
        change e.symm (Q (g x)) = e.symm (Q x)
        rw [hg x]
      exact ⟨g', hg', LinearEquiv.ext fun v => rfl⟩
  have hcomm : (orthDerived (formOfRingEquiv e hsmul Q)).map (restrictScalarsHom e hsmul) =
      orthDerived Q := by
    rw [orthDerived, orthDerived, Subgroup.map_commutator, hOmap]
  exact ⟨(orthDerived (formOfRingEquiv e hsmul Q)).equivMapOfInjective
    (restrictScalarsHom e hsmul) hφinj |>.trans (MulEquiv.subgroupCongr hcomm)⟩

theorem famOmM_holds : FamOmM := by
  intro n q hv hq hn
  obtain ⟨F, hFfield, hFfin, hFchar, V, hVadd, hVmod, hVfd, Q, hFcard, hQ, hdim, hminus, hθ⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.S172C.exists_omegaMinus_model (n := n) (k := 1) hn (by norm_num)
  letI := hFfield
  letI := hFfin
  letI := hFchar
  letI := hVadd
  letI := hVmod
  letI := hVfd
  have hcat : CFSG.Yardstones.Md0ec50421ce4.catalogIs
      (TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩).Group
      (CFSG.LocalAnalysis.GLTheoremA.isOmMA n 2) :=
    ⟨TauCeti.CFSGIndex.lie ⟨.twistedD n q, hv⟩, Or.inl ⟨rfl, hq⟩, ⟨MulEquiv.refl _⟩⟩
  obtain ⟨eθ⟩ := hθ _ hcat
  have hNo : NoSmallModel ↥(orthDerived Q) := by
    haveI : Fintype F := Fintype.ofFinite F
    haveI : Finite V := Module.finite_of_finite F
    have hF2 : Nat.card F = 2 := by simpa using hFcard
    have hF2' : Fintype.card F = 2 := by rwa [← Nat.card_eq_fintype_card]
    let e : ZMod 2 ≃+* F := ZMod.ringEquivOfPrime F Nat.prime_two hF2'
    letI : Module (ZMod 2) V := Module.compHom V (e : ZMod 2 →+* F)
    have hsmul : ∀ (c : ZMod 2) (v : V), c • v = e c • v := fun _ _ => rfl
    let Q' : QuadraticForm (ZMod 2) V := formOfRingEquiv e hsmul Q
    haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
    have hQ' : (polarBilin Q').Nondegenerate := nondegenerate_formOfRingEquiv hQ
    have hdim' : finrank (ZMod 2) V = 2 * n := by
      have h1 : Nat.card V = Nat.card F ^ finrank F V := Module.natCard_eq_pow_finrank
      have h2 : Nat.card V = Nat.card (ZMod 2) ^ finrank (ZMod 2) V :=
        Module.natCard_eq_pow_finrank
      have hFc : Nat.card F = Nat.card (ZMod 2) := by
        rw [hF2, Nat.card_zmod]
      rw [hdim, hFc] at h1
      have h2' : Nat.card (ZMod 2) ^ finrank (ZMod 2) V = Nat.card (ZMod 2) ^ (2 * n) :=
        h2.symm.trans h1
      exact Nat.pow_right_injective (by rw [Nat.card_zmod]) h2'
    have hminus' : ¬ CFSG.GroupTheory.WeirSylow.IsPlusType Q' := by
      rintro ⟨W, hWdim, hW0⟩
      apply hminus
      let W' : Submodule F V :=
        { carrier := W
          add_mem' := W.add_mem
          zero_mem' := W.zero_mem
          smul_mem' := fun c v hv => by
            have h := W.smul_mem (e.symm c) hv
            rwa [hsmul, RingEquiv.apply_symm_apply] at h }
      haveI : Finite ↥W' := Subtype.finite
      haveI : Finite ↥W := Subtype.finite
      haveI : Module.Finite F ↥W' := Module.Finite.of_finite
      haveI : Module.Finite (ZMod 2) ↥W := Module.Finite.of_finite
      have hdimW : finrank F W' = finrank (ZMod 2) W := by
        have h1 : Nat.card ↥W' = Nat.card F ^ finrank F W' := Module.natCard_eq_pow_finrank
        have h2 : Nat.card ↥W = Nat.card (ZMod 2) ^ finrank (ZMod 2) W :=
          Module.natCard_eq_pow_finrank
        have hc : Nat.card ↥W' = Nat.card ↥W :=
          Nat.card_congr (Equiv.subtypeEquivRight fun _ => Iff.rfl)
        have hFc : Nat.card F = Nat.card (ZMod 2) := by rw [hF2, Nat.card_zmod]
        rw [hc, hFc] at h1
        exact Nat.pow_right_injective (by rw [Nat.card_zmod]) (h1.symm.trans h2)
      refine ⟨W', ?_, fun x hx => ?_⟩
      · rw [hdimW, hWdim, hdim', hdim]
      · have hx0 : formOfRingEquiv e hsmul Q x = 0 := hW0 x hx
        rw [formOfRingEquiv_apply] at hx0
        exact (map_eq_zero_iff e.symm e.symm.injective).1 hx0
    have hNo' : NoSmallModel ↥(orthDerived Q') := by
      rcases (show n = 4 ∨ n = 5 ∨ 6 ≤ n by omega) with rfl | rfl | h6
      · exact noSmallModel_minus_four hQ' hdim' hminus'
      · exact noSmallModel_minus_five hQ' hdim' hminus'
      · exact noSmallModel_minus_ge_six hQ' hdim' h6 hminus'
    obtain ⟨iso⟩ := nonempty_orthDerived_equiv_of_ringEquiv e hsmul Q
    exact noSmallModel_of_mulEquiv iso.symm hNo'
  exact noSmallModel_of_mulEquiv eθ hNo

end CFSG.LocalAnalysis.GLTheoremA.T171S

end
