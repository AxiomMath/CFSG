module

public import CFSG.ClassicalGroups.Orthogonal.ComponentBorelMinus
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15K517_4bGenericHall
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S15NoXBlockBorelAll
public import CFSG.LocalAnalysis.StandardType.GGOmegaMinusCentrallyClosed
public import CFSG.GroupTheory.SylowTwoEquiv
public import CFSG.ClassicalGroups.Orthogonal.DiagTorusFlagStabilizer

public noncomputable section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

open CFSG.Open CFSG.AGLEmbedding CFSG.QuasithinUnique
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.ClassicalGroups.Orthogonal
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open CFSG.LocalAnalysis.ComponentInitial.NonsplitOrthogonalCover
open CFSG.ComponentClassification.CatalogueBOrthogonalPointPlusBorel
open CFSG.LieType.Universal.Spin
open QuadraticMap
open scoped Pointwise

theorem exists_piSubgroup_three_le_pRank_in_borel_projective_minus_gen {K : Type} [Field K]
    [Finite K] [CharP K 2] {r : ℕ} (hr : 3 ≤ r) {q : ℕ} (hq : q.Prime)
    (hq2 : q != 2) (hdvd : q ∣ Nat.card K - 1)
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ∃ H : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K b c)) ⧸
        elemScalars (quadTail r (minusTailForm K b c))),
      H ≤ Subgroup.normalizer (((tailUnipotent r (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail r (minusTailForm K b c)))).map
        (QuotientGroup.mk' (elemScalars (quadTail r (minusTailForm K b c)))) : Set _) ∧
      IsPiSubgroup {p : Nat.Primes | (p : Nat) != 2} H ∧
      3 ≤ CFSG.Open.pRank q H := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hani : (minusTailForm K b c).Anisotropic := anisotropic_minusTailForm hirr
  have hreg : (polarBilin (minusTailForm K b c)).Nondegenerate :=
    nondegenerate_minusTailForm hirr
  haveI : FiniteDimensional K (Fin 2 → K) := inferInstance
  haveI : Finite (Fin 2 → K) := inferInstance
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K))) := inferInstance
  haveI : Finite (((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K))) :=
    Finite.of_injective (fun g : ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) ≃ₗ[K]
      ((Fin r ⊕ Fin r → K) × (Fin 2 → K)) => (g : _ → _)) DFunLike.coe_injective
  haveI : Finite (orthElementaryGroup (quadTail r (minusTailForm K b c))) := Subtype.finite
  haveI : Finite (orthElementaryGroup (quadTail r (minusTailForm K b c)) ⧸
      elemScalars (quadTail r (minusTailForm K b c))) :=
    Finite.of_surjective (QuotientGroup.mk' (elemScalars (quadTail r (minusTailForm K b c))))
      (QuotientGroup.mk'_surjective _)
  haveI : Finite (GL (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2) K) := by
    haveI : Finite (Matrix (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2)
        (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2) K) := inferInstance
    exact Finite.of_injective (fun g : GL (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2) K =>
      (g : Matrix (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2)
        (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2) K)) Units.val_injective
  haveI : Finite (StatedOmega (StatedQuadMinus (r + 1) K b c)) := Subtype.finite
  let ψ : (quadTail r (minusTailForm K b c)).IsometryEquiv (quadMinus (r + 1) K b c) :=
    minusTailIsometry (r + 1) K b c
  have hQ : ⇑(quadMinus (r + 1) K b c) = StatedQuadMinus (r + 1) K b c :=
    coe_quadMinus (r + 1) K b c
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (r + 1) K b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (r + 1) K b c)⁆ =
      elementaryGroup (quadMinus (r + 1) K b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr
  let Φ := tailOmegaEquiv ψ hQ hE
  let F : Fin r → Submodule K (Fin ((r + 1) - 1) ⊕ Fin ((r + 1) - 1) ⊕ Fin 2 → K) :=
    tailModelFlag r K (Fin 2)
  have hF : ∀ i, F i = (OrthogonalTail.stdFlag K (Fin 2 → K) r i).map ψ.toLinearMap := by
    intro i
    simpa [F, OrthogonalTail.stdFlag] using tailModelFlag_eq_map ψ (fun _ => rfl) i
  have hflag : (fun i => (F i).map ψ.symm.toLinearMap) =
      OrthogonalTail.stdFlag K (Fin 2 → K) r := by
    funext i
    rw [hF i, ← Submodule.map_comp]
    rw [show (ψ.symm.toLinearMap.comp ψ.toLinearMap) = LinearMap.id from
      LinearMap.ext fun v => ψ.symm_apply_apply v, Submodule.map_id]
  let B0 : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
    (tailBorel r (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail r (minusTailForm K b c)))
  have hB : (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
      Φ.toMonoidHom = B0 := by
    rw [tailOmegaEquiv_flagStabilizer ψ hQ hE F, hflag]
    exact tailBorel_subgroupOf_eq.symm
  let D := (diagTorusMinus (r + 1) K).subgroupOf
    (StatedOmega (StatedQuadMinus (r + 1) K b c))
  have hD : D ≤ statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F := by
    simpa [D, F] using diagTorusMinus_subgroupOf_le_statedDerivedFlagStabilizer
      (m := r + 1) (F := K) (b := b) (c := c) (by omega)
  have hrankD : 3 ≤ CFSG.Open.pRank q D :=
    three_le_pRank_diagTorus_orthogonal_minus_gen (by omega) hq hdvd b c
  obtain ⟨E, hED, hEelem, hEcard⟩ := CFSG.SectionRank.exists_pRank hq.one_lt D
  let T : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K b c))) :=
    E.map Φ.toMonoidHom
  have hTB0 : T ≤ B0 := by
    calc T ≤ (statedDerivedFlagStabilizer (StatedQuadMinus (r + 1) K b c) F).map
          Φ.toMonoidHom := Subgroup.map_mono (hED.trans hD)
      _ = B0 := hB
  let qmap : orthElementaryGroup (quadTail r (minusTailForm K b c)) →*
      (orthElementaryGroup (quadTail r (minusTailForm K b c)) ⧸
        elemScalars (quadTail r (minusTailForm K b c))) :=
    QuotientGroup.mk' (elemScalars (quadTail r (minusTailForm K b c)))
  let H : Subgroup (orthElementaryGroup (quadTail r (minusTailForm K b c)) ⧸
      elemScalars (quadTail r (minusTailForm K b c))) := T.map qmap
  have hqmap : Function.Injective qmap := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
    exact elemScalars_quadTail_eq_bot (by omega)
  have hHcard : Nat.card H = q ^ CFSG.Open.pRank q D := by
    rw [show Nat.card H = Nat.card T from Subgroup.card_map_of_injective hqmap,
      show Nat.card T = Nat.card E from Subgroup.card_map_of_injective Φ.injective, hEcard]
  have hHle : H ≤ Subgroup.normalizer
      ((((tailUnipotent r (minusTailForm K b c)).subgroupOf
        (orthElementaryGroup (quadTail r (minusTailForm K b c)))).map qmap) : Set _) := by
    have hN := normalizer_map_tailUnipotent (p := 2) (r := r) hr hani hreg
      (Or.inr finrank_fin_two_fun)
    rw [hN]
    exact Subgroup.map_mono hTB0
  have hHpi : IsPiSubgroup {p : Nat.Primes | (p : Nat) != 2} H := by
    have hset : {p : Nat.Primes | (p : Nat) != 2} = {p : Nat.Primes | (p : Nat) ≠ 2} := by
      ext p
      simp
    rw [hset]
    intro p hp
    have hdvdq : (p : ℕ) ∣ q := by
      refine Nat.Prime.dvd_of_dvd_pow (m := q) (n := CFSG.Open.pRank q D) p.property ?_
      rw [← hHcard]
      exact hp
    have hpq : (p : ℕ) = q := (Nat.prime_dvd_prime_iff_eq p.property hq).mp hdvdq
    have hq2' : q ≠ 2 := by simpa using hq2
    change (p : ℕ) ≠ 2
    rw [hpq]
    exact hq2'
  have hTelem : CFSG.Open.IsElemAbelian q T :=
    CFSG.SectionRank.isElemAbelian_map hEelem Φ.toMonoidHom
  have hHelem : CFSG.Open.IsElemAbelian q H :=
    CFSG.SectionRank.isElemAbelian_map hTelem qmap
  have hHrank : 3 ≤ CFSG.Open.pRank q H := by
    have hle := CFSG.SectionRank.le_pRank hq.one_lt (le_refl H) hHelem hHcard
    omega
  exact ⟨H, hHle, hHpi, hHrank⟩

theorem exists_hc_twistedD
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m : ℕ} (hm : 4 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    ∃ Hc : Subgroup L, Hc ≤ Subgroup.normalizer (U : Set L) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧
      3 ≤ CFSG.Open.pRank q Hc := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 3 ≤ n := by omega
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedD (n + 1) Q, hv⟩
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField d)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype F := Fintype.ofFinite F
  let D := (TauCeti.CFSGIndex.lie d).Group
  have hQcardpow : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hdchar : d.characteristic = 2 := by
    change TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.twistedD (n + 1) Q) = 2
    rw [TauCeti.LieTypeIndex.characteristic_twistedD, hQ]
  have hdfexp : d.fieldExponent = Q.exponent := by
    change TauCeti.LieTypeIndex.fieldExponent (TauCeti.LieTypeIndex.twistedD (n + 1) Q) = Q.exponent
    rw [TauCeti.LieTypeIndex.fieldExponent_twistedD]
  have hFcardpow : Nat.card F = 2 ^ Q.exponent := by
    change Nat.card ↥d.fixedField = 2 ^ Q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hdchar, hdfexp]
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := Q.exponent)
      (by simpa [Nat.card_eq_fintype_card] using hFcardpow)
  have hf : 2 ≤ Q.exponent := by
    have h4 : 2 ^ 2 ≤ 2 ^ Q.exponent := by
      rw [← hQcardpow]
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      (n + 1) Q hv
  let E := StatedProj (StatedOmega (StatedQuadMinus (n + 1) F b c))
  let qmap : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let ψ : L →* E := eD.toMonoidHom.comp (e.toMonoidHom.comp qmap)
  have hψ : Function.Surjective ψ :=
    eD.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker ≤ Subgroup.center L := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : e (qmap y) = 1 := eD.injective (by simpa [ψ] using hy)
    have h2 : qmap y = 1 := e.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff y).mp h2
  have hv0 : quadMinus (n + 1) F b c (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1) ≠ 0 := by
    rw [quadMinus_apply]
    simp
  have hbot : (StatedScalars (Fin n ⊕ Fin n ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus (n + 1) F b c)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus (n + 1) F b c) (Q₀ := StatedQuadMinus (n + 1) F b c)
      (coe_quadMinus (n + 1) F b c) ⟨_, hv0⟩
  let eΩ : E ≃* StatedOmega (StatedQuadMinus (n + 1) F b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eR : CFSG.StandardType.OrthRest.RMinus F n b c ≃*
      StatedOmega (StatedQuadMinus (n + 1) F b c) :=
    CFSG.StandardType.rMinusEquivStatedOmega F n b c
  have hclose : Function.Injective ψ := by
    let ψ' : L →* CFSG.StandardType.OrthRest.RMinus F n b c :=
      eR.symm.toMonoidHom.comp (eΩ.toMonoidHom.comp ψ)
    have hψ' : Function.Surjective ψ' := eR.symm.surjective.comp (eΩ.surjective.comp hψ)
    have hker' : ψ'.ker ≤ Subgroup.center L := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      have h1 : eΩ (ψ y) = 1 := eR.symm.injective (by simpa [ψ'] using hy)
      have h2 : ψ y = 1 := by
        have := congrArg eΩ.symm h1
        simpa using this
      exact h2
    have hperf : commutator L = ⊤ := hL.1
    have hinj := CFSG.StandardType.rMinus_injective_of_cover (K := F) hFcardpow hf hn hirr L
      ψ' hψ' hker' hperf
    intro a b hab
    exact hinj (by
      show ψ' a = ψ' b
      simp only [ψ', MonoidHom.comp_apply, hab])
  have hqinj : Function.Injective qmap := by
    intro a b hab
    exact hclose (by simp [ψ, hab])
  let eL : L ≃* E :=
    (MulEquiv.ofBijective qmap ⟨hqinj, QuotientGroup.mk'_surjective _⟩).trans (e.trans eD)
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (n + 1) F b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (n + 1) F b c)⁆ =
      elementaryGroup (quadMinus (n + 1) F b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr
  let eP := tailProjEquiv (minusTailIsometry (n + 1) F b c) (coe_quadMinus (n + 1) F b c) hE
  let P := ↥(orthElementaryGroup (quadTail n (minusTailForm F b c))) ⧸
      elemScalars (quadTail n (minusTailForm F b c))
  let eM : L ≃* P := eL.trans eP
  let Ubar : Subgroup P :=
    ((tailUnipotent n (minusTailForm F b c)).subgroupOf
      (orthElementaryGroup (quadTail n (minusTailForm F b c)))).map
      (QuotientGroup.mk' (elemScalars (quadTail n (minusTailForm F b c))))
  let Bbar : Subgroup P :=
    ((tailBorel n (minusTailForm F b c)).subgroupOf
      (orthElementaryGroup (quadTail n (minusTailForm F b c)))).map
      (QuotientGroup.mk' (elemScalars (quadTail n (minusTailForm F b c))))
  have hani : (minusTailForm F b c).Anisotropic := anisotropic_minusTailForm hirr
  have hreg : (polarBilin (minusTailForm F b c)).Nondegenerate := nondegenerate_minusTailForm hirr
  haveI : FiniteDimensional F (Fin 2 → F) := inferInstance
  have hPsyl : CFSG.QuasithinUnique.IsSylowTwoOf Ubar ⊤ := by
    obtain ⟨S, hS⟩ :=
      (orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hn hani hreg
        (Or.inr finrank_fin_two_fun)).2.2.1
    rw [show Ubar = (S : Subgroup _) from hS.symm]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hUsylP : CFSG.QuasithinUnique.IsSylowTwoOf (U.map eM.toMonoidHom) ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eM hUmax
    rwa [Subgroup.map_top_of_surjective _ eM.surjective] at h
  obtain ⟨g, -, hg⟩ := hPsyl.exists_conj hUsylP
  have hNbar : Subgroup.normalizer (Ubar : Set _) = Bbar :=
    normalizer_map_tailUnipotent (p := 2) hn hani hreg (Or.inr finrank_fin_two_fun)
  have hN : Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup _) : Set _) =
      Bbar.map (MulAut.conj g).toMonoidHom := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq Ubar (MulAut.conj g), hNbar]
  have hdvdF : q ∣ Nat.card F - 1 := by
    rw [hFcardpow, ← hQcardpow]
    exact hdvd
  have hq2' : (q != 2) = true := bne_iff_ne.mpr hq2
  obtain ⟨H, hHN, hHpi, hHrk⟩ :=
    exists_piSubgroup_three_le_pRank_in_borel_projective_minus_gen (K := F) hn hq hq2' hdvdF hirr
  have hset : {p : Nat.Primes | (p : Nat) != 2} = {p : Nat.Primes | (p : Nat) ≠ 2} := by
    ext p
    simp
  rw [hset] at hHpi
  let Hg : Subgroup (orthElementaryGroup (quadTail n (minusTailForm F b c)) ⧸
      elemScalars (quadTail n (minusTailForm F b c))) := H.map (MulAut.conj g).toMonoidHom
  have hHgN : Hg ≤ Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup _) : Set _) := by
    calc Hg ≤ (Subgroup.normalizer (Ubar : Set _)).map (MulAut.conj g).toMonoidHom :=
          Subgroup.map_mono hHN
      _ = Subgroup.normalizer ((Ubar.map (MulAut.conj g).toMonoidHom : Subgroup _) : Set _) :=
          Subgroup.map_equiv_normalizer_eq _ (MulAut.conj g)
      _ = Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup _) : Set _) := by rw [← hg]
  let Hc : Subgroup L := Hg.map eM.symm.toMonoidHom
  have hUU : (U.map eM.toMonoidHom).map eM.symm.toMonoidHom = U := by
    rw [Subgroup.map_map]
    have hcomp : eM.symm.toMonoidHom.comp eM.toMonoidHom = MonoidHom.id L := by
      ext x
      simp
    rw [hcomp, Subgroup.map_id]
  have hHcN : Hc ≤ Subgroup.normalizer (U : Set L) := by
    calc Hc ≤ (Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup _) : Set _)).map
          eM.symm.toMonoidHom := Subgroup.map_mono hHgN
      _ = Subgroup.normalizer
            ((((U.map eM.toMonoidHom).map eM.symm.toMonoidHom : Subgroup L)) : Set L) :=
          Subgroup.map_equiv_normalizer_eq _ eM.symm
      _ = Subgroup.normalizer (U : Set L) := by rw [hUU]
  refine ⟨Hc, hHcN, ?_, ?_⟩
  ·
    exact CFSG.LocalCores.isPiSubgroup_map
      (CFSG.LocalCores.isPiSubgroup_map hHpi (MulAut.conj g).toMonoidHom) eM.symm.toMonoidHom
  ·
    have h1 : CFSG.Open.pRank q Hc = CFSG.Open.pRank q Hg :=
      CFSG.Quasithin.E3.pRank_map_mulEquiv' eM.symm hq Hg
    have h2 : CFSG.Open.pRank q Hg = CFSG.Open.pRank q H :=
      CFSG.Quasithin.E3.pRank_map_mulEquiv' (MulAut.conj g) hq H
    rw [h1, h2]
    exact hHrk

theorem isSolvable_normalizer_sylow_of_component_twistedD
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m : ℕ} (hm : 4 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    Group.IsSolvable ↥(Subgroup.normalizer (U : Set L)) := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 3 ≤ n := by omega
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedD (n + 1) Q, hv⟩
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField d)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype F := Fintype.ofFinite F
  let D := (TauCeti.CFSGIndex.lie d).Group
  have hQcardpow : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hdchar : d.characteristic = 2 := by
    change TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.twistedD (n + 1) Q) = 2
    rw [TauCeti.LieTypeIndex.characteristic_twistedD, hQ]
  have hdfexp : d.fieldExponent = Q.exponent := by
    change TauCeti.LieTypeIndex.fieldExponent (TauCeti.LieTypeIndex.twistedD (n + 1) Q) = Q.exponent
    rw [TauCeti.LieTypeIndex.fieldExponent_twistedD]
  have hFcardpow : Nat.card F = 2 ^ Q.exponent := by
    change Nat.card ↥d.fixedField = 2 ^ Q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hdchar, hdfexp]
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := Q.exponent)
      (by simpa [Nat.card_eq_fintype_card] using hFcardpow)
  have hf : 2 ≤ Q.exponent := by
    have h4 : 2 ^ 2 ≤ 2 ^ Q.exponent := by
      rw [← hQcardpow]
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      (n + 1) Q hv
  let E := StatedProj (StatedOmega (StatedQuadMinus (n + 1) F b c))
  let qmap : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let ψ : L →* E := eD.toMonoidHom.comp (e.toMonoidHom.comp qmap)
  have hψ : Function.Surjective ψ :=
    eD.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker ≤ Subgroup.center L := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : e (qmap y) = 1 := eD.injective (by simpa [ψ] using hy)
    have h2 : qmap y = 1 := e.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff y).mp h2
  have hv0 : quadMinus (n + 1) F b c (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1) ≠ 0 := by
    rw [quadMinus_apply]
    simp
  have hbot : (StatedScalars (Fin n ⊕ Fin n ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus (n + 1) F b c)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus (n + 1) F b c) (Q₀ := StatedQuadMinus (n + 1) F b c)
      (coe_quadMinus (n + 1) F b c) ⟨_, hv0⟩
  let eΩ : E ≃* StatedOmega (StatedQuadMinus (n + 1) F b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eR : CFSG.StandardType.OrthRest.RMinus F n b c ≃*
      StatedOmega (StatedQuadMinus (n + 1) F b c) :=
    CFSG.StandardType.rMinusEquivStatedOmega F n b c
  have hclose : Function.Injective ψ := by
    let ψ' : L →* CFSG.StandardType.OrthRest.RMinus F n b c :=
      eR.symm.toMonoidHom.comp (eΩ.toMonoidHom.comp ψ)
    have hψ' : Function.Surjective ψ' := eR.symm.surjective.comp (eΩ.surjective.comp hψ)
    have hker' : ψ'.ker ≤ Subgroup.center L := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      have h1 : eΩ (ψ y) = 1 := eR.symm.injective (by simpa [ψ'] using hy)
      have h2 : ψ y = 1 := by
        have := congrArg eΩ.symm h1
        simpa using this
      exact h2
    have hperf : commutator L = ⊤ := hL.1
    have hinj := CFSG.StandardType.rMinus_injective_of_cover (K := F) hFcardpow hf hn hirr L
      ψ' hψ' hker' hperf
    intro a b hab
    exact hinj (by
      show ψ' a = ψ' b
      simp only [ψ', MonoidHom.comp_apply, hab])
  have hqinj : Function.Injective qmap := by
    intro a b hab
    exact hclose (by simp [ψ, hab])
  let eL : L ≃* E :=
    (MulEquiv.ofBijective qmap ⟨hqinj, QuotientGroup.mk'_surjective _⟩).trans (e.trans eD)
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (n + 1) F b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (n + 1) F b c)⁆ =
      elementaryGroup (quadMinus (n + 1) F b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr
  let eP := tailProjEquiv (minusTailIsometry (n + 1) F b c) (coe_quadMinus (n + 1) F b c) hE
  let P := ↥(orthElementaryGroup (quadTail n (minusTailForm F b c))) ⧸
      elemScalars (quadTail n (minusTailForm F b c))
  let eM : L ≃* P := eL.trans eP
  let Ubar : Subgroup P :=
    ((tailUnipotent n (minusTailForm F b c)).subgroupOf
      (orthElementaryGroup (quadTail n (minusTailForm F b c)))).map
      (QuotientGroup.mk' (elemScalars (quadTail n (minusTailForm F b c))))
  let Bbar : Subgroup P :=
    ((tailBorel n (minusTailForm F b c)).subgroupOf
      (orthElementaryGroup (quadTail n (minusTailForm F b c)))).map
      (QuotientGroup.mk' (elemScalars (quadTail n (minusTailForm F b c))))
  have hani : (minusTailForm F b c).Anisotropic := anisotropic_minusTailForm hirr
  have hreg : (polarBilin (minusTailForm F b c)).Nondegenerate := nondegenerate_minusTailForm hirr
  haveI : FiniteDimensional F (Fin 2 → F) := inferInstance
  have hPsyl : CFSG.QuasithinUnique.IsSylowTwoOf Ubar ⊤ := by
    obtain ⟨S, hS⟩ :=
      (orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hn hani hreg
        (Or.inr finrank_fin_two_fun)).2.2.1
    rw [show Ubar = (S : Subgroup _) from hS.symm]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hUsylP : CFSG.QuasithinUnique.IsSylowTwoOf (U.map eM.toMonoidHom) ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eM hUmax
    rwa [Subgroup.map_top_of_surjective _ eM.surjective] at h
  obtain ⟨g, -, hg⟩ := hPsyl.exists_conj hUsylP
  have hNbar : Subgroup.normalizer (Ubar : Set _) = Bbar :=
    normalizer_map_tailUnipotent (p := 2) hn hani hreg (Or.inr finrank_fin_two_fun)
  have hN : Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup _) : Set _) =
      Bbar.map (MulAut.conj g).toMonoidHom := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq Ubar (MulAut.conj g), hNbar]
  haveI hBbar : Group.IsSolvable ↥Bbar :=
    isSolvable_minusProjectiveBorel (K := F) hn hani hreg (Or.inr finrank_fin_two_fun)
  haveI hNP : Group.IsSolvable
      ↥(Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup P) : Set P)) := by
    rw [hN]
    exact Group.isSolvable_of_surjective
      (f := (Subgroup.equivMapOfInjective Bbar (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hmap := Subgroup.map_equiv_normalizer_eq (U : Subgroup L) eM
  haveI : Group.IsSolvable ↥((Subgroup.normalizer (U : Set L)).map eM.toMonoidHom) :=
    hmap.symm ▸ hNP
  exact Group.isSolvable_of_isSolvable_injective
    (f := (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set L))
      eM.toMonoidHom eM.injective).toMonoidHom)
    (MulEquiv.injective _)

theorem isMulCommutative_normalizer_quotient_pCore_of_component_twistedD
    {L : Type} [Group L] [Finite L] (hL : CFSG.Open.IsQuasisimple L)
    {m : ℕ} (hm : 4 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid}
    (e : L ⧸ Subgroup.center L ≃* (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hQcard : 4 ≤ Q.card) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hdvd : q ∣ Q.card - 1) {U : Subgroup L} (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤) :
    IsMulCommutative
      (↥(Subgroup.normalizer (U : Set L)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer (U : Set L))) := by
  classical
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  haveI : Fact (2 : ℕ).Prime := ⟨Nat.prime_two⟩
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn : 3 ≤ n := by omega
  let d : TauCeti.ValidLieTypeIndex := ⟨TauCeti.LieTypeIndex.twistedD (n + 1) Q, hv⟩
  let F := ↥(TauCeti.ValidLieTypeIndex.fixedField d)
  haveI : Finite F := CFSG.QuasithinUnique.SQTK.finite_validIndex_fixedField d
  haveI : Fintype F := Fintype.ofFinite F
  let D := (TauCeti.CFSGIndex.lie d).Group
  have hQcardpow : Q.card = 2 ^ Q.exponent := by
    rw [TauCeti.PrimePower.card_def, hQ]
  have hdchar : d.characteristic = 2 := by
    change TauCeti.LieTypeIndex.characteristic (TauCeti.LieTypeIndex.twistedD (n + 1) Q) = 2
    rw [TauCeti.LieTypeIndex.characteristic_twistedD, hQ]
  have hdfexp : d.fieldExponent = Q.exponent := by
    change TauCeti.LieTypeIndex.fieldExponent (TauCeti.LieTypeIndex.twistedD (n + 1) Q) = Q.exponent
    rw [TauCeti.LieTypeIndex.fieldExponent_twistedD]
  have hFcardpow : Nat.card F = 2 ^ Q.exponent := by
    change Nat.card ↥d.fixedField = 2 ^ Q.exponent
    rw [TauCeti.ValidLieTypeIndex.card_fixedField,
      TauCeti.ValidLieTypeIndex.fieldOrder_eq_characteristic_pow, hdchar, hdfexp]
  haveI : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := Q.exponent)
      (by simpa [Nat.card_eq_fintype_card] using hFcardpow)
  have hf : 2 ≤ Q.exponent := by
    have h4 : 2 ^ 2 ≤ 2 ^ Q.exponent := by
      rw [← hQcardpow]
      omega
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  obtain ⟨b, c, hirr, ⟨eD⟩⟩ :=
    CFSG.RankThree.PartTwo.Census.Carrier.SpinD.exists_typeTwistedDGroupEquivStatedProj_of_valid
      (n + 1) Q hv
  let E := StatedProj (StatedOmega (StatedQuadMinus (n + 1) F b c))
  let qmap : L →* L ⧸ Subgroup.center L := QuotientGroup.mk' (Subgroup.center L)
  let ψ : L →* E := eD.toMonoidHom.comp (e.toMonoidHom.comp qmap)
  have hψ : Function.Surjective ψ :=
    eD.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : ψ.ker ≤ Subgroup.center L := by
    intro y hy
    rw [MonoidHom.mem_ker] at hy
    have h1 : e (qmap y) = 1 := eD.injective (by simpa [ψ] using hy)
    have h2 : qmap y = 1 := e.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff y).mp h2
  have hv0 : quadMinus (n + 1) F b c (Pi.single (Sum.inr (Sum.inr (0 : Fin 2))) 1) ≠ 0 := by
    rw [quadMinus_apply]
    simp
  have hbot : (StatedScalars (Fin n ⊕ Fin n ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus (n + 1) F b c)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus (n + 1) F b c) (Q₀ := StatedQuadMinus (n + 1) F b c)
      (coe_quadMinus (n + 1) F b c) ⟨_, hv0⟩
  let eΩ : E ≃* StatedOmega (StatedQuadMinus (n + 1) F b c) :=
    (CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot).symm
  let eR : CFSG.StandardType.OrthRest.RMinus F n b c ≃*
      StatedOmega (StatedQuadMinus (n + 1) F b c) :=
    CFSG.StandardType.rMinusEquivStatedOmega F n b c
  have hclose : Function.Injective ψ := by
    let ψ' : L →* CFSG.StandardType.OrthRest.RMinus F n b c :=
      eR.symm.toMonoidHom.comp (eΩ.toMonoidHom.comp ψ)
    have hψ' : Function.Surjective ψ' := eR.symm.surjective.comp (eΩ.surjective.comp hψ)
    have hker' : ψ'.ker ≤ Subgroup.center L := by
      intro y hy
      apply hker
      rw [MonoidHom.mem_ker] at hy ⊢
      have h1 : eΩ (ψ y) = 1 := eR.symm.injective (by simpa [ψ'] using hy)
      have h2 : ψ y = 1 := by
        have := congrArg eΩ.symm h1
        simpa using this
      exact h2
    have hperf : commutator L = ⊤ := hL.1
    have hinj := CFSG.StandardType.rMinus_injective_of_cover (K := F) hFcardpow hf hn hirr L
      ψ' hψ' hker' hperf
    intro a b hab
    exact hinj (by
      show ψ' a = ψ' b
      simp only [ψ', MonoidHom.comp_apply, hab])
  have hqinj : Function.Injective qmap := by
    intro a b hab
    exact hclose (by simp [ψ, hab])
  let eL : L ≃* E :=
    (MulEquiv.ofBijective qmap ⟨hqinj, QuotientGroup.mk'_surjective _⟩).trans (e.trans eD)
  have hE : ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus (n + 1) F b c),
      TauCeti.QuadraticMap.orthogonalGroup (quadMinus (n + 1) F b c)⁆ =
      elementaryGroup (quadMinus (n + 1) F b c) :=
    commutator_orthogonalGroup_quadMinus_of_two_le (by omega) hirr
  let eP := tailProjEquiv (minusTailIsometry (n + 1) F b c) (coe_quadMinus (n + 1) F b c) hE
  let P := ↥(orthElementaryGroup (quadTail n (minusTailForm F b c))) ⧸
      elemScalars (quadTail n (minusTailForm F b c))
  let eM : L ≃* P := eL.trans eP
  let Ubar : Subgroup P :=
    ((tailUnipotent n (minusTailForm F b c)).subgroupOf
      (orthElementaryGroup (quadTail n (minusTailForm F b c)))).map
      (QuotientGroup.mk' (elemScalars (quadTail n (minusTailForm F b c))))
  let Bbar : Subgroup P :=
    ((tailBorel n (minusTailForm F b c)).subgroupOf
      (orthElementaryGroup (quadTail n (minusTailForm F b c)))).map
      (QuotientGroup.mk' (elemScalars (quadTail n (minusTailForm F b c))))
  have hani : (minusTailForm F b c).Anisotropic := anisotropic_minusTailForm hirr
  have hreg : (polarBilin (minusTailForm F b c)).Nondegenerate := nondegenerate_minusTailForm hirr
  haveI : FiniteDimensional F (Fin 2 → F) := inferInstance
  have hPsyl : CFSG.QuasithinUnique.IsSylowTwoOf Ubar ⊤ := by
    obtain ⟨S, hS⟩ :=
      (orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2) hn hani hreg
        (Or.inr finrank_fin_two_fun)).2.2.1
    rw [show Ubar = (S : Subgroup _) from hS.symm]
    exact CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hUsylP : CFSG.QuasithinUnique.IsSylowTwoOf (U.map eM.toMonoidHom) ⊤ := by
    have h := CFSG.QuasithinUnique.IsSylowTwoOf.map_mulEquiv eM hUmax
    rwa [Subgroup.map_top_of_surjective _ eM.surjective] at h
  obtain ⟨g, -, hg⟩ := hPsyl.exists_conj hUsylP
  have hNbar : Subgroup.normalizer (Ubar : Set _) = Bbar :=
    normalizer_map_tailUnipotent (p := 2) hn hani hreg (Or.inr finrank_fin_two_fun)
  have hN : Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup _) : Set _) =
      Bbar.map (MulAut.conj g).toMonoidHom := by
    rw [hg, ← Subgroup.map_equiv_normalizer_eq Ubar (MulAut.conj g), hNbar]
  have hcommBbar : IsMulCommutative (↥Bbar ⧸ CFSG.pCore 2 ↥Bbar) :=
    isMulCommutative_minusProjectiveBorel_quotient (K := F) hn hani hreg
      (Or.inr finrank_fin_two_fun)
  have hcommConj : IsMulCommutative
      (↥(Bbar.map (MulAut.conj g).toMonoidHom) ⧸
        CFSG.pCore 2 ↥(Bbar.map (MulAut.conj g).toMonoidHom)) :=
    CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
      (Subgroup.equivMapOfInjective Bbar (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).toMonoidHom
      (MulEquiv.surjective _) hcommBbar
  have hcommNP : IsMulCommutative
      (↥(Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup P) : Set P)) ⧸
        CFSG.pCore 2 ↥(Subgroup.normalizer
          ((U.map eM.toMonoidHom : Subgroup P) : Set P))) := by
    rw [hN]
    exact hcommConj
  have hmap := Subgroup.map_equiv_normalizer_eq (U : Subgroup L) eM
  let eN : ↥(Subgroup.normalizer ((U.map eM.toMonoidHom : Subgroup P) : Set P)) ≃*
      ↥(Subgroup.normalizer (U : Set L)) :=
    (MulEquiv.subgroupCongr hmap.symm).trans
      (Subgroup.equivMapOfInjective (Subgroup.normalizer (U : Set L)) eM.toMonoidHom
        eM.injective).symm
  exact CFSG.ClassicalGroups.SpecialLinear.isMulCommutative_quotient_pCore_of_surjective
    eN.toMonoidHom eN.surjective hcommNP

variable {X : Type} [Group X] [Finite X] {T T₁ T₂ : Subgroup X}

theorem noXBlock_borelPre_subtype_2D
    (hX : GNSetting X T) {Ls : Subgroup (X ⧸ gnC T)}
    (hLs : CFSG.Open.IsComponentOf Ls ⊤)
    (hinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    (m : ℕ) (hm : 4 ≤ m) (Q : TauCeti.PrimePower) (hQ : Q.p = 2)
    (hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid)
    (e : ↥Ls ⧸ Subgroup.center ↥Ls ≃* (TauCeti.CFSGIndex.lie
      (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hcard : 5 ≤ Q.card ∨ Q.card = 4) :
    ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False := by
  intro Y hsub hblock
  let H : Subgroup X := borelPre T Ls
  let Y' : Subgroup X := Y.map H.subtype
  have hY' : Y' ≤ H := Subgroup.map_subtype_le (H := H) Y
  have hsub' : IsSubnormal Y' H := by
    have h := CFSG.Open.IsSubnormal.map (f := H.subtype) hsub
    rwa [Subgroup.map_top, Subgroup.range_subtype] at h
  have hblock' : InClassXBlock Y' := by
    have hx : CFSG.RankThree.PartOne.InClassX ↥Y :=
      CFSG.AGLEmbedding.NoXBlock.inClassX_of_inClassXBlock hblock
    let eY : ↥Y ≃* ↥Y' :=
      Subgroup.equivMapOfInjective Y H.subtype H.subtype_injective
    have hx' : CFSG.RankThree.PartOne.InClassX ↥Y' :=
      CFSG.CGT.PushingUpLit.InClassX.of_mulEquiv eY hx
    exact CFSG.AGLEmbedding.LocalCGT.inClassXBlock_of_inClassX hx'
  exact noXBlock_borelPre_done_2D hX hLs hinv m hm Q hQ hv e hcard Y' hY' hsub' hblock'

theorem k517_4b_2D_of_top_of_hall
    (hX : GNSetting X T) (hGood : GNGood T T₁ T₂) {Ls : Subgroup (X ⧸ gnC T)} {q : ℕ}
    (hLs : GNYComponent T T₁ T₂ Ls) (hq : q.Prime) (hq2 : q ≠ 2)
    {m : ℕ} (hm : 4 ≤ m) {Q : TauCeti.PrimePower} (hQ : Q.p = 2)
    {hv : (TauCeti.LieTypeIndex.twistedD m Q).Valid}
    (e : (↥Ls ⧸ Subgroup.center ↥Ls) ≃*
      (TauCeti.CFSGIndex.lie
        (⟨TauCeti.LieTypeIndex.twistedD m Q, hv⟩ : TauCeti.ValidLieTypeIndex)).Group)
    (hTinv : gnImg T T ≤ Subgroup.normalizer (Ls : Set (X ⧸ gnC T)))
    {U : Subgroup ↥Ls} (hU2 : IsPGroup 2 U) (hUmax : CFSG.QuasithinUnique.IsSylowTwoOf U ⊤)
    (hqQ : q ∣ Q.card - 1)
    (hU : U = (gnImg T T ⊓ Ls).subgroupOf Ls) :
    1 < mS T T₁ q Ls ∨ 1 < mS T T₂ q Ls := by
  classical
  have hQcard : 4 ≤ Q.card := by
    have hpow : Q.card = 2 ^ Q.exponent := by
      rw [TauCeti.PrimePower.card_def, hQ]
    have h2le : 2 ≤ Q.card := by
      rw [hpow]
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ Q.exponent := Nat.pow_le_pow_right (by norm_num) Q.exponent_pos
    have hdiv : 2 ∣ Q.card := by
      rw [hpow]
      exact dvd_pow_self 2 Q.exponent_pos.ne'
    have hne2 : Q.card ≠ 2 := by
      intro h2
      have h2' : Q.card - 1 = 1 := by omega
      exact hq.not_dvd_one (h2' ▸ hqQ)
    rcases Nat.lt_or_ge Q.card 4 with hlt | hge
    · rcases Nat.lt_or_ge Q.card 2 with h1 | h1
      · omega
      · interval_cases Q.card
        · exact absurd rfl hne2
        · exact absurd hdiv (by norm_num)
    · exact hge
  obtain ⟨Hc, hHcN, hHcpi, hHc3⟩ :=
    exists_hc_twistedD (L := ↥Ls) (m := m) (Q := Q) (hv := hv)
      hLs.1.2.2 hm hQ e hQcard hq hq2 hqQ hUmax
  have hHc : ∃ Hc : Subgroup ↥Ls, Hc ≤ Subgroup.normalizer (U : Set ↥Ls) ∧
      IsPiSubgroup {p : Nat.Primes | (p : ℕ) ≠ 2} Hc ∧ 3 ≤ CFSG.Open.pRank q Hc :=
    ⟨Hc, hHcN, hHcpi, hHc3⟩
  have hNB : ∀ Y : Subgroup (borelPre T Ls), IsSubnormal Y ⊤ → InClassXBlock Y → False :=
    noXBlock_borelPre_subtype_2D hX hLs.1 hTinv m hm Q hQ hv e (by
      rcases Nat.lt_or_ge Q.card 5 with h | h
      · exact Or.inr (by omega)
      · exact Or.inl h)
  have hsolvY : Group.IsSolvable ↥(gnImg T (borelPre T Ls)) :=
    isSolvable_gnImg_borelPre_of_borel hX hTinv hU
      (isSolvable_normalizer_sylow_of_component_twistedD (L := ↥Ls) (m := m) (Q := Q) (hv := hv)
        hLs.1.2.2 hm hQ e hQcard hq hq2 hqQ hUmax)
  obtain ⟨hB, hHallB, hcommBY⟩ :=
    k517_4b_normalizer_data_of_mulCommutative hX hGood hLs hTinv hU
      (isMulCommutative_normalizer_quotient_pCore_of_component_twistedD (L := ↥Ls) (m := m)
        (Q := Q) (hv := hv) hLs.1.2.2 hm hQ e hQcard hq hq2 hqQ hUmax)
  have hBLs : (Subgroup.normalizer ((gnImg T T ⊓ Ls : Subgroup (X ⧸ gnC T)) :
        Set (X ⧸ gnC T)) ⊓ Ls).subgroupOf (gnImg T (borelPre T Ls)) ≤
      Ls.subgroupOf (gnImg T (borelPre T Ls)) := by
    intro y hy
    exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hy)).2
  exact k517_4b_of_setting_of_hall hX hGood hLs hq hq2 hHc hU hNB hsolvY hB hHallB hcommBY hBLs

end CFSG.LocalAnalysis.RankThreeUC.S15

end
