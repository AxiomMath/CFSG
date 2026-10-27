module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Th
public import CFSG.Sporadic.SuzRecog.NativeType
public import CFSG.Sporadic.SuzRecog.Generation
public import CFSG.LocalAnalysis.ComponentClassification.AS81Step18Classes
public import CFSG.Sporadic.SuzOddCore.SmallModel
public import Certificates.Certificate10147
public import Certificates.Certificate6001
public import Certificates.Certificate6002
public import Certificates.Certificate6003
public import Certificates.Certificate6004
public import Certificates.Certificate6005
public import Certificates.Certificate6007
public import Certificates.Certificate16026
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.ClassicalInvolution.SmallCases.Sporadic.QuasiAssembly
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Interface
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.Proving.ExistsOrderPCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Proving.GLAPrimeCoreCentralizer
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LieType.Multipliers.U62Sylow
public import CFSG.LocalAnalysis.AGLEmbedding.JStarReducedDefs
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVL34FFDefs
public import CFSG.LocalAnalysis.AGLEmbedding.ReeFacts
public import CFSG.LocalAnalysis.AGLEmbedding.UnitaryFacts
public import CFSG.LocalAnalysis.ComponentClassification.TBLitPropC
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremA.CatA.YS1011LabUniq
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S3.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4.Assembly
public import CFSG.LocalAnalysis.GLTheoremA.S4.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.S4S.Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma118T
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SeitzReduction.E6PilotHR4
public import CFSG.Quasithin.Background.A1cA133Three
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B15P4LayerDict
public import CFSG.Quasithin.EmptyFaithful.S146zYFacts
public import CFSG.Quasithin.EmptyFaithful.S146zYRes
public import CFSG.Quasithin.H13.J4Order
public import CFSG.Quasithin.H13.NQCoreP134Main
public import CFSG.Quasithin.Vol2.Ch11SecAFacts02
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11StatementsB
public import CFSG.Quasithin.Vol2.Ch11StatementsC
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Inputs
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate2323
public import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.ComponentClassification.PSL3Four CFSG.PSL3Four.Native

theorem isPGroup_of_elemAbelian3 {X : Type} [Group X] {F : Subgroup X} (hF : IsElemAbelian 3 F) :
    IsPGroup 3 F := fun g => ⟨1, Subtype.ext (by simpa using hF.2 g g.2)⟩

theorem card_lt_27_of_dvd {X : Type} [Group X] [Finite X] {F : Subgroup X} (hF : IsPGroup 3 F)
    {n : ℕ} (hdvd : Nat.card F ∣ n) (h27 : ¬ 27 ∣ n) : Nat.card F < 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 hF
  rw [hk] at hdvd ⊢
  by_contra hlt
  push Not at hlt
  have hk3 : 3 ≤ k := by
    by_contra h
    push Not at h
    have : 3 ^ k ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact h27 ((pow_dvd_pow 3 hk3).trans hdvd)

theorem card_le_27_of_nine {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : ¬ 3 ^ 5 ∣ Nat.card H) {g : G} (hg : g ∈ H) (h3 : g ^ 3 ≠ 1) (h9 : g ^ 9 = 1)
    {F : Subgroup G} (hFH : F ≤ H) (hF : IsElemAbelian 3 F) : Nat.card F ≤ 27 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (isPGroup_of_elemAbelian3 hF)
  have hFdvd : Nat.card F ∣ Nat.card H := Subgroup.card_dvd_of_le hFH
  have hk4 : k ≤ 4 := by
    by_contra h
    push Not at h
    rw [hk] at hFdvd
    exact hH ((pow_dvd_pow 3 (by omega)).trans hFdvd)
  by_contra hlt
  push Not at hlt
  have hk4' : k = 4 := by
    by_contra h
    have : 3 ^ k ≤ 3 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  subst hk4'
  set P : Subgroup H := F.subgroupOf H
  have hPc : Nat.card P = 3 ^ 4 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hFH).toEquiv, hk]
  have hP : IsPGroup 3 P := IsPGroup.of_card hPc
  obtain ⟨S, hPS⟩ := hP.exists_le_sylow
  have hSc : Nat.card (S : Subgroup H) ≤ 3 ^ 4 := by
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 S.isPGroup'
    have hSd : Nat.card (S : Subgroup H) ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
    rw [hj] at hSd ⊢
    by_contra h
    push Not at h
    have hj5 : 5 ≤ j := by
      by_contra h'
      have : 3 ^ j ≤ 3 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    exact hH ((pow_dvd_pow 3 hj5).trans hSd)
  have hPS' : P = (S : Subgroup H) :=
    Subgroup.eq_of_le_of_card_ge hPS (by rw [hPc]; exact hSc)
  set g' : H := ⟨g, hg⟩
  have hZ : IsPGroup 3 (Subgroup.zpowers g') := by
    rintro ⟨_, n, rfl⟩
    refine ⟨2, Subtype.ext (Subtype.ext ?_)⟩
    show (g ^ n) ^ 3 ^ 2 = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num [h9]
  obtain ⟨S'', hS''⟩ := hZ.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq H S S''
  have hg'S : g' ∈ ((c • S : Sylow 3 H) : Subgroup H) := by
    rw [hc]
    exact hS'' (Subgroup.mem_zpowers g')
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem] at hg'S
  set y : H := (MulAut.conj c)⁻¹ • g' with hy
  have hyP : y ∈ P := by rw [hPS']; exact hg'S
  have hy3 : y ^ 3 = 1 := Subtype.ext (hF.2 _ (Subgroup.mem_subgroupOf.1 hyP))
  rw [hy, ← smul_pow', MulAut.smul_def, map_eq_one_iff _ (MulEquiv.injective _)] at hy3
  exact h3 (congrArg Subtype.val hy3)

theorem not_dvd_card_stab {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : List Tab}
    (hH : Enumerates H T) (x : Fin n) {m : ℕ}
    (h : (T.filter fun t => t[x.val]! == x.val).length % m ≠ 0) :
    ¬ m ∣ Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin n)) x ⊓ H) := by
  have hE := hH.filter (K := MulAction.stabilizer (Equiv.Perm (Fin n)) x)
    (fun t => t[x.val]! == x.val) (fun t g ht => by
      rw [beq_iff_eq, ht.apply, MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
      exact Fin.val_inj)
  rw [hE.card]
  exact fun hd => h (Nat.mod_eq_zero_of_dvd hd)

theorem not_dvd_card_cent {n : ℕ} {H : Subgroup (Equiv.Perm (Fin n))} {T : List Tab}
    (hH : Enumerates H T) {s : Equiv.Perm (Fin n)} {ts : Tab} (hs : TabRep ts s) {m : ℕ}
    (h : (T.filter fun t => comp n t ts == comp n ts t).length % m ≠ 0) :
    ¬ m ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin n))) ⊓ H) := by
  have hE := hH.filter (K := Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin n))))
    (fun t => comp n t ts == comp n ts t) (fun t g ht => by
      rw [(ht.comp hs).beq_iff (hs.comp ht), Subgroup.mem_centralizer_singleton_iff])
  rw [hE.card]
  exact fun hd => h (Nat.mod_eq_zero_of_dvd hd)

theorem elemAbelian_range {X Y : Type} [Group X] [Group Y] {p : ℕ} {F : Subgroup X}
    (hF : IsElemAbelian p F) (φ : F →* Y) : IsElemAbelian p φ.range := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, ?_⟩
  · obtain ⟨_, x, rfl⟩ := a
    obtain ⟨_, y, rfl⟩ := b
    show φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul]
    haveI := hF.1
    rw [mul_comm' x y]
  · rintro _ ⟨x, rfl⟩
    show φ x ^ p = 1
    rw [← map_pow, show x ^ p = 1 from Subtype.ext (hF.2 x x.2), map_one]

open CFSG.ComponentClassification.AS81.SuzB0 CFSG.ComponentClassification.AS81
open CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog CFSG.LocalAnalysis.GLTheoremA.H1017.SuzLm


local notation "ψ" => Coord.psi (t := suzInv 1) (q := qVec)

local notation "R" => (rho1.range.map kappa : Subgroup (Equiv.Perm (Fin 64)))

theorem lm_facts :
    (∃ g ∈ R, g ^ 3 ≠ 1 ∧ g ^ 9 = 1) ∧
    (∀ x : Fin 64, x ≠ 0 →
      ¬ 27 ∣ Nat.card ↥(MulAction.stabilizer (Equiv.Perm (Fin 64)) x ⊓ R)) ∧
    (∀ s ∈ R, s ^ 2 = 1 → s ≠ 1 →
      ¬ 27 ∣ Nat.card ↥(Subgroup.centralizer ({s} : Set (Equiv.Perm (Fin 64))) ⊓ R)) := by
  have hc := Certificates.certificate10147
  simp only [lmRankOK, Bool.and_eq_true] at hc
  obtain ⟨⟨h9, hst⟩, hce⟩ := hc
  have hH := kappa_rho1_enumerates
  refine ⟨?_, fun x hx => ?_, fun s hs hs2 hs1 => ?_⟩
  · simp only [lmNineOK, anyBelow_eq_true, Bool.and_eq_true, Bool.not_eq_true'] at h9
    obtain ⟨k, hk, hk3, hk9⟩ := h9
    have hks : k < matEnum.tabs.size := hk
    obtain ⟨g, hg, hrep⟩ := hH.exists_elt hks
    have r3 := hrep.comp (hrep.comp hrep)
    have r9 := r3.comp (r3.comp r3)
    refine ⟨g, hg, fun h => ?_, ?_⟩
    · have : g * (g * g) = 1 := by rw [← pow_three]; exact h
      rw [this] at r3
      rw [(r3.beq_iff TabRep.idTab).2 rfl] at hk3
      exact Bool.noConfusion hk3
    · have e3 : g * (g * g) = g ^ 3 := (pow_three g).symm
      have e : g ^ 9 = g ^ 3 * (g ^ 3 * g ^ 3) := by rw [← pow_add, ← pow_add]
      rw [e, ← e3]
      exact (r9.beq_iff TabRep.idTab).1 hk9
  · simp only [lmStabOK, allBelow_eq_true] at hst
    have hx' : x.val - 1 < 63 := by omega
    have := hst (x.val - 1) hx'
    have e : x.val - 1 + 1 = x.val := by
      have : x.val ≠ 0 := fun h => hx (Fin.ext h)
      omega
    rw [e, bne_iff_ne] at this
    exact not_dvd_card_stab hH x this
  · obtain ⟨k, hk, hrep⟩ := hH.exists_pos hs
    simp only [lmCentOK, allBelow_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hce
    rcases hce k hk with (h1 | h1) | h1
    · exfalso
      have : s * s = 1 := by rw [← sq]; exact hs2
      have h2 := (hrep.comp hrep).beq_iff TabRep.idTab
      rw [this] at h2
      rw [h2.2 rfl] at h1
      exact Bool.noConfusion h1
    · exact absurd ((hrep.beq_iff TabRep.idTab).1 h1) hs1
    · rw [bne_iff_ne] at h1
      exact not_dvd_card_cent hH hrep h1

@[expose] noncomputable def phiR : ↥(invE 1) →* Equiv.Perm (Fin 64) := kappa.comp rho1

theorem phiR_mem (c : ↥(invE 1)) : phiR c ∈ R := ⟨rho1 c, ⟨c, rfl⟩, rfl⟩

theorem mem_Q_of_phiR (c : ↥(invE 1)) (h : phiR c = 1) : (c : Equiv.Perm (Fin 1782)) ∈ coord_qVec.Q := by
  rw [← phi0_eq_one_iff]
  apply Subtype.ext
  rw [coe_phi0]
  apply kappa_injective
  show kappa (rho1 c) = kappa 1
  rw [map_one]
  exact h

theorem eq_one_of_mem_Q_of_cube {q : Equiv.Perm (Fin 1782)} (hq : q ∈ coord_qVec.Q) (h3 : q ^ 3 = 1) :
    q = 1 := by
  have h128 : q ^ 128 = 1 := by
    have := pow_card_eq_one' (G := coord_qVec.Q) (x := ⟨q, hq⟩)
    rw [coord_qVec.card_Q] at this
    simpa using congrArg Subtype.val this
  have hd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h128)
  have : Nat.gcd 3 128 = 1 := by norm_num
  rw [this, Nat.dvd_one, orderOf_eq_one_iff] at hd
  exact hd

theorem image_data {F : Subgroup (Equiv.Perm (Fin 1782))} (hF1 : F ≤ invE 1)
    (hF : IsElemAbelian 3 F) :
    IsElemAbelian 3 (phiR.comp (F.subgroupOf (invE 1)).subtype).range ∧
      Nat.card (phiR.comp (F.subgroupOf (invE 1)).subtype).range = Nat.card F ∧
      (phiR.comp (F.subgroupOf (invE 1)).subtype).range ≤ R := by
  have hinj : Function.Injective (phiR.comp (F.subgroupOf (invE 1)).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro w hw
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hw
    have hwQ := mem_Q_of_phiR _ hw
    have hw3 : ((w : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ^ 3 = 1 :=
      hF.2 _ (Subgroup.mem_subgroupOf.1 w.2)
    rw [Subgroup.mem_bot]
    exact Subtype.ext (Subtype.ext (eq_one_of_mem_Q_of_cube hwQ hw3))
  have hFe : IsElemAbelian 3 (F.subgroupOf (invE 1)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a ha => Subtype.ext ?_⟩
    · exact comm_of_elemAbelian' hF (Subgroup.mem_subgroupOf.1 a.2) (Subgroup.mem_subgroupOf.1 b.2)
    · exact hF.2 _ (Subgroup.mem_subgroupOf.1 ha)
  refine ⟨elemAbelian_range hFe _, ?_, ?_⟩
  · rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF1).toEquiv
  · rintro _ ⟨w, rfl⟩
    exact phiR_mem _

theorem card_le_27_of_le_invE {F : Subgroup (Equiv.Perm (Fin 1782))} (hF1 : F ≤ invE 1)
    (hF : IsElemAbelian 3 F) : Nat.card F ≤ 27 := by
  obtain ⟨he, hc, hle⟩ := image_data hF1 hF
  obtain ⟨⟨g, hg, h3, h9⟩, -, -⟩ := lm_facts
  have hR : Nat.card R = 25920 := by
    rw [kappa_rho1_enumerates.card, Array.length_toList, b0_parts.2.2.2.2.2.1]
  rw [← hc]
  exact card_le_27_of_nine (by rw [hR]; norm_num) hg h3 h9 hle he

theorem eq_t1_of_centralizes {F : Subgroup (Equiv.Perm (Fin 1782))} (hF1 : F ≤ invE 1)
    (hF : IsElemAbelian 3 F) (h27 : Nat.card F = 27) {u : Equiv.Perm (Fin 1782)} (hu : u ∈ invE 1)
    (hu2 : u ^ 2 = 1) (huF : ∀ f ∈ F, f * u = u * f) : u = 1 ∨ u = suzInv 1 := by
  obtain ⟨he, hc, hle⟩ := image_data hF1 hF
  obtain ⟨-, hstab, hcent⟩ := lm_facts
  set F' := (phiR.comp (F.subgroupOf (invE 1)).subtype).range with hF'
  set u' : ↥(invE 1) := ⟨u, hu⟩
  by_cases h1 : phiR u' = 1
  · have huQ : u ∈ coord_qVec.Q := mem_Q_of_phiR u' h1
    by_cases h0 : ψ u = 0
    · exact mem_zpowers_t1_iff.1 ((coord_qVec.psi_eq_zero_iff huQ).1 h0)
    · exfalso
      set x : Fin 64 := bitEquiv.symm (ψ u) with hx
      have hx0 : x ≠ 0 := by
        intro h
        apply h0
        have : bitEquiv x = ψ u := by rw [hx, Equiv.apply_symm_apply]
        rw [← this, h]
        exact bitVec_zero
      apply hstab x hx0
      have hsub : F' ≤ MulAction.stabilizer (Equiv.Perm (Fin 64)) x ⊓ R := by
        refine le_inf ?_ hle
        rintro _ ⟨w, rfl⟩
        rw [MulAction.mem_stabilizer_iff, Equiv.Perm.smul_def]
        have hwF : ((w : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ F := Subgroup.mem_subgroupOf.1 w.2
        have hcomm := huF _ hwF
        have hconj : ((w : ↥(invE 1)) : Equiv.Perm (Fin 1782)) * u *
            ((w : ↥(invE 1)) : Equiv.Perm (Fin 1782))⁻¹ = u := by
          rw [hcomm, mul_inv_cancel_right]
        have hp := psi_conj (w : ↥(invE 1)) huQ
        rw [hconj] at hp
        show kappa (rho1 (w : ↥(invE 1))) x = x
        rw [kappa_apply, show bitVec (x : ℕ) = ψ u from by
          rw [show bitVec (x : ℕ) = bitEquiv x from rfl, hx, Equiv.apply_symm_apply], ← hp, hx]
      have := Subgroup.card_dvd_of_le hsub
      rwa [hc, h27] at this
  · exfalso
    apply hcent (phiR u') (phiR_mem u') (by
      rw [← map_pow]
      have : u' ^ 2 = 1 := Subtype.ext hu2
      rw [this, map_one]) h1
    have hsub : F' ≤ Subgroup.centralizer ({phiR u'} : Set (Equiv.Perm (Fin 64))) ⊓ R := by
      refine le_inf ?_ hle
      rintro _ ⟨w, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, MonoidHom.comp_apply, ← map_mul, ← map_mul]
      have hwF : ((w : ↥(invE 1)) : Equiv.Perm (Fin 1782)) ∈ F := Subgroup.mem_subgroupOf.1 w.2
      have hcomm : ((F.subgroupOf (invE 1)).subtype w) * u' = u' * (F.subgroupOf (invE 1)).subtype w :=
        Subtype.ext (huF _ hwF)
      rw [hcomm]
    have := Subgroup.card_dvd_of_le hsub
    rwa [hc, h27] at this

theorem mem_invE_one {g : Equiv.Perm (Fin 1782)} (hg : g ∈ suzM) (hc : g * suzInv 1 = suzInv 1 * g) :
    g ∈ invE 1 := by
  rw [invE_eq_centM (by norm_num : 1 < 4)]
  exact ⟨Subgroup.mem_centralizer_singleton_iff.2 hc, hg⟩

set_option maxRecDepth 100000 in
theorem twoLocalBound27_suzM : TwoLocalBound27 ↥suzM := by
  set a0 : ↥suzM := ⟨suzInv 0, suzInv_mem_suzM (by norm_num)⟩ with ha0
  set a1 : ↥suzM := ⟨suzInv 1, suzInv_mem_suzM (by norm_num)⟩ with ha1
  have hconj : ∀ t : ↥suzM, orderOf t = 2 → IsConj a0 t ∨ IsConj a1 t := by
    intro t ht
    have ht' : orderOf (t : Equiv.Perm (Fin 1782)) = 2 := by rw [Subgroup.orderOf_coe]; exact ht
    rcases suzM_conj_cases t.2 ht' with ⟨m, hm, hmt⟩ | ⟨m, hm, hmt⟩
    · exact Or.inl (isConj_iff.2 ⟨⟨m, hm⟩, Subtype.ext hmt.symm⟩)
    · exact Or.inr (isConj_iff.2 ⟨⟨m, hm⟩, Subtype.ext hmt.symm⟩)
  have hC0 : Nat.card (Subgroup.centralizer ({a0} : Set ↥suzM)) = 161280 :=
    card_centralizer_suzInv (i := 0) (by norm_num)
  have d0a : ∀ F : Subgroup ↥suzM, F ≤ Subgroup.centralizer ({a0} : Set ↥suzM) →
      IsElemAbelian 3 F → Nat.card F < 27 := fun F hF hE =>
    card_lt_27_of_dvd (n := 161280) (isPGroup_of_elemAbelian3 hE)
      (by rw [← hC0]; exact Subgroup.card_dvd_of_le hF)
      (by norm_num)
  have himg : ∀ F : Subgroup ↥suzM, F ≤ Subgroup.centralizer ({a1} : Set ↥suzM) →
      IsElemAbelian 3 F → (suzM.subtype.comp F.subtype).range ≤ invE 1 ∧
        IsElemAbelian 3 (suzM.subtype.comp F.subtype).range ∧
        Nat.card (suzM.subtype.comp F.subtype).range = Nat.card F := by
    intro F hF hE
    refine ⟨?_, elemAbelian_range hE _, ?_⟩
    · rintro _ ⟨f, rfl⟩
      have hc := Subgroup.mem_centralizer_singleton_iff.1 (hF f.2)
      exact mem_invE_one ((f : ↥suzM)).2 (congrArg Subtype.val hc)
    · have hinj : Function.Injective (suzM.subtype.comp F.subtype) :=
        suzM.subtype_injective.comp F.subtype_injective
      exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  have d1a : ∀ F : Subgroup ↥suzM, F ≤ Subgroup.centralizer ({a1} : Set ↥suzM) →
      IsElemAbelian 3 F → Nat.card F ≤ 3 ^ 3 := by
    intro F hF hE
    obtain ⟨h1, h2, h3⟩ := himg F hF hE
    rw [← h3]
    exact card_le_27_of_le_invE h1 h2
  have d1b : ∀ F : Subgroup ↥suzM, F ≤ Subgroup.centralizer ({a1} : Set ↥suzM) →
      IsElemAbelian 3 F → Nat.card F = 3 ^ 3 → ∀ u : ↥suzM, orderOf u = 2 →
        u ∈ Subgroup.centralizer (F : Set ↥suzM) → u * a1 = a1 * u → u = a1 := by
    intro F hF hE h27 u hu huF hua
    obtain ⟨h1, h2, h3⟩ := himg F hF hE
    have hu1 : (u : Equiv.Perm (Fin 1782)) ∈ invE 1 :=
      mem_invE_one u.2 (congrArg Subtype.val hua)
    have hu2 : (u : Equiv.Perm (Fin 1782)) ^ 2 = 1 := by
      have := pow_orderOf_eq_one u
      rw [hu] at this
      exact congrArg Subtype.val this
    have huF' : ∀ f ∈ (suzM.subtype.comp F.subtype).range,
        f * (u : Equiv.Perm (Fin 1782)) = (u : Equiv.Perm (Fin 1782)) * f := by
      rintro _ ⟨f, rfl⟩
      exact congrArg Subtype.val ((Subgroup.mem_centralizer_iff.1 huF) f f.2)
    rcases eq_t1_of_centralizes h1 h2 (by rw [h3, h27]; norm_num) hu1 hu2 huF' with h | h
    · exfalso
      have : u = 1 := Subtype.ext h
      rw [this, orderOf_one] at hu
      exact absurd hu (by norm_num)
    · exact Subtype.ext h
  intro R₀ E hR hR2 hEN hE
  refine card_le_of_involution_data (fun t ht => ?_) (fun t ht => ?_) R₀ E hR hR2 hEN hE
  · rcases hconj t ht with h | h
    · exact (involution_data_of_conj (fun F hF hE => (d0a F hF hE).le)
        (fun F hF hE h27 => absurd h27 (d0a F hF hE).ne) h).1
    · exact (involution_data_of_conj d1a d1b h).1
  · rcases hconj t ht with h | h
    · exact (involution_data_of_conj (fun F hF hE => (d0a F hF hE).le)
        (fun F hF hE h27 => absurd h27 (d0a F hF hE).ne) h).2
    · exact (involution_data_of_conj d1a d1b h).2

set_option maxRecDepth 100000 in
theorem i1016SuzFact_holds : I1016SuzFact := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Suz
  have φ₁ : K ≃* CFSG.Blueprint.NativeSporadic.Carrier .Suz := e.trans b.symm
  have hN : TwoLocalBound27 CFSG.Blueprint.NativeSporadic.Suz := by
    have hS := twoLocalBound27_suzM
    refine twoLocalBound27_of_mulEquiv (G := CFSG.Blueprint.NativeSporadic.Suz) (H := ↥suzM) ?_ hS
    exact suzEquivM
  have hC : TwoLocalBound27 (CFSG.Blueprint.NativeSporadic.Carrier .Suz) := by
    unfold CFSG.Blueprint.NativeSporadic.Carrier
    exact hN
  have hK : TwoLocalBound27 K := twoLocalBound27_of_mulEquiv φ₁ hC
  exact CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le Nat.prime_three
    fun R₀ E hR hR2 hEN hE => hK R₀ E hR hR2 hEN hE

end CFSG.LocalAnalysis.GLTheoremA.H1017

end
