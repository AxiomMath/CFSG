module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Fi24Side
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H1017Facts
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAFi24Inv
public import CFSG.LocalAnalysis.EvenSporadicStandard.Solomon78.Fi24RowEdge
public import CFSG.Sporadic.Fi22.InvFix
public import Certificates.Certificate1007
public import Certificates.Certificate431005
public import CFSG.Sporadic.Bridge.Catalogue
public import Certificates.Certificate431006
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
public import CFSG.LargeExtraspecial.BridgeSetting
public import CFSG.LargeExtraspecial.S3Asch
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
public import CFSG.Sporadic.Co1Block.Iota
public import CFSG.Sporadic.Co2Smith.Defs
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.Recognition.LyonsSimsEndgame
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Sporadic.Schreier.LyFixedSet
public import CFSG.YGroups.DCE.B433Check
public import Certificates.Certificate2323
public import Certificates.Certificate9124

public section

namespace CFSG.LocalAnalysis.GLTheoremA.H1017

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native
open CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24RankNative CFSG.LocalAnalysis.GLTheoremA.H1017.Fi24Side

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem involution_data_of_hom {Y X' : Type} [Group Y] [Group X'] {k : ℕ} {t : Y}
    (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (Φ : Subgroup.centralizer ({t} : Set Y) →* X')
    (hker : ∀ c, Φ c = 1 → (c : Y) = 1 ∨ (c : Y) = t)
    (ha : ∀ E : Subgroup X', IsElemAbelian 3 E → Nat.card E ≤ 3 ^ k)
    (hb : ∀ E : Subgroup X', IsElemAbelian 3 E → Nat.card E = 3 ^ k → ∀ σ : X', σ * σ = 1 →
      (∀ e ∈ E, σ * e = e * σ) → σ = 1) :
    (∀ F : Subgroup Y, F ≤ Subgroup.centralizer ({t} : Set Y) → IsElemAbelian 3 F →
      Nat.card F ≤ 3 ^ k) ∧
    (∀ F : Subgroup Y, F ≤ Subgroup.centralizer ({t} : Set Y) → IsElemAbelian 3 F →
      Nat.card F = 3 ^ k → ∀ u : Y, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set Y) →
        u * t = t * u → u = t) := by
  have himg : ∀ F : Subgroup Y, F ≤ Subgroup.centralizer ({t} : Set Y) → IsElemAbelian 3 F →
      IsElemAbelian 3 ((F.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map Φ) ∧
        Nat.card ((F.subgroupOf (Subgroup.centralizer ({t} : Set Y))).map Φ) = Nat.card F := by
    intro F hF hE
    have hE' := isElemAbelian_subgroupOf hE (Subgroup.centralizer ({t} : Set Y))
    refine ⟨isElemAbelian_map' Φ hE', ?_⟩
    have hinj : Function.Injective
        (Φ.comp (F.subgroupOf (Subgroup.centralizer ({t} : Set Y))).subtype) := by
      rw [injective_iff_map_eq_one]
      intro x hx
      have hx3 : ((x : Subgroup.centralizer ({t} : Set Y)) : Y) ^ 3 = 1 :=
        hE.2 _ (Subgroup.mem_subgroupOf.1 x.2)
      rcases hker x hx with h | h
      · exact Subtype.ext (Subtype.ext h)
      · exfalso
        rw [h, pow_succ, pow_two, ht2, one_mul] at hx3
        exact ht1 hx3
    have e1 := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [MonoidHom.range_comp, Subgroup.range_subtype] at e1
    rw [← e1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hF).toEquiv
  refine ⟨fun F hF hE => ?_, fun F hF hE hcard u hu huF hut => ?_⟩
  · obtain ⟨h1, h2⟩ := himg F hF hE
    exact h2 ▸ ha _ h1
  · obtain ⟨h1, h2⟩ := himg F hF hE
    have huC : u ∈ Subgroup.centralizer ({t} : Set Y) :=
      Subgroup.mem_centralizer_singleton_iff.2 hut
    let u' : Subgroup.centralizer ({t} : Set Y) := ⟨u, huC⟩
    have hu2 : u * u = 1 := by rw [← pow_two, ← hu]; exact pow_orderOf_eq_one u
    have hσ := hb _ h1 (h2.trans hcard) (Φ u') (by rw [← map_mul]; exact
      (congrArg Φ (Subtype.ext hu2 : u' * u' = 1)).trans (map_one Φ)) (by
        rintro _ ⟨f, hf, rfl⟩
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.1 huF _ (Subgroup.mem_subgroupOf.1 hf)).symm)
    rcases hker u' hσ with h | h
    · exfalso
      have : orderOf u = 1 := by rw [show u = 1 from h, orderOf_one]
      omega
    · exact h

theorem getElem!_append_left' {α : Type*} [Inhabited α] {a b : Array α} {k : ℕ}
    (hk : k < a.size) : (a ++ b)[k]! = a[k]! := by
  rw [getElem!_pos (a ++ b) k (by simp; omega), getElem!_pos a k hk, Array.getElem_append_left hk]

theorem getElem!_append_right' {α : Type*} [Inhabited α] {a b : Array α} {l : ℕ}
    (hl : l < b.size) : (a ++ b)[a.size + l]! = b[l]! := by
  rw [getElem!_pos (a ++ b) (a.size + l) (by simp; omega), getElem!_pos b l hl,
    Array.getElem_append_right (by omega)]
  simp

section Fi22


theorem fi22Rank_parts :
    sideOK 3510 (fi22RA ()) (fi22RG ()) (fi22RMu ()) fi22RP0 81 = true ∧
      nonabOK (fi22RMu ()) 81 = true ∧ fi22TauOK () = true ∧ fi22PosOK () = true := by
  have h := Certificates.certificate431005
  rw [fi22RankOK, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem fi22_hside : sideOK 3510 (fi22RA ()) (fi22RG ()) (fi22RMu ()) fi22RP0 81 = true :=
  fi22Rank_parts.1

theorem fi22_sizes : (fi22RA ()).size = 5 ∧ (fi22RG ()).size = 2 := by
  have h := (sideOK_parts fi22_hside).1
  unfold permsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩

theorem orb_eq : CFSG.Sporadic.Fi22.orb = CFSG.Sporadic.Fi22.Native.orbitData () := rfl

theorem tabOf_ap (c x : Fin 3510) :
    CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.Fi22.Native.tabOf CFSG.Sporadic.Fi22.orb c) x =
      (CFSG.Sporadic.Fi22.tauIdx c x : ℕ) := by
  have h1 := CFSG.Sporadic.Fi22.rep_tabOf c.2 x x.2
  have h2 := CFSG.Sporadic.Fi22.idx_perm (CFSG.Sporadic.Fi22.tauIdx ⟨c, c.2⟩) x.2
  simp only [Fin.eta] at h1 h2
  exact h1.trans h2

theorem mem_tauAut_of_base {σ : Equiv.Perm (Fin 3510)}
    (h : ∀ j < 6, CFSG.Sporadic.Fi22.TauCompatAt σ (CFSG.Sporadic.Fi22.nfpPt j)) :
    σ ∈ CFSG.Sporadic.Fi22.tauAut := by
  open CFSG.Sporadic.Fi22 CFSG.Sporadic.Fi22.Native CFSG.Sporadic.Th.Native in
  have hT := nfpTreeFacts (i := 6) (by norm_num) (by norm_num)
  have hg : ∀ g ∈ CFSG.Perm.lettersGroup (Array.range 6) nfpG, ∀ x,
      TauCompatAt σ x → TauCompatAt σ (g x) := by
    intro g hgm
    unfold CFSG.Perm.lettersGroup at hgm
    induction hgm using Subgroup.closure_induction_left with
    | one => intro x hx; exact hx
    | mul_left y hy z _ ih =>
      obtain ⟨l, hl, rfl⟩ := hy
      rw [Array.mem_range] at hl
      intro x hx
      rw [Equiv.Perm.mul_apply]
      exact tauCompatAt_tauIdx (h l hl) (ih x hx)
    | inv_mul_cancel y hy z _ ih =>
      obtain ⟨l, hl, rfl⟩ := hy
      rw [Array.mem_range] at hl
      intro x hx
      rw [Equiv.Perm.mul_apply, tauIdx_inv]
      exact tauCompatAt_tauIdx (h l hl) (ih x hx)
  refine CFSG.Sporadic.Fi22.mem_tauAut.2 fun v => ?_
  obtain ⟨k, hk, rfl⟩ := mem_nfpTree_six v
  rw [nfpTree_pt (by norm_num) (by norm_num) hk]
  exact hg _ (hT.treeG_mem hk) _ (h 0 (by norm_num))

theorem fi22_tau_base {k : ℕ} (hk : k < 7)
    (hinv : isInvA 3510 (fi22RA () ++ fi22RG ())[k]! (invCand 3510 (fi22RA () ++ fi22RG ())[k]!) =
      true) {j : ℕ} (hj : j < 6) :
    CFSG.Sporadic.Fi22.TauCompatAt (permOfArr 3510 (fi22RA () ++ fi22RG ())[k]!)
      (CFSG.Sporadic.Fi22.nfpPt j) := by
  have hr := rep_permOfArr hinv
  set σ := permOfArr 3510 (fi22RA () ++ fi22RG ())[k]!
  have h := fi22Rank_parts.2.2.1
  simp only [fi22TauOK] at h
  have hj' := allLt_iff.1 (allLt_iff.1 h k hk) j hj
  rw [Bool.and_eq_true, decide_eq_true_eq] at hj'
  obtain ⟨-, hall⟩ := hj'
  rw [← orb_eq] at hall
  have hb := CFSG.Sporadic.Fi22.nfpPt_val hj
  unfold CFSG.Sporadic.Fi22.TauCompatAt
  refine Equiv.ext fun x => Fin.ext ?_
  have h1 := beq_iff_eq.1 (allLt_iff.1 hall x x.2)
  have hG : ∀ y : Fin 3510, CFSG.Sporadic.Th.Native.ap (CFSG.Sporadic.Fi22.Native.tabOf
      CFSG.Sporadic.Fi22.orb CFSG.Sporadic.Fi22.Native.nfpBase[j]!) y =
        (CFSG.Sporadic.Fi22.tauIdx (CFSG.Sporadic.Fi22.nfpPt j) y : ℕ) := fun y => by
    have e : CFSG.Sporadic.Fi22.nfpPt j =
        ⟨CFSG.Sporadic.Fi22.Native.nfpBase[j]!, CFSG.Sporadic.Fi22.nfpBase_lt hj⟩ :=
      Fin.ext hb
    rw [e]
    exact tabOf_ap ⟨CFSG.Sporadic.Fi22.Native.nfpBase[j]!, CFSG.Sporadic.Fi22.nfpBase_lt hj⟩ y
  have hsb : ((fi22RA () ++ fi22RG ())[k]!)[CFSG.Sporadic.Fi22.Native.nfpBase[j]!]! =
      (σ (CFSG.Sporadic.Fi22.nfpPt j) : ℕ) := by
    rw [← hb]
    exact hr.1 _
  rw [hr.2 x, hG, hr.1, hsb] at h1
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, h1, tabOf_ap]

theorem fi22_A_mem {k : ℕ} (hk : k < 5) : permOfArr 3510 (fi22RA ())[k]! ∈ CFSG.Sporadic.Fi22.tauAut := by
  have hinv := (permsOK_parts (sideOK_parts fi22_hside).1).1 k hk
  have e : (fi22RA () ++ fi22RG ())[k]! = (fi22RA ())[k]! :=
    getElem!_append_left' (by rw [fi22_sizes.1]; exact hk)
  have hinv' : isInvA 3510 (fi22RA () ++ fi22RG ())[k]! (invCand 3510 (fi22RA () ++ fi22RG ())[k]!) =
      true := by rw [e]; exact hinv
  have := mem_tauAut_of_base fun j hj => fi22_tau_base (k := k) (by omega) hinv' hj
  rwa [e] at this

theorem fi22_G_mem {l : ℕ} (hl : l < 2) : permOfArr 3510 (fi22RG ())[l]! ∈ CFSG.Sporadic.Fi22.tauAut := by
  have hinv := (permsOK_parts (sideOK_parts fi22_hside).1).2.1 l hl
  have e : (fi22RA () ++ fi22RG ())[5 + l]! = (fi22RG ())[l]! := by
    have := getElem!_append_right' (a := fi22RA ()) (b := fi22RG ()) (l := l)
      (by rw [fi22_sizes.2]; exact hl)
    rwa [fi22_sizes.1] at this
  have hinv' : isInvA 3510 (fi22RA () ++ fi22RG ())[5 + l]!
      (invCand 3510 (fi22RA () ++ fi22RG ())[5 + l]!) = true := by rw [e]; exact hinv
  have := mem_tauAut_of_base fun j hj => fi22_tau_base (k := 5 + l) (by omega) hinv' hj
  rwa [e] at this

theorem fi22_hfix : ∀ σ ∈ CFSG.Sporadic.Fi22.tauAut, σ * σ = 1 →
    (∀ i < 243, σ * iotaP 3510 (fi22RA ()) i = iotaP 3510 (fi22RA ()) i * σ) → σ = 1 := by
  intro σ hσ hσ2 hσA
  have h := fi22Rank_parts.2.2.2
  simp only [fi22PosOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hsize, hq⟩ := h
  have hq' := parLt_spec (by norm_num) hq
  have key : ∀ c : ℕ, ∀ q : Fin 3510, (fi22RPos ())[q.val]! ≤ c → σ q = q := by
    intro c
    induction c using Nat.strong_induction_on with
    | _ c ih =>
      intro q hqc
      have hqq := hq' q q.2
      split_ifs at hqq with h0
      · exact apply_eq_of_uniqAt fi22_hside q.2 hqq hσA hσ2
      · simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hqq
        obtain ⟨⟨⟨⟨⟨⟨-, hz⟩, hx⟩, hy⟩, hpx⟩, hpy⟩, hzq⟩ := hqq
        set c' := (fi22RPos ())[q.val]! - 1 with hc'
        have hc'c : c' < c := by omega
        set x : Fin 3510 := ⟨(fi22RChain ())[3 * c' + 1]!, hx⟩
        set y : Fin 3510 := ⟨(fi22RChain ())[3 * c' + 2]!, hy⟩
        have hσx : σ x = x := ih c' hc'c x hpx
        have hσy : σ y = y := ih c' hc'c y hpy
        have hqxy : q = CFSG.Sporadic.Fi22.tauIdx x y := by
          apply Fin.ext
          rw [← tabOf_ap x y, orb_eq]
          exact hzq.symm
        rw [hqxy, CFSG.Sporadic.Fi22.tauAut_apply hσ, hσx, hσy]
  exact Equiv.ext fun q => key _ q le_rfl

theorem fi22_side :
    (∀ E : Subgroup CFSG.Sporadic.Fi22.tauAut, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 5) ∧
      (∀ E : Subgroup CFSG.Sporadic.Fi22.tauAut, IsElemAbelian 3 E → Nat.card E = 3 ^ 5 →
        ∀ σ : CFSG.Sporadic.Fi22.tauAut, σ * σ = 1 → (∀ e ∈ E, σ * e = e * σ) → σ = 1) :=
  side_facts (m := 4) CFSG.Sporadic.Fi22.tauAut fi22_hside (fun k hk => fi22_A_mem hk)
    (fun l hl => fi22_G_mem hl) (by norm_num)
    (by rw [CFSG.Sporadic.Fi22.card_tauAut]; norm_num) (Or.inr ⟨rfl, fi22Rank_parts.2.1⟩)
    fi22_hfix

end Fi22


section K

open CFSG.Sporadic.FischerOddCore CFSG.Certificates.Native


theorem kRank_parts :
    sideOK 504 (kRA ()) (kRG ()) (kRMu ()) kRP0 9 = true ∧ kMemOK () = true ∧ kUniqOK () = true := by
  have h := Certificates.certificate431006
  rw [kRankOK, Bool.and_eq_true, Bool.and_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem k_hside : sideOK 504 (kRA ()) (kRG ()) (kRMu ()) kRP0 9 = true := kRank_parts.1

theorem k_sizes : (kRA ()).size = 5 ∧ (kRG ()).size = 2 := by
  have h := (sideOK_parts k_hside).1
  unfold permsOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2⟩

theorem k_mem {k : ℕ} (hk : k < 7) (hinv : isInvA 504 (kRA () ++ kRG ())[k]!
    (invCand 504 (kRA () ++ kRG ())[k]!) = true) :
    permOfArr 504 (kRA () ++ kRG ())[k]! ∈ fi24K := by
  have h := kRank_parts.2.1
  simp only [kMemOK] at h
  exact mem_fi24K_of_siftA (rep_permOfArr hinv).1 (allLt_iff.1 h k hk)

theorem k_A_mem {k : ℕ} (hk : k < 5) : permOfArr 504 (kRA ())[k]! ∈ fi24K := by
  have hinv := (permsOK_parts (sideOK_parts k_hside).1).1 k hk
  have e : (kRA () ++ kRG ())[k]! = (kRA ())[k]! :=
    getElem!_append_left' (by rw [k_sizes.1]; exact hk)
  have := k_mem (k := k) (by omega) (by rw [e]; exact hinv)
  rwa [e] at this

theorem k_G_mem {l : ℕ} (hl : l < 2) : permOfArr 504 (kRG ())[l]! ∈ fi24K := by
  have hinv := (permsOK_parts (sideOK_parts k_hside).1).2.1 l hl
  have e : (kRA () ++ kRG ())[5 + l]! = (kRG ())[l]! := by
    have := getElem!_append_right' (a := kRA ()) (b := kRG ()) (l := l)
      (by rw [k_sizes.2]; exact hl)
    rwa [k_sizes.1] at this
  have := k_mem (k := 5 + l) (by omega) (by rw [e]; exact hinv)
  rwa [e] at this

theorem k_hfix : ∀ σ ∈ fi24K, σ * σ = 1 →
    (∀ i < 243, σ * iotaP 504 (kRA ()) i = iotaP 504 (kRA ()) i * σ) → σ = 1 := by
  intro σ _ hσ2 hσA
  have h := kRank_parts.2.2
  simp only [kUniqOK] at h
  exact Equiv.ext fun q => apply_eq_of_uniqAt k_hside q.2 (allLt_iff.1 h q q.2) hσA hσ2

theorem k_side :
    (∀ E : Subgroup fi24K, IsElemAbelian 3 E → Nat.card E ≤ 3 ^ 5) ∧
      (∀ E : Subgroup fi24K, IsElemAbelian 3 E → Nat.card E = 3 ^ 5 →
        ∀ σ : fi24K, σ * σ = 1 → (∀ e ∈ E, σ * e = e * σ) → σ = 1) :=
  side_facts (m := 2) fi24K k_hside (fun k hk => k_A_mem hk) (fun l hl => k_G_mem hl)
    (by norm_num) (by rw [card_fi24K]; norm_num) (Or.inl (by norm_num)) k_hfix

end K

section R2

open CFSG.Sporadic.FischerOddCore CFSG.Sporadic.Fi24

theorem fi24R2_mul_self :
    fi24R2 * fi24R2 = 1 := by
  have h : CFSG.Sporadic.Fi24.fi23EquivM.symm fi23U3 * CFSG.Sporadic.Fi24.fi23EquivM.symm fi23U3 = 1 := by
    rw [← map_mul, ← pow_two, fi23U3_facts.1, map_one]
  unfold fi24R2
  rw [← Subgroup.coe_mul, h, OneMemClass.coe_one]

theorem exists_r2_hom :
    ∃ Φ : fi24C →* fi24K, ∀ c, Φ c = 1 → (c : J) = 1 ∨ (c : J) = fi24R2 := by
  obtain ⟨ρ, hρ⟩ := exists_famHom ((MulAction.toPermHom J (Fin 306936)).comp fi24C.subtype)
    fi24FPt_injective fi24C_inv
  have hρ' : ∀ (c : fi24C) j, fi24FPt (ρ c j) = (c : J) • fi24FPt j := hρ
  have hρa : ρ ⟨fi24Ca, fi24Ca_mem⟩ = fi24Sa :=
    Equiv.ext fun j => fi24FPt_injective (by rw [hρ']; exact fi24Ca_smul j)
  have hρb : ρ ⟨fi24Cb, fi24Cb_mem⟩ = fi24Sb :=
    Equiv.ext fun j => fi24FPt_injective (by rw [hρ']; exact fi24Cb_smul j)
  have hKle : fi24K ≤ ρ.range := by
    rw [fi24K_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hρa⟩
    · exact ⟨_, hρb⟩
  have hr2 : (⟨fi24R2, fi24R2_mem_C⟩ : fi24C) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    exact Equiv.ext fun j => fi24FPt_injective (by
      rw [hρ', Equiv.Perm.one_apply]
      exact fi24R2_smul_fi24FPt j)
  have hker2 : 2 ≤ Nat.card ρ.ker := by
    have hne : ρ.ker ≠ ⊥ := fun h => by
      rw [h, Subgroup.mem_bot] at hr2
      exact fi24R2_ne_one (by simpa using congrArg (Subtype.val : fi24C → J) hr2)
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hcard := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at hcard
  have hrange : Nat.card fi24K ≤ Nat.card ρ.range := Subgroup.card_le_of_le hKle
  rw [card_fi24K] at hrange
  have hC := card_fi24C_le
  have hb : Nat.card ρ.range = 80263249920 := by
    have h2b : 2 * Nat.card ρ.range ≤ Nat.card ρ.ker * Nat.card ρ.range :=
      Nat.mul_le_mul_right _ hker2
    omega
  have ha : Nat.card ρ.ker = 2 := by
    rw [hb] at hcard
    omega
  have hreq : ρ.range = fi24K := (Subgroup.eq_of_le_of_card_ge hKle (by rw [hb, card_fi24K])).symm
  refine ⟨ρ.codRestrict fi24K fun x => hreq ▸ ⟨x, rfl⟩, fun c hc => ?_⟩
  have hc' : c ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    exact congrArg Subtype.val hc
  by_contra hne
  push Not at hne
  have h3 : ({1, ⟨fi24R2, fi24R2_mem_C⟩, c} : Set fi24C) ⊆ ρ.ker := by
    rintro x (rfl | rfl | rfl)
    · exact ρ.ker.one_mem
    · exact hr2
    · exact hc'
  have hne1 : (1 : fi24C) ≠ ⟨fi24R2, fi24R2_mem_C⟩ := fun e =>
    fi24R2_ne_one (congrArg Subtype.val e).symm
  have hne2 : (1 : fi24C) ≠ c := fun e => hne.1 (congrArg Subtype.val e).symm
  have hne3 : (⟨fi24R2, fi24R2_mem_C⟩ : fi24C) ≠ c := fun e => hne.2 (congrArg Subtype.val e).symm
  have hc3 : ({1, ⟨fi24R2, fi24R2_mem_C⟩, c} : Set fi24C).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hne1, hne2]), Set.ncard_pair hne3]
  have h4 := Set.ncard_le_ncard h3 (Set.toFinite _)
  have h5 : (ρ.ker : Set fi24C).ncard = 2 := by rw [← Nat.card_coe_set_eq]; exact ha
  omega

end R2

section TJ

open CFSG.Sporadic CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Sporadic.Fi24
open CFSG.EvenSporadicStandard.Solomon78.Fi24Row (edge_surj edge_hW)

theorem exists_tJ_hom :
    ∃ Φ : Subgroup.centralizer ({tJ} : Set J) →* Fi22.tauAut,
      ∀ c, Φ c = 1 → (c : J) = 1 ∨ (c : J) = tJ := by
  obtain ⟨ψ, hψc, hψt⟩ := edgeLocal_of_localPoints pair_R Fi23.pair_J Fi22.pair_D
    localPoints_D24 (Fi23.localPoints_D23 CFSG.Fischer.polarFacts) ⟨tR, tR_mem_D24⟩
    ⟨xb, xb_mem_D24⟩ tR_ne_xb tR_xb_comm
  have hsurj := edge_surj ψ hψc hψt Fi22.card_fixed_involution_D edgeSwap_a
  have hker := edgeHomC_ker pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc
    hψt Fi22.center_eq_bot (inf_le_left : CE ≤ _) hsurj (card_CE edgeSwap_a (edge_hW ψ hψc))
    tR_mul_xb_mem_CE
  have hmem : ∀ c : Subgroup.centralizer ({tJ} : Set J),
      (jR.comp (Subgroup.centralizer ({tJ} : Set J)).subtype) c ∈ CE := fun c => by
    rw [← map_centralizer_tJ]
    exact Subgroup.mem_map_of_mem jR c.2
  let ι : Subgroup.centralizer ({tJ} : Set J) →* CE :=
    (jR.comp (Subgroup.centralizer ({tJ} : Set J)).subtype).codRestrict CE hmem
  have hι : ∀ c, ((ι c : CE) : R) = jR c := fun _ => rfl
  refine ⟨Fi22.tauAutEquiv.symm.toMonoidHom.comp ((edgeHomC pair_R Fi22.pair_D tR_mem_D24
    xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt Fi22.center_eq_bot (inf_le_left : CE ≤ _)).comp ι),
    fun c hc => ?_⟩
  have h1 : edgeHomC pair_R Fi22.pair_D tR_mem_D24 xb_mem_D24 tR_ne_xb tR_xb_comm ψ hψc hψt
      Fi22.center_eq_bot (inf_le_left : CE ≤ _) (ι c) = 1 := by
    have := hc
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff] at this
    exact this
  rcases hker (ι c) h1 with h | h
  · left
    apply jR_injective
    rw [← hι, h, map_one]
  · right
    apply jR_injective
    rw [← hι, h, jR_tJ]

end TJ

section Final

open CFSG.Sporadic CFSG.Sporadic.Fi24 CFSG.Sporadic.FischerOddCore
open CFSG.HardMathSupport.Dickson.I271.TabMThreeA

set_option maxRecDepth 100000 in
theorem twoLocalBoundPow_fi24 : TwoLocalBoundPow 5 J := by
  obtain ⟨Φ₁, hΦ₁⟩ := exists_tJ_hom
  have dT := involution_data_of_hom (Y := J) (X' := Fi22.tauAut) (k := 5) (t := tJ) tJ_mul_tJ
    tJ_ne_one Φ₁ hΦ₁ fi22_side.1 fi22_side.2
  obtain ⟨Φ₂, hΦ₂⟩ := exists_r2_hom
  have dR := involution_data_of_hom (Y := J) (X' := fi24K) (k := 5) (t := fi24R2) fi24R2_mul_self
    fi24R2_ne_one Φ₂ hΦ₂ k_side.1 k_side.2
  have hcls := fi24J_involutions.1
  have hdata : ∀ t : J, orderOf t = 2 →
      (∀ F : Subgroup J, F ≤ Subgroup.centralizer ({t} : Set J) → IsElemAbelian 3 F →
        Nat.card F ≤ 3 ^ 5) ∧
      (∀ F : Subgroup J, F ≤ Subgroup.centralizer ({t} : Set J) → IsElemAbelian 3 F →
        Nat.card F = 3 ^ 5 → ∀ u : J, orderOf u = 2 → u ∈ Subgroup.centralizer (F : Set J) →
          u * t = t * u → u = t) := by
    intro t ht
    have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    have ht1 : t ≠ 1 := fun h => by rw [h, orderOf_one] at ht; omega
    rcases hcls t ht2 ht1 with h | h
    · exact involution_data_of_conj_k 5 dT.1 dT.2 h.symm
    · exact involution_data_of_conj_k 5 dR.1 dR.2 h.symm
  intro R E hR hR2 hEN hE
  exact card_le_of_involution_data_k 5 (fun t ht => (hdata t ht).1) (fun t ht => (hdata t ht).2)
    R E hR hR2 hEN hE

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000 in
theorem i1016Fi24Fact_holds :
   I1016Fi24Fact := by
  intro K _ _ hcat
  obtain ⟨i, hi, ⟨e⟩⟩ := hcat
  simp only [S8.sporIs] at hi
  subst hi
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.nonempty_carrier_mulEquiv_group .Fi24Prime
  have f : K ≃* ↥J := (e.trans b.symm).trans fi24EquivJ
  have hK : TwoLocalBoundPow 5 K :=
    @twoLocalBoundPow_of_mulEquiv 5 K ↥J _ (Subgroup.toGroup J) f twoLocalBoundPow_fi24
  exact CFSG.LocalAnalysis.GLTheoremA.glaTwoLocalRank_le_of_card_le Nat.prime_three
    fun R₀ E hR hR2 hEN hE => hK R₀ E hR hR2 hEN hE

end Final

end CFSG.LocalAnalysis.GLTheoremA.H1017
