module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KBlkStatement
import CFSG.Goldschmidt.Steps.G310Basic
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L617
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.Steps
public import CFSG.LocalAnalysis.RankThreeTheoremC.D2LocalCGT3

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC (IsTwoInvariantIn IsMaxTwoInvariantIn Prop614Pair)

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M : Subgroup G} {x z : G}

theorem normalizer_le_normalizer_pCoreOf' (L : Subgroup G) :
    normalizer (L : Set G) ≤ normalizer (pCoreOf 2 L : Set G) := by
  have key : ∀ {g : G}, g ∈ normalizer (L : Set G) → ∀ {y : G}, y ∈ pCoreOf 2 L →
      g * y * g⁻¹ ∈ pCoreOf 2 L := by
    intro g hg y hy
    let φ : ↥L ≃* ↥L :=
      ((MulAut.conj g).subgroupMap L).trans
        (MulEquiv.subgroupCongr (Subgroup.mem_normalizer_iff_map_conj_eq.mp hg))
    obtain ⟨y, hy, rfl⟩ := hy
    have hfix := (inferInstance : (CFSG.pCore 2 ↥L).Characteristic).fixed φ
    have hy' : φ y ∈ CFSG.pCore 2 ↥L := by
      have : y ∈ (CFSG.pCore 2 ↥L).comap φ.toMonoidHom := by rw [hfix]; exact hy
      exact Subgroup.mem_comap.mp this
    exact ⟨φ y, hy', rfl⟩
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key hg hy, fun hy => ?_⟩
  have := key (Subgroup.inv_mem _ hg) hy
  simpa [mul_assoc] using this

theorem pCoreOf_le_of_isSylowTwoOf {N S : Subgroup G} (hS : CFSG.QuasithinUnique.IsSylowTwoOf S N) :
    pCoreOf 2 N ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSN, hS2, hSi⟩ := hS
  let P2 : Sylow 2 ↥N := (hS2.comap_subtype : IsPGroup 2 (S.subgroupOf N)).toSylow hSi
  have h1 : CFSG.pCore 2 ↥N ≤ (P2 : Subgroup ↥N) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥N)).le_sylow_of_normal P2
  have h2 : (CFSG.pCore 2 ↥N).map N.subtype ≤ (S.subgroupOf N).map N.subtype :=
    Subgroup.map_mono h1
  rwa [Subgroup.map_subgroupOf_eq_of_le hSN] at h2

theorem stepL617_of_kfact' (hB : KFactBlocksInSylowCentralizerQS)
    (hA3 : StepL617PrimeTop) : StepL617 := by
  intro G _ _ p P M x z hS hx hz H S hopt
  have hprime := hS.prime
  haveI : Fact p.Prime := ⟨hprime⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpl := plane_of_central hS hx hz
  have hB3 : IsPGroup p (zpowers x ⊔ zpowers z : Subgroup G) :=
    IsPGroup.of_card (n := 2) hpl.card_eq
  have hHtop : H ≠ ⊤ := isTwoLocal_ne_top hS hopt.ext.pair.isTwoLocal
  have hBH : zpowers x ⊔ zpowers z ≤ H := hopt.ext.pair.le
  have hSHM : S ≤ H ⊓ M := hopt.ext.pair.isMax.1.1
  have hSH : S ≤ H := hSHM.trans inf_le_left
  have hSM : S ≤ M := hSHM.trans inf_le_right
  obtain ⟨⟨-, hS2, hBS⟩, hSmax⟩ := hopt.maxInv
  have hOH : GLBPrimeCore p H ≤ H := CFSG.AGLEmbedding.glbPrimeCore_le p H
  have hHO : H ≤ normalizer (GLBPrimeCore p H : Set G) :=
    CFSG.AGLEmbedding.le_normalizer_glbPrimeCore p H
  have hOcop : Nat.Coprime p (Nat.card (GLBPrimeCore p H)) :=
    CFSG.AGLEmbedding.glbPrimeCore_coprime p H
  suffices hNM : (GLBPrimeCore p H ⊔ S) ≤ M from le_sup_left.trans hNM
  by_contra hNM
  set N : Subgroup G := GLBPrimeCore p H ⊔ S with hN
  have hNH : N ≤ H := sup_le hOH hSH
  have hNtop : N ≠ ⊤ := fun h => hHtop (top_le_iff.mp (h ▸ hNH))
  have hNp : ¬ p ∣ Nat.card N :=
    not_dvd_card_sup hprime hS.ne_two hOH hSH hHO hOcop hS2
  have hKN : CFSG.Open.IsKGroup ↥N :=
    CFSG.AGLEmbedding.catalogSimpleSections_iff_isKGroup.mp
      (CFSG.AGLEmbedding.catalogSimpleSections_of_isKProper hS.toGlobal.d1Global.kProper N hNtop)
  have hBN : zpowers x ⊔ zpowers z ≤ normalizer (N : Set G) := fun b hb =>
    mem_normalizer_sup (hHO (hBH hb)) (hBS hb)
  have hSsylow : CFSG.QuasithinUnique.IsSylowTwoOf S N := by
    obtain ⟨S₁, hS₁, hSS₁, hBS₁⟩ := CFSG.Goldschmidt.G310.exists_invariant_sylow_containing
      hprime Nat.prime_two hB3 hNp hBN le_sup_right hS2 hBS
    have hS₁S : S₁ = S := hSmax S₁ ⟨hS₁.1.trans hNH, hS₁.2.1, hBS₁⟩ hSS₁
    rw [hS₁S] at hS₁
    obtain ⟨P2, hP2⟩ := CFSG.Goldschmidt.G310.exists_sylow_of_fusionIsSylowIn hS₁
    have hsub : S.subgroupOf N = (P2 : Subgroup N) := by
      rw [← hP2]
      exact Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    exact ⟨hS₁.1, hS2, by have h := P2.not_dvd_index; rwa [← hsub] at h⟩
  have hchar : CFSG.QuasithinUnique.CharTwo N := by
    have hH := hS.toGlobal.d1Global.charTwo H hopt.ext.pair.isTwoLocal
    have hQ := pCoreOf_le_pCoreOf hNH (hopt.core_le.trans le_sup_right)
    intro g hg
    obtain ⟨hgN, hgC⟩ := Subgroup.mem_inf.mp hg
    exact hQ (hH (Subgroup.mem_inf.mpr ⟨hNH hgN, Subgroup.centralizer_le hQ hgC⟩))
  have hcgs : CFSG.Quasithin.cgsIn N S ≤ M := by
    refine iSup_le fun C => iSup_le fun hCS => iSup_le fun hC0 => iSup_le fun hCc => ?_
    exact inf_le_right.trans (hopt.char_le C hCS hC0 hCc)
  have hcore_le : pCoreOf 2 H ≤ pCoreOf 2 N :=
    pCoreOf_le_pCoreOf hNH (hopt.core_le.trans le_sup_right)
  have hSN : S ≤ N := le_sup_right
  have hN2S : pCoreOf 2 N ≤ S := pCoreOf_le_of_isSylowTwoOf hSsylow
  have hBN2 : S ⊔ (zpowers x ⊔ zpowers z) ≤ normalizer (pCoreOf 2 N : Set G) :=
    sup_le (hSN.trans (localGroup_le_normalizer_pCoreOf 2 N))
      (fun b hb => normalizer_le_normalizer_pCoreOf' N (hBN hb))
  by_cases hlt : pCoreOf 2 H < pCoreOf 2 N
  · exact hNM ((localGroup_le_normalizer_pCoreOf 2 N).trans
      (hopt.norm_le (pCoreOf 2 N) hlt hN2S hBN2))
  have hEq : pCoreOf 2 N = pCoreOf 2 H := (eq_of_le_of_not_lt hcore_le hlt).symm
  obtain ⟨Y, hY, hYM⟩ := CFSG.CGT.PushingUpLit.AschbacherLocalFactorization.relative
    CFSG.LocalAnalysis.RankThreeTheoremC.aschbacherLocalFactorization_proved
    (CFSG.AGLEmbedding.LocalCGT.kProper_of_isKGroup hKN)
    (CFSG.AGLEmbedding.LocalCGT.isCharacteristicP_of_charTwo hchar)
    (CFSG.AGLEmbedding.LocalCGT.isSylowOf_of_isSylowTwoOf hSsylow)
    ((CFSG.AGLEmbedding.LocalCGT.centralizer_inf_le_cgsIn hS2 hopt.ext.pair.ne_bot).trans hcgs)
    (fun B hB0 hBS' hBc =>
      (CFSG.AGLEmbedding.LocalCGT.normalizer_inf_le_cgsIn B hB0 hBS' hBc).trans hcgs) hNM
  have hzN : z ∈ normalizer (N : Set G) := hBN (mem_sup_right (mem_zpowers z))
  have hzS : z ∈ normalizer (S : Set G) := hBS (mem_sup_right (mem_zpowers z))
  by_cases hq : CFSG.IsQuasisimple (↥Y ⧸ CFSG.pCore 2 ↥Y) ∨ z ∈ normalizer (Y : Set G)
  · exact hYM ((hB G p N S z hprime hS.p_ge hKN hchar hSsylow hNp hzN hzS hz.pow_eq_one Y hY
      hq).trans (sup_le hSM (inf_le_right.trans (centralizer_singleton_le hS hz))))
  · push Not at hq
    exact hYM (hA3 G p P M x z hS hx hz H S hopt hEq Y hY hq.1 hq.2)


end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty
