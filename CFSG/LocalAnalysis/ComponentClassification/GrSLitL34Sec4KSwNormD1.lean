module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4KSwNormB5
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingleTools
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitSingle
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCDiagCover
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitContainmentTransfer
import CFSG.LocalAnalysis.ComponentClassification.FooteLitClassical
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec5Fixed
public import Certificates.Kernel.ThCent.Leaves
import CFSG.LocalAnalysis.ComponentClassification.GSThmBCorollaryC
import CFSG.LocalAnalysis.ComponentClassification.GrSLitFixedHe
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixA
import CFSG.LocalAnalysis.ComponentClassification.GrSLitHeldFixB
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL2Balance
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCClimb
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCMax
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCRankGap
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCSteps
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4CorCTypes
import CFSG.LocalAnalysis.ComponentClassification.GrSLitLocalBalanceHe
import CFSG.LocalAnalysis.ComponentClassification.GrSLitReach39
import CFSG.LocalAnalysis.ComponentClassification.SolAltLitBasic
import CFSG.LocalAnalysis.ComponentClassification.UGSChainRankTwoMaximality

public section

namespace CFSG.ComponentClassification.GrSLit.KSw

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ComponentClassification.UnbalancedGS
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem le_of_commutator_mem_of_cover {L H : Subgroup G} (hLH : L ≤ H)
    (hL : IsPComponent 2 (L.subgroupOf H)) {C : Subgroup G} (hCL : C ≤ L)
    (hcov : L ≤ C ⊔ oddIn L) {J Y : Subgroup G} (hJL : J ≤ normalizer (L : Set G))
    (hJ : ¬ J ≤ coreActionKernel L) (hY : ∀ g ∈ C, ∀ j ∈ J, g⁻¹ * j * g * j⁻¹ ∈ Y)
    (hOY : oddIn L ≤ Y) : L ≤ Y := by
  set S : Set G := {x | ∃ g ∈ C, ∃ j ∈ J, x = g⁻¹ * j * g * j⁻¹} with hS
  set P : Subgroup G := closure S ⊔ oddIn L with hP
  have hON : L ≤ normalizer ((oddIn L : Subgroup G) : Set G) := GrS4.self_le_normalizer_oddIn L
  have hSL : S ⊆ L := by
    rintro x ⟨g, hg, j, hj, rfl⟩
    rw [show g⁻¹ * j * g * j⁻¹ = g⁻¹ * (j * g * j⁻¹) by group]
    exact mul_mem (inv_mem (hCL hg)) ((mem_normalizer_iff.mp (hJL hj) g).mp (hCL hg))
  have hPL : P ≤ L := sup_le ((closure_le L).mpr hSL) (map_subtype_le _)
  have hPY : P ≤ Y := sup_le ((closure_le Y).mpr (by
    rintro x ⟨g, hg, j, hj, rfl⟩
    exact hY g hg j hj)) hOY
  have hCN : C ≤ normalizer (P : Set G) := by
    intro h hh
    refine FooteLit.mem_normalizer_of_map_conj_le ?_
    rw [hP, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rw [MonoidHom.map_closure, closure_le]
      rintro _ ⟨x, ⟨g, hg, j, hj, rfl⟩, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      have h1 : g * h⁻¹ ∈ C := mul_mem hg (inv_mem hh)
      have h2 : h⁻¹ ∈ C := inv_mem hh
      have e : h * (g⁻¹ * j * g * j⁻¹) * h⁻¹ = ((g * h⁻¹)⁻¹ * j * (g * h⁻¹) * j⁻¹) *
          (h⁻¹⁻¹ * j * h⁻¹ * j⁻¹)⁻¹ := by group
      rw [e]
      exact mem_sup_left (mul_mem (subset_closure ⟨_, h1, j, hj, rfl⟩)
        (inv_mem (subset_closure ⟨_, h2, j, hj, rfl⟩)))
    · rintro _ ⟨y, hy, rfl⟩
      exact mem_sup_right ((mem_normalizer_iff.mp (hON (hCL hh)) y).mp hy)
  have hON' : oddIn L ≤ normalizer (P : Set G) := by
    intro o ho
    refine FooteLit.mem_normalizer_of_map_conj_le ?_
    rintro _ ⟨x, hx, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : o * (x * o⁻¹ * x⁻¹) ∈ oddIn L :=
      mul_mem ho ((mem_normalizer_iff.mp (hON (hPL hx)) _).mp (inv_mem ho))
    rw [show o * x * o⁻¹ = (o * (x * o⁻¹ * x⁻¹)) * x by group]
    exact mul_mem (mem_sup_right h1) hx
  have hLN : L ≤ normalizer (P : Set G) := hcov.trans (sup_le hCN hON')
  rcases Single.eq_or_commutator_le_oddIn hLH hL hPL hLN le_sup_right with h | h
  · exact h ▸ hPY
  · exfalso
    apply hJ
    intro j hj
    refine Single.mem_coreActionKernel_of_comm hLH hL (hJL hj) fun g hg k hk => ?_
    obtain ⟨c, hc, o, ho, rfl⟩ := Single.exists_mul_of_mem_sup (hCL.trans hON) (hcov hg)
    have hjo : j * o * j⁻¹ ∈ oddIn L := GrS4.conj_mem_oddIn_of_mem_normalizer (hJL hj) ho
    have hmem : (c * o)⁻¹ * (j * (c * o) * j⁻¹) ∈ P := by
      rw [show (c * o)⁻¹ * (j * (c * o) * j⁻¹) = o⁻¹ * (c⁻¹ * j * c * j⁻¹) * (j * o * j⁻¹) by
        group]
      exact mul_mem (mul_mem (mem_sup_right (inv_mem ho))
        (mem_sup_left (subset_closure ⟨c, hc, j, hj, rfl⟩))) (mem_sup_right hjo)
    exact h (commutator_mem_commutator hk hmem)

theorem mem_coreActionKernel_of_sup {J K K' M : Subgroup G} {s : G} (hJM : J ≤ M)
    (hKM : K ≤ M) (hK'M : K' ≤ M) (hOK : oddIn K ≤ oddIn M) (hOK' : oddIn K' ≤ oddIn M)
    (hJKK : J ≤ K ⊔ K' ⊔ oddIn M) (hsM : s ∈ M) (hsJ : s ∈ normalizer (J : Set G))
    (hsK : s ∈ coreActionKernel K) (hsK' : s ∈ coreActionKernel K') :
    s ∈ coreActionKernel J := by
  set O : Subgroup G := oddIn M with hO
  have hON : ∀ g ∈ M, ∀ o ∈ O, g * o * g⁻¹ ∈ O := fun g hg o ho =>
    (mem_normalizer_iff.mp (GrS4.self_le_normalizer_oddIn M hg) o).mp ho
  let H : Subgroup G :=
    { carrier := {m | m ∈ M ∧ m⁻¹ * s⁻¹ * m * s ∈ O}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨haM, ha⟩ ⟨hbM, hb⟩
        refine ⟨mul_mem haM hbM, ?_⟩
        have h1 : b⁻¹ * (a⁻¹ * s⁻¹ * a * s) * b ∈ O := by
          have h2 := hON b⁻¹ (inv_mem hbM) _ ha
          rwa [inv_inv] at h2
        have h3 : (a * b)⁻¹ * s⁻¹ * (a * b) * s =
            b⁻¹ * (a⁻¹ * s⁻¹ * a * s) * b * (b⁻¹ * s⁻¹ * b * s) := by group
        rw [h3]
        exact mul_mem h1 hb
      inv_mem' := by
        rintro a ⟨haM, ha⟩
        refine ⟨inv_mem haM, ?_⟩
        have h1 := hON a haM _ (inv_mem ha)
        have h2 : a⁻¹⁻¹ * s⁻¹ * a⁻¹ * s = a * (a⁻¹ * s⁻¹ * a * s)⁻¹ * a⁻¹ := by group
        rw [h2]
        exact h1 }
  have hLH : ∀ {L : Subgroup G}, L ≤ M → oddIn L ≤ O → s ∈ coreActionKernel L → L ≤ H :=
    fun hLM hLO hsL l hl => ⟨hLM hl, hLO ((mem_coreActionKernel.mp hsL).2 l hl)⟩
  have hOH : O ≤ H := fun o ho => ⟨map_subtype_le _ ho, by
    have h1 := hON s⁻¹ (inv_mem hsM) o ho
    rw [inv_inv] at h1
    have h2 := mul_mem (inv_mem ho) h1
    rwa [show o⁻¹ * (s⁻¹ * o * s) = o⁻¹ * s⁻¹ * o * s by group] at h2⟩
  have hJH : J ≤ H := hJKK.trans (sup_le (sup_le (hLH hKM hOK hsK) (hLH hK'M hOK' hsK')) hOH)
  refine mem_coreActionKernel.mpr ⟨hsJ, fun j hj => ?_⟩
  have h1 : j⁻¹ * s⁻¹ * j * s ∈ J := by
    have h2 : s⁻¹ * j * s ∈ J := by
      have := (mem_normalizer_iff.mp (inv_mem hsJ) j).mp hj
      rwa [inv_inv] at this
    have := mul_mem (inv_mem hj) h2
    rwa [← mul_assoc, ← mul_assoc] at this
  exact GrS5.inf_oddIn_le_oddIn hJM (mem_inf.mpr ⟨(hJH hj).2, h1⟩)

theorem false_of_diag_kernel (hMax : MaximalTwoComponentInput)
    (hS : SchreierFor Blueprint.Catalog) (hbase : L34BaseSetting G) {a : G} {J W K : Subgroup G}
    (hg : GSMaximalSetting G a J) (hL34 : IsL34Type (J ⧸ Open.fusionZStar J))
    (hNJ : normalizer (J : Set G) ≤ normalizer (W : Set G)) (hKM : K ≤ normalizer (W : Set G))
    (hKc : IsPComponent 2 (K.subgroupOf (normalizer (W : Set G)))) (hKa : conjugate K a ≠ K)
    (hJKK : J ≤ K ⊔ conjugate K a ⊔ oddIn (normalizer (W : Set G))) {s : G}
    (hs2 : orderOf s = 2) (has : a * s = s * a) (hsK : s ∈ coreActionKernel K)
    (hsK' : s ∈ coreActionKernel (conjugate K a)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M : Subgroup G := normalizer (W : Set G) with hM
  set K' : Subgroup G := conjugate K a with hK'
  have hJa : J ≤ centralizer ({a} : Set G) := hg.le_centralizer
  have hJc := hg.isPComponent
  have hCaN : centralizer ({a} : Set G) ≤ normalizer (J : Set G) :=
    GrS4.centralizer_le_normalizer_of_gsMaximalSetting hMax hg
  have hCaM : centralizer ({a} : Set G) ≤ M := hCaN.trans hNJ
  have haM : a ∈ M := hCaM (mem_centralizer_singleton_iff.mpr rfl)
  have hsCa : s ∈ centralizer ({a} : Set G) := mem_centralizer_singleton_iff.mpr has.symm
  have hJM : J ≤ M := hJa.trans hCaM
  have hK'M : K' ≤ M := conjugate_le_of_mem hKM haM
  have hK'c : IsPComponent 2 (K'.subgroupOf M) := isPComponent_conjugate_subgroupOf haM hKc
  have hne : K ≠ K' := fun e => hKa e.symm
  have hOK : oddIn K ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hKM hKc
  have hOK' : oddIn K' ≤ oddIn M := GSLit.map_pPrimeCore_le_of_isPComponent hK'M hK'c
  have hK'NK : K' ≤ normalizer (K : Set G) := (GrS5.commutator_le_of_ne hKM hK'M hKc hK'c hne).2
  have hKNK' : K ≤ normalizer (K' : Set G) :=
    (GrS5.commutator_le_of_ne hK'M hKM hK'c hKc hne.symm).2
  have hJNK : J ≤ normalizer (K : Set G) := hJKK.trans
    (sup_le (sup_le le_normalizer hK'NK) (GrS4.oddIn_le_normalizer_of_isPComponent hKM hKc))
  have hJNK' : J ≤ normalizer (K' : Set G) := hJKK.trans
    (sup_le (sup_le hKNK' le_normalizer) (GrS4.oddIn_le_normalizer_of_isPComponent hK'M hK'c))
  have haa : a * a = 1 := by rw [← pow_two, ← hg.orderOf_eq, pow_orderOf_eq_one]
  have hsJ : s ∈ coreActionKernel J := mem_coreActionKernel_of_sup hJM hKM hK'M hOK hOK' hJKK
    (hCaM hsCa) (hCaN hsCa) hsK hsK'
  obtain ⟨L, hLs, hLc, hCN, -, -, hFL, hFsup⟩ := exists_target hMax hS hbase hg.orderOf_eq hs2
    has hJa hJc hg.maximal hL34 hsJ
  set F : Subgroup G := gsFixedLayer J s with hFdef
  have hFJ : F ≤ J := (gsFixedLayer_le_inf J s).trans inf_le_left
  have hFK : F ≤ normalizer (K : Set G) := hFJ.trans hJNK
  have hJF : F ⊔ oddIn J = J := UnbalancedLayer.gsFixedLayer_sup_map_pPrimeCore hs2
    (FooteLit.isQuasisimple_quotient_of_isPComponent hJa hJc) (hCaN hsCa)
    (mem_coreActionKernel.mp hsJ).2
  have hFnot : ¬ F ≤ coreActionKernel K := by
    intro hFk
    refine Single.not_le_coreActionKernel_of_diagonal hJa hJc hJM hKM hK'M hJNK hJNK' hOK hOK'
      hJKK haa (Or.inl ?_)
    refine GSThmB.CorC.le_of_perfect_of_le_sup_odd (fun o ho => ?_)
      (UnbalancedCorr.odd_card_map_pPrimeCore J) (commutator_eq_of_isPComponent hJa hJc) ?_
    · refine GrS4.mem_normalizer_of_map_le_self ?_
      rintro _ ⟨y, hy, rfl⟩
      exact UnbalancedLayer.conj_mem_coreActionKernel (hJNK (map_subtype_le _ ho)) hy
    · calc J = F ⊔ oddIn J := hJF.symm
        _ ≤ coreActionKernel K ⊔ oddIn J := sup_le_sup_right hFk _
  set A : Subgroup G := L ⊓ K with hA
  have hsP : IsPGroup 2 (zpowers s) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs2, pow_one])
  have hcomK : ∀ {g f : G}, g ∈ K → f ∈ F → g⁻¹ * f * g * f⁻¹ ∈ K := fun {g f} hg hf => by
    rw [show g⁻¹ * f * g * f⁻¹ = g⁻¹ * (f * g * f⁻¹) by group]
    exact mul_mem (inv_mem hg) ((mem_normalizer_iff.mp (hFK hf) _).mp hg)
  have hcomL : ∀ {g f : G}, g ∈ normalizer (L : Set G) → f ∈ F → g⁻¹ * f * g * f⁻¹ ∈ L :=
    fun {g f} hg hf => by
      have h1 := (mem_normalizer_iff.mp (inv_mem hg) _).mp (hFL hf)
      rw [inv_inv] at h1
      exact mul_mem h1 (inv_mem (hFL hf))
  have hKA : K ≤ A ⊔ oddIn K := Single.le_of_commutator_mem hKM hKc hsP hsK hFK hFnot
    (fun g hg f hf => mem_sup_left (mem_inf.mpr ⟨hcomL (hCN (mem_centralizer_singleton_iff.mpr
      (mem_centralizer_iff.mp hg.2 s (mem_zpowers s)).symm)) hf, hcomK hg.1 hf⟩)) le_sup_right
  set P : Subgroup G := A ⊔ oddIn L with hP
  have hLP : L ≤ normalizer (P : Set G) := by
    calc L = F ⊔ oddIn L := hFsup.symm
      _ ≤ normalizer (P : Set G) := sup_le (fun f hf => Single.mem_normalizer_sup
          (Single.mem_normalizer_inf (le_normalizer (hFL hf)) (hFK hf))
          (GrS4.self_le_normalizer_oddIn L (hFL hf))) (le_sup_right.trans le_normalizer)
  rcases Single.eq_or_commutator_le_oddIn hLs hLc (sup_le inf_le_left (map_subtype_le _)) hLP
    le_sup_right with hPL | hPL
  ·
    have haL : a ∈ normalizer (L : Set G) := hCN (mem_centralizer_singleton_iff.mpr has)
    have hLa : conjugate L a = L := conjugate_eq_of_mem_normalizer haL
    have hOa : conjugate (oddIn L) a = oddIn L := conjugate_eq_of_mem_normalizer
      (UnbalancedGS.normalizer_le_normalizer_map_of_characteristic L (pPrimeCore 2 L) haL)
    have hAaL : conjugate A a ≤ L := by
      rw [← hLa]
      exact map_mono inf_le_left
    have hAasup : conjugate A a ⊔ oddIn L = L := by
      have hPL' : P = L := hPL
      have h1 : conjugate P a = conjugate A a ⊔ conjugate (oddIn L) a :=
        Subgroup.map_sup _ _ _
      rw [hPL', hLa, hOa] at h1
      exact h1.symm
    have hcomm : ⁅A, conjugate A a⁆ ≤ oddIn K :=
      (commutator_mono inf_le_right (map_mono inf_le_right)).trans
        ((GrS5.commutator_le_inf_oddIn hKM hK'M hKc hK'c hne).trans inf_le_left)
    exact not_odd_card_commutator_of_perfect (commutator_eq_of_isPComponent hLs hLc)
      (GrS4.not_odd_card_of_isPComponent hLs hLc) inf_le_left hAaL hPL hAasup
      ((UnbalancedCorr.odd_card_map_pPrimeCore K).of_dvd_nat (card_dvd_of_le hcomm))
  ·
    have hKO : K ≤ (oddIn L ⊓ K) ⊔ oddIn K := by
      refine le_of_commutator_mem_of_cover hKM hKc inf_le_right hKA hFK hFnot
        (fun g hg f hf => mem_sup_left (mem_inf.mpr ⟨?_, hcomK hg.2 hf⟩)) le_sup_right
      have h1 : ⁅g⁻¹, f⁆ ∈ ⁅P, L⁆ := commutator_mem_commutator (mem_sup_left (inv_mem hg))
        (hFL hf)
      rw [Subgroup.commutator_comm] at h1
      have h2 := hPL h1
      rwa [commutatorElement_def, inv_inv] at h2
    have hodd : Odd (Nat.card ↥((oddIn L ⊓ K) ⊔ oddIn K)) :=
      Single.odd_card_sup ((UnbalancedCorr.odd_card_map_pPrimeCore L).of_dvd_nat
        (card_dvd_of_le inf_le_left)) (UnbalancedCorr.odd_card_map_pPrimeCore K)
        (inf_le_right.trans (GrS4.self_le_normalizer_oddIn K))
    exact GrS4.not_odd_card_of_isPComponent hKM hKc (hodd.of_dvd_nat (card_dvd_of_le hKO))

end CFSG.ComponentClassification.GrSLit.KSw
