module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfProps
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallQ3P45
public meta import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfChecks2
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallConfP45Inputs
public import Certificates.Certificate2009
public import Certificates.Certificate2012
public import Certificates.Certificate2015

public section

namespace CFSG.ComponentClassification.CatFactsSmall.PSp43

open CFSG.GH74.KGroups CFSG.Certificates CFSG.Sporadic.Schreier Subgroup
open CFSG.ComponentClassification.GSThmB

local notation "PX" => Equiv.Perm (Fin 45)

theorem cfQ_closure : QQ45.originalSubgroup = closure {q | q ∈ q0gens} := by
  rw [QQ45, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem cfQ_mem {q : PX} (hq : q ∈ q0gens) : q ∈ QQ45.originalSubgroup := by
  rw [cfQ_closure]
  exact Subgroup.subset_closure hq

theorem cfCoset_ok : (elemsT QA45).all (fun x => !(q0gens.all fun q =>
    QQ45.sift (x * q * x⁻¹) 0) || QQ45.sift x 0 || QQ45.sift (g045⁻¹ * x) 0) = true :=
  Certificates.certificate2009.1

theorem cfComm_ok : (q0gens.all fun q => decide (q * cfTau = cfTau * q) &&
    decide (q * cfZ = cfZ * q)) = true ∧ g045⁻¹ * cfZ * g045 = cfZ :=
  Certificates.certificate2009.2.1

theorem cfTau_Q : ∀ q ∈ QQ45.originalSubgroup, cfTau * q = q * cfTau := by
  intro q hq
  have h := mem_centralizer_of_gens cfQ_closure (x := cfTau) fun g hg => by
    have := List.all_eq_true.1 cfComm_ok.1 g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.1
  exact ((mem_centralizer_iff.1 h) q hq).symm

theorem cfZ_Q : ∀ q ∈ QQ45.originalSubgroup, cfZ * q = q * cfZ := by
  intro q hq
  have h := mem_centralizer_of_gens cfQ_closure (x := cfZ) fun g hg => by
    have := List.all_eq_true.1 cfComm_ok.1 g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this.2
  exact ((mem_centralizer_iff.1 h) q hq).symm

theorem cfZ_ok : (elemsT QQ45).all (fun w => !QL45.sift w 0 || !decide (w * w = 1) ||
    decide (w = 1) || decide (w = cfZ) ||
    (elemsT QQ45).any (fun v => QL45.sift v 0 && !decide (w * v = v * w))) = true :=
  Certificates.certificate2009.2.2.1

theorem cfQH_valid : cfQH.check = true ∧ cfQH.orderCertificate = 64 :=
  Certificates.certificate2009.2.2.2.1

theorem cfQR_valid : cfQR.check = true ∧ cfQR.orderCertificate = 128 :=
  Certificates.certificate2009.2.2.2.2.1

theorem cfQH_ok : ValidSchreier cfQH := cfQH_valid.1

theorem cfQR_ok : ValidSchreier cfQR := cfQR_valid.1

theorem cfQH_closure : cfQH.originalSubgroup = closure {g | g ∈ cfHgens} := by
  rw [cfQH, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem cfQR_closure : cfQR.originalSubgroup = closure {g | g ∈ cfRgens} := by
  rw [cfQR, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem card_cfQH : Nat.card cfQH.originalSubgroup = 64 := by
  rw [card_group cfQH cfQH_ok, cfQH_valid.2]

theorem card_cfQR : Nat.card cfQR.originalSubgroup = 128 := by
  rw [card_group cfQR cfQR_ok, cfQR_valid.2]

theorem cfNorm_ok : (elemsT QA45).all (fun x => !(cfHgens.all fun h =>
    cfQH.sift (x * h * x⁻¹) 0) || cfQR.sift x 0) = true :=
  Certificates.certificate2009.2.2.2.2.2.1

theorem cfR_unique : ∀ R' : Subgroup PX, R' ≤ QA45.originalSubgroup → Nat.card R' = 128 →
    QQ45.originalSubgroup ≤ R' → g045 ∈ R' → R' = cfQR.originalSubgroup := by
  intro R' hR'A hcard hQR hgR
  refine eq_of_normalizer_check QA45_ok cfQH_ok cfQR_ok cfQH_closure cfNorm_ok R' hR'A ?_
    (by rw [hcard, card_cfQH]) (by rw [card_cfQR, hcard])
  rw [cfQH_closure, closure_le]
  intro h hh
  simp only [cfHgens, List.mem_append, List.mem_singleton, Set.mem_ofPred_eq] at hh
  rcases hh with hh | rfl
  · exact hQR (cfQ_mem hh)
  · exact hgR

theorem cfR_ok : (cfRgens.all fun x => QA45.sift x 0 &&
    decide (x * (cfTau * cfZ) = cfTau * cfZ * x)) = true ∧
    (elemsT cfQR).all (fun x => !(cfRgens.all fun g => decide (g * x = x * g)) ||
      decide (x = 1) || decide (x = cfTau * cfZ)) = true ∧
    cfQR.sift (cfTau * cfZ) 0 = true ∧ (cfTau * cfZ) * (cfTau * cfZ) = 1 :=
  Certificates.certificate2009.2.2.2.2.2.2.1

theorem cfR_le : cfQR.originalSubgroup ≤ QA45.originalSubgroup ⊓
    centralizer ({cfTau * cfZ} : Set PX) := by
  rw [cfQR_closure, closure_le]
  intro x hx
  have h := List.all_eq_true.1 cfR_ok.1 x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(mem_iff_sift QA45 QA45_ok x).2 h.1, mem_centralizer_singleton_iff.2 h.2⟩

theorem cfR_leA : cfQR.originalSubgroup ≤ QA45.originalSubgroup := cfR_le.trans inf_le_left

theorem cfZ_R : (center cfQR.originalSubgroup).map cfQR.originalSubgroup.subtype =
    zpowers (cfTau * cfZ) := by
  obtain ⟨h1, h2, h3, h4⟩ := cfR_ok
  have hc : cfTau * cfZ ∈ centralizer {g | g ∈ cfRgens} := by
    rw [mem_centralizer_iff]
    intro g hg
    have h := List.all_eq_true.1 h1 g hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact h.2
  refine center_map_eq_of_gens cfQR_closure
    (zpowers_le.2 ((mem_iff_sift cfQR cfQR_ok _).2 h3)) (fun s hs g hg => ?_) (fun x hx hc' => ?_)
  · have := (zpowers_le.2 hc) hs
    exact (mem_centralizer_iff.1 this) g hg
  · have h := List.all_eq_true.1 h2 x ((mem_elemsT cfQR cfQR_ok x).2 hx)
    have hall : (cfRgens.all fun g => decide (g * x = x * g)) = true :=
      List.all_eq_true.2 fun g hg => decide_eq_true (hc' g hg)
    simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq] at h
    exact (mem_zpowers_involution h4).2 h

theorem cfCard_ok : ((elemsT QQ45).filter fun x => QL45.sift x 0).length = 8 ∧
    ((elemsT QL45).filter fun x => decide (x * cfTau = cfTau * x)).length = 24 ∧
    ((elemsT QA45).filter fun x => decide (x * (cfTau * cfZ) = cfTau * cfZ * x)).length =
      2 ^ 7 * 9 ∧
    ((elemsT cfQR).filter fun x => decide (x * cfZ = cfZ * x)).length = 64 ∧
    ((elemsT QA45).filter fun x => decide (x * cfZ = cfZ * x)).length = 2 ^ 6 * 3 :=
  Certificates.certificate2009.2.2.2.2.2.2.2.1

theorem cfCard_D : Nat.card ↥(QQ45.originalSubgroup ⊓ QL45.originalSubgroup) = 8 := by
  rw [card_inf_eq_length QQ45 QQ45_ok QL45.originalSubgroup (fun x => QL45.sift x 0)
    (fun x _ => mem_iff_sift QL45 QL45_ok x)]
  exact cfCard_ok.1

theorem cfFix_tau :
    Nat.card ↥(QL45.originalSubgroup ⊓ centralizer ({cfTau} : Set PX)) = 24 := by
  rw [card_inf_centralizer QL45 QL45_ok]
  exact cfCard_ok.2.1

theorem cfCard_Ctz : Nat.card ↥(QA45.originalSubgroup ⊓
    centralizer ({cfTau * cfZ} : Set PX)) = 2 ^ 7 * 9 := by
  rw [card_inf_centralizer QA45 QA45_ok]
  exact cfCard_ok.2.2.1

theorem cfCard_R0 : Nat.card ↥(cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX)) = 64 := by
  rw [card_inf_centralizer cfQR cfQR_ok]
  exact cfCard_ok.2.2.2.1

theorem cfCard_Cz :
    Nat.card ↥(QA45.originalSubgroup ⊓ centralizer ({cfZ} : Set PX)) = 2 ^ 6 * 3 := by
  rw [card_inf_centralizer QA45 QA45_ok]
  exact cfCard_ok.2.2.2.2

theorem cfQeq_ok : (q0gens.all fun q => QL45.sift q 0 || QL45.sift (q * cfTau⁻¹) 0 ||
    QL45.sift (q * s045⁻¹) 0 || QL45.sift (q * s045⁻¹ * cfTau⁻¹) 0) = true ∧
    QQ45.sift cfTau 0 = true ∧ QQ45.sift s045 0 = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.1

theorem cfQ_eq : QQ45.originalSubgroup = QQ45.originalSubgroup ⊓ QL45.originalSubgroup ⊔
    zpowers cfTau ⊔ zpowers s045 :=
  Q_eq_of_check QL45_ok cfQ_closure ((mem_iff_sift QQ45 QQ45_ok _).2 cfQeq_ok.2.1)
    ((mem_iff_sift QQ45 QQ45_ok _).2 cfQeq_ok.2.2) cfQeq_ok.1

theorem cfElt_ok : cfQR.sift cfTzu 0 = true ∧ cfQR.sift cfTzv 0 = true ∧
    cfTzu * cfTzv * cfTzu⁻¹ * cfTzv⁻¹ = cfTau * cfZ ∧ QP45.sift cfK0 0 = true ∧
    cfK0⁻¹ * cfZ * cfK0 = cfTau :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.1

theorem cfTz_comm : cfTau * cfZ ∈ ⁅cfQR.originalSubgroup, cfQR.originalSubgroup⁆ := by
  rw [← cfElt_ok.2.2.1, ← commutatorElement_def]
  exact commutator_mem_commutator ((mem_iff_sift cfQR cfQR_ok _).2 cfElt_ok.1)
    ((mem_iff_sift cfQR cfQR_ok _).2 cfElt_ok.2.1)

theorem cfZ_tau : ∃ k ∈ QP45.originalSubgroup, k⁻¹ * cfZ * k = cfTau :=
  ⟨cfK0, (mem_iff_sift QP45 QP45_ok _).2 cfElt_ok.2.2.2.1, cfElt_ok.2.2.2.2⟩

theorem cfQD_valid : cfQD1.check = true ∧ cfQD1.orderCertificate = 8 ∧ cfQD2.check = true ∧
    cfQD2.orderCertificate = 8 ∧ cfQD12.check = true ∧ cfQD12.orderCertificate = 64 :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.1

theorem cfQD1_eq : cfQD1.originalSubgroup = closure ({cfR1, cfS1} : Set PX) := by
  rw [cfQD1, certificate_originalSubgroup]
  congr 1
  ext x
  simp [tab_eq]

theorem cfQD2_eq : cfQD2.originalSubgroup = closure ({cfR2, cfS2} : Set PX) := by
  rw [cfQD2, certificate_originalSubgroup]
  congr 1
  ext x
  simp [tab_eq]

theorem cfQD12_eq : cfQD12.originalSubgroup =
    closure ({cfR1, cfS1, cfR2, cfS2} : Set PX) := by
  rw [cfQD12, certificate_originalSubgroup]
  congr 1
  ext x
  simp [tab_eq]

theorem cfD_ok : orderIs cfR1 4 = true ∧ orderIs cfR2 4 = true ∧ cfS1 * cfS1 = 1 ∧
    cfS2 * cfS2 = 1 ∧ cfS1 * cfR1 * cfS1⁻¹ = cfR1⁻¹ ∧ cfS2 * cfR2 * cfS2⁻¹ = cfR2⁻¹ ∧
    cfR1 * cfR1 = cfZ ∧ cfR2 * cfR2 = cfTau ∧ cfZ * cfZ = 1 ∧ cfTau * cfTau = 1 ∧
    ([cfR1, cfS1, cfR2, cfS2].all fun x => cfQR.sift x 0 && decide (x * cfZ = cfZ * x)) = true ∧
    ([cfR1, cfS1].all fun x => [cfR2, cfS2].all fun y => decide (y * x = x * y)) = true ∧
    ((List.range 4).all fun k => !decide (cfS1 = cfR1 ^ k)) = true ∧
    ((List.range 4).all fun k => !decide (cfS2 = cfR2 ^ k)) = true ∧
    (elemsT cfQD1).all (fun x => decide (x = 1) || !cfQD2.sift x 0) = true ∧
    (elemsT cfQD1).all (fun x => decide ((cfR1 * x = x * cfR1 ∧ cfS1 * x = x * cfS1) ↔
      (x = 1 ∨ x = cfZ))) = true ∧
    (elemsT cfQD2).all (fun x => decide ((cfR2 * x = x * cfR2 ∧ cfS2 * x = x * cfS2) ↔
      (x = 1 ∨ x = cfTau))) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfR0_mem : ∀ x ∈ [cfR1, cfS1, cfR2, cfS2],
    x ∈ cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) := fun x hx => by
  have h := List.all_eq_true.1 cfD_ok.2.2.2.2.2.2.2.2.2.2.1 x hx
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨(mem_iff_sift cfQR cfQR_ok x).2 h.1, mem_centralizer_singleton_iff.2 h.2⟩

theorem not_mem_zpowers_of_check {r s : PX} (hr : orderOf r = 4)
    (hn : ((List.range 4).all fun k => !decide (s = r ^ k)) = true) : s ∉ zpowers r := by
  intro hs
  rw [mem_zpowers_iff_mem_range_orderOf, Finset.mem_image] at hs
  obtain ⟨k, hk, hks⟩ := hs
  rw [hr, Finset.mem_range] at hk
  have := List.all_eq_true.1 hn k (List.mem_range.2 hk)
  rw [hks] at this
  simp at this

theorem center_pair_of_check {r s z : PX} {Q : RawSchreierDatum 45} (hQ : ValidSchreier Q)
    (hQe : Q.originalSubgroup = closure ({r, s} : Set PX)) (hz : z * z = 1)
    (h : (elemsT Q).all (fun x => decide ((r * x = x * r ∧ s * x = x * s) ↔
      (x = 1 ∨ x = z))) = true) :
    center (closure ({r, s} : Set PX)) = (zpowers z).subgroupOf (closure ({r, s} : Set PX)) := by
  refine center_eq_of_gens rfl hz fun x hx => ?_
  rw [← hQe] at hx
  have h1 := of_decide_eq_true (List.all_eq_true.1 h x ((mem_elemsT Q hQ x).2 hx))
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
  exact h1

theorem cfR0_decomp : ∃ D₁ D₂ : Subgroup PX,
    D₁ ⊔ D₂ = cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) ∧ D₁ ⊓ D₂ = ⊥ ∧
    D₁ ≤ centralizer (D₂ : Set PX) ∧ Nonempty (D₁ ≃* DihedralGroup 4) ∧
    Nonempty (D₂ ≃* DihedralGroup 4) ∧ center D₁ = (zpowers cfZ).subgroupOf D₁ ∧
    center D₂ = (zpowers cfTau).subgroupOf D₂ := by
  obtain ⟨hr1, hr2, hs1, hs2, hrel1, hrel2, -, -, hz2, hτ2, -, hcomm, hn1, hn2, hinf, hc1, hc2⟩ :=
    cfD_ok
  have hQD1 : ValidSchreier cfQD1 := cfQD_valid.1
  have hQD2 : ValidSchreier cfQD2 := cfQD_valid.2.2.1
  have hQD12 : ValidSchreier cfQD12 := cfQD_valid.2.2.2.2.1
  have hrd1 : orderOf cfR1 = 4 := (orderIs_iff _ (by norm_num)).1 hr1
  have hrd2 : orderOf cfR2 = 4 := (orderIs_iff _ (by norm_num)).1 hr2
  have hsup : closure ({cfR1, cfS1} : Set PX) ⊔ closure ({cfR2, cfS2} : Set PX) =
      cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) := by
    rw [← Subgroup.closure_union]
    have h12 : ({cfR1, cfS1} : Set PX) ∪ {cfR2, cfS2} = {cfR1, cfS1, cfR2, cfS2} := by
      rw [Set.insert_union, Set.singleton_union]
    rw [h12, ← cfQD12_eq]
    refine eq_of_le_of_card_ge ?_ ?_
    · rw [cfQD12_eq, closure_le]
      intro x hx
      exact cfR0_mem x (by simpa using hx)
    · rw [cfCard_R0, card_group cfQD12 hQD12, cfQD_valid.2.2.2.2.2]
  refine ⟨closure ({cfR1, cfS1} : Set PX), closure ({cfR2, cfS2} : Set PX), hsup, ?_, ?_,
    dihedral_of_gens hrd1 hs1 hrel1 (not_mem_zpowers_of_check hrd1 hn1),
    dihedral_of_gens hrd2 hs2 hrel2 (not_mem_zpowers_of_check hrd2 hn2),
    center_pair_of_check hQD1 cfQD1_eq hz2 hc1, center_pair_of_check hQD2 cfQD2_eq hτ2 hc2⟩
  · rw [eq_bot_iff, ← cfQD1_eq, ← cfQD2_eq]
    intro x hx
    rw [mem_bot]
    have h := List.all_eq_true.1 hinf x ((mem_elemsT cfQD1 hQD1 x).2 hx.1)
    simp only [Bool.or_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
    rcases h with h | h
    · exact h
    · rw [(mem_iff_sift cfQD2 hQD2 x).1 hx.2] at h
      exact absurd h (by decide)
  · rw [closure_le]
    intro x hx
    refine mem_centralizer_of_gens rfl fun g hg => ?_
    have h := List.all_eq_true.1 hcomm x (by simpa using hx)
    exact of_decide_eq_true (List.all_eq_true.1 h g (by simpa using hg))

theorem cfQF_valid : cfQF1.check = true ∧ cfQF1.orderCertificate = 16 ∧ cfQF2.check = true ∧
    cfQF2.orderCertificate = 16 ∧ cfQF3.check = true ∧ cfQF3.orderCertificate = 16 ∧
    cfQRz.check = true ∧ cfQRz.orderCertificate = 64 :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfQF1_eq : cfQF1.originalSubgroup = closure {g | g ∈ cfF1} := by
  rw [cfQF1, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem cfQF2_eq : cfQF2.originalSubgroup = closure {g | g ∈ cfF2} := by
  rw [cfQF2, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem cfQF3_eq : cfQF3.originalSubgroup = closure {g | g ∈ cfF3} := by
  rw [cfQF3, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem cfQRz_eq : cfQRz.originalSubgroup = closure {g | g ∈ cfFgens} := by
  rw [cfQRz, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem cfF_ok : (cfFgens.all fun x => cfQR.sift x 0 && decide (x * cfZ = cfZ * x)) = true ∧
    (elemsT cfQF1).all (fun x => decide (x * x = 1)) = true ∧
    (elemsT cfQF2).all (fun x => decide (x * x = 1)) = true ∧
    (elemsT cfQF3).all (fun x => decide (x * x = 1)) = true ∧
    cfQRz.sift cfZ 0 = true ∧ cfQRz.sift cfTau 0 = true ∧ cfQRz.sift cfR1 0 = true ∧
    cfQRz.sift cfR2 0 = true ∧ (cfFgens.all fun x => decide (x * cfZ = cfZ * x) &&
      decide (x * cfTau = cfTau * x)) = true ∧
    (elemsT cfQRz).all (fun x => !(cfFgens.all fun g => decide (g * x = x * g)) ||
      (decide (x = 1) || decide (x = cfZ) || decide (x = cfTau) || decide (x = cfZ * cfTau))) =
      true ∧
    (elemsT cfQRz).all (fun x => decide (x * x = 1) || decide (x * x = cfZ) ||
      decide (x * x = cfTau) || decide (x * x = cfZ * cfTau)) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfRz_eq : cfQRz.originalSubgroup =
    cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) := by
  refine eq_of_le_of_card_ge ?_ ?_
  · rw [cfQRz_eq, closure_le]
    intro x hx
    have h := List.all_eq_true.1 cfF_ok.1 x hx
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨(mem_iff_sift cfQR cfQR_ok x).2 h.1, mem_centralizer_singleton_iff.2 h.2⟩
  · rw [cfCard_R0, card_group cfQRz cfQF_valid.2.2.2.2.2.2.1, cfQF_valid.2.2.2.2.2.2.2]

theorem cfR0_gen : closure {y | ∃ E : Subgroup PX,
    E ≤ cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) ∧ Cat8.IsElemAb2 E ∧
      Nat.card E = 16 ∧ y ∈ E} = cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) := by
  apply le_antisymm
  · rw [closure_le]
    rintro y ⟨E, hE, -, -, hy⟩
    exact hE hy
  · refine le_trans (le_of_eq (cfRz_eq.symm.trans cfQRz_eq)) ?_
    rw [closure_le]
    intro x hx
    apply Subgroup.subset_closure
    have hle : ∀ F : List PX, (∀ g ∈ F, g ∈ cfFgens) →
        closure {g | g ∈ F} ≤ cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) := by
      intro F hF
      rw [← cfRz_eq, cfQRz_eq]
      exact closure_mono fun g hg => hF g hg
    obtain ⟨-, h2, h3, h4, -⟩ := cfF_ok
    obtain ⟨v1, c1, v2, c2, v3, c3, -⟩ := cfQF_valid
    have hF : ∀ (F : List PX) (Q : RawSchreierDatum 45), ValidSchreier Q →
        Q.originalSubgroup = closure {g | g ∈ F} → Q.orderCertificate = 16 →
        (elemsT Q).all (fun x => decide (x * x = 1)) = true → (∀ g ∈ F, g ∈ cfFgens) →
        ∀ g ∈ F, ∃ E : Subgroup PX, E ≤ cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX) ∧
          Cat8.IsElemAb2 E ∧ Nat.card E = 16 ∧ g ∈ E := by
      intro F Q hQ hQe hQc hQ2 hFg g hg
      refine ⟨Q.originalSubgroup, ?_, elemAb_of_check hQ hQ2, ?_, ?_⟩
      · rw [hQe]
        exact hle F hFg
      · rw [card_group Q hQ, hQc]
      · rw [hQe]
        exact Subgroup.subset_closure hg
    simp only [cfFgens, List.mem_append, Set.mem_ofPred_eq] at hx
    rcases hx with (hx | hx) | hx
    · exact hF cfF1 cfQF1 v1 cfQF1_eq c1 h2 (fun g hg => by simp [cfFgens, hg]) x hx
    · exact hF cfF2 cfQF2 v2 cfQF2_eq c2 h3 (fun g hg => by simp [cfFgens, hg]) x hx
    · exact hF cfF3 cfQF3 v3 cfQF3_eq c3 h4 (fun g hg => by simp [cfFgens, hg]) x hx

theorem cfR0_center : (center ↥(cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX))).map
      (cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX)).subtype = zpowers cfZ ⊔
        zpowers cfTau ∧
    closure {y | ∃ x ∈ cfQR.originalSubgroup ⊓ centralizer ({cfZ} : Set PX), y = x * x} =
      zpowers cfZ ⊔ zpowers cfTau := by
  obtain ⟨-, -, -, -, hz, hτ, hr1, hr2, hc, hcen, hsq⟩ := cfF_ok
  have hQRz : ValidSchreier cfQRz := cfQF_valid.2.2.2.2.2.2.1
  rw [← cfRz_eq]
  constructor
  · have hcg : ∀ g ∈ cfFgens, g * cfZ = cfZ * g ∧ g * cfTau = cfTau * g := by
      intro g hg
      have h := List.all_eq_true.1 hc g hg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact h
    have hcz : cfZ ∈ centralizer {g | g ∈ cfFgens} ∧ cfTau ∈ centralizer {g | g ∈ cfFgens} :=
      ⟨mem_centralizer_iff.2 fun g hg => (hcg g hg).1,
        mem_centralizer_iff.2 fun g hg => (hcg g hg).2⟩
    refine center_map_eq_of_gens cfQRz_eq (sup_le (zpowers_le.2 ((mem_iff_sift _ hQRz _).2 hz))
      (zpowers_le.2 ((mem_iff_sift _ hQRz _).2 hτ))) (fun s hs g hg => ?_) (fun x hx hc' => ?_)
    · have := (sup_le (zpowers_le.2 hcz.1) (zpowers_le.2 hcz.2)) hs
      exact (mem_centralizer_iff.1 this) g hg
    · have h := List.all_eq_true.1 hcen x ((mem_elemsT cfQRz hQRz x).2 hx)
      have hall : (cfFgens.all fun g => decide (g * x = x * g)) = true :=
        List.all_eq_true.2 fun g hg => decide_eq_true (hc' g hg)
      simp only [hall, Bool.not_true, Bool.false_or, Bool.or_eq_true, decide_eq_true_eq,
        or_assoc] at h
      exact mem_sup_zpowers_of_mem_list h
  · apply le_antisymm
    · rw [closure_le]
      rintro y ⟨x, hx, rfl⟩
      have h := List.all_eq_true.1 hsq x ((mem_elemsT cfQRz hQRz x).2 hx)
      simp only [Bool.or_eq_true, decide_eq_true_eq, or_assoc] at h
      exact mem_sup_zpowers_of_mem_list h
    · have h1 : cfZ ∈ closure {y | ∃ x ∈ cfQRz.originalSubgroup, y = x * x} :=
        Subgroup.subset_closure ⟨cfR1, (mem_iff_sift _ hQRz _).2 hr1, cfD_ok.2.2.2.2.2.2.1.symm⟩
      have h2 : cfTau ∈ closure {y | ∃ x ∈ cfQRz.originalSubgroup, y = x * x} :=
        Subgroup.subset_closure ⟨cfR2, (mem_iff_sift _ hQRz _).2 hr2, cfD_ok.2.2.2.2.2.2.2.1.symm⟩
      exact sup_le (zpowers_le.2 h1) (zpowers_le.2 h2)

theorem cfQE_valid : cfQE.check = true ∧ cfQE.orderCertificate = 16 :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfQE_ok : ValidSchreier cfQE := cfQE_valid.1

theorem cfQE_eq : cfQE.originalSubgroup = closure {g | g ∈ cfEgens} := by
  rw [cfQE, certificate_originalSubgroup, show (tab : PX → PX) = id from funext tab_eq,
    List.map_id]

theorem card_cfQE : Nat.card cfQE.originalSubgroup = 16 := by
  rw [card_group cfQE cfQE_ok, cfQE_valid.2]

theorem cfE_ok : (cfEgens.all fun x => cfQR.sift x 0 && QP45.sift x 0) = true ∧
    (elemsT cfQE).all (fun x => decide (x * x = 1)) = true ∧ cfQE.sift cfZ 0 = true ∧
    cfQE.sift cfTau 0 = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfE_le : cfQE.originalSubgroup ≤ cfQR.originalSubgroup ⊓ QP45.originalSubgroup := by
  rw [cfQE_eq, closure_le]
  intro x hx
  have h := List.all_eq_true.1 cfE_ok.1 x hx
  simp only [Bool.and_eq_true] at h
  exact ⟨(mem_iff_sift cfQR cfQR_ok x).2 h.1, (mem_iff_sift QP45 QP45_ok x).2 h.2⟩

theorem cfE_sq : Cat8.IsElemAb2 cfQE.originalSubgroup := elemAb_of_check cfQE_ok cfE_ok.2.1

theorem cfE_uniq_ok : ((elemsT cfQR).filter fun x => QP45.sift x 0).all (fun x =>
    !decide (x * x = 1) || cfQE.sift x 0 || decide ((((elemsT cfQR).filter fun x =>
      QP45.sift x 0).filter fun y => decide (y * y = 1) && decide (y * x = x * y)).length <
        16)) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfE_cent_ok : (elemsT QA45).all (fun x => !(cfEgens.all fun e =>
    decide (e * x = x * e)) || cfQE.sift x 0) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfE_cent : QA45.originalSubgroup ⊓ centralizer (cfQE.originalSubgroup : Set PX) =
    cfQE.originalSubgroup := by
  apply le_antisymm
  · rintro x ⟨hxA, hxc⟩
    have h := List.all_eq_true.1 cfE_cent_ok x ((mem_elemsT _ QA45_ok x).2 hxA)
    have h2 : (cfEgens.all fun e => decide (e * x = x * e)) = true :=
      List.all_eq_true.2 fun e he => decide_eq_true ((mem_centralizer_iff.1 hxc) e
        (by rw [cfQE_eq]; exact Subgroup.subset_closure he))
    rw [h2, Bool.not_true, Bool.false_or] at h
    exact (mem_iff_sift cfQE cfQE_ok x).2 h
  · intro x hx
    exact ⟨cfR_leA (cfE_le hx).1, mem_centralizer_iff.2 fun y hy => mul_comm_of_sq cfE_sq hy hx⟩

theorem cfN_iff (x : PX) : x ∈ normalizer (cfQE.originalSubgroup : Set PX) ↔
    (cfEgens.all fun e => cfQE.sift (x * e * x⁻¹) 0) = true := by
  constructor
  · intro hx
    refine List.all_eq_true.2 fun e he => (mem_iff_sift cfQE cfQE_ok _).1 ?_
    exact (mem_normalizer_iff.1 hx e).1 (by rw [cfQE_eq]; exact Subgroup.subset_closure he)
  · intro h
    exact mem_normalizer_of_gens cfQE_eq fun e he =>
      (mem_iff_sift cfQE cfQE_ok _).2 (List.all_eq_true.1 h e he)

theorem cfOrb_ok : (cfOz.all fun p => decide (p.2⁻¹ * cfZ * p.2 = p.1) && QA45.sift p.2 0 &&
      (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
    (cfOzt.all fun p => decide (p.2⁻¹ * (cfZ * cfTau) * p.2 = p.1) && QA45.sift p.2 0 &&
      (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true ∧
    (cfOz.map Prod.fst).Nodup ∧ (cfOzt.map Prod.fst).Nodup ∧
    (elemsT cfQE).all (fun w => decide (w = 1) || decide (w ∈ cfOz.map Prod.fst) ||
      decide (w ∈ cfOzt.map Prod.fst)) = true ∧
    (cfOz.all fun p => cfQE.sift p.1 0) = true ∧ (cfOzt.all fun p => cfQE.sift p.1 0) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfOrb_ok2 : (elemsT QA45).all (fun x => !(cfEgens.all fun e =>
      cfQE.sift (x * e * x⁻¹) 0) || (decide (x⁻¹ * cfZ * x ∈ cfOz.map Prod.fst) &&
      decide (x⁻¹ * (cfZ * cfTau) * x ∈ cfOzt.map Prod.fst))) = true ∧
    ((elemsT QA45).filter fun x => cfEgens.all fun e => cfQE.sift (x * e * x⁻¹) 0).length =
      1920 :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfOrb_iff (L : List (PX × PX)) (w₀ : PX)
    (hL : (L.all fun p => decide (p.2⁻¹ * w₀ * p.2 = p.1) && QA45.sift p.2 0 &&
      (cfEgens.all fun e => cfQE.sift (p.2 * e * p.2⁻¹) 0)) = true)
    (hall : ∀ x ∈ QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set PX),
      x⁻¹ * w₀ * x ∈ L.map Prod.fst) (y : PX) :
    y ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set PX))
      w₀ ↔ y ∈ L.map Prod.fst := by
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact hall n hn
  · intro hy
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
    have h := List.all_eq_true.1 hL p hp
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨p.2, ⟨(mem_iff_sift QA45 QA45_ok _).2 h.1.2, (cfN_iff p.2).2 h.2⟩, h.1.1⟩

theorem cfOz_iff (y : PX) :
    y ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set PX))
      cfZ ↔ y ∈ cfOz.map Prod.fst :=
  cfOrb_iff cfOz cfZ cfOrb_ok.1 (fun x hx => by
    have h := List.all_eq_true.1 cfOrb_ok2.1 x ((mem_elemsT _ QA45_ok x).2 hx.1)
    rw [(cfN_iff x).1 hx.2, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    exact of_decide_eq_true h.1) y

theorem cfOzt_iff (y : PX) :
    y ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set PX))
      (cfZ * cfTau) ↔ y ∈ cfOzt.map Prod.fst :=
  cfOrb_iff cfOzt (cfZ * cfTau) cfOrb_ok.2.1 (fun x hx => by
    have h := List.all_eq_true.1 cfOrb_ok2.1 x ((mem_elemsT _ QA45_ok x).2 hx.1)
    rw [(cfN_iff x).1 hx.2, Bool.not_true, Bool.false_or, Bool.and_eq_true] at h
    exact of_decide_eq_true h.2) y

theorem cfN_card :
    Nat.card ↥(QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set PX)) =
      1920 := by
  rw [card_inf_eq_length QA45 QA45_ok _ (fun x => cfEgens.all fun e =>
    cfQE.sift (x * e * x⁻¹) 0) (fun x _ => cfN_iff x)]
  exact cfOrb_ok2.2

theorem cfEsub_ok : (cfEgens.all fun x => decide (x ∈ cfOzt.map Prod.fst)) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfDisj :
    (Nat.card ↥(QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set PX)) = 1920 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set
            PX)) cfZ) = 10 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set
            PX)) (cfZ * cfTau)) = 5 ∧
        closure (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set
            PX)) (cfZ * cfTau)) = cfQE.originalSubgroup) ∨
      (Nat.card ↥(QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set PX)) = 1152 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set
            PX)) cfZ) = 6 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (cfQE.originalSubgroup : Set
            PX)) (cfZ * cfTau)) = 9 ∧
        closure {y | ∃ u ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer
            (cfQE.originalSubgroup : Set PX)) cfZ, ∃ v ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓
            normalizer (cfQE.originalSubgroup : Set PX)) cfZ,
          y = u * v} = cfQE.originalSubgroup) := by
  left
  refine ⟨cfN_card, ?_, ?_, ?_⟩
  · rw [natCard_eq_length cfOrb_ok.2.2.1 cfOz_iff]
    rfl
  · rw [natCard_eq_length cfOrb_ok.2.2.2.1 cfOzt_iff]
    rfl
  · apply le_antisymm
    · rw [closure_le]
      intro y hy
      replace hy := (cfOzt_iff y).1 hy
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy
      exact (mem_iff_sift cfQE cfQE_ok _).2 (List.all_eq_true.1 cfOrb_ok.2.2.2.2.2.2 p hp)
    · refine le_trans (le_of_eq cfQE_eq) ?_
      rw [closure_le]
      intro x hx
      exact Subgroup.subset_closure ((cfOzt_iff x).2
        (of_decide_eq_true (List.all_eq_true.1 cfEsub_ok x hx)))

theorem cfCls_mem : ∀ k ∈ cfCls1 ++ cfCls2, k ∈ QA45.originalSubgroup := by
  intro k hk
  simp only [cfCls1, cfCls2, List.mem_append, List.mem_map] at hk
  rcases hk with ⟨w, -, rfl⟩ | ⟨w, -, rfl⟩ <;>
  · rw [tab_eq]
    refine evalCodes_mem_of_gens _ QA45.originalSubgroup (fun g hg => ?_) w
    rw [QA45_closure]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl <;> rw [tab_eq] <;> exact subset_closure (by simp)

theorem cfICls_mem : ∀ k ∈ cfICls1 ++ cfICls2, k ∈ QP45.originalSubgroup := by
  intro k hk
  simp only [cfICls1, cfICls2, List.mem_append, List.mem_map] at hk
  rcases hk with ⟨w, -, rfl⟩ | ⟨w, -, rfl⟩ <;>
  · rw [tab_eq]
    refine evalCodes_mem_of_gens _ QP45.originalSubgroup (fun g hg => ?_) w
    rw [QP45_closure]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl <;> rw [tab_eq] <;> exact subset_closure (by simp)

theorem cfCls_conj {C K : List PX} {w₀ y : PX} (hC : C = K.map fun k => tab (k⁻¹ * w₀ * k))
    (hy : y ∈ C) : ∃ k ∈ K, k⁻¹ * w₀ * k = y := by
  rw [hC, List.mem_map] at hy
  obtain ⟨k, hk, rfl⟩ := hy
  exact ⟨k, hk, (tab_eq _).symm⟩

theorem cfNormal_ok : (elemsT cfQR).all (fun w => !decide (w * w = 1) || QP45.sift w 0 ||
    (fun y => decide (y ∈ cfCls1C)) w ||
    (elemsT cfQR).any (fun r => !decide (w * (r * w * r⁻¹) = r * w * r⁻¹ * w)) ||
    decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
      !(fun y => decide (y ∈ cfCls1C)) y &&
      (elemsT cfQR).all fun r => decide (y * (r * w * r⁻¹) = r * w * r⁻¹ * y)).length < 16)) =
      true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfMisc_ok : (elemsT cfQE).all (fun e => decide (e * s045 * e⁻¹ * s045⁻¹ = 1) ||
      decide (e * s045 * e⁻¹ * s045⁻¹ = cfCE)) = true ∧ s045 * s045 = 1 ∧
    cfQE.sift cfE1 0 = true ∧ cfE1 * s045 * cfE1⁻¹ * s045⁻¹ = cfCE ∧ cfCE * cfCE = 1 ∧
    cfCE ≠ 1 ∧ cfQR.sift cfEe 0 = true ∧ QP45.sift cfEe 0 = true ∧
    cfEn1 * cfEn2 * cfEn1⁻¹ * cfEn2⁻¹ = cfEe ∧ cfEe * cfEe = 1 ∧
    (cfEgens.all fun g => decide (g * cfEe = cfEe * g)) = false ∧ QA45.sift cfEn1 0 = true ∧
    QA45.sift cfEn2 0 = true ∧ (cfEgens.all fun e => cfQE.sift (cfEn1 * e * cfEn1⁻¹) 0) = true ∧
    (cfEgens.all fun e => cfQE.sift (cfEn2 * e * cfEn2⁻¹) 0) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfOuter_ok : (elemsT QA45).all (fun y => !decide (y * y = 1) || QP45.sift y 0 ||
    decide (y ∈ cfCls1C) || decide (y ∈ cfCls2C)) = true ∧
    (elemsT QP45).all (fun y => !decide (y * y = 1) || decide (y = 1) ||
      decide (y ∈ cfICls1C) || decide (y ∈ cfICls2C)) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem cfE32_ok : (elemsT cfQR).all (fun x => !decide (x * x = 1) || decide (x = 1) ||
    decide (x ∈ cfB) || decide (((elemsT cfQR).filter fun y => decide (y * y = 1) &&
      decide (y * x = x * y)).length < 32)) = true :=
  Certificates.certificate2009.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

theorem cfE0 : ∃ E₀ : Subgroup PX,
    E₀ ≤ cfQR.originalSubgroup ⊓ QP45.originalSubgroup ∧ Cat8.IsElemAb2 E₀ ∧
    Nat.card E₀ = 16 ∧
    (∀ E' : Subgroup PX, E' ≤ cfQR.originalSubgroup ⊓ QP45.originalSubgroup →
      Cat8.IsElemAb2 E' → Nat.card E' = 16 → E' = E₀) ∧
    cfZ ∈ E₀ ∧ cfTau ∈ E₀ ∧ QA45.originalSubgroup ⊓ centralizer (E₀ : Set PX) = E₀ ∧
    (∀ w ∈ E₀, w = 1 ∨ w ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX))
      cfZ ∨ w ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX))
        (cfZ * cfTau)) ∧
    ((Nat.card ↥(QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX)) = 1920 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX)) cfZ) =
          10 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX))
          (cfZ * cfTau)) = 5 ∧
        closure (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX))
          (cfZ * cfTau)) = E₀) ∨
      (Nat.card ↥(QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX)) = 1152 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX)) cfZ) =
          6 ∧
        Nat.card (Cat8.conjOrbit (QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX))
          (cfZ * cfTau)) = 9 ∧
        closure {y | ∃ u ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓
          normalizer (E₀ : Set PX)) cfZ, ∃ v ∈ Cat8.conjOrbit (QA45.originalSubgroup ⊓
            normalizer (E₀ : Set PX)) cfZ, y = u * v} = E₀)) ∧
    (∀ A' : Subgroup PX, A' ≤ cfQR.originalSubgroup → Cat8.IsElemAb2 A' → Nat.card A' = 16 →
      (∀ r ∈ cfQR.originalSubgroup, ∀ x ∈ A', r * x * r⁻¹ ∈ A') →
        A' = E₀ ∨ ∃ w ∈ A', ∃ y ∈ QA45.originalSubgroup, y⁻¹ * s045 * y = w) ∧
    Nat.card ↥(⁅E₀, zpowers s045⁆ : Subgroup PX) = 2 ∧
    ∃ e ∈ cfQR.originalSubgroup ⊓ QP45.originalSubgroup,
      e ∈ ⁅QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX),
        QA45.originalSubgroup ⊓ normalizer (E₀ : Set PX)⁆ ∧
      e * e = 1 ∧ e ∉ centralizer (E₀ : Set PX) := by
  have hunique := fun E' hE' h2 h16 =>
    unique_E16_of_check cfQR_ok QP45_ok cfQE_ok cfE_uniq_ok card_cfQE E' hE' h2 h16
  obtain ⟨hc1, hs2, he1, hce, hcc, hc1', heR, heP, hen, hee, henc, hn1A, hn2A, hn1N, hn2N⟩ :=
    cfMisc_ok
  refine ⟨cfQE.originalSubgroup, cfE_le, cfE_sq, card_cfQE, hunique,
    (mem_iff_sift cfQE cfQE_ok _).2 cfE_ok.2.2.1, (mem_iff_sift cfQE cfQE_ok _).2 cfE_ok.2.2.2,
    cfE_cent, ?_, cfDisj, ?_, ?_, ?_⟩
  · intro w hw
    have h := List.all_eq_true.1 cfOrb_ok.2.2.2.2.1 w ((mem_elemsT cfQE cfQE_ok w).2 hw)
    simp only [Bool.or_eq_true, decide_eq_true_eq] at h
    rcases h with (h | h) | h
    · exact Or.inl h
    · exact Or.inr (Or.inl ((cfOz_iff w).2 h))
    · exact Or.inr (Or.inr ((cfOzt_iff w).2 h))
  · intro A' hA'R hA'2 hA'16 hA'n
    by_cases hA'P : A' ≤ QP45.originalSubgroup
    · exact Or.inl (hunique A' (le_inf hA'R hA'P) hA'2 hA'16)
    · obtain ⟨w, hw, hwc⟩ := normal_E16_of_check cfQR_ok QP45_ok
        (fun y => decide (y ∈ cfCls1C)) cfNormal_ok A' hA'R hA'2 hA'16 hA'n hA'P
      obtain ⟨k, hk, hkw⟩ := cfCls_conj rfl (of_decide_eq_true hwc)
      exact Or.inr ⟨w, hw, k, cfCls_mem k (List.mem_append_left _ hk), hkw⟩
  · have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [commutator_zpowers_eq hs2 (fun e he => ?_) ((mem_iff_sift cfQE cfQE_ok _).2 he1) hce,
      Nat.card_zpowers]
    · exact orderOf_eq_prime (by rw [pow_two]; exact hcc) hc1'
    · have h := List.all_eq_true.1 hc1 e ((mem_elemsT cfQE cfQE_ok e).2 he)
      simp only [Bool.or_eq_true, decide_eq_true_eq] at h
      rcases h with h | h
      · rw [h]; exact one_mem _
      · rw [h]; exact mem_zpowers _
  · refine ⟨cfEe, ⟨(mem_iff_sift cfQR cfQR_ok _).2 heR, (mem_iff_sift QP45 QP45_ok _).2 heP⟩,
      ?_, hee, ?_⟩
    · rw [← hen, ← commutatorElement_def]
      exact commutator_mem_commutator ⟨(mem_iff_sift QA45 QA45_ok _).2 hn1A, (cfN_iff _).2 hn1N⟩
        ⟨(mem_iff_sift QA45 QA45_ok _).2 hn2A, (cfN_iff _).2 hn2N⟩
    · intro hc
      have hall : (cfEgens.all fun g => decide (g * cfEe = cfEe * g)) = true :=
        List.all_eq_true.2 fun g hg => decide_eq_true ((mem_centralizer_iff.1 hc) g
          (by rw [cfQE_eq]; exact Subgroup.subset_closure hg))
      rw [hall] at henc
      exact absurd henc (by decide)

theorem cfNo_E32 : ∀ A' : Subgroup PX, A' ≤ cfQR.originalSubgroup → Cat8.IsElemAb2 A' →
    Nat.card A' ≠ 32 :=
  fun A' hA' h2 => no_E32_of_check cfQR_ok cfB (by decide) cfE32_ok A' hA' h2

theorem cfOuter : ∀ y ∈ QA45.originalSubgroup, y * y = 1 → y ∉ QP45.originalSubgroup →
    (∃ k ∈ QA45.originalSubgroup, k⁻¹ * s045 * k = y) ∨
      ∃ k ∈ QA45.originalSubgroup, k⁻¹ * (s045 * cfZ * cfTau) * k = y := by
  intro y hy hy2 hyP
  have h := List.all_eq_true.1 cfOuter_ok.1 y ((mem_elemsT _ QA45_ok y).2 hy)
  have hs : QP45.sift y 0 = false := by
    rcases Bool.eq_false_or_eq_true (QP45.sift y 0) with h2 | h2
    · exact absurd ((mem_iff_sift QP45 QP45_ok y).2 h2) hyP
    · exact h2
  simp only [hy2, hs, decide_true, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | h
  · obtain ⟨k, hk, hky⟩ := cfCls_conj rfl h
    exact Or.inl ⟨k, cfCls_mem k (List.mem_append_left _ hk), hky⟩
  · obtain ⟨k, hk, hky⟩ := cfCls_conj rfl h
    exact Or.inr ⟨k, cfCls_mem k (List.mem_append_right _ hk), hky⟩

theorem cfInner : ∀ y ∈ QP45.originalSubgroup, y * y = 1 → y ≠ 1 →
    (∃ k ∈ QP45.originalSubgroup, k⁻¹ * cfZ * k = y) ∨
      ∃ k ∈ QP45.originalSubgroup, k⁻¹ * (cfZ * cfTau) * k = y := by
  intro y hy hy2 hy1
  have h := List.all_eq_true.1 cfOuter_ok.2 y ((mem_elemsT _ QP45_ok y).2 hy)
  simp only [hy2, hy1, decide_true, decide_false, Bool.not_true, Bool.false_or, Bool.or_eq_true,
    decide_eq_true_eq] at h
  rcases h with h | h
  · obtain ⟨k, hk, hky⟩ := cfCls_conj rfl h
    exact Or.inl ⟨k, cfICls_mem k (List.mem_append_left _ hk), hky⟩
  · obtain ⟨k, hk, hky⟩ := cfCls_conj rfl h
    exact Or.inr ⟨k, cfICls_mem k (List.mem_append_right _ hk), hky⟩

noncomputable def cfConfData {K₀ : Type} [Group K₀] (e : K₀ ≃* QP45.originalSubgroup) :
    Q3ConfData K₀ PX := by
  classical
  let M := (exists_model e).choose
  have hP : M.P = QP45.originalSubgroup := (exists_model e).choose_spec.1
  have hA : M.A = QA45.originalSubgroup := (exists_model e).choose_spec.2
  have hK : Nat.card K₀ = 2 ^ 6 * 405 := by
    rw [Nat.card_congr e.toEquiv, card_P]
    norm_num
  exact
    { M := M
      PA := by rw [hP, hA]; exact P_le_A
      cent := by rw [hP, hA]; exact cent_triv
      card := by rw [hP, hA]; exact card_A_eq
      m := 405
      hm := by decide
      hK := fun d hd hdo => odd_dvd_of_dvd_mul (hK ▸ hd) hdo
      noNilp := by rw [hP, hA]; exact fun s hs hs2 => noNilp_fact hs hs2
      s₀ := s045
      adm := by
        rw [hP, hA]
        intro s hs hs2 hsP h5
        have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
        obtain ⟨⟨x, hx⟩, hxo⟩ := exists_prime_orderOf_dvd_card' 5 h5
        rw [Subgroup.orderOf_mk] at hxo
        have hx5 : x ∈ five45 := by
          rw [five45, List.mem_filter, mem_elemsT QP45 QP45_ok]
          refine ⟨hx.1, ?_⟩
          simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
            decide_eq_false_iff_not]
          exact ⟨hxo ▸ pow_orderOf_eq_one x, fun h1 => by rw [h1, orderOf_one] at hxo; omega⟩
        obtain ⟨k, hk, hks⟩ := exists_conj_of_admCheckA QP45_ok adm_ok
          ((mem_elemsT QA45 QA45_ok s).2 hs) hs2 hsP hx5 (mem_centralizer_singleton_iff.1 hx.2)
        exact ⟨k, admConj_mem k hk, hks⟩
      L := QL45.originalSubgroup
      commL := by rw [hP]; exact commutator_C0
      cardL := card_QL45
      oddL := L_oddNormal
      Q₀ := QQ45.originalSubgroup
      Q₀le := by rw [hA]; exact QQ45_le
      cardCA := by rw [hA]; exact card_CA0
      cardQ₀ := card_QQ45
      g₀ := g045
      g₀P := by rw [hP]; exact g045_mem
      g₀N := g045_norm
      g₀Q := g045_not_mem
      g₀2 := g045_sq
      g₀σ := by rw [hP]; exact g045_sigma
      τ₀ := cfTau
      τ_eq := rfl
      z₀ := cfZ
      R₀ := cfQR.originalSubgroup
      g_coset := by
        rw [hA]
        exact coset_of_check QA45_ok QQ45_ok (fun q hq => cfQ_mem hq) cfCoset_ok
      τ_Q := cfTau_Q
      z_unique := z_unique_of_check QQ45_ok QL45_ok cfZ_ok
      R_unique := by rw [hA]; exact cfR_unique
      R_le := by rw [hA]; exact cfR_leA
      card_A := ⟨405, by decide, by
        rw [hA, card_group QA45 QA45_ok, QA45_valid.2]
        norm_num⟩
      card_D := ⟨cfCard_D, card_cfQR⟩
      Q_eq := cfQ_eq
      fix_τ := cfFix_tau
      g_z := cfComm_ok.2
      z_Q := cfZ_Q
      T₀ := cfQR.originalSubgroup
      T_le := by rw [hA]; exact cfR_le
      card_T := card_cfQR
      card_Ctz := ⟨9, by decide, by rw [hA]; exact cfCard_Ctz⟩
      tz_comm := cfTz_comm
      z_τ := by rw [hP]; exact cfZ_tau
      card_R0 := cfCard_R0
      card_Cz := ⟨3, by decide, by rw [hA]; exact cfCard_Cz⟩
      R0_decomp := cfR0_decomp
      R0_center := cfR0_center
      R0_gen := cfR0_gen
      E0 := by rw [hP, hA]; exact cfE0
      Z_R := cfZ_R
      no_E32 := cfNo_E32
      outer := by rw [hP, hA]; exact cfOuter
      inner := by rw [hP]; exact cfInner }

end CFSG.ComponentClassification.CatFactsSmall.PSp43
