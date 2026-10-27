module

public import CFSG.ClassicalInvolution.Q3.TL4S289U3
public import CFSG.ClassicalInvolution.Q3.TL4S289U2
public import CFSG.ClassicalInvolution.Q3.TL4S289Z
public import CFSG.ClassicalInvolution.Q3.TL4S3Dich

public section

namespace CFSG.ClassicalInvolution.Q3.TL4

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Balance
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.Blueprint
open CFSG.ClassicalInvolution.Disconnected (DConnected)

namespace S289

section Shape

variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem isPGroup_of_q8Shape {c : CompData} (h : SecIdQ8Shape c Φ) {M : Subgroup X}
    (hM : M ∈ Φ) : IsPGroup 2 ↥M := by
  obtain ⟨ψ, -, -, hfund⟩ := h
  obtain ⟨R', -, hR'⟩ := hfund M hM
  exact hR'.2.1

end Shape

section CitL


variable {X : Type} [Group X] {Φ : Set (Subgroup X)}

theorem isPGroup_of_lieS3 (h : SecIdLieS3 Φ) {M : Subgroup X} (hM : M ∈ Φ) : IsPGroup 2 ↥M := by
  rcases h with h | h | h
  · exact isPGroup_of_q8Shape h hM
  · exact isPGroup_of_q8Shape h hM
  · exact isPGroup_of_q8Shape h hM

theorem lieModel_quot_center_of_q8Shape {tg : CFSG.Assembly.LowTwoRank.StatedLieTag} {k : ℕ}
    (hFT : IsFundTag tg) (hadm : CFSG.Assembly.LowTwoRank.StatedLieAdmissible tg k 3 1)
    (h : SecIdQ8Shape (CompData.model tg k) Φ) :
    LieModel (X ⧸ Subgroup.center X) tg k 3 1 := by
  obtain ⟨ψ, hψ, hker, -⟩ := h
  obtain ⟨-, hsurj, hker', -, hZ⟩ := Q3NM.centralQuotientData Nat.prime_three hFT hadm X ψ hψ hker
  set ψ' := (QuotientGroup.mk' (Subgroup.center X)).comp ψ with hψ'
  have hkeq : ψ'.ker = Subgroup.center (modelUniv tg k 3 1 Nat.prime_three).K := by
    refine le_antisymm hker' fun z hz => ?_
    have h1 : ψ' z ∈ Subgroup.center (X ⧸ Subgroup.center X) :=
      Subgroup.mem_center_iff.mpr fun y => by
        obtain ⟨y, rfl⟩ := hsurj y
        rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz y]
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  have e : (modelUniv tg k 3 1 Nat.prime_three).K ⧸
      Subgroup.center (modelUniv tg k 3 1 Nat.prime_three).K ≃* X ⧸ Subgroup.center X :=
    (QuotientGroup.quotientMulEquivOfEq hkeq.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ' hsurj)
  exact LieType.CurtisTits.lieModel_of_mulEquiv e
    (ModelFacts.modelClauseZero tg k 3 1 Nat.prime_three hFT hadm).2

theorem centOmega3_of_lieS4 (h : SecIdLieS4 Φ) : PhilipHall.Frame.CentOmega3 X := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (Or.inl (lieModel_quot_center_of_q8Shape (tg := .PSU) (k := 4) trivial
      ⟨Nat.prime_three, le_rfl, by norm_num, by decide⟩ h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨3, le_rfl, lieModel_quot_center_of_q8Shape
      (tg := .POmegaOdd) (k := 3) trivial ⟨Nat.prime_three, le_rfl, le_rfl, by norm_num⟩ h⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨4, le_rfl, lieModel_quot_center_of_q8Shape
      (tg := .POmegaMinus) (k := 4) trivial ⟨Nat.prime_three, le_rfl, le_rfl⟩ h⟩))))

end CitL

section Cit3


variable {r n : ℕ} {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem linkDichSyl_of_lieS3
    (hk : SecIdLieS3 (restrictFamily (coreLinkFam R t) (linkGrp R t))) : LinkDichSyl R t := by
  intro M hM a ha P hP β hβ2 hβP
  have hPM : M = P := hP.2.2 M le_rfl (isPGroup_of_lieS3 hk hM) hP.1
  exact secIdS3Dich3_proved _ _ hk M hM a ha β hβ2 fun x hx => hβP x (hPM ▸ hx)

theorem linkDichSyl_of_exit (hX : SecIdExitDich3) (hIF : SecIdExitS3IdentF n)
    (hL : TightLargeHypR 3 n Y R S t)
    (htr : ∀ L ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
      ∀ L' ∈ restrictFamily (coreLinkFam R t) (linkGrp R t),
        ∃ g : ↥(linkGrp R t), conjSub g L = L')
    (hk : SecIdExitS3 (restrictFamily (coreLinkFam R t) (linkGrp R t))) : LinkDichSyl R t := by
  have hΦ := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  exact hX _ _ hΦ (oddCore_linkGrp_eq_bot hL) omegaGen_linkRestrict htr hk
    (hIF _ (natCard_linkGrp_lt hL) _ hΦ (oddCore_linkGrp_eq_bot hL) omegaGen_linkRestrict htr hk)

theorem tfree_at_t (hL : TightLargeHypR 3 n Y R S t) (hcase : LinkS3S4 R t)
    (hOm : OmegaAutOddFreeR) (hX : SecIdExitDich3) (hIF : SecIdExitS3IdentF n)
    {J' K''' : Subgroup Y} {t' w' : Y}
    (hJ' : J' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) (tightCore R))
    (ht' : IsUniqueInvolution J' t')
    (hK : K''' ∈ omegaNbr (CoreAssembly.conjClass (tightCore R)) J')
    (hw : IsUniqueInvolution K''' w') (ht'C : t' ∈ Subgroup.centralizer ({t} : Set Y))
    (hwt : w' ∈ Subgroup.centralizer ({t} : Set Y)) {L : Subgroup (OddQuot t)}
    (hLc : IsComponent L)
    (hmt : ∃ y ∈ L, oddQuotMk t ⟨t', ht'C⟩ * y ≠ y * oddQuotMk t ⟨t', ht'C⟩)
    (hmw : ∃ y ∈ L, oddQuotMk t ⟨w', hwt⟩ * y ≠ y * oddQuotMk t ⟨w', hwt⟩)
    (hmtw : ∃ y ∈ L, oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩ * y ≠
      y * (oddQuotMk t ⟨t', ht'C⟩ * oddQuotMk t ⟨w', hwt⟩)) :
    Q3NM.AutOddFree ↥L ∧ oddQuotMk t ⟨t', ht'C⟩ ∈ Subgroup.normalizer (L : Set (OddQuot t)) := by
  obtain ⟨htr, -, hkind⟩ := hcase
  have htt' : t * t' = t' * t :=
    Q3CL.T8.mul_comm_of_mem_omegaNbr hL.datum.hypOmegaGen hL.datum.isUniqueInvolution_core hJ' ht'
  have ht'Λ : t' ∈ linkLayer R t := coreAt_le_linkLayerAt hJ' (mem_coreAt_of_sq_sq ht'.mem
    (by rw [ht'.sq, one_mul]) htt'.symm)
  have ht'N' : oddQuotMk t ⟨t', ht'C⟩ ∈ modOdd t (linkLayer R t) :=
    oddQuotMk_mem_modOdd ht'Λ ht'C
  have hN : ∀ c ∈ Subgroup.centralizer ({t} : Set Y), ∀ y ∈ linkLayer R t,
      c * y * c⁻¹ ∈ linkLayer R t := fun _ hc _ hy => conj_mem_linkLayer hL hc hy
  have hLN : L ≤ modOdd t (linkLayer R t) := le_of_moved (modOdd_normal hN) hLc ht'N' hmt
  set e := linkVtxEquiv hL with he
  have hC : IsComponent ((L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv e (LocalCores.component_overgroup hLc hLN)
  have hΦ := (typeRFam_coreLinkFam hL).restrict (linkGrp R t)
  have hJm := subgroupOf_mem_linkRestrict (t := t) hJ'
  have hau := isUniqueInvolution_link_of hL hJ' ht' ht'Λ
  set eL : ↥L ≃* ↥((L.subgroupOf (modOdd t (linkLayer R t))).map e.toMonoidHom) :=
    (Subgroup.subgroupOfEquivOfLe hLN).symm.trans
      ((L.subgroupOf (modOdd t (linkLayer R t))).equivMapOfInjective e.toMonoidHom e.injective)
    with heL
  rcases hkind with hk | hk | hk | hk | hk | hk | hk
  · exact (false_of_linkDich hL (linkDichSyl_of_lieS3 hk) hJ' ht' hK hw ht'C hwt hLc hmt hmw
      hmtw).elim
  ·
    obtain ⟨hq, -⟩ := lie_facts_of (Or.inr hk)
    have hLeq := eq_of_isQuasisimple linkLayerAt_le_centralizer hN
      (LocalCores.isQuasisimple_of_mulEquiv (linkLayerEquiv hL).symm hq) hLc hLN
    have hAOF : Q3NM.AutOddFree ↥(linkGrp R t) :=
      Vtx.autOddFree_of_quot_center hq.1 (hOm _ (centOmega3_of_lieS4 hk))
    refine ⟨Q3NM.AutOddFree.of_mulEquiv (e.symm.trans (MulEquiv.subgroupCongr hLeq.symm)) hAOF,
      ?_⟩
    rw [hLeq]
    exact Subgroup.le_normalizer ht'N'
  · exact (false_of_linkDich hL (linkDichSyl_of_exit hX hIF hL htr hk) hJ' ht' hK hw ht'C hwt
      hLc hmt hmw hmtw).elim
  · exact (e8_not_isComponent hk.1 hC).elim
  · exfalso
    obtain ⟨y, hy, hne⟩ := hmt
    exact hne (commute_of_map e hLN ht'N'
      (e64_commute omegaGen_linkRestrict hk.1 hC hJm hau) y hy)
  · have hS : IsSimpleGroup (↥(linkGrp R t) ⧸ Subgroup.center ↥(linkGrp R t)) :=
      Vtx.isSimpleGroup_of_exLie (Or.inl hk.2.1)
    exact ⟨Q3NM.AutOddFree.of_mulEquiv eL.symm (sp6_autOddFree hk.2.1 hC),
      mem_normalizer_of_map e hLN (normal_of_simple_quot hS hC) ht'N'⟩
  · exfalso
    obtain ⟨y, hy, hne⟩ := hmt
    exact hne (commute_of_map e hLN ht'N' (wNormal_commute hΦ.hyp hk.1 hC hJm hau) y hy)

end Cit3

end S289

section Cit3


variable {n : ℕ}

theorem tightStar289TFreeR_of (hOm : OmegaAutOddFreeR) (hX : SecIdExitDich3)
    (hIF : SecIdExitS3IdentF n) : TightStar289TFreeR 3 n := by
  intro Y _ _ R S t hL _ _ hcase J K'' u w hF htu L hLc hm _
  have ht := hL.datum.isUniqueInvolution_core
  have hB := hF.isElemAbelian hL
  have hm3 := mem_closure_three_left t u w
  have hncl := hF.not_mem_closure hL
  have hwu : w ∈ Subgroup.centralizer ({u} : Set Y) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hF.comm_uw hL).symm
  have hct : t ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have hcu : u ∈ Subgroup.closure ({t, u} : Set Y) := Subgroup.subset_closure (by simp)
  have htu' : t ≠ u := fun e =>
    hF.memJ.2.1 (eq_core_of_isUniqueInvolution hL hF.memJ.1 (e ▸ hF.invJ))
  have hwu' : w ≠ u := fun e => hncl (e ▸ hcu)
  have htw1 : t * w ≠ 1 := fun e => hncl ((eq_inv_of_mul_eq_one_right e) ▸ Subgroup.inv_mem _ hct)
  have htwu : t * w ≠ u := fun e => hncl (by
    rw [show w = t⁻¹ * u by rw [← e]; group]
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hct) hcu)
  have htwB := Subgroup.mul_mem _ hm3.1 hm3.2.2
  have htwC : t * w ∈ Subgroup.centralizer ({u} : Set Y) := Subgroup.mul_mem _ htu hwu
  have hmt := hm _ (oddQuotMk_mem_modOdd hm3.1 htu)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one hm3.1 ht.ne_one htu' htu)
  have hmw := hm _ (oddQuotMk_mem_modOdd hm3.2.2 hwu)
    (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one hm3.2.2 hF.invK.ne_one
      hwu' hwu)
  have hmtw : ∃ y ∈ L, oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩ * y ≠
      y * (oddQuotMk u ⟨t, htu⟩ * oddQuotMk u ⟨w, hwu⟩) := by
    rw [← map_mul]
    exact hm _ (oddQuotMk_mem_modOdd htwB htwC)
      (Lemma52Proof.oddQuotMk_not_mem_zpowers hB hm3.2.1 hF.invJ.ne_one htwB htw1 htwu htwC)
  obtain ⟨hAOF, hNt⟩ := S289.vertexU_cps hL hF.memJ hF.invJ hF.memK hF.invK htu hwu hLc hmt hmw
    hmtw (C := Q3NM.AutOddFree ↥L ∧
      oddQuotMk u ⟨t, htu⟩ ∈ Subgroup.normalizer (L : Set (OddQuot u)))
    fun _ _ _ _ hJ' ht' hK' hw' ht'C hwt _ hL'c hmt' hmw' hmtw' hA hN =>
      let h := S289.tfree_at_t hL hcase hOm hX hIF hJ' ht' hK' hw' ht'C hwt hL'c hmt' hmw' hmtw'
      ⟨hA h.1, hN h.2⟩
  exact S289.alphaOf_eq_bot_of_autFree hB hAOF hm3.1 htu hNt hmt

end Cit3

end CFSG.ClassicalInvolution.Q3.TL4
