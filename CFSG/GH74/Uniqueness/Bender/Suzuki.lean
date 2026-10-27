module

public import CFSG.GH74.Uniqueness.Bender.Embedding
public import CFSG.GH74.Uniqueness.Bender.Lemma32
public import CFSG.GH74.Uniqueness.SE
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.SzUModels
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.CharacterTheory.CyclicBlocks.Family
public import CFSG.CharacterTheory.PSL2Table.BlocksProduct
public import CFSG.CharacterTheory.Semidihedral.Principal.LargePrimeTorusSylowCentralizers
public import CFSG.CharacterTheory.Semidihedral.Principal.PrimeTorusBlockAlignment
public import CFSG.CharacterTheory.Wreathed.FourPointInvolutionHexagon
public import CFSG.CharacterTheory.Wreathed.OrderThirtyTwoWreathFusion
public import CFSG.Combinatorics.AperiodicCentralInvolution
public import CFSG.Combinatorics.AperiodicFiveOfSix
public import CFSG.Combinatorics.AperiodicOppositeComponents
public import CFSG.Combinatorics.AperiodicSixteenGraphDistances
public import CFSG.Combinatorics.OuterLayerPredecessors
public import CFSG.GH74.Statements
public import CFSG.LieType.CurtisTits.Conclusion
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNine
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.Permutation.UnitaryThreeRecognition.Model
public import CFSG.StronglyEmbedded.TheoremSE.BenderLowRank
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2NormalizedRootSylowCount

public section

namespace CFSG.GH74.Uniqueness.Bender

open Subgroup
open scoped commutatorElement
open CFSG.ProperTwoGeneratedCore.Lemma37

theorem sq_sq_eq_one_of_rootData {R : Type*} [Group R] [Finite R] {q n : ℕ}
    (hR : BenderRootData R q n) (hcard : Nat.card R = q + (q - 1) * n) :
    ∀ x : R, x ^ 2 ≠ 1 → (x ^ 2) ^ 2 = 1 := by
  classical
  have := Fintype.ofFinite R
  set Zs : Finset R := Finset.univ.filter (fun x => x ^ 2 = 1) with hZs
  have hZcard : Zs.card = q := by
    rw [← hR.card_sq_one, Nat.card_eq_fintype_card, Fintype.card_subtype]
  set B : Finset R := Finset.univ.filter (fun x => x ^ 2 ≠ 1 ∧ (x ^ 2) ^ 2 = 1) with hB
  set C : Finset R := Finset.univ.filter (fun x => x ^ 2 ≠ 1) with hC
  have h1Zs : (1 : R) ∈ Zs := by simp [hZs]
  have hCcard : C.card = (q - 1) * n := by
    have : C = Finset.univ \ Zs := by
      ext x
      simp [hC, hZs]
    rw [this, Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ,
      ← Nat.card_eq_fintype_card, hcard, hZcard]
    omega
  have hBcard : B.card = (q - 1) * n := by
    have hmaps : ∀ x ∈ B, x ^ 2 ∈ Zs.erase 1 := by
      intro x hx
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_erase, hZs, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx.1, hx.2⟩
    rw [Finset.card_eq_sum_card_fiberwise hmaps]
    have hfib : ∀ r ∈ Zs.erase 1, (B.filter (fun x => x ^ 2 = r)).card = n := by
      intro r hr
      simp only [Finset.mem_erase, hZs, Finset.mem_filter, Finset.mem_univ, true_and] at hr
      rw [← hR.card_sq r hr.1 hr.2, Nat.card_eq_fintype_card, Fintype.card_subtype]
      congr 1
      ext x
      simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨-, h2⟩
        exact h2
      · intro h2
        exact ⟨⟨by rw [h2]; exact hr.1, by rw [h2]; exact hr.2⟩, h2⟩
    rw [Finset.sum_congr rfl hfib, Finset.sum_const, smul_eq_mul,
      Finset.card_erase_of_mem h1Zs, hZcard]
  have hBC : B ⊆ C := by
    intro x hx
    simp only [hB, hC, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    exact hx.1
  have hBeqC : B = C := Finset.eq_of_subset_of_card_le hBC (by rw [hBcard, hCcard])
  intro x hx
  have hxC : x ∈ C := by simp [hC, hx]
  rw [← hBeqC] at hxC
  simp only [hB, Finset.mem_filter, Finset.mem_univ, true_and] at hxC
  exact hxC.2

section Irreducible

variable {K : Type*} [Group K]

theorem BenderCore.suzuki_irreducible [Finite K] {q : ℕ} {P : Subgroup K} {t : K}
    (hc : BenderCore q 2 1 P t) (hRD : BenderRootData P q q) {W : Subgroup K}
    (hZW : rootCenter P ≤ W) (hWP : W ≤ P) (hD : ∀ d ∈ cartan P t, ∀ w ∈ W, d * w * d⁻¹ ∈ W) :
    W = rootCenter P ∨ W = P := by
  by_cases hWZ : W = rootCenter P
  · exact Or.inl hWZ
  right
  obtain ⟨x, hxW, hxZ⟩ : ∃ x ∈ W, x ∉ rootCenter P := by
    by_contra hcon
    apply hWZ
    refine le_antisymm (fun x hx => ?_) hZW
    by_contra hxZ
    exact hcon ⟨x, hx, hxZ⟩
  have hq1 : 1 ≤ q := by
    have := Nat.card_pos (α := rootCenter P)
    rw [hc.card_center] at this
    exact this
  have hcardP : Nat.card ↥P = q + (q - 1) * q := by
    rw [hc.card_eq]
    obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
    simp only [Nat.add_sub_cancel]
    ring
  have hsq := sq_sq_eq_one_of_rootData hRD hcardP
  have hsqZ : ∀ y ∈ P, y ∉ rootCenter P → y * y ∈ rootCenter P ∧ y * y ≠ 1 := by
    intro y hyP hyZ
    have h1 : y * y ≠ 1 := fun h => hyZ (hc.mem_rootCenter_of_mul_self hyP h)
    refine ⟨hc.mem_rootCenter_of_mul_self (P.mul_mem hyP hyP) ?_, h1⟩
    have h2 := hsq ⟨y, hyP⟩ (fun h => h1 (by simpa [sq] using congrArg Subtype.val h))
    simpa [sq] using congrArg Subtype.val h2
  apply le_antisymm hWP
  intro y hyP
  by_cases hyZ : y ∈ rootCenter P
  · exact hZW hyZ
  obtain ⟨hr, hr1⟩ := hsqZ x (hWP hxW) hxZ
  obtain ⟨hr', hr1'⟩ := hsqZ y hyP hyZ
  obtain ⟨d, hd, hdd⟩ := hc.exists_cartan_conj hr hr1 hr' hr1'
  have hx' : d⁻¹ * x * d ∈ W := by
    have := hD d⁻¹ ((cartan P t).inv_mem hd) x hxW
    simpa using this
  have hx'P : d⁻¹ * x * d ∈ P := hWP hx'
  have hx'sq : (d⁻¹ * x * d) * (d⁻¹ * x * d) = y * y := by
    rw [hdd]; group
  set x' := d⁻¹ * x * d with hx'def
  have hrsq : (y * y) ^ 2 = 1 := by
    rw [sq]; exact hc.center_sq _ hr'
  have hS : Nat.card {u : K // u ∈ P ∧ u ^ 2 = y * y} = q := by
    rw [card_mem_sq_eq_card_subtype_sq P (P.mul_mem hyP hyP)]
    exact hRD.card_sq ⟨y * y, P.mul_mem hyP hyP⟩ (fun h => hr1' (congrArg Subtype.val h))
      (Subtype.ext (by simpa using hrsq))
  let f : rootCenter P → {u : K // u ∈ P ∧ u ^ 2 = y * y} := fun z =>
    ⟨x' * z, P.mul_mem hx'P (rootCenter_le P z.2), by
      have hcomm : x' * z = z * x' := (mem_rootCenter_iff.mp z.2).2 x' hx'P
      have hzz : (z : K) * z = 1 := hc.center_sq z z.2
      calc (x' * z) ^ 2 = x' * z * (x' * z) := sq _
        _ = x' * (z * x') * z := by group
        _ = x' * (x' * z) * z := by rw [hcomm]
        _ = (x' * x') * (z * z) := by group
        _ = y * y := by rw [hzz, hx'sq, mul_one]⟩
  have hfinj : Function.Injective f := fun a b hab =>
    Subtype.ext (mul_left_cancel (congrArg Subtype.val hab))
  have hfbij : Function.Bijective f :=
    hfinj.bijective_of_nat_card_le (by rw [hS, hc.card_center])
  obtain ⟨z, hz⟩ := hfbij.2 ⟨y, hyP, sq y⟩
  have hyz : x' * z = y := congrArg Subtype.val hz
  rw [← hyz]
  exact W.mul_mem hx' (hZW z.2)

end Irreducible

section SylowStructure

variable {K : Type*} [Group K]

theorem BenderCore.exponent_two_of_inf_eq [Finite K] {q i e : ℕ} {Q : Sylow 2 K} {t : K}
    (hc : BenderCore q i e (Q : Subgroup K) t) {L : Subgroup K}
    (hZL : rootCenter (Q : Subgroup K) ≤ L)
    (hLQ : (Q : Subgroup K) ⊓ L = rootCenter (Q : Subgroup K)) {T : Subgroup K} (hTL : T ≤ L)
    (hT2 : IsPGroup 2 T) : ∀ x ∈ T, x * x = 1 := by
  set Z := rootCenter (Q : Subgroup K) with hZ
  have hZ2 : IsPGroup 2 Z := fun g => ⟨1, Subtype.ext (by
    simpa [sq] using hc.center_sq g g.2)⟩
  have hZL2 : IsPGroup 2 (Z.subgroupOf L) :=
    hZ2.of_equiv (Subgroup.subgroupOfEquivOfLe hZL).symm
  have hTL2 : IsPGroup 2 (T.subgroupOf L) :=
    hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTL).symm
  obtain ⟨T₀, hT₀⟩ := hTL2.exists_le_sylow
  obtain ⟨T₁, hT₁⟩ := hZL2.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (↥L) T₁ T₀
  have hT₁sq : ∀ y ∈ (T₁ : Subgroup L), (y : K) * y = 1 := by
    set T₁' : Subgroup K := (T₁ : Subgroup L).map L.subtype with hT₁'
    have hT₁'2 : IsPGroup 2 T₁' := by
      obtain ⟨k, hk⟩ := T₁.isPGroup'.exists_card_eq
      refine IsPGroup.of_card (n := k) ?_
      rw [hT₁', Subgroup.card_map_of_injective L.subtype_injective]
      exact hk
    have hZT : Z ≤ T₁' := by
      intro z hz
      exact ⟨⟨z, hZL hz⟩, hT₁ hz, rfl⟩
    obtain ⟨Q₁, hQ₁⟩ := hT₁'2.exists_le_sylow
    obtain ⟨z₀, hz₀, hz₀1⟩ := hc.exists_involution
    have hQ₁Q : Q₁ = Q := by
      refine hc.sylow_eq_of_ne_bot (V := Z) ?_ (rootCenter_le _) (hZT.trans hQ₁)
      intro hbot
      have hz₀' : z₀ ∈ Z := hz₀
      rw [hbot] at hz₀'
      exact hz₀1 (Subgroup.mem_bot.mp hz₀')
    intro y hy
    have hyQ : (y : K) ∈ (Q : Subgroup K) := by
      rw [← hQ₁Q]
      exact hQ₁ ⟨y, hy, rfl⟩
    have hyZ : (y : K) ∈ Z := by
      rw [← hLQ]
      exact Subgroup.mem_inf.mpr ⟨hyQ, y.2⟩
    exact hc.center_sq _ hyZ
  intro x hx
  have hxL : x ∈ L := hTL hx
  have hxT₀ : (⟨x, hxL⟩ : L) ∈ (T₀ : Subgroup L) := hT₀ hx
  rw [← hg, mem_sylow_smul_iff] at hxT₀
  have h1 := hT₁sq _ hxT₀
  have h2 : ((g⁻¹ * ⟨x, hxL⟩ * g : L) : K) = (g : K)⁻¹ * x * g := rfl
  rw [h2] at h1
  calc x * x = (g : K) * ((g : K)⁻¹ * x * g * ((g : K)⁻¹ * x * g)) * (g : K)⁻¹ := by group
    _ = 1 := by rw [h1]; group

end SylowStructure

section StrongEmbedding

variable {K : Type*} [Group K]

theorem isStronglyEmbedded_subgroupOf [Finite K] {M L : Subgroup K} (hM : IsStronglyEmbedded M)
    {z : K} (hzM : z ∈ M) (hzL : z ∈ L) (hz2 : orderOf z = 2) {t : K} (htL : t ∈ L)
    (htM : t ∉ M) : IsStronglyEmbedded ((M ⊓ L).subgroupOf L) := by
  refine ⟨?_, ?_, ?_⟩
  · intro htop
    have : (⟨t, htL⟩ : L) ∈ (M ⊓ L).subgroupOf L := by rw [htop]; trivial
    exact htM (Subgroup.mem_inf.mp this).1
  · have hmem : (⟨z, hzL⟩ : L) ∈ (M ⊓ L).subgroupOf L := Subgroup.mem_inf.mpr ⟨hzM, hzL⟩
    have hord : orderOf (⟨z, hzL⟩ : L) = 2 := by
      rw [← Subgroup.orderOf_coe]; exact hz2
    exact even_iff_two_dvd.mpr (hord ▸ Subgroup.orderOf_dvd_natCard _ hmem)
  · intro g hg
    have hgM : (g : K) ∉ M := fun h => hg (Subgroup.mem_inf.mpr ⟨h, g.2⟩)
    have hodd := hM.2.2 g hgM
    have hdvd : Nat.card ↥((M ⊓ L).subgroupOf L ⊓ conjugate ((M ⊓ L).subgroupOf L) g) ∣
        Nat.card ↥(M ⊓ conjugate M (g : K)) := by
      rw [← Subgroup.card_map_of_injective (f := L.subtype) L.subtype_injective]
      apply Subgroup.card_dvd_of_le
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
      refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hy1).1, ?_⟩
      rw [mem_conjugate_iff_mul_inv]
      have h3 : g * y * g⁻¹ ∈ (M ⊓ L).subgroupOf L := mem_conjugate_iff_mul_inv.mp hy2
      have h4 : ((g * y * g⁻¹ : L) : K) ∈ M ⊓ L := h3
      exact (Subgroup.mem_inf.mp h4).1
    exact Odd.of_dvd_nat hodd hdvd

end StrongEmbedding

section Main

theorem BenderType.suzuki_rootData {K : Type*} [Group K] {n : ℕ} (h : BenderType K n 2 1)
    (Q : Sylow 2 K) : BenderRootData (Q : Subgroup K) (2 ^ n) (2 ^ n) := by
  cases h with
  | suzuki a ha e =>
    exact (benderRootData_of_mulEquiv_suzukiMatrixGroup a ha
      (e.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a))) Q).1

theorem BenderType.lemma_3_2_h_suzuki
    {K : Type} [Group K] [Finite K] {n : ℕ}
    (h : BenderType K n 2 1) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) {z : K} (hz : z ∈ rootCenter (Q : Subgroup K))
    (hz1 : z ≠ 1) :
    Subgroup.closure ({z, t} : Set K) ⊔ ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ = ⊤ := by
  have hc := h.benderCore Q ht htQ
  have hsimple : IsSimpleGroup K := h.isSimple
  have hRD := h.suzuki_rootData Q
  obtain ⟨a, ha, hn⟩ : ∃ a, 1 ≤ a ∧ n = 2 * a + 1 := by
    rcases h.cases' with ⟨hi, -, -⟩ | ⟨-, -, a, ha, hn⟩ | ⟨hi, -, -⟩
    · omega
    · exact ⟨a, ha, hn⟩
    · omega
  set L : Subgroup K := Subgroup.closure ({z, t} : Set K) ⊔
    ⁅cartan (Q : Subgroup K) t, Subgroup.zpowers t⁆ with hL
  have hZL : rootCenter (Q : Subgroup K) ≤ L := hc.rootCenter_le_sup hz hz1
  have htL : t ∈ L := Subgroup.mem_sup_left (Subgroup.subset_closure (by simp))
  have hzL : z ∈ L := hZL hz
  have hDL : cartan (Q : Subgroup K) t ≤ L :=
    (hc.cartan_eq_commutator rfl).le.trans le_sup_right
  have hirr := hc.suzuki_irreducible hRD (W := (Q : Subgroup K) ⊓ L)
    (le_inf (rootCenter_le _) hZL) inf_le_left (by
      intro d hd w hw
      refine Subgroup.mem_inf.mpr ⟨?_, L.mul_mem (L.mul_mem (hDL hd) hw.2) (L.inv_mem (hDL hd))⟩
      exact (Subgroup.mem_normalizer_iff.mp (cartan_le_borel _ t hd) w).mp hw.1)
  rcases hirr with hWZ | hWQ
  · exfalso
    have hexp := fun {T : Subgroup K} (hTL : T ≤ L) (hT2 : IsPGroup 2 T) =>
      hc.exponent_two_of_inf_eq hZL hWZ hTL hT2
    have hz2 : orderOf z = 2 := by
      apply orderOf_eq_prime _ hz1
      rw [sq]
      exact hc.center_sq z hz
    have hMX : IsStronglyEmbedded ((borel (Q : Subgroup K) ⊓ L).subgroupOf L) :=
      isStronglyEmbedded_subgroupOf hc.strong (le_borel _ (rootCenter_le _ hz)) hzL hz2 htL htQ
    rcases S_SE_proof ↥L _ hMX with hrank | ⟨hBender, -, -⟩
    ·
      have hZLcard : Nat.card ((rootCenter (Q : Subgroup K)).subgroupOf L) = 2 ^ n := by
        rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZL).toEquiv, hc.card_center]
      have hZsq : ∀ x : ↥L, x ∈ (rootCenter (Q : Subgroup K)).subgroupOf L → x * x = 1 := by
        intro x hx
        exact Subtype.ext (hc.center_sq _ hx)
      have hE : CFSG.Open.IsElemAbelian 2 ((rootCenter (Q : Subgroup K)).subgroupOf L) := by
        refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
        · apply Subtype.ext
          apply Subtype.ext
          have ha := mem_rootCenter_iff.mp x.2
          have hb := mem_rootCenter_iff.mp y.2
          exact hb.2 _ ha.1
        · rw [sq]
          exact hZsq x hx
      have hEle : (rootCenter (Q : Subgroup K)).subgroupOf L ≤ involutionClosure ↥L := by
        intro x hx
        by_cases hx1 : x = 1
        · rw [hx1]; exact one_mem _
        · apply Subgroup.subset_closure
          show orderOf x = 2
          apply orderOf_eq_prime _ hx1
          rw [sq]
          exact hZsq x hx
      have := CFSG.SectionRank.le_pRank (by norm_num : 1 < 2) hEle hE hZLcard
      omega
    ·
      obtain ⟨n', i', e', hS⟩ := isBenderGroup_iff_exists_benderType.mp hBender
      set Xc : Subgroup ↥L := involutionClosure ↥L with hXc
      let Tc : Sylow 2 ↥Xc := default
      let Q' := Sylow.mapSurjective (QuotientGroup.mk'_surjective
        (pPrimeCore 2 ↥Xc)) Tc
      have hQ'sq : ∀ x ∈ (Q' : Subgroup (↥Xc ⧸ pPrimeCore 2 ↥Xc)), x * x = 1 := by
        intro x hx
        rw [Sylow.coe_mapSurjective] at hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
        set T : Subgroup K := ((Tc : Subgroup ↥Xc).map Xc.subtype).map L.subtype with hT
        have hTL : T ≤ L := by
          rintro _ ⟨w, -, rfl⟩
          exact w.2
        have hT2 : IsPGroup 2 T := by
          obtain ⟨k, hk⟩ := Tc.isPGroup'.exists_card_eq
          refine IsPGroup.of_card (n := k) ?_
          rw [hT, Subgroup.card_map_of_injective L.subtype_injective,
            Subgroup.card_map_of_injective Xc.subtype_injective]
          exact hk
        have hyT : (((y : ↥Xc) : ↥L) : K) ∈ T := ⟨(y : ↥L), ⟨y, hy, rfl⟩, rfl⟩
        have h1 := hexp hTL hT2 _ hyT
        have h2 : y * y = 1 := Subtype.ext (Subtype.ext h1)
        change QuotientGroup.mk' _ y * QuotientGroup.mk' _ y = 1
        rw [← map_mul, h2, map_one]
      obtain ⟨t', hc'⟩ := hS.exists_benderCore Q'
      have hi' : i' = 1 := by
        by_contra hne
        have hle : (Q' : Subgroup (↥Xc ⧸ pPrimeCore 2 ↥Xc)) ≤
            rootCenter (Q' : Subgroup (↥Xc ⧸ pPrimeCore 2 ↥Xc)) :=
          hc'.elemAbelian_le_rootCenter le_rfl hQ'sq
        have hdvd := Subgroup.card_dvd_of_le hle
        rw [hc'.card_eq, hc'.card_center] at hdvd
        have hi2 : 2 ≤ i' := by
          have := hS.two_le.1
          omega
        have hn2 : 2 ≤ n' := hS.two_le.2
        have hq2 : 4 ≤ 2 ^ n' := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ n' := Nat.pow_le_pow_right (by norm_num) hn2
        have hle2 := Nat.le_of_dvd (by positivity) hdvd
        have h3 : (2 ^ n') ^ 2 ≤ (2 ^ n') ^ i' := Nat.pow_le_pow_right (by omega) hi2
        have h4 : 2 ^ n' < (2 ^ n') ^ 2 := by
          rw [sq]; nlinarith
        omega
      subst hi'
      have he' : e' = 1 := by
        rcases hS.cases' with ⟨-, he, -⟩ | ⟨hi, -, -⟩ | ⟨hi, -, -⟩
        · exact he
        · omega
        · omega
      subst he'
      have h3S : 3 ∣ Nat.card (↥Xc ⧸ pPrimeCore 2 ↥Xc) := by
        rw [hS.card_eq]
        exact three_dvd_linear_card n'
      have h3K : 3 ∣ Nat.card K :=
        h3S.trans ((Subgroup.card_quotient_dvd_card _).trans
          ((Subgroup.card_subgroup_dvd_card Xc).trans (Subgroup.card_subgroup_dvd_card L)))
      rw [h.card_eq, hn] at h3K
      exact not_three_dvd_sz_card a h3K
  · have hQL : (Q : Subgroup K) ≤ L := by
      intro x hx
      have : x ∈ (Q : Subgroup K) ⊓ L := by rw [hWQ]; exact hx
      exact this.2
    rw [eq_top_iff, ← hc.sup_zpowers_eq_top htQ]
    exact sup_le hQL (Subgroup.zpowers_le.mpr htL)

end Main

end CFSG.GH74.Uniqueness.Bender
