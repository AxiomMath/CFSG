module

public import CFSG.ClassicalInvolution.Asc77.WP3ChainVRank3

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG CFSG.Open CFSG.ComponentClassification CFSG.ClassicalInvolution
  CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.Generic.DeltaClosure
  CFSG.ClassicalInvolution.Generic.CoreAssembly CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Asc77.ExactLayer
  CFSG.ClassicalInvolution.Disconnected
open CFSG.Assembly.LowTwoRank

section Lift

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {a : G}

theorem exists_lift_centralizer_of_normalizes {E : Subgroup G} (hE2 : ∀ e ∈ E, e * e = 1)
    (hEC : E ≤ Subgroup.centralizer ({a} : Set G))
    (hEN : E ≤ Subgroup.normalizer ((centLayer Ω a : Subgroup G) : Set G)) {q : OddQuot a}
    (hq : q ∈ memberJoin Ω a)
    (hcent : ∀ (e : G) (_ : e ∈ E) (hC : e ∈ Subgroup.centralizer ({a} : Set G)),
      oddQuotMk a ⟨e, hC⟩ * q = q * oddQuotMk a ⟨e, hC⟩) :
    ∃ (y : G) (hyC : y ∈ Subgroup.centralizer ({a} : Set G)), y ∈ centLayer Ω a ∧
      y ∈ Subgroup.centralizer (E : Set G) ∧ oddQuotMk a ⟨y, hyC⟩ = q := by
  set C : Subgroup G := Subgroup.centralizer ({a} : Set G) with hC
  have hYC : centLayer Ω a ≤ C := centLayer_le_centralizer Ω a
  have hker : Odd (Nat.card (oddQuotMk a).ker) := by
    rw [show (oddQuotMk a).ker = componentClassificationOddCore ↥C from
      QuotientGroup.ker_mk' _]
    exact OddCore.odd_card _
  have hnorm : E.subgroupOf C ≤
      Subgroup.normalizer (((centLayer Ω a).subgroupOf C : Subgroup ↥C) : Set ↥C) := by
    intro e he
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have := Subgroup.mem_normalizer_iff.mp (hEN (Subgroup.mem_subgroupOf.mp he)) (h : G)
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
    exact this
  have key := map_inf_centralizer_eq (oddQuotMk a) hker (E.subgroupOf C)
    ((centLayer Ω a).subgroupOf C)
    (isPGroup_two_of_sq_eq_one fun x hx => Subtype.ext (hE2 _ (Subgroup.mem_subgroupOf.mp hx)))
    hnorm
  have hqmem : q ∈ ((centLayer Ω a).subgroupOf C).map (oddQuotMk a) ⊓
      Subgroup.centralizer ((E.subgroupOf C).map (oddQuotMk a) : Set (OddQuot a)) := by
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · rw [← range_layerToOddQuot_eq] at hq
      obtain ⟨y, rfl⟩ := hq
      exact ⟨⟨y, centLayer_le_centralizer Ω a y.2⟩, y.2, rfl⟩
    · rintro _ ⟨e, he, rfl⟩
      exact hcent e (Subgroup.mem_subgroupOf.mp he) e.2
  rw [← key] at hqmem
  obtain ⟨g, ⟨hgY, hgE⟩, hgq⟩ := hqmem
  refine ⟨g, g.2, Subgroup.mem_subgroupOf.mp hgY, fun e he => ?_, hgq⟩
  have := Subgroup.mem_centralizer_iff.mp hgE ⟨e, hEC he⟩ (Subgroup.mem_subgroupOf.mpr he)
  exact congrArg Subtype.val this

end Lift

section Gen

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)} {z : G}

theorem mem_normalizer_exactLayer (hΩ : ConjInvariant Ω) {n : G}
    (hn : n ∈ Subgroup.centralizer ({z} : Set G)) :
    n ∈ Subgroup.normalizer ((exactLayer Ω z : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff_conjSub_eq]
  have h := exactLayer_conj hΩ n z
  rw [conj_eq_of_mem_centralizer_singleton hn] at h
  exact h.symm

theorem ChainCtx.mem_modOdd_of_commutes' (C : ChainCtx p f Ω z) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hzB : z ∈ B) {e : G} (heB : e ∈ B) (he1 : e ≠ 1) (hez : e ≠ z)
    {q : OddQuot z} (hq : q ∈ memberJoin (exactFamily Ω z) z)
    (hcomm : ∀ he : e ∈ Subgroup.centralizer ({z} : Set G),
      oddQuotMk z ⟨e, he⟩ * q = q * oddQuotMk z ⟨e, he⟩) :
    q ∈ modOdd z (⨆ F ∈ signalizerFunctorEk 2 2 B,
      (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z)) := by
  have hz1 : z ≠ 1 := C.hKz.ne_one
  have hBC : B ≤ Subgroup.centralizer ({z} : Set G) := Lemma52Proof.le_centralizer_of_mem hB hzB
  have hcB : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => comm_of_mem_elemAbelian hB hx hy
  have hsqB : ∀ x ∈ B, x * x = 1 := fun x hx => by rw [← pow_two]; exact hB.2 x hx
  have hesq : e * e = 1 := hsqB e heB
  have hze : z * e = e * z := hcB z hzB e heB
  set F : Subgroup G := Subgroup.closure ({z, e} : Set G) with hF
  have hFB : F ≤ B := by
    rw [hF, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hzB
    · exact heB
  have hcard : Nat.card F = 4 :=
    card_closure_pair_eq_four C.hKz.sq hesq hz1 he1 (fun h => hez h.symm) hze
  have hFE : F ∈ signalizerFunctorEk 2 2 B := ⟨hFB, by rw [hcard]; norm_num⟩
  have hF2 : ∀ x ∈ F, x * x = 1 := fun x hx => hsqB x (hFB hx)
  have hFC : F ≤ Subgroup.centralizer ({z} : Set G) := hFB.trans hBC
  have hFN : F ≤ Subgroup.normalizer ((exactLayer Ω z : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_exactLayer C.hΩ.conjInvariant (hFC hx)
  have hcent : ∀ (x : G) (_ : x ∈ F) (hC : x ∈ Subgroup.centralizer ({z} : Set G)),
      oddQuotMk z ⟨x, hC⟩ * q = q * oddQuotMk z ⟨x, hC⟩ := by
    refine ChainFrame.commutes_of_closure (oddQuotMk z) q (S := ({z, e} : Set G)) ?_ ?_
    · rintro s (rfl | rfl)
      · exact ChainLift.hzC
      · exact hBC heB
    · rintro s (rfl | rfl) hs
      · exact oddQuotMk_central ChainLift.hzC q
      · exact hcomm hs
  obtain ⟨y, hyC, hyY, hyF, hyq⟩ :=
    exists_lift_centralizer_of_normalizes (a := z) hF2 hFC hFN hq hcent
  have hle : (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) ≤
      ⨆ F ∈ signalizerFunctorEk 2 2 B, (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) :=
    le_iSup₂ (f := fun F (_ : F ∈ signalizerFunctorEk 2 2 B) =>
      Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) F hFE
  exact ⟨⟨y, hyC⟩, Subgroup.mem_subgroupOf.mpr (hle ⟨hyF, hyY⟩), hyq⟩

theorem ChainCtx.generation_of_not_movedByAll (C : ChainCtx p f Ω z) {B : Subgroup G}
    (hB : IsElemAbelian 2 B) (hzB : z ∈ B)
    (hnot : ∀ j : Fin C.D.card, ¬ MovedByAll B z (C.psi j).range) :
    CentralizerGenerationStar Ω B z := by
  classical
  set H : Subgroup G := ⨆ F ∈ signalizerFunctorEk 2 2 B,
    (Subgroup.centralizer (F : Set G) ⊓ exactLayer Ω z) with hH
  have hHY : H ≤ exactLayer Ω z := iSup₂_le fun F _ => inf_le_right
  have hψ : ∀ (j : Fin C.D.card) (k : (compModel C.D j).K), C.psi j k ∈ modOdd z H := by
    intro j k
    obtain ⟨x, hxB, hxZ, hx⟩ : ∃ x ∈ modOdd z B, x ∉ modOdd z (Subgroup.zpowers z) ∧
        ∀ y ∈ (C.psi j).range, x * y = y * x := by
      by_contra hcon
      apply hnot j
      unfold MovedByAll
      intro x hx hxZ
      by_contra hne
      push Not at hne
      exact hcon ⟨x, hx, hxZ, hne⟩
    obtain ⟨e, heB, rfl⟩ := mem_modOdd_iff.mp hxB
    have he1 : (e : G) ≠ 1 := by
      intro h
      apply hxZ
      have : e = 1 := Subtype.ext h
      rw [this, map_one]
      exact Subgroup.one_mem _
    have hez : (e : G) ≠ z := by
      intro h
      apply hxZ
      have : e = ⟨z, ChainLift.hzC⟩ := Subtype.ext h
      rw [this]
      exact oddQuotMk_mem_modOdd (Subgroup.mem_zpowers z) ChainLift.hzC
    exact C.mem_modOdd_of_commutes' hB hzB heB he1 hez (C.psi_mem_memberJoin j k)
      fun he => hx _ ⟨k, rfl⟩
  have hgen : ∀ x : ↥(exactLayer Ω z) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω z),
      sectionQuotientHom C.hs.normalizes x ∈ modOdd z H := by
    have hle : (⨆ i, (C.D.hom i).range) ≤
        (modOdd z H).comap (sectionQuotientHom C.hs.normalizes) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨k, rfl⟩
      exact hψ j k
    intro x
    exact hle (by rw [C.D.generate]; exact Subgroup.mem_top x)
  intro y hy
  obtain ⟨c, hcH, hc⟩ := hgen (QuotientGroup.mk' _ ⟨y, hy⟩)
  have hcH' : (c : G) ∈ H := Subgroup.mem_subgroupOf.mp hcH
  have hcY : (c : G) ∈ exactLayer Ω z := hHY hcH'
  have heq : oddQuotMk z ⟨y, exactLayer_le_centralizer Ω z hy⟩ =
      oddQuotMk z ⟨c, exactLayer_le_centralizer Ω z hcY⟩ := by
    have h1 : sectionQuotientHom C.hs.normalizes (QuotientGroup.mk' _ ⟨y, hy⟩) =
        oddQuotMk z ⟨y, exactLayer_le_centralizer Ω z hy⟩ := rfl
    rw [← h1, ← hc]
  have hker : (⟨y, hy⟩ : ↥(exactLayer Ω z)) * ⟨c, hcY⟩⁻¹ ∈
      (layerToOddQuot (exactFamily Ω z) z).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, layerToOddQuot_apply, layerToOddQuot_apply]
    exact mul_inv_eq_one.mpr heq
  rw [ker_layerToOddQuot_of_normalizes C.hs.normalizes] at hker
  have hmem := mem_oddCoreIn_of_mem_classicalInvolutionOddCore hker
  have hmem' : y * (c : G)⁻¹ ∈ oddCoreIn (exactLayer Ω z) := by
    have : ((⟨y, hy⟩ * ⟨c, hcY⟩⁻¹ : ↥(exactLayer Ω z)) : G) = y * (c : G)⁻¹ := by simp
    rwa [this] at hmem
  have e : y = (y * (c : G)⁻¹) * c := by group
  rw [e]
  exact mul_mem (Subgroup.mem_sup_left hmem') (Subgroup.mem_sup_right hcH')

end Gen

section Conj

variable {G : Type} [Group G] [Finite G] {Ω : Set (Subgroup G)}

theorem centralizerGenerationStar_conj (hΩ : ConjInvariant Ω) (g : G) {A : Subgroup G} {a : G}
    (h : CentralizerGenerationStar Ω A a) :
    CentralizerGenerationStar Ω (conjSub g A) (g * a * g⁻¹) := by
  unfold CentralizerGenerationStar at h ⊢
  rw [exactLayer_conj hΩ g a, oddCoreIn_conjSub_eq]
  refine le_trans (conjSub_mono h) ?_
  unfold conjSub
  rw [Subgroup.map_sup, Subgroup.map_iSup]
  refine sup_le_sup_left (iSup_le fun F => ?_) _
  rw [Subgroup.map_iSup]
  refine iSup_le fun hF => ?_
  have hF' : (F.map (MulAut.conj g).toMonoidHom) ∈ signalizerFunctorEk 2 2
      (A.map (MulAut.conj g).toMonoidHom) :=
    ⟨Subgroup.map_mono hF.1, by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]; exact hF.2⟩
  refine le_iSup₂_of_le (F.map (MulAut.conj g).toMonoidHom) hF' ?_
  refine le_trans (Subgroup.map_inf_le _ _ _) (inf_le_inf ?_ le_rfl)
  rintro _ ⟨c, hc, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨f, hf, rfl⟩
  have := Subgroup.mem_centralizer_iff.mp hc f hf
  simp only [MulEquiv.coe_toMonoidHom, ← map_mul]
  rw [this]

end Conj

section GenT

variable {p f : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
  {Ω : Set (Subgroup G)} {K J K' : Subgroup G} {z t z' : G}

theorem chainFrameGenT_rank3 (hs : ChainFrameSetting p f Ω K J K' z t z')
    (hr3 : ChainShapeRank p f 3 Ω z) :
    CentralizerGenerationStar Ω (Subgroup.closure ({z, t, z'} : Set G)) t := by
  obtain ⟨C, g, hgt, hB, -, hzB, -, hnot⟩ := chainFrame_rank3_conj hs hr3
  have h1 := C.generation_of_not_movedByAll hB hzB hnot
  have h2 := centralizerGenerationStar_conj hs.hyp.conjInvariant g⁻¹ h1
  rw [conjSub_inv_conjSub] at h2
  have e : g⁻¹ * z * g⁻¹⁻¹ = t := by rw [← hgt]; group
  rwa [e] at h2

end GenT

end CFSG.ClassicalInvolution.Asc77
