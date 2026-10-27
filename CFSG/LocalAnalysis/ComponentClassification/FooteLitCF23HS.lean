module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Tools
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Model
public import CFSG.Sporadic.SmallOddCore.HSLocal
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19HSAutOuter
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieFix
public import Certificates.Certificate23203
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Fus

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.SmallOddCore Sporadic.Schreier Sporadic.Th Sporadic.Th.Native
open Sporadic.SmallOddCore.Native LocalAnalysis.ComponentInitial

theorem isComponentOf_embed {M : Type*} [Group M] {P R : Subgroup M}
    (h : AutModel P R) {G : Type*} [Group G] {N J : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) (θ : N ≃* P) {α : G} (hJN : J ≤ N)
    (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    Assembly.IsComponentOf (J.map (h.embed N θ))
      (P ⊓ centralizer ({h.embed N θ α} : Set M)) := by
  set ι := h.embed N θ with hιdef
  have hinj := h.embed_injective N θ hC
  have hc := (isComponentOf_iff_isComponent_subgroupOf hJα).2 hJ
  have h1 := (isComponentOf_map_iff hinj).2 hc
  have hmap : (centralizer ({α} : Set G)).map ι = ι.range ⊓ centralizer ({ι α} : Set M) := by
    rw [map_centralizer_eq_inf hinj, Set.image_singleton]
  rw [hmap] at h1
  have hJP : J.map ι ≤ P := by
    rintro _ ⟨x, hx, rfl⟩
    rw [show x = ((⟨x, hJN hx⟩ : N) : G) from rfl, h.embed_coe]
    exact (θ _).2
  have hPr : P ≤ ι.range := fun p hp => ⟨(θ.symm ⟨p, hp⟩ : G), by
    rw [h.embed_coe, MulEquiv.apply_symm_apply]⟩
  exact isComponentOf_of_le h1 (le_inf hJP (h1.1.trans inf_le_right))
    (inf_le_inf_right _ hPr)

theorem card_eq_sixty_of_dvd_1920 {X : Type} [Group X]
    (h : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧ Blueprint.LieModel X .PSL 2 p f) ∨
      Nonempty (X ≃* alternatingGroup (Fin 7))) (hd : Nat.card X ∣ 1920) :
    Nat.card X = 60 := by
  rcases card_small h with ⟨q, hq, hq5, hX⟩ | hX
  · rw [hX] at hd ⊢
    have hle := Nat.le_of_dvd (by norm_num) hd
    have hq17 : q < 17 := by
      by_contra hq17
      push Not at hq17
      have : 17 * (17 ^ 2 - 1) ≤ q * (q ^ 2 - 1) :=
        Nat.mul_le_mul hq17 (Nat.sub_le_sub_right (Nat.pow_le_pow_left hq17 2) 1)
      omega
    interval_cases q <;> simp_all
  · rw [hX] at hd
    omega

theorem alternatingGroup_five_pow_six :
    ∀ g : alternatingGroup (Fin 5), g ^ 6 = 1 → g ^ 2 = 1 ∨ g ^ 3 = 1 := by
  decide +kernel


theorem hs_gens12_le : genOf 3850 HS.gens12 ≤ hsP := by
  obtain ⟨h1, h2, -⟩ := Sporadic.SmallOddCore.hs_reps
  have m1 : ∀ T ∈ [hsCentTbl 6, hsCentTbl 7], tp 3850 T ∈ hsP := fun T hT => by
    have := Subgroup.subset_closure
      (k := tp 3850 '' {x | x ∈ [hsCentTbl 6, hsCentTbl 7].toArray}) ⟨T, by simpa using hT, rfl⟩
    rw [h1] at this
    exact this.1
  have m2 : ∀ T ∈ [hsCentTbl 13, hsCentTbl 14, hsCentTbl 15, hsCentTbl 16],
      tp 3850 T ∈ hsP := fun T hT => by
    have := Subgroup.subset_closure (k := tp 3850 '' {x | x ∈ [hsCentTbl 13, hsCentTbl 14,
      hsCentTbl 15, hsCentTbl 16].toArray}) ⟨T, by simpa using hT, rfl⟩
    rw [h2] at this
    exact this.1
  rw [genOf, closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ [hsCentTbl 6, hsCentTbl 7] ++
      [hsCentTbl 13, hsCentTbl 14, hsCentTbl 15, hsCentTbl 16] := by
    have : g ∈ HS.gens12 := by simpa using hg
    exact this
  rcases List.mem_append.mp hg' with h | h
  · exact m1 g h
  · exact m2 g h

theorem hs_gens4_eq :
    genOf 3850 HS.gens4 = hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set _) := by
  obtain ⟨-, -, -, hrows, -⟩ := hs_involution_centralizers
  have h := (hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_cons_of_mem _ List.mem_cons_self)))).2.2.2.1
  dsimp only [Sporadic.SmallOddCore.hsC] at h
  rw [genOf, HS.gens4]
  exact h

theorem hs_witness : (∃ d ∈ genGroup 3850 hsDGens hsDPerm, orderOf d = 2 ∧
      ∃ c ∈ hsP, c⁻¹ * hsT2 * c = hsT2 * d) ∧
    ∃ x ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set _),
      ∃ y ∈ hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set _),
        orderOf x = 3 ∧ orderOf y = 5 ∧ orderOf (x * y) = 6 := by
  have hn : 3850 < 2 ^ 32 := by norm_num
  have h := Certificates.certificate23203
  simp only [HS.hsFusOK, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hg12, hg4⟩, ht2⟩, hd0⟩, hcinv⟩, heq⟩, hx3⟩, hy5⟩, hxy6⟩ := h
  have hp13 : permOK 3850 (hsCentTbl 13) = true := hg12 _ (by
    unfold HS.gens12
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hp14 : permOK 3850 (hsCentTbl 14) = true := hg12 _ (by
    unfold HS.gens12
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
      List.mem_cons_self)))
  have r13 := rep_tp (n := 3850) hp13
  have r14 := rep_tp (n := 3850) hp14
  have hRepD : Rep 3850 HS.d0Tbl (hsDPerm 0) := by
    have hw := Rep.compT (Rep.compT (Rep.compT r13 r13) r14) r13
    have hdp : hsDPerm 0 = tp 3850 (hsCentTbl 13) * tp 3850 (hsCentTbl 13) *
        tp 3850 (hsCentTbl 14) * tp 3850 (hsCentTbl 13) := by
      simp only [hsDPerm, hsDWords, List.getD_cons_zero, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, hsC2Perm, mul_one, mul_assoc]
    rw [hdp]
    exact hw
  have hdD : hsDPerm 0 ∈ genGroup 3850 hsDGens hsDPerm :=
    subset_closure ⟨0, by simp [hsDGens], rfl⟩
  obtain ⟨c, hcG, hcRep⟩ := rep_wordTbl hn hg12 [1, 6, 1, 6, 2, 2] (by decide)
  have hT := rep_tp (n := 3850) ht2
  have hcI := rep_invT hcRep hcinv
  have he := (tblEq_iff_eq (Rep.compT (Rep.compT hcI hT) hcRep) (Rep.compT hT hRepD)).1 heq
  obtain ⟨x, hxG, hxRep⟩ := rep_wordTbl hn hg4 [2] (by decide)
  obtain ⟨y, hyG, hyRep⟩ := rep_wordTbl hn hg4 [1, 3] (by decide)
  rw [hs_gens4_eq] at hxG hyG
  exact ⟨⟨_, hdD, orderOf_eq_two_of_involOK hn hRepD hd0, c, hs_gens12_le hcG, he⟩, x, hxG, y,
    hyG, (ordTest_iff_perm hxRep (by norm_num)).1 hx3, (ordTest_iff_perm hyRep (by norm_num)).1 hy5,
    (ordTest_iff_perm (Rep.compT hxRep hyRep) (by norm_num)).1 hxy6⟩

theorem hs_inner {G : Type} [Group G] {N J : Subgroup G} (e : ↥N ≃* Blueprint.NativeSporadic.HS)
    {α : G} (hα : orderOf α = 2) (hαN : α ∈ N) (hJN : J ≤ N)
    (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    ∃ ζ₀ ∈ J, orderOf ζ₀ = 2 ∧ ∃ γ₀ ∈ N, γ₀⁻¹ * α * γ₀ = α * ζ₀ := by
  let θ : ↥N ≃* hsP := e.trans hsPermEquiv
  set f : ↥N →* Equiv.Perm (Fin 3850) := hsP.subtype.comp θ.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.injective
  set α' : ↥N := ⟨α, hαN⟩ with hα'
  have hB := isComponentOf_image hαN hJN hJα hJ θ
  have hτP : f α' ∈ hsP := (θ α').2
  have hτ2 : orderOf (f α') = 2 := by
    rw [orderOf_injective f hf, Subgroup.orderOf_mk, hα]
  obtain ⟨-, -, -, -, hcls⟩ := Sporadic.SmallOddCore.hs_reps
  obtain ⟨r, hr, g, hg, hτg⟩ := hcls (f α') hτP hτ2
  set B := (J.subgroupOf N).map f with hBdef
  change Assembly.IsComponentOf B (hsP ⊓ centralizer ({f α'} : Set _)) at hB
  rw [hτg] at hB
  have hBr := isComponentOf_conj hg hB
  set fc := (MulAut.conj g⁻¹).toMonoidHom with hfcdef
  rcases hr with rfl | rfl
  · exact (hsC1_no_component hBr).elim
  · have hBD := hsC2_component hBr
    obtain ⟨⟨d, hdD, hd2, c, hcP, hc⟩, -⟩ := hs_witness
    have hgd : g * d * g⁻¹ ∈ B := by
      rw [← hBD] at hdD
      obtain ⟨b, hb, hbd⟩ := mem_map.mp hdD
      have : b = g * d * g⁻¹ := by
        rw [← hbd]
        simp only [fc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
        group
      rw [← this]
      exact hb
    obtain ⟨z, hz, hfz⟩ := mem_map.mp hgd
    have hcg : g * c * g⁻¹ ∈ hsP := hsP.mul_mem (hsP.mul_mem hg hcP) (hsP.inv_mem hg)
    refine ⟨(z : G), mem_subgroupOf.mp hz, ?_, (θ.symm ⟨g * c * g⁻¹, hcg⟩ : G),
      (θ.symm ⟨g * c * g⁻¹, hcg⟩).2, ?_⟩
    · rw [Subgroup.orderOf_coe, ← orderOf_injective f hf, hfz, ← MulAut.conj_apply,
        MulEquiv.orderOf_eq, hd2]
    · have hγ : f (θ.symm ⟨g * c * g⁻¹, hcg⟩) = g * c * g⁻¹ := by
        show ((θ (θ.symm ⟨g * c * g⁻¹, hcg⟩) : hsP) : Equiv.Perm (Fin 3850)) = _
        rw [MulEquiv.apply_symm_apply]
      have hN' : (θ.symm ⟨g * c * g⁻¹, hcg⟩)⁻¹ * α' * θ.symm ⟨g * c * g⁻¹, hcg⟩ = α' * z := by
        apply hf
        rw [map_mul, map_mul, map_inv, hγ, map_mul, hfz, hτg]
        calc (g * c * g⁻¹)⁻¹ * (g * hsT2 * g⁻¹) * (g * c * g⁻¹) =
              g * (c⁻¹ * hsT2 * c) * g⁻¹ := by group
          _ = g * (hsT2 * d) * g⁻¹ := by rw [hc]
          _ = g * hsT2 * g⁻¹ * (g * d * g⁻¹) := by group
      exact congrArg Subtype.val hN'

theorem hs_outer_false {G : Type} [Group G] [Finite G] {N J : Subgroup G} [N.Normal]
    (hC : centralizer (N : Set G) = ⊥) (e : ↥N ≃* Blueprint.NativeSporadic.HS) {α : G}
    (hα : orderOf α = 2) (hαN : α ∉ N) (hJN : J ≤ N) (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G))))
    (hsmall : (∃ p f : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ f ∧ 5 ≤ p ^ f ∧
        Blueprint.LieModel (↥J ⧸ center ↥J) .PSL 2 p f) ∨
      Nonempty (↥J ⧸ center ↥J ≃* alternatingGroup (Fin 7)))
    (hZ : Odd (Nat.card (center ↥J))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ : ↥N ≃* hsP := e.trans hsPermEquiv
  have hM := hs_autModel
  set ι := hM.embed N θ with hιdef
  have hinj := hM.embed_injective N θ hC
  have hB := isComponentOf_embed hM hC θ hJN hJα hJ
  obtain ⟨hmem, hord⟩ := embed_mem_orderOf hM hC θ hα
  have hnP : ι α ∉ hsP := fun h => hαN ((embed_mem_iff hM hC θ α).1 h)
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ := hs_involution_centralizers
  obtain ⟨r, hr, g, hg, hτg⟩ := hcover (ι α) hmem hord
  rw [hτg] at hB
  have hBr := isComponentOf_conj hg hB
  set fc := (MulAut.conj g⁻¹).toMonoidHom with hfcdef
  set B := (J.map ι).map fc with hBdef
  let eB : ↥J ≃* ↥B := (J.equivMapOfInjective ι hinj).trans
    ((J.map ι).equivMapOfInjective fc (MulAut.conj g⁻¹).injective)
  have hcardB : Nat.card B = Nat.card J := (Nat.card_congr eB.toEquiv).symm
  have hJZ : Nat.card (↥J ⧸ center ↥J) ∣ Nat.card J := by
    rw [← Subgroup.index_eq_card]
    exact (center ↥J).index_dvd_card
  have hnPr : tp 3850 r.rep ∉ hsP := fun h => hnP (hτg ▸ (conj_mem_iff hg _).2 h)
  have hrow := (hrows r hr).2.2.1
  have hcardr := (hrows r hr).2.2.2.2.1
  have hr' := hr
  simp only [hsRows, List.mem_cons, List.not_mem_nil, or_false] at hr'
  rcases hr' with h0 | h0 | h0 | h0
  · have hout : r.outer = false := by rw [h0]
    exact Bool.false_ne_true (hout.symm.trans (hrow.2 hnPr))
  · have hout : r.outer = false := by rw [h0]
    exact Bool.false_ne_true (hout.symm.trans (hrow.2 hnPr))
  ·
    have hrep : r.rep = hsCentTbl 21 := by rw [h0]
    rw [hrep] at hBr
    set C := QuasithinUnique.Id2519.HSAut.outerC
    change Assembly.IsComponentOf B C at hBr
    have : IsSimpleGroup ↥(commutator ↥C) := QuasithinUnique.Id2519.HSAut.commutator_simple'
    have hc := (isComponentOf_iff_isComponent_subgroupOf hBr.1).1 hBr
    have hle := QuasithinUnique.Id2519.le_commutator_of_isQuasisimple hc.1
    have htop := QuasithinUnique.Id2519.isComponent_eq_top_of_isSimpleGroup
      (CFSG.LocalCores.component_overgroup hc hle)
    have hBeq : B.subgroupOf C = commutator ↥C := le_antisymm hle (subgroupOf_eq_top.mp htop)
    let e2 : ↥B ≃* ↥(commutator ↥C) :=
      (subgroupOfEquivOfLe hBr.1).symm.trans (MulEquiv.subgroupCongr hBeq)
    have hBs : IsSimpleGroup ↥B := MulEquiv.isSimpleGroup e2
    have hBcard : Nat.card ↥B = 20160 := by
      rw [Nat.card_congr e2.toEquiv]
      exact QuasithinUnique.Id2519.HSAut.card_commutator'
    have hZB : center ↥B = ⊥ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center ↥B) with h | h
      · exact h
      · exfalso
        obtain ⟨-, hsimple⟩ := hBr.2.2
        have : Subsingleton (↥B ⧸ center ↥B) := by
          rw [h]
          exact QuotientGroup.subsingleton_quotient_top
        exact (not_subsingleton (↥B ⧸ center ↥B)) this
    have hq : Nat.card (↥B ⧸ center ↥B) = 20160 := by
      rw [Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hZB).trans
        QuotientGroup.quotientBot).toEquiv, hBcard]
    exact not_small_of_card_20160 ((card_quotient_center_congr eB).trans hq) hsmall
  ·
    have hrep : r.rep = hsCentTbl 34 := by rw [h0]
    have hco : r.centOrder = 1920 := by rw [h0]
    rw [hrep] at hBr hcardr
    rw [hco] at hcardr
    have hdvd : Nat.card J ∣ 1920 := by
      rw [← hcardB, ← hcardr]
      exact Subgroup.card_dvd_of_le hBr.1
    have h60 := card_eq_sixty_of_dvd_1920 hsmall (hJZ.trans hdvd)
    have hm := Subgroup.card_mul_index (center ↥J)
    rw [Subgroup.index_eq_card, h60] at hm
    have hZ32 : Nat.card (center ↥J) ∣ 2 ^ 5 := by
      have : Nat.card (center ↥J) * 60 ∣ 32 * 60 := by rw [hm]; exact hdvd
      exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) this
    obtain ⟨i, hi, hi'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hZ32
    have hi0 : i = 0 := by
      rcases i with _ | i
      · rfl
      · rw [hi'] at hZ
        exact absurd (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.succ_ne_zero i)))
          (Nat.not_even_iff_odd.mpr hZ)
    rw [hi0, pow_zero] at hi'
    rw [hi', one_mul] at hm
    have hk : Nat.card ↥(hsP ⊓ centralizer ({tp 3850 (hsCentTbl 34)} : Set _)) =
        2 ^ 5 * Nat.card B := by
      rw [hcardr, hcardB, ← hm]
      norm_num
    obtain ⟨-, x, hx, y, hy, hx3, hy5, hxy6⟩ := hs_witness
    have hxB : x ∈ B := mem_of_isSubnormal_of_odd hBr.2.1 (by rw [hx3]; decide) hx 5 hk
    have hyB : y ∈ B := mem_of_isSubnormal_of_odd hBr.2.1 (by rw [hy5]; decide) hy 5 hk
    have hJq : CFSG.IsQuasisimple ↥J := (isQuasisimple_congr (subgroupOfEquivOfLe hJα)).1 hJ.1
    have hZJ : center ↥J = ⊥ := Subgroup.eq_bot_of_card_eq _ hi'
    have hJs : IsSimpleGroup ↥J := by
      have := hJq.2.1
      exact ((QuotientGroup.quotientMulEquivOfEq hZJ).trans
        QuotientGroup.quotientBot).symm.isSimpleGroup
    obtain ⟨eA⟩ := CFSG.BenderSuzuki.nonempty_mulEquiv_alternatingGroup_five (G := ↥J) (hm.symm)
    set a := eA (eB.symm ⟨x * y, B.mul_mem hxB hyB⟩) with hadef
    have ha6 : orderOf a = 6 := by
      rw [hadef, MulEquiv.orderOf_eq, MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hxy6]
    have h6 : a ^ 6 = 1 := by rw [← ha6, pow_orderOf_eq_one]
    rcases alternatingGroup_five_pow_six a h6 with h | h
    · have := orderOf_dvd_of_pow_eq_one h
      rw [ha6] at this
      omega
    · have := orderOf_dvd_of_pow_eq_one h
      rw [ha6] at this
      omega

theorem hs : CF23InnerFusionFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .HS := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  obtain ⟨e⟩ := hY
  have := hN
  have e' : ↥N ≃* Blueprint.NativeSporadic.HS := e
  by_cases hαN : α ∈ N
  · obtain ⟨ζ₀, hζ₀, hζ₀2, γ₀, hγ₀, h⟩ := hs_inner e' hα hαN hJN hJα hJ
    exact concl_of_witness hJN hJα (oneClass_of_small hZ hsmall) hζ₀ hζ₀2 hγ₀ h
  · exact (hs_outer_false hC e' hα hαN hJN hJα hJ hsmall hZ).elim

end CFSG.ComponentClassification.GSThmB.CF23I
