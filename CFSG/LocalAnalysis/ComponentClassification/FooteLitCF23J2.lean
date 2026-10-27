module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Fus
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitCF23Model
public import CFSG.Sporadic.SmallOddCore.J2Local
public import Certificates.Certificate23202

public section

namespace CFSG.ComponentClassification.GSThmB.CF23I

open CFSG Subgroup Sporadic.SmallOddCore Sporadic.Schreier Sporadic.Th Sporadic.Th.Native
open Sporadic.SmallOddCore.Native LocalAnalysis.ComponentInitial


theorem j2_centralizers :
    genOf 315 j2C1Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 17)} : Set _) ∧
      genOf 315 j2C2Gens = j2P ⊓ centralizer ({tp 315 (j2CentTbl 31)} : Set _) := by
  obtain ⟨-, -, -, hrows, -, -, -, -⟩ := ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  constructor
  · have h := (hrows _ (List.mem_cons_of_mem _ List.mem_cons_self)).2.2.2.1
    dsimp only [Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C1Gens]
    exact h
  · have h := (hrows _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))).2.2.2.1
    dsimp only [Sporadic.SmallOddCore.j2C] at h
    rw [genOf, j2C2Gens]
    exact h

theorem genOf_j2C12_le : genOf 315 (j2C1Gens ++ j2C2Gens) ≤ j2P := by
  obtain ⟨hC1, hC2⟩ := j2_centralizers
  rw [genOf, closure_le]
  rintro _ ⟨g, hg, rfl⟩
  have hg' : g ∈ j2C1Gens ++ j2C2Gens := by simpa using hg
  rcases List.mem_append.mp hg' with h | h
  · have := tp_mem_genOf (n := 315) h
    rw [hC1] at this
    exact this.1
  · have := tp_mem_genOf (n := 315) h
    rw [hC2] at this
    exact this.1

theorem j2_fusion_witness : ∃ d ∈ genOf 315 j2DGens, orderOf d = 2 ∧
    ∃ c ∈ j2P, c⁻¹ * tp 315 (j2CentTbl 17) * c = tp 315 (j2CentTbl 17) * d := by
  have hn : 315 < 2 ^ 32 := by norm_num
  have h := Certificates.certificate23202
  simp only [J2.j2FusOK, J2.d0Tbl, J2.c0Tbl, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hcp, hdp⟩, ht1⟩, hd0⟩, hcinv⟩, heq⟩ := h
  obtain ⟨d, hdD, hdRep⟩ := rep_wordTbl hn hdp [1, 2, 2] (by decide)
  obtain ⟨c, hcG, hcRep⟩ := rep_wordTbl hn hcp [9, 5, 6, 9] (by decide)
  have hT := rep_tp (n := 315) ht1
  have hcI := rep_invT hcRep hcinv
  have he := (tblEq_iff_eq (Rep.compT (Rep.compT hcI hT) hcRep) (Rep.compT hT hdRep)).1 heq
  exact ⟨d, hdD, orderOf_eq_two_of_involOK hn hdRep hd0, c, genOf_j2C12_le hcG, he⟩

theorem j2_inner {G : Type} [Group G] {N J : Subgroup G} (e : ↥N ≃* Blueprint.NativeSporadic.J2)
    {α : G} (hα : orderOf α = 2) (hαN : α ∈ N) (hJN : J ≤ N)
    (hJα : J ≤ centralizer ({α} : Set G))
    (hJ : IsComponent (J.subgroupOf (centralizer ({α} : Set G)))) :
    ∃ ζ₀ ∈ J, orderOf ζ₀ = 2 ∧ ∃ γ₀ ∈ N, γ₀⁻¹ * α * γ₀ = α * ζ₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let θ : ↥N ≃* j2P := e.trans j2PermEquiv
  set f : ↥N →* Equiv.Perm (Fin 315) := j2P.subtype.comp θ.toMonoidHom with hfdef
  have hf : Function.Injective f := Subtype.val_injective.comp θ.injective
  set α' : ↥N := ⟨α, hαN⟩ with hα'
  have hB := isComponentOf_image hαN hJN hJα hJ θ
  have hτP : f α' ∈ j2P := (θ α').2
  have hτ2 : orderOf (f α') = 2 := by
    rw [orderOf_injective f hf, Subgroup.orderOf_mk, hα]
  obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
    ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
  obtain ⟨r, hr, g, hg, hτg⟩ := hcover (f α') (j2P_le_j2R hτP) hτ2
  set B := (J.subgroupOf N).map f with hBdef
  change Assembly.IsComponentOf B (j2P ⊓ centralizer ({f α'} : Set _)) at hB
  rw [hτg] at hB
  set fc := (MulAut.conj g⁻¹).toMonoidHom with hfcdef
  have hfcinj : Function.Injective fc := (MulAut.conj g⁻¹).injective
  have hBr : Assembly.IsComponentOf (B.map fc)
      (j2P ⊓ centralizer ({tp 315 r.rep} : Set _)) := by
    have h := (isComponentOf_map_iff hfcinj).2 hB
    rwa [map_conj_inf_centralizer j2P (j2P.inv_mem hg), Set.image_singleton,
      show fc (g * tp 315 r.rep * g⁻¹) = tp 315 r.rep by simp only [fc]; simp; group] at h
  have htrP : tp 315 r.rep ∈ j2P := by
    have := j2P.mul_mem (j2P.mul_mem (j2P.inv_mem hg) (hτg ▸ hτP)) hg
    rwa [show g⁻¹ * (g * tp 315 r.rep * g⁻¹) * g = tp 315 r.rep by group] at this
  have hBq := hBr.2.2
  have hrow := (hrows r hr).2.2.1
  have hr' := hr
  simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr'
  obtain ⟨hC1, hC2⟩ := j2_centralizers
  rcases hr' with h0 | h0 | h0
  ·
    have hout : r.outer = true := by rw [h0]
    exact absurd htrP (hrow.1 hout)
  ·
    have hrep : r.rep = j2CentTbl 17 := by rw [h0]
    rw [hrep] at hBr hτg
    obtain ⟨-, hDC1, hC1D, hDsimple, hC1cent⟩ := j2_D_facts
    rw [← hC1] at hBr
    have hBD : B.map fc = genOf 315 j2DGens := by
      rcases isComponentOf_le_or_commute hBr hDC1 hC1D with hle | hcomm
      · set D := genOf 315 j2DGens
        have hBDc := isComponentOf_of_le hBr hle hDC1
        have hc := (isComponentOf_iff_isComponent_subgroupOf hle).1 hBDc
        have hn : 315 < 2 ^ 32 := by norm_num
        have hm1 : wordTbl 315 j2C1Gens [3, 2] ∈ j2DGens := by simp [j2DGens]
        have hm2 : wordTbl 315 j2C1Gens [2, 4, 2, 4] ∈ j2DGens := by simp [j2DGens]
        have hnab : ∃ a b : ↥D, a * b ≠ b * a := by
          refine ⟨⟨_, tp_mem_genOf hm1⟩, ⟨_, tp_mem_genOf hm2⟩, fun h => ?_⟩
          have h' := congrArg Subtype.val h
          have := (commTT_iff (rep_tp (j2_DGens_perm _ hm1)) (rep_tp (j2_DGens_perm _ hm2))).2 h'
          rw [j2_D_noncomm] at this
          exact Bool.noConfusion this
        have : IsSimpleGroup ↥D := hDsimple
        obtain ⟨hDq, hDZ⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
        rcases quasisimple_subnormal_subgroups hDq hc.2 with htop | hcen
        · apply le_antisymm hle
          intro x hx
          have : (⟨x, hx⟩ : ↥D) ∈ (B.map fc).subgroupOf D := by rw [htop]; trivial
          exact mem_subgroupOf.mp this
        · exfalso
          rw [hDZ] at hcen
          have hbot : (B.map fc).subgroupOf D = ⊥ := le_bot_iff.mp hcen
          have hB'bot : B.map fc = ⊥ := by
            rw [eq_bot_iff]
            intro x hx
            have : (⟨x, hle hx⟩ : ↥D) ∈ (B.map fc).subgroupOf D := mem_subgroupOf.mpr hx
            rw [hbot, mem_bot] at this
            exact congrArg Subtype.val this
          have hq := hBq
          rw [ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native] at hq
          obtain ⟨a, b, hab⟩ := hq.2.2
          apply hab
          have : Subsingleton ↥(B.map fc) := by
            rw [hB'bot]
            infer_instance
          have : Subsingleton (↥(B.map fc) ⧸ center ↥(B.map fc)) := inferInstance
          exact Subsingleton.elim _ _
      · exfalso
        have hle : B.map fc ≤ genOf 315 j2C1Gens ⊓
            centralizer (genOf 315 j2DGens : Set (Equiv.Perm (Fin 315))) := by
          intro x hx
          refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
          rw [mem_centralizer_iff]
          intro y hy
          have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
          rw [mem_centralizer_iff] at this
          exact this y hy
        exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 2) (by rw [hC1cent]; norm_num))
          hle
    obtain ⟨d, hdD, hd2, c, hcP, hc⟩ := j2_fusion_witness
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
    have hcg : g * c * g⁻¹ ∈ j2P := j2P.mul_mem (j2P.mul_mem hg hcP) (j2P.inv_mem hg)
    refine ⟨(z : G), mem_subgroupOf.mp hz, ?_, (θ.symm ⟨g * c * g⁻¹, hcg⟩ : G),
      (θ.symm ⟨g * c * g⁻¹, hcg⟩).2, ?_⟩
    · rw [Subgroup.orderOf_coe, ← orderOf_injective f hf, hfz]
      rw [show g * d * g⁻¹ = (MulAut.conj g) d from rfl, MulEquiv.orderOf_eq, hd2]
    · have hγ : f (θ.symm ⟨g * c * g⁻¹, hcg⟩) = g * c * g⁻¹ := by
        show ((θ (θ.symm ⟨g * c * g⁻¹, hcg⟩) : j2P) : Equiv.Perm (Fin 315)) = _
        rw [MulEquiv.apply_symm_apply]
      have hN' : (θ.symm ⟨g * c * g⁻¹, hcg⟩)⁻¹ * α' * θ.symm ⟨g * c * g⁻¹, hcg⟩ = α' * z := by
        apply hf
        rw [map_mul, map_mul, map_inv, hγ, map_mul, hfz, hτg]
        calc (g * c * g⁻¹)⁻¹ * (g * tp 315 (j2CentTbl 17) * g⁻¹) * (g * c * g⁻¹) =
              g * (c⁻¹ * tp 315 (j2CentTbl 17) * c) * g⁻¹ := by group
          _ = g * (tp 315 (j2CentTbl 17) * d) * g⁻¹ := by rw [hc]
          _ = g * tp 315 (j2CentTbl 17) * g⁻¹ * (g * d * g⁻¹) := by group
      exact congrArg Subtype.val hN'
  ·
    exfalso
    have hrep : r.rep = j2CentTbl 31 := by rw [h0]
    rw [hrep] at hBr
    obtain ⟨hQcard, hQC2, hC2Q, hC2cent⟩ := j2_Q_facts
    rw [← hC2] at hBr
    rcases isComponentOf_le_or_commute hBr hQC2 hC2Q with hle | hcomm
    · exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 5) (by rw [hQcard]; norm_num)) hle
    · have hle : B.map fc ≤ genOf 315 j2C2Gens ⊓
          centralizer (genOf 315 j2QGens : Set (Equiv.Perm (Fin 315))) := by
        intro x hx
        refine mem_inf.mpr ⟨hBr.1 hx, ?_⟩
        rw [mem_centralizer_iff]
        intro y hy
        have := (commutator_eq_bot_iff_le_centralizer.mp hcomm) hx
        rw [mem_centralizer_iff] at this
        exact this y hy
      exact not_le_of_isPGroup hBq (isPGroup_two_of_card (k := 1) (by rw [hC2cent]; norm_num))
        hle

theorem j2 : CF23InnerFusionFor fun Y _ => Blueprint.NativeSporadic.IsSporadic Y .J2 := by
  intro G _ _ N hN hC hY α J hα hJN hJα hJ _ hsmall hZ _
  obtain ⟨e⟩ := hY
  have := hN
  have e' : ↥N ≃* Blueprint.NativeSporadic.J2 := e
  by_cases hαN : α ∈ N
  · obtain ⟨ζ₀, hζ₀, hζ₀2, γ₀, hγ₀, h⟩ := j2_inner e' hα hαN hJN hJα hJ
    exact concl_of_witness hJN hJα (oneClass_of_small hZ hsmall) hζ₀ hζ₀2 hγ₀ h
  · let θ : ↥N ≃* j2P := e'.trans j2PermEquiv
    have hM := j2_autModel
    obtain ⟨hmem, hord⟩ := embed_mem_orderOf hM hC θ hα
    have hnP : hM.embed N θ α ∉ j2P := fun h => hαN ((embed_mem_iff hM hC θ α).1 h)
    obtain ⟨-, -, -, hrows, hcover, -, -, -⟩ :=
      ctuc_j2_all_involution_fixed_subgroups_odd_core_trivial
    have hcls : ∀ t ∈ j2R, t ∉ j2P → orderOf t = 2 →
        ∃ g ∈ j2P, t = g * tp 315 (j2CentTbl 9) * g⁻¹ := by
      intro t ht htP ht2
      obtain ⟨r, hr, g, hg, rfl⟩ := hcover t ht ht2
      have hrow := (hrows r hr).2.2.1
      have hnP : tp 315 r.rep ∉ j2P := fun h => htP ((conj_mem_iff hg _).2 h)
      have hr' := hr
      simp only [j2Rows, List.mem_cons, List.not_mem_nil, or_false] at hr'
      rcases hr' with h0 | h0 | h0
      · have hrep : r.rep = j2CentTbl 9 := by rw [h0]
        exact ⟨g, hg, by rw [hrep]⟩
      all_goals exfalso
      all_goals have hout : r.outer = false := by rw [h0]
      all_goals exact Bool.false_ne_true (hout.symm.trans (hrow.2 hnP))
    exact concl_of_coset hα hJN hJα hZ (coset_of_autModel hM hC θ
      (coset_of_rep_outer j2P_le_j2R _ hcls _ hmem hnP hord))

end CFSG.ComponentClassification.GSThmB.CF23I
