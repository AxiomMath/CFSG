module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB.KG2F

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.MI
open CFSG.LocalAnalysis.GLTheoremA.CatB.KMultA1

@[expose] def G2FieldLayerS : Prop :=
  ∀ (S : Type) [Group S], IsSimpleGroup S → ∀ β : MulAut S,
    GLAMarking S (fun lab _ _ I F θ => GLAPrimeField 3 lab I F (GLAInduces θ fun x y => β x = y)) →
    ∀ J : Subgroup S, J ≤ FP.fixSub β → CFSG.Open.IsSubnormal J (FP.fixSub β) →
      ∀ (T : Type) [Group T], catalogIs T (isG2n 2) → (∃ φ : ↥J →* T, Function.Surjective φ) →
        catalogIs S (isG2n 6)

variable {G : Type} [Group G] [Finite G]

theorem g2FieldLayerAt_of_fact (hF : G2FieldLayerS) : KMultA1.G2FieldLayerAt G := by
  intro X L I b hL hLq _hbp hFO hI hcat
  have hb : b ∈ Subgroup.normalizer (L : Set G) := hFO.1
  obtain ⟨hcomm, lab, hlab, hraw⟩ := hFO.2
  have hq := isQuasisimple_pQuot_of_glaPComponent Nat.prime_three hL
  have hsim : IsSimpleGroup (PSimple 3 L) := hq.2
  have hcS : Subgroup.center (PSimple 3 L) = ⊥ := center_pSimple_eq_bot Nat.prime_three hL
  have hcommS : commutator (PSimple 3 L) = ⊤ := by
    have h1 := hq.1
    rw [commutator_def] at h1 ⊢
    have hs := QuotientGroup.mk'_surjective (Subgroup.center (PQuot 3 L))
    have h2 := Subgroup.map_commutator (⊤ : Subgroup (PQuot 3 L)) ⊤
      (QuotientGroup.mk' (Subgroup.center (PQuot 3 L)))
    rw [h1, Subgroup.map_top_of_surjective _ hs] at h2
    exact h2.symm
  have hMS : GLAMarking (PSimple 3 L)
      (fun lab _ _ I F θ => GLAPrimeField 3 lab I F (GLAInduces θ fun x y => indAut 3 L b hb x = y)) := by
    refine ⟨hcommS, lab, hlab, ?_⟩
    refine CFSG.StandardType.Canonical.largeEvenRawDatum_mono ?_ hraw
    rintro R _ I F ⟨hs, hna, θ, hP⟩
    have hθ' : ∀ s : PSimple 3 L,
        ((QuotientGroup.quotientMulEquivOfEq hcS).trans (QuotientGroup.quotientBot.trans θ))
          (QuotientGroup.mk s) = θ s := fun s => rfl
    refine ⟨hs, hna, (QuotientGroup.quotientMulEquivOfEq hcS).trans (QuotientGroup.quotientBot.trans θ), ?_⟩
    obtain ⟨hne, f, hf, u, hu, hord, hα⟩ := hP
    refine ⟨hne, f, hf, u, hu, hord, ?_⟩
    intro x y hxy
    obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨q', hq'⟩ := indRel_total hb q
    have hy : QuotientGroup.mk q' = y := by
      have h1 : indAut 3 L b hb (QuotientGroup.mk q) = y := hxy
      rw [← h1, indAut_apply_mk hb hq']
    rw [hθ', hθ', ← hy]
    exact hα q q' hq'
  have hπs : Function.Surjective (chevQuotHom 3 L) := chevQuotHom_surjective 3 L
  have hker : (chevQuotHom 3 L).ker = Subgroup.center ↥L := ker_chevQuotHom_eq_center hL hLq
  have hIL : I ≤ L := hI.1.trans inf_le_left
  have hN : ∀ k : ↥L,
      ((L.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ k : ↥L) : G) = b⁻¹ * (k : G) * b := by
    intro k
    simp
  have hfix : ∀ h : ↥L, (h : G) ∈ cx b → indAut 3 L b hb (chevQuotHom 3 L h) = chevQuotHom 3 L h := by
    intro h hh
    have hh' : b * (h : G) = (h : G) * b := Subgroup.mem_centralizer_iff.1 hh b (Set.mem_singleton b)
    rw [indAut_chevQuotHom hb h]
    congr 1
    apply Subtype.ext
    rw [hN h]
    calc b⁻¹ * (h : G) * b = b⁻¹ * ((h : G) * b) := by group
      _ = b⁻¹ * (b * (h : G)) := by rw [hh']
      _ = (h : G) := by group
  have hconj : ∀ k : ↥L, indAut 3 L b hb (chevQuotHom 3 L k) = chevQuotHom 3 L k →
      ∀ h : ↥L, (h : G) ∈ cx b → (k : G) * (h : G) * (k : G)⁻¹ ∈ cx b := by
    intro k hk h hh
    obtain ⟨z, hzdef⟩ : ∃ z : ↥L, z = k⁻¹ * L.normalizerMonoidHom ⟨b⁻¹, Subgroup.inv_mem _ hb⟩ k :=
      ⟨_, rfl⟩
    have hz : z ∈ Subgroup.center ↥L := by
      rw [← hker, MonoidHom.mem_ker, hzdef, map_mul, map_inv, ← indAut_chevQuotHom hb k, hk, inv_mul_cancel]
    have hzc : ∀ g : ↥L, g * z = z * g := fun g => Subgroup.mem_center_iff.1 hz g
    obtain ⟨zG, hzG⟩ : ∃ zG : G, zG = (k : G)⁻¹ * (b⁻¹ * (k : G) * b) := ⟨_, rfl⟩
    have hzG' : (z : G) = zG := by
      rw [hzdef, Subgroup.coe_mul, Subgroup.coe_inv, hN k, hzG]
    have hzcG : ∀ g : G, g ∈ L → g * zG = zG * g := by
      intro g hg
      have h1 := congrArg Subtype.val (hzc ⟨g, hg⟩)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, hzG'] at h1
      exact h1
    have hbx : b * (k : G) = (k : G) * b * zG⁻¹ := by
      rw [hzG]
      group
    have hzy : zG⁻¹ * (h : G) = (h : G) * zG⁻¹ := by
      have h1 := hzcG (h : G) h.2
      calc zG⁻¹ * (h : G) = zG⁻¹ * ((h : G) * zG) * zG⁻¹ := by group
        _ = zG⁻¹ * (zG * (h : G)) * zG⁻¹ := by rw [h1]
        _ = (h : G) * zG⁻¹ := by group
    have hyb : b * (h : G) = (h : G) * b := Subgroup.mem_centralizer_iff.1 hh b (Set.mem_singleton b)
    have e3 : (k : G)⁻¹ * b = b * zG⁻¹ * (k : G)⁻¹ := by
      calc (k : G)⁻¹ * b = (k : G)⁻¹ * (b * (k : G)) * (k : G)⁻¹ := by group
        _ = (k : G)⁻¹ * ((k : G) * b * zG⁻¹) * (k : G)⁻¹ := by rw [hbx]
        _ = b * zG⁻¹ * (k : G)⁻¹ := by group
    rw [cx, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff] at hg
    rw [hg]
    calc b * ((k : G) * (h : G) * (k : G)⁻¹)
        = ((b * (k : G)) * (h : G)) * (k : G)⁻¹ := by group
      _ = (((k : G) * b * zG⁻¹) * (h : G)) * (k : G)⁻¹ := by rw [hbx]
      _ = (k : G) * b * (zG⁻¹ * (h : G)) * (k : G)⁻¹ := by group
      _ = (k : G) * b * ((h : G) * zG⁻¹) * (k : G)⁻¹ := by rw [hzy]
      _ = (k : G) * (b * (h : G)) * zG⁻¹ * (k : G)⁻¹ := by group
      _ = (k : G) * ((h : G) * b) * zG⁻¹ * (k : G)⁻¹ := by rw [hyb]
      _ = (k : G) * (h : G) * (b * zG⁻¹ * (k : G)⁻¹) := by group
      _ = (k : G) * (h : G) * ((k : G)⁻¹ * b) := by rw [e3]
      _ = ((k : G) * (h : G) * (k : G)⁻¹) * b := by group
  have hHLle : (L ⊓ cx b).subgroupOf L ≤ (FP.fixSub (indAut 3 L b hb)).comap (chevQuotHom 3 L) := by
    intro h hh
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hh
    rw [Subgroup.mem_comap, FP.mem_fixSub]
    exact hfix h hh.2
  have hle : ((L ⊓ cx b).subgroupOf L).map (chevQuotHom 3 L) ≤ FP.fixSub (indAut 3 L b hb) :=
    Subgroup.map_le_iff_le_comap.2 hHLle
  have hnormal : ((((L ⊓ cx b).subgroupOf L).map (chevQuotHom 3 L)).subgroupOf
      (FP.fixSub (indAut 3 L b hb))).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn
    rw [Subgroup.mem_subgroupOf]
    obtain ⟨h, hh, hnh⟩ := Subgroup.mem_map.1 hn
    obtain ⟨k, hk⟩ := hπs (g : PSimple 3 L)
    have hkfix : indAut 3 L b hb (chevQuotHom 3 L k) = chevQuotHom 3 L k := by
      rw [hk]
      exact FP.mem_fixSub.1 g.2
    have hhc : (h : G) ∈ cx b := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hh)).2
    have hkh : ((k * h * k⁻¹ : ↥L) : G) ∈ cx b := by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact hconj k hkfix h hhc
    have hmem : k * h * k⁻¹ ∈ (L ⊓ cx b).subgroupOf L := by
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact ⟨(k * h * k⁻¹ : ↥L).2, hkh⟩
    have heq : (g : PSimple 3 L) * (n : PSimple 3 L) * (g : PSimple 3 L)⁻¹
        = chevQuotHom 3 L (k * h * k⁻¹) := by
      rw [← hk, ← hnh, map_mul, map_mul, map_inv]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, heq]
    exact Subgroup.mem_map_of_mem _ hmem
  have hstep : CFSG.Open.IsSubnormal (((L ⊓ cx b).subgroupOf L).map (chevQuotHom 3 L))
      (FP.fixSub (indAut 3 L b hb)) :=
    CFSG.Open.IsSubnormal.step hle hnormal (CFSG.Open.IsSubnormal.refl _)
  have hsub : CFSG.Open.IsSubnormal ((I.subgroupOf L).map (chevQuotHom 3 L))
      (FP.fixSub (indAut 3 L b hb)) :=
    (CFSG.Open.IsSubnormal.map (chevQuotHom 3 L) (CFSG.Open.IsSubnormal.comap L.subtype hI.2.1)).trans hstep
  let φL : ↥(I.subgroupOf L) →* PSimple 3 L := (chevQuotHom 3 L).comp (I.subgroupOf L).subtype
  have hJeq : φL.range = (I.subgroupOf L).map (chevQuotHom 3 L) := by
    ext x
    simp [φL, MonoidHom.mem_range, Subgroup.mem_map]
  have hJsub : CFSG.Open.IsSubnormal φL.range (FP.fixSub (indAut 3 L b hb)) := by
    rw [hJeq]
    exact hsub
  have hJfix : φL.range ≤ FP.fixSub (indAut 3 L b hb) := by
    rw [hJeq]
    exact hsub.le
  let F : ↥(I.subgroupOf L) →* PSimple 3 I :=
    (chevQuotHom 3 I).comp (Subgroup.subgroupOfEquivOfLe hIL).toMonoidHom
  have hFsurj : Function.Surjective F :=
    (chevQuotHom_surjective 3 I).comp (Subgroup.subgroupOfEquivOfLe hIL).surjective
  have hcen : ∀ x : ↥(I.subgroupOf L), φL x = 1 →
      Subgroup.subgroupOfEquivOfLe hIL x ∈ Subgroup.center ↥I := by
    intro x hx
    have hxL : (x : ↥L) ∈ Subgroup.center ↥L := by
      rw [← hker, MonoidHom.mem_ker]
      exact hx
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.1 hxL ⟨(g : G), hIL g.2⟩
    have h2 : (g : G) * (x : G) = (x : G) * (g : G) := congrArg Subtype.val h1
    apply Subtype.ext
    exact h2
  have hle' : φL.rangeRestrict.ker ≤ F.ker := by
    intro x hx
    rw [MonoidHom.ker_rangeRestrict, MonoidHom.mem_ker] at hx
    rw [MonoidHom.mem_ker]
    exact center_le_ker_chevQuotHom I (hcen x hx)
  let ψ : φL.range →* PSimple 3 I :=
    (QuotientGroup.lift φL.rangeRestrict.ker F hle').comp
      (QuotientGroup.quotientKerEquivOfSurjective φL.rangeRestrict
        (MonoidHom.rangeRestrict_surjective φL)).symm.toMonoidHom
  have hψ : Function.Surjective ψ := by
    intro t
    obtain ⟨x, hx⟩ := hFsurj t
    refine ⟨(QuotientGroup.quotientKerEquivOfSurjective φL.rangeRestrict
      (MonoidHom.rangeRestrict_surjective φL)) (QuotientGroup.mk x), ?_⟩
    simp only [ψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply,
      QuotientGroup.lift_mk]
    exact hx
  exact hF (PSimple 3 L) hsim (indAut 3 L b hb) hMS φL.range hJfix hJsub (PSimple 3 I) hcat ⟨ψ, hψ⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB.KG2F

end
