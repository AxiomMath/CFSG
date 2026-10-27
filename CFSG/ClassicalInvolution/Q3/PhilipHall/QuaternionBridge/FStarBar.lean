module

public import CFSG.ClassicalInvolution.Q3.TA3SmallTools
public import CFSG.ClassicalInvolution.Q3.TL3DichMain

public section

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Q3
open scoped commutatorElement

instance genFittingFitting_normal_inst (Y : Type) [Group Y] : (genFittingFitting Y).Normal :=
  genFittingFitting_normal

variable {Y : Type} [Group Y] [Finite Y]

theorem fstar_quot_quasisimple (hQ : TightFStarQuasisimple Y)
    (hNc : TA3.fstarCenter Y ≤ Subgroup.center Y) :
    IsSimpleGroup ↥(genFittingFStar (Y ⧸ TA3.fstarCenter Y)) ∧
      ∃ a b : ↥(genFittingFStar (Y ⧸ TA3.fstarCenter Y)), a * b ≠ b * a := by
  rw [TA3.genFittingFStar_quotient_fstarCenter Y hQ hNc]
  exact ⟨TA3.isSimpleGroup_fstarBar Y hQ, TA3.exists_ne_comm_fstarBar Y hQ⟩

theorem center_map_le_fitting {L : Subgroup Y} (hLn : L.Normal) :
    (Subgroup.center ↥L).map L.subtype ≤ genFittingFitting Y := by
  set Z : Subgroup Y := (Subgroup.center ↥L).map L.subtype with hZ
  have hZn : Z.Normal := by
    refine ⟨fun z hz y => ?_⟩
    obtain ⟨c, hc'', rfl⟩ := hz
    have hc' : c ∈ Subgroup.center ↥L := hc''
    refine ⟨⟨y * c * y⁻¹, hLn.conj_mem _ c.2 y⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro f
    apply Subtype.ext
    have hf : y⁻¹ * (f : Y) * y ∈ L := by simpa using hLn.conj_mem _ f.2 y⁻¹
    have h' : y⁻¹ * (f : Y) * y * (c : Y) = (c : Y) * (y⁻¹ * (f : Y) * y) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.mp hc' ⟨_, hf⟩)
    show (f : Y) * (y * c * y⁻¹) = y * c * y⁻¹ * f
    calc (f : Y) * (y * c * y⁻¹) = y * ((y⁻¹ * f * y) * c) * y⁻¹ := by group
      _ = y * (c * (y⁻¹ * f * y)) * y⁻¹ := by rw [h']
      _ = y * c * y⁻¹ * f := by group
  have hZcomm : ∀ a b : ↥Z, a * b = b * a := by
    rintro ⟨a, c₁, hc₁, rfl⟩ ⟨b, c₂, hc₂, rfl⟩
    apply Subtype.ext
    show (c₁ : Y) * c₂ = c₂ * c₁
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hc₁ c₂).symm
  have hZnil : Group.IsNilpotent ↥Z := by
    refine Subgroup.isNilpotent_of_ker_le_center (1 : ↥Z →* Unit) ?_
    intro z _
    rw [Subgroup.mem_center_iff]
    intro w
    exact hZcomm w z
  exact le_sSup ⟨hZn, hZnil⟩

theorem subgroupOf_fitting_eq_center {L : Subgroup Y} (hLn : L.Normal)
    (hFc : genFittingFitting Y ≤ Subgroup.center Y) :
    (genFittingFitting Y).subgroupOf L = Subgroup.center ↥L := by
  ext l
  rw [Subgroup.mem_subgroupOf]
  constructor
  · intro h
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hFc h) (g : Y))
  · intro h
    exact center_map_le_fitting hLn ⟨l, h, rfl⟩

theorem fstar_quot_twisted {L : Subgroup Y} (hLc : CFSG.IsComponent L) (hLn : L.Normal)
    (hlayer : CFSG.layer Y = L) (hFc : genFittingFitting Y ≤ Subgroup.center Y) :
    IsSimpleGroup ↥(genFittingFStar (Y ⧸ genFittingFitting Y)) ∧
      ∃ a b : ↥(genFittingFStar (Y ⧸ genFittingFitting Y)), a * b ≠ b * a := by
  classical
  obtain ⟨-, -, hperf, hsimple⟩ := (CFSG.isComponent_iff_open L).mp hLc
  have hLbn : (L.map (QuotientGroup.mk' (genFittingFitting Y))).Normal :=
    hLn.map _ (QuotientGroup.mk'_surjective _)
  have hkerL : ((QuotientGroup.mk' (genFittingFitting Y)).domRestrict L).ker =
      Subgroup.center ↥L := by
    rw [MonoidHom.ker_domRestrict, QuotientGroup.ker_mk']
    exact subgroupOf_fitting_eq_center hLn hFc
  obtain ⟨e⟩ : Nonempty (↥(L.map (QuotientGroup.mk' (genFittingFitting Y))) ≃*
      ↥L ⧸ Subgroup.center ↥L) :=
    ⟨(((QuotientGroup.quotientMulEquivOfEq hkerL).symm.trans
      (QuotientGroup.quotientKerEquivRange _)).trans
        (MulEquiv.subgroupCongr (MonoidHom.domRestrict_range _ _))).symm⟩
  have hLbs : IsSimpleGroup ↥(L.map (QuotientGroup.mk' (genFittingFitting Y))) := by
    have := hsimple
    exact e.isSimpleGroup
  have hnab : ∃ a b : ↥(L.map (QuotientGroup.mk' (genFittingFitting Y))), a * b ≠ b * a := by
    have hs := QuotientGroup.mk'_surjective (Subgroup.center ↥L)
    have hperf' : commutator (↥L ⧸ Subgroup.center ↥L) = ⊤ := by
      rw [_root_.commutator_def, ← Subgroup.map_top_of_surjective _ hs, ← Subgroup.map_commutator,
        ← _root_.commutator_def, hperf, Subgroup.map_top_of_surjective _ hs]
    have := hsimple
    obtain ⟨a, b, hab⟩ := TA3.exists_ne_comm_of_commutator_eq_top hperf'
    exact ⟨e.symm a, e.symm b, fun h => hab (by simpa using congrArg e h)⟩
  have hFS : genFittingFStar Y = L ⊔ genFittingFitting Y := by
    simp only [CFSG.Open.genFittingFStar.eq_sup]
    rw [genFittingLayer_eq_layer, hlayer, sup_comm]
  have hC : Subgroup.centralizer
      ((L.map (QuotientGroup.mk' (genFittingFitting Y)) :
        Subgroup (Y ⧸ genFittingFitting Y)) : Set (Y ⧸ genFittingFitting Y)) = ⊥ := by
    rw [eq_bot_iff]
    intro ybar hy
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (genFittingFitting Y) ybar
    have hcomm : ∀ ℓ ∈ L, y * ℓ * y⁻¹ * ℓ⁻¹ ∈ genFittingFitting Y := by
      intro ℓ hℓ
      have h1 := Subgroup.mem_centralizer_iff.mp hy (QuotientGroup.mk' (genFittingFitting Y) ℓ)
        (Subgroup.mem_map_of_mem _ hℓ)
      simp only [QuotientGroup.mk'_apply] at h1
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [← h1]
      group
    have hcen : ∀ ℓ : ↥L, y * ℓ * y⁻¹ * (ℓ : Y)⁻¹ ∈ Subgroup.center Y := fun ℓ =>
      hFc (hcomm ℓ ℓ.2)
    let ψ : ↥L →* ↥(Subgroup.center Y) :=
      { toFun := fun ℓ => ⟨y * ℓ * y⁻¹ * (ℓ : Y)⁻¹, hcen ℓ⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by
          apply Subtype.ext
          have hb := Subgroup.mem_center_iff.mp (hcen b) ((a : Y)⁻¹)
          simp only [Subgroup.coe_mul, mul_inv_rev]
          calc y * ((a : Y) * b) * y⁻¹ * ((b : Y)⁻¹ * (a : Y)⁻¹)
              = y * a * y⁻¹ * ((y * b * y⁻¹ * (b : Y)⁻¹) * (a : Y)⁻¹) := by group
            _ = y * a * y⁻¹ * ((a : Y)⁻¹ * (y * b * y⁻¹ * (b : Y)⁻¹)) := by rw [hb]
            _ = y * a * y⁻¹ * (a : Y)⁻¹ * (y * b * y⁻¹ * (b : Y)⁻¹) := by group }
    have hker : commutator ↥L ≤ ψ.ker := Abelianization.commutator_subset_ker ψ
    rw [hperf] at hker
    have hyC : ∀ ℓ ∈ L, ℓ * y = y * ℓ := by
      intro ℓ hℓ
      have h1 : ψ ⟨ℓ, hℓ⟩ = 1 := MonoidHom.mem_ker.mp (hker (Subgroup.mem_top _))
      have h2 : y * ℓ * y⁻¹ * ℓ⁻¹ = 1 := congrArg Subtype.val h1
      calc ℓ * y = (y * ℓ * y⁻¹ * ℓ⁻¹)⁻¹ * (y * ℓ) := by group
        _ = y * ℓ := by rw [h2, inv_one, one_mul]
    have hle : genFittingFStar Y ≤ Subgroup.centralizer ({y} : Set Y) := by
      rw [hFS]
      refine sup_le ?_ ?_
      · intro ℓ hℓ
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hyC ℓ hℓ
      · intro f hf
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_center_iff.mp (hFc hf) y).symm
    have hyF : y ∈ Subgroup.centralizer (genFittingFStar Y : Set Y) :=
      Subgroup.mem_centralizer_iff.mpr fun h hh =>
        Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
    have hyFS : y ∈ genFittingFStar Y := CFSG.Adapters.generalized_fitting_self_centralizing Y hyF
    rw [hFS, ← SetLike.mem_coe, Subgroup.mul_normal, Set.mem_mul] at hyFS
    obtain ⟨ℓ, hℓ, f, hf, rfl⟩ := hyFS
    have hℓc : (⟨ℓ, hℓ⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro m
      apply Subtype.ext
      show (m : Y) * ℓ = ℓ * m
      have h1 := hyC m m.2
      have hfc : ∀ a : Y, a * f = f * a := Subgroup.mem_center_iff.mp (hFc hf)
      calc (m : Y) * ℓ = ((m : Y) * (ℓ * f)) * f⁻¹ := by group
        _ = ((ℓ * f) * (m : Y)) * f⁻¹ := by rw [h1]
        _ = ℓ * (f * (m : Y)) * f⁻¹ := by group
        _ = ℓ * ((m : Y) * f) * f⁻¹ := by rw [hfc (m : Y)]
        _ = ℓ * m := by group
    have hℓX : ℓ ∈ genFittingFitting Y := by
      have h2 : (⟨ℓ, hℓ⟩ : ↥L) ∈ (genFittingFitting Y).subgroupOf L := by
        rw [subgroupOf_fitting_eq_center hLn hFc]
        exact hℓc
      exact Subgroup.mem_subgroupOf.mp h2
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (genFittingFitting Y).mul_mem hℓX hf
  haveI := hLbn
  haveI := hLbs
  rw [genFittingFStar_eq_of_normal_simple _ hnab hC]
  exact ⟨hLbs, hnab⟩

end CFSG.ClassicalInvolution.Q3.PhilipHall.QuaternionBridge
