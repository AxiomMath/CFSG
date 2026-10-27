module

public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention

public section

namespace CFSG.ComponentClassification.CatalogueBPrimeJoin

open CFSG CFSG.LocalCores
open scoped Pointwise commutatorElement

variable {X : Type*} [Group X]

theorem commutatorElement_mul_central_left {g h z : X} (hz : z ∈ Subgroup.center X) :
    ⁅g * z, h⁆ = ⁅g, h⁆ := by
  have hz' := Subgroup.mem_center_iff.1 hz
  rw [commutatorElement_def, commutatorElement_def, mul_inv_rev, mul_assoc g z h, ← hz' h,
    ← mul_assoc g h z]
  group

theorem commutatorElement_mul_central_right {g h z : X} (hz : z ∈ Subgroup.center X) :
    ⁅g, h * z⁆ = ⁅g, h⁆ := by
  rw [← commutatorElement_inv, commutatorElement_mul_central_left hz, commutatorElement_inv]

theorem commutator_sup_central (A K : Subgroup X) (hK : K ≤ Subgroup.center X) :
    ⁅A ⊔ K, A ⊔ K⁆ = ⁅A, A⁆ := by
  have : K.Normal := ⟨fun k hk g => by
    rw [Subgroup.mem_center_iff.1 (hK hk) g, mul_inv_cancel_right]
    exact hk⟩
  refine le_antisymm (Subgroup.commutator_le.2 fun g hg h hh => ?_)
    (Subgroup.commutator_mono le_sup_left le_sup_left)
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at hg hh
  obtain ⟨a, ha, k, hk, rfl⟩ := hg
  obtain ⟨b, hb, l, hl, rfl⟩ := hh
  change ⁅a * k, b * l⁆ ∈ ⁅A, A⁆
  rw [commutatorElement_mul_central_left (hK hk), commutatorElement_mul_central_right (hK hl)]
  exact Subgroup.commutator_mem_commutator ha hb

variable [Finite X] {p : ℕ} [Fact p.Prime]

theorem primeResidual_eq_top_of_central_surjective {M : Type*} [Group M] [Group.IsPerfect X]
    (g : X →* M) (hg : Function.Surjective g) (hcentral : g.ker ≤ Subgroup.center X)
    (hM : primeResidual p M = ⊤) : primeResidual p X = ⊤ := by
  have hsup : primeResidual p X ⊔ g.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, primeResidual_map_surjective p g hg, hM, Subgroup.comap_top]
  have htop : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = (⊤ : Subgroup X) := by
    rw [← _root_.commutator_def]
    exact Group.isPerfect_def.1 inferInstance
  have := primeResidual_characteristic p X
  refine eq_top_iff.2 ?_
  calc (⊤ : Subgroup X) = ⁅primeResidual p X ⊔ g.ker, primeResidual p X ⊔ g.ker⁆ := by
        rw [hsup, htop]
    _ = ⁅primeResidual p X, primeResidual p X⁆ := commutator_sup_central _ _ hcentral
    _ ≤ primeResidual p X := Subgroup.commutator_le_left _ _

theorem central_kernel_core_quotient_quasisimple_iff {M : Type*} [Group M] [Finite M]
    [Group.IsPerfect X] (g : X →* M) (hg : Function.Surjective g)
    (hcentral : g.ker ≤ Subgroup.center X) (hpker : IsPGroup p g.ker) :
    IsQuasisimple (X ⧸ pPrimeCore p X) ↔ IsQuasisimple (M ⧸ pPrimeCore p M) := by
  have hcore := central_p_kernel_prime_core_image g hg hcentral hpker
  have hle : pPrimeCore p X ≤ ((QuotientGroup.mk' (pPrimeCore p M)).comp g).ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    change ((g x : M) : M ⧸ pPrimeCore p M) = 1
    rw [QuotientGroup.eq_one_iff, hcore]
    exact Subgroup.mem_map_of_mem g hx
  have hψ : Function.Surjective
      (QuotientGroup.lift (pPrimeCore p X) ((QuotientGroup.mk' (pPrimeCore p M)).comp g) hle) :=
    QuotientGroup.lift_surjective_of_surjective (pPrimeCore p X)
      ((QuotientGroup.mk' (pPrimeCore p M)).comp g) ((QuotientGroup.mk'_surjective _).comp hg) hle
  have hker : (QuotientGroup.lift (pPrimeCore p X)
      ((QuotientGroup.mk' (pPrimeCore p M)).comp g) hle).ker ≤
        Subgroup.center (X ⧸ pPrimeCore p X) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : g x ∈ pPrimeCore p M := by
      have h1 := MonoidHom.mem_ker.1 hq
      change ((g x : M) : M ⧸ pPrimeCore p M) = 1 at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    rw [hcore] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
    have hz : y⁻¹ * x ∈ Subgroup.center X := hcentral (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hyx, inv_mul_cancel])
    have hmk : (x : X ⧸ pPrimeCore p X) = ((y⁻¹ * x : X) : X ⧸ pPrimeCore p X) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, (QuotientGroup.eq_one_iff y).2 hy, inv_one,
        one_mul]
    rw [hmk, Subgroup.mem_center_iff]
    intro w
    obtain ⟨w', rfl⟩ := QuotientGroup.mk_surjective w
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 hz w']
  have hperf : Group.IsPerfect (X ⧸ pPrimeCore p X) :=
    Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
  exact isQuasisimple_iff_of_surjective hperf _ hψ hker

variable {H : Type*} [Group H] [Finite H]

theorem central_p_quotient_p_component_bijection (f : X →* H) (hf : Function.Surjective f)
    (hcentral : f.ker ≤ Subgroup.center X) (hpker : IsPGroup p f.ker) :
    Set.BijOn (fun L : Subgroup X => L.map f) {L | IsPComponent p L} {M | IsPComponent p M} ∧
    (∀ M : Subgroup H, IsPComponent p M →
      IsPComponent p ⁅M.comap f, M.comap f⁆ ∧ ⁅M.comap f, M.comap f⁆.map f = M) ∧
    ∀ L : Subgroup X, IsPComponent p L → (IsQuasisimple L ↔ IsQuasisimple (L.map f)) := by
  have hrestr : ∀ L : Subgroup X, (f.subgroupMap L).ker ≤ Subgroup.center L ∧
      IsPGroup p (f.subgroupMap L).ker := by
    intro L
    have hmem : ∀ x ∈ (f.subgroupMap L).ker, (x : X) ∈ f.ker := fun x hx =>
      MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hx))
    refine ⟨fun x hx => Subgroup.mem_center_iff.2 fun y => Subtype.ext
      (Subgroup.mem_center_iff.1 (hcentral (hmem x hx)) y), ?_⟩
    let ι : (f.subgroupMap L).ker →* f.ker :=
      { toFun := fun x => ⟨x.1.1, hmem x.1 x.2⟩, map_one' := rfl, map_mul' := fun _ _ => rfl }
    exact hpker.of_injective ι fun a b h => Subtype.ext (Subtype.ext
      (show ((ι a : f.ker) : X) = ((ι b : f.ker) : X) from congrArg Subtype.val h))
  have hfwd : ∀ L : Subgroup X, IsPComponent p L → IsPComponent p (L.map f) := by
    intro L hL
    obtain ⟨hLsub, hLgen, hLq⟩ := (pComponent_iff_subnormal_generated_quasisimple p L).1 hL
    have := CatalogueBHeldSmallCore.pComponent_perfect p L hL
    have hgen : primeResidual p (L.map f) = ⊤ := by
      rw [← primeResidual_map_surjective p (f.subgroupMap L) (f.subgroupMap_surjective L), hLgen]
      exact Subgroup.map_top_of_surjective _ (f.subgroupMap_surjective L)
    exact (pComponent_iff_subnormal_generated_quasisimple p _).2 ⟨hLsub.map hf, hgen,
      (central_kernel_core_quotient_quasisimple_iff (f.subgroupMap L) (f.subgroupMap_surjective L)
        (hrestr L).1 (hrestr L).2).1 hLq⟩
  have hrecover : ∀ L : Subgroup X, IsPComponent p L →
      ⁅(L.map f).comap f, (L.map f).comap f⁆ = L := by
    intro L hL
    have := CatalogueBHeldSmallCore.pComponent_perfect p L hL
    rw [Subgroup.comap_map_eq, commutator_sup_central L f.ker hcentral,
      Subgroup.commutator_eq_self]
  have hinv : ∀ M : Subgroup H, IsPComponent p M →
      IsPComponent p ⁅M.comap f, M.comap f⁆ ∧ ⁅M.comap f, M.comap f⁆.map f = M := by
    intro M hM
    obtain ⟨hMsub, hMgen, hMq⟩ := (pComponent_iff_subnormal_generated_quasisimple p M).1 hM
    have := CatalogueBHeldSmallCore.pComponent_perfect p M hM
    have hmap : ⁅M.comap f, M.comap f⁆.map f = M := by
      rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hf,
        Subgroup.commutator_eq_self]
    refine ⟨?_, hmap⟩
    have hV : M.comap f = ⁅M.comap f, M.comap f⁆ ⊔ f.ker := by
      calc M.comap f = (⁅M.comap f, M.comap f⁆.map f).comap f := by rw [hmap]
        _ = _ := Subgroup.comap_map_eq _ _
    have hLperf : Group.IsPerfect ↥(⁅M.comap f, M.comap f⁆ : Subgroup X) := by
      refine Subgroup.isPerfect_iff.2 ?_
      calc ⁅⁅M.comap f, M.comap f⁆, ⁅M.comap f, M.comap f⁆⁆ =
          ⁅⁅M.comap f, M.comap f⁆ ⊔ f.ker, ⁅M.comap f, M.comap f⁆ ⊔ f.ker⁆ :=
            (commutator_sup_central _ _ hcentral).symm
        _ = ⁅M.comap f, M.comap f⁆ := by rw [← hV]
    have hLsub : ⁅M.comap f, M.comap f⁆.IsSubnormal := by
      have heq : ⁅M.comap f, M.comap f⁆ = (commutator (M.comap f)).map (M.comap f).subtype := by
        rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
      rw [heq]
      have hn : (commutator (M.comap f)).Normal := inferInstance
      exact hn.isSubnormal.trans' (hMsub.comap f)
    have hgen : primeResidual p (⁅M.comap f, M.comap f⁆.map f) = ⊤ :=
      (congrArg (fun Y : Subgroup H => primeResidual p Y = ⊤) hmap).mpr hMgen
    have hq : IsQuasisimple ((⁅M.comap f, M.comap f⁆.map f) ⧸
        pPrimeCore p (⁅M.comap f, M.comap f⁆.map f)) :=
      (congrArg (fun Y : Subgroup H => IsQuasisimple (Y ⧸ pPrimeCore p Y)) hmap).mpr hMq
    exact (pComponent_iff_subnormal_generated_quasisimple p _).2 ⟨hLsub,
      primeResidual_eq_top_of_central_surjective (f.subgroupMap ⁅M.comap f, M.comap f⁆)
        (f.subgroupMap_surjective _) (hrestr _).1 hgen,
      (central_kernel_core_quotient_quasisimple_iff (f.subgroupMap ⁅M.comap f, M.comap f⁆)
        (f.subgroupMap_surjective _) (hrestr _).1 (hrestr _).2).2 hq⟩
  refine ⟨⟨fun L hL => hfwd L hL, fun L₁ hL₁ L₂ hL₂ h => ?_, fun M hM => ?_⟩, hinv,
    fun L hL => ?_⟩
  · rw [← hrecover L₁ hL₁, ← hrecover L₂ hL₂]
    change L₁.map f = L₂.map f at h
    rw [h]
  · exact ⟨_, (hinv M hM).1, (hinv M hM).2⟩
  · have := CatalogueBHeldSmallCore.pComponent_perfect p L hL
    exact isQuasisimple_iff_of_surjective inferInstance (f.subgroupMap L)
      (f.subgroupMap_surjective L) (hrestr L).1

end CFSG.ComponentClassification.CatalogueBPrimeJoin
