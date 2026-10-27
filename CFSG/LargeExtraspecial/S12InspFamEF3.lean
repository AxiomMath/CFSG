module

public import CFSG.LargeExtraspecial.S12InspFamDO
public import CFSG.LargeExtraspecial.S12InspFamEF3Count

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup Module CFSG.RankThree.OrthogonalInvolutions CFSG.Blueprint.Fischer
open CFSG.Fischer.Classification (R3 D3 IsF3Form reflBar)

@[expose] def R3SimpleInput : Prop :=
  ∀ (n : ℕ) (f : LinearMap.BilinForm (ZMod 3) (Fin n → ZMod 3)), IsF3Form f → 4 ≤ n →
    (n = 4 → (D3 f).ncard = 15) → IsSimpleGroup (commutator (R3 f))

open Matrix in
@[expose] def InspPSU4 : Prop := InspFor fun (X : Type) [Group X] (D : Set X) =>
  ¬ InspNondeg X D ∧ CFSG.Open.fischerCentralQuotientModel D
    (CFSG.Open.fischerMatrixGroup fun A => A.det = 1 ∧
      ∀ x y, CFSG.Open.fischerHermitianF4 4 (A *ᵥ x) (A *ᵥ y) = CFSG.Open.fischerHermitianF4 4 x y)
    (CFSG.Open.fischerTransvections (CFSG.Open.fischerHermitianF4 4)
      fun v => v ≠ 0 ∧ CFSG.Open.fischerHermitianF4 4 v v = 0)

theorem inspPSU4_of (h : InspPSU) : InspPSU4 := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred hX
  exact h G S g t haQ hne hn ht htA hS hred ⟨hX.1, 4, le_rfl, hX.2⟩

namespace Setting

variable {G : Type} [Group G] [Finite G] {S : Setting G}

theorem false_of_commutator_hom_simple {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {K : Subgroup S.O} (hKM : K ≤ S.Mbar)
    (hKt : ∀ c ∈ K, c * t = t * c) (hconj : ∀ ℓ ∈ S.Lbar g, ∀ c ∈ K, ℓ * c * ℓ⁻¹ ∈ K)
    {H : Type*} [Group H] [Finite H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : commutator K →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  have hιK : (⊤ : Subgroup K).map K.subtype = K := by
    rw [← MonoidHom.range_eq_map, range_subtype]
  have hmap : (commutator K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, hιK]
  obtain ⟨e⟩ : Nonempty (commutator K ≃* (⁅K, K⁆ : Subgroup S.O)) :=
    ⟨((commutator K).equivMapOfInjective K.subtype K.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)⟩
  have hKK : ⁅K, K⁆ ≤ K := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hx hy) (K.inv_mem hx)) (K.inv_mem hy)
  have hconj' : ∀ ℓ ∈ S.Lbar g, ∀ c ∈ ⁅K, K⁆, ℓ * c * ℓ⁻¹ ∈ ⁅K, K⁆ := by
    intro ℓ hℓ c hc
    have hle : K.map (MulAut.conj ℓ).toMonoidHom ≤ K := by
      rintro _ ⟨x, hx, rfl⟩
      exact hconj ℓ hℓ x hx
    have h1 : (⁅K, K⁆ : Subgroup S.O).map (MulAut.conj ℓ).toMonoidHom ≤ ⁅K, K⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono hle hle
    exact h1 ⟨c, hc, rfl⟩
  have hLK : S.Lbar g ≤ normalizer ((⁅K, K⁆ : Subgroup S.O) : Set S.O) := fun ℓ hℓ =>
    mem_normalizer_of_conj_le (hconj' ℓ hℓ) (hconj' ℓ⁻¹ ((S.Lbar g).inv_mem hℓ))
  obtain ⟨ρ', hρ', hker'⟩ := s12_exists_hom_of_mulEquiv e ρ hρ hker
  exact false_of_hom_simple haQ hne hn ht htA (hKK.trans hKM) (fun c hc => hKt c (hKK hc)) hLK
    hH ρ' hρ' hker'

set_option maxHeartbeats 400000 in
theorem false_of_R3 (hR3 : R3SimpleInput) {g : G} (haQ : g * S.z * g⁻¹ ∈ S.QG)
    (hne : g * S.z * g⁻¹ ≠ S.z) (hn : 3 ≤ S.width) {t : S.O} (ht : t ∈ S.Lbar g)
    (htA : IsTypeA S.q (t : S.Qt ≃ₗ[ZMod 2] S.Qt) 2) {m : ℕ} (hm : 5 ≤ m)
    {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (h36 : m = 5 → (D3 f).ncard = 36)
    (ψ : S.Xbar12 g ≃* R3 f)
    (hψ : ∀ x, x ∈ (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ↔ ψ x ∈ D3 f) : False := by
  have htX : t ∈ S.Xbar12 g := subset_Xbar12 (mem_Ebar12_of_mem_Lbar ht htA)
  obtain ⟨v, hv, hvt⟩ := CFSG.Fischer.Classification.mem_D3_iff.1
    ((hψ ⟨t, htX⟩).1 (mem_Ebar12_of_mem_Lbar ht htA))
  obtain ⟨f', hf', ⟨e', he'⟩, Φ, -⟩ :=
    CFSG.Fischer.Classification.exists_localQuotient_equiv hf (by omega) hv
  have hmapC : ψ '' LocalClass (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⟨t, htX⟩ =
      LocalClass (D3 f) (reflBar f v) := by
    ext q
    constructor
    · rintro ⟨x, ⟨hxE, hxt, hxc⟩, rfl⟩
      refine ⟨(hψ x).1 hxE, fun h => hxt (ψ.injective (by rw [h, hvt])), ?_⟩
      rw [hvt, ← map_mul, ← map_mul, hxc]
    · rintro ⟨hqD, hqt, hqc⟩
      refine ⟨ψ.symm q, ⟨(hψ _).2 (by rwa [MulEquiv.apply_symm_apply]), fun h => hqt ?_, ?_⟩,
        MulEquiv.apply_symm_apply ψ q⟩
      · rw [hvt, ← h, MulEquiv.apply_symm_apply]
      · apply ψ.injective
        rw [map_mul, map_mul, MulEquiv.apply_symm_apply, ← hvt, hqc]
  have hmapG : (LocalGroup (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⟨t, htX⟩).map
      ψ.toMonoidHom = LocalGroup (D3 f) (reflBar f v) := by
    rw [LocalGroup, MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, hmapC]
    rfl
  obtain ⟨K, hKdef⟩ : ∃ K : Subgroup S.O, K =
      (LocalGroup (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⟨t, htX⟩).map
        (S.Xbar12 g).subtype := ⟨_, rfl⟩
  have hKM : K ≤ S.Mbar := hKdef ▸ (map_subtype_le _).trans Xbar12_le_Mbar
  have hKt : ∀ c ∈ K, c * t = t * c := by
    rw [hKdef]
    rintro _ ⟨x, hx, rfl⟩
    have := congrArg Subtype.val (mem_centralizer_singleton_iff.mp
      (CFSG.Fischer.Classification.Recognition.R3.localGroup_le_centralizer _ hx))
    simpa using this
  have hKcl : K = closure (Subtype.val ''
      LocalClass (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⟨t, htX⟩) := by
    rw [hKdef, LocalGroup, MonoidHom.map_closure, coe_subtype]
  have hconj : ∀ ℓ ∈ S.Lbar g, ∀ c ∈ K, ℓ * c * ℓ⁻¹ ∈ K := by
    intro ℓ hℓ
    rw [hKcl]
    refine conj_mem_closure_of_conj_mem ?_
    rintro _ ⟨x, ⟨hxE, hxt, hxc⟩, rfl⟩
    have hℓM := S.Lbar_le_Mbar g hℓ
    have hℓt : ℓ * t = t * ℓ :=
      congrArg Subtype.val ((S.isElementaryAbelian_Lbar haQ).is_comm.comm ⟨ℓ, hℓ⟩ ⟨t, ht⟩)
    have hxc' : (x : S.O) * t = t * x := congrArg Subtype.val hxc
    have hE := conj_mem_Ebar12 hℓM hxE
    refine ⟨⟨ℓ * x * ℓ⁻¹, subset_Xbar12 hE⟩, ⟨hE, fun h => hxt (Subtype.ext ?_), ?_⟩, rfl⟩
    · have h1 : ℓ * (x : S.O) * ℓ⁻¹ = t := congrArg Subtype.val h
      calc (x : S.O) = ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * ℓ := by group
        _ = ℓ⁻¹ * t * ℓ := by rw [h1]
        _ = t := by rw [mul_assoc, ← hℓt, ← mul_assoc, inv_mul_cancel, one_mul]
    · apply Subtype.ext
      change ℓ * (x : S.O) * ℓ⁻¹ * t = t * (ℓ * x * ℓ⁻¹)
      have hℓt' : ℓ⁻¹ * t = t * ℓ⁻¹ := by
        calc ℓ⁻¹ * t = ℓ⁻¹ * (t * ℓ) * ℓ⁻¹ := by group
          _ = ℓ⁻¹ * (ℓ * t) * ℓ⁻¹ := by rw [hℓt]
          _ = t * ℓ⁻¹ := by group
      calc ℓ * (x : S.O) * ℓ⁻¹ * t = ℓ * (x * t) * ℓ⁻¹ := by rw [mul_assoc, hℓt']; group
        _ = ℓ * (t * x) * ℓ⁻¹ := by rw [hxc']
        _ = (ℓ * t) * x * ℓ⁻¹ := by group
        _ = t * (ℓ * x * ℓ⁻¹) := by rw [hℓt]; group
  let θ : K ≃* LocalGroup (D3 f) (reflBar f v) :=
    (MulEquiv.subgroupCongr hKdef).trans
      ((((LocalGroup (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⟨t, htX⟩).equivMapOfInjective
        _ (S.Xbar12 g).subtype_injective).symm.trans
      (((LocalGroup (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) ⟨t, htX⟩).equivMapOfInjective
        ψ.toMonoidHom ψ.injective).trans (MulEquiv.subgroupCongr hmapG))))
  let ρ : K →* R3 f' := Φ.toMonoidHom.comp
    ((QuotientGroup.mk' (center (LocalGroup (D3 f) (reflBar f v)))).comp θ.toMonoidHom)
  have hρ : Function.Surjective ρ :=
    Φ.surjective.comp ((QuotientGroup.mk'_surjective _).comp θ.surjective)
  have hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k := by
    intro k hk x
    have h1 : (QuotientGroup.mk' (center (LocalGroup (D3 f) (reflBar f v)))) (θ k) = 1 := by
      have := MonoidHom.mem_ker.mp hk
      simpa [ρ] using this
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    apply θ.injective
    rw [map_mul, map_mul]
    exact (mem_center_iff.mp h1 (θ x)).symm
  have hA : (commutator K).map ρ = commutator (R3 f') := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ρ hρ]
  obtain ⟨ρ', hρ', hker'⟩ := S12InspO.exists_commutator_hom ρ hA hker
  have hS : IsSimpleGroup (commutator (R3 f')) := by
    refine hR3 _ f' hf' (by omega) fun h4 => ?_
    have hm5 : m = 5 := by omega
    subst hm5
    exact S12InspF3.ncard_D3_local_eq_fifteen hf hv (h36 rfl) hf' he'
  have : Finite (R3 f') := (CFSG.Fischer.Classification.pair_R3 hf' (by omega)).1
  have hns : ¬ Group.IsSolvable (commutator (R3 f')) := fun hsol => by
    obtain ⟨a, b, hab⟩ := S12InspF3.nonabelian_commutator_R3_of_four_le hf' (by omega) hS
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)
  exact false_of_commutator_hom_simple haQ hne hn ht htA hKM hKt hconj hns ρ' hρ' hker'

end Setting

theorem inspF3_of (hR3 : R3SimpleInput) (hPSU : InspPSU4) : InspF3 := by
  intro G _ _ _ S g t haQ hne hn ht htA hS hred h
  obtain ⟨hND, m, hm, f, hsymm, hnd, hmodel⟩ := h
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff _).1 hmodel
  by_cases hm6 : 6 ≤ m
  · exact (Setting.false_of_R3 hR3 haQ hne (by omega) ht htA hm hf (fun h => by omega) ψ
      hψ).elim
  obtain rfl : m = 5 := by omega
  rcases CFSG.Fischer.Classification.R3_five_cases hf with ⟨h45, -⟩ | ⟨h36', -⟩
  · obtain ⟨ψ', hψ'⟩ := CFSG.Fischer.Classification.exists_mulEquiv_U2_four_of_ncard hf h45
    have himg : ψ '' (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g)) = D3 f := by
      ext q
      refine ⟨?_, fun hq => ⟨ψ.symm q, (hψ _).2 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply ψ q⟩⟩
      rintro ⟨x, hx, rfl⟩
      exact (hψ x).1 hx
    have hmodel' : CFSG.Open.fischerCentralQuotientModel
        (Subtype.val ⁻¹' S.Ebar12 g : Set (S.Xbar12 g))
        (CFSG.Fischer.Classification.Unitary.SUm 4)
        (CFSG.Fischer.Classification.Unitary.TU 4) := by
      refine CFSG.Fischer.Classification.fischerCentralQuotientModel_iff_U2.2 ⟨ψ.trans ψ', ?_⟩
      rw [MulEquiv.coe_trans, Set.image_comp, himg, hψ']
    exact hPSU G S g t haQ hne hn ht htA hS hred ⟨hND, hmodel'⟩
  · exact (Setting.false_of_R3 hR3 haQ hne (by omega) ht htA le_rfl hf (fun _ => h36') ψ
      hψ).elim

end CFSG.LargeExtraspecial
