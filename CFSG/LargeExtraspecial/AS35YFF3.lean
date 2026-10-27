module

public import CFSG.LargeExtraspecial.AS35YFPSU
public import CFSG.LargeExtraspecial.AS35YFHub
public import CFSG.LargeExtraspecial.S12InspFamER3b
public import Certificates.Data.ExceptionalSL3

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LargeExtraspecial

open Subgroup CFSG.Blueprint.Fischer
open CFSG.Fischer.Classification (R3 D3 IsF3Form reflBar)

namespace Setting

section Generic

variable {Xh : Type} [Group Xh] {τ : Xh} {𝒜 : Set (MulAut Xh)}

theorem asc_false_of_commutator_hom_simple_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    {K : Subgroup Xh} (hKt : ∀ y ∈ K, y * τ = τ * y) (hKP : ∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K)
    {H : Type*} [Group H] [IsSimpleGroup H] (hH : ¬ Group.IsSolvable H)
    (ρ : commutator K →* H) (hρ : Function.Surjective ρ)
    (hker : ∀ k ∈ ρ.ker, ∀ x, k * x = x * k) : False := by
  have hK1 : (commutator K).map K.subtype = ⁅K, K⁆ := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨ρ', hρ', hker'⟩ := asc_exists_hom_of_mulEquiv
    (((commutator K).equivMapOfInjective _ K.subtype_injective).trans
      (MulEquiv.subgroupCongr hK1)) ρ hρ hker
  exact asc_false_of_hom_simple_gen hub (fun y hy => hKt y (asc_commutator_le_self K hy))
    (fun α hα y hy => asc_aut_mem_commutator α (hKP α hα) hy) hH ρ' hρ' hker'

theorem asc_false_of_R3_gen
    (hub : ∀ K : Subgroup Xh, CFSG.IsQuasisimple K → (∀ y ∈ K, y * τ = τ * y) →
      (∀ α ∈ 𝒜, ∀ y ∈ K, α y ∈ K) → False)
    (h𝒜τ : ∀ α ∈ 𝒜, α τ = τ) {E : Set Xh} (h𝒜E : ∀ α ∈ 𝒜, ∀ e ∈ E, α e ∈ E) (hτE : τ ∈ E)
    {m : ℕ} (hm : 5 ≤ m) {f : LinearMap.BilinForm (ZMod 3) (Fin m → ZMod 3)} (hf : IsF3Form f)
    (h36 : m = 5 → (D3 f).ncard = 36) (ψ : Xh ≃* R3 f) (hψ : ∀ x, x ∈ E ↔ ψ x ∈ D3 f) :
    False := by
  obtain ⟨v, hv, hvt⟩ := CFSG.Fischer.Classification.mem_D3_iff.1 ((hψ τ).1 hτE)
  obtain ⟨f', hf', ⟨e', he'⟩, Φ, -⟩ :=
    CFSG.Fischer.Classification.exists_localQuotient_equiv hf (by omega) hv
  have hmapC : ψ '' LocalClass E τ = LocalClass (D3 f) (reflBar f v) := by
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
  have hmapG : (LocalGroup E τ).map ψ.toMonoidHom = LocalGroup (D3 f) (reflBar f v) := by
    rw [LocalGroup, MonoidHom.map_closure, MulEquiv.coe_toMonoidHom, hmapC]
    rfl
  have hKt : ∀ y ∈ LocalGroup E τ, y * τ = τ * y := fun y hy =>
    mem_centralizer_singleton_iff.mp
      (CFSG.Fischer.Classification.Recognition.R3.localGroup_le_centralizer τ hy)
  have hKP : ∀ α ∈ 𝒜, ∀ y ∈ LocalGroup E τ, α y ∈ LocalGroup E τ := by
    intro α hα y hy
    have hle : LocalGroup E τ ≤ (LocalGroup E τ).comap α.toMonoidHom := by
      rw [LocalGroup, closure_le]
      rintro x ⟨hxE, hxt, hxc⟩
      show α x ∈ LocalGroup E τ
      refine subset_closure ⟨h𝒜E α hα x hxE, fun h => hxt (α.injective ?_), ?_⟩
      · rw [h, h𝒜τ α hα]
      · rw [← h𝒜τ α hα, ← map_mul, ← map_mul, hxc]
    exact hle hy
  let θ : LocalGroup E τ ≃* LocalGroup (D3 f) (reflBar f v) :=
    ((LocalGroup E τ).equivMapOfInjective ψ.toMonoidHom ψ.injective).trans
      (MulEquiv.subgroupCongr hmapG)
  let ρ : LocalGroup E τ →* R3 f' := Φ.toMonoidHom.comp
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
  have hA : (commutator (LocalGroup E τ)).map ρ = commutator (R3 f') := by
    rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective ρ hρ]
  obtain ⟨ρ', hρ', hker'⟩ := S12InspO.exists_commutator_hom ρ hA hker
  have hS : IsSimpleGroup (commutator (R3 f')) := by
    refine r3SimpleInput _ f' hf' (by omega) fun h4 => ?_
    have hm5 : m = 5 := by omega
    subst hm5
    exact S12InspF3.ncard_D3_local_eq_fifteen hf hv (h36 rfl) hf' he'
  have : Finite (R3 f') := (CFSG.Fischer.Classification.pair_R3 hf' (by omega)).1
  have hns : ¬ Group.IsSolvable (commutator (R3 f')) := fun hsol => by
    obtain ⟨a, b, hab⟩ := S12InspF3.nonabelian_commutator_R3_of_four_le hf' (by omega) hS
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr hsol) a b)
  exact asc_false_of_commutator_hom_simple_gen hub hKt hKP hns ρ' hρ' hker'

end Generic

end Setting

namespace S14

theorem asc512InspFor_F3 (h58 : Asc512FiveEightStmt) (hP : Asc512PbarStmt) :
    Asc512InspFor fun (X : Type) [Group X] (D : Set X) => ¬ InspNondeg X D ∧ FischerF3 X D := by
  intro G _ _ S hS hst hfam
  obtain ⟨hND, m, hm, f, hsymm, hnd, hmodel⟩ := hfam
  have hf : IsF3Form f := ⟨hsymm, hnd⟩
  obtain ⟨ψ, hψ⟩ := (CFSG.Fischer.Classification.fischerCentralQuotientModel_iff _).1 hmodel
  obtain ⟨t, ht⟩ := S.DSet_nonempty hS.sixFour hS.hSet_nonempty
  obtain ⟨g, rfl⟩ := Setting.exists_conj_of_mem_DSet S ht
  have hgM := Setting.mem_M_of_mem_ESet S hS.sixFour ht.1
  have hfalse : (m = 5 → (D3 f).ncard = 36) → False := fun h36 =>
    Setting.asc_false_of_R3_gen (Setting.asc_hub hst h58 hS ht hgM)
      (Setting.asc_hub_fix hst hP hS ht hgM) (Setting.asc_hub_E hst)
      ⟨Setting.ascTL ht hgM, S.ρ_mem_DbarAsc ht hgM, rfl⟩ hm hf h36 ψ hψ
  by_cases hm6 : 6 ≤ m
  · exact (hfalse fun h => by omega).elim
  obtain rfl : m = 5 := by omega
  rcases CFSG.Fischer.Classification.R3_five_cases hf with ⟨h45, -⟩ | ⟨h36', -⟩
  · obtain ⟨ψ', hψ'⟩ := CFSG.Fischer.Classification.exists_mulEquiv_U2_four_of_ncard hf h45
    have himg : ψ '' S.EhatAsc = D3 f := by
      ext q
      refine ⟨?_, fun hq => ⟨ψ.symm q, (hψ _).2 (by rwa [MulEquiv.apply_symm_apply]),
        MulEquiv.apply_symm_apply ψ q⟩⟩
      rintro ⟨x, hx, rfl⟩
      exact (hψ x).1 hx
    refine asc512InspFor_psu hP G S hS hst ⟨hND, 4, le_rfl, ?_⟩
    refine CFSG.Fischer.Classification.fischerCentralQuotientModel_iff_U2.2 ⟨ψ.trans ψ', ?_⟩
    rw [MulEquiv.coe_trans, Set.image_comp, himg, hψ']
  · exact (hfalse fun _ => h36').elim

end S14

end CFSG.LargeExtraspecial
