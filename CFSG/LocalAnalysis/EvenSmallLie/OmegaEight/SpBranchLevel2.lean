module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchSPrime
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.SpBranchLevel1Base

public section

namespace CFSG.EvenSmallLie.OmegaEight.SpBranch

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1

variable {G : Type*} [Group G]


namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

theorem inf_normalizer_eq (hH : Hyp ε t TH E₁ S) {P : Subgroup G}
    (hP : IsPGroup 2 P) (hSP : S ≤ P) : P ⊓ normalizer (E₁ : Set G) = S :=
  hH.sylow.maximal _ inf_le_right (hP.to_le inf_le_left) (le_inf hSP hH.sylow.le_normalizer)

end Hyp

theorem exists_class
    {S : Subgroup G} (e : S ≃* SModel) {p : G}
    (hp : p ∈ normalizer (S : Set G)) :
    ∃ s₀ : SModel, ∃ k, k < 8 ∧ ∃ m, m < (sLeaves k).length ∧
      ∀ s : S, e (conjEquiv hp s) = s₀ * ⟨sFm k m (e s).code, sF_lt _ _ _⟩ * s₀⁻¹ := by
  set γ : SModel ≃* SModel := e.symm.trans ((conjEquiv hp).trans e)
  obtain ⟨s₀, k, hk, ds, hds, hγ⟩ := sClassify SModel.codeIso γ
  obtain ⟨m, hm, hmds⟩ := mem_sLeaves hk hds
  refine ⟨s₀, k, hk, m, hm, fun s => ?_⟩
  have hγe : γ (e s) = e (conjEquiv hp s) := by
    simp only [γ, MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [← hγe]
  apply SModel.ext
  have h1 := hγ (e s)
  rw [SModel.codeIso_f, SModel.codeIso_f, SModel.codeIso_f, sConj, cconj] at h1
  rw [SModel.code_mul, SModel.code_mul, SModel.code_inv, h1]
  show sMul (sMul s₀.code (sAutData.F sMul k ds (e s).code)) (sInv s₀.code) =
    sMul (sMul s₀.code (sAutData.F sMul k ((sLeaves k).getD m []) (e s).code)) (sInv s₀.code)
  rw [hmds]

theorem fix_or_map {k m : ℕ}
    (hk : k < 8) (hm : m < (sLeaves k).length) :
    sFixE (sFm k m) = true ∨ sMapF (sFm k m) = true := by
  have h := t1Enum_check
  unfold t1EnumCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, Bool.or_eq_true] at h
  exact h.1.1.2 k hk m hm

namespace Hyp

variable {ε : Eps} {t : G} {TH E₁ S : Subgroup G}

theorem card_EM : Nat.card {x : SModel // x.code < 128} = 128 := by
  rw [Nat.card_congr
    { toFun := fun x => (⟨x.1.code, x.2⟩ : Fin 128)
      invFun := fun c => ⟨⟨c.1, by omega⟩, c.2⟩
      left_inv := fun x => rfl
      right_inv := fun c => rfl }, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem card_E₁ (hH : Hyp ε t TH E₁ S) {e : S ≃* SModel}
    (he : ∀ s : S, ((s : G) = t ↔ e s = SModel.tM ε) ∧ ((s : G) ∈ E₁ ↔ e s ∈ SModel.EM)) :
    Nat.card E₁ = 128 := by
  rw [← card_EM]
  refine Nat.card_congr
    { toFun := fun y => ⟨e ⟨y, hH.sylow.E₁_le y.2⟩, ((he _).2).1 y.2⟩
      invFun := fun x => ⟨e.symm x.1, ((he _).2).2 (by rw [MulEquiv.apply_symm_apply]; exact x.2)⟩
      left_inv := fun y => by simp
      right_inv := fun x => by simp }

theorem exists_of_fp (hH : Hyp ε t TH E₁ S) {e : S ≃* SModel}
    (he : ∀ s : S, ((s : G) = t ↔ e s = SModel.tM ε) ∧ ((s : G) ∈ E₁ ↔ e s ∈ SModel.EM))
    {x : G} (hx : x ∈ normalizer (S : Set G)) {F : ℕ → ℕ}
    (hF : ∀ s : S, (e (conjEquiv hx s)).code = F (e s).code) (hmap : sMapF F = true)
    (hcount : fpCount = 128) {w : SModel} (hw : fpArr[w.code]! = true) :
    ∃ y : G, ∃ hy : y ∈ E₁, e (conjEquiv hx ⟨y, hH.sylow.E₁_le hy⟩) = w := by
  have hfin := SModel.codeIso.finite
  set f : E₁ → {w : SModel // fpArr[w.code]! = true} := fun y =>
    ⟨e (conjEquiv hx ⟨y, hH.sylow.E₁_le y.2⟩), by
      rw [hF]
      unfold sMapF at hmap
      rw [List.all_eq_true] at hmap
      exact hmap _ (List.mem_range.2 ((he _).2.1 y.2))⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    simp only [f] at h1
    have h2 := congrArg Subtype.val (e.injective h1)
    simp only [conjEquiv_apply] at h2
    exact Subtype.ext (by simpa using h2)
  have hcard : Nat.card E₁ = Nat.card {w : SModel // fpArr[w.code]! = true} := by
    rw [hH.card_E₁ he]
    have := SModel.codeIso.card_eq (fun c => fpArr[c]!)
    rw [show Nat.card {w : SModel // fpArr[w.code]! = true} =
      Nat.card {h : SModel // (fun c => fpArr[c]!) (SModel.codeIso.f h) = true} from rfl, this]
    rw [← hcount]; rfl
  obtain ⟨y, hy⟩ := ((Nat.bijective_iff_injective_and_card f).2 ⟨hinj, hcard⟩).2 ⟨w, hw⟩
  exact ⟨y, y.2, congrArg Subtype.val hy⟩

theorem maxN
    [Finite G] (hH : Hyp ε t TH E₁ S) {e : S ≃* SModel}
    (he : ∀ s : S, ((s : G) = t ↔ e s = SModel.tM ε) ∧ ((s : G) ∈ E₁ ↔ e s ∈ SModel.EM))
    {x : G} (hx : x ∈ normalizer (S : Set G)) {k₁ m₁ : ℕ} (hk₁ : k₁ < 8)
    (hm₁ : m₁ < (sLeaves k₁).length)
    (hF : ∀ s : S, (e (conjEquiv hx s)).code = sFm k₁ m₁ (e s).code)
    (hmove : sFixE (sFm k₁ m₁) = false) (hcount : fpCount = 128) :
    ∀ P : Subgroup G, P ≤ normalizer (S : Set G) → IsPGroup 2 P → S ⊔ zpowers x ≤ P →
      P = S ⊔ zpowers x := by
  intro P hPN hP hTP
  have hSP : S ≤ P := le_sup_left.trans hTP
  have hxP : x ∈ P := hTP (mem_sup_right (mem_zpowers x))
  have hPE := hH.inf_normalizer_eq hP hSP
  have hmap : sMapF (sFm k₁ m₁) = true := (fix_or_map hk₁ hm₁).resolve_left (by rw [hmove]; simp)
  refine le_antisymm (fun p hp => ?_) hTP
  obtain ⟨s₀, k, hk, m, hm, hcl⟩ := exists_class e (hPN hp)
  rcases fix_or_map hk hm with hfix | hfp
  ·
    have hmaps : ∀ y ∈ E₁, p * y * p⁻¹ ∈ E₁ := by
      intro y hy
      have hyS := hH.sylow.E₁_le hy
      have h1 := hcl ⟨y, hyS⟩
      have hw : (⟨sFm k m (e ⟨y, hyS⟩).code, sF_lt _ _ _⟩ : SModel) ∈ SModel.EM := by
        unfold sFixE at hfix
        rw [List.all_eq_true] at hfix
        have := hfix _ (List.mem_range.2 ((he ⟨y, hyS⟩).2.1 hy))
        show sFm k m (e ⟨y, hyS⟩).code < 128
        exact of_decide_eq_true this
      have h2 := SModel.conj_mem_EM s₀ hw
      rw [← h1] at h2
      exact (he _).2.2 h2
    have hpE : p ∈ normalizer (E₁ : Set G) := mem_normalizer_of_maps hmaps
    have : p ∈ P ⊓ normalizer (E₁ : Set G) := ⟨hp, hpE⟩
    rw [hPE] at this
    exact mem_sup_left this
  ·
    have hmaps : ∀ y ∈ E₁, (x⁻¹ * p) * y * (x⁻¹ * p)⁻¹ ∈ E₁ := by
      intro y hy
      have hyS := hH.sylow.E₁_le hy
      have h1 := hcl ⟨y, hyS⟩
      set w : SModel := ⟨sFm k m (e ⟨y, hyS⟩).code, sF_lt _ _ _⟩
      have hw : fpArr[w.code]! = true := by
        unfold sMapF at hfp
        rw [List.all_eq_true] at hfp
        exact hfp _ (List.mem_range.2 ((he ⟨y, hyS⟩).2.1 hy))
      obtain ⟨y', hy', hy'w⟩ := hH.exists_of_fp he hx hF hmap hcount hw
      set σ : S := e.symm s₀
      have hpy : p * y * p⁻¹ = (σ : G) * (x * y' * x⁻¹) * (σ : G)⁻¹ := by
        have h3 : e (conjEquiv (hPN hp) ⟨y, hyS⟩) =
            e (σ * conjEquiv hx ⟨y', hH.sylow.E₁_le hy'⟩ * σ⁻¹) := by
          rw [h1, map_mul, map_mul, map_inv, hy'w]
          simp [σ]
        have h4 := congrArg Subtype.val (e.injective h3)
        simpa [conjEquiv_apply] using h4
      have hτ : x⁻¹ * σ * x ∈ S := by
        have := (mem_normalizer_iff.1 (inv_mem hx) σ).1 σ.2
        simpa using this
      have hτE := hH.sylow.le_normalizer hτ
      have e1 : (x⁻¹ * p) * y * (x⁻¹ * p)⁻¹ = (x⁻¹ * σ * x) * y' * (x⁻¹ * σ * x)⁻¹ := by
        calc (x⁻¹ * p) * y * (x⁻¹ * p)⁻¹ = x⁻¹ * (p * y * p⁻¹) * x := by group
          _ = x⁻¹ * ((σ : G) * (x * y' * x⁻¹) * (σ : G)⁻¹) * x := by rw [hpy]
          _ = (x⁻¹ * σ * x) * y' * (x⁻¹ * σ * x)⁻¹ := by group
      rw [e1]
      exact (mem_normalizer_iff.1 hτE y').1 hy'
    have hqE : x⁻¹ * p ∈ normalizer (E₁ : Set G) := mem_normalizer_of_maps hmaps
    have : x⁻¹ * p ∈ P ⊓ normalizer (E₁ : Set G) := ⟨P.mul_mem (P.inv_mem hxP) hp, hqE⟩
    rw [hPE] at this
    have e2 : p = x * (x⁻¹ * p) := by group
    rw [e2]
    exact mul_mem (mem_sup_right (mem_zpowers x)) (mem_sup_left this)

end Hyp

end CFSG.EvenSmallLie.OmegaEight.SpBranch
