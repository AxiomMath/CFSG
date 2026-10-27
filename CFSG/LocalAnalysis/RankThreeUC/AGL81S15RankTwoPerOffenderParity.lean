module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.GroupTheory.PGroup
import Mathlib.Algebra.Module.ZMod

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15

variable {G : Type} [Group G] {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y]
variable {M₀ M₁ : Submodule (ZMod 2) Y}

private lemma add_self_eq_zero' (y : Y) : y + y = 0 := by
  rw [← two_smul (ZMod 2) y]
  rw [show (2 : ZMod 2) = 0 by decide, zero_smul]

private def HInv (ρY : Representation (ZMod 2) G Y) (H : Subgroup G)
    (W : Submodule (ZMod 2) Y) : Prop :=
  ∀ h ∈ H, ∀ y ∈ W, ρY h y ∈ W

private def HIrred (ρY : Representation (ZMod 2) G Y) (H : Subgroup G)
    (W : Submodule (ZMod 2) Y) : Prop :=
  W ≠ ⊥ ∧ HInv ρY H W ∧
    ∀ W' : Submodule (ZMod 2) Y, W' ≤ W → HInv ρY H W' → W' = ⊥ ∨ W' = W

private abbrev IrrSet (ρY : Representation (ZMod 2) G Y) (H : Subgroup G) : Type _ :=
  { W : Submodule (ZMod 2) Y // HIrred ρY H W }

private lemma HInv.inf {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {W W' : Submodule (ZMod 2) Y} (hW : HInv ρY H W) (hW' : HInv ρY H W') :
    HInv ρY H (W ⊓ W') := by
  intro h hh y hy
  rw [Submodule.mem_inf] at hy ⊢
  exact ⟨hW h hh y hy.1, hW' h hh y hy.2⟩

private lemma HInv.map_of_comm {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {W : Submodule (ZMod 2) Y} (hW : HInv ρY H W) (e : Y →ₗ[ZMod 2] Y)
    (he : ∀ (h : G), h ∈ H → ∀ y : Y, e (ρY h y) = ρY h (e y)) :
    HInv ρY H (Submodule.map e W) := by
  intro h hh x hx
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
  rw [← he h hh w]
  exact Submodule.mem_map_of_mem (hW h hh w hw)

private lemma HInv.comap_of_comm {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {W : Submodule (ZMod 2) Y} (hW : HInv ρY H W) (e : Y →ₗ[ZMod 2] Y)
    (he : ∀ (h : G), h ∈ H → ∀ y : Y, e (ρY h y) = ρY h (e y)) :
    HInv ρY H (Submodule.comap e W) := by
  intro h hh y hy
  rw [Submodule.mem_comap] at hy ⊢
  rw [he h hh y]
  exact hW h hh (e y) hy

private lemma HIrred.map_of_comm {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {W : Submodule (ZMod 2) Y} (hW : HIrred ρY H W) (e : Y ≃ₗ[ZMod 2] Y)
    (he : ∀ (h : G), h ∈ H → ∀ y : Y, e (ρY h y) = ρY h (e y)) :
    HIrred ρY H (Submodule.map (e : Y →ₗ[ZMod 2] Y) W) := by
  refine ⟨?_, HInv.map_of_comm hW.2.1 _ he, ?_⟩
  · intro h
    exact hW.1 ((Submodule.map_eq_bot_iff (e := e)).mp h)
  · intro W' hW' hW'inv
    have hcomap_le : Submodule.comap (e : Y →ₗ[ZMod 2] Y) W' ≤ W := by
      intro y hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp (hW' hy)
      rw [← e.injective hwe]
      exact hw
    have hcomap_inv : HInv ρY H (Submodule.comap (e : Y →ₗ[ZMod 2] Y) W') :=
      HInv.comap_of_comm hW'inv _ he
    rcases hW.2.2 _ hcomap_le hcomap_inv with hbot | htop
    · left
      have h := Submodule.map_comap_eq (e : Y →ₗ[ZMod 2] Y) W'
      rw [LinearMap.range_eq_top.mpr e.surjective, top_inf_eq, hbot,
        Submodule.map_bot] at h
      exact h.symm
    · right
      have h := Submodule.map_comap_eq (e : Y →ₗ[ZMod 2] Y) W'
      rw [LinearMap.range_eq_top.mpr e.surjective, top_inf_eq, htop] at h
      exact h.symm

private noncomputable def proj₀ (hcompl : IsCompl M₀ M₁) : Y →ₗ[ZMod 2] M₀ :=
  Submodule.projectionOnto M₀ M₁ hcompl

private lemma proj₀_apply_left (hcompl : IsCompl M₀ M₁) (x : M₀) :
    proj₀ hcompl (x : Y) = x :=
  Submodule.projectionOnto_apply_left hcompl x

private lemma proj₀_apply_right (hcompl : IsCompl M₀ M₁) (x : M₁) :
    proj₀ hcompl (x : Y) = 0 :=
  Submodule.projectionOnto_apply_right hcompl x

private lemma proj₀_eq_zero_iff (hcompl : IsCompl M₀ M₁) {y : Y} :
    proj₀ hcompl y = 0 ↔ y ∈ M₁ :=
  Submodule.projectionOnto_apply_eq_zero_iff hcompl

private lemma sub_proj₀_mem (hcompl : IsCompl M₀ M₁) (y : Y) :
    y - (proj₀ hcompl y : Y) ∈ M₁ := by
  rw [← proj₀_eq_zero_iff hcompl, map_sub, proj₀_apply_left, sub_self]

private lemma proj₀_eq_of_mem (hcompl : IsCompl M₀ M₁) {a y : Y} (ha : a ∈ M₀)
    (hy : y - a ∈ M₁) : a = (proj₀ hcompl y : Y) := by
  have h₁ : a - (proj₀ hcompl y : Y) ∈ M₀ := M₀.sub_mem ha (proj₀ hcompl y).2
  have h₂ : a - (proj₀ hcompl y : Y) ∈ M₁ := by
    have h := M₁.sub_mem (sub_proj₀_mem hcompl y) hy
    convert h using 1
    abel_nf
  have hbot : a - (proj₀ hcompl y : Y) ∈ (⊥ : Submodule (ZMod 2) Y) :=
    (disjoint_iff_inf_le.mp hcompl.disjoint) ⟨h₁, h₂⟩
  have hz : a - (proj₀ hcompl y : Y) = 0 := by simpa using hbot
  exact sub_eq_zero.mp hz

private lemma proj₀_comm {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    (hcompl : IsCompl M₀ M₁)
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀)
    (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    {h : G} (hh : h ∈ H) (y : Y) :
    proj₀ hcompl (ρY h y)
      = ⟨ρY h ((proj₀ hcompl y : M₀) : Y), hM₀ h hh _ (proj₀ hcompl y).2⟩ := by
  apply Subtype.ext
  exact (proj₀_eq_of_mem hcompl (hM₀ h hh _ (proj₀ hcompl y).2) (by
    rw [← map_sub]
    exact hM₁ h hh _ (sub_proj₀_mem hcompl y))).symm

private def thetaLin (θ : M₀ →+ M₁) : M₀ →ₗ[ZMod 2] M₁ :=
  AddMonoidHom.toZModLinearMap 2 θ

private noncomputable def tau (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) : Y →ₗ[ZMod 2] Y :=
  LinearMap.id + ((Submodule.subtype M₁).comp (thetaLin θ)).comp (proj₀ hcompl)

private lemma thetaLin_apply (θ : M₀ →+ M₁) (x : M₀) : thetaLin θ x = θ x := rfl

private lemma tau_apply (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) (y : Y) :
    tau hcompl θ y = y + ((θ (proj₀ hcompl y) : M₁) : Y) := by
  simp [tau, thetaLin]

private lemma tau_tau (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) (y : Y) :
    tau hcompl θ (tau hcompl θ y) = y := by
  have hp : proj₀ hcompl (tau hcompl θ y) = proj₀ hcompl y := by
    rw [tau_apply, map_add, proj₀_apply_right, add_zero]
  rw [tau_apply, hp, tau_apply, add_assoc, add_self_eq_zero', add_zero]

private noncomputable def taue (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) : Y ≃ₗ[ZMod 2] Y :=
  LinearEquiv.ofBijective (tau hcompl θ) ⟨fun x y h => by
    have hh := congrArg (tau hcompl θ) h
    rwa [tau_tau, tau_tau] at hh,
    fun y => ⟨tau hcompl θ y, tau_tau hcompl θ y⟩⟩

private lemma taue_apply (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) (y : Y) :
    (taue hcompl θ : Y →ₗ[ZMod 2] Y) y = tau hcompl θ y := rfl

private lemma tau_comm {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {M₀ M₁ : Submodule (ZMod 2) Y}
    (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁)
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀)
    (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    (hθH : ∀ (h : G) (hh : h ∈ H) (y : M₀),
      (θ ⟨ρY h y, hM₀ h hh y y.2⟩ : Y) = ρY h (θ y))
    {h : G} (hh : h ∈ H) (y : Y) :
    tau hcompl θ (ρY h y) = ρY h (tau hcompl θ y) := by
  rw [tau_apply, tau_apply, map_add, proj₀_comm hcompl hM₀ hM₁ hh y]
  congr 1
  exact hθH h hh (proj₀ hcompl y)

private lemma sub_irreducible {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {M : Submodule (ZMod 2) Y}
    (hirr : ∀ W : Submodule (ZMod 2) Y, W ≤ M → HInv ρY H W → W = ⊥ ∨ W = M)
    {U : Submodule (ZMod 2) M}
    (hUinv : HInv ρY H (Submodule.map (Submodule.subtype M) U)) :
    U = ⊥ ∨ U = ⊤ := by
  rcases hirr (Submodule.map M.subtype U) (Submodule.map_subtype_le M U) hUinv with h | h
  · left
    have h' := congrArg (Submodule.comap M.subtype) h
    rwa [Submodule.comap_map_eq_of_injective (Submodule.subtype_injective M) U,
      Submodule.comap_bot, Submodule.ker_subtype] at h'
  · right
    have h' := congrArg (Submodule.comap M.subtype) h
    rwa [Submodule.comap_map_eq_of_injective (Submodule.subtype_injective M) U,
      Submodule.comap_subtype_self] at h'

private lemma exists_ne_zero_apply {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    {θ : M →+ N} (hθ : θ ≠ 0) : ∃ x, θ x ≠ 0 := by
  by_contra h
  push Not at h
  exact hθ (AddMonoidHom.ext (fun x => by simpa using h x))

private lemma M₁_ne_bot {θ : M₀ →+ M₁} (hθ : θ ≠ 0) : M₁ ≠ ⊥ := by
  obtain ⟨x, hx⟩ := exists_ne_zero_apply hθ
  refine (Submodule.ne_bot_iff M₁).mpr ⟨((θ x : M₁) : Y), (θ x).2, ?_⟩
  intro h
  exact hx (Subtype.ext (by simpa using h))

private lemma HIrred.m₁ {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {M₁ : Submodule (ZMod 2) Y} (hM₁ne : M₁ ≠ ⊥) (hM₁ : HInv ρY H M₁)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → HInv ρY H W → W = ⊥ ∨ W = M₁) :
    HIrred ρY H M₁ :=
  ⟨hM₁ne, hM₁, hirr₁⟩

private def m₁Irr (ρY : Representation (ZMod 2) G Y) (H : Subgroup G)
    {M₁ : Submodule (ZMod 2) Y} (hM₁ne : M₁ ≠ ⊥) (hM₁ : HInv ρY H M₁)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → HInv ρY H W → W = ⊥ ∨ W = M₁) :
    IrrSet ρY H :=
  ⟨M₁, HIrred.m₁ hM₁ne hM₁ hirr₁⟩

private noncomputable def rhoEquiv (ρY : Representation (ZMod 2) G Y) (g : G) :
    Y ≃ₗ[ZMod 2] Y :=
  LinearEquiv.ofBijective (ρY g) (ρY.apply_bijective g)

private lemma rhoEquiv_apply (ρY : Representation (ZMod 2) G Y) (g : G) (y : Y) :
    (rhoEquiv ρY g : Y →ₗ[ZMod 2] Y) y = ρY g y := rfl

private lemma rho_mul_apply (ρY : Representation (ZMod 2) G Y) (a b : G) (w : Y) :
    ρY (a * b) w = ρY a (ρY b w) := by
  rw [map_mul]
  rfl

private lemma rhoEquiv_one (ρY : Representation (ZMod 2) G Y) :
    (rhoEquiv ρY (1 : G) : Y →ₗ[ZMod 2] Y) = LinearMap.id := by
  ext y
  rw [rhoEquiv_apply, map_one, Module.End.one_apply, LinearMap.id_apply]

private lemma rhoEquiv_comp (ρY : Representation (ZMod 2) G Y) (a b : G) :
    ((rhoEquiv ρY a : Y →ₗ[ZMod 2] Y).comp (rhoEquiv ρY b : Y →ₗ[ZMod 2] Y))
      = (rhoEquiv ρY (a * b) : Y →ₗ[ZMod 2] Y) := by
  ext y
  rw [LinearMap.comp_apply, rhoEquiv_apply, rhoEquiv_apply, rhoEquiv_apply, map_mul]
  rfl

private lemma rhoEquiv_comm_normalizer {ρY : Representation (ZMod 2) G Y}
    {a : G} {h : G} (w : Y) :
    ρY h (ρY a w) = ρY a (ρY (a⁻¹ * h * a) w) := by
  have h1 : ρY h (ρY a w) = ρY (h * a) w := (rho_mul_apply ρY h a w).symm
  have h2 : ρY a (ρY (a⁻¹ * h * a) w) = ρY (a * (a⁻¹ * h * a)) w :=
    (rho_mul_apply ρY a (a⁻¹ * h * a) w).symm
  rw [h1, h2]
  congr 1
  group

private lemma HInv.map_rho_of_normalizer {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {W : Submodule (ZMod 2) Y} (hW : HInv ρY H W) {a : G}
    (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    HInv ρY H (Submodule.map (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) W) := by
  intro h hh x hx
  obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
  have hconj : a⁻¹ * h * a ∈ H := by
    have hm := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha)) h
    simpa using hm.mp hh
  refine Submodule.mem_map.mpr ⟨ρY (a⁻¹ * h * a) w, hW _ hconj w hw, ?_⟩
  rw [rhoEquiv_apply]
  exact (rhoEquiv_comm_normalizer w).symm

private lemma HInv.comap_rho_of_normalizer {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {W : Submodule (ZMod 2) Y} (hW : HInv ρY H W) {a : G}
    (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    HInv ρY H (Submodule.comap (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) W) := by
  intro h hh y hy
  rw [Submodule.mem_comap] at hy ⊢
  rw [rhoEquiv_apply] at hy ⊢
  have hconj : a * h * a⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp ha h).mp hh
  have h1 : ρY a (ρY h y) = ρY (a * h * a⁻¹) (ρY a y) := by
    rw [show ρY a (ρY h y) = ρY (a * h) y from (rho_mul_apply ρY a h y).symm,
        show ρY (a * h * a⁻¹) (ρY a y) = ρY ((a * h * a⁻¹) * a) y from
          (rho_mul_apply ρY (a * h * a⁻¹) a y).symm]
    congr 1
    group
  rw [h1]
  exact hW _ hconj _ hy

private lemma HIrred.map_rho_of_normalizer {ρY : Representation (ZMod 2) G Y}
    {H : Subgroup G} {W : Submodule (ZMod 2) Y} (hW : HIrred ρY H W) {a : G}
    (ha : a ∈ Subgroup.normalizer (H : Set G)) :
    HIrred ρY H (Submodule.map (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) W) := by
  refine ⟨?_, HInv.map_rho_of_normalizer hW.2.1 ha, ?_⟩
  · intro h
    exact hW.1 ((Submodule.map_eq_bot_iff (e := rhoEquiv ρY a)).mp h)
  · intro W' hW' hW'inv
    have hcomap_le : Submodule.comap (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) W' ≤ W := by
      intro y hy
      rw [Submodule.mem_comap] at hy
      obtain ⟨w, hw, hwe⟩ := Submodule.mem_map.mp (hW' hy)
      rw [← (rhoEquiv ρY a).injective hwe]
      exact hw
    have hcomap_inv : HInv ρY H (Submodule.comap (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) W') :=
      HInv.comap_rho_of_normalizer hW'inv ha
    rcases hW.2.2 _ hcomap_le hcomap_inv with hbot | htop
    · left
      have h := Submodule.map_comap_eq (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) W'
      rw [LinearMap.range_eq_top.mpr (rhoEquiv ρY a).surjective, top_inf_eq, hbot,
        Submodule.map_bot] at h
      exact h.symm
    · right
      have h := Submodule.map_comap_eq (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) W'
      rw [LinearMap.range_eq_top.mpr (rhoEquiv ρY a).surjective, top_inf_eq, htop] at h
      exact h.symm

private lemma tauSet_fixed_iff {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {M₀ M₁ : Submodule (ZMod 2) Y}
    (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) (hθ : θ ≠ 0)
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀)
    (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    (hirr₀ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₀ → HInv ρY H W → W = ⊥ ∨ W = M₀)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → HInv ρY H W → W = ⊥ ∨ W = M₁)
    (W : IrrSet ρY H) :
    Submodule.map (taue hcompl θ : Y →ₗ[ZMod 2] Y) W.1 = W.1 ↔ W.1 = M₁ := by
  constructor
  · intro hmap
    by_contra hne
    have hInf : W.1 ⊓ M₁ = ⊥ := by
      have hinv : HInv ρY H (W.1 ⊓ M₁) := HInv.inf W.2.2.1 hM₁
      rcases W.2.2.2 (W.1 ⊓ M₁) inf_le_left hinv with h | h
      · exact h
      · exfalso
        have hle : W.1 ≤ M₁ := h ▸ inf_le_right
        rcases hirr₁ W.1 hle W.2.2.1 with hb | hm
        · exact W.2.1 hb
        · exact hne hm
    have hθzero : ∀ w ∈ W.1, θ (proj₀ hcompl w) = 0 := by
      intro w hw
      have hτ : tau hcompl θ w ∈ W.1 := by
        have hmem : (taue hcompl θ : Y →ₗ[ZMod 2] Y) w ∈
            Submodule.map (taue hcompl θ : Y →ₗ[ZMod 2] Y) W.1 :=
          Submodule.mem_map_of_mem hw
        rw [hmap] at hmem
        exact hmem
      have hsub : tau hcompl θ w - w = ((θ (proj₀ hcompl w) : M₁) : Y) := by
        rw [tau_apply, add_sub_cancel_left]
      have hmem2 : ((θ (proj₀ hcompl w) : M₁) : Y) ∈ W.1 ⊓ M₁ := by
        refine ⟨?_, (θ (proj₀ hcompl w)).2⟩
        rw [← hsub]
        exact W.1.sub_mem hτ hw
      rw [hInf] at hmem2
      exact Subtype.ext (by simpa using hmem2)
    have hVinv : HInv ρY H (W.1.map ((Submodule.subtype M₀).comp (proj₀ hcompl))) := by
      apply HInv.map_of_comm W.2.2.1
      intro h hh y
      exact congrArg (fun z : M₀ => (z : Y)) (proj₀_comm hcompl hM₀ hM₁ hh y)
    have hVle : W.1.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) ≤ M₀ := by
      intro x hx
      obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
      exact (proj₀ hcompl w).2
    have hVne : W.1.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) ≠ ⊥ := by
      intro hbot
      have hle : W.1 ≤ M₁ := by
        intro w hw
        have hm : ((Submodule.subtype M₀).comp (proj₀ hcompl)) w ∈
            (⊥ : Submodule (ZMod 2) Y) := by
          rw [← hbot]
          exact Submodule.mem_map_of_mem hw
        have hz : ((proj₀ hcompl w : M₀) : Y) = 0 := by
          simpa using hm
        exact (proj₀_eq_zero_iff hcompl).mp (Subtype.ext hz)
      rcases hirr₁ W.1 hle W.2.2.1 with hb | hm
      · exact W.2.1 hb
      · exact hne hm
    have hV : W.1.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) = M₀ := by
      rcases hirr₀ _ hVle hVinv with h | h
      · exact absurd h hVne
      · exact h
    apply hθ
    ext x
    have hx : (x : Y) ∈ W.1.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) := by
      rw [hV]
      exact x.2
    obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp hx
    have hxeq : x = proj₀ hcompl w := Subtype.ext (by simpa using hwx.symm)
    rw [hxeq, hθzero w hw]
    rfl
  · intro hW
    rw [hW]
    apply le_antisymm
    · intro x hx
      obtain ⟨y, hy, rfl⟩ := Submodule.mem_map.mp hx
      have he : (taue hcompl θ : Y →ₗ[ZMod 2] Y) y = y := by
        rw [taue_apply, tau_apply]
        have hz : proj₀ hcompl y = 0 := proj₀_apply_right hcompl ⟨y, hy⟩
        rw [hz, map_zero]
        simp
      rw [he]
      exact hy
    · intro x hx
      have he : (taue hcompl θ : Y →ₗ[ZMod 2] Y) x = x := by
        rw [taue_apply, tau_apply]
        have hz : proj₀ hcompl x = 0 := proj₀_apply_right hcompl ⟨x, hx⟩
        rw [hz, map_zero]
        simp
      rw [← he]
      exact Submodule.mem_map_of_mem hx

private noncomputable def oddCardAux [Finite Y] {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {M₀ M₁ : Submodule (ZMod 2) Y}
    (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) (hθ : θ ≠ 0)
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀)
    (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    (hirr₀ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₀ → HInv ρY H W → W = ⊥ ∨ W = M₀)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → HInv ρY H W → W = ⊥ ∨ W = M₁)
    (hθH : ∀ (h : G) (hh : h ∈ H) (y : M₀),
      (θ ⟨ρY h y, hM₀ h hh y y.2⟩ : Y) = ρY h (θ y)) :
    PLift (Odd (Nat.card (IrrSet ρY H))) := by
  classical
  haveI : Fintype Y := Fintype.ofFinite Y
  haveI : Finite (Submodule (ZMod 2) Y) :=
    Finite.of_injective (fun p : Submodule (ZMod 2) Y => (p : Set Y)) SetLike.coe_injective
  haveI : Finite (IrrSet ρY H) :=
    Finite.of_injective (fun W : IrrSet ρY H => W.1) Subtype.coe_injective
  haveI : Fintype (IrrSet ρY H) := Fintype.ofFinite _
  let σ : IrrSet ρY H → IrrSet ρY H := fun W =>
    ⟨W.1.map (taue hcompl θ : Y →ₗ[ZMod 2] Y),
      HIrred.map_of_comm W.2 (taue hcompl θ)
        (fun h hh y => tau_comm hcompl θ hM₀ hM₁ hθH hh y)⟩
  have hσ : Function.Involutive σ := by
    intro W
    apply Subtype.ext
    change Submodule.map (taue hcompl θ : Y →ₗ[ZMod 2] Y)
        (Submodule.map (taue hcompl θ : Y →ₗ[ZMod 2] Y) W.1) = W.1
    rw [← Submodule.map_comp]
    rw [show (taue hcompl θ : Y →ₗ[ZMod 2] Y).comp (taue hcompl θ : Y →ₗ[ZMod 2] Y)
        = LinearMap.id from by ext y; exact tau_tau hcompl θ y]
    rw [Submodule.map_id]
  let σp : Equiv.Perm (IrrSet ρY H) := hσ.toPerm σ
  have hσp_coe : (σp : IrrSet ρY H → IrrSet ρY H) = σ := Function.Involutive.coe_toPerm hσ
  have hσp2 : σp ^ 2 = 1 := by
    rw [pow_two]
    apply Equiv.ext
    intro x
    rw [Equiv.Perm.mul_apply, hσp_coe]
    exact hσ x
  let m₁ := m₁Irr ρY H (M₁_ne_bot hθ) hM₁ hirr₁
  have hfix : ∀ W : IrrSet ρY H, σ W = W ↔ W = m₁ := by
    intro W
    have hW := tauSet_fixed_iff hcompl θ hθ hM₀ hM₁ hirr₀ hirr₁ W
    constructor
    · intro h
      apply Subtype.ext
      exact hW.mp (Subtype.ext_iff.mp h)
    · intro h
      apply Subtype.ext
      exact hW.mpr (by rw [h]; rfl)
  have hcard := Equiv.Perm.card_compl_support_modEq (σ := σp) (p := 2) (n := 1) hσp2
  have hsupp : σp.supportᶜ.card = 1 := by
    have hset : σp.supportᶜ = {m₁} := by
      ext x
      rw [Finset.mem_compl, Equiv.Perm.notMem_support, Finset.mem_singleton]
      rw [hσp_coe]
      exact hfix x
    rw [hset]
    simp
  refine PLift.up ?_
  rw [Nat.card_eq_fintype_card]
  refine Nat.odd_iff.mpr ?_
  rw [hsupp] at hcard
  have h : Fintype.card (IrrSet ρY H) % 2 = 1 % 2 := hcard.symm
  omega

private lemma odd_card_irrSet [Finite Y] {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    {M₀ M₁ : Submodule (ZMod 2) Y}
    (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) (hθ : θ ≠ 0)
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀)
    (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    (hirr₀ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₀ → HInv ρY H W → W = ⊥ ∨ W = M₀)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → HInv ρY H W → W = ⊥ ∨ W = M₁)
    (hθH : ∀ (h : G) (hh : h ∈ H) (y : M₀),
      (θ ⟨ρY h y, hM₀ h hh y y.2⟩ : Y) = ρY h (θ y)) :
    Odd (Nat.card (IrrSet ρY H)) :=
  (oddCardAux hcompl θ hθ hM₀ hM₁ hirr₀ hirr₁ hθH).down

@[instance_reducible] private noncomputable def smulIrrSet {ρY : Representation (ZMod 2) G Y} {H A : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) : SMul ↥A (IrrSet ρY H) :=
  ⟨fun a W => ⟨W.1.map (rhoEquiv ρY (a : G) : Y →ₗ[ZMod 2] Y),
    HIrred.map_rho_of_normalizer W.2 (hAH a.2)⟩⟩

@[instance_reducible] private noncomputable def mulActionIrrSet {ρY : Representation (ZMod 2) G Y} {H A : Subgroup G}
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) : MulAction ↥A (IrrSet ρY H) where
  smul := (smulIrrSet hAH).smul
  one_smul W := by
    apply Subtype.ext
    change W.1.map (rhoEquiv ρY (((1 : ↥A) : G)) : Y →ₗ[ZMod 2] Y) = W.1
    rw [show ((1 : ↥A) : G) = (1 : G) from rfl, rhoEquiv_one, Submodule.map_id]
  mul_smul a b W := by
    apply Subtype.ext
    change W.1.map (rhoEquiv ρY (((a * b : ↥A) : G)) : Y →ₗ[ZMod 2] Y)
      = (W.1.map (rhoEquiv ρY (b : G) : Y →ₗ[ZMod 2] Y)).map
          (rhoEquiv ρY (a : G) : Y →ₗ[ZMod 2] Y)
    rw [← Submodule.map_comp]
    rw [show (rhoEquiv ρY (a : G) : Y →ₗ[ZMod 2] Y).comp
          (rhoEquiv ρY (b : G) : Y →ₗ[ZMod 2] Y)
        = (rhoEquiv ρY (((a * b : ↥A) : G)) : Y →ₗ[ZMod 2] Y) from by
      rw [show (((a * b : ↥A) : G)) = (a : G) * (b : G) from rfl]
      exact rhoEquiv_comp ρY (a : G) (b : G)]

private noncomputable def fixedIrrSetOfPGroup {ρY : Representation (ZMod 2) G Y}
    {H A : Subgroup G} (hA : IsPGroup 2 A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G)) (hodd : Odd (Nat.card (IrrSet ρY H))) :
    { W : IrrSet ρY H //
      ∀ a : ↥A, W.1.map (rhoEquiv ρY (a : G) : Y →ₗ[ZMod 2] Y) = W.1 } := by
  haveI : Fact (Nat.Prime 2) := inferInstance
  letI : MulAction ↥A (IrrSet ρY H) := mulActionIrrSet hAH
  have hnotdvd : ¬ 2 ∣ Nat.card (IrrSet ρY H) := Odd.not_two_dvd_nat hodd
  have hne := IsPGroup.nonempty_fixed_point_of_prime_not_dvd_card (p := 2) hA
    (IrrSet ρY H) hnotdvd
  refine ⟨Classical.choose hne, fun a => ?_⟩
  have hf : (a : ↥A) • Classical.choose hne = Classical.choose hne :=
    (MulAction.mem_fixedPoints).mp (Classical.choose_spec hne) a
  exact congrArg (fun X : IrrSet ρY H => X.1) hf

private lemma equiv_of_compl_of_irred {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    (hcompl : IsCompl M₀ M₁)
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀)
    (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    (hirr₀ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₀ → HInv ρY H W → W = ⊥ ∨ W = M₀)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → HInv ρY H W → W = ⊥ ∨ W = M₁)
    {W : Submodule (ZMod 2) Y} (hWne : W ≠ ⊥) (hWH : HInv ρY H W)
    (hWirr : ∀ W' : Submodule (ZMod 2) Y, W' ≤ W → HInv ρY H W' → W' = ⊥ ∨ W' = W)
    (hne : W ≠ M₁) :
    ∃ ψ : W ≃+ M₀, ∀ (h : G) (hh : h ∈ H) (y : W),
      (ψ ⟨ρY h y, hWH h hh y y.2⟩ : Y) = ρY h (ψ y) := by
  have hInf : W ⊓ M₁ = ⊥ := by
    have hinv : HInv ρY H (W ⊓ M₁) := HInv.inf hWH hM₁
    rcases hWirr (W ⊓ M₁) inf_le_left hinv with h | h
    · exact h
    · exfalso
      have hle : W ≤ M₁ := h ▸ inf_le_right
      rcases hirr₁ W hle hWH with hb | hm
      · exact hWne hb
      · exact hne hm
  have hVinv : HInv ρY H (W.map ((Submodule.subtype M₀).comp (proj₀ hcompl))) := by
    apply HInv.map_of_comm hWH
    intro h hh y
    exact congrArg (fun z : M₀ => (z : Y)) (proj₀_comm hcompl hM₀ hM₁ hh y)
  have hVle : W.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) ≤ M₀ := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Submodule.mem_map.mp hx
    exact (proj₀ hcompl w).2
  have hVne : W.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) ≠ ⊥ := by
    intro hbot
    have hle : W ≤ M₁ := by
      intro w hw
      have hm : ((Submodule.subtype M₀).comp (proj₀ hcompl)) w ∈
          (⊥ : Submodule (ZMod 2) Y) := by
        rw [← hbot]
        exact Submodule.mem_map_of_mem hw
      have hz : ((proj₀ hcompl w : M₀) : Y) = 0 := by simpa using hm
      exact (proj₀_eq_zero_iff hcompl).mp (Subtype.ext hz)
    rcases hirr₁ W hle hWH with hb | hm
    · exact hWne hb
    · exact hne hm
  have hV : W.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) = M₀ := by
    rcases hirr₀ _ hVle hVinv with h | h
    · exact absurd h hVne
    · exact h
  let φ : W →ₗ[ZMod 2] M₀ := (proj₀ hcompl).comp W.subtype
  have hφ_inj : Function.Injective φ := by
    intro x y hxy
    have h0 : φ (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    have hmem : ((x - y : W) : Y) ∈ M₁ := (proj₀_eq_zero_iff hcompl).mp h0
    have hinf : ((x - y : W) : Y) ∈ W ⊓ M₁ := ⟨(x - y).2, hmem⟩
    rw [hInf] at hinf
    have hzero : (x - y : W) = 0 := Subtype.ext (by simpa using hinf)
    exact sub_eq_zero.mp hzero
  have hφ_surj : Function.Surjective φ := by
    intro x
    have hx : (x : Y) ∈ W.map ((Submodule.subtype M₀).comp (proj₀ hcompl)) := by
      rw [hV]
      exact x.2
    obtain ⟨w, hw, hwx⟩ := Submodule.mem_map.mp hx
    refine ⟨⟨w, hw⟩, ?_⟩
    apply Subtype.ext
    exact hwx
  refine ⟨AddEquiv.ofBijective φ ⟨hφ_inj, hφ_surj⟩, ?_⟩
  intro h hh y
  exact congrArg (fun z : M₀ => (z : Y)) (proj₀_comm hcompl hM₀ hM₁ hh (y : Y))

private lemma equiv_of_eq_m₁ {ρY : Representation (ZMod 2) G Y} {H : Subgroup G}
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀)
    (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    (hirr₀ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₀ → HInv ρY H W → W = ⊥ ∨ W = M₀)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → HInv ρY H W → W = ⊥ ∨ W = M₁)
    (θ : M₀ →+ M₁) (hθ : θ ≠ 0)
    (hθH : ∀ (h : G) (hh : h ∈ H) (y : M₀),
      (θ ⟨ρY h y, hM₀ h hh y y.2⟩ : Y) = ρY h (θ y)) :
    ∃ ψ : M₁ ≃+ M₀, ∀ (h : G) (hh : h ∈ H) (y : M₁),
      (ψ ⟨ρY h y, hM₁ h hh y y.2⟩ : Y) = ρY h (ψ y) := by
  have hkerbot : LinearMap.ker (thetaLin θ) = ⊥ := by
    have hUinv : HInv ρY H
        (Submodule.map (Submodule.subtype M₀) (LinearMap.ker (thetaLin θ))) := by
      intro h hh x hx
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
      refine Submodule.mem_map.mpr ⟨⟨ρY h (z : Y), hM₀ h hh _ z.2⟩, ?_, rfl⟩
      have hz0 : θ z = 0 := hz
      apply Subtype.ext
      rw [thetaLin_apply, hθH h hh z, hz0]
      simp
    rcases sub_irreducible hirr₀ hUinv with h | h
    · exact h
    · exfalso
      have hθ0 : θ = 0 := by
        refine AddMonoidHom.ext (fun x => ?_)
        have hx : x ∈ LinearMap.ker (thetaLin θ) := by rw [h]; exact Submodule.mem_top
        exact hx
      exact hθ hθ0
  have hinj : Function.Injective θ := by
    have := LinearMap.ker_eq_bot.mp hkerbot
    exact this
  have hsurj : Function.Surjective θ := by
    have hRinv : HInv ρY H
        (Submodule.map (Submodule.subtype M₁) (LinearMap.range (thetaLin θ))) := by
      intro h hh x hx
      obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hx
      obtain ⟨z', hz'⟩ := hz
      have hz'' : θ z' = z := hz'
      refine Submodule.mem_map.mpr ⟨⟨ρY h (z : Y), hM₁ h hh _ z.2⟩, ?_, rfl⟩
      refine ⟨⟨ρY h (z' : Y), hM₀ h hh _ z'.2⟩, ?_⟩
      apply Subtype.ext
      rw [thetaLin_apply, hθH h hh z', hz'']
    have hR : LinearMap.range (thetaLin θ) = ⊤ := by
      rcases sub_irreducible hirr₁ hRinv with h | h
      · exfalso
        have hθ0 : θ = 0 := by
          refine AddMonoidHom.ext (fun x => ?_)
          have hx : thetaLin θ x ∈ LinearMap.range (thetaLin θ) := ⟨x, rfl⟩
          rw [h] at hx
          exact hx
        exact hθ hθ0
      · exact h
    intro y
    have hy : y ∈ LinearMap.range (thetaLin θ) := by rw [hR]; trivial
    exact hy
  let θe : M₀ ≃+ M₁ := AddEquiv.ofBijective θ ⟨hinj, hsurj⟩
  refine ⟨θe.symm, ?_⟩
  intro h hh y
  have hRHS : ρY h ((θe.symm y : M₀) : Y)
      = ((⟨ρY h ((θe.symm y : M₀) : Y), hM₀ h hh _ (θe.symm y).2⟩ : M₀) : Y) := rfl
  rw [hRHS]
  refine congrArg (fun z : M₀ => (z : Y)) ?_
  apply θe.injective
  rw [AddEquiv.apply_symm_apply]
  apply Subtype.ext
  change ρY h (y : Y) = (θ ⟨ρY h ((θe.symm y : M₀) : Y), hM₀ h hh _ (θe.symm y).2⟩ : Y)
  have hsymm : θ (θe.symm y) = y := AddEquiv.apply_symm_apply θe y
  rw [hθH h hh (θe.symm y), hsymm]

theorem exists_invariant_equiv_of_isCompl {G : Type} [Group G] [Finite G]
    {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
    (ρY : Representation (ZMod 2) G Y) (H A : Subgroup G) (hA : IsPGroup 2 A)
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    {M₀ M₁ : Submodule (ZMod 2) Y}
    (hM₀ : ∀ h ∈ H, ∀ y ∈ M₀, ρY h y ∈ M₀) (hM₁ : ∀ h ∈ H, ∀ y ∈ M₁, ρY h y ∈ M₁)
    (hirr₀ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₀ → (∀ h ∈ H, ∀ y ∈ W, ρY h y ∈ W) →
      W = ⊥ ∨ W = M₀)
    (hirr₁ : ∀ W : Submodule (ZMod 2) Y, W ≤ M₁ → (∀ h ∈ H, ∀ y ∈ W, ρY h y ∈ W) →
      W = ⊥ ∨ W = M₁)
    (hcompl : IsCompl M₀ M₁) (θ : M₀ →+ M₁) (hθ : θ ≠ 0)
    (hθH : ∀ (h : G) (hh : h ∈ H) (y : M₀), (θ ⟨ρY h y, hM₀ h hh y y.2⟩ : Y) = ρY h (θ y)) :
    ∃ (W : Submodule (ZMod 2) Y) (hWH : ∀ h ∈ H, ∀ y ∈ W, ρY h y ∈ W),
      (∀ a ∈ A, ∀ y ∈ W, ρY a y ∈ W) ∧
      ∃ ψ : W ≃+ M₀, ∀ (h : G) (hh : h ∈ H) (y : W),
        (ψ ⟨ρY h y, hWH h hh y y.2⟩ : Y) = ρY h (ψ y) := by
  classical
  have hodd : Odd (Nat.card (IrrSet ρY H)) :=
    odd_card_irrSet hcompl θ hθ hM₀ hM₁ hirr₀ hirr₁ hθH
  obtain ⟨W, hWmap⟩ := fixedIrrSetOfPGroup hA hAH hodd
  obtain ⟨W₀, hWne, hWH, hWirr⟩ := W
  have hAinv : ∀ a ∈ A, ∀ y ∈ W₀, ρY a y ∈ W₀ := by
    intro a ha y hy
    have hmap : W₀.map (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) = W₀ := hWmap ⟨a, ha⟩
    have hmem : (rhoEquiv ρY a : Y →ₗ[ZMod 2] Y) y ∈ W₀ := by
      rw [← hmap]
      exact Submodule.mem_map_of_mem hy
    simpa [rhoEquiv_apply] using hmem
  refine ⟨W₀, hWH, hAinv, ?_⟩
  rcases eq_or_ne W₀ M₁ with hWeq | hne
  · subst hWeq
    exact equiv_of_eq_m₁ hM₀ hM₁ hirr₀ hirr₁ θ hθ hθH
  · exact equiv_of_compl_of_irred hcompl hM₀ hM₁ hirr₀ hirr₁ hWne hWH hWirr hne

end CFSG.LocalAnalysis.RankThreeUC.S15
