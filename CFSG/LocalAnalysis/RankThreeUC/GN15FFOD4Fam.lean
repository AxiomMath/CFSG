module

public import CFSG.LocalAnalysis.RankThreeUC.GN15FFOD4FamDefs
public import CFSG.RankThree.PartOne.S11d.OutAbstract
public import CFSG.Quasithin.SteinbergBSClifford
import all CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4

open scoped Pointwise
open CFSG.RankThree.PartOne.OutStructure (actionOnQuot)

section Perm


private lemma perm_smul_set_eq_image {V : Type*} (σ : Equiv.Perm V) (C : Set V) :
    σ • C = σ '' C := by
  ext x
  rw [Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, by simpa only [Equiv.Perm.smul_def] using h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨y, hy, by simpa only [Equiv.Perm.smul_def] using h⟩

private lemma setStab_eq_comap_of_map {H₁ H₂ : Type*} [Group H₁] [Group H₂]
    {V₁ V₂ : Type*} (σ₁ : H₁ →* Equiv.Perm V₁) (σ₂ : H₂ →* Equiv.Perm V₂)
    (S₁ : Set V₁) (S₂ : Set V₂) (hS₁ : ∀ h, ∀ v ∈ S₁, σ₁ h v ∈ S₁)
    (ψ : H₁ →* H₂) (hψ : Function.Surjective ψ) (e : S₁ → S₂) (he : Function.Bijective e)
    (heq : ∀ (h : H₁) (v w : S₁), (w : V₁) = σ₁ h v → (e w : V₂) = σ₂ (ψ h) (e v))
    (T₁ : Subgroup H₁) (T₂ : Subgroup H₂) (hT : T₂ = T₁.map ψ) :
    setStab σ₁ (S₁ ∩ fixSet σ₁ T₁) = Subgroup.comap ψ (setStab σ₂ (S₂ ∩ fixSet σ₂ T₂)) := by
  let E : S₁ → V₂ := fun v => (e v : V₂)
  have hE : ∀ (h : H₁) (v : S₁),
      (e ⟨σ₁ h v, hS₁ h v v.2⟩ : V₂) = σ₂ (ψ h) (e v) := by
    intro h v
    exact heq h v ⟨σ₁ h v, hS₁ h v v.2⟩ rfl
  have hE' : ∀ (h : H₁) (v : S₁), E ⟨σ₁ h v, hS₁ h v v.2⟩ = σ₂ (ψ h) (E v) :=
    fun h v => hE h v
  have hEinj : Function.Injective E := by
    intro a b hab
    exact he.1 (Subtype.ext hab)
  have himgS : E '' (Set.univ : Set S₁) = S₂ := by
    ext y
    constructor
    · rintro ⟨x, -, rfl⟩
      exact (e x).2
    · intro hy
      obtain ⟨x, hx⟩ := he.2 ⟨y, hy⟩
      exact ⟨x, Set.mem_univ _, congrArg Subtype.val hx⟩
  have hS₂ : ∀ h : H₂, ∀ v ∈ S₂, σ₂ h v ∈ S₂ := by
    intro h₂ v hv
    rw [← himgS] at hv ⊢
    obtain ⟨x, -, rfl⟩ := hv
    obtain ⟨h₁, rfl⟩ := hψ h₂
    rw [← hE h₁ x]
    exact ⟨⟨σ₁ h₁ x, hS₁ h₁ x x.2⟩, Set.mem_univ _, rfl⟩
  let C : Set V₁ := S₁ ∩ fixSet σ₁ T₁
  let C₂ : Set V₂ := S₂ ∩ fixSet σ₂ T₂
  let D : Set S₁ := {v | (v : V₁) ∈ C}
  have hcoe : (fun v : S₁ => (v : V₁)) '' D = C := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · rintro ⟨hxS, hxfix⟩
      exact ⟨⟨x, hxS⟩, ⟨hxS, hxfix⟩, rfl⟩
  have hEimg : E '' D = C₂ := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      refine ⟨(e v).2, ?_⟩
      intro t₂ ht₂
      rw [hT] at ht₂
      obtain ⟨t₁, ht₁, rfl⟩ := Subgroup.mem_map.mp ht₂
      rw [← hE t₁ v]
      exact congrArg E (Subtype.ext (hv.2 t₁ ht₁))
    · rintro ⟨hyS, hyfix⟩
      obtain ⟨v, hv⟩ := he.2 ⟨y, hyS⟩
      have hv' : E v = y := congrArg Subtype.val hv
      refine ⟨v, ?_, hv'⟩
      refine ⟨?_, ?_⟩
      · exact v.2
      · intro t₁ ht₁
        have hmem : ψ t₁ ∈ T₂ := by
          rw [hT]
          exact Subgroup.mem_map.mpr ⟨t₁, ht₁, rfl⟩
        have hfix := hyfix (ψ t₁) hmem
        have h2 : σ₂ (ψ t₁) (E v) = E v := by simpa [hv'] using hfix
        have hsub : (⟨σ₁ t₁ v, hS₁ t₁ v v.2⟩ : S₁) = v := by
          apply he.1
          apply Subtype.ext
          rw [hE t₁ v, h2]
        exact congrArg Subtype.val hsub
  have hkey : ∀ h : H₁, σ₁ h '' C = C ↔ σ₂ (ψ h) '' C₂ = C₂ := by
    intro h
    constructor
    · intro hh
      apply le_antisymm
      · rintro y ⟨z, hz, rfl⟩
        rw [← hEimg] at hz
        obtain ⟨v, hv, rfl⟩ := hz
        rw [← hE h v]
        rw [← hEimg]
        refine ⟨⟨σ₁ h v, hS₁ h v v.2⟩, ?_, rfl⟩
        have hmem : σ₁ h v ∈ C := by
          rw [← hh]
          exact ⟨(v : V₁), hv, rfl⟩
        exact hmem
      · rintro y hy
        rw [← hEimg] at hy
        obtain ⟨v, hv, rfl⟩ := hy
        have hv' : (v : V₁) ∈ σ₁ h '' C := by rw [hh]; exact hv
        obtain ⟨v', hv'C, hv'eq⟩ := hv'
        have hvs : v' ∈ S₁ := hv'C.1
        refine ⟨E ⟨v', hvs⟩, ?_, ?_⟩
        · rw [← hEimg]
          exact ⟨⟨v', hvs⟩, hv'C, rfl⟩
        · rw [← hE h ⟨v', hvs⟩]
          exact congrArg E (Subtype.ext hv'eq)
    · intro hh
      apply le_antisymm
      · rintro y ⟨v, hvC, rfl⟩
        have hvs : σ₁ h v ∈ S₁ := hS₁ h v hvC.1
        have hEvC₂ : E ⟨v, hvC.1⟩ ∈ C₂ := by
          rw [← hEimg]
          exact ⟨⟨v, hvC.1⟩, hvC, rfl⟩
        have hEyC₂ : E ⟨σ₁ h v, hvs⟩ ∈ C₂ := by
          rw [hE' h ⟨v, hvC.1⟩, ← hh]
          exact ⟨E ⟨v, hvC.1⟩, hEvC₂, rfl⟩
        rw [← hEimg] at hEyC₂
        obtain ⟨w, hw, hwe⟩ := hEyC₂
        have hvw : (σ₁ h v : V₁) = (w : V₁) := congrArg Subtype.val (hEinj hwe).symm
        rw [hvw]
        exact hw
      · rintro y hy
        have hys : y ∈ S₁ := hy.1
        have hEyC₂ : E ⟨y, hys⟩ ∈ C₂ := by
          rw [← hEimg]
          exact ⟨⟨y, hys⟩, hy, rfl⟩
        rw [← hh] at hEyC₂
        obtain ⟨z, hz, hze⟩ := hEyC₂
        rw [← hEimg] at hz
        obtain ⟨v, hv, rfl⟩ := hz
        refine ⟨(v : V₁), hv, ?_⟩
        have hEeq : E ⟨σ₁ h v, hS₁ h v v.2⟩ = E ⟨y, hys⟩ := by
          rw [hE' h v]
          exact hze
        exact congrArg Subtype.val (hEinj hEeq)
  ext h
  simp only [setStab, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rw [perm_smul_set_eq_image, perm_smul_set_eq_image]
  exact hkey h

theorem sylowFamilyOn_eq_comap {H₁ H₂ : Type*} [Group H₁] [Group H₂] [Finite H₁]
    {V₁ V₂ : Type*} (σ₁ : H₁ →* Equiv.Perm V₁) (σ₂ : H₂ →* Equiv.Perm V₂) (S₁ : Set V₁)
    (S₂ : Set V₂) (hS₁ : ∀ h, ∀ v ∈ S₁, σ₁ h v ∈ S₁) (ψ : H₁ →* H₂)
    (hψ : Function.Surjective ψ) (e : S₁ → S₂) (he : Function.Bijective e)
    (heq : ∀ (h : H₁) (v w : S₁), (w : V₁) = σ₁ h v → (e w : V₂) = σ₂ (ψ h) (e v)) :
    sylowFamilyOn σ₁ S₁ = Subgroup.comap ψ '' sylowFamilyOn σ₂ S₂ := by
  have : Finite H₂ := Finite.of_surjective ψ hψ
  ext P
  constructor
  · rintro ⟨T₁, rfl⟩
    refine ⟨setStab σ₂ (S₂ ∩ fixSet σ₂ ↑(Sylow.mapSurjective hψ T₁)),
      ⟨Sylow.mapSurjective hψ T₁, rfl⟩, ?_⟩
    exact (setStab_eq_comap_of_map σ₁ σ₂ S₁ S₂ hS₁ ψ hψ e he heq (T₁ : Subgroup H₁)
      (Sylow.mapSurjective hψ T₁ : Subgroup H₂) (Sylow.coe_mapSurjective hψ T₁)).symm
  · rintro ⟨T₂, hT₂, rfl⟩
    obtain ⟨T, rfl⟩ := hT₂
    obtain ⟨T₁, hT₁⟩ := Sylow.mapSurjective_surjective hψ 2 T
    refine ⟨T₁, ?_⟩
    have hcoe : (T : Subgroup H₂) = (T₁ : Subgroup H₁).map ψ := by
      rw [← Sylow.coe_mapSurjective hψ T₁, hT₁]
    exact setStab_eq_comap_of_map σ₁ σ₂ S₁ S₂ hS₁ ψ hψ e he heq (T₁ : Subgroup H₁)
      (T : Subgroup H₂) hcoe

end Perm

private theorem actionOnQuot_apply_mk' {G : Type} [Group G] (L : Subgroup G)
    (g : Subgroup.normalizer (L : Set G)) (l : L) :
    actionOnQuot L g (QuotientGroup.mk' (Subgroup.center L) l) =
      QuotientGroup.mk' (Subgroup.center L) (L.normalizerMonoidHom g l) := by
  unfold actionOnQuot
  rw [MonoidHom.comp_apply]
  exact CFSG.ComponentClassification.PerfectAutomorphisms.onCenterQuotient_apply_mk _ _

section Module

variable {G : Type} [Group G] {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
variable (ρ : Representation (ZMod 2) G W) (L : Subgroup G)

private lemma comap_inv_toMonoidHom_eq_map {X : Type*} [Group X] (α : MulAut X)
    (Q : Subgroup X) :
    Subgroup.comap (α⁻¹).toMonoidHom Q = Q.map α.toMonoidHom := by
  ext x
  rw [Subgroup.mem_comap, Subgroup.mem_map]
  constructor
  · intro h
    exact ⟨α⁻¹ x, h, by simp⟩
  · rintro ⟨q, hq, rfl⟩
    simpa using hq

private lemma mulAut_smul_subgroup {X : Type*} [Group X] (α : MulAut X) (H : Subgroup X) :
    α • H = H.map α.toMonoidHom := by
  rw [Subgroup.pointwise_smul_def]
  rfl

private lemma setStab_eq_comap_of_map_ambient {H₁ H₂ : Type*} [Group H₁] [Group H₂]
    {V₁ V₂ : Type*} (σ₁ : H₁ →* Equiv.Perm V₁) (σ₂ : H₂ →* Equiv.Perm V₂)
    (S₁ : Set V₁) (S₂ : Set V₂) (ψ : H₁ →* H₂) (E : V₁ → V₂)
    (hE : Function.Bijective E)
    (hEeq : ∀ (h : H₁) (v : V₁), E (σ₁ h v) = σ₂ (ψ h) (E v))
    (hES : E '' S₁ = S₂)
    (T₁ : Subgroup H₁) (T₂ : Subgroup H₂) (hT : T₂ = T₁.map ψ) :
    setStab σ₁ (S₁ ∩ fixSet σ₁ T₁) = Subgroup.comap ψ (setStab σ₂ (S₂ ∩ fixSet σ₂ T₂)) := by
  have hEfix : E '' fixSet σ₁ T₁ = fixSet σ₂ T₂ := by
    ext y
    constructor
    · rintro ⟨v, hv, rfl⟩
      intro t₂ ht₂
      rw [hT] at ht₂
      obtain ⟨t₁, ht₁, rfl⟩ := Subgroup.mem_map.mp ht₂
      rw [← hEeq]
      exact congrArg E (hv t₁ ht₁)
    · intro hy
      obtain ⟨v, rfl⟩ := hE.2 y
      refine ⟨v, ?_, rfl⟩
      intro t₁ ht₁
      apply hE.1
      rw [hEeq]
      exact hy (ψ t₁) (by rw [hT]; exact Subgroup.mem_map.mpr ⟨t₁, ht₁, rfl⟩)
  have hC : E '' (S₁ ∩ fixSet σ₁ T₁) = S₂ ∩ fixSet σ₂ T₂ := by
    rw [Set.image_inter hE.1, hES, hEfix]
  have himg : ∀ h : H₁, E '' (σ₁ h '' (S₁ ∩ fixSet σ₁ T₁)) =
      σ₂ (ψ h) '' (E '' (S₁ ∩ fixSet σ₁ T₁)) := by
    intro h
    rw [← Set.image_comp, ← Set.image_comp]
    congr 1
    ext v
    exact hEeq h v
  have hkey : ∀ h : H₁, σ₁ h '' (S₁ ∩ fixSet σ₁ T₁) = S₁ ∩ fixSet σ₁ T₁ ↔
      σ₂ (ψ h) '' (S₂ ∩ fixSet σ₂ T₂) = S₂ ∩ fixSet σ₂ T₂ := by
    intro h
    constructor
    · intro hh
      rw [← hC, ← himg h, hh, hC]
    · intro hh
      rw [← hC, ← himg h] at hh
      exact (Set.image_injective.mpr hE.1) hh
  ext h
  simp only [setStab, Subgroup.mem_comap, MulAction.mem_stabilizer_iff]
  rw [perm_smul_set_eq_image, perm_smul_set_eq_image]
  exact hkey h

private lemma modFamily_map_eq_smul [Finite G] {g : G}
    (hg : g ∈ Subgroup.normalizer (L : Set G)) (S : Submodule (ZMod 2) W) :
    modFamily ρ L (S.map (ρ g)) =
      (L.normalizerMonoidHom ⟨g, hg⟩) • modFamily ρ L S := by
  have : Finite L := Subtype.finite
  let γ : MulAut L := L.normalizerMonoidHom ⟨g, hg⟩
  let ψ : L →* L := (γ⁻¹).toMonoidHom
  have hψ : Function.Surjective ψ := (γ⁻¹).surjective
  have hψ_apply : ∀ l : L, (ψ l : G) = g⁻¹ * (l : G) * g := by
    intro l
    have := Subgroup.normalizerMonoidHom_apply_symm_apply_coe L ⟨g, hg⟩ l
    simp [γ, ψ]
  let E : W → W := fun v => ρ g⁻¹ v
  have hE_id : ∀ v : W, E (ρ g v) = v := by
    intro v
    show ρ g⁻¹ (ρ g v) = v
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  have hE_id' : ∀ v : W, ρ g (E v) = v := by
    intro v
    show ρ g (ρ g⁻¹ v) = v
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hE : Function.Bijective E := by
    constructor
    · intro a b hab
      have := congrArg (fun v => ρ g v) hab
      simpa [hE_id'] using this
    · intro y
      exact ⟨ρ g y, hE_id y⟩
  have hEeq : ∀ (h : L) (v : W), E ((permRep ρ L) h v) = (permRep ρ L) (ψ h) (E v) := by
    intro h v
    show ρ g⁻¹ (ρ (h : G) v) = ρ ((ψ h : L) : G) (ρ g⁻¹ v)
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
    congr 1
    rw [hψ_apply h]
    group
  have hES : E '' (S.map (ρ g) : Set W) = (S : Set W) := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      change x ∈ Submodule.map (ρ g) S at hx
      rw [Submodule.mem_map] at hx
      obtain ⟨s, hs, rfl⟩ := hx
      rw [hE_id s]
      exact hs
    · intro hy
      refine ⟨ρ g y, ?_, hE_id y⟩
      change ρ g y ∈ Submodule.map (ρ g) S
      rw [Submodule.mem_map]
      exact ⟨y, hy, rfl⟩
  have hstab : ∀ T : Sylow 2 L,
      setStab (permRep ρ L) ((S.map (ρ g) : Set W) ∩
        fixSet (permRep ρ L) (T : Subgroup L)) =
      Subgroup.comap ψ (setStab (permRep ρ L) ((S : Set W) ∩
        fixSet (permRep ρ L) ↑(Sylow.mapSurjective hψ T))) := by
    intro T
    exact setStab_eq_comap_of_map_ambient (permRep ρ L) (permRep ρ L) _ _ ψ E hE hEeq hES
      (T : Subgroup L) ↑(Sylow.mapSurjective hψ T) (Sylow.coe_mapSurjective hψ T)
  have hcomap : ∀ Q : Subgroup L, Subgroup.comap ψ Q = Q.map γ.toMonoidHom := by
    intro Q
    simpa [ψ] using comap_inv_toMonoidHom_eq_map γ Q
  rw [modFamily]
  ext P
  constructor
  · rintro ⟨T, rfl⟩
    show setStab (permRep ρ L) ((S.map (ρ g) : Set W) ∩
      fixSet (permRep ρ L) (T : Subgroup L)) ∈
      (L.normalizerMonoidHom ⟨g, hg⟩) • modFamily ρ L S
    rw [hstab T]
    refine Set.mem_smul_set.mpr ⟨_, ⟨Sylow.mapSurjective hψ T, rfl⟩, ?_⟩
    rw [mulAut_smul_subgroup, hcomap]
  · rintro ⟨Q, ⟨T, rfl⟩, rfl⟩
    obtain ⟨T₁, hT₁⟩ := Sylow.mapSurjective_surjective hψ 2 T
    refine ⟨T₁, ?_⟩
    show setStab (permRep ρ L) ((S.map (ρ g) : Set W) ∩
      fixSet (permRep ρ L) (T₁ : Subgroup L)) =
      (L.normalizerMonoidHom ⟨g, hg⟩) •
        setStab (permRep ρ L) ((S : Set W) ∩ fixSet (permRep ρ L) (T : Subgroup L))
    rw [hstab T₁, hT₁, mulAut_smul_subgroup, hcomap]

theorem famBar_map [Finite G] {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (S : Submodule (ZMod 2) W) :
    famBar ρ L (S.map (ρ g)) = actionOnQuot L ⟨g, hg⟩ • famBar ρ L S := by
  let γ : MulAut L := L.normalizerMonoidHom ⟨g, hg⟩
  have hmod : modFamily ρ L (S.map (ρ g)) = γ • modFamily ρ L S :=
    modFamily_map_eq_smul ρ L hg S
  have hmk : (QuotientGroup.mk' (Subgroup.center L)).comp γ.toMonoidHom =
      (actionOnQuot L ⟨g, hg⟩).toMonoidHom.comp
        (QuotientGroup.mk' (Subgroup.center L)) := by
    ext l
    exact (actionOnQuot_apply_mk' L ⟨g, hg⟩ l).symm
  have hmap_eq : ∀ H : Subgroup L,
      Subgroup.map (QuotientGroup.mk' (Subgroup.center L)) (γ • H) =
      (actionOnQuot L ⟨g, hg⟩) •
        Subgroup.map (QuotientGroup.mk' (Subgroup.center L)) H := by
    intro H
    rw [mulAut_smul_subgroup, mulAut_smul_subgroup, Subgroup.map_map, Subgroup.map_map, hmk]
  rw [famBar, famBar, hmod]
  ext R
  constructor
  · rintro ⟨Q, hQ, rfl⟩
    obtain ⟨H, hH, rfl⟩ := hQ
    exact Set.mem_smul_set.mpr ⟨_, ⟨H, hH, rfl⟩, (hmap_eq H).symm⟩
  · rintro ⟨K, ⟨H, hH, rfl⟩, rfl⟩
    exact ⟨γ • H, ⟨H, hH, rfl⟩, hmap_eq H⟩

private lemma map_map_inv (g : G) (S : Submodule (ZMod 2) W) :
    (S.map (ρ g)).map (ρ g⁻¹) = S := by
  rw [← Submodule.map_comp]
  have hcomp : (ρ g⁻¹).comp (ρ g) = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
  rw [hcomp, Submodule.map_id]

private lemma map_map_inv' (g : G) (S : Submodule (ZMod 2) W) :
    (S.map (ρ g⁻¹)).map (ρ g) = S := by
  rw [← Submodule.map_comp]
  have hcomp : (ρ g).comp (ρ g⁻¹) = LinearMap.id := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  rw [hcomp, Submodule.map_id]

private lemma isInv_map {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {S : Submodule (ZMod 2) W} (hS : IsInv ρ L S) : IsInv ρ L (S.map (ρ g)) := by
  intro l hl v hv
  obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp hv
  have hglg : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) l).mp hl
    simpa using this
  refine Submodule.mem_map.mpr ⟨ρ (g⁻¹ * l * g) s, hS _ hglg s hs, ?_⟩
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]
  congr 1
  group

theorem isSimpleL_map {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    {S : Submodule (ZMod 2) W} (hS : IsSimpleL ρ L S) : IsSimpleL ρ L (S.map (ρ g)) := by
  obtain ⟨hne, hinv, hmin⟩ := hS
  refine ⟨?_, isInv_map ρ L hg hinv, ?_⟩
  · intro hbot
    have h1 := map_map_inv ρ g S
    rw [hbot, Submodule.map_bot] at h1
    exact hne h1.symm
  · intro S' hS'le hS'inv
    have hmap : S'.map (ρ g⁻¹) ≤ S := by
      calc S'.map (ρ g⁻¹) ≤ (S.map (ρ g)).map (ρ g⁻¹) := Submodule.map_mono hS'le
        _ = S := map_map_inv ρ g S
    have hinv' : IsInv ρ L (S'.map (ρ g⁻¹)) := isInv_map ρ L (Subgroup.inv_mem _ hg) hS'inv
    rcases hmin (S'.map (ρ g⁻¹)) hmap hinv' with h | h
    · left
      have := congrArg (fun T => T.map (ρ g)) h
      rwa [map_map_inv' ρ g S', Submodule.map_bot] at this
    · right
      have := congrArg (fun T => T.map (ρ g)) h
      rwa [map_map_inv' ρ g S'] at this

theorem le_famSum {S : Submodule (ZMod 2) W} (hS : IsSimpleL ρ L S) :
    S ≤ famSum ρ L (famBar ρ L S) := by
  rw [famSum]
  exact le_iSup_of_le S (le_iSup_of_le hS (le_iSup_of_le rfl le_rfl))

theorem map_famSum [Finite G] {g : G} (hg : g ∈ Subgroup.normalizer (L : Set G))
    (Ψ : Set (Subgroup (L ⧸ Subgroup.center L))) :
    (famSum ρ L Ψ).map (ρ g) = famSum ρ L (actionOnQuot L ⟨g, hg⟩ • Ψ) := by
  apply le_antisymm
  · apply (Submodule.map_le_iff_le_comap (f := ρ g) (p := famSum ρ L Ψ)
      (q := famSum ρ L (actionOnQuot L ⟨g, hg⟩ • Ψ))).mpr
    rw [famSum]
    apply iSup_le; intro S
    apply iSup_le; intro hS
    apply iSup_le; intro hf
    exact (Submodule.map_le_iff_le_comap (f := ρ g) (p := S)
      (q := famSum ρ L (actionOnQuot L ⟨g, hg⟩ • Ψ))).mp (by
      have h := le_famSum ρ L (isSimpleL_map ρ L hg hS)
      rwa [famBar_map ρ L hg S, hf] at h)
  · rw [famSum]
    apply iSup_le; intro T
    apply iSup_le; intro hT
    apply iSup_le; intro hfT
    have hg_inv : g⁻¹ ∈ Subgroup.normalizer (L : Set G) := Subgroup.inv_mem _ hg
    have hTinv : IsSimpleL ρ L (T.map (ρ g⁻¹)) := isSimpleL_map ρ L hg_inv hT
    have hfbar : famBar ρ L (T.map (ρ g⁻¹)) = Ψ := by
      rw [famBar_map ρ L hg_inv T, hfT]
      have hnorm : (⟨g⁻¹, hg_inv⟩ : Subgroup.normalizer (L : Set G)) = (⟨g, hg⟩)⁻¹ :=
        Subtype.ext rfl
      rw [hnorm, map_inv]
      exact inv_smul_smul (actionOnQuot L ⟨g, hg⟩) Ψ
    have hle : T.map (ρ g⁻¹) ≤ famSum ρ L Ψ := by
      have h := le_famSum ρ L hTinv
      rwa [hfbar] at h
    calc T = (T.map (ρ g⁻¹)).map (ρ g) := (map_map_inv' ρ g T).symm
      _ ≤ (famSum ρ L Ψ).map (ρ g) := Submodule.map_mono hle

private noncomputable def linRep : L →* (W ≃ₗ[ZMod 2] W) where
  toFun l := LinearEquiv.ofBijective (ρ (l : G)) (by
    constructor
    · intro a b hab
      have := congrArg (fun v => ρ ((l : G)⁻¹) v) hab
      simpa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply] using this
    · intro y
      exact ⟨ρ ((l : G)⁻¹) y, by
        show ρ (l : G) (ρ ((l : G)⁻¹) y) = y
        rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one,
          Module.End.one_apply]⟩)
  map_one' := by
    ext v
    show ρ ((1 : L) : G) v = v
    rw [OneMemClass.coe_one, map_one, Module.End.one_apply]
  map_mul' a b := by
    ext v
    show ρ ((a * b : L) : G) v = ρ (a : G) (ρ (b : G) v)
    rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply]

private lemma linRep_apply (l : L) (v : W) : linRep ρ L l v = ρ (l : G) v := rfl

private lemma isSimpleL_iff_isIrr (S : Submodule (ZMod 2) W) :
    IsSimpleL ρ L S ↔ CFSG.Quasithin.SteinbergBS.Clifford.IsIrr (linRep ρ L) ⊤ S := by
  unfold IsSimpleL CFSG.Quasithin.SteinbergBS.Clifford.IsIrr
  constructor
  · rintro ⟨hne, hinv, hmin⟩
    refine ⟨?_, hne, ?_⟩
    · simpa [IsInv, CFSG.Quasithin.SteinbergBS.Clifford.IsInv, linRep_apply] using hinv
    · intro U' hle hinv'
      exact hmin U' hle (by
        simpa [IsInv, CFSG.Quasithin.SteinbergBS.Clifford.IsInv, linRep_apply] using hinv')
  · rintro ⟨hinv, hne, hmin⟩
    refine ⟨hne, ?_, ?_⟩
    · simpa [IsInv, CFSG.Quasithin.SteinbergBS.Clifford.IsInv, linRep_apply] using hinv
    · intro U' hle hinv'
      exact hmin U' hle (by
        simpa [IsInv, CFSG.Quasithin.SteinbergBS.Clifford.IsInv, linRep_apply] using hinv')


private lemma famBar_eq_of_NIso [Finite L] {B C : Submodule (ZMod 2) W}
    (hB : IsSimpleL ρ L B) (_hC : IsSimpleL ρ L C)
    (h : CFSG.Quasithin.SteinbergBS.Clifford.NIso (linRep ρ L) ⊤ B C) :
    famBar ρ L B = famBar ρ L C := by
  obtain ⟨f, hf, hinj, hrange⟩ := h
  let e : B → C := fun x => ⟨f x, by
    rw [← hrange]
    exact LinearMap.mem_range.mpr ⟨x, rfl⟩⟩
  have he : Function.Bijective e := by
    constructor
    · intro x y hxy
      exact hinj (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx⟩ := LinearMap.mem_range.mp (by rw [hrange]; exact y.2)
      exact ⟨x, Subtype.ext hx⟩
  have heq : ∀ (l : L) (v w : B), (w : W) = (permRep ρ L) l v →
      (e w : W) = (permRep ρ L) l (e v) := by
    intro l v w hw
    have h' := hf l (Subgroup.mem_top l) v w (by simpa [linRep_apply, permRep] using hw)
    simpa [e, linRep_apply, permRep] using h'
  have hBinv : IsInv ρ L B := hB.2.1
  have hmain := sylowFamilyOn_eq_comap (permRep ρ L) (permRep ρ L) (B : Set W) (C : Set W)
    (fun h v hv => hBinv h h.2 v hv) (MonoidHom.id L) (fun x => ⟨x, rfl⟩) e he heq
  rw [famBar, famBar, modFamily, modFamily, hmain]
  simp


private lemma isInv_inf {U V : Submodule (ZMod 2) W} (hU : IsInv ρ L U) (hV : IsInv ρ L V) :
    IsInv ρ L (U ⊓ V) := fun l hl u hu => ⟨hU l hl u hu.1, hV l hl u hu.2⟩

private lemma famSum_eq_sSup (Ψ : Set (Subgroup (L ⧸ Subgroup.center L))) :
    famSum ρ L Ψ = sSup {S : Submodule (ZMod 2) W | IsSimpleL ρ L S ∧ famBar ρ L S = Ψ} := by
  rw [famSum, sSup_eq_iSup]
  simp only [Set.mem_setOf_eq, iSup_and]

private lemma isInv_famSum (Ψ : Set (Subgroup (L ⧸ Subgroup.center L))) :
    IsInv ρ L (famSum ρ L Ψ) := by
  rw [famSum_eq_sSup]
  have h : CFSG.Quasithin.SteinbergBS.Clifford.IsInv (linRep ρ L) ⊤
      (sSup {S : Submodule (ZMod 2) W | IsSimpleL ρ L S ∧ famBar ρ L S = Ψ}) := by
    apply CFSG.Quasithin.SteinbergBS.Clifford.isInv_sSup
    intro U hU
    have hU' : IsInv ρ L U := hU.1.2.1
    simpa [IsInv, CFSG.Quasithin.SteinbergBS.Clifford.IsInv, linRep_apply] using hU'
  simpa [IsInv, CFSG.Quasithin.SteinbergBS.Clifford.IsInv, linRep_apply] using h

private lemma exists_isSimpleL_le_of_ne_bot [Finite W] {N : Submodule (ZMod 2) W}
    (hNinv : IsInv ρ L N) (hN : N ≠ ⊥) :
    ∃ B : Submodule (ZMod 2) W, B ≤ N ∧ IsSimpleL ρ L B := by
  classical
  let s : Set (Submodule (ZMod 2) W) := {M | M ≤ N ∧ M ≠ ⊥ ∧ IsInv ρ L M}
  have hs : s.Finite := Set.toFinite s
  have hne : s.Nonempty := ⟨N, le_rfl, hN, hNinv⟩
  obtain ⟨B, hBmin⟩ := hs.exists_minimal hne
  obtain ⟨hBle, hBne, hBinv⟩ := hBmin.1
  refine ⟨B, hBle, hBne, hBinv, ?_⟩
  intro B' hB'le hB'inv
  by_cases hB'bot : B' = ⊥
  · exact Or.inl hB'bot
  · right
    have hB'mem : B' ∈ s := ⟨hB'le.trans hBle, hB'bot, hB'inv⟩
    exact le_antisymm hB'le ((hBmin.2 hB'mem) hB'le)

theorem famSum_disjoint [Finite G] [Finite W] {Ψ Ψ' : Set (Subgroup (L ⧸ Subgroup.center L))}
    (h : Ψ ≠ Ψ') : Disjoint (famSum ρ L Ψ) (famSum ρ L Ψ') := by
  have : Finite L := Subtype.finite
  rw [disjoint_iff]
  by_contra hne
  have hNinv : IsInv ρ L (famSum ρ L Ψ ⊓ famSum ρ L Ψ') :=
    isInv_inf ρ L (isInv_famSum ρ L Ψ) (isInv_famSum ρ L Ψ')
  obtain ⟨B, hBle, hBsimp⟩ := exists_isSimpleL_le_of_ne_bot ρ L hNinv hne
  have hBΨ : B ≤ famSum ρ L Ψ := hBle.trans inf_le_left
  have hBΨ' : B ≤ famSum ρ L Ψ' := hBle.trans inf_le_right
  have hBirr := (isSimpleL_iff_isIrr ρ L B).mp hBsimp
  let sΨ : Set (Submodule (ZMod 2) W) := {S | IsSimpleL ρ L S ∧ famBar ρ L S = Ψ}
  let sΨ' : Set (Submodule (ZMod 2) W) := {S | IsSimpleL ρ L S ∧ famBar ρ L S = Ψ'}
  have hsΨ : sΨ.Finite := Set.toFinite sΨ
  have hsΨ' : sΨ'.Finite := Set.toFinite sΨ'
  have hsiΨ : ∀ C ∈ sΨ, CFSG.Quasithin.SteinbergBS.Clifford.IsIrr (linRep ρ L) ⊤ C :=
    fun C hC => (isSimpleL_iff_isIrr ρ L C).mp hC.1
  have hsiΨ' : ∀ C ∈ sΨ', CFSG.Quasithin.SteinbergBS.Clifford.IsIrr (linRep ρ L) ⊤ C :=
    fun C hC => (isSimpleL_iff_isIrr ρ L C).mp hC.1
  have hleΨ : B ≤ sSup sΨ := by rw [← famSum_eq_sSup]; exact hBΨ
  have hleΨ' : B ≤ sSup sΨ' := by rw [← famSum_eq_sSup]; exact hBΨ'
  obtain ⟨C, hC, hBC⟩ :=
    CFSG.Quasithin.SteinbergBS.Clifford.exists_niso_of_le_sSup hBirr sΨ hsΨ hsiΨ hleΨ
  obtain ⟨D, hD, hBD⟩ :=
    CFSG.Quasithin.SteinbergBS.Clifford.exists_niso_of_le_sSup hBirr sΨ' hsΨ' hsiΨ' hleΨ'
  have hfamB : famBar ρ L B = famBar ρ L C := famBar_eq_of_NIso ρ L hBsimp hC.1 hBC
  have hfamB' : famBar ρ L B = famBar ρ L D := famBar_eq_of_NIso ρ L hBsimp hD.1 hBD
  have hΨ : famBar ρ L B = Ψ := hfamB.trans hC.2
  have hΨ' : famBar ρ L B = Ψ' := hfamB'.trans hD.2
  exact h (hΨ.symm.trans hΨ')

end Module

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15.FFO.D4
