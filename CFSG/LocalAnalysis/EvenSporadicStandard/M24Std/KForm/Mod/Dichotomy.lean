module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.KForm.Mod.RestBot
public import CFSG.LocalAnalysis.EvenSporadicStandard.SolomonRed.Dichotomy
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.InvCent.Util.Perfect

public section

namespace CFSG.EvenSporadicStandard.M24Std.KForm.Mod

open Subgroup CFSG CFSG.EvenSporadicStandard.SolomonRed CFSG.EvenSporadicStandard.HSStd.InvCent

variable {G : Type*} [Group G] {B : Type*} [Group B] {t : G} {B₀ : Subgroup B}
  {ψ : ↥(centralizer ({t} : Set G)) →* Multiplicative (ZMod 2) × B}

structure ModSwapData (G : Type*) [Group G] (t : G) {B : Type*} [Group B] (B₀ : Subgroup B)
    (S₁ S₂ : Subgroup G) : Prop where
  comp : IsComponent S₁
  conj_eq : S₂ = S₁.map (MulAut.conj t).toMonoidHom
  ne : S₁ ≠ S₂
  layer_eq : layer G = S₁ ⊔ S₂
  commute : ∀ a ∈ S₁, ∀ b ∈ S₂, a * b = b * a
  disjoint : S₁ ⊓ S₂ = ⊥
  iso : Nonempty (↥S₁ ≃* ↥B₀)

theorem ModData.le_imgOf_of_fixedData [Finite G] (h : ModData t B₀ ψ) {S : Subgroup G}
    (hS : FixedData G S) : B₀ ≤ imgOf ψ (S ⊓ centralizer ({t} : Set G)) := by
  have hX : ⁅S, S⁆ = S :=
    Subgroup.isPerfect_iff.1 (isPerfect_of_simple_of_nonab hS.simple hS.nonab)
  have hX1 : S ≠ ⊥ := by
    intro hbot
    obtain ⟨a, ha, b, hb, hab⟩ := hS.nonab
    rw [hbot, Subgroup.mem_bot] at ha hb
    exact hab (by rw [ha, hb])
  exact h.le_imgOf_of_perfect hX hX1 fun c _ x hx => hS.normal.conj_mem x hx c

theorem iso_of_swap_mod [Finite G] (h : ModData t B₀ ψ) (hF : CFSG.fittingSubgroup G = ⊥)
    {L₁ L₂ : Subgroup G} (hL₁ : IsComponent L₁)
    (hL₂ : L₂ = L₁.map (MulAut.conj t).toMonoidHom) (hne : L₁ ≠ L₂)
    (hlayer : layer G = L₁ ⊔ L₂) : Nonempty (↥L₁ ≃* ↥B₀) := by
  subst hL₂
  haveI hsimple : IsSimpleGroup ↥L₁ := component_isSimple hF hL₁
  have hL₂c : IsComponent (L₁.map (MulAut.conj t).toMonoidHom) := isComponent_conj hL₁ t
  have hcom : ∀ a ∈ L₁, ∀ b ∈ L₁.map (MulAut.conj t).toMonoidHom, a * b = b * a :=
    component_commute hL₁ hL₂c hne
  have hdisj : L₁ ⊓ L₁.map (MulAut.conj t).toMonoidHom = ⊥ :=
    component_inf_eq_bot hF hL₁ hL₂c hne
  have hrange : (diagHom t hcom rfl).range =
      (L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set G) :=
    diagHom_range h.t_sq hdisj hcom rfl
  have hmem : ∀ s : ↥L₁, diagHom t hcom rfl s ∈ centralizer ({t} : Set G) := fun s => by
    rw [mem_centralizer_singleton_iff, diagHom_apply]
    exact (swap_fixed h.t_sq hcom rfl s.2).symm
  let θ : ↥L₁ →* B :=
    (phi ψ).comp ((diagHom t hcom rfl).codRestrict (centralizer ({t} : Set G)) hmem)
  have hθapply : ∀ s : ↥L₁, θ s = phi ψ ⟨diagHom t hcom rfl s, hmem s⟩ := fun _ => rfl
  have hθrange : θ.range =
      imgOf ψ ((L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set G)) := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      rw [hθapply, mem_imgOf]
      exact ⟨diagHom t hcom rfl s,
        by rw [← hrange]; exact MonoidHom.mem_range.2 ⟨s, rfl⟩, hmem s, rfl⟩
    · intro hb
      rw [mem_imgOf] at hb
      obtain ⟨y, hyD, hyC, hyb⟩ := hb
      have hyrange : y ∈ (diagHom t hcom rfl).range := by rw [hrange]; exact hyD
      rw [MonoidHom.mem_range] at hyrange ⊢
      obtain ⟨s, hs⟩ := hyrange
      exact ⟨s, by rw [hθapply, ← hyb]; exact congrArg (phi ψ) (Subtype.ext hs)⟩
  have hDne : imgOf ψ ((L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓
      centralizer ({t} : Set G)) ≠ ⊥ := h.imgOf_pair_ne_bot hL₁
  have hθker : θ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal θ.ker with hker | hker
    · exact hker
    · exfalso
      apply hDne
      rw [← hθrange, eq_bot_iff]
      rintro b ⟨s, rfl⟩
      have hs : s ∈ θ.ker := by rw [hker]; trivial
      rw [MonoidHom.mem_ker] at hs
      rw [hs]
      exact Subgroup.one_mem ⊥
  have hθinj : Function.Injective θ := θ.ker_eq_bot_iff.1 hθker
  have hY : ∀ c ∈ centralizer ({t} : Set G),
      ∀ y ∈ (L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓ centralizer ({t} : Set G),
      c * y * c⁻¹ ∈ (L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer ({t} : Set G) := by
    intro c hc y hy
    refine ⟨?_, ?_⟩
    · have hyE : y ∈ layer G := by rw [hlayer]; exact hy.1
      haveI hEc : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic
      have hcyE : c * y * c⁻¹ ∈ layer G :=
        (inferInstance : (layer G).Normal).conj_mem y hyE c
      rwa [hlayer] at hcyE
    · exact (centralizer ({t} : Set G)).mul_mem
        ((centralizer ({t} : Set G)).mul_mem hc hy.2)
        ((centralizer ({t} : Set G)).inv_mem hc)
  have hB₀le : B₀ ≤ imgOf ψ ((L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓
      centralizer ({t} : Set G)) := by
    rcases h.imgOf_eq_bot_or_le (Y := (L₁ ⊔ L₁.map (MulAut.conj t).toMonoidHom) ⊓
        centralizer ({t} : Set G)) hY with hbot | hle
    · exact absurd hbot hDne
    · exact hle
  have hcomap : B₀.comap θ = ⊤ := by
    haveI : (B₀.comap θ).Normal := h.hR.normal.comap θ
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (B₀.comap θ) with hbot | htop
    · exfalso
      obtain ⟨b, hb, hb1⟩ : ∃ b ∈ B₀, b ≠ 1 := by
        obtain ⟨a, ha, c', hc', hac⟩ := h.hR.nonab
        by_cases ha1 : a = 1
        · exact ⟨c', hc', fun hc1 => hac (by rw [ha1, hc1])⟩
        · exact ⟨a, ha, ha1⟩
      have hbimg : b ∈ θ.range := by rw [hθrange]; exact hB₀le hb
      obtain ⟨s, hs⟩ := MonoidHom.mem_range.1 hbimg
      have hscomap : s ∈ B₀.comap θ := by
        rw [Subgroup.mem_comap]; rw [hs]; exact hb
      rw [hbot, Subgroup.mem_bot] at hscomap
      rw [hscomap, map_one] at hs
      exact hb1 hs.symm
    · exact htop
  have hrangeB₀ : θ.range = B₀ := by
    refine le_antisymm ?_ ?_
    · intro b hb
      rw [MonoidHom.mem_range] at hb
      obtain ⟨s, rfl⟩ := hb
      have : s ∈ B₀.comap θ := by rw [hcomap]; exact Subgroup.mem_top s
      rwa [Subgroup.mem_comap] at this
    · rw [hθrange]; exact hB₀le
  exact ⟨(MonoidHom.ofInjective hθinj).trans (MulEquiv.subgroupCongr hrangeB₀)⟩

theorem dichotomy_mod [Finite G] (h : ModData t B₀ ψ) (hF : CFSG.fittingSubgroup G = ⊥) :
    (∃ S : Subgroup G, FixedData G S ∧ B₀ ≤ imgOf ψ (S ⊓ centralizer ({t} : Set G))) ∨
      ∃ S₁ S₂ : Subgroup G, ModSwapData G t B₀ S₁ S₂ := by
  obtain ⟨L₁, hL₁⟩ := exists_component hF ⟨t, h.t_ne⟩
  obtain ⟨L₂, hL₂def⟩ : ∃ L₂ : Subgroup G, L₂ = L₁.map (MulAut.conj t).toMonoidHom :=
    ⟨_, rfl⟩
  have hL₂ : IsComponent L₂ := by rw [hL₂def]; exact isComponent_conj hL₁ t
  have hR : Rest G L₁ L₂ = ⊥ := by rw [hL₂def]; exact rest_eq_bot_mod h hF hL₁
  have hE : layer G = L₁ ⊔ L₂ := by rw [layer_eq_sup_rest hL₁ hL₂, hR, sup_bot_eq]
  by_cases hsw : L₂ = L₁
  · left
    have hlay : layer G = L₁ := by rw [hE, hsw, sup_idem]
    haveI hEc : (layer G).Characteristic := CFSG.LocalCores.layer_characteristic
    have hFix : FixedData G L₁ :=
      ⟨by rw [← hlay]; exact (inferInstance : (layer G).Normal), component_isSimple hF hL₁,
        component_nonab hF hL₁, by rw [← hlay]; exact centralizer_layer_eq_bot hF⟩
    exact ⟨L₁, hFix, h.le_imgOf_of_fixedData hFix⟩
  · right
    have hne : L₁ ≠ L₂ := fun h1 => hsw h1.symm
    exact ⟨L₁, L₂, ⟨hL₁, hL₂def, hne, hE, component_commute hL₁ hL₂ hne,
      component_inf_eq_bot hF hL₁ hL₂ hne, iso_of_swap_mod h hF hL₁ hL₂def hne hE⟩⟩

end CFSG.EvenSporadicStandard.M24Std.KForm.Mod
