module

public import CFSG.LocalAnalysis.EvenSmallLie.TwoE6.CoverPullback

public section

namespace CFSG.EvenSmallLie.TwoE6

open Subgroup CFSG.LieType.Steinberg.Exceptional
open scoped commutatorElement

theorem exists_mulEquiv_of_graph
    {U : Type*} [Group U] [Group.IsPerfect U] {K₁ K₂ : Subgroup U}
    (hCT : ∀ (G : Type) [Group G] [Group.IsPerfect G] (ι : G →* U), Function.Surjective ι →
      ι.ker ≤ center G → (∀ x ∈ ⁅K₁.comap ι, K₁.comap ι⁆, ι x = 1 → x = 1) →
      (∀ x ∈ ⁅K₂.comap ι, K₂.comap ι⁆, ι x = 1 → x = 1) → ι.ker = ⊥)
    {E₁ E₂ : Type} [Group E₁] [Group E₂] [Group.IsPerfect E₁] [Group.IsPerfect E₂]
    {η₁ : E₁ →* U} {η₂ : E₂ →* U} (hη₁ : Function.Surjective η₁)
    (hη₂ : Function.Surjective η₂) (hC₁ : η₁.ker ≤ center E₁) (hC₂ : η₂.ker ≤ center E₂)
    (hS₁ : ⁅K₁.comap η₁, K₁.comap η₁⁆ ⊓ η₁.ker = ⊥) (hS₂ : ⁅K₁.comap η₂, K₁.comap η₂⁆ ⊓ η₂.ker = ⊥)
    (φ : K₂.comap η₁ ≃* K₂.comap η₂) (hφ : ∀ x, η₂ (φ x) = η₁ x) :
    ∃ ψ : E₁ ≃* E₂, ∀ x, η₂ (ψ x) = η₁ x := by
  obtain ⟨F, hFdef⟩ : ∃ F : Subgroup (E₁ × E₂),
      F = MonoidHom.eqLocus (η₁.comp (MonoidHom.fst E₁ E₂)) (η₂.comp (MonoidHom.snd E₁ E₂)) :=
    ⟨_, rfl⟩
  have hF : ∀ {x : E₁ × E₂}, x ∈ F ↔ η₁ x.1 = η₂ x.2 := fun {x} => by
    rw [hFdef]
    exact Iff.rfl
  obtain ⟨Δ, hΔdef⟩ : ∃ Δ : Subgroup (E₁ × E₂), Δ = ⁅F, F⁆ := ⟨_, rfl⟩
  have hΔF : Δ ≤ F := hΔdef ▸ commutator_self_le F
  have hF1 : F.map (MonoidHom.fst E₁ E₂) = ⊤ := eq_top_iff.2 fun x _ => by
    obtain ⟨y, hy⟩ := hη₂ (η₁ x)
    exact ⟨(x, y), hF.2 hy.symm, rfl⟩
  have hF2 : F.map (MonoidHom.snd E₁ E₂) = ⊤ := eq_top_iff.2 fun y _ => by
    obtain ⟨x, hx⟩ := hη₁ (η₂ y)
    exact ⟨(x, y), hF.2 hx, rfl⟩
  have hΔ1 : Δ.map (MonoidHom.fst E₁ E₂) = ⊤ := by
    rw [hΔdef, map_commutator, hF1, commutator_top_eq_top]
  have hΔ2 : Δ.map (MonoidHom.snd E₁ E₂) = ⊤ := by
    rw [hΔdef, map_commutator, hF2, commutator_top_eq_top]
  obtain ⟨C, hCdef⟩ : ∃ C : Subgroup (E₁ × E₂), C = η₁.ker.prod η₂.ker := ⟨_, rfl⟩
  have hC : ∀ {x : E₁ × E₂}, x ∈ C ↔ η₁ x.1 = 1 ∧ η₂ x.2 = 1 := fun {x} => by
    rw [hCdef, mem_prod, MonoidHom.mem_ker, MonoidHom.mem_ker]
  have hCZ : C ≤ center (E₁ × E₂) := by
    rw [hCdef, Subgroup.center_prod]
    exact prod_mono hC₁ hC₂
  have hFC : F ≤ Δ ⊔ C := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ : x.1 ∈ Δ.map (MonoidHom.fst E₁ E₂) := hΔ1 ▸ mem_top _
    change y.1 = x.1 at hyx
    have hyF : y ∈ F := hΔF hy
    have hc : y⁻¹ * x ∈ C := by
      refine hC.2 ⟨?_, ?_⟩
      · rw [Prod.fst_mul, Prod.fst_inv, hyx, inv_mul_cancel, map_one]
      · rw [Prod.snd_mul, Prod.snd_inv, map_mul, map_inv, ← hF.1 hyF, ← hF.1 hx, hyx,
          inv_mul_cancel]
    rw [show x = y * (y⁻¹ * x) by group]
    exact mul_mem_sup hy hc
  have hΔΔ : ⁅Δ, Δ⁆ = Δ := le_antisymm (commutator_self_le _) (by
    conv_lhs => rw [hΔdef]
    exact (commutator_mono hFC hFC).trans (commutator_sup_le_of_le_center hCZ))
  have : Group.IsPerfect Δ := Subgroup.isPerfect_iff.2 hΔΔ
  obtain ⟨p₁, hp₁def⟩ : ∃ p₁ : Δ →* E₁, p₁ = (MonoidHom.fst E₁ E₂).comp Δ.subtype := ⟨_, rfl⟩
  obtain ⟨p₂, hp₂def⟩ : ∃ p₂ : Δ →* E₂, p₂ = (MonoidHom.snd E₁ E₂).comp Δ.subtype := ⟨_, rfl⟩
  have hp₁x : ∀ x : Δ, p₁ x = (x : E₁ × E₂).1 := fun x => by rw [hp₁def]; rfl
  have hp₂x : ∀ x : Δ, p₂ x = (x : E₁ × E₂).2 := fun x => by rw [hp₂def]; rfl
  obtain ⟨ηΔ, hηΔdef⟩ : ∃ ηΔ : Δ →* U, ηΔ = η₁.comp p₁ := ⟨_, rfl⟩
  have hηp₁ : ∀ x : Δ, ηΔ x = η₁ (p₁ x) := fun x => by rw [hηΔdef]; rfl
  have hηp₂ : ∀ x : Δ, ηΔ x = η₂ (p₂ x) := fun x => by
    rw [hηp₁, hp₁x, hp₂x]
    exact hF.1 (hΔF x.2)
  have hηΔ : Function.Surjective ηΔ := by
    intro u
    obtain ⟨x, hx1⟩ := hη₁ u
    obtain ⟨y, hy, hyx⟩ : x ∈ Δ.map (MonoidHom.fst E₁ E₂) := hΔ1 ▸ mem_top _
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hηp₁, hp₁x]
    change η₁ y.1 = u
    rw [show y.1 = x from hyx, hx1]
  have hηΔC : ∀ x : Δ, ηΔ x = 1 → (x : E₁ × E₂) ∈ C := fun x hx => hC.2
    ⟨by rw [← hp₁x, ← hηp₁]; exact hx, by rw [← hp₂x, ← hηp₂]; exact hx⟩
  obtain ⟨gr, hgrdef⟩ : ∃ gr : K₂.comap η₁ →* E₁ × E₂,
      gr = (K₂.comap η₁).subtype.prod ((K₂.comap η₂).subtype.comp φ.toMonoidHom) := ⟨_, rfl⟩
  have hgr : ∀ m, gr m = ((m : E₁), ((φ m : K₂.comap η₂) : E₂)) := fun m => by rw [hgrdef]; rfl
  obtain ⟨D, hDdef⟩ : ∃ D : Subgroup (E₁ × E₂), D = ((η₁.ker).subgroupOf (K₂.comap η₁)).map gr :=
    ⟨_, rfl⟩
  have hD : ∀ {x : E₁ × E₂}, x ∈ D ↔ ∃ m : K₂.comap η₁, η₁ (m : E₁) = 1 ∧ gr m = x :=
      fun {x} => by
    rw [hDdef]
    exact ⟨fun ⟨m, hm, h⟩ => ⟨m, hm, h⟩, fun ⟨m, hm, h⟩ => ⟨m, hm, h⟩⟩
  have hDC : D ≤ C := by
    intro x hx
    obtain ⟨m, hm1, rfl⟩ := hD.1 hx
    rw [hgr]
    exact hC.2 ⟨hm1, by rw [hφ, hm1]⟩
  obtain ⟨D', hD'def⟩ : ∃ D' : Subgroup Δ, D' = D.subgroupOf Δ := ⟨_, rfl⟩
  have hD' : ∀ {x : Δ}, x ∈ D' ↔ (x : E₁ × E₂) ∈ D := fun {x} => by rw [hD'def]; exact Iff.rfl
  have hD'Z : D' ≤ center Δ := fun x hx => by
    rw [mem_center_iff]
    intro y
    exact Subtype.ext (mem_center_iff.1 (hCZ (hDC (hD'.1 hx))) y)
  have : D'.Normal := normal_of_le_center hD'Z
  have hD'ker : D' ≤ ηΔ.ker := fun x hx => by
    rw [MonoidHom.mem_ker, hηp₁, hp₁x]
    exact (hC.1 (hDC (hD'.1 hx))).1
  obtain ⟨ι, hιdef⟩ : ∃ ι : Δ ⧸ D' →* U, ι = QuotientGroup.lift D' ηΔ hD'ker := ⟨_, rfl⟩
  have hιmk : ∀ x : Δ, ι (x : Δ ⧸ D') = ηΔ x := fun x => by
    rw [hιdef]
    exact QuotientGroup.lift_mk _ _ _
  have hπsurj : Function.Surjective (QuotientGroup.mk' D') := QuotientGroup.mk'_surjective D'
  have hι : Function.Surjective ι := fun u => by
    obtain ⟨x, rfl⟩ := hηΔ u
    exact ⟨x, hιmk x⟩
  have hιC : ι.ker ≤ center (Δ ⧸ D') := by
    intro y hy
    obtain ⟨x, rfl⟩ := hπsurj y
    have hx : ηΔ x = 1 := by rw [← hιmk]; exact hy
    have hxZ : x ∈ center Δ := by
      rw [mem_center_iff]
      intro w
      exact Subtype.ext (mem_center_iff.1 (hCZ (hηΔC x hx)) w)
    refine mem_center_iff.2 fun g => ?_
    obtain ⟨g', rfl⟩ := hπsurj g
    rw [← map_mul, ← map_mul, mem_center_iff.1 hxZ g']
  have hcomap : ∀ Y : Subgroup U, Y.comap ι = (Y.comap ηΔ).map (QuotientGroup.mk' D') := by
    intro Y
    ext y
    constructor
    · intro hy
      obtain ⟨x, rfl⟩ := hπsurj y
      exact ⟨x, show ηΔ x ∈ Y by rw [← hιmk]; exact hy, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      rw [mem_comap, QuotientGroup.mk'_apply, hιmk]
      exact hx
  have hL : ∀ x ∈ ⁅K₁.comap ι, K₁.comap ι⁆, ι x = 1 → x = 1 := by
    intro x hx hx1
    rw [hcomap, ← map_commutator] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : ηΔ y = 1 := by rw [← hιmk]; exact hx1
    have hproj : ∀ {E : Type} [Group E] {η : E →* U} (p : Δ →* E),
        ⁅K₁.comap η, K₁.comap η⁆ ⊓ η.ker = ⊥ → (∀ x, ηΔ x = η (p x)) → p y = 1 := by
      intro E _ η p hS hηp
      have hle : (K₁.comap ηΔ).map p ≤ K₁.comap η := by
        rintro _ ⟨z, hz, rfl⟩
        rw [mem_comap, ← hηp]
        exact hz
      have hmem : p y ∈ ⁅K₁.comap η, K₁.comap η⁆ ⊓ η.ker := by
        refine mem_inf.2 ⟨?_, MonoidHom.mem_ker.2 (by rw [← hηp]; exact hy1)⟩
        have h := mem_map_of_mem p hy
        rw [map_commutator] at h
        exact commutator_mono hle hle h
      rw [hS] at hmem
      exact hmem
    have h₁ := hproj p₁ hS₁ hηp₁
    have h₂ := hproj p₂ hS₂ hηp₂
    rw [hp₁x] at h₁
    rw [hp₂x] at h₂
    have : y = 1 := Subtype.ext (Prod.ext h₁ h₂)
    rw [this, map_one]
  obtain ⟨R, hRdef⟩ : ∃ R : Subgroup (E₁ × E₂), R = F ⊓ (K₂.comap η₁).prod (K₂.comap η₂) :=
    ⟨_, rfl⟩
  have hR : ∀ {x : E₁ × E₂}, x ∈ R ↔ x ∈ F ∧ η₁ x.1 ∈ K₂ ∧ η₂ x.2 ∈ K₂ := fun {x} => by
    rw [hRdef]
    exact Iff.rfl
  have hRR : ⁅R, R⁆ ≤ gr.range := by
    rw [commutator_le]
    intro a ha b hb
    obtain ⟨haF, ha1, ha2⟩ := hR.1 ha
    obtain ⟨hbF, hb1, hb2⟩ := hR.1 hb
    obtain ⟨ma, hma⟩ : ∃ ma : K₂.comap η₁, (ma : E₁) = a.1 := ⟨⟨a.1, ha1⟩, rfl⟩
    obtain ⟨mb, hmb⟩ : ∃ mb : K₂.comap η₁, (mb : E₁) = b.1 := ⟨⟨b.1, hb1⟩, rfl⟩
    have hca : ((φ ma : E₂))⁻¹ * a.2 ∈ center E₂ := hC₂ (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hma, ← hF.1 haF, inv_mul_cancel])
    have hcb : ((φ mb : E₂))⁻¹ * b.2 ∈ center E₂ := hC₂ (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, hmb, ← hF.1 hbF, inv_mul_cancel])
    refine ⟨⁅ma, mb⁆, ?_⟩
    rw [hgr]
    refine Prod.ext ?_ ?_
    · change (K₂.comap η₁).subtype ⁅ma, mb⁆ = ⁅a.1, b.1⁆
      rw [map_commutatorElement, coe_subtype, hma, hmb]
    · change (K₂.comap η₂).subtype (φ ⁅ma, mb⁆) = ⁅a.2, b.2⁆
      rw [map_commutatorElement, map_commutatorElement, coe_subtype,
        show a.2 = (φ ma : E₂) * ((φ ma : E₂)⁻¹ * a.2) by group,
        show b.2 = (φ mb : E₂) * ((φ mb : E₂)⁻¹ * b.2) by group,
        CFSG.LieType.Steinberg.Isogeny.commutatorElement_mul_mul_of_mem_center _ _ hca hcb]
  have h34 : ∀ x ∈ ⁅K₂.comap ι, K₂.comap ι⁆, ι x = 1 → x = 1 := by
    intro x hx hx1
    rw [hcomap, ← map_commutator] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    have hy1 : ηΔ y = 1 := by rw [← hιmk]; exact hx1
    have hle : (K₂.comap ηΔ).map Δ.subtype ≤ R := by
      rintro _ ⟨z, hz, rfl⟩
      have hz' : ηΔ z ∈ K₂ := hz
      refine hR.2 ⟨hΔF z.2, ?_, ?_⟩
      · change η₁ (z : E₁ × E₂).1 ∈ K₂
        rw [← hp₁x, ← hηp₁]
        exact hz'
      · change η₂ (z : E₁ × E₂).2 ∈ K₂
        rw [← hp₂x, ← hηp₂]
        exact hz'
    have hyR : (y : E₁ × E₂) ∈ gr.range := by
      have h := mem_map_of_mem Δ.subtype hy
      rw [map_commutator] at h
      exact hRR (commutator_mono hle hle h)
    obtain ⟨m, hm⟩ := hyR
    have hm1 : η₁ (m : E₁) = 1 := by
      have h := congrArg Prod.fst hm
      rw [hgr] at h
      change (m : E₁) = (y : E₁ × E₂).1 at h
      rw [h, ← hp₁x, ← hηp₁]
      exact hy1
    exact (QuotientGroup.eq_one_iff y).2 (hD'.2 (hD.2 ⟨m, hm1, hm⟩))
  have hbot := hCT (Δ ⧸ D') ι hι hιC hL h34
  have hker : ∀ x : Δ, ηΔ x = 1 → (x : E₁ × E₂) ∈ D := by
    intro x hx
    have hx' : (x : Δ ⧸ D') ∈ ι.ker := by rw [MonoidHom.mem_ker, hιmk]; exact hx
    rw [hbot, mem_bot, QuotientGroup.eq_one_iff] at hx'
    exact hD'.1 hx'
  have hbij₁ : Function.Bijective p₁ := by
    refine ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_, fun e => ?_⟩
    · obtain ⟨m, hm, hmx⟩ := hD.1 (hker x (by rw [hηp₁, hx, map_one]))
      rw [hgr] at hmx
      have hm1 : m = 1 := Subtype.ext (by
        have h := congrArg Prod.fst hmx
        change (m : E₁) = (x : E₁ × E₂).1 at h
        rw [h, ← hp₁x, hx]
        rfl)
      rw [hm1, map_one] at hmx
      exact Subtype.ext hmx.symm
    · obtain ⟨y, hy, hye⟩ : e ∈ Δ.map (MonoidHom.fst E₁ E₂) := hΔ1 ▸ mem_top _
      exact ⟨⟨y, hy⟩, by rw [hp₁x]; exact hye⟩
  have hbij₂ : Function.Bijective p₂ := by
    refine ⟨(injective_iff_map_eq_one _).2 fun x hx => ?_, fun e => ?_⟩
    · obtain ⟨m, hm, hmx⟩ := hD.1 (hker x (by rw [hηp₂, hx, map_one]))
      rw [hgr] at hmx
      have hm1 : m = 1 := by
        have h := congrArg Prod.snd hmx
        change ((φ m : K₂.comap η₂) : E₂) = (x : E₁ × E₂).2 at h
        have h' : φ m = 1 := Subtype.ext (by rw [h, ← hp₂x, hx]; rfl)
        rw [← map_one φ] at h'
        exact φ.injective h'
      rw [hm1, map_one] at hmx
      exact Subtype.ext hmx.symm
    · obtain ⟨y, hy, hye⟩ : e ∈ Δ.map (MonoidHom.snd E₁ E₂) := hΔ2 ▸ mem_top _
      exact ⟨⟨y, hy⟩, by rw [hp₂x]; exact hye⟩
  refine ⟨(MulEquiv.ofBijective p₁ hbij₁).symm.trans (MulEquiv.ofBijective p₂ hbij₂),
    fun x => ?_⟩
  obtain ⟨y, hy⟩ : ∃ y, (MulEquiv.ofBijective p₁ hbij₁).symm x = y := ⟨_, rfl⟩
  have hyx : p₁ y = x := by
    rw [← hy]
    exact (MulEquiv.ofBijective p₁ hbij₁).apply_symm_apply x
  rw [MulEquiv.trans_apply, hy]
  change η₂ (p₂ y) = η₁ x
  rw [← hηp₂, hηp₁, hyx]

theorem exists_mulEquiv_of_levi34
    {E₁ E₂ : Type} [Group E₁] [Group E₂] [Finite E₁] [Finite E₂]
    [Group.IsPerfect E₁] [Group.IsPerfect E₂] {η₁ : E₁ →* twistedE6Group 2 1}
    {η₂ : E₂ →* twistedE6Group 2 1} (hη₁ : Function.Surjective η₁)
    (hη₂ : Function.Surjective η₂) (hC₁ : η₁.ker ≤ center E₁) (hC₂ : η₂.ker ≤ center E₂)
    (h2₁ : IsPGroup 2 η₁.ker) (h2₂ : IsPGroup 2 η₂.ker)
    (φ : ((twistedE6Datum 2 1).levi levi34).comap η₁ ≃*
      ((twistedE6Datum 2 1).levi levi34).comap η₂)
    (hφ : ∀ x, η₂ (φ x) = η₁ x) :
    ∃ ψ : E₁ ≃* E₂, ∀ x, η₂ (ψ x) = η₁ x := by
  have := isPerfect_twistedE6Group
  exact exists_mulEquiv_of_graph (K₁ := (twistedE6Datum 2 1).levi levi123)
    (fun G _ _ ι hι hC hL h34 => ker_eq_bot_of_injOn_levi ι hι hC hL h34) hη₁ hη₂ hC₁ hC₂
    (commutator_comap_levi123_inf_ker_eq_bot η₁ hη₁ hC₁ h2₁).1
    (commutator_comap_levi123_inf_ker_eq_bot η₂ hη₂ hC₂ h2₂).1 φ hφ

end CFSG.EvenSmallLie.TwoE6
