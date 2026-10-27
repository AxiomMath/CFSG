module

public import CFSG.GH74.GLS.IVK.Lifted.CentralProd
public import CFSG.GH74.GLS.IVK.L2.GroupAux
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2Stmt
public import CFSG.GH74.GLS.Stage2.Signalizer.L48Sl2Facts
public import CFSG.GH74.GLS.Stage2.Local.Defs

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.L48

open Subgroup CFSG.GH74.GLS.IVK CFSG.GH74.GLS.IVK.Lifted CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {A : Type} [Group A]

noncomputable def prodHom (L₁ L₂ : Subgroup A) (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    ↥L₁ × ↥L₂ →* ↥(L₁ ⊔ L₂) :=
  (commProd L₁ L₂ hcom).codRestrict (L₁ ⊔ L₂) (fun p => by
    rw [commProd_apply]
    exact mul_mem (mem_sup_left p.1.2) (mem_sup_right p.2.2))

theorem prodHom_surjective (L₁ L₂ : Subgroup A) (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    Function.Surjective (prodHom L₁ L₂ hcom) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_of_commute hcom).mp hx
  exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩

noncomputable def projHom (L₁ L₂ : Subgroup A) (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) :
    ↥(L₁ ⊔ L₂) →* ↥L₁ ⧸ center ↥L₁ :=
  MonoidHom.liftOfSurjective (prodHom L₁ L₂ hcom) (prodHom_surjective L₁ L₂ hcom)
    ⟨(QuotientGroup.mk' (center ↥L₁)).comp (MonoidHom.fst ↥L₁ ↥L₂), by
      rintro ⟨x₁, x₂⟩ hx
      rw [MonoidHom.mem_ker] at hx ⊢
      have h1 : (x₁ : A) * (x₂ : A) = 1 := congrArg Subtype.val hx
      have h2 : (x₁ : A) = (x₂ : A)⁻¹ := eq_inv_of_mul_eq_one_left h1
      have h3 : (x₁ : A) ∈ L₂ := by rw [h2]; exact L₂.inv_mem x₂.2
      show QuotientGroup.mk' (center ↥L₁) x₁ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcom g g.2 x₁ h3)⟩

theorem projHom_apply (L₁ L₂ : Subgroup A) (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) {x₁ x₂ : A}
    (h₁ : x₁ ∈ L₁) (h₂ : x₂ ∈ L₂) (hx : x₁ * x₂ ∈ L₁ ⊔ L₂) :
    projHom L₁ L₂ hcom ⟨x₁ * x₂, hx⟩ = (QuotientGroup.mk ⟨x₁, h₁⟩ : ↥L₁ ⧸ center ↥L₁) := by
  have : (⟨x₁ * x₂, hx⟩ : ↥(L₁ ⊔ L₂)) = prodHom L₁ L₂ hcom (⟨x₁, h₁⟩, ⟨x₂, h₂⟩) := rfl
  rw [this]
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ _

theorem map_mem_normalizer {G H : Type*} [Group G] [Group H] (f : G →* H) {K : Subgroup G} {x : G}
    (hx : x ∈ normalizer (K : Set G)) : f x ∈ normalizer ((K.map f : Subgroup H) : Set H) := by
  have fwd : ∀ x : G, x ∈ normalizer (K : Set G) → ∀ y ∈ K.map f, f x * y * (f x)⁻¹ ∈ K.map f := by
    intro x hx y hy
    obtain ⟨k, hk, rfl⟩ := hy
    exact ⟨x * k * x⁻¹, (Subgroup.mem_normalizer_iff.mp hx k).mp hk, by simp⟩
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fwd x hx y, fun hy => ?_⟩
  have := fwd x⁻¹ ((normalizer (K : Set G)).inv_mem hx) _ hy
  simpa [mul_assoc] using this


open CFSG.GH74.GLS

theorem proj_trivial (hk : SL2Key) (L₁ L₂ : Subgroup A) (hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F)) (e : ↥L₁ ≃* ↥(StatedSL 2 F))
    (hinv₂ : ∀ b ∈ L₂, b * b ∈ L₁ → b * b ≠ 1 → ∃ y ∈ L₂, y * b * y⁻¹ = b⁻¹)
    {a₁ a₂ t : A} (ha₁ : a₁ ∈ L₁) (ha₂ : a₂ ∈ L₂) (ht : t = a₁ * a₂) (ht2 : t * t = 1)
    (hne : a₁ * a₁ ≠ 1) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Y : Subgroup A} (hYp : IsPGroup p ↥Y)
    (hYL : Y ≤ L₁ ⊔ L₂) (hN : ∀ c ∈ L₁ ⊔ L₂, c * t = t * c → c ∈ normalizer (Y : Set A))
    (hcomm : ⁅Y, zpowers t⁆ = Y) :
    ∀ y ∈ Y, ∀ x₁ ∈ L₁, ∀ x₂ ∈ L₂, y = x₁ * x₂ → ∀ g ∈ L₁, g * x₁ = x₁ * g := by
  classical
  obtain ⟨-, hsq1, hcen1, -⟩ := sl2_facts hodd e
  have htL : t ∈ L₁ ⊔ L₂ := by rw [ht]; exact mul_mem (mem_sup_left ha₁) (mem_sup_right ha₂)
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := hcom a₁ ha₁ a₂ ha₂
  have hsq : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    have h := ht2
    rw [ht] at h
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [ha₁₂]
      _ = (a₁ * a₂) * (a₁ * a₂) := by group
      _ = 1 := h
  have hsq₁ : a₁ * a₁ ∈ L₂ := by
    rw [eq_inv_of_mul_eq_one_left hsq]; exact L₂.inv_mem (mul_mem ha₂ ha₂)
  have hsq₂ : a₂ * a₂ ∈ L₁ := by
    rw [eq_inv_of_mul_eq_one_right hsq]; exact L₁.inv_mem (mul_mem ha₁ ha₁)
  have hne₂ : a₂ * a₂ ≠ 1 := fun h => hne (by
    rw [h, mul_one] at hsq; exact hsq)
  set α₁ : ↥L₁ := ⟨a₁, ha₁⟩ with hα₁
  have hα₁sq : α₁ * α₁ ∈ center ↥L₁ := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hcom g g.2 (a₁ * a₁) hsq₁)
  have hα₁ne : α₁ * α₁ ≠ 1 := fun h => hne (congrArg Subtype.val h)
  set Q₁ : Type := ↥L₁ ⧸ center ↥L₁ with hQ₁
  set ā₁ : Q₁ := QuotientGroup.mk α₁ with hā₁
  have hā₁sq : ā₁ * ā₁ = 1 := by
    rw [hā₁, ← QuotientGroup.mk_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hα₁sq
  have hā₁ne : ā₁ ≠ 1 := by
    intro h
    have : α₁ ∈ center ↥L₁ := (QuotientGroup.eq_one_iff _).mp h
    exact hα₁ne (hsq1 α₁ this)
  set ρ := projHom L₁ L₂ hcom with hρ
  set YS : Subgroup ↥(L₁ ⊔ L₂) := Y.subgroupOf (L₁ ⊔ L₂) with hYS
  set Y₁ : Subgroup Q₁ := YS.map ρ with hY₁
  have hY₁p : IsPGroup p ↥Y₁ := by
    have h1 : IsPGroup p ↥YS := hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYL).symm
    exact h1.map ρ
  have hρt : ρ ⟨t, htL⟩ = ā₁ := by
    have : (⟨t, htL⟩ : ↥(L₁ ⊔ L₂)) = ⟨a₁ * a₂, by rw [← ht]; exact htL⟩ := Subtype.ext ht
    rw [this]
    exact projHom_apply L₁ L₂ hcom ha₁ ha₂ _
  have hρL₁ : ∀ (c : ↥L₁) (hx : (c : A) ∈ L₁ ⊔ L₂), ρ ⟨c, hx⟩ = QuotientGroup.mk c := by
    intro c hx
    have h := projHom_apply L₁ L₂ hcom c.2 (one_mem L₂) (by simpa using hx)
    have : (⟨(c : A), hx⟩ : ↥(L₁ ⊔ L₂)) = ⟨(c : A) * 1, by simpa using hx⟩ := Subtype.ext (mul_one _).symm
    rw [this, h]
  have hρL₂ : ∀ (x₂ : A) (h₂ : x₂ ∈ L₂) (hx : x₂ ∈ L₁ ⊔ L₂), ρ ⟨x₂, hx⟩ = 1 := by
    intro x₂ h₂ hx
    have h := projHom_apply L₁ L₂ hcom (one_mem L₁) h₂ (by simpa using hx)
    have : (⟨x₂, hx⟩ : ↥(L₁ ⊔ L₂)) = ⟨1 * x₂, by simpa using hx⟩ := Subtype.ext (one_mul _).symm
    rw [this, h]
    exact QuotientGroup.mk_one _
  have hnorm_lift : ∀ (x : A) (hxL : x ∈ L₁ ⊔ L₂), x ∈ normalizer (Y : Set A) →
      ρ ⟨x, hxL⟩ ∈ normalizer (Y₁ : Set Q₁) := by
    intro x hxL hxN
    refine map_mem_normalizer ρ (K := YS) ?_
    rw [Subgroup.mem_normalizer_iff] at hxN ⊢
    intro y
    exact hxN (y : A)
  have hinvt : a₁⁻¹ * a₂⁻¹ = a₁ * a₂ := by
    have h1 : (a₁ * a₂) * (a₁ * a₂) = 1 := by rw [← ht]; exact ht2
    calc a₁⁻¹ * a₂⁻¹ = (a₂ * a₁)⁻¹ := by group
      _ = (a₁ * a₂)⁻¹ := by rw [ha₁₂]
      _ = a₁ * a₂ := inv_eq_of_mul_eq_one_right h1
  have hN₁ : ∀ c : Q₁, c * ā₁ = ā₁ * c → c ∈ normalizer (Y₁ : Set Q₁) := by
    intro c hc
    obtain ⟨c₀, rfl⟩ := QuotientGroup.mk_surjective c
    have hcL : (c₀ : A) ∈ L₁ := c₀.2
    have hcL' : (c₀ : A) ∈ L₁ ⊔ L₂ := mem_sup_left hcL
    have hcom2 : (c₀ : A) * a₂ = a₂ * (c₀ : A) := hcom _ hcL a₂ ha₂
    have hcomm0 : ⁅c₀, α₁⁆ ∈ center ↥L₁ := by
      have h0 : (QuotientGroup.mk' (center ↥L₁)) ⁅c₀, α₁⁆ = 1 := by
        rw [map_commutatorElement]
        exact commutatorElement_eq_one_iff_mul_comm.mpr hc
      exact (QuotientGroup.eq_one_iff _).mp h0
    by_cases hz : ⁅c₀, α₁⁆ = 1
    · have h1 : c₀ * α₁ = α₁ * c₀ := commutatorElement_eq_one_iff_mul_comm.mp hz
      have h1' : (c₀ : A) * a₁ = a₁ * (c₀ : A) := congrArg Subtype.val h1
      have hxt : (c₀ : A) * t = t * (c₀ : A) := by
        rw [ht]
        calc (c₀ : A) * (a₁ * a₂) = ((c₀ : A) * a₁) * a₂ := by group
          _ = (a₁ * (c₀ : A)) * a₂ := by rw [h1']
          _ = a₁ * ((c₀ : A) * a₂) := by group
          _ = a₁ * (a₂ * (c₀ : A)) := by rw [hcom2]
          _ = (a₁ * a₂) * (c₀ : A) := by group
      have := hnorm_lift _ hcL' (hN _ hcL' hxt)
      rwa [hρL₁ c₀ hcL'] at this
    · have hζ : ⁅c₀, α₁⁆ = α₁ * α₁ := hcen1 _ hcomm0 _ hα₁sq hz hα₁ne
      have hα₁4 : (α₁ * α₁) * (α₁ * α₁) = 1 := hsq1 _ hα₁sq
      have hinv : c₀ * α₁ * c₀⁻¹ = α₁⁻¹ := by
        have e1 : c₀ * α₁ * c₀⁻¹ = (α₁ * α₁) * α₁ := by
          calc c₀ * α₁ * c₀⁻¹ = ⁅c₀, α₁⁆ * α₁ := by simp [commutatorElement_def]
            _ = (α₁ * α₁) * α₁ := by rw [hζ]
        rw [e1]
        have h4 : (α₁ * α₁ * α₁) * α₁ = 1 := by
          calc α₁ * α₁ * α₁ * α₁ = (α₁ * α₁) * (α₁ * α₁) := by group
            _ = 1 := hα₁4
        exact eq_inv_of_mul_eq_one_left h4
      have hinvA : (c₀ : A) * a₁ * (c₀ : A)⁻¹ = a₁⁻¹ := congrArg Subtype.val hinv
      obtain ⟨y₂, hy₂L, hy₂⟩ := hinv₂ a₂ ha₂ hsq₂ hne₂
      have hy₂a₁ : y₂ * a₁ = a₁ * y₂ := (hcom a₁ ha₁ y₂ hy₂L).symm
      have hc₁ : (c₀ : A) * a₁ = a₁⁻¹ * (c₀ : A) := by
        calc (c₀ : A) * a₁ = ((c₀ : A) * a₁ * (c₀ : A)⁻¹) * (c₀ : A) := by group
          _ = a₁⁻¹ * (c₀ : A) := by rw [hinvA]
      have hy₂' : y₂ * a₂ = a₂⁻¹ * y₂ := by
        calc y₂ * a₂ = (y₂ * a₂ * y₂⁻¹) * y₂ := by group
          _ = a₂⁻¹ * y₂ := by rw [hy₂]
      have hca₂inv : (c₀ : A) * a₂⁻¹ = a₂⁻¹ * (c₀ : A) := by
        calc (c₀ : A) * a₂⁻¹ = a₂⁻¹ * (a₂ * (c₀ : A)) * a₂⁻¹ := by group
          _ = a₂⁻¹ * ((c₀ : A) * a₂) * a₂⁻¹ := by rw [hcom2]
          _ = a₂⁻¹ * (c₀ : A) := by group
      have hxL : (c₀ : A) * y₂ ∈ L₁ ⊔ L₂ := mul_mem hcL' (mem_sup_right hy₂L)
      have hxt : ((c₀ : A) * y₂) * t = t * ((c₀ : A) * y₂) := by
        rw [ht]
        calc (c₀ : A) * y₂ * (a₁ * a₂) = (c₀ : A) * (y₂ * a₁) * a₂ := by group
          _ = (c₀ : A) * (a₁ * y₂) * a₂ := by rw [hy₂a₁]
          _ = ((c₀ : A) * a₁) * (y₂ * a₂) := by group
          _ = (a₁⁻¹ * (c₀ : A)) * (a₂⁻¹ * y₂) := by rw [hc₁, hy₂']
          _ = a₁⁻¹ * ((c₀ : A) * a₂⁻¹) * y₂ := by group
          _ = a₁⁻¹ * (a₂⁻¹ * (c₀ : A)) * y₂ := by rw [hca₂inv]
          _ = (a₁⁻¹ * a₂⁻¹) * ((c₀ : A) * y₂) := by group
          _ = (a₁ * a₂) * ((c₀ : A) * y₂) := by rw [hinvt]
      have hmem := hnorm_lift _ hxL (hN _ hxL hxt)
      have hρx : ρ ⟨(c₀ : A) * y₂, hxL⟩ = QuotientGroup.mk c₀ := by
        have : (⟨(c₀ : A) * y₂, hxL⟩ : ↥(L₁ ⊔ L₂)) =
            ⟨(c₀ : A), hcL'⟩ * ⟨y₂, mem_sup_right hy₂L⟩ := rfl
        rw [this, map_mul, hρL₁ c₀ hcL', hρL₂ y₂ hy₂L (mem_sup_right hy₂L), mul_one]
      rwa [hρx] at hmem
  have hY₁comm : ⁅Y₁, zpowers ā₁⁆ = Y₁ := by
    have h1 : ⁅YS, zpowers (⟨t, htL⟩ : ↥(L₁ ⊔ L₂))⁆ = YS := by
      apply Subgroup.map_injective (L₁ ⊔ L₂).subtype_injective
      rw [Subgroup.map_commutator, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hYL]
      simpa using hcomm
    calc ⁅Y₁, zpowers ā₁⁆ = ⁅YS.map ρ, (zpowers (⟨t, htL⟩ : ↥(L₁ ⊔ L₂))).map ρ⁆ := by
          rw [MonoidHom.map_zpowers, hρt]
      _ = (⁅YS, zpowers (⟨t, htL⟩ : ↥(L₁ ⊔ L₂))⁆).map ρ := (Subgroup.map_commutator _ _ _).symm
      _ = Y₁ := by rw [h1]
  have hcomm₁ := hk F hodd ↥L₁ ⟨e⟩ ā₁ hā₁sq hā₁ne p hp hp2 Y₁ hY₁p hN₁
  have hY₁bot : Y₁ = ⊥ := by
    have : ⁅Y₁, zpowers ā₁⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact (Commute.zpow_left (hcomm₁ y hy : Commute y ā₁).symm m).eq
    rw [← hY₁comm, this]
  intro y hy x₁ hx₁ x₂ hx₂ hyx g hg
  have hyL : y ∈ L₁ ⊔ L₂ := hYL hy
  have hmemY : ρ ⟨y, hyL⟩ ∈ Y₁ := ⟨⟨y, hyL⟩, hy, rfl⟩
  rw [hY₁bot, Subgroup.mem_bot] at hmemY
  have h2 : ρ ⟨y, hyL⟩ = QuotientGroup.mk ⟨x₁, hx₁⟩ := by
    have : (⟨y, hyL⟩ : ↥(L₁ ⊔ L₂)) = ⟨x₁ * x₂, by rw [← hyx]; exact hyL⟩ := Subtype.ext hyx
    rw [this]
    exact projHom_apply L₁ L₂ hcom hx₁ hx₂ _
  rw [h2, QuotientGroup.eq_one_iff, Subgroup.mem_center_iff] at hmemY
  exact congrArg Subtype.val (hmemY ⟨g, hg⟩)


open CFSG.GH74.GLS.Stage2.Local

theorem star_sl2_sl2 (hk : SL2Key) {A : Type} [Group A] [Finite A] (L₁ L₂ : Subgroup A) (r₁ r₂ : ℕ)
    (hc : IsCentralProd L₁ L₂ (L₁ ⊔ L₂)) (h1 : HasSL2Model ↥L₁ (fun q => q = r₁))
    (h2 : HasSL2Model ↥L₂ (fun q => q = r₂))
    (ho1 : Odd r₁) (ho2 : Odd r₂) (t : A) (htL : t ∈ L₁ ⊔ L₂) (ht2 : t * t = 1)
    (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) (Y : Subgroup A) (hYp : IsPGroup p ↥Y) (hYL : Y ≤ L₁ ⊔ L₂)
    (hN : ∀ c ∈ L₁ ⊔ L₂, c * t = t * c → c ∈ normalizer (Y : Set A))
    (hcomm : ⁅Y, zpowers t⁆ = Y) : Y = ⊥ := by
  classical
  obtain ⟨F₁, i₁, f₁, hF₁, ⟨e₁⟩⟩ := h1
  obtain ⟨F₂, i₂, f₂, hF₂, ⟨e₂⟩⟩ := h2
  have hodd₁ : Odd (Nat.card F₁) := by rw [hF₁]; exact ho1
  have hodd₂ : Odd (Nat.card F₂) := by rw [hF₂]; exact ho2
  have hcom : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a := hc.2.1
  have hcom' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hcom b hb a ha).symm
  obtain ⟨hs1a, hs1b, hs1c, hs1d⟩ := sl2_facts hodd₁ e₁
  obtain ⟨hs2a, hs2b, hs2c, hs2d⟩ := sl2_facts hodd₂ e₂
  obtain ⟨a₁, ha₁, a₂, ha₂, hta⟩ := (mem_sup_of_commute hcom).mp htL
  have ha₁₂ : a₁ * a₂ = a₂ * a₁ := hcom a₁ ha₁ a₂ ha₂
  have hsq : (a₁ * a₁) * (a₂ * a₂) = 1 := by
    have h := ht2
    rw [hta] at h
    calc (a₁ * a₁) * (a₂ * a₂) = a₁ * (a₁ * a₂) * a₂ := by group
      _ = a₁ * (a₂ * a₁) * a₂ := by rw [ha₁₂]
      _ = (a₁ * a₂) * (a₁ * a₂) := by group
      _ = 1 := h
  have hsq₁ : a₁ * a₁ ∈ L₂ := by
    rw [eq_inv_of_mul_eq_one_left hsq]; exact L₂.inv_mem (mul_mem ha₂ ha₂)
  have hsq₂ : a₂ * a₂ ∈ L₁ := by
    rw [eq_inv_of_mul_eq_one_right hsq]; exact L₁.inv_mem (mul_mem ha₁ ha₁)
  have hinv₂ : ∀ b ∈ L₂, b * b ∈ L₁ → b * b ≠ 1 → ∃ y ∈ L₂, y * b * y⁻¹ = b⁻¹ := by
    intro b hb hbb hb1
    have hcb : (⟨b, hb⟩ : ↥L₂) * ⟨b, hb⟩ ∈ center ↥L₂ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcom (b * b) hbb g g.2).symm
    obtain ⟨y, hy⟩ := hs2d ⟨b, hb⟩ hcb (fun h => hb1 (congrArg Subtype.val h))
    exact ⟨y, y.2, congrArg Subtype.val hy⟩
  have hinv₁ : ∀ b ∈ L₁, b * b ∈ L₂ → b * b ≠ 1 → ∃ y ∈ L₁, y * b * y⁻¹ = b⁻¹ := by
    intro b hb hbb hb1
    have hcb : (⟨b, hb⟩ : ↥L₁) * ⟨b, hb⟩ ∈ center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hcom' (b * b) hbb g g.2).symm
    obtain ⟨y, hy⟩ := hs1d ⟨b, hb⟩ hcb (fun h => hb1 (congrArg Subtype.val h))
    exact ⟨y, y.2, congrArg Subtype.val hy⟩
  by_cases hcase : a₁ * a₁ = 1
  ·
    have ha₂sq : a₂ * a₂ = 1 := by rw [hcase, one_mul] at hsq; exact hsq
    have hα₁c : (⟨a₁, ha₁⟩ : ↥L₁) ∈ center ↥L₁ := hs1a _ (Subtype.ext hcase)
    have hα₂c : (⟨a₂, ha₂⟩ : ↥L₂) ∈ center ↥L₂ := hs2a _ (Subtype.ext ha₂sq)
    have htc : ∀ x ∈ L₁ ⊔ L₂, x * t = t * x := by
      intro x hx
      obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := (mem_sup_of_commute hcom).mp hx
      have e1 : x₁ * a₁ = a₁ * x₁ :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hα₁c ⟨x₁, hx₁⟩)
      have e2 : x₂ * a₂ = a₂ * x₂ :=
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hα₂c ⟨x₂, hx₂⟩)
      have e3 : x₂ * a₁ = a₁ * x₂ := (hcom a₁ ha₁ x₂ hx₂).symm
      have e4 : x₁ * a₂ = a₂ * x₁ := hcom x₁ hx₁ a₂ ha₂
      have e5 : x₁ * x₂ = x₂ * x₁ := hcom x₁ hx₁ x₂ hx₂
      rw [hta]
      calc x₁ * x₂ * (a₁ * a₂) = x₁ * (x₂ * a₁) * a₂ := by group
        _ = x₁ * (a₁ * x₂) * a₂ := by rw [e3]
        _ = (x₁ * a₁) * (x₂ * a₂) := by group
        _ = (a₁ * x₁) * (a₂ * x₂) := by rw [e1, e2]
        _ = a₁ * (x₁ * a₂) * x₂ := by group
        _ = a₁ * (a₂ * x₁) * x₂ := by rw [e4]
        _ = a₁ * a₂ * (x₁ * x₂) := by group
    have hbot : ⁅Y, zpowers t⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
      exact ((Commute.zpow_left (htc y (hYL hy) : Commute y t).symm m)).eq
    rw [← hcomm, hbot]
  · have hne₂ : a₂ * a₂ ≠ 1 := fun h => hcase (by rw [h, mul_one] at hsq; exact hsq)
    have hxa : ∀ y ∈ Y, ∀ x₁ ∈ L₁, ∀ x₂ ∈ L₂, y = x₁ * x₂ → ∀ g ∈ L₁, g * x₁ = x₁ * g :=
      proj_trivial hk L₁ L₂ hcom hodd₁ e₁ hinv₂ ha₁ ha₂ hta ht2 hcase hp hp2 hYp hYL hN hcomm
    have hxb : ∀ y ∈ Y, ∀ x₂ ∈ L₂, ∀ x₁ ∈ L₁, y = x₂ * x₁ → ∀ g ∈ L₂, g * x₂ = x₂ * g := by
      refine proj_trivial hk L₂ L₁ hcom' hodd₂ e₂ hinv₁ ha₂ ha₁ ?_ ht2 hne₂ hp hp2 hYp
        (by rw [sup_comm]; exact hYL) ?_ ?_
      · rw [hta]; exact ha₁₂
      · intro c hc; rw [sup_comm] at hc; exact hN c hc
      · exact hcomm
    rw [eq_bot_iff]
    intro y hy
    rw [Subgroup.mem_bot]
    obtain ⟨x₁, hx₁, x₂, hx₂, hyx⟩ := (mem_sup_of_commute hcom).mp (hYL hy)
    have hc1 : (⟨x₁, hx₁⟩ : ↥L₁) ∈ center ↥L₁ := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (hxa y hy x₁ hx₁ x₂ hx₂ hyx g g.2)
    have hc2 : (⟨x₂, hx₂⟩ : ↥L₂) ∈ center ↥L₂ := by
      rw [Subgroup.mem_center_iff]
      intro g
      refine Subtype.ext (hxb y hy x₂ hx₂ x₁ hx₁ ?_ g g.2)
      rw [hyx]; exact hcom x₁ hx₁ x₂ hx₂
    have hx1sq : x₁ * x₁ = 1 := congrArg Subtype.val (hs1b _ hc1)
    have hx2sq : x₂ * x₂ = 1 := congrArg Subtype.val (hs2b _ hc2)
    have hysq : y * y = 1 := by
      rw [hyx]
      calc x₁ * x₂ * (x₁ * x₂) = x₁ * (x₂ * x₁) * x₂ := by group
        _ = x₁ * (x₁ * x₂) * x₂ := by rw [← hcom x₁ hx₁ x₂ hx₂]
        _ = (x₁ * x₁) * (x₂ * x₂) := by group
        _ = 1 := by rw [hx1sq, hx2sq, one_mul]
    obtain ⟨k, hk'⟩ := hYp ⟨y, hy⟩
    have hk1 : y ^ p ^ k = 1 := congrArg Subtype.val hk'
    have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hysq
    have hcop : Nat.Coprime (p ^ k) 2 := Nat.Coprime.pow_left _ ((Nat.coprime_primes hp Nat.prime_two).mpr hp2)
    have := pow_gcd_eq_one.mpr ⟨hk1, hy2⟩
    rwa [Nat.Coprime.gcd_eq_one hcop, pow_one] at this

end CFSG.GH74.GLS.Stage2.Signalizer.L48
