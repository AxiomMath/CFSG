module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13Cls
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.Child5Y13E
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaQSetting

public section

namespace CFSG.EvenSmallLie.UnitarySix.Child5

open Subgroup Matrix YamadaPar YamadaD

variable {G : Type} [Group G] {d : YamadaD.Data G}

@[expose] def TrivW (d : YamadaD.Data G) (g : G) : Prop :=
  ∀ y ∈ d.D₁, (g * y * g⁻¹)⁻¹ * y ∈ d.V₁

theorem trivW_mul {g g' : G} (hgV : g ∈ normalizer (d.V₁ : Set G)) (hg : TrivW d g)
    (hg' : TrivW d g') : TrivW d (g * g') := by
  intro y hy
  have h1 : g * ((g' * y * g'⁻¹)⁻¹ * y) * g⁻¹ ∈ d.V₁ := (mem_normalizer_iff.mp hgV _).mp (hg' y hy)
  have e : (g * g' * y * (g * g')⁻¹)⁻¹ * y =
      (g * ((g' * y * g'⁻¹)⁻¹ * y) * g⁻¹) * ((g * y * g⁻¹)⁻¹ * y) := by group
  rw [e]
  exact mul_mem h1 (hg y hy)

theorem trivW_inv {g : G} (hgD : g ∈ normalizer (d.D₁ : Set G)) (hg : TrivW d g) :
    TrivW d g⁻¹ := by
  intro y hy
  have hy' : g⁻¹ * y * g⁻¹⁻¹ ∈ d.D₁ := (mem_normalizer_iff.mp (inv_mem hgD) y).mp hy
  have e : (g⁻¹ * y * g⁻¹⁻¹)⁻¹ * y =
      ((g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹)⁻¹ * (g⁻¹ * y * g⁻¹⁻¹))⁻¹ := by group
  rw [e]
  exact inv_mem (hg _ hy')

theorem trivW_of_mem (hs : YamadaPar.ElemSec d.D₁ d.V₁) {g : G} (hgD : g ∈ d.D₁) :
    TrivW d g := by
  intro y hy
  rw [show (g * y * g⁻¹)⁻¹ * y = g * y⁻¹ * g⁻¹ * y⁻¹⁻¹ by group]
  exact hs.comm g hgD y⁻¹ (inv_mem hy)

theorem trivW_conj {g c : G} (hcD : c ∈ normalizer (d.D₁ : Set G))
    (hcV : c ∈ normalizer (d.V₁ : Set G)) (hg : TrivW d g) : TrivW d (c * g * c⁻¹) := by
  intro y hy
  have hy' : c⁻¹ * y * c⁻¹⁻¹ ∈ d.D₁ := (mem_normalizer_iff.mp (inv_mem hcD) y).mp hy
  have h1 := (mem_normalizer_iff.mp hcV _).mp (hg _ hy')
  have e : (c * g * c⁻¹ * y * (c * g * c⁻¹)⁻¹)⁻¹ * y =
      c * ((g * (c⁻¹ * y * c⁻¹⁻¹) * g⁻¹)⁻¹ * (c⁻¹ * y * c⁻¹⁻¹)) * c⁻¹ := by group
  rw [e]
  exact h1

theorem exists_kap_eq [Finite G] (h : Hyp d) (hB : HypB d) (hV : ∀ v ∈ d.V₁, v * v = 1) (h416 : Hyp416 d)
    {c : G} (hc : c ∈ d.A₁ ⊓ d.A₂) : ∃ z ∈ d.D₁ ⊓ d.D₂, kap d z = c := by
  set X := d.D₁ ⊓ d.D₂
  have htX : d.t ∈ normalizer (X : Set G) :=
    Hyp.mem_normalizer_inf h.t_mem_normalizer_D₁ h.t_mem_normalizer_D₂
  set κ := kapHom h hB X inf_le_right htX
  set R := κ.range.map X.subtype
  have hRB : R ≤ d.A₁ ⊓ d.A₂ := by
    rintro _ ⟨_, ⟨z, rfl⟩, rfl⟩
    have hz := mem_inf.mp z.2
    have hA₂ := kap_mem_A₂ h hB hz.2
    exact mem_inf.mpr ⟨mem_A₁_of_mem_A₂ h hB hV (kap_mem h.t_mem_normalizer_D₁ hz.1) hA₂, hA₂⟩
  have hker : Nat.card κ.ker ≤ Nat.card (d.A₁ ⊓ d.A₂ : Subgroup G) := by
    refine Nat.card_le_card_of_injective (fun z => ⟨((z : X) : G), ?_⟩) ?_
    · have h1 : kap d ((z : X) : G) = 1 := congrArg Subtype.val z.2
      have hzt := (kap_eq_one_iff h).mp h1
      have hz := mem_inf.mp (z : X).2
      refine mem_inf.mpr ⟨mem_A₁_of_comm h hB hV hz.1 hzt, ?_⟩
      rw [← h.D₂_inf_H]
      exact mem_inf.mpr ⟨hz.2, mem_centralizer_singleton_iff.mpr hzt.symm⟩
    · intro x y hxy
      have h1 : ((x : X) : G) = ((y : X) : G) := by
        have := congrArg (fun w : (d.A₁ ⊓ d.A₂ : Subgroup G) => (w : G)) hxy
        simpa using this
      exact Subtype.ext (Subtype.ext h1)
  have hR : R = d.A₁ ⊓ d.A₂ := by
    refine Subgroup.eq_of_le_of_card_ge hRB ?_
    have h1 := card_eq_card_ker_mul_card_range κ
    rw [show Nat.card X = 2 ^ 10 from h.card_D₁_inf_D₂ hB hV] at h1
    rw [show Nat.card R = Nat.card κ.range from card_map_of_injective (subtype_injective _)]
    rw [h416.card_A₁A₂] at hker ⊢
    by_contra hlt
    have := Nat.mul_lt_mul_of_le_of_lt hker (not_le.mp hlt) (by norm_num)
    omega
  rw [← hR] at hc
  obtain ⟨_, ⟨z, rfl⟩, rfl⟩ := hc
  exact ⟨z, z.2, rfl⟩

theorem kap_inv [Finite G] (h : Hyp d) (hB : HypB d) {z : G} (hz : z ∈ d.D₂) :
    kap d z⁻¹ = (kap d z)⁻¹ := by
  have h1 := kap_mul h hB hz (inv_mem hz)
  rw [mul_inv_cancel, kap_one] at h1
  exact (eq_inv_of_mul_eq_one_right h1.symm)


theorem D₂_le_normalizer_V₁ [Finite G] (h : Hyp d) (hB : HypB d) : d.D₂ ≤ normalizer (d.V₁ : Set G) :=
  fun x hx => YamadaPar.mem_normalizer_of_conj_eq fun v hv => by
    rw [h.D₂_comm hB hx (h.V₁_le_D₂ hv), mul_inv_cancel_right]

section E

variable [Finite G]
variable {θ : d.K₁ ≃* SU42b} {ιG : (Fin 8 → ZMod 2) → G}

@[expose] noncomputable def eG (θ : d.K₁ ≃* SU42b) : Subgroup G :=
  (E16.map θ.symm.toMonoidHom).map d.K₁.subtype

omit [Finite G] in
theorem mem_eG {x : G} : x ∈ eG θ ↔ ∃ g ∈ E16, ((θ.symm g : d.K₁) : G) = x := by
  constructor
  · rintro ⟨y, ⟨g, hg, rfl⟩, rfl⟩
    exact ⟨g, hg, rfl⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨θ.symm g, ⟨g, hg, rfl⟩, rfl⟩

omit [Finite G] in
theorem eG_le_K₁ : eG θ ≤ d.K₁ := by
  intro x hx
  obtain ⟨g, -, rfl⟩ := mem_eG.mp hx
  exact (θ.symm g).2

omit [Finite G] in
theorem eG_le_A₂ (hc : Y13Coords d θ ιG) : eG θ ≤ d.A₂ := by
  intro x hx
  obtain ⟨g, hg, rfl⟩ := mem_eG.mp hx
  have hle : E16 ≤ d.A₂.comap (d.K₁.subtype.comp θ.symm.toMonoidHom) := by
    rw [E16, closure_le]
    rintro _ ⟨m, rfl⟩
    exact hc.E_mem m m.2
  exact hle hg

omit [Finite G] in
theorem card_eG_ge : 16 ≤ Nat.card (eG θ) := by
  rw [eG, card_map_of_injective (subtype_injective _),
    card_map_of_injective (MulEquiv.injective θ.symm)]
  exact card_E16_ge

theorem A₂_eq_sup (h : Hyp d) (h416 : Hyp416 d)
    (hc : Y13Coords d θ ιG) (hKA : d.K₁ ⊓ d.A₁ = ⊥) : eG θ ⊔ (d.A₁ ⊓ d.A₂) = d.A₂ := by
  have hle : eG θ ⊔ (d.A₁ ⊓ d.A₂) ≤ d.A₂ := sup_le (eG_le_A₂ hc) inf_le_right
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have hcomm : ∀ a ∈ eG θ, ∀ b ∈ d.A₁ ⊓ d.A₂, a * b = b * a :=
    fun a ha b hb => h.A₂_comm a (eG_le_A₂ hc ha) b (mem_inf.mp hb).2
  have h1 := card_sup_mul_card_inf_of_commute hcomm
  have hbot : eG θ ⊓ (d.A₁ ⊓ d.A₂) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : x ∈ d.K₁ ⊓ d.A₁ :=
      mem_inf.mpr ⟨eG_le_K₁ (mem_inf.mp hx).1, (mem_inf.mp (mem_inf.mp hx).2).1⟩
    rwa [hKA] at hx'
  rw [hbot, card_bot, mul_one, h416.card_A₁A₂] at h1
  rw [h.card_A₂, h1]
  have := card_eG_ge (θ := θ)
  norm_num
  omega

theorem exists_eG_of_kap_mem (h : Hyp d) (hB : HypB d)
    (hV : ∀ v ∈ d.V₁, v * v = 1) (h416 : Hyp416 d) (hc : Y13Coords d θ ιG)
    (hKA : d.K₁ ⊓ d.A₁ = ⊥) {x : G} (hx : x ∈ d.D₂) (hkx : kap d x ∈ d.D₁) :
    ∃ g ∈ E16, x⁻¹ * ((θ.symm g : d.K₁) : G) ∈ d.D₁ := by
  have hcA₂ := kap_mem_A₂ h hB hx
  obtain ⟨z, hz, hzc⟩ := exists_kap_eq h hB hV h416
    (mem_inf.mpr ⟨mem_A₁_of_mem_A₂ h hB hV hkx hcA₂, hcA₂⟩)
  have hz' := mem_inf.mp hz
  have h1 : kap d (x * z⁻¹) = 1 := by
    rw [kap_mul h hB hx (inv_mem hz'.2), kap_inv h hB hz'.2, hzc, mul_inv_cancel]
  have h2 : x * z⁻¹ ∈ d.A₂ := by
    rw [← h.D₂_inf_H]
    exact mem_inf.mpr ⟨mul_mem hx (inv_mem hz'.2),
      mem_centralizer_singleton_iff.mpr ((kap_eq_one_iff h).mp h1).symm⟩
  rw [← A₂_eq_sup h h416 hc hKA] at h2
  obtain ⟨g, hg, b, hb, hgb⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha b hb => h.A₂_comm a (eG_le_A₂ hc ha) b (mem_inf.mp hb).2) h2
  obtain ⟨g', hg', rfl⟩ := mem_eG.mp hg
  refine ⟨g', hg', ?_⟩
  have e : x = ((θ.symm g' : d.K₁) : G) * b * z := by
    rw [hgb, inv_mul_cancel_right]
  rw [e, show (((θ.symm g' : d.K₁) : G) * b * z)⁻¹ * ((θ.symm g' : d.K₁) : G) = z⁻¹ * b⁻¹ by
    group]
  exact mul_mem (inv_mem hz'.1) (inv_mem (h.A₁_le_D₁ hB hV (mem_inf.mp hb).1))


theorem eq_one_of_trivW (h : Hyp d) (hC : HypC d) (hc : Y13Coords d θ ιG) {g : G} (hg : g ∈ eG θ)
    (hT : TrivW d g) (hA : d.A₁ ≤ d.D₁) : g = 1 := by
  have := h.V₁_normal_AV
  obtain ⟨g', -, rfl⟩ := mem_eG.mp hg
  have h1 := eq_one_of_cent h hC hc (θ.symm g') fun a ha => hT a (hA ha)
  rw [h1]
  rfl

theorem mem_D₁_of_trivW (h : Hyp d) (hB : HypB d) (hC : HypC d)
    (hV : ∀ v ∈ d.V₁, v * v = 1) (h416 : Hyp416 d) (hc : Y13Coords d θ ιG)
    (hKA : d.K₁ ⊓ d.A₁ = ⊥) (hN : d.D₂ ≤ normalizer (d.D₁ : Set G)) {x : G} (hx : x ∈ d.D₂)
    (hT : TrivW d x) : x ∈ d.D₁ := by
  have hs := elemSec h hB hC hV
  have hA := h.A₁_le_D₁ hB hV
  have hD₂V := D₂_le_normalizer_V₁ h hB
  have htx : d.t * x * d.t⁻¹ ∈ d.D₂ := t_conj_mem_of_normalizer h.t_mem_normalizer_D₂ hx
  have hTk : TrivW d (kap d x) :=
    trivW_mul (hD₂V htx) (trivW_conj h.t_mem_normalizer_D₁ h.t_mem_normalizer_V₁ hT)
      (trivW_inv (hN hx) hT)
  have hkA₂ := kap_mem_A₂ h hB hx
  have hkD : kap d x ∈ d.D₁ := by
    have h2 := hkA₂
    rw [← A₂_eq_sup h h416 hc hKA] at h2
    obtain ⟨g, hg, b, hb, hgb⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => h.A₂_comm a (eG_le_A₂ hc ha) b (mem_inf.mp hb).2) h2
    have hbD : b ∈ d.D₁ := hA (mem_inf.mp hb).1
    have hTg : TrivW d g := by
      have e : g = kap d x * b⁻¹ := by rw [← hgb, mul_inv_cancel_right]
      rw [e]
      exact trivW_mul (hD₂V (h.A₂_le_D₂ hkA₂)) hTk
        (trivW_inv (hN (h.A₂_le_D₂ (mem_inf.mp hb).2)) (trivW_of_mem hs hbD))
    rw [← hgb, eq_one_of_trivW h hC hc hg hTg hA, one_mul]
    exact hbD
  obtain ⟨g', hg', hxg⟩ := exists_eG_of_kap_mem h hB hV h416 hc hKA hx hkD
  have hg : ((θ.symm g' : d.K₁) : G) ∈ eG θ := mem_eG.mpr ⟨g', hg', rfl⟩
  have hTe : TrivW d ((θ.symm g' : d.K₁) : G) := by
    have e : ((θ.symm g' : d.K₁) : G) = x * (x⁻¹ * ((θ.symm g' : d.K₁) : G)) := by group
    rw [e]
    exact trivW_mul (hD₂V hx) hT (trivW_of_mem hs hxg)
  rw [eq_one_of_trivW h hC hc hg hTe hA, mul_one] at hxg
  exact inv_mem_iff.mp hxg

end E

end CFSG.EvenSmallLie.UnitarySix.Child5
