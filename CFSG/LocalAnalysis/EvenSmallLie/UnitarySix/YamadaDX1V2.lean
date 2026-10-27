module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDV2

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

theorem eq_of_card_le_two {K : Subgroup G} [Finite K] (hK : Nat.card K ≤ 2) {b b' : G}
    (hb : b ∈ K) (hb' : b' ∈ K) (h1 : b ≠ 1) (h1' : b' ≠ 1) : b = b' := by
  by_contra hne
  have hsub : ({1, b, b'} : Set G) ⊆ K := by
    rintro x (rfl | rfl | rfl)
    · exact one_mem _
    · exact hb
    · exact hb'
  have h3 : ({1, b, b'} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [Ne.symm h1, Ne.symm h1']), Set.ncard_pair hne]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  rw [h3, ← Nat.card_coe_set_eq] at hle
  change 3 ≤ Nat.card K at hle
  omega

namespace Hyp

variable {d : Data G} (h : Hyp d)
include h

theorem X₈_cent_X₁ [Finite G] {b : G} (hb : b ∈ d.X₈) (h1 : b * d.u₁ = d.u₁ * b)
    (h2 : b * d.u₂ = d.u₂ * b) : b = 1 := by
  have hX : d.X₁ ≤ centralizer ({b} : Set G) := by
    rw [h.X₁_eq, closure_le]
    rintro x (rfl | rfl)
    · exact mem_centralizer_singleton_iff.mpr h1.symm
    · exact mem_centralizer_singleton_iff.mpr h2.symm
  have hbX : b ∈ centralizer (d.X₁ : Set G) := mem_centralizer_iff.mpr fun x hx =>
    mem_centralizer_singleton_iff.mp (hX hx)
  have hz := h.A₄_cent_X₁ (mem_inf.mpr ⟨h.X₈_le_A₄ hb, hbX⟩)
  have : b ∈ d.X₈ ⊓ zpowers d.z := mem_inf.mpr ⟨hb, hz⟩
  rwa [h.X₈_inf_z, mem_bot] at this

theorem j₀_mem_normalizer_X₈ [Finite G] : d.j₀ ∈ normalizer (d.X₈ : Set G) := by
  have := le_normalizer_commutator_right d.A₄ d.J h.j₀_mem_J
  rwa [h.comm_A₄_J] at this

theorem card_X₈_cent_u₁ [Finite G] :
    Nat.card (d.X₈ ⊓ centralizer ({d.u₁} : Set G) : Subgroup G) ≤ 2 := by
  set C₁ := d.X₈ ⊓ centralizer ({d.u₁} : Set G) with hC₁
  set C₂ := d.X₈ ⊓ centralizer ({d.u₂} : Set G) with hC₂
  have hj := h.j₀_mem_normalizer_X₈
  have hmap : C₁.map (MulAut.conj d.j₀).toMonoidHom ≤ C₂ := by
    rintro _ ⟨b, ⟨hb, hbu⟩, rfl⟩
    refine mem_inf.mpr ⟨(mem_normalizer_iff.mp hj b).mp hb, mem_centralizer_singleton_iff.mpr ?_⟩
    have e := mem_centralizer_singleton_iff.mp hbu
    change d.j₀ * b * d.j₀⁻¹ * d.u₂ = d.u₂ * (d.j₀ * b * d.j₀⁻¹)
    rw [← h.j₀_u₁]
    calc d.j₀ * b * d.j₀⁻¹ * (d.j₀ * d.u₁ * d.j₀⁻¹) = d.j₀ * (b * d.u₁) * d.j₀⁻¹ := by group
      _ = d.j₀ * (d.u₁ * b) * d.j₀⁻¹ := by rw [e]
      _ = d.j₀ * d.u₁ * d.j₀⁻¹ * (d.j₀ * b * d.j₀⁻¹) := by group
  have hcard : Nat.card C₁ ≤ Nat.card C₂ := by
    rw [← card_map_of_injective (f := (MulAut.conj d.j₀).toMonoidHom) (MulEquiv.injective _)]
    exact card_le_of_le hmap
  have hinj : Function.Injective (fun p : C₁ × C₂ => (⟨(p.1 : G) * p.2,
      mul_mem (mem_inf.mp p.1.2).1 (mem_inf.mp p.2.2).1⟩ : d.X₈)) := by
    rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ ⟨⟨a', ha'⟩, ⟨b', hb'⟩⟩ e
    have e' : a * b = a' * b' := congrArg Subtype.val e
    have hc : a'⁻¹ * a = b' * b⁻¹ := by
      calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
        _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [e']
        _ = b' * b⁻¹ := by group
    have h1 : a'⁻¹ * a ∈ C₁ := mul_mem (inv_mem ha') ha
    have h2 : a'⁻¹ * a ∈ C₂ := hc ▸ mul_mem hb' (inv_mem hb)
    have h3 : a'⁻¹ * a = 1 := h.X₈_cent_X₁ (mem_inf.mp h1).1
      (mem_centralizer_singleton_iff.mp (mem_inf.mp h1).2)
      (mem_centralizer_singleton_iff.mp (mem_inf.mp h2).2)
    have haa : a = a' := by
      calc a = a' * (a'⁻¹ * a) := by group
        _ = a' := by rw [h3, mul_one]
    have hbb : b = b' := by
      have : b' * b⁻¹ = 1 := hc ▸ h3
      calc b = (b' * b⁻¹)⁻¹ * b' := by group
        _ = b' := by rw [this, inv_one, one_mul]
    subst haa hbb
    rfl
  have h4 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, h.card_X₈] at h4
  nlinarith

theorem comm_mul_D₄ [Finite G] {x y y' : G} (hx : x ∈ normalizer (d.D₄ : Set G))
    (hy : y ∈ d.D₄) (hy' : y' ∈ d.D₄) :
    x * (y * y') * x⁻¹ * (y * y')⁻¹ = (x * y * x⁻¹ * y⁻¹) * (x * y' * x⁻¹ * y'⁻¹) := by
  have h1 : x * y' * x⁻¹ ∈ d.D₄ := (mem_normalizer_iff.mp hx y').mp hy'
  have h2 := h.D₄_comm (inv_mem hy) h1
  have h3 := h.D₄_comm (inv_mem hy) (inv_mem hy')
  calc x * (y * y') * x⁻¹ * (y * y')⁻¹ = x * y * x⁻¹ * (x * y' * x⁻¹) * (y'⁻¹ * y⁻¹) := by
        group
    _ = x * y * x⁻¹ * (x * y' * x⁻¹) * (y⁻¹ * y'⁻¹) := by rw [← h3]
    _ = x * y * x⁻¹ * ((x * y' * x⁻¹) * y⁻¹) * y'⁻¹ := by group
    _ = x * y * x⁻¹ * (y⁻¹ * (x * y' * x⁻¹)) * y'⁻¹ := by rw [← h2]
    _ = (x * y * x⁻¹ * y⁻¹) * (x * y' * x⁻¹ * y'⁻¹) := by group

theorem X₁_le_normalizer_D₄ [Finite G] {x : G} (hx : x ∈ d.X₁) :
    x ∈ normalizer (d.D₄ : Set G) := h.Λ_le_normalizer_D₄ (h.X₁_le_Λ hx)

theorem comm_X₁_DJ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x y : G} (hx : x ∈ d.X₁)
    (hy : y ∈ ⁅d.D₄, d.J⁆) : ∃ b ∈ d.X₈, b * x = x * b ∧ ∃ v ∈ d.V₁,
      x * y * x⁻¹ * y⁻¹ = b * v := by
  have hyD := h.comm_D₄_J_le hy
  have hc := h.comm_X₁_D₄ hx hyD (mem_sup_left (h.crossed_comm_D₄_J hy))
  have hle : d.Z₂S ⊔ d.V₁ ≤ d.X₈ ⊔ d.V₁ :=
    sup_le (sup_le le_sup_left (zpowers_le.mpr (mem_sup_right h.z_mem_V₁))) le_sup_right
  obtain ⟨b, hb, v, hv, hbv⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun b hb v hv => h.D₄_comm (h.A₄_le_D₄ (h.X₈_le_A₄ hb)) (V₁_le_D₄ hv)) (hle hc)
  refine ⟨b, hb, ?_, v, hv, hbv.symm⟩
  have hx2 : x * x = 1 := h.X₁_sq hx
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hxv : x * v = v * x := mem_centralizer_iff.mp (V₁_le_cent_X₁ hv) x hx
  have hb2 : b * b = 1 := h.A₄_sq (h.X₈_le_A₄ hb)
  have hbv' : b * v = v * b := h.D₄_comm (h.A₄_le_D₄ (h.X₈_le_A₄ hb)) (V₁_le_D₄ hv)
  set c := x * y * x⁻¹ * y⁻¹ with hcdef
  have hxc : x * c * x⁻¹ = c⁻¹ := by
    rw [hcdef, hxi]
    calc x * (x * y * x * y⁻¹) * x = (x * x) * y * x * y⁻¹ * x := by group
      _ = (x * y * x * y⁻¹)⁻¹ := by
          rw [hx2, one_mul, show (x * y * x * y⁻¹)⁻¹ = y * x⁻¹ * y⁻¹ * x⁻¹ by group, hxi]
  have hcinv : c⁻¹ = b * v := by
    rw [← hbv]
    calc (b * v)⁻¹ = v⁻¹ * b⁻¹ := by group
      _ = v * b := by
          rw [inv_eq_of_mul_eq_one_right (hV v hv), inv_eq_of_mul_eq_one_right hb2]
      _ = b * v := hbv'.symm
  have hxv' : v * x⁻¹ = x⁻¹ * v := by rw [hxi]; exact hxv.symm
  have e : x * b * x⁻¹ * v = b * v := by
    calc x * b * x⁻¹ * v = x * b * (x⁻¹ * v) := by group
      _ = x * b * (v * x⁻¹) := by rw [hxv']
      _ = x * (b * v) * x⁻¹ := by group
      _ = x * c * x⁻¹ := by rw [hbv]
      _ = b * v := by rw [hxc, hcinv]
  have e2 : x * b * x⁻¹ = b := mul_right_cancel e
  calc b * x = x * b * x⁻¹ * x := by rw [e2]
    _ = x * b := by group

theorem X₈_inf_V₁ [Finite G] {b : G} (hb : b ∈ d.X₈) (hbV : b ∈ d.V₁) : b = 1 := by
  have hz := h.V₁_inf_H_le (mem_inf.mpr ⟨hbV, h.L_le_H (h.A₄_le_L (h.X₈_le_A₄ hb))⟩)
  have : b ∈ d.X₈ ⊓ zpowers d.z := mem_inf.mpr ⟨hb, hz⟩
  rwa [h.X₈_inf_z, mem_bot] at this

theorem comm_u₁_mul_of_not [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {y y' : G}
    (hy : y ∈ ⁅d.D₄, d.J⁆) (hy' : y' ∈ ⁅d.D₄, d.J⁆)
    (hn : d.u₁ * y * d.u₁⁻¹ * y⁻¹ ∉ d.V₁) (hn' : d.u₁ * y' * d.u₁⁻¹ * y'⁻¹ ∉ d.V₁) :
    d.u₁ * (y * y') * d.u₁⁻¹ * (y * y')⁻¹ ∈ d.V₁ := by
  obtain ⟨b, hb, hbu, v, hv, hc⟩ := h.comm_X₁_DJ hV h.u₁_mem hy
  obtain ⟨b', hb', hbu', v', hv', hc'⟩ := h.comm_X₁_DJ hV h.u₁_mem hy'
  have hb1 : b ≠ 1 := fun e => hn (by rw [hc, e, one_mul]; exact hv)
  have hb1' : b' ≠ 1 := fun e => hn' (by rw [hc', e, one_mul]; exact hv')
  have hbb : b = b' := eq_of_card_le_two h.card_X₈_cent_u₁
    (mem_inf.mpr ⟨hb, mem_centralizer_singleton_iff.mpr hbu⟩)
    (mem_inf.mpr ⟨hb', mem_centralizer_singleton_iff.mpr hbu'⟩) hb1 hb1'
  have hbD := h.A₄_le_D₄ (h.X₈_le_A₄ hb)
  rw [h.comm_mul_D₄ (h.X₁_le_normalizer_D₄ h.u₁_mem) (h.comm_D₄_J_le hy) (h.comm_D₄_J_le hy'),
    hc, hc', ← hbb]
  have hbv := h.D₄_comm (V₁_le_D₄ hv) hbD
  have hb2 : b * b = 1 := h.A₄_sq (h.X₈_le_A₄ hb)
  rw [show b * v * (b * v') = (v * b) * b * v' by rw [← hbv]; group,
    show v * b * b * v' = v * (b * b) * v' by group, hb2, mul_one]
  exact mul_mem hv hv'

theorem comm_u₁_of_comm_u₂ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {w : G}
    (hw : w ∈ ⁅d.D₄, d.J⁆) (h2 : d.u₂ * w * d.u₂⁻¹ * w⁻¹ ∈ d.V₁) :
    d.u₁ * w * d.u₁⁻¹ * w⁻¹ ∈ d.V₁ := by
  have hu₃ : d.u₁ * d.u₂ ∈ d.X₁ := mul_mem h.u₁_mem h.u₂_mem
  obtain ⟨b₁, hb₁, hbu₁, v₁, hv₁, hc₁⟩ := h.comm_X₁_DJ hV h.u₁_mem hw
  obtain ⟨b₃, hb₃, hbu₃, v₃, hv₃, hc₃⟩ := h.comm_X₁_DJ hV hu₃ hw
  set v₂ := d.u₂ * w * d.u₂⁻¹ * w⁻¹ with hv₂def
  have hu₁v₂ : d.u₁ * v₂ * d.u₁⁻¹ = v₂ := by
    rw [mem_centralizer_iff.mp (V₁_le_cent_X₁ h2) d.u₁ h.u₁_mem, mul_inv_cancel_right]
  have hsplit : d.u₁ * d.u₂ * w * (d.u₁ * d.u₂)⁻¹ * w⁻¹ = v₂ * (d.u₁ * w * d.u₁⁻¹ * w⁻¹) := by
    rw [← hu₁v₂, hv₂def]
    group
  rw [hc₃, hc₁] at hsplit
  have hD : ∀ {a}, a ∈ d.X₈ → a ∈ d.D₄ := fun ha => h.A₄_le_D₄ (h.X₈_le_A₄ ha)
  have hbb : b₃ = b₁ := by
    have e1 : b₁⁻¹ * b₃ = v₂ * v₁ * v₃⁻¹ := by
      have c1 := h.D₄_comm (V₁_le_D₄ h2) (hD hb₁)
      have c2 := h.D₄_comm (V₁_le_D₄ hv₃) (hD hb₃)
      calc b₁⁻¹ * b₃ = b₁⁻¹ * (b₃ * v₃) * v₃⁻¹ := by group
        _ = b₁⁻¹ * (v₂ * (b₁ * v₁)) * v₃⁻¹ := by rw [hsplit]
        _ = b₁⁻¹ * ((v₂ * b₁) * v₁) * v₃⁻¹ := by group
        _ = b₁⁻¹ * ((b₁ * v₂) * v₁) * v₃⁻¹ := by rw [c1]
        _ = v₂ * v₁ * v₃⁻¹ := by group
    have := h.X₈_inf_V₁ (mul_mem (inv_mem hb₁) hb₃)
      (e1 ▸ mul_mem (mul_mem h2 hv₁) (inv_mem hv₃))
    calc b₃ = b₁ * (b₁⁻¹ * b₃) := by group
      _ = b₁ := by rw [this, mul_one]
  rw [hbb] at hbu₃
  have hbu₂ : b₁ * d.u₂ = d.u₂ * b₁ := by
    calc b₁ * d.u₂ = d.u₁⁻¹ * (d.u₁ * b₁) * d.u₂ := by group
      _ = d.u₁⁻¹ * (b₁ * d.u₁) * d.u₂ := by rw [hbu₁]
      _ = d.u₁⁻¹ * (b₁ * (d.u₁ * d.u₂)) := by group
      _ = d.u₁⁻¹ * ((d.u₁ * d.u₂) * b₁) := by rw [hbu₃]
      _ = d.u₂ * b₁ := by group
  rw [hc₁, h.X₈_cent_X₁ hb₁ hbu₁ hbu₂, one_mul]
  exact hv₁

theorem j₀_mem_normalizer_DJ [Finite G] : d.j₀ ∈ normalizer ((⁅d.D₄, d.J⁆ : Subgroup G) : Set G) :=
  le_normalizer_commutator_right d.D₄ d.J h.j₀_mem_J

theorem comm_u₁_conj_j₀ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {y : G}
    (hy : y ∈ ⁅d.D₄, d.J⁆) (h1 : d.u₁ * y * d.u₁⁻¹ * y⁻¹ ∈ d.V₁) :
    d.u₁ * (d.j₀ * y * d.j₀⁻¹) * d.u₁⁻¹ * (d.j₀ * y * d.j₀⁻¹)⁻¹ ∈ d.V₁ := by
  have hy' : d.j₀ * y * d.j₀⁻¹ ∈ ⁅d.D₄, d.J⁆ :=
    (mem_normalizer_iff.mp h.j₀_mem_normalizer_DJ y).mp hy
  refine h.comm_u₁_of_comm_u₂ hV hy' ?_
  have e : d.u₂ * (d.j₀ * y * d.j₀⁻¹) * d.u₂⁻¹ * (d.j₀ * y * d.j₀⁻¹)⁻¹ =
      d.j₀ * (d.u₁ * y * d.u₁⁻¹ * y⁻¹) * d.j₀⁻¹ := by
    rw [← h.j₀_u₁]
    group
  rw [e]
  exact (mem_normalizer_iff.mp h.j₀_mem_normalizer_V₁ _).mp h1

theorem comm_u₁_DJ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {y : G} (hy : y ∈ ⁅d.D₄, d.J⁆) :
    d.u₁ * y * d.u₁⁻¹ * y⁻¹ ∈ d.V₁ := by
  by_contra hn
  have hJ : ∀ {w}, w ∈ ⁅d.D₄, d.J⁆ → d.j₀ * w * d.j₀⁻¹ ∈ ⁅d.D₄, d.J⁆ := fun hw =>
    (mem_normalizer_iff.mp h.j₀_mem_normalizer_DJ _).mp hw
  set y' := d.j₀ * y * d.j₀⁻¹ with hy'def
  set y'' := d.j₀ * y' * d.j₀⁻¹ with hy''def
  have hy' : y' ∈ ⁅d.D₄, d.J⁆ := hJ hy
  have hy'' : y'' ∈ ⁅d.D₄, d.J⁆ := hJ hy'
  have hback : d.j₀ * y'' * d.j₀⁻¹ = y := by
    rw [hy''def, hy'def]
    have hj3 : d.j₀ * d.j₀ * d.j₀ = 1 := by
      rw [← h.j₀_pow, pow_three, mul_assoc]
    calc d.j₀ * (d.j₀ * (d.j₀ * y * d.j₀⁻¹) * d.j₀⁻¹) * d.j₀⁻¹ =
        (d.j₀ * d.j₀ * d.j₀) * y * (d.j₀ * d.j₀ * d.j₀)⁻¹ := by group
      _ = y := by rw [hj3]; group
  have hn'' : d.u₁ * y'' * d.u₁⁻¹ * y''⁻¹ ∉ d.V₁ := fun h3 => hn (by
    have := h.comm_u₁_conj_j₀ hV hy'' h3
    rwa [hback] at this)
  have hn' : d.u₁ * y' * d.u₁⁻¹ * y'⁻¹ ∉ d.V₁ := fun h3 =>
    hn'' (h.comm_u₁_conj_j₀ hV hy' h3)
  have h12 := h.comm_u₁_mul_of_not hV hy hy' hn hn'
  have hDJ : ∀ {w}, w ∈ ⁅d.D₄, d.J⁆ → w ∈ d.D₄ := fun hw => h.comm_D₄_J_le hw
  have hnorm : y * y' * y'' = 1 := h.normJ_comm hy
  have e := h.comm_mul_D₄ (h.X₁_le_normalizer_D₄ h.u₁_mem) (mul_mem (hDJ hy) (hDJ hy')) (hDJ hy'')
  rw [hnorm] at e
  simp only [mul_one, inv_one, mul_inv_cancel] at e
  apply hn''
  have := mul_mem (inv_mem h12) (e ▸ one_mem d.V₁ : _ ∈ d.V₁)
  rwa [inv_mul_cancel_left] at this

theorem comm_u₂_DJ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {y : G} (hy : y ∈ ⁅d.D₄, d.J⁆) :
    d.u₂ * y * d.u₂⁻¹ * y⁻¹ ∈ d.V₁ := by
  have hy' : d.j₀⁻¹ * y * d.j₀ ∈ ⁅d.D₄, d.J⁆ := by
    have := (mem_normalizer_iff.mp (inv_mem h.j₀_mem_normalizer_DJ) y).mp hy
    rwa [inv_inv] at this
  have h1 := h.comm_u₁_DJ hV hy'
  have e : d.u₂ * y * d.u₂⁻¹ * y⁻¹ =
      d.j₀ * (d.u₁ * (d.j₀⁻¹ * y * d.j₀) * d.u₁⁻¹ * (d.j₀⁻¹ * y * d.j₀)⁻¹) * d.j₀⁻¹ := by
    rw [← h.j₀_u₁]
    group
  rw [e]
  exact (mem_normalizer_iff.mp h.j₀_mem_normalizer_V₁ _).mp h1

theorem comm_X₁_DJ_mem [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x y : G} (hx : x ∈ d.X₁)
    (hy : y ∈ ⁅d.D₄, d.J⁆) : x * y * x⁻¹ * y⁻¹ ∈ d.V₁ := by
  rcases h.X₁_cases hx with rfl | rfl | rfl | rfl
  · simp
  · exact h.comm_u₁_DJ hV hy
  · exact h.comm_u₂_DJ hV hy
  · have h2 := h.comm_u₂_DJ hV hy
    have e : d.u₁ * d.u₂ * y * (d.u₁ * d.u₂)⁻¹ * y⁻¹ =
        (d.u₁ * (d.u₂ * y * d.u₂⁻¹ * y⁻¹) * d.u₁⁻¹) * (d.u₁ * y * d.u₁⁻¹ * y⁻¹) := by group
    rw [e, mem_centralizer_iff.mp (V₁_le_cent_X₁ h2) d.u₁ h.u₁_mem, mul_inv_cancel_right]
    exact mul_mem h2 (h.comm_u₁_DJ hV hy)

theorem comm_X₁_V₂ [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x y : G} (hx : x ∈ d.X₁)
    (hy : y ∈ d.V₂) : x * y * x⁻¹ * y⁻¹ ∈ d.V₁ := by
  obtain ⟨a, ha, v, hv, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
    (fun a ha v hv => h.D₄_comm (h.comm_D₄_J_le ha) (V₁_le_D₄ hv)) hy
  rw [h.comm_mul_D₄ (h.X₁_le_normalizer_D₄ hx) (h.comm_D₄_J_le ha) (V₁_le_D₄ hv),
    mem_centralizer_iff.mp (V₁_le_cent_X₁ hv) x hx, mul_inv_cancel_right, mul_inv_cancel,
    mul_one]
  exact h.comm_X₁_DJ_mem hV hx ha

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
