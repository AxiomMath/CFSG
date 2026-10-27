module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDOmega
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.YamadaDSettingB

public section

namespace CFSG.EvenSmallLie.UnitarySix.YamadaD

open Subgroup

variable {G : Type*} [Group G]

theorem comm_of_mem_closure {S : Set G} (hS : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) {a b : G}
    (ha : a ∈ closure S) (hb : b ∈ closure S) : a * b = b * a := by
  have h1 : closure S ≤ centralizer S :=
    closure_le _ |>.mpr fun x hx => mem_centralizer_iff.mpr fun y hy => hS y hy x hx
  have h2 := closure_le_centralizer_centralizer S ha
  exact (mem_centralizer_iff.mp h2 b (h1 hb)).symm

namespace Data

variable (d : Data G)

@[expose] def D₂gen : Set G := (d.A₂ : Set G) ∪ {x | ∃ k ∈ d.K₂, ∃ v ∈ d.V₁, x = k * v * k⁻¹}

@[expose] def D₂g : Subgroup G := closure d.D₂gen

end Data

namespace Hyp

variable {d : Data G} (h : Hyp d) (hB : HypB d)
include h hB

theorem K₂_le_H : d.K₂ ≤ d.H := hB.K₂_le_L.trans h.L_le_H

theorem K₂_comm_t {k : G} (hk : k ∈ d.K₂) : k * d.t = d.t * k :=
  mem_centralizer_singleton_iff.mp (h.K₂_le_H hB hk)

theorem K₂_le_normalizer_C₂ [Finite G] : d.K₂ ≤ normalizer (d.C₂ : Set G) := fun _ hk =>
  h.C₂_normal (mem_normalizer_sup (hB.K₂_le_normalizer hk)
    (mem_normalizer_zpowers (h.K₂_comm_t hB hk)))

theorem K₂_cent_z_normalizer_V₁ [Finite G] {k : G} (hk : k ∈ d.K₂) (hkz : k * d.z = d.z * k) :
    k ∈ normalizer (d.V₁ : Set G) :=
  h.X_le_normalizer_V₁ (CHz_le_X (mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr hkz,
    h.K₂_le_H hB hk⟩))

omit hB in
theorem exists_Λ_move_z [Finite G] : ∃ l ∈ d.Λ, l * d.z * l⁻¹ ≠ d.z := by
  by_contra hne
  push Not at hne
  have himg : (fun l => l * d.z * l⁻¹) '' (d.Λ : Set G) ⊆ {d.z} := by
    rintro _ ⟨l, hl, rfl⟩
    exact hne l hl
  have hle : d.A₄ ≤ zpowers d.z := by
    refine h.A₄_le_orbit_z.trans ?_
    rw [closure_le]
    exact himg.trans (Set.singleton_subset_iff.mpr (mem_zpowers _))
  have := card_le_of_le hle
  rw [h.card_A₄, h.card_zpowers_z] at this
  norm_num at this

theorem comm_conj_V₁ [Finite G] {k : G} (hk : k ∈ d.K₂) {v w : G} (hv : v ∈ d.V₁)
    (hw : w ∈ d.V₁) : v * (k * w * k⁻¹) = (k * w * k⁻¹) * v := by
  by_cases hkz : k * d.z * k⁻¹ = d.z
  · have hkz' : k * d.z = d.z * k := by
      calc k * d.z = k * d.z * k⁻¹ * k := by group
        _ = d.z * k := by rw [hkz]
    have hkV := h.K₂_cent_z_normalizer_V₁ hB hk hkz'
    exact h.V₁_comm hv ((mem_normalizer_iff.mp hkV w).mp hw)
  · obtain ⟨l, hl, hlz⟩ := h.exists_Λ_move_z
    have hlK := hB.Λ_le_K₂ hl
    obtain ⟨m, hm, hmz, hml⟩ := hB.K₂_trans l hlK k hk hlz hkz
    have hcK : (m * l)⁻¹ * k ∈ d.K₂ := mul_mem (inv_mem (mul_mem hm hlK)) hk
    have hcz : (m * l)⁻¹ * k * d.z = d.z * ((m * l)⁻¹ * k) := by
      have e : (m * l)⁻¹ * k * d.z * ((m * l)⁻¹ * k)⁻¹ = d.z := by
        calc (m * l)⁻¹ * k * d.z * ((m * l)⁻¹ * k)⁻¹ =
            l⁻¹ * m⁻¹ * (k * d.z * k⁻¹) * m * l := by group
          _ = l⁻¹ * m⁻¹ * (m * (l * d.z * l⁻¹) * m⁻¹) * m * l := by rw [hml]
          _ = d.z := by group
      calc (m * l)⁻¹ * k * d.z = (m * l)⁻¹ * k * d.z * ((m * l)⁻¹ * k)⁻¹ * ((m * l)⁻¹ * k) := by
            group
        _ = d.z * ((m * l)⁻¹ * k) := by rw [e]
    have hcV := h.K₂_cent_z_normalizer_V₁ hB hcK hcz
    have hmV := h.K₂_cent_z_normalizer_V₁ hB hm hmz
    have hw' : (m * l)⁻¹ * k * w * ((m * l)⁻¹ * k)⁻¹ ∈ d.V₁ :=
      (mem_normalizer_iff.mp hcV w).mp hw
    have hv' : m⁻¹ * v * m ∈ d.V₁ := by
      have := (mem_normalizer_iff.mp (inv_mem hmV) v).mp hv
      rwa [inv_inv] at this
    have hlw : l * ((m * l)⁻¹ * k * w * ((m * l)⁻¹ * k)⁻¹) * l⁻¹ ∈ d.D₄ :=
      (mem_normalizer_iff.mp (h.Λ_le_normalizer_D₄ hl) _).mp (V₁_le_D₄ hw')
    have hcomm := h.D₄_comm (V₁_le_D₄ hv') hlw
    calc v * (k * w * k⁻¹) = m * ((m⁻¹ * v * m) *
          (l * ((m * l)⁻¹ * k * w * ((m * l)⁻¹ * k)⁻¹) * l⁻¹)) * m⁻¹ := by group
      _ = m * ((l * ((m * l)⁻¹ * k * w * ((m * l)⁻¹ * k)⁻¹) * l⁻¹) *
          (m⁻¹ * v * m)) * m⁻¹ := by rw [hcomm]
      _ = (k * w * k⁻¹) * v := by group

omit hB in
theorem A₂_le_C₂ : d.A₂ ≤ d.C₂ := fun _ ha =>
  (h.C₂_inf_H.symm ▸ (le_withT d.A₂ ha) : _ ∈ d.C₂ ⊓ d.H).1

theorem conj_V₁_mem_C₂ [Finite G] {k v : G} (hk : k ∈ d.K₂) (hv : v ∈ d.V₁) :
    k * v * k⁻¹ ∈ d.C₂ :=
  (mem_normalizer_iff.mp (h.K₂_le_normalizer_C₂ hB hk) v).mp (h.V₁_le_C₂ hv)

theorem D₂gen_subset_C₂ [Finite G] : d.D₂gen ⊆ d.C₂ := by
  rintro x (hx | ⟨k, hk, v, hv, rfl⟩)
  · exact h.A₂_le_C₂ hx
  · exact h.conj_V₁_mem_C₂ hB hk hv

theorem D₂gen_comm [Finite G] : ∀ x ∈ d.D₂gen, ∀ y ∈ d.D₂gen, x * y = y * x := by
  have hC : ∀ {a c : G}, a ∈ d.A₂ → c ∈ d.C₂ → a * c = c * a := fun ha hc =>
    (mem_centralizer_iff.mp (h.C₂_le_cent hc) _ ha)
  rintro x (hx | ⟨k, hk, v, hv, rfl⟩) y (hy | ⟨k', hk', w, hw, rfl⟩)
  · exact h.A₂_comm x hx y hy
  · exact hC hx (h.conj_V₁_mem_C₂ hB hk' hw)
  · exact (hC hy (h.conj_V₁_mem_C₂ hB hk hv)).symm
  · have e := h.comm_conj_V₁ hB (mul_mem (inv_mem hk) hk') hv hw
    calc k * v * k⁻¹ * (k' * w * k'⁻¹) = k * (v * (k⁻¹ * k' * w * (k⁻¹ * k')⁻¹)) * k⁻¹ := by
          group
      _ = k * ((k⁻¹ * k' * w * (k⁻¹ * k')⁻¹) * v) * k⁻¹ := by rw [e]
      _ = k' * w * k'⁻¹ * (k * v * k⁻¹) := by group

theorem D₂g_comm [Finite G] {x y : G} (hx : x ∈ d.D₂g) (hy : y ∈ d.D₂g) : x * y = y * x :=
  comm_of_mem_closure (h.D₂gen_comm hB) hx hy

theorem D₂g_le_C₂ [Finite G] : d.D₂g ≤ d.C₂ := closure_le _ |>.mpr (h.D₂gen_subset_C₂ hB)

omit h hB in
theorem V₁_le_D₂g : d.V₁ ≤ d.D₂g := fun v hv =>
  subset_closure (Or.inr ⟨1, one_mem _, v, hv, by group⟩)

omit h hB in
theorem A₂_le_D₂g : d.A₂ ≤ d.D₂g := fun _ ha => subset_closure (Or.inl ha)

theorem D₂g_le_D₂ [Finite G] : d.D₂g ≤ d.D₂ :=
  le_inf (h.D₂g_le_C₂ hB) fun _ hx =>
    mem_centralizer_iff.mpr fun _ hv => h.D₂g_comm hB (V₁_le_D₂g hv) hx

omit h in
theorem K₂_le_normalizer_D₂g [Finite G] : d.K₂ ≤ normalizer (d.D₂g : Set G) := by
  intro k hk
  apply mem_normalizer_of_conj_mem
  have hle : d.D₂g ≤ d.D₂g.comap (MulAut.conj k).toMonoidHom := by
    refine closure_le _ |>.mpr ?_
    rintro x (hx | ⟨k', hk', v, hv, rfl⟩)
    · exact subset_closure (Or.inl ((mem_normalizer_iff.mp (hB.K₂_le_normalizer hk) x).mp hx))
    · refine subset_closure (Or.inr ⟨k * k', mul_mem hk hk', v, hv, ?_⟩)
      change k * (k' * v * k'⁻¹) * k⁻¹ = _
      group
  exact fun x hx => hle hx

theorem card_ge_of_inv [Finite G] {E : Subgroup G} (hEC : E ≤ d.C₂) (hAE : d.A₂ ≤ E)
    (hKE : d.K₂ ≤ normalizer (E : Set G)) (hy : ∃ y ∈ E, y * d.t ≠ d.t * y) :
    2 ^ 18 ≤ Nat.card E := by
  have hEB : E ≤ centralizer (d.A₂ : Set G) := hEC.trans h.C₂_le_cent
  have hEt : ∀ y ∈ E, y⁻¹ * d.t * y * d.t ∈ d.A₂ := fun y hy => h.crossed_C₂ (hEC hy)
  set φ := crossedHom h.t_sq d.A₂ E hEB hEt with hφ
  set B : Subgroup G := φ.range.map d.A₂.subtype with hBdef
  have hBA : B ≤ d.A₂ := map_subtype_le _
  have hmemB : ∀ y ∈ E, y⁻¹ * d.t * y * d.t ∈ B := fun y hy =>
    ⟨φ ⟨y, hy⟩, ⟨⟨y, hy⟩, rfl⟩, rfl⟩
  have hBmem : ∀ b ∈ B, ∃ y ∈ E, y⁻¹ * d.t * y * d.t = b := by
    rintro _ ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨y, y.2, rfl⟩
  have hKB : d.K₂ ≤ normalizer (B : Set G) := by
    intro k hk
    apply mem_normalizer_of_conj_mem
    intro b hb
    obtain ⟨y, hyE, rfl⟩ := hBmem b hb
    rw [← crossed_conj (h.K₂_comm_t hB hk)]
    exact hmemB _ ((mem_normalizer_iff.mp (hKE hk) y).mp hyE)
  have hBtop : B = d.A₂ := by
    rcases hB.A₂_irred B hBA hKB with hb | hb
    · exfalso
      obtain ⟨y, hyE, hyt⟩ := hy
      have h1 := hmemB y hyE
      rw [hb, mem_bot, crossed_eq_one_iff h.t_sq] at h1
      exact hyt h1
    · exact hb
  have hcardB : Nat.card φ.range = 2 ^ 9 := by
    have e1 : Nat.card B = Nat.card φ.range := by
      rw [hBdef]
      exact card_map_of_injective (subtype_injective _)
    rw [← e1, hBtop, h.card_A₂]
  have hHE : d.A₂ ≤ E ⊓ centralizer ({d.t} : Set G) := le_inf hAE (h.A₂_le_L.trans h.L_le_H)
  have h1 := card_le_of_le hHE
  rw [h.card_A₂] at h1
  rw [card_eq_of_crossed h.t_sq hEB hEt, ← hφ, hcardB]
  calc 2 ^ 18 = 2 ^ 9 * 2 ^ 9 := by norm_num
    _ ≤ _ := Nat.mul_le_mul_right _ h1

omit hB in
theorem V₁_le_D₂ [Finite G] : d.V₁ ≤ d.D₂ :=
  le_inf h.V₁_le_C₂ fun _ hv => mem_centralizer_iff.mpr fun _ hw => h.V₁_comm hw hv

omit hB in
theorem A₂_le_D₂ [Finite G] : d.A₂ ≤ d.D₂ :=
  le_inf h.A₂_le_C₂ fun _ ha => mem_centralizer_iff.mpr fun _ hv =>
    (mem_centralizer_iff.mp (h.C₂_le_cent (h.V₁_le_C₂ hv)) _ ha).symm

omit hB in
theorem D₄_le_D₂ [Finite G] : d.D₄ ≤ d.D₂ :=
  le_inf h.D₄_le_C₂ fun _ hy => mem_centralizer_iff.mpr fun _ hv =>
    h.D₄_comm (V₁_le_D₄ hv) hy

omit hB in
theorem D₂_inf_H [Finite G] : d.D₂ ⊓ d.H = d.A₂ := by
  refine le_antisymm ?_ (le_inf h.A₂_le_D₂ (h.A₂_le_L.trans h.L_le_H))
  rintro x ⟨⟨hxC, hxV⟩, hxH⟩
  have hx : x ∈ d.withT d.A₂ := h.C₂_inf_H ▸ (⟨hxC, hxH⟩ : x ∈ d.C₂ ⊓ d.H)
  rcases (h.mem_withT_iff h.A₂_le_L).mp hx with hxA | hxA
  · exact hxA
  · exfalso
    apply h.t_not_cent_V₁
    have haV := (h.A₂_le_D₂ hxA).2
    have ht : d.t = x⁻¹ * (x * d.t) := by group
    rw [ht]
    exact mul_mem (inv_mem hxV) haV

omit hB in
theorem card_D₂_le [Finite G] : Nat.card d.D₂ ≤ 2 ^ 18 := by
  have hEB : d.D₂ ≤ centralizer (d.A₂ : Set G) := inf_le_left.trans h.C₂_le_cent
  have h1 := card_le_of_crossed h.t_sq hEB (fun y hy => h.crossed_C₂ hy.1)
  change Nat.card d.D₂ ≤ Nat.card (d.D₂ ⊓ d.H : Subgroup G) * Nat.card d.A₂ at h1
  rw [h.D₂_inf_H, h.card_A₂] at h1
  calc Nat.card d.D₂ ≤ 2 ^ 9 * 2 ^ 9 := h1
    _ = 2 ^ 18 := by norm_num

omit hB in
theorem exists_V₁_not_comm_t [Finite G] : ∃ y ∈ d.V₁, y * d.t ≠ d.t * y := by
  obtain ⟨v, hv, hvt⟩ := h.exists_V₁_conj
  refine ⟨v, hv, fun hc => h.z_ne_one ?_⟩
  have : v⁻¹ * d.t * v = d.t := by rw [mul_assoc, ← hc]; group
  rw [this] at hvt
  calc d.z = d.z * d.t * d.t⁻¹ := by group
    _ = 1 := by rw [← hvt]; group

theorem D₂g_eq [Finite G] : d.D₂g = d.D₂ := by
  obtain ⟨y, hy, hyt⟩ := h.exists_V₁_not_comm_t
  have h1 := h.card_ge_of_inv hB (h.D₂g_le_C₂ hB) A₂_le_D₂g (K₂_le_normalizer_D₂g hB)
    ⟨y, V₁_le_D₂g hy, hyt⟩
  exact eq_of_le_of_card_ge (h.D₂g_le_D₂ hB) (h.card_D₂_le.trans h1)

theorem card_D₂ [Finite G] : Nat.card d.D₂ = 2 ^ 18 := by
  obtain ⟨y, hy, hyt⟩ := h.exists_V₁_not_comm_t
  refine le_antisymm h.card_D₂_le ?_
  rw [← h.D₂g_eq hB]
  exact h.card_ge_of_inv hB (h.D₂g_le_C₂ hB) A₂_le_D₂g (K₂_le_normalizer_D₂g hB)
    ⟨y, V₁_le_D₂g hy, hyt⟩

theorem D₂_comm [Finite G] {x y : G} (hx : x ∈ d.D₂) (hy : y ∈ d.D₂) : x * y = y * x := by
  rw [← h.D₂g_eq hB] at hx hy
  exact h.D₂g_comm hB hx hy

theorem K₂_le_normalizer_D₂ [Finite G] : d.K₂ ≤ normalizer (d.D₂ : Set G) := by
  rw [← h.D₂g_eq hB]
  exact K₂_le_normalizer_D₂g hB

theorem D₂_irred [Finite G] {E : Subgroup G} (hAE : d.A₂ ≤ E) (hED : E ≤ d.D₂)
    (hKE : d.K₂ ≤ normalizer (E : Set G)) : E = d.A₂ ∨ E = d.D₂ := by
  by_cases hy : ∃ y ∈ E, y * d.t ≠ d.t * y
  · right
    have h1 := h.card_ge_of_inv hB (hED.trans inf_le_left) hAE hKE hy
    exact eq_of_le_of_card_ge hED (by rw [h.card_D₂ hB]; exact h1)
  · left
    push Not at hy
    refine le_antisymm (fun x hx => ?_) hAE
    rw [← h.D₂_inf_H]
    exact ⟨hED hx, mem_centralizer_singleton_iff.mpr (hy x hx)⟩

theorem D₂_sq [Finite G] (hV : ∀ v ∈ d.V₁, v * v = 1) {x : G} (hx : x ∈ d.D₂) : x * x = 1 := by
  let Ω : Subgroup G :=
    { carrier := {y | y ∈ d.D₂ ∧ y * y = 1}
      one_mem' := ⟨one_mem _, mul_one 1⟩
      mul_mem' := by
        rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
        refine ⟨mul_mem ha hb, ?_⟩
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [h.D₂_comm hB hb ha]
          _ = (a * a) * (b * b) := by group
          _ = 1 := by rw [ha2, hb2, one_mul]
      inv_mem' := by
        rintro a ⟨ha, ha2⟩
        refine ⟨inv_mem ha, ?_⟩
        rw [← mul_inv_rev, ha2, inv_one] }
  have hΩD : Ω ≤ d.D₂ := fun _ hy => hy.1
  have hAΩ : d.A₂ ≤ Ω := fun a ha => ⟨h.A₂_le_D₂ ha, h.A₂_sq a ha⟩
  have hKΩ : d.K₂ ≤ normalizer (Ω : Set G) := by
    intro k hk
    apply mem_normalizer_of_conj_mem
    rintro y ⟨hy, hy2⟩
    refine ⟨(mem_normalizer_iff.mp (h.K₂_le_normalizer_D₂ hB hk) y).mp hy, ?_⟩
    calc k * y * k⁻¹ * (k * y * k⁻¹) = k * (y * y) * k⁻¹ := by group
      _ = 1 := by rw [hy2]; group
  obtain ⟨v, hv, hvt⟩ := h.exists_V₁_not_comm_t
  rcases h.D₂_irred hB hAΩ hΩD hKΩ with hΩ | hΩ
  · exfalso
    have hvΩ : v ∈ Ω := ⟨h.V₁_le_D₂ hv, hV v hv⟩
    rw [hΩ] at hvΩ
    exact hvt (mem_centralizer_singleton_iff.mp (h.A₂_le_L.trans h.L_le_H hvΩ))
  · rw [← hΩ] at hx
    exact hx.2

omit hB in
theorem t_mem_normalizer_D₂ [Finite G] : d.t ∈ normalizer (d.D₂ : Set G) := by
  have htC : d.t ∈ d.C₂ := by
    have := t_mem_withT (d := d) d.A₂
    rw [← h.C₂_inf_H] at this
    exact this.1
  apply mem_normalizer_of_conj_mem
  intro y hy
  obtain ⟨hyC, hyV⟩ := mem_inf.mp hy
  exact mem_inf.mpr ⟨mul_mem (mul_mem htC hyC) (inv_mem htC),
    conj_mem_centralizer h.t_mem_normalizer_V₁ hyV⟩

end Hyp

end CFSG.EvenSmallLie.UnitarySix.YamadaD
