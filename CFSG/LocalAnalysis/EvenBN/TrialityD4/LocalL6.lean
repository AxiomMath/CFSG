module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL6Prelim
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Nine
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Ten

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section LFour

theorem yamadaL₃_le_yamadaL₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₃ d t ≤ yamadaL₄ d t := fun x hx => by
  have hy := h.l6Hyps d hlay
  exact mem_inf.2 ⟨(h.yamada_5_14 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593).2.2.2.2.1.1
    (h.yamadaL₃_le_yamadaR₃_D3 d hlay hx), h.yamadaL₃_le_centralizer_Y d hy.h592 hy.h520 hx⟩

theorem yamadaL₃_le_map_conj_yamadaL₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₃ d t ≤ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom := fun x hx => by
  rw [mem_map_conj_iff_D4]
  apply h.yamadaL₃_le_yamadaL₄ d hlay
  have := (mem_normalizer_iff.1 (inv_mem (h.v_mem_normalizer_yamadaL₃ d)) x).1 hx
  rwa [inv_inv] at this

theorem yamadaL₄_le_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₄ d t ≤ yamadaT₆ d t := fun x hx => by
  have hy := h.l6Hyps d hlay
  have hxR₄ : x ∈ yamadaR₄ d t := (mem_inf.1 hx).1
  have hxY : x ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := (mem_inf.1 hx).2
  have hxY₂ := h.yamadaR₄_le_normalizer_yamadaY₂_L6 d hlay hxR₄
  have hxL₃ := h.yamadaR₄_le_normalizer_yamadaL₃ d hlay hxR₄
  have hxR₅ : x ∈ yamadaR₅ d t := (mem_inf.1 hxR₄).1
  refine mem_yamadaT₆_of hxL₃ (h.yamadaR₄_le_normalizer_yamadaM₃ d hlay hxR₄)
    (h.normalizer_yamadaL₃_le_normalizer_yamadaW₂ d hlay hxL₃) hxY₂ (fun w hw => ?_) hxY
  have hw' : w ∈ ((d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hw
  rw [coe_mul_of_right_le_normalizer_left _ _ (yamadaY₂_le_normalizer_W d hy.h592),
    Set.mem_mul] at hw'
  obtain ⟨_, ⟨a, ha, rfl⟩, y', hy', rfl⟩ := hw'
  have haW₁ : L.subtype a ∈ yamadaW₁ d t := mem_sup_left ⟨a, ha, rfl⟩
  have h1 := h.commutatorElement_mem_yamadaY₁ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
    haW₁ hxR₅
  have h1' : x * L.subtype a * x⁻¹ * (L.subtype a)⁻¹ ∈ yamadaY₂ d t := by
    have := inv_mem h1
    rw [show (L.subtype a * x * (L.subtype a)⁻¹ * x⁻¹)⁻¹ =
      x * L.subtype a * x⁻¹ * (L.subtype a)⁻¹ by group] at this
    exact (sup_le (Y_le_yamadaY₂ d hy.h592) (le_sup_left : yamadaV₁ d t ≤ yamadaY₂ d t) :
      yamadaY₁ d t ≤ yamadaY₂ d t) this
  have haY₂ : L.subtype a ∈ normalizer (yamadaY₂ d t : Set G) :=
    h.S_map_le_normalizer_yamadaY₂ d hlay ⟨a, d.W_le_S ha, rfl⟩
  have h2 : x * y' * x⁻¹ * y'⁻¹ ∈ yamadaY₂ d t :=
    mul_mem ((mem_normalizer_iff.1 hxY₂ y').1 hy') (inv_mem hy')
  have h3 : L.subtype a * (x * y' * x⁻¹ * y'⁻¹) * (L.subtype a)⁻¹ ∈ yamadaY₂ d t :=
    (mem_normalizer_iff.1 haY₂ _).1 h2
  have e : x * (L.subtype a * y') * x⁻¹ * (L.subtype a * y')⁻¹ =
      (x * L.subtype a * x⁻¹ * (L.subtype a)⁻¹) *
        (L.subtype a * (x * y' * x⁻¹ * y'⁻¹) * (L.subtype a)⁻¹) := by group
  rw [e]
  exact mul_mem h1' h3

theorem map_conj_yamadaL₄_le_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ≤ yamadaT₆ d t := by
  rintro _ ⟨x, hx, rfl⟩
  exact h.v_conj_mem_yamadaT₆ d hlay (h.yamadaL₄_le_yamadaT₆ d hlay hx)

end LFour

section Stabilizer

theorem yamadaT₆_inf_normalizer_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaT₆ d t ⊓ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaL₃ d t := by
  intro g hg
  obtain ⟨hgT, hgK⟩ := mem_inf.1 hg
  have hy := h.l6Hyps d hlay
  rw [h.yamada_5_22_2 d hlay, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _
      (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ d), Set.mem_mul] at hgK
  obtain ⟨l, hl, c, hc, rfl⟩ := hgK
  have hcT : c ∈ yamadaT₆ d t := by
    have := mul_mem (inv_mem (h.yamadaL₃_le_yamadaT₆ d hlay hl)) hgT
    rwa [inv_mul_cancel_left] at this
  have hcN : c ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    h.centralizer_inf_normalizer_Y_le d hc
  have hcE : c ∈ centralizerW₂Y₂ d t :=
    (h.mem_centralizerW₂Y₂_iff d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
      hy.h5102).2 ⟨h.normalizer_tY_le_normalizer_yamadaV₂ d hy.h591 hy.h592 hcN,
        fun w hw => commutator_mem_yamadaY₂_of_mem_yamadaT₆ hcT hw⟩
  have hc' := h.kernelTW₂_le d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102
    (mem_inf.2 ⟨hcE, hcN⟩)
  have hBK := h.leviLong_le_kernelTW₂ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
    hy.h5102
  have hBL₂ : d.leviLong.map L.subtype ≤ normalizer (yamadaL₂ d t : Set G) := fun b hb =>
    le_normalizer_yamadaL₂ d t (mem_inf.1 (hBK hb)).2
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hBL₂, Set.mem_mul] at hc'
  obtain ⟨l₂, hl₂, b, hb, rfl⟩ := hc'
  have hl₂L₃ : l₂ ∈ yamadaL₃ d t :=
    h.yamadaL₂_le_yamadaL₃ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102 hl₂
  have hl₂Y := h.yamadaL₃_le_centralizer_Y d hy.h592 hy.h520 hl₂L₃
  have hbY : b ∈ centralizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    have := mul_mem (inv_mem hl₂Y) (yamadaT₆_le_centralizer_Y d t hcT)
    rwa [inv_mul_cancel_left] at this
  obtain ⟨b₀, hb₀, rfl⟩ := hb
  have hb1 : b₀ = 1 := d.eq_one_of_mem_leviLong_of_conj_yv hb₀ fun w => by
    have hcomm : d.yv w * b₀ = b₀ * d.yv w :=
      Subtype.ext (mem_centralizer_iff.1 hbY _ ⟨d.yv w, d.yv_mem_Y w, rfl⟩)
    rw [← hcomm, mul_inv_cancel_right]
  rw [hb1, map_one, mul_one]
  exact mul_mem hl hl₂L₃

end Stabilizer

section Orbits

theorem exists_mem_yamadaL₄_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {a : G} (ha : a ∈ yamadaF₃ d t) :
    ∃ x ∈ yamadaL₄ d t, ∃ w ∈ yamadaW₃ d t, x * t * x⁻¹ = t * a * w := by
  have hy := h.l6Hyps d hlay
  have h514 := h.yamada_5_14 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
  have hW₁W₃ : yamadaW₁ d t ≤ yamadaW₃ d t :=
    sup_le (h.W_map_le_yamadaW₃_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
      hy.h5102) (h.yamadaV₁_le_yamadaW₃_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
        hy.h5101 hy.h5102)
  have hD₁N : yamadaD₁ d t ≤ normalizer (yamadaW₃ d t : Set G) := fun x hx =>
    (h.yamadaD₅_le_normalizer_yamadaW₃ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
      hy.h5102 hy.h59e hy.h520 hy.h5221 hy.h521).1 (by
        have hx₃ := h.yamadaD₁_le_yamadaD₃_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hx
        exact mem_inf.2 ⟨(mem_inf.1 hx₃).2, (mem_inf.1 (mem_inf.1 hx₃).1).2⟩)
  have hD₃ : a ∈ yamadaD₃ d t := (mem_inf.1 ha).2
  rw [h.yamadaD₃_eq_sup_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101 hy.h5102
    hy.h521, ← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hD₁N,
    Set.mem_mul] at hD₃
  obtain ⟨w₀, hw₀, d₀, hd₀, rfl⟩ := hD₃
  have hF₃ : d₀ ∈ yamadaF₃ d t := by
    have := mul_mem (inv_mem (h.yamadaW₃_le_yamadaF₃ d hlay hw₀)) ha
    rwa [inv_mul_cancel_left] at this
  have hd₀N : d₀ ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (mem_inf.1 (mem_inf.1 hF₃).1).1
  have hF₁ : d₀ ∈ yamadaF₁ d t :=
    h.yamadaF₃_inf_yamadaD₁_le_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
      hy.h5102 (mem_inf.2 ⟨hF₃, hd₀⟩)
  obtain ⟨x, hx, v₁, hv₁, ex⟩ := h514.2.1.2 d₀ hF₁
  have hxsup : x ∈ yamadaR₃ d t ⊔ yamadaL₄ d t := by
    rw [← h.yamadaR₄_eq_sup d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h59e]
    exact hx
  have hL₄R₃ : yamadaL₄ d t ≤ normalizer (yamadaR₃ d t : Set G) := fun g hg =>
    h514.2.2.2.2.1.2 (mem_inf.1 hg).1
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hL₄R₃, Set.mem_mul] at hxsup
  obtain ⟨r, hr, l, hl, rfl⟩ := hxsup
  obtain ⟨w₁, hw₁, er⟩ := h514.1.1 r hr
  obtain ⟨f₁, hf₁, el⟩ := h514.2.1.1 l (mem_inf.1 hl).1
  have hrR₅ : r ∈ yamadaR₅ d t := (mem_inf.1 hr).1
  have hw₂ := h.commutatorElement_mem_yamadaW₁ d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
    (inv_mem hf₁) hrR₅
  rw [inv_inv] at hw₂
  obtain ⟨w₂, hw₂def⟩ : ∃ w₂, w₂ = f₁⁻¹ * r * f₁ * r⁻¹ := ⟨_, rfl⟩
  rw [← hw₂def] at hw₂
  have e3 : r * f₁ * r⁻¹ = f₁ * w₂ := by rw [hw₂def]; group
  have e4 : r * l * t * (r * l)⁻¹ = t * w₁ * (f₁ * w₂) := by
    calc r * l * t * (r * l)⁻¹ = r * (l * t * l⁻¹) * r⁻¹ := by group
      _ = r * (t * f₁) * r⁻¹ := by rw [el]
      _ = (r * t * r⁻¹) * (r * f₁ * r⁻¹) := by group
      _ = t * w₁ * (f₁ * w₂) := by rw [er, e3]
  rw [e4] at ex
  have h1 : w₁ * (f₁ * w₂) = d₀ * v₁ :=
    mul_left_cancel (a := t) (by simpa only [mul_assoc] using ex)
  have hf₁eq : f₁ = w₁⁻¹ * (d₀ * v₁) * w₂⁻¹ := by
    calc f₁ = w₁⁻¹ * (w₁ * (f₁ * w₂)) * w₂⁻¹ := by group
      _ = w₁⁻¹ * (d₀ * v₁) * w₂⁻¹ := by rw [h1]
  refine ⟨l, hl, d₀⁻¹ * (w₀⁻¹ * w₁⁻¹) * d₀ * v₁ * w₂⁻¹, ?_, ?_⟩
  · have h2 : d₀⁻¹ * (w₀⁻¹ * w₁⁻¹) * d₀ ∈ yamadaW₃ d t := by
      have := (mem_normalizer_iff.1 (inv_mem hd₀N) _).1
        (mul_mem (inv_mem hw₀) (inv_mem (hW₁W₃ hw₁)))
      rwa [inv_inv] at this
    exact mul_mem (mul_mem h2 (h.yamadaV₁_le_yamadaW₃_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592
      hy.h593 hy.h5101 hy.h5102 hv₁)) (inv_mem (hW₁W₃ hw₂))
  · rw [el, hf₁eq]
    group

theorem exists_mem_map_conj_yamadaL₄_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {b : G}
    (hb : b ∈ (yamadaF₃ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom) :
    ∃ y ∈ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom, ∃ w ∈ yamadaW₃ d t,
      y * t * y⁻¹ = t * b * w := by
  rw [mem_map_conj_iff_D4] at hb
  obtain ⟨x, hx, w, hw, e⟩ := h.exists_mem_yamadaL₄_conj_eq d hlay hb
  have hvt := h.v_mul_t d
  have hvt' : ((d.v : L) : G) * t * ((d.v : L) : G)⁻¹ = t := by rw [hvt, mul_inv_cancel_right]
  have hvt'' : ((d.v : L) : G)⁻¹ * t * ((d.v : L) : G) = t := by
    rw [mul_assoc, ← hvt, inv_mul_cancel_left]
  refine ⟨((d.v : L) : G) * x * ((d.v : L) : G)⁻¹, ⟨x, hx, rfl⟩,
    ((d.v : L) : G) * w * ((d.v : L) : G)⁻¹,
    (mem_normalizer_iff.1 (h.v_mem_normalizer_yamadaW₃ d) w).1 hw, ?_⟩
  calc ((d.v : L) : G) * x * ((d.v : L) : G)⁻¹ * t * (((d.v : L) : G) * x * ((d.v : L) : G)⁻¹)⁻¹
      = ((d.v : L) : G) * (x * (((d.v : L) : G)⁻¹ * t * ((d.v : L) : G)) * x⁻¹) *
        ((d.v : L) : G)⁻¹ := by group
    _ = ((d.v : L) : G) * (x * t * x⁻¹) * ((d.v : L) : G)⁻¹ := by rw [hvt'']
    _ = ((d.v : L) : G) * (t * (((d.v : L) : G)⁻¹ * b * ((d.v : L) : G)) * w) *
        ((d.v : L) : G)⁻¹ := by rw [e]
    _ = (((d.v : L) : G) * t * ((d.v : L) : G)⁻¹) * b *
        (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) := by group
    _ = t * b * (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) := by rw [hvt']

theorem exists_mul_conj_eq_of_mem_yamadaM₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {m : G} (hm : m ∈ yamadaM₃ d t) :
    ∃ x ∈ yamadaL₄ d t, ∃ y ∈ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom,
      ∃ w ∈ yamadaW₃ d t, x * y * t * (x * y)⁻¹ = t * m * w := by
  rw [← SetLike.mem_coe, h.coe_yamadaM₃_eq_mul d hlay, Set.mem_mul] at hm
  obtain ⟨a, ha, b, hb, rfl⟩ := hm
  obtain ⟨x, hx, w₁, hw₁, ex⟩ := h.exists_mem_yamadaL₄_conj_eq d hlay ha
  obtain ⟨y, hy, w₂, hw₂, ey⟩ := h.exists_mem_map_conj_yamadaL₄_conj_eq d hlay hb
  have hxT := h.yamadaL₄_le_yamadaT₆ d hlay hx
  have hbM₃ : b ∈ yamadaM₃ d t := h.map_conj_yamadaF₃_le_yamadaM₃ d hlay hb
  have hw₀ := h.commutator_mem_yamadaW₃_of_mem_yamadaT₆ d hlay hxT hbM₃
  have hxW₃ : x ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay (yamadaT₆_le_normalizer_yamadaL₃ d t hxT)
  have hbW₃ : b ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay (mem_inf.1 hbM₃).1
  refine ⟨x, hx, y, hy, b⁻¹ * (w₁ * (x * b * x⁻¹ * b⁻¹)) * b * (x * w₂ * x⁻¹), ?_, ?_⟩
  · refine mul_mem ?_ ((mem_normalizer_iff.1 hxW₃ w₂).1 hw₂)
    have := (mem_normalizer_iff.1 (inv_mem hbW₃) _).1 (mul_mem hw₁ hw₀)
    rwa [inv_inv] at this
  · calc x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
      _ = x * (t * b * w₂) * x⁻¹ := by rw [ey]
      _ = (x * t * x⁻¹) * (x * b * x⁻¹) * (x * w₂ * x⁻¹) := by group
      _ = (t * a * w₁) * (x * b * x⁻¹) * (x * w₂ * x⁻¹) := by rw [ex]
      _ = t * (a * b) * (b⁻¹ * (w₁ * (x * b * x⁻¹ * b⁻¹)) * b * (x * w₂ * x⁻¹)) := by group

end Orbits

section Frattini

theorem isPGroup_yamadaL₃ {q : ℕ} (d : TrialityD4Data L q) (t : G) :
    IsPGroup 2 (yamadaL₃ d t) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem exists_mul_mem_normalizer_tW₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {g : G}
    (hg : g ∈ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G)) :
    ∃ x ∈ yamadaL₄ d t, ∃ y ∈ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom,
      (x * y)⁻¹ * g ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) := by
  obtain ⟨m, hm, eg⟩ := h.exists_conj_t_eq_mul_of_mem d hlay hg
  obtain ⟨x, hx, y, hy, w, hw, ez⟩ := h.exists_mul_conj_eq_of_mem_yamadaM₃ d hlay hm
  refine ⟨x, hx, y, hy, ?_⟩
  have hzT : x * y ∈ yamadaT₆ d t :=
    mul_mem (h.yamadaL₄_le_yamadaT₆ d hlay hx) (h.map_conj_yamadaL₄_le_yamadaT₆ d hlay hy)
  have hzW₃ : x * y ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay (yamadaT₆_le_normalizer_yamadaL₃ d t hzT)
  have hgW₃ : g ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay hg.1
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay htL₃
  refine h.mem_normalizer_sup_zpowers_D3 htW₃ (mul_mem (inv_mem hzW₃) hgW₃) ?_
  have ht' : t * m = (x * y) * t * (x * y)⁻¹ * w⁻¹ := by rw [ez]; group
  have e1 : (x * y)⁻¹ * g * t * ((x * y)⁻¹ * g)⁻¹ = t * ((x * y)⁻¹ * w⁻¹ * (x * y)) := by
    calc (x * y)⁻¹ * g * t * ((x * y)⁻¹ * g)⁻¹ = (x * y)⁻¹ * (g * t * g⁻¹) * (x * y) := by group
      _ = (x * y)⁻¹ * (t * m) * (x * y) := by rw [eg]
      _ = (x * y)⁻¹ * ((x * y) * t * (x * y)⁻¹ * w⁻¹) * (x * y) := by rw [← ht']
      _ = t * ((x * y)⁻¹ * w⁻¹ * (x * y)) := by group
  rw [e1]
  refine mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left ?_)
  have := (mem_normalizer_iff.1 (inv_mem hzW₃) w⁻¹).1 (inv_mem hw)
  rwa [inv_inv] at this

theorem exists_mem_yamadaT₆_mul_eq_of_mem_normalizer (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {g : G}
    (hg : g ∈ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G)) :
    ∃ z ∈ yamadaT₆ d t, ∃ c ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G), g = z * c := by
  obtain ⟨x, hx, y, hy, hc⟩ := h.exists_mul_mem_normalizer_tW₃ d hlay hg
  have hzT : x * y ∈ yamadaT₆ d t :=
    mul_mem (h.yamadaL₄_le_yamadaT₆ d hlay hx) (h.map_conj_yamadaL₄_le_yamadaT₆ d hlay hy)
  rw [h.yamada_5_22_2 d hlay, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _
      (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ d), Set.mem_mul] at hc
  obtain ⟨l, hl, c, hc', hlc⟩ := hc
  refine ⟨x * y * l, mul_mem hzT (h.yamadaL₃_le_yamadaT₆ d hlay hl), c, hc', ?_⟩
  calc g = (x * y) * ((x * y)⁻¹ * g) := (mul_inv_cancel_left _ _).symm
    _ = (x * y) * (l * c) := by rw [hlc]
    _ = x * y * l * c := (mul_assoc _ _ _).symm

theorem mul_self_mem_yamadaL₃_of_mem_yamadaT₆ (h : Setup G L f t)
    (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) {g : G} (hg : g ∈ yamadaT₆ d t) :
    g * g ∈ yamadaL₃ d t := by
  have hgH : g ∈ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) :=
    ⟨yamadaT₆_le_normalizer_yamadaL₃ d t hg, yamadaT₆_le_normalizer_yamadaM₃ d t hg⟩
  obtain ⟨m, hm, eg⟩ := h.exists_conj_t_eq_mul_of_mem d hlay hgH
  have hmL₃ : m ∈ yamadaL₃ d t := (mem_inf.1 hm).1
  have hmW₃ : m ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay hmL₃
  have hgW₃ : g ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay hgH.1
  have hw₀ := h.commutator_mem_yamadaW₃_of_mem_yamadaT₆ d hlay hg hm
  have hmm : m * m ∈ yamadaW₃ d t :=
    h.yamadaW₂_le_yamadaW₃ d hlay (h.mul_self_mem_yamadaW₂_of_mem_yamadaL₃ d hlay hmL₃)
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have htW₃ : t ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.yamadaL₃_le_normalizer_yamadaW₃ d hlay htL₃
  have hggT : g * g ∈ yamadaT₆ d t := mul_mem hg hg
  have e1 : g * g * t * (g * g)⁻¹ = t * (m * m * (m⁻¹ * (g * m * g⁻¹ * m⁻¹) * m)) := by
    calc g * g * t * (g * g)⁻¹ = g * (g * t * g⁻¹) * g⁻¹ := by group
      _ = g * (t * m) * g⁻¹ := by rw [eg]
      _ = (g * t * g⁻¹) * (g * m * g⁻¹) := by group
      _ = t * m * ((g * m * g⁻¹ * m⁻¹) * m) := by rw [eg]; group
      _ = t * (m * m * (m⁻¹ * (g * m * g⁻¹ * m⁻¹) * m)) := by group
  have hggK : g * g ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    refine h.mem_normalizer_sup_zpowers_D3 htW₃ (mul_mem hgW₃ hgW₃) ?_
    rw [e1]
    refine mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left (mul_mem hmm ?_))
    have := (mem_normalizer_iff.1 (inv_mem hmW₃) _).1 hw₀
    rwa [inv_inv] at this
  exact h.yamadaT₆_inf_normalizer_le d hlay ⟨hggT, hggK⟩

theorem isPGroup_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : IsPGroup 2 (yamadaT₆ d t) := by
  intro g
  obtain ⟨n, hn⟩ := isPGroup_yamadaL₃ d t
    ⟨(g : G) * g, h.mul_self_mem_yamadaL₃_of_mem_yamadaT₆ d hlay g.2⟩
  refine ⟨n + 1, Subtype.ext ?_⟩
  have hn' := congrArg Subtype.val hn
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at hn' ⊢
  rw [pow_succ', pow_mul, sq]
  exact hn'

theorem yamadaT₆_le_yamadaL₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaT₆ d t ≤ yamadaL₆ d t := by
  have hTH : yamadaT₆ d t ≤ normalizer (yamadaL₃ d t : Set G) ⊓
      normalizer (yamadaM₃ d t : Set G) :=
    le_inf (yamadaT₆_le_normalizer_yamadaL₃ d t) (yamadaT₆_le_normalizer_yamadaM₃ d t)
  have hHT : normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) ≤
      normalizer (yamadaT₆ d t : Set G) := fun g hg => by
    obtain ⟨z, hz, c, hc, rfl⟩ := h.exists_mem_yamadaT₆_mul_eq_of_mem_normalizer d hlay hg
    refine mem_normalizer_fintype fun y hy => ?_
    have h1 := h.conj_mem_yamadaT₆ d hlay hc hy
    have := mul_mem (mul_mem hz h1) (inv_mem hz)
    rwa [show z * (c * y * c⁻¹) * z⁻¹ = z * c * y * (z * c)⁻¹ by group] at this
  exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hTH hHT (h.isPGroup_yamadaT₆ d hlay)

end Frattini

section Six

theorem yamadaL₃_le_H (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    yamadaL₃ d t ≤ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) :=
  fun g hg => ⟨le_normalizer hg, h.yamadaL₃_le_normalizer_yamadaM₃ d hlay hg⟩

theorem centralizer_inf_normalizer_Y_le_H (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) := fun g hg =>
  ⟨h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ d hg,
    h.centralizer_inf_normalizer_Y_le_normalizer_yamadaM₃ d hlay hg⟩

theorem yamadaL₃_le_yamadaL₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₃ d t ≤ yamadaL₆ d t :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (h.yamadaL₃_le_H d hlay)
    (fun _ hg => hg.1) (isPGroup_yamadaL₃ d t)

theorem yamadaL₆_inf_normalizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₆ d t ⊓ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) =
      yamadaL₃ d t := by
  have hy := h.l6Hyps d hlay
  have hN₂H : normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G) ⊓
      normalizer (yamadaM₃ d t : Set G) := by
    rw [h.normalizer_yamadaL₂_eq_sup d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593 hy.h5101
      hy.h5102]
    exact sup_le (h.yamadaL₃_le_H d hlay) (h.centralizer_inf_normalizer_Y_le_H d hlay)
  have hKN₂ : normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaL₂ d t : Set G) := by
    rw [h.yamada_5_22_2 d hlay]
    exact sup_le (yamadaL₃_le_normalizer_yamadaL₂ d) fun g hg =>
      le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d hg)
  refine le_antisymm ?_ (le_inf (h.yamadaL₃_le_yamadaL₆ d hlay) ?_)
  · rintro x ⟨hxL₆, hxK⟩
    have hp : IsPGroup 2 (yamadaL₆ d t ⊓ normalizer (yamadaL₂ d t : Set G) : Subgroup G) :=
      (isPGroup_yamadaL₆ d t).to_le inf_le_left
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right
      (fun g hg => Common.mem_normalizer_inf (le_normalizer_yamadaL₆ d t (hN₂H hg))
        (le_normalizer hg)) hp ⟨hxL₆, hKN₂ hxK⟩
  · rw [h.yamada_5_22_2 d hlay]
    exact le_sup_left

theorem yamadaL₆_le_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₆ d t ≤ yamadaT₆ d t := fun x hx => by
  obtain ⟨x₀, hx₀, y₀, hy₀, hc⟩ := h.exists_mul_mem_normalizer_tW₃ d hlay (yamadaL₆_le d t hx)
  have hzT : x₀ * y₀ ∈ yamadaT₆ d t :=
    mul_mem (h.yamadaL₄_le_yamadaT₆ d hlay hx₀) (h.map_conj_yamadaL₄_le_yamadaT₆ d hlay hy₀)
  have hc₆ : (x₀ * y₀)⁻¹ * x ∈ yamadaL₆ d t :=
    mul_mem (inv_mem (h.yamadaT₆_le_yamadaL₆ d hlay hzT)) hx
  have hc' : (x₀ * y₀)⁻¹ * x ∈ yamadaL₃ d t := by
    rw [← h.yamadaL₆_inf_normalizer d hlay]
    exact mem_inf.2 ⟨hc₆, hc⟩
  have := mul_mem hzT (h.yamadaL₃_le_yamadaT₆ d hlay hc')
  rwa [mul_inv_cancel_left] at this

theorem yamadaL₆_eq_yamadaT₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : yamadaL₆ d t = yamadaT₆ d t :=
  le_antisymm (h.yamadaL₆_le_yamadaT₆ d hlay) (h.yamadaT₆_le_yamadaL₆ d hlay)

end Six

section Main

theorem exists_conj_t_eq_mul_of_mem_yamadaL₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {z : G} (hz : z ∈ yamadaL₄ d t) :
    ∃ a ∈ yamadaF₃ d t, z * t * z⁻¹ = t * a := by
  have hy := h.l6Hyps d hlay
  have hzH : z ∈ normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) :=
    ⟨h.yamadaR₄_le_normalizer_yamadaL₃ d hlay (mem_inf.1 hz).1,
      h.yamadaR₄_le_normalizer_yamadaM₃ d hlay (mem_inf.1 hz).1⟩
  obtain ⟨m, hm, e⟩ := h.exists_conj_t_eq_mul_of_mem d hlay hzH
  obtain ⟨f₁, hf₁, e'⟩ := (h.yamada_5_14 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592
    hy.h593).2.1.1 z (mem_inf.1 hz).1
  have hmf : m = f₁ := mul_left_cancel (e.symm.trans e')
  refine ⟨m, mem_inf.2 ⟨hm, ?_⟩, e⟩
  exact h.yamadaD₁_le_yamadaD₃_C9 d hy.hNH hy.h561 hy.h562 hy.h591 hy.h592 hy.h593
    (yamadaF₁_le_yamadaD₁ d (by rw [hmf]; exact hf₁))

theorem yamadaL₄_inf_map_conj_yamadaL₄ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₄ d t ⊓ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom =
      yamadaL₃ d t := by
  have hy := h.l6Hyps d hlay
  have hvt := h.v_mul_t d
  have hvt' : ((d.v : L) : G) * t * ((d.v : L) : G)⁻¹ = t := by rw [hvt, mul_inv_cancel_right]
  refine le_antisymm (fun z hz => ?_) (le_inf (h.yamadaL₃_le_yamadaL₄ d hlay)
    (h.yamadaL₃_le_map_conj_yamadaL₄ d hlay))
  obtain ⟨hz₁, hz₂⟩ := mem_inf.1 hz
  obtain ⟨a, ha, ea⟩ := h.exists_conj_t_eq_mul_of_mem_yamadaL₄ d hlay hz₁
  rw [mem_map_conj_iff_D4] at hz₂
  obtain ⟨b, hb, eb⟩ := h.exists_conj_t_eq_mul_of_mem_yamadaL₄ d hlay hz₂
  have hab : a = ((d.v : L) : G) * b * ((d.v : L) : G)⁻¹ := by
    have e1 : z * t * z⁻¹ = t * (((d.v : L) : G) * b * ((d.v : L) : G)⁻¹) := by
      calc z * t * z⁻¹ = z * (((d.v : L) : G) * t * ((d.v : L) : G)⁻¹) * z⁻¹ := by rw [hvt']
        _ = ((d.v : L) : G) * (((d.v : L) : G)⁻¹ * z * ((d.v : L) : G) * t *
            (((d.v : L) : G)⁻¹ * z * ((d.v : L) : G))⁻¹) * ((d.v : L) : G)⁻¹ := by group
        _ = ((d.v : L) : G) * (t * b) * ((d.v : L) : G)⁻¹ := by rw [eb]
        _ = (((d.v : L) : G) * t * ((d.v : L) : G)⁻¹) *
            (((d.v : L) : G) * b * ((d.v : L) : G)⁻¹) := by group
        _ = t * (((d.v : L) : G) * b * ((d.v : L) : G)⁻¹) := by rw [hvt']
    exact mul_left_cancel (ea.symm.trans e1)
  have haW₃ : a ∈ yamadaW₃ d t := by
    rw [hy.h521.1]
    exact mem_inf.2 ⟨ha, by rw [hab]; exact ⟨b, hb, rfl⟩⟩
  have hzT := h.yamadaL₄_le_yamadaT₆ d hlay hz₁
  have hzW₃ : z ∈ normalizer (yamadaW₃ d t : Set G) :=
    h.normalizer_yamadaL₃_le_normalizer_yamadaW₃ d hlay (yamadaT₆_le_normalizer_yamadaL₃ d t hzT)
  have htL₃ : t ∈ yamadaL₃ d t := by
    rw [h.yamadaL₃_eq_sup d hlay]
    exact mem_sup_right (mem_zpowers t)
  have hzK : z ∈ normalizer ((yamadaW₃ d t ⊔ zpowers t : Subgroup G) : Set G) := by
    refine h.mem_normalizer_sup_zpowers_D3 (h.yamadaL₃_le_normalizer_yamadaW₃ d hlay htL₃) hzW₃ ?_
    rw [ea]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left haW₃)
  exact h.yamadaT₆_inf_normalizer_le d hlay ⟨hzT, hzK⟩

theorem conj_t_mem_of_mem_yamadaL₆ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G} (hx : x ∈ yamadaL₆ d t) :
    ∃ m ∈ yamadaM₃ d t, x * t * x⁻¹ = t * m :=
  h.exists_conj_t_eq_mul_of_mem d hlay (yamadaL₆_le d t hx)

theorem exists_mem_yamadaL₆_conj_eq (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {m : G} (hm : m ∈ yamadaM₃ d t) :
    ∃ x ∈ yamadaL₆ d t, ∃ w ∈ yamadaW₃ d t, x * t * x⁻¹ = t * m * w := by
  obtain ⟨x, hx, y, hy, w, hw, e⟩ := h.exists_mul_conj_eq_of_mem_yamadaM₃ d hlay hm
  exact ⟨x * y, h.yamadaT₆_le_yamadaL₆ d hlay (mul_mem (h.yamadaL₄_le_yamadaT₆ d hlay hx)
    (h.map_conj_yamadaL₄_le_yamadaT₆ d hlay hy)), w, hw, e⟩

theorem yamada_5_27_1 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    normalizer (yamadaL₃ d t : Set G) ⊓ normalizer (yamadaM₃ d t : Set G) =
        yamadaL₆ d t ⊔ (centralizer ({t} : Set G) ⊓
          normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) ∧
      yamadaL₆ d t =
        yamadaL₄ d t ⊔ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom ∧
      yamadaL₄ d t ⊓ (yamadaL₄ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom =
        yamadaL₃ d t := by
  refine ⟨le_antisymm (fun g hg => ?_) (sup_le (yamadaL₆_le d t)
    (h.centralizer_inf_normalizer_Y_le_H d hlay)), le_antisymm (fun x hx => ?_) ?_,
    h.yamadaL₄_inf_map_conj_yamadaL₄ d hlay⟩
  · obtain ⟨z, hz, c, hc, rfl⟩ := h.exists_mem_yamadaT₆_mul_eq_of_mem_normalizer d hlay hg
    exact mul_mem (mem_sup_left (h.yamadaT₆_le_yamadaL₆ d hlay hz)) (mem_sup_right hc)
  · obtain ⟨x₀, hx₀, y₀, hy₀, hc⟩ := h.exists_mul_mem_normalizer_tW₃ d hlay (yamadaL₆_le d t hx)
    have hzL₆ : x₀ * y₀ ∈ yamadaL₆ d t :=
      h.yamadaT₆_le_yamadaL₆ d hlay (mul_mem (h.yamadaL₄_le_yamadaT₆ d hlay hx₀)
        (h.map_conj_yamadaL₄_le_yamadaT₆ d hlay hy₀))
    have hc₆ : (x₀ * y₀)⁻¹ * x ∈ yamadaL₆ d t := mul_mem (inv_mem hzL₆) hx
    have hc' : (x₀ * y₀)⁻¹ * x ∈ yamadaL₃ d t := by
      rw [← h.yamadaL₆_inf_normalizer d hlay]
      exact mem_inf.2 ⟨hc₆, hc⟩
    have := mul_mem (mul_mem (mem_sup_left hx₀ : x₀ ∈ _) (mem_sup_right hy₀ : y₀ ∈ _))
      (mem_sup_left (h.yamadaL₃_le_yamadaL₄ d hlay hc') : _ ∈ yamadaL₄ d t ⊔ _)
    rwa [mul_inv_cancel_left] at this
  · exact sup_le (h.yamadaL₄_le_yamadaT₆ d hlay |>.trans (h.yamadaT₆_le_yamadaL₆ d hlay))
      (h.map_conj_yamadaL₄_le_yamadaT₆ d hlay |>.trans (h.yamadaT₆_le_yamadaL₆ d hlay))

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
