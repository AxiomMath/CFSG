module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalL3Prelim
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Seven

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open CFSG.Blueprint
open scoped commutatorElement Pointwise

theorem mem_normalizer_commutator_D4 {G : Type*} [Group G] [Finite G] {H : Subgroup G} {g : G}
    (hg : g ∈ normalizer (H : Set G)) :
    g ∈ normalizer ((⁅H, H⁆ : Subgroup G) : Set G) := by
  have hmap : H.map (MulAut.conj g).toMonoidHom = H := by
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact (mem_normalizer_iff.1 hg x).1 hx
    · intro x hx
      refine ⟨g⁻¹ * x * g, ?_, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
      have := (mem_normalizer_iff.1 (inv_mem hg) x).1 hx
      rwa [inv_inv] at this
  refine mem_normalizer_fintype fun x hx => ?_
  have : (MulAut.conj g).toMonoidHom x ∈ (⁅H, H⁆).map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rw [Subgroup.map_commutator, hmap] at this
  exact this

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Basic

omit [Finite G] in
theorem yamadaL₃_le_normalizer_yamadaL₂ {q : ℕ} (d : TrialityD4Data L q) :
    yamadaL₃ d t ≤ normalizer (yamadaL₂ d t : Set G) :=
  LieType.BorelTits.pCoreOf_le 2 _

omit [Finite G] in
theorem normalizer_yamadaL₂_le_normalizer_yamadaL₃ {q : ℕ} (d : TrialityD4Data L q) :
    normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaL₃ d t : Set G) := fun _ hg =>
  LieType.BorelTits.le_normalizer_pCoreOf 2 _ hg

theorem centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ (h : Setup G L f t) {q : ℕ}
    (d : TrialityD4Data L q) :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaL₃ d t : Set G) := fun _ hg =>
  normalizer_yamadaL₂_le_normalizer_yamadaL₃ d
    (le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d hg))

theorem leviLong_map_le_normalizer_yamadaL₃ (h : Setup G L f t) {q : ℕ}
    (d : TrialityD4Data L q) :
    d.leviLong.map L.subtype ≤ normalizer (yamadaL₃ d t : Set G) := by
  rintro _ ⟨l, hl, rfl⟩
  exact h.centralizer_inf_normalizer_Y_le_normalizer_yamadaL₃ d (Subgroup.mem_inf.2
    ⟨h.L_le_centralizer l.2, coe_mem_normalizer_map (d.leviLong_le_normalizer_Y hl)⟩)

theorem v_mem_normalizer_yamadaL₃ (h : Setup G L f t) {q : ℕ} (d : TrialityD4Data L q) :
    ((d.v : L) : G) ∈ normalizer (yamadaL₃ d t : Set G) :=
  h.leviLong_map_le_normalizer_yamadaL₃ d ⟨d.v, d.v_mem_leviLong, rfl⟩

omit [Finite G] in
theorem mul_self_mem_D_of_mem_S {q : ℕ} (d : TrialityD4Data L q) {s : L} (hs : s ∈ d.S) :
    s * s ∈ d.D := by
  obtain ⟨a, n, hn, rfl⟩ := d.mem_S_iff.1 hs
  have hx : d.x₁ a ∈ normalizer (d.D : Set L) := d.S_le_normalizer_D (d.U₁_le_S (d.x₁_mem_U₁ a))
  have e : d.x₁ a * n * (d.x₁ a * n) = (d.x₁ a * n * (d.x₁ a)⁻¹) * n := by
    rw [inv_eq_of_mul_eq_one_right (d.x₁_mul_self a)]
    group
  rw [e]
  exact mul_mem ((mem_normalizer_iff.1 hx n).1 hn) hn

end Basic

section Eighteen

theorem mul_self_mem_yamadaL₂_of_mem_yamadaL₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaL₃ d t) : x * x ∈ yamadaL₂ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  obtain ⟨_, _, φ, hφ, -⟩ := h.yamada_5_17_1_module d hNH h561 h562 h591 h592
    (h.yamada_5_9_3 d hlay) (h.yamada_5_10_1 d hlay) (h.yamada_5_10_2 d hlay)
  obtain ⟨hw, e⟩ := hφ ⟨x, hx⟩
  have h1 : φ (QuotientGroup.mk (⟨x, hx⟩ * ⟨x, hx⟩)) = 1 := by
    rw [QuotientGroup.mk_mul, map_mul, e, ← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff]
    have hww := yamadaW₂_mul_self d h562 h592
      ((le_sup_left : d.W.map L.subtype ≤ yamadaW₂ d t) hw)
    have : (⟨t * x * t * x⁻¹, hw⟩ * ⟨t * x * t * x⁻¹, hw⟩ : d.W.map L.subtype) = 1 :=
      Subtype.ext hww
    rw [this]
    exact one_mem _
  rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem mul_self_mem_yamadaC₅_of_mem_yamadaR₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    {x : G} (hx : x ∈ yamadaR₅ d t) : x * x ∈ yamadaC₅ d t := by
  have hSC : d.S.map L.subtype ≤ normalizer (yamadaC₅ d t : Set G) :=
    (h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t)
  have hDC : d.D.map L.subtype ≤ yamadaC₅ d t :=
    (h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)
  have hx' : x ∈ ((yamadaR₅ d t : Subgroup G) : Set G) := hx
  rw [h.coe_yamadaR₅ d] at hx'
  obtain ⟨c, hc, s, hs, e⟩ := hx'
  have e' : c * s = x := e
  subst e'
  have hsC : s * c * s⁻¹ ∈ yamadaC₅ d t := (mem_normalizer_iff.1 (hSC hs) c).1 hc
  have hss : s * s ∈ d.D.map L.subtype := by
    obtain ⟨s', hs', rfl⟩ := hs
    exact ⟨s' * s', mul_self_mem_D_of_mem_S d hs', map_mul _ _ _⟩
  have e2 : c * s * (c * s) = c * (s * c * s⁻¹) * (s * s) := by group
  rw [e2]
  exact mul_mem (mul_mem hc hsC) (hDC hss)

theorem mul_self_mem_yamadaW₂_of_mem_yamadaL₃ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {x : G}
    (hx : x ∈ yamadaL₃ d t) : x * x ∈ yamadaW₂ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h5171 := h.yamada_5_17_1 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have h5172 := h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hL₃R₅ : yamadaL₃ d t ≤ yamadaR₅ d t := by
    have : yamadaL₃ d t ≤ yamadaR₃ d t := by rw [h5172.2]; exact le_sup_left
    exact this.trans inf_le_left
  have hsq : ∀ y ∈ yamadaL₃ d t, y * y ∈ yamadaF₂ d t ⊔ zpowers t := fun y hy => by
    rw [← h.yamadaL₂_inf_yamadaC₅ d hlay]
    exact Subgroup.mem_inf.2 ⟨h.mul_self_mem_yamadaL₂_of_mem_yamadaL₃ d hlay hy,
      h.mul_self_mem_yamadaC₅_of_mem_yamadaR₅ d (hL₃R₅ hy)⟩
  have htF₂ : t ∈ normalizer (yamadaF₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.F) (h.t_mem_normalizer_yamadaY₂_D1 d)
  have hF₂C := h.yamadaF₂_le_centralizer_yamadaY₂ d hlay
  have htY := t_not_mem_centralizer_yamadaY₂ d h592
  have hvt := h.v_mul_t d
  have hvY := v_mem_normalizer_yamadaY₂ (t := t) d
  have hvx : ((d.v : L) : G)⁻¹ * x * (d.v : G) ∈ yamadaL₃ d t := by
    have := (mem_normalizer_iff.1 (inv_mem (h.v_mem_normalizer_yamadaL₃ d)) x).1 hx
    rwa [inv_inv] at this
  have hzv : ((d.v : L) : G)⁻¹ * (x * x) * (d.v : G) ∈ yamadaF₂ d t ⊔ zpowers t := by
    have := hsq _ hvx
    rwa [show ((d.v : L) : G)⁻¹ * x * (d.v : G) * (((d.v : L) : G)⁻¹ * x * (d.v : G)) =
      ((d.v : L) : G)⁻¹ * (x * x) * (d.v : G) by group] at this
  have hCv : ∀ z, z ∈ centralizer (yamadaY₂ d t : Set G) →
      ((d.v : L) : G)⁻¹ * z * (d.v : G) ∈ centralizer (yamadaY₂ d t : Set G) := fun z hz => by
    have := (mem_normalizer_iff.1 (mem_normalizer_centralizer_D4 (inv_mem hvY)) z).1 hz
    rwa [inv_inv] at this
  have hvtz : ∀ z : G, ((d.v : L) : G)⁻¹ * (t * z) * (d.v : G) =
      t * (((d.v : L) : G)⁻¹ * z * (d.v : G)) := fun z => by
    have hvt' : ((d.v : L) : G)⁻¹ * t = t * ((d.v : L) : G)⁻¹ := by
      calc ((d.v : L) : G)⁻¹ * t = ((d.v : L) : G)⁻¹ * (t * (d.v : G)) * ((d.v : L) : G)⁻¹ := by
            group
        _ = ((d.v : L) : G)⁻¹ * ((d.v : G) * t) * ((d.v : L) : G)⁻¹ := by rw [hvt]
        _ = t * ((d.v : L) : G)⁻¹ := by group
    rw [← mul_assoc, ← mul_assoc, hvt']
    group
  have hzW : x * x ∈ yamadaW₂ d t ⊔ zpowers t := by
    have hz := hsq x hx
    rw [h.mem_sup_zpowers_iff_of_normalizer htF₂] at hz hzv
    rcases hz with hz | hz
    · rcases hzv with hzv | hzv
      · exact mem_sup_left (h.yamadaF₂_inf_conj_v d hlay hz hzv)
      · exfalso
        apply htY
        have h1 := hF₂C hzv
        have h2 := hCv _ (hF₂C hz)
        have := mul_mem h1 (inv_mem h2)
        rwa [mul_inv_cancel_right] at this
    · rcases hzv with hzv | hzv
      · exfalso
        apply htY
        have h1 := hF₂C hz
        have h2 : x * x ∈ centralizer (yamadaY₂ d t : Set G) := by
          have := hCv _ (hF₂C hzv)
          have e : ((d.v : L) : G)⁻¹ * (((d.v : L) : G)⁻¹ * (x * x) * (d.v : G)) * (d.v : G) =
              x * x := by
            have hv2 : ((d.v : L) : G) * (d.v : G) = 1 := by
              rw [← Subgroup.coe_mul, d.v_mul_self, OneMemClass.coe_one]
            have hvinv : ((d.v : L) : G)⁻¹ = (d.v : G) := inv_eq_of_mul_eq_one_right hv2
            rw [hvinv, show (d.v : G) * ((d.v : G) * (x * x) * (d.v : G)) * (d.v : G) =
              ((d.v : G) * (d.v : G)) * (x * x) * ((d.v : G) * (d.v : G)) by group, hv2]
            group
          rwa [e] at this
        have := mul_mem h1 (inv_mem h2)
        rwa [mul_inv_cancel_right] at this
      · have h1 := h.yamadaF₂_inf_conj_v d hlay hz (by rw [hvtz]; exact hzv)
        have e : x * x = t * (t * (x * x)) := by rw [← mul_assoc, h.t_mul_t, one_mul]
        rw [e]
        exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)
  have htW₂ : t ∈ normalizer (yamadaW₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.W) (h.t_mem_normalizer_yamadaY₂_D1 d)
  rw [h.mem_sup_zpowers_iff_of_normalizer htW₂] at hzW
  rcases hzW with hzW | hzW
  · exact hzW
  · exfalso
    set w := t * (x * x) with hwdef
    have hxx : x * x = t * w := by rw [hwdef, ← mul_assoc, h.t_mul_t, one_mul]
    have hYN : yamadaY₂ d t ≤ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) :=
      fun y hy => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
        (mem_centralizer_iff.1 (h.M_map_le_centralizer_yamadaY₂ d hlay
          (map_mono (d.W_le_F.trans d.F_le_M) ha)) y hy).symm)
    have hw' : w ∈ ((d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hzW
    rw [coe_mul_of_right_le_normalizer_left _ _ hYN] at hw'
    obtain ⟨w₀, hw₀, a, ha, e⟩ := hw'
    have e' : w₀ * a = w := e
    have hmem : t * w₀ ∈ {x | ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = x} := by
      rw [h5171.2.2.2.2]
      exact ⟨w₀, hw₀, rfl⟩
    obtain ⟨y, hy, hyt⟩ := hmem
    have hY₂N : yamadaL₃ d t ≤ normalizer (yamadaY₂ d t : Set G) := fun g hg =>
      h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
        (h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hg)
    set z := y⁻¹ * x * y with hzdef
    have hzL₃ : z ∈ yamadaL₃ d t := mul_mem (mul_mem (inv_mem hy) hx) hy
    set b := y⁻¹ * a * y with hbdef
    have hb : b ∈ yamadaY₂ d t := by
      have := (mem_normalizer_iff.1 (inv_mem (hY₂N hy)) a).1 ha
      rwa [inv_inv] at this
    have hzz : z * z = t * b := by
      have e3 : z * z = y⁻¹ * (x * x) * y := by rw [hzdef]; group
      rw [e3, hxx, ← e', show t * (w₀ * a) = (t * w₀) * a by group, ← hyt, hbdef]
      group
    have hzt : z * t * z⁻¹ ∈ t • (yamadaY₂ d t : Set G) := by
      have hbN : z * b * z⁻¹ ∈ yamadaY₂ d t := (mem_normalizer_iff.1 (hY₂N hzL₃) b).1 hb
      refine ⟨b * (z * b * z⁻¹)⁻¹, mul_mem hb (inv_mem hbN), ?_⟩
      have e4 : t = z * z * b⁻¹ := by rw [hzz, mul_inv_cancel_right]
      show t * (b * (z * b * z⁻¹)⁻¹) = z * t * z⁻¹
      calc t * (b * (z * b * z⁻¹)⁻¹) = (t * b) * z * b⁻¹ * z⁻¹ := by group
        _ = (z * z) * z * b⁻¹ * z⁻¹ := by rw [hzz]
        _ = z * (z * z * b⁻¹) * z⁻¹ := by group
        _ = z * t * z⁻¹ := by rw [← e4]
    obtain ⟨c, hc, hct⟩ := hzt
    have hct' : z * t * z⁻¹ = t * c := hct.symm
    have hcW : c ∈ d.W.map L.subtype := by
      have hmem2 : z * t * z⁻¹ ∈ {x | ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = x} := ⟨z, hzL₃, rfl⟩
      rw [h5171.2.2.2.2] at hmem2
      obtain ⟨c', hc', e5⟩ := hmem2
      rw [hct'] at e5
      rw [← mul_left_cancel e5]
      exact hc'
    have hcY : c ∈ d.Y.map L.subtype := by
      rw [← h.map_inf_yamadaY₂ d hlay d.Y_le_W]
      exact Subgroup.mem_inf.2 ⟨hcW, hc⟩
    have hmem3 : t * c ∈ {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} := by
      rw [(h.yamada_5_3_2 d).2.2.2.2.2.1]
      exact ⟨c, hcY, rfl⟩
    obtain ⟨l, hl, hlt⟩ := hmem3
    have hzL₂ : z ∈ yamadaL₂ d t := by
      have hlz : l⁻¹ * z ∈ yamadaL₃ d t ⊓ centralizer ({t} : Set G) := by
        refine Subgroup.mem_inf.2 ⟨mul_mem (inv_mem (hL₂L₃ hl)) hzL₃,
          mem_centralizer_singleton_iff.2 ?_⟩
        calc l⁻¹ * z * t = l⁻¹ * (z * t * z⁻¹) * z := by group
          _ = l⁻¹ * (l * t * l⁻¹) * z := by rw [hct', ← hlt]
          _ = t * (l⁻¹ * z) := by group
      rw [h5171.2.2.2.1] at hlz
      have := mul_mem hl (h.tM_le_yamadaL₂ d hlz)
      rwa [mul_inv_cancel_left] at this
    have hzzM : z * z ∈ yamadaM₂ d t := by
      have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
        mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.M) (h.t_mem_normalizer_yamadaY₂_D1 d)
      have hzL₂' := hzL₂
      rw [h591.1, h.mem_sup_zpowers_iff_of_normalizer htM₂] at hzL₂'
      rcases hzL₂' with hzM | hzM
      · exact mul_mem hzM hzM
      · have e6 : z * z = (t * (t * z) * t) * (t * z) := by
          calc z * z = (t * t) * z * (t * t) * z := by rw [h.t_mul_t]; group
            _ = (t * (t * z) * t) * (t * z) := by group
        rw [e6]
        have := (mem_normalizer_iff.1 htM₂ _).1 hzM
        rw [htinv] at this
        exact mul_mem this hzM
    apply h591.2.1
    have hbM : b ∈ yamadaM₂ d t := le_sup_right (a := d.M.map L.subtype) hb
    rw [hzz] at hzzM
    have := mul_mem hzzM (inv_mem hbM)
    rwa [mul_inv_cancel_right] at this

theorem yamada_5_18 (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hlay : h.LayerHyp d) :
    ⁅yamadaL₃ d t, yamadaL₃ d t⁆ = yamadaW₂ d t := by
  have hNH := h.normalizerHyp_of_layerHyp d hlay
  have h561 := h.yamada_5_6_1 d hlay
  have h562 := h.yamada_5_6_2 d hlay
  have h591 := h.yamada_5_9_1 d hlay
  have h592 := h.yamada_5_9_2 d hlay
  have h593 := h.yamada_5_9_3 d hlay
  have h5101 := h.yamada_5_10_1 d hlay
  have h5102 := h.yamada_5_10_2 d hlay
  have h5171 := h.yamada_5_17_1 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have h5172 := h.yamada_5_17_2 d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hL₃V₂ := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hML₃ : d.M.map L.subtype ≤ yamadaL₃ d t :=
    (le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans hL₂L₃
  have hle : ⁅yamadaL₃ d t, yamadaL₃ d t⁆ ≤ yamadaW₂ d t := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact commutator_mem_of_mul_self_mem_of_normal_D4
      (fun g hg => (h.normalizer_yamadaV₂_le d h562 h592).1 (hL₃V₂ hg))
      (fun y hy => h.mul_self_mem_yamadaW₂_of_mem_yamadaL₃ d hlay hy) ha hb
  have hW : d.W.map L.subtype ≤ ⁅yamadaL₃ d t, yamadaL₃ d t⁆ := by
    rw [← d.commutator_M_eq, Subgroup.map_commutator]
    exact Subgroup.commutator_mono hML₃ hML₃
  have hne : ¬ ⁅yamadaL₃ d t, yamadaL₃ d t⁆ ≤ d.W.map L.subtype := by
    intro hc
    have hWM₁ : d.W.map L.subtype ≤ yamadaM₁ d t :=
      le_inf ((map_mono (d.W_le_F.trans d.F_le_M)).trans (le_sup_left.trans (h.tM_le_yamadaL₂ d)))
        ((map_mono (d.W_le_F.trans (d.F_le_M.trans d.M_le_S))).trans le_sup_left)
    have hM₁L₃ : yamadaM₁ d t ≤ yamadaL₃ d t := inf_le_left.trans hL₂L₃
    have hL₃N : yamadaL₃ d t ≤ normalizer (yamadaM₁ d t : Set G) := fun x hx =>
      mem_normalizer_fintype fun m hm => by
        have hcm : x * m * x⁻¹ * m⁻¹ ∈ yamadaM₁ d t :=
          hWM₁ (hc (Subgroup.commutator_mem_commutator hx (hM₁L₃ hm)))
        have := mul_mem hcm hm
        rwa [inv_mul_cancel_right] at this
    have hL₃R₂ : yamadaL₃ d t ≤ yamadaR₂ d t := by
      rw [← (h.yamada_5_15 d hNH h561 h562 h591 h592 h593).2]
      refine le_inf ?_ hL₃N
      have : yamadaL₃ d t ≤ yamadaR₃ d t := by rw [h5172.2]; exact le_sup_left
      exact this.trans inf_le_left
    have hmem : t * ((d.x₄ 1 : L) : G) ∈ {x | ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = x} := by
      rw [h5171.2.2.2.2]
      exact ⟨_, ⟨d.x₄ 1, d.x₄_mem_W 1, rfl⟩, rfl⟩
    obtain ⟨c, hc', hct⟩ := hmem
    have hY := h.crossed_mem_Y_of_mem_yamadaR₂ d (hL₃R₂ (inv_mem hc'))
    rw [inv_inv, hct] at hY
    have e : t * ((d.x₄ 1 : L) : G) * t = ((d.x₄ 1 : L) : G) := by
      rw [mul_assoc, mem_centralizer_singleton_iff.1 (h.L_le_centralizer (d.x₄ 1).2),
        ← mul_assoc, h.t_mul_t, one_mul]
    rw [e] at hY
    obtain ⟨y, hy, hy'⟩ := hY
    rw [Subtype.val_inj.1 hy'] at hy
    exact one_ne_zero (d.x₄_mem_Y_iff.1 hy)
  exact (h.eq_yamadaW₂_of_le d hlay hW hle hne fun _ hg =>
    mem_normalizer_commutator_D4 (h.leviLong_map_le_normalizer_yamadaL₃ d hg))

end Eighteen

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
