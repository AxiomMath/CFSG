module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalD1Series
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.QTwoD1
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Three

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

theorem commutator_mem_of_mul_self_mem_of_normal_D4 {G : Type*} [Group G] {X N : Subgroup G}
    (hN : X ≤ normalizer (N : Set G)) (hX : ∀ x ∈ X, x * x ∈ N) {a b : G} (ha : a ∈ X)
    (hb : b ∈ X) : a * b * a⁻¹ * b⁻¹ ∈ N := by
  have e : a * b * a⁻¹ * b⁻¹ = (a * b * (a * b)) * (b⁻¹ * (a * a)⁻¹ * b⁻¹⁻¹) * (b * b)⁻¹ := by
    group
  rw [e]
  refine mul_mem (mul_mem (hX _ (mul_mem ha hb)) ?_) (inv_mem (hX b hb))
  exact (mem_normalizer_iff.1 (hN (inv_mem hb)) _).1 (inv_mem (hX a ha))

namespace TrialityD4Data

variable {X : Type*} [Group X] {q : ℕ} (d : TrialityD4Data X q)

theorem F_inf_conj_v : d.F ⊓ d.F.map (MulAut.conj d.v).toMonoidHom = d.W := by
  refine le_antisymm ?_ (le_inf d.W_le_F ?_)
  · rintro g ⟨hgF, ⟨g', hg'F, rfl⟩⟩
    obtain ⟨a₃, a₄, a₅, a₆, rfl⟩ := d.mem_F_coords hg'F
    obtain ⟨b₃, b₄, b₅, b₆, hb⟩ := d.mem_F_coords hgF
    have e : (MulAut.conj d.v).toMonoidHom (d.nf (0, 0, a₃, a₄, a₅, a₆)) =
        d.nf (a₃, 0, 0, a₄, a₆, a₅) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, nf_apply, d.x₁_zero, d.x₂_zero,
        d.x₃_zero, one_mul, mul_one]
      calc d.v * (d.x₃ a₃ * d.x₄ a₄ * d.x₅ a₅ * d.x₆ a₆) * d.v⁻¹ =
          (d.v * d.x₃ a₃ * d.v⁻¹) * (d.v * d.x₄ a₄ * d.v⁻¹) * (d.v * d.x₅ a₅ * d.v⁻¹) *
            (d.v * d.x₆ a₆ * d.v⁻¹) := by group
        _ = d.x₁ a₃ * d.x₄ a₄ * d.x₆ a₅ * d.x₅ a₆ := by
          rw [d.v_conj_x₃, d.v_conj_x₄, d.v_conj_x₅, d.v_conj_x₆]
        _ = d.x₁ a₃ * d.x₄ a₄ * d.x₅ a₆ * d.x₆ a₅ := by
          rw [mul_assoc (d.x₁ a₃ * d.x₄ a₄), (d.commute₅₆ a₆ a₅).eq.symm, ← mul_assoc]
    rw [e] at hb ⊢
    have h := d.nf_injective hb
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, -⟩ := h
    rw [← h1]
    exact (d.mem_W_iff.2 ⟨a₄, d.x₅ a₆ * d.x₆ a₅, mul_mem (d.x₅_mem_Y a₆) (d.x₆_mem_Y a₅),
      by simp only [nf_apply, d.x₁_zero, d.x₂_zero, d.x₃_zero, one_mul, mul_assoc]⟩)
  · intro w hw
    refine ⟨d.v⁻¹ * w * d.v, d.W_le_F ?_, by simp [MulAut.conj_apply]; group⟩
    have := (mem_normalizer_iff.1 (inv_mem d.v_mem_normalizer_W_of_Y) w).1 hw
    rwa [inv_inv] at this

theorem eq_Y_of_le_Y {T : Subgroup X} (hTY : T ≤ d.Y) (hT : T ≠ ⊥)
    (hU₂ : ∀ a, d.x₂ a ∈ normalizer (T : Set X)) (hv : d.v ∈ normalizer (T : Set X)) :
    T = d.Y := by
  have hvT : ∀ y ∈ T, d.v * y * d.v⁻¹ ∈ T := fun y hy => (mem_normalizer_iff.1 hv y).1 hy
  have hx₂T : ∀ a, ∀ y ∈ T, d.x₂ a * y * (d.x₂ a)⁻¹ ∈ T := fun a y hy =>
    (mem_normalizer_iff.1 (hU₂ a) y).1 hy
  have key : ∀ b : d.Γ₀, b ≠ 0 → d.x₆ b ∈ T → d.Y ≤ T := by
    intro b hb h6
    have h5 : d.x₅ b ∈ T := by
      have := hvT _ h6
      rwa [d.v_conj_x₆] at this
    have hU₆ : d.U₆ ≤ T := by
      rintro _ ⟨e, rfl⟩
      have h1 := hx₂T (e * b⁻¹) _ h5
      rw [d.x₂_conj_x₅, mul_assoc, inv_mul_cancel₀ hb, mul_one] at h1
      have := mul_mem (inv_mem h5) h1
      rwa [inv_mul_cancel_left] at this
    have hU₅ : d.U₅ ≤ T := by
      rintro _ ⟨e, rfl⟩
      have := hvT _ (hU₆ ⟨e, rfl⟩)
      rwa [d.v_conj_x₆] at this
    exact sup_le hU₅ hU₆
  refine le_antisymm hTY ?_
  obtain ⟨y, hyT, hy1⟩ := T.bot_or_exists_ne_one.resolve_left hT
  obtain ⟨a, n, hn, hyn⟩ := d.mem_Y_iff.1 (hTY hyT)
  obtain ⟨b, rfl⟩ := hn
  by_cases ha : a = 0
  · refine key b (fun hb => hy1 ?_) ?_
    · rw [← Subtype.coe_mk y hyT] at hyn ⊢
      rw [← hyn, ha, hb, d.x₅_zero, d.x₆_zero, one_mul]
    · rw [← hyn, ha, d.x₅_zero, one_mul] at hyT
      exact hyT
  · refine key a ha ?_
    have h1 := hx₂T 1 _ hyT
    rw [← hyn] at h1 hyT
    have e : d.x₂ 1 * (d.x₅ a * d.x₆ b) * (d.x₂ 1)⁻¹ = d.x₅ a * d.x₆ b * d.x₆ a := by
      calc d.x₂ 1 * (d.x₅ a * d.x₆ b) * (d.x₂ 1)⁻¹ =
          (d.x₂ 1 * d.x₅ a * (d.x₂ 1)⁻¹) * (d.x₂ 1 * d.x₆ b * (d.x₂ 1)⁻¹) := by group
        _ = d.x₅ a * d.x₆ a * d.x₆ b := by
          rw [d.x₂_conj_x₅, one_mul, (d.commute₂₆ 1 b).eq, mul_inv_cancel_right]
        _ = d.x₅ a * d.x₆ b * d.x₆ a := by
          rw [mul_assoc, (d.x₆_add a b).symm, add_comm, d.x₆_add, ← mul_assoc]
    rw [e] at h1
    have := mul_mem (inv_mem hyT) h1
    rwa [inv_mul_cancel_left] at this

end TrialityD4Data

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

namespace Setup

section Prelim

theorem normalizerHyp_of_layerHyp (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) : NormalizerHyp d t :=
  h.normalizerHyp_all d (h.yamada_5_6_1 d hlay) (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay)
    (h.yamada_5_9_2 d hlay) (h.yamada_5_9_3 d hlay)

theorem yamadaL₂_inf_yamadaC₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    yamadaL₂ d t ⊓ yamadaC₅ d t = yamadaF₂ d t ⊔ zpowers t := by
  have h512 := h.yamada_5_12 d (h.normalizerHyp_of_layerHyp d hlay) (h.yamada_5_6_1 d hlay)
    (h.yamada_5_6_2 d hlay) (h.yamada_5_9_1 d hlay) (h.yamada_5_9_2 d hlay)
    (h.yamada_5_9_3 d hlay)
  have hYC₅ : yamadaY₂ d t ≤ yamadaC₅ d t := h512.2.2.1
  have hC₅C : yamadaC₅ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t :=
    h512.1.2.2.2
  have htC₅ : t ∈ yamadaC₅ d t := yamadaC₁_le_yamadaC₅ d t (h.t_mem_yamadaC₁_D1 d)
  have hDC₅ : d.D.map L.subtype ≤ yamadaC₅ d t :=
    (h.D_map_le_yamadaC₁ d).trans (yamadaC₁_le_yamadaC₅ d t)
  have hL₂ := (h.yamada_5_9_1 d hlay).1
  refine le_antisymm (fun x hx => ?_) (le_inf (sup_le (sup_le
    ((map_mono d.F_le_M).trans ((le_sup_left).trans (h.tM_le_yamadaL₂ d)))
    (h.yamadaY₂_le_yamadaL₂_D1 d hlay)) ((zpowers_le).2 (h.t_mem_yamadaL₂ d)))
    (sup_le (sup_le ((map_mono d.F_le_D).trans hDC₅) hYC₅) ((zpowers_le).2 htC₅)))
  obtain ⟨hxL, hxC⟩ := Subgroup.mem_inf.1 hx
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    mem_normalizer_sup (h.t_mem_normalizer_map_D1 d.M) (h.t_mem_normalizer_yamadaY₂_D1 d)
  have key : ∀ z ∈ yamadaM₂ d t, z ∈ yamadaC₅ d t → z ∈ yamadaF₂ d t := by
    intro z hzM hzC
    have hz' : z ∈ ((d.M.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hzM
    rw [coe_mul_of_right_le_normalizer_left _ _ ((le_centralizer_iff.1
      (h.M_map_le_centralizer_yamadaY₂ d hlay)).trans (Subgroup.centralizer_le_normalizer _))]
      at hz'
    obtain ⟨m, hm, y, hy, e⟩ := hz'
    have e' : m * y = z := e
    subst e'
    have hmC : m ∈ yamadaC₅ d t := by
      have := mul_mem hzC (inv_mem (hYC₅ hy))
      rwa [mul_inv_cancel_right] at this
    have hmL : m ∈ L := map_subtype_le _ hm
    have hmtD : m ∈ d.D.map L.subtype ⊔ zpowers t := by
      rw [← hC₅C]
      exact Subgroup.mem_inf.2 ⟨hmC, h.L_le_centralizer hmL⟩
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hmtD with hmD | hmD
    · obtain ⟨m', hm', rfl⟩ := hm
      obtain ⟨m'', hm'', e''⟩ := hmD
      have : m'' = m' := L.subtype_injective e''
      subst this
      exact mul_mem (le_sup_left (a := d.F.map L.subtype)
        ⟨m'', d.M_inf_D_le_F (Subgroup.mem_inf.2 ⟨hm', hm''⟩), rfl⟩)
        (le_sup_right (a := d.F.map L.subtype) hy)
    · exfalso
      apply h.t_not_mem_L
      have := mul_mem (map_subtype_le _ hmD) (inv_mem hmL)
      rwa [mul_inv_cancel_right] at this
  rw [hL₂, h.mem_sup_zpowers_iff_of_normalizer htM₂] at hxL
  rcases hxL with hxM | hxM
  · exact mem_sup_left (key x hxM hxC)
  · have h1 := key _ hxM (mul_mem htC₅ hxC)
    have e : x = t * (t * x) := by rw [← mul_assoc, h.t_mul_t, one_mul]
    rw [e]
    exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h1)

theorem v_mem_normalizer_yamadaY₂ {q : ℕ} (d : TrialityD4Data L q) :
    ((d.v : L) : G) ∈ normalizer (yamadaY₂ d t : Set G) := by
  have hv2 : ((d.v : L) : G) * (d.v : G) = 1 := by
    rw [← Subgroup.coe_mul, d.v_mul_self, OneMemClass.coe_one]
  have hvinv : ((d.v : L) : G)⁻¹ = (d.v : G) := inv_eq_of_mul_eq_one_right hv2
  refine mem_normalizer_fintype fun y hy => ?_
  have hle : yamadaY₂ d t ≤ (yamadaY₂ d t).comap (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
    refine sup_le (fun w hw => yamadaV₁_conj_le_yamadaY₂ d ⟨w, hw, rfl⟩) ?_
    rintro _ ⟨w, hw, rfl⟩
    simp only [mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [show ((d.v : L) : G) * (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) * ((d.v : L) : G)⁻¹ =
      ((d.v : G) * (d.v : G)) * w * ((d.v : G) * (d.v : G))⁻¹ by group, hv2]
    simpa using yamadaV₁_le_yamadaY₂ d hw
  exact hle hy

theorem yamadaF₂_inf_conj_v (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {z : G}
    (hz : z ∈ yamadaF₂ d t) (hzv : ((d.v : L) : G)⁻¹ * z * (d.v : G) ∈ yamadaF₂ d t) :
    z ∈ yamadaW₂ d t := by
  have hYN : yamadaY₂ d t ≤ normalizer ((d.F.map L.subtype : Subgroup G) : Set G) :=
    fun y hy => Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
      (mem_centralizer_iff.1 (h.yamadaF₂_le_centralizer_yamadaY₂ d hlay
        (le_sup_left (a := d.F.map L.subtype) ha)) y hy).symm)
  have hset : ((yamadaF₂ d t : Subgroup G) : Set G) =
      ((d.F.map L.subtype : Subgroup G) : Set G) * (yamadaY₂ d t : Set G) :=
    coe_mul_of_right_le_normalizer_left _ _ hYN
  have hz' : z ∈ ((yamadaF₂ d t : Subgroup G) : Set G) := hz
  rw [hset] at hz'
  obtain ⟨a, ha, y, hy, e⟩ := hz'
  have e' : a * y = z := e
  subst e'
  have hvY := v_mem_normalizer_yamadaY₂ (t := t) d
  have hyv : ((d.v : L) : G)⁻¹ * y * (d.v : G) ∈ yamadaY₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hvY) y).1 hy
    rwa [inv_inv] at this
  have hav : ((d.v : L) : G)⁻¹ * a * (d.v : G) ∈ yamadaF₂ d t := by
    have e2 : ((d.v : L) : G)⁻¹ * a * (d.v : G) = (((d.v : L) : G)⁻¹ * (a * y) * (d.v : G)) *
        (((d.v : L) : G)⁻¹ * y * (d.v : G))⁻¹ := by group
    rw [e2]
    exact mul_mem hzv (inv_mem (le_sup_right (a := d.F.map L.subtype) hyv))
  have hav' : ((d.v : L) : G)⁻¹ * a * (d.v : G) ∈ ((yamadaF₂ d t : Subgroup G) : Set G) := hav
  rw [hset] at hav'
  obtain ⟨b, hb, y', hy', e3⟩ := hav'
  have e3' : b * y' = ((d.v : L) : G)⁻¹ * a * (d.v : G) := e3
  have haL : a ∈ L := map_subtype_le _ ha
  have hy'L : y' ∈ L := by
    have : y' = b⁻¹ * (((d.v : L) : G)⁻¹ * a * (d.v : G)) := by rw [← e3', inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem (map_subtype_le _ hb)) (mul_mem (mul_mem (inv_mem d.v.2) haL) d.v.2)
  have hy'Y : y' ∈ d.Y.map L.subtype := by
    rw [← h.yamadaY₂_inf_centralizer d hlay]
    exact Subgroup.mem_inf.2 ⟨hy', h.L_le_centralizer hy'L⟩
  obtain ⟨a', ha', rfl⟩ := ha
  have hav'' : (d.v⁻¹ * a' * d.v : L) ∈ d.F := by
    obtain ⟨b', hb', rfl⟩ := hb
    obtain ⟨y'', hy'', rfl⟩ := hy'Y
    have : d.v⁻¹ * a' * d.v = b' * y'' := by
      apply L.subtype_injective
      simp only [map_mul, map_inv, Subgroup.coe_subtype] at e3' ⊢
      exact e3'.symm
    rw [this]
    exact mul_mem hb' (d.Y_le_W.trans d.W_le_F hy'')
  have ha'W : a' ∈ d.W := by
    rw [← d.F_inf_conj_v]
    refine Subgroup.mem_inf.2 ⟨ha', d.v⁻¹ * a' * d.v, hav'', ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  exact mul_mem (le_sup_left (a := d.W.map L.subtype) ⟨a', ha'W, rfl⟩)
    (le_sup_right (a := d.W.map L.subtype) hy)

theorem leviLong_map_le_normalizer_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) :
    d.leviLong.map L.subtype ≤ normalizer (yamadaY₂ d t : Set G) := by
  have : d.leviLong ≤ (normalizer (yamadaY₂ d t : Set G)).comap L.subtype := by
    refine (closure_le _).2 fun g hg => ?_
    rcases hg with hg | hg
    · exact h.S_map_le_normalizer_yamadaY₂ d hlay ⟨g, d.U₂_le_S hg, rfl⟩
    · rw [Set.mem_singleton_iff.1 hg]
      exact v_mem_normalizer_yamadaY₂ d
  rintro _ ⟨l, hl, rfl⟩
  exact this hl

theorem eq_yamadaW₂_of_le (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (hlay : h.LayerHyp d) {K : Subgroup G}
    (hWK : d.W.map L.subtype ≤ K) (hKW : K ≤ yamadaW₂ d t) (hne : ¬ K ≤ d.W.map L.subtype)
    (hlevi : d.leviLong.map L.subtype ≤ normalizer (K : Set G)) : K = yamadaW₂ d t := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have hYW : d.Y.map L.subtype ≤ d.W.map L.subtype := map_mono d.Y_le_W
  have hYY₂ := h.Y_map_le_yamadaY₂ d hlay
  have hlY₂ := h.leviLong_map_le_normalizer_yamadaY₂ d hlay
  have hlt : ∀ l ∈ d.leviLong.map L.subtype, l * t = t * l := fun l hl =>
    mem_centralizer_iff.1 h.htL l (map_subtype_le _ hl)
  have htY : ∀ z ∈ yamadaY₂ d t, t * z * t ∈ yamadaY₂ d t := fun z hz => by
    have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaY₂_D1 d) z).1 hz
    rwa [htinv] at this
  let ψ : (K ⊓ yamadaY₂ d t : Subgroup G) →* G :=
    { toFun := fun z => (z : G) * (t * z * t)
      map_one' := by simp [h.t_mul_t]
      map_mul' := fun a b => by
        have ha := (Subgroup.mem_inf.1 a.2).2
        have hb := (Subgroup.mem_inf.1 b.2).2
        have hc := h.mul_comm_of_mem_yamadaY₂ d hlay hb (htY a ha)
        show (a : G) * b * (t * (a * b) * t) = (a : G) * (t * a * t) * (b * (t * b * t))
        calc (a : G) * b * (t * (a * b) * t) = a * (b * (t * a * t)) * (t * b * t) := by
              rw [show (t : G) * (a * b) * t = (t * a * t) * (t * b * t) by
                rw [show (t * a * t) * (t * b * t) = t * a * (t * t) * b * t by group,
                  h.t_mul_t]
                group]
              group
          _ = a * ((t * a * t) * b) * (t * b * t) := by rw [hc]
          _ = a * (t * a * t) * (b * (t * b * t)) := by group }
  have hψ : ∀ z, ψ z = (z : G) * (t * z * t) := fun _ => rfl
  have hψY : ψ.range ≤ d.Y.map L.subtype := by
    rintro _ ⟨z, rfl⟩
    have hz := (Subgroup.mem_inf.1 z.2).2
    have := h.commutator_t_mem_Y_of_mem_yamadaY₂ d hlay hz
    rw [commutatorElement_def, htinv,
      inv_eq_of_mul_eq_one_right (h.mul_self_eq_one_of_mem_yamadaY₂ d hlay hz)] at this
    rw [hψ]
    simpa [mul_assoc] using this
  have hψN : ∀ l ∈ d.leviLong.map L.subtype, ∀ x ∈ ψ.range, l * x * l⁻¹ ∈ ψ.range := by
    rintro l hl _ ⟨z, rfl⟩
    have hz := Subgroup.mem_inf.1 z.2
    refine ⟨⟨l * z * l⁻¹, Subgroup.mem_inf.2 ⟨(mem_normalizer_iff.1 (hlevi hl) z).1 hz.1,
      (mem_normalizer_iff.1 (hlY₂ hl) z).1 hz.2⟩⟩, ?_⟩
    have hlt' : l⁻¹ * t = t * l⁻¹ := by
      calc l⁻¹ * t = l⁻¹ * (t * l) * l⁻¹ := by group
        _ = l⁻¹ * (l * t) * l⁻¹ := by rw [hlt l hl]
        _ = t * l⁻¹ := by group
    rw [hψ, hψ]
    calc l * z * l⁻¹ * (t * (l * z * l⁻¹) * t) = l * z * (l⁻¹ * t) * l * z * (l⁻¹ * t) := by
          group
      _ = l * z * (t * l⁻¹) * l * z * (t * l⁻¹) := by rw [hlt']
      _ = l * (z * (t * z * t)) * l⁻¹ := by group
  obtain ⟨k, hk, hkW⟩ := Set.not_subset.1 hne
  have hYN : yamadaY₂ d t ≤ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) := fun y hy =>
    Subgroup.centralizer_le_normalizer _ (mem_centralizer_iff.2 fun a ha =>
      (mem_centralizer_iff.1 (h.M_map_le_centralizer_yamadaY₂ d hlay
        (map_mono (d.W_le_F.trans d.F_le_M) ha)) y hy).symm)
  have hk' : k ∈ ((d.W.map L.subtype ⊔ yamadaY₂ d t : Subgroup G) : Set G) := hKW hk
  rw [coe_mul_of_right_le_normalizer_left _ _ hYN] at hk'
  obtain ⟨w, hw, y₀, hy₀, e⟩ := hk'
  have e' : w * y₀ = k := e
  have hy₀K : y₀ ∈ K := by
    have : y₀ = w⁻¹ * k := by rw [← e', inv_mul_cancel_left]
    rw [this]
    exact mul_mem (inv_mem (hWK hw)) hk
  have hy₀Y : y₀ ∉ d.Y.map L.subtype := fun hy => hkW (by
    rw [← e']
    exact mul_mem hw (hYW hy))
  have hψy₀ : ψ ⟨y₀, Subgroup.mem_inf.2 ⟨hy₀K, hy₀⟩⟩ ≠ 1 := by
    intro h1
    apply hy₀Y
    rw [← h.yamadaY₂_inf_centralizer d hlay]
    refine Subgroup.mem_inf.2 ⟨hy₀, mem_centralizer_singleton_iff.2 ?_⟩
    rw [hψ] at h1
    have h2 : t * y₀ * t = y₀⁻¹ := eq_inv_of_mul_eq_one_right h1
    rw [inv_eq_of_mul_eq_one_right (h.mul_self_eq_one_of_mem_yamadaY₂ d hlay hy₀)] at h2
    calc y₀ * t = t * y₀ * t * t := by rw [h2]
      _ = t * y₀ := by rw [mul_assoc (t * y₀), h.t_mul_t, mul_one]
  have hrange : ψ.range = d.Y.map L.subtype := by
    have hTL : ψ.range.comap L.subtype = d.Y := by
      refine d.eq_Y_of_le_Y (fun x hx => ?_) ?_ (fun a => ?_) ?_
      · obtain ⟨x', hx', e⟩ := hψY hx
        rw [← L.subtype_injective e]
        exact hx'
      · intro hbot
        apply hψy₀
        have hmem : ψ ⟨y₀, Subgroup.mem_inf.2 ⟨hy₀K, hy₀⟩⟩ ∈ L :=
          map_subtype_le _ (hψY ⟨_, rfl⟩)
        have : (⟨_, hmem⟩ : L) ∈ ψ.range.comap L.subtype := ⟨_, rfl⟩
        rw [hbot, mem_bot] at this
        exact congrArg Subtype.val this
      · refine mem_normalizer_fintype fun x hx => ?_
        have := hψN _ ⟨d.x₂ a, d.x₂_mem_leviLong a, rfl⟩ _ hx
        rw [SetLike.mem_coe, mem_comap, map_mul, map_mul, map_inv]
        exact this
      · refine mem_normalizer_fintype fun x hx => ?_
        have := hψN _ ⟨d.v, d.v_mem_leviLong, rfl⟩ _ hx
        rw [SetLike.mem_coe, mem_comap, map_mul, map_mul, map_inv]
        exact this
    rw [← hTL, Subgroup.map_comap_eq_self]
    rw [range_subtype]
    exact hψY.trans (map_subtype_le _)
  have hker : Nat.card (d.Y.map L.subtype) ≤ Nat.card ψ.ker := by
    refine Nat.card_le_card_of_injective (fun y => ⟨⟨y, Subgroup.mem_inf.2
      ⟨hWK (hYW y.2), hYY₂ y.2⟩⟩, ?_⟩) (fun a b hab => ?_)
    · rw [MonoidHom.mem_ker, hψ]
      have hyt : (y : G) * t = t * y := mem_centralizer_iff.1 h.htL _ (map_subtype_le _ y.2)
      have hyy := h.mul_self_eq_one_of_mem_yamadaY₂ d hlay (hYY₂ y.2)
      calc (y : G) * (t * y * t) = y * (y * t) * t := by rw [← hyt]; group
        _ = 1 := by rw [← mul_assoc, hyy, one_mul, h.t_mul_t]
    · have := congrArg (fun z : ψ.ker => ((z : (K ⊓ yamadaY₂ d t : Subgroup G)) : G)) hab
      exact Subtype.ext this
  have hcardKY := Subgroup.card_ker_mul_card_range ψ
  rw [hrange] at hcardKY
  have hY₂K : yamadaY₂ d t ≤ K := by
    have hle : Nat.card (yamadaY₂ d t) ≤ Nat.card (K ⊓ yamadaY₂ d t : Subgroup G) := by
      rw [h.card_yamadaY₂ d hlay, ← hcardKY, card_map_of_injective L.subtype_injective,
        d.card_Y]
      have := hker
      rw [card_map_of_injective L.subtype_injective, d.card_Y] at this
      calc (2 ^ f) ^ 4 = (2 ^ f) ^ 2 * (2 ^ f) ^ 2 := by ring
        _ ≤ Nat.card ψ.ker * (2 ^ f) ^ 2 := Nat.mul_le_mul_right _ this
    have heq := eq_of_le_of_card_ge (inf_le_right : K ⊓ yamadaY₂ d t ≤ yamadaY₂ d t) hle
    rw [← heq]
    exact inf_le_left
  exact le_antisymm hKW (sup_le hWK hY₂K)

end Prelim

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
