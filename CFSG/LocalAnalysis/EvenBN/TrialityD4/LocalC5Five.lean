module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Four
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Three

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Generic

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_le_normalizer_thompsonSubgroup_D4 (P : Subgroup G) :
    normalizer (P : Set G) ≤ normalizer (CFSG.Open.thompsonSubgroup P : Set G) := by
  intro g hg
  have hle : CFSG.Open.thompsonSubgroup P ≤
      (CFSG.Open.thompsonSubgroup P).comap (MulAut.conj g).toMonoidHom := by
    refine thompsonSubgroup_le_D4 fun A hA hAc hAmax => ?_
    have hAg : A.map (MulAut.conj g).toMonoidHom ≤ CFSG.Open.thompsonSubgroup P := by
      refine le_thompsonSubgroup_D4 ?_ ?_ fun B hB hBc => ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact (mem_normalizer_iff.1 hg x).1 (hA hx)
      · exact ⟨⟨fun a b => Subtype.ext (mul_comm_of_mem_map_conj_D4
          (mul_comm_of_isMulCommutative_D4 hAc) g a a.2 b b.2)⟩⟩
      · rw [card_map_of_injective (MulAut.conj g).injective]
        exact hAmax B hB hBc
    exact fun a ha => hAg ⟨a, ha, rfl⟩
  exact mem_normalizer_fintype fun x hx => hle hx

end Generic

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Main

variable (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) (hNH : NormalizerHyp d t)
  (h561 : yamadaC₁ d t = yamadaD₁ d t ⊔ zpowers t ∧ t ∉ yamadaD₁ d t ∧
    (normalizer (d.V : Set L)).map L.subtype ≤ normalizer (yamadaD₁ d t : Set G))
  (h562 : IsElemAbelian 2 (yamadaV₁ d t) ∧ Nat.card (yamadaV₁ d t) = (2 ^ f) ^ 2 ∧
    yamadaV₁ d t ⊓ centralizer ({t} : Set G) = d.V.map L.subtype ∧ yamadaV₁ d t ≤ yamadaF₁ d t)
  (h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
    yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t)
  (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
    Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
    yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
    yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype)
  (h593 : (Subgroup.upperCentralSeries (yamadaS₂ d t) 1).map (yamadaS₂ d t).subtype =
      yamadaV₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaS₂ d t) 2).map (yamadaS₂ d t).subtype = yamadaY₂ d t)
  (h5101 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
      d.V.map L.subtype ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype = yamadaY₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
      yamadaW₂ d t ⊔ zpowers t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
      yamadaF₂ d t ⊔ zpowers t)
  (h5102 : CFSG.Open.thompsonSubgroup (yamadaF₂ d t ⊔ zpowers t) = yamadaF₂ d t)

include h592 in
theorem yamadaF₂_inf_centralizer :
    yamadaF₂ d t ⊓ centralizer (yamadaF₂ d t : Set G) = yamadaY₂ d t := by
  have hFM : d.F.map L.subtype ≤ d.M.map L.subtype := map_mono d.F_le_M
  have hY₂F : yamadaY₂ d t ≤ normalizer ((d.F.map L.subtype : Subgroup G) : Set G) := fun a ha =>
    mem_normalizer_fintype fun n hn => by
      rw [← commute_of_mem_M_of_mem_yamadaY₂ d h592 (hFM hn) ha, mul_inv_cancel_right]
      exact hn
  apply le_antisymm
  · intro z hz
    obtain ⟨hzF, hzC⟩ := mem_inf.1 hz
    rw [show yamadaF₂ d t = d.F.map L.subtype ⊔ yamadaY₂ d t from rfl, ← SetLike.mem_coe,
      coe_mul_of_right_le_normalizer_left _ _ hY₂F, Set.mem_mul] at hzF
    obtain ⟨n, hn, a, ha, rfl⟩ := hzF
    have hnY : n ∈ d.Y.map L.subtype := by
      obtain ⟨n', hn', rfl⟩ := hn
      refine ⟨n', ?_, rfl⟩
      rw [← d.F_inf_centralizer_F]
      refine mem_inf.2 ⟨hn', mem_centralizer_iff.2 fun y hy => Subtype.ext ?_⟩
      have h1 := mem_centralizer_iff.1 hzC (y : G) (mem_sup_left ⟨y, hy, rfl⟩)
      have h2 : (y : G) * a = a * y := commute_of_mem_M_of_mem_yamadaY₂ d h592 (hFM ⟨y, hy, rfl⟩) ha
      simp only [Subgroup.coe_subtype] at h1
      calc (y : G) * n' = y * (n' * a) * a⁻¹ := by group
        _ = n' * a * y * a⁻¹ := by rw [h1]
        _ = n' * (a * y) * a⁻¹ := by group
        _ = n' * (y * a) * a⁻¹ := by rw [h2]
        _ = n' * y := by group
    exact mul_mem (Y_le_yamadaY₂ d h592 hnY) ha
  · refine le_inf le_sup_right ((Subgroup.le_centralizer_iff).2 (sup_le (fun n hn =>
      mem_centralizer_iff.2 fun a ha => (commute_of_mem_M_of_mem_yamadaY₂ d h592 (hFM hn) ha).symm)
      fun b hb => mem_centralizer_iff.2 fun a ha => yamadaY₂_mul_comm d h592 ha hb))

include h592 h5101 h5102 in
theorem normalizer_yamadaR₂_le :
    normalizer (yamadaR₂ d t : Set G) ≤
      normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ⊓
        normalizer (yamadaY₂ d t : Set G) := by
  intro g hg
  have h3 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3) hg
  have h4 := LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4) hg
  rw [h5101.2.2.1] at h3
  rw [h5101.2.2.2] at h4
  have hF := normalizer_le_normalizer_thompsonSubgroup_D4 _ h4
  rw [h5102] at hF
  refine mem_inf.2 ⟨h3, ?_⟩
  rw [← yamadaF₂_inf_centralizer d h592]
  refine Common.mem_normalizer_inf hF (mem_normalizer_fintype fun c hc =>
    mem_centralizer_iff.2 fun l hl => ?_)
  have hl' : g⁻¹ * l * g ∈ yamadaF₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hF) l).1 hl
    rwa [inv_inv] at this
  have h1 := mem_centralizer_iff.1 hc _ hl'
  calc l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by rw [h1]
    _ = g * c * g⁻¹ * l := by group

include h592 h5101 h5102 in
theorem yamadaR₂_le_normalizer_yamadaY₂ :
    yamadaR₂ d t ≤ normalizer (yamadaY₂ d t : Set G) := fun _ hx =>
  (mem_inf.1 (normalizer_yamadaR₂_le d h592 h5101 h5102 (le_normalizer hx))).2

include h h592 h5101 h5102 in
theorem centralizer_inf_normalizer_S_le_normalizer_yamadaY₂ :
    centralizer ({t} : Set G) ⊓ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) := by
  intro c hc
  have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
  have hcR : c ∈ normalizer (yamadaR d t : Set G) := by
    rw [hR]
    exact Common.mem_normalizer_sup hc.2
      (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hc.1))
  exact (mem_inf.1 (normalizer_yamadaR₂_le d h592 h5101 h5102
    (h.normalizer_yamadaR_le_normalizer_yamadaR₂ d hcR))).2

include h h592 h5101 h5102 in
theorem centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂ :
    centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) := by
  have hNS := h.centralizer_inf_normalizer_S_le_normalizer_yamadaY₂ d h592 h5101 h5102
  have hR₂ := yamadaR₂_le_normalizer_yamadaY₂ d h592 h5101 h5102
  have hSR₂ : d.S.map L.subtype ≤ yamadaR₂ d t := le_sup_right
  have hMR₂ : d.M.map L.subtype ≤ yamadaR₂ d t :=
    (le_sup_left.trans (h.tM_le_yamadaL₂ d)).trans le_sup_left
  have hv : ((d.v : L) : G) ∈ normalizer (yamadaY₂ d t : Set G) := by
    have hvv : ((d.v : L) : G) * ((d.v : L) : G) = 1 := by
      rw [← Subgroup.coe_mul, d.v_mul_self, Subgroup.coe_one]
    have hle : yamadaY₂ d t ≤ (yamadaY₂ d t).comap (MulAut.conj ((d.v : L) : G)).toMonoidHom := by
      refine sup_le (fun a ha => mem_sup_right ⟨a, ha, rfl⟩) ?_
      rintro _ ⟨a, ha, rfl⟩
      refine mem_sup_left ?_
      show ((d.v : L) : G) * (((d.v : L) : G) * a * ((d.v : L) : G)⁻¹) * ((d.v : L) : G)⁻¹ ∈ _
      rw [show ((d.v : L) : G) * (((d.v : L) : G) * a * ((d.v : L) : G)⁻¹) *
        ((d.v : L) : G)⁻¹ = (((d.v : L) : G) * ((d.v : L) : G)) * a *
          (((d.v : L) : G) * ((d.v : L) : G))⁻¹ by group, hvv, one_mul, inv_one, mul_one]
      exact ha
    exact mem_normalizer_fintype fun a ha => hle ha
  have hlevi : d.leviLong.map L.subtype ≤ normalizer (yamadaY₂ d t : Set G) := by
    rw [show d.leviLong = closure ((d.U₂ : Set L) ∪ {d.v}) from rfl, MonoidHom.map_closure]
    refine (closure_le _).2 (Set.image_subset_iff.2 (Set.union_subset (fun u hu => ?_)
      (Set.singleton_subset_iff.2 hv)))
    exact hR₂ (hSR₂ ⟨u, d.U₂_le_S hu, rfl⟩)
  intro c hc
  obtain ⟨hcC, hcY⟩ := mem_inf.1 hc
  obtain ⟨g, k, hgk⟩ := d.aut_eq (h.act ⟨c, hcC⟩)
  have hgY : g ∈ normalizer (d.Y : Set L) :=
    d.mem_normalizer_Y_of_conj_mul_φ_pow fun y hy => hgk ▸ h.act_mem_Y d hcC hcY y hy
  have hgC : (g : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer g.2
  have hc'C : (g : G)⁻¹ * c ∈ centralizer ({t} : Set G) := mul_mem (inv_mem hgC) hcC
  have hact : h.act ⟨(g : G)⁻¹ * c, hc'C⟩ = d.φ ^ k := by
    have e : (⟨(g : G)⁻¹ * c, hc'C⟩ : centralizer ({t} : Set G)) =
        (⟨(g : G), hgC⟩ : centralizer ({t} : Set G))⁻¹ * ⟨c, hcC⟩ := rfl
    rw [e, map_mul, map_inv, hgk, show (⟨(g : G), hgC⟩ : centralizer ({t} : Set G)) =
      ⟨(g : G), h.L_le_centralizer g.2⟩ from rfl, h.act_of_mem_L g.2, Subtype.coe_eta]
    group
  have hc'S : (g : G)⁻¹ * c ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun z hz => ?_
    obtain ⟨s, hs, rfl⟩ := hz
    rw [SetLike.mem_coe, Subgroup.coe_subtype, h.conj_mem_map_iff hc'C, hact]
    exact d.φ_pow_mem_S k hs
  have hc' := hNS (mem_inf.2 ⟨hc'C, hc'S⟩)
  obtain ⟨m, hm, s, hs, j, hj, hgeq⟩ := d.exists_mul_of_mem_normalizer_Y hgY
  have hjN : ((j : L) : G) ∈ normalizer (yamadaY₂ d t : Set G) := by
    refine hNS (mem_inf.2 ⟨h.L_le_centralizer j.2, ?_⟩)
    exact map_le_normalizer_map (inf_le_left.trans d.J_le_normalizer_S) ⟨j, hj, rfl⟩
  have hgN : (g : G) ∈ normalizer (yamadaY₂ d t : Set G) := by
    rw [hgeq, Subgroup.coe_mul, Subgroup.coe_mul]
    exact mul_mem (mul_mem (hR₂ (hMR₂ ⟨m, hm, rfl⟩)) (hlevi ⟨s, hs, rfl⟩)) hjN
  have := mul_mem hgN hc'
  rwa [mul_inv_cancel_left] at this

include h h592 h5101 h5102 in
theorem normalizer_tY_le_normalizer_yamadaY₂ :
    normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) := by
  rw [(h.yamada_5_3_2 d).2.1]
  exact sup_le (le_sup_left.trans (yamadaR₂_le_normalizer_yamadaY₂ d h592 h5101 h5102))
    (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂ d h592 h5101 h5102)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaR₃_le_normalizer :
    yamadaR₃ d t ≤ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ⊓
      normalizer (yamadaY₂ d t : Set G) :=
  (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.1.2.trans
    (normalizer_yamadaR₂_le d h592 h5101 h5102)

omit [Finite G] in
theorem crossed_mul_D4 {t : G} (htt : t * t = 1) (a b : G) :
    t * (a * b) * t * (a * b)⁻¹ = (t * a * t * a⁻¹) * (a * (t * b * t * b⁻¹) * a⁻¹) := by
  have e : (t * a * t * a⁻¹) * (a * (t * b * t * b⁻¹) * a⁻¹) =
      t * a * (t * t) * b * t * b⁻¹ * a⁻¹ := by group
  rw [e, htt]
  group

omit [Finite G] in
theorem crossed_inv_D4 {t : G} (htt : t * t = 1) (a : G) :
    t * a⁻¹ * t * a⁻¹⁻¹ = a⁻¹ * (t * a * t * a⁻¹)⁻¹ * a := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have e : a⁻¹ * (t * a * t * a⁻¹)⁻¹ * a = t⁻¹ * a⁻¹ * t⁻¹ * a := by group
  rw [e, htinv, inv_inv]

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem exists_conj_t_eq_mul_of_mem_W {w : G} (hw : w ∈ d.W.map L.subtype) :
    ∃ g ∈ yamadaR₃ d t, ∃ l ∈ yamadaL₂ d t, g * l * t * (g * l)⁻¹ = t * w := by
  obtain ⟨g, hg, v, hv, e⟩ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).1.2 w
    (mem_sup_left hw)
  obtain ⟨hgV, hgY₂⟩ := mem_inf.1 (h.yamadaR₃_le_normalizer d hNH h561 h562 h591 h592 h593
    h5101 h5102 hg)
  have hκ : t * g * t * g⁻¹ = w * v := by
    rw [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group, e,
      show t * (t * w * v) = (t * t) * w * v by group, h.t_mul_t, one_mul]
  have hwv : w * v ∈ d.W.map L.subtype := by
    rw [← hκ]
    exact h.crossed_mem_W d h562 h592 hgV
  have hvW : v ∈ d.W.map L.subtype := by
    have := mul_mem (inv_mem hw) hwv
    rwa [inv_mul_cancel_left] at this
  have hvY : v ∈ d.Y.map L.subtype := by
    have hvV : v ∈ d.V.map L.subtype := by
      rw [← h562.2.2.1]
      exact mem_inf.2 ⟨hv, h.L_le_centralizer (map_subtype_le _ hvW)⟩
    exact map_mono d.V_le_Y hvV
  have hgY : g ∈ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    rw [← h.W_inf_yamadaY₂ d h592]
    exact Common.mem_normalizer_inf ((h.normalizer_yamadaV₂_le d h562 h592).2.2 hgV) hgY₂
  have hy : g⁻¹ * v⁻¹ * g ∈ d.Y.map L.subtype := by
    have := (mem_normalizer_iff.1 (inv_mem hgY) v⁻¹).1 (inv_mem hvY)
    rwa [inv_inv] at this
  have hmem : t * (g⁻¹ * v⁻¹ * g) ∈ {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} := by
    rw [(h.yamada_5_3_2 d).2.2.2.2.2.1]
    exact ⟨_, hy, rfl⟩
  obtain ⟨l, hl, el⟩ := hmem
  refine ⟨g, hg, l, hl, ?_⟩
  calc g * l * t * (g * l)⁻¹ = g * (l * t * l⁻¹) * g⁻¹ := by group
    _ = g * (t * (g⁻¹ * v⁻¹ * g)) * g⁻¹ := by rw [el]
    _ = (g * t * g⁻¹) * v⁻¹ := by group
    _ = t * w * v * v⁻¹ := by rw [e]
    _ = t * w := by group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem exists_mul_mem_centralizer {g : G} (hg : t * g * t * g⁻¹ ∈ d.W.map L.subtype) :
    ∃ x ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ⊓
      normalizer (yamadaY₂ d t : Set G), x⁻¹ * g ∈ centralizer ({t} : Set G) := by
  obtain ⟨x, hx, l, hl, e⟩ :=
    h.exists_conj_t_eq_mul_of_mem_W d hNH h561 h562 h591 h592 h593 h5101 h5102 hg
  obtain ⟨hxV, hxY₂⟩ := mem_inf.1 (h.yamadaR₃_le_normalizer d hNH h561 h562 h591 h592 h593
    h5101 h5102 hx)
  have hlN := yamadaL₂_le d t hl
  refine ⟨x * l, mem_inf.2 ⟨mul_mem hxV (h.normalizer_tY_le_normalizer_yamadaV₂ d h591 h592 hlN),
    mul_mem hxY₂ (h.normalizer_tY_le_normalizer_yamadaY₂ d h592 h5101 h5102 hlN)⟩, ?_⟩
  have e' : g * t * g⁻¹ = x * l * t * (x * l)⁻¹ := by
    rw [e]
    calc g * t * g⁻¹ = (t * t) * (g * t * g⁻¹) := by rw [h.t_mul_t, one_mul]
      _ = t * (t * g * t * g⁻¹) := by group
  rw [mem_centralizer_singleton_iff]
  calc (x * l)⁻¹ * g * t = (x * l)⁻¹ * (g * t * g⁻¹) * g := by group
    _ = (x * l)⁻¹ * (x * l * t * (x * l)⁻¹) * g := by rw [e']
    _ = t * ((x * l)⁻¹ * g) := by group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaV₂_le_normalizer_yamadaY₂ :
    normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaY₂ d t : Set G) := by
  intro g hg
  obtain ⟨x, hx, hc⟩ := h.exists_mul_mem_centralizer d hNH h561 h562 h591 h592 h593 h5101 h5102
    (h.crossed_mem_W d h562 h592 hg)
  obtain ⟨hxV, hxY₂⟩ := mem_inf.1 hx
  have hcW := (h.normalizer_yamadaV₂_le d h562 h592).2.2 (mul_mem (inv_mem hxV) hg)
  have hcY : x⁻¹ * g ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    rw [h.centralizer_inf_normalizer_Y_eq_W d]
    exact mem_inf.2 ⟨hc, hcW⟩
  have := mul_mem hxY₂ (h.centralizer_inf_normalizer_Y_le_normalizer_yamadaY₂ d h592 h5101 h5102
    hcY)
  rwa [mul_inv_cancel_left] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaV₂_le_normalizer_Y :
    normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := fun g hg => by
  rw [← h.W_inf_yamadaY₂ d h592]
  exact Common.mem_normalizer_inf ((h.normalizer_yamadaV₂_le d h562 h592).2.2 hg)
    (h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hg)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem crossed_mem_Y_iff {g : G}
    (hg : g ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G)) :
    t * g * t * g⁻¹ ∈ d.Y.map L.subtype ↔
      g ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  have hgY := h.normalizer_yamadaV₂_le_normalizer_Y d hNH h561 h562 h591 h592 h593 h5101 h5102 hg
  have htY := h.t_mem_normalizer_map d.Y
  constructor
  · intro hκ
    have hgt : g * t * g⁻¹ = t * (t * g * t * g⁻¹) := by
      rw [show t * (t * g * t * g⁻¹) = (t * t) * g * t * g⁻¹ by group, h.t_mul_t, one_mul]
    refine mem_normalizer_fintype fun z hz => ?_
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htY).1 hz with hz | ⟨w, hw, rfl⟩
    · exact mem_sup_left ((mem_normalizer_iff.1 hgY z).1 hz)
    · rw [show g * (w * t) * g⁻¹ = g * w * g⁻¹ * (g * t * g⁻¹) by group, hgt]
      exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hgY w).1 hw))
        (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hκ))
  · intro hgN
    have hgt := (mem_normalizer_iff.1 hgN t).1 (mem_sup_right (mem_zpowers t))
    rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hgt with h1 | h1
    · exfalso
      exact h.conj_not_mem_L d g (map_subtype_le _ h1)
    · rwa [show t * g * t * g⁻¹ = t * (g * t * g⁻¹) by group]

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem inv_mul_mem_normalizer_tY {p z y : G}
    (hp : p ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G))
    (hz : z ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G))
    (hy : y ∈ d.Y.map L.subtype) (e : t * p * t * p⁻¹ = t * z * t * z⁻¹ * y) :
    p⁻¹ * z ∈ normalizer ((d.Y.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  have hpY := h.normalizer_yamadaV₂_le_normalizer_Y d hNH h561 h562 h591 h592 h593 h5101 h5102 hp
  refine (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102
    (mul_mem (inv_mem hp) hz)).1 ?_
  rw [crossed_mul_D4 h.t_mul_t p⁻¹ z, crossed_inv_D4 h.t_mul_t p, e,
    show p⁻¹ * (t * z * t * z⁻¹ * y)⁻¹ * p * (p⁻¹ * (t * z * t * z⁻¹) * p⁻¹⁻¹) =
      p⁻¹ * y⁻¹ * p by group]
  have := (mem_normalizer_iff.1 (inv_mem hpY) y⁻¹).1 (inv_mem hy)
  rwa [inv_inv] at this

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
