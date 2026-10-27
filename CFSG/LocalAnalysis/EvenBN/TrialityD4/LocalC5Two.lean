module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped commutatorElement Pointwise

section Defs

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {q : ℕ}

@[expose] noncomputable def yamadaQ₅ (d : TrialityD4Data L q) (t : G) : Subgroup G :=
  Common.centralizerMod (normalizer (yamadaC₁ d t : Set G) ⊓ normalizer (yamadaD₁ d t : Set G))
    (yamadaD₁ d t) (yamadaV₁ d t)
    (fun _ hg y hy => (mem_normalizer_iff.1 (mem_inf.1 hg).2 y).1 hy)
    (fun _ hg b hb => (mem_normalizer_iff.1
      (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (mem_inf.1 hg).2) b).1 hb)

theorem mem_yamadaQ₅ {d : TrialityD4Data L q} {t x : G} :
    x ∈ yamadaQ₅ d t ↔ (x ∈ normalizer (yamadaC₁ d t : Set G) ∧
      x ∈ normalizer (yamadaD₁ d t : Set G)) ∧
        ∀ y ∈ yamadaD₁ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t :=
  Iff.rfl

@[expose] def NormalizerHyp (d : TrialityD4Data L q) (t : G) : Prop :=
  normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaD₁ d t : Set G) ∧
    normalizer ((yamadaV₁ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G)

end Defs

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Basic

theorem t_mem_yamadaC₁ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) : t ∈ yamadaC₁ d t :=
  h.tD_le_yamadaC₁ d (mem_sup_right (mem_zpowers t))

theorem t_mem_normalizer_map (h : Setup G L f t) (E : Subgroup L) :
    t ∈ normalizer ((E.map L.subtype : Subgroup G) : Set G) :=
  mem_normalizer_fintype fun n hn => by
    rw [show t * n * t⁻¹ = n by
      rw [← mem_centralizer_iff.1 h.htL n (map_subtype_le _ hn), mul_inv_cancel_right]]
    exact hn

theorem t_mem_normalizer_yamadaY₂ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    t ∈ normalizer (yamadaY₂ d t : Set G) := by
  have htV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)
  refine Common.mem_normalizer_sup htV₁ (mem_normalizer_fintype fun z hz => ?_)
  obtain ⟨w, hw, rfl⟩ := hz
  have hvt : ((d.v : L) : G) * t = t * (d.v : L) := mem_centralizer_iff.1 h.htL _ (d.v : L).2
  refine ⟨t * w * t⁻¹, (mem_normalizer_iff.1 htV₁ w).1 hw, ?_⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  calc ((d.v : L) : G) * (t * w * t⁻¹) * ((d.v : L) : G)⁻¹ =
      (((d.v : L) : G) * t) * w * (((d.v : L) : G) * t)⁻¹ := by group
    _ = (t * (d.v : L)) * w * (t * (d.v : L))⁻¹ := by rw [hvt]
    _ = t * (((d.v : L) : G) * w * ((d.v : L) : G)⁻¹) * t⁻¹ := by group

end Basic

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

include h h561 h562 in
theorem exists_mul_of_mem_yamadaD₁ {δ : G} (hδ : δ ∈ yamadaD₁ d t) :
    ∃ n ∈ d.D.map L.subtype, ∃ v ∈ yamadaV₁ d t, δ = n * v := by
  have hDV : d.D.map L.subtype ≤ normalizer (yamadaV₁ d t : Set G) :=
    (D_le_yamadaD₁ d t).trans (le_normalizer.trans
      (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t))
  rw [h.yamadaD₁_eq_sup d h561 h562, ← SetLike.mem_coe,
    coe_mul_of_left_le_normalizer_right _ _ hDV, Set.mem_mul] at hδ
  obtain ⟨n, hn, v, hv, rfl⟩ := hδ
  exact ⟨n, hn, v, hv, rfl⟩

include h h561 h562 in
theorem commutatorElement_mem_yamadaV₁_of_mem_yamadaD₁ {δ y : G} (hδ : δ ∈ yamadaD₁ d t)
    (hy : y ∈ yamadaD₁ d t) : δ * y * δ⁻¹ * y⁻¹ ∈ yamadaV₁ d t := by
  obtain ⟨n, hn, v, hv, rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hδ
  obtain ⟨n', hn', v', hv', rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hy
  have hc : ∀ {w : G}, w ∈ yamadaV₁ d t → ∀ x ∈ yamadaD₁ d t, w * x * w⁻¹ = x :=
    fun hw x hx => by rw [← commute_of_mem_yamadaV₁ d t hw hx, mul_inv_cancel_right]
  have hn'v' : n' * v' ∈ yamadaD₁ d t :=
    mul_mem (D_le_yamadaD₁ d t hn') (yamadaV₁_le_yamadaD₁ d t hv')
  have e : n * v * (n' * v') * (n * v)⁻¹ * (n' * v')⁻¹ = n * n' * n⁻¹ * n'⁻¹ := by
    calc n * v * (n' * v') * (n * v)⁻¹ * (n' * v')⁻¹ =
        n * (v * (n' * v') * v⁻¹) * n⁻¹ * (n' * v')⁻¹ := by group
      _ = n * (n' * v') * n⁻¹ * (n' * v')⁻¹ := by rw [hc hv _ hn'v']
      _ = n * n' * (v' * n⁻¹ * v'⁻¹) * n'⁻¹ := by group
      _ = n * n' * n⁻¹ * n'⁻¹ := by rw [hc hv' _ (D_le_yamadaD₁ d t (inv_mem hn))]
  rw [e]
  obtain ⟨a, ha, rfl⟩ := hn
  obtain ⟨b, hb, rfl⟩ := hn'
  exact V_le_yamadaV₁ d h562 (mem_map_of_mem L.subtype (d.commutatorElement_mem_V_of_mem_D ha hb))

include h h561 h562 in
theorem t_commutatorElement_mem_yamadaV₁ {y : G} (hy : y ∈ yamadaD₁ d t) :
    t * y * t⁻¹ * y⁻¹ ∈ yamadaV₁ d t := by
  obtain ⟨n, hn, v, hv, rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hy
  have hnt : t * n = n * t := (mem_centralizer_iff.1 h.htL n (map_subtype_le _ hn)).symm
  have htv : t * v * t⁻¹ ∈ yamadaV₁ d t := (mem_normalizer_iff.1
    (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)) v).1 hv
  have hnV : n ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (le_normalizer (D_le_yamadaD₁ d t hn))
  have e : t * (n * v) * t⁻¹ * (n * v)⁻¹ = n * ((t * v * t⁻¹) * v⁻¹) * n⁻¹ := by
    calc t * (n * v) * t⁻¹ * (n * v)⁻¹ = (t * n) * v * t⁻¹ * v⁻¹ * n⁻¹ := by group
      _ = (n * t) * v * t⁻¹ * v⁻¹ * n⁻¹ := by rw [hnt]
      _ = n * ((t * v * t⁻¹) * v⁻¹) * n⁻¹ := by group
  rw [e]
  exact (mem_normalizer_iff.1 hnV _).1 (mul_mem htv (inv_mem hv))

include h h561 h562 in
theorem yamadaC₁_le_yamadaQ₅ : yamadaC₁ d t ≤ yamadaQ₅ d t := by
  have hN : ∀ {x : G}, x ∈ yamadaC₁ d t → x ∈ normalizer (yamadaC₁ d t : Set G) ∧
      x ∈ normalizer (yamadaD₁ d t : Set G) := fun hx =>
    ⟨le_normalizer hx, h.yamadaC₁_le_normalizer_yamadaD₁ d h561 hx⟩
  have hD₁ : yamadaD₁ d t ≤ yamadaQ₅ d t := fun δ hδ => mem_yamadaQ₅.2
    ⟨hN (h.yamadaD₁_le_yamadaC₁ d hδ), fun y hy =>
      h.commutatorElement_mem_yamadaV₁_of_mem_yamadaD₁ d h561 h562 hδ hy⟩
  have ht : t ∈ yamadaQ₅ d t := mem_yamadaQ₅.2
    ⟨hN (h.t_mem_yamadaC₁ d), fun y hy => h.t_commutatorElement_mem_yamadaV₁ d h561 h562 hy⟩
  rw [h561.1]
  exact sup_le hD₁ ((zpowers_le).2 ht)

include h hNH h561 h562 in
theorem exists_conj_t_eq {g : G} (hg : g ∈ normalizer (yamadaC₁ d t : Set G)) :
    ∃ δ ∈ yamadaD₁ d t, g * t * g⁻¹ = t * δ := by
  have hgD := hNH.1 hg
  have hgt : g * t * g⁻¹ ∈ yamadaD₁ d t ⊔ zpowers t := by
    rw [← h561.1]
    exact (mem_normalizer_iff.1 hg t).1 (h.t_mem_yamadaC₁ d)
  rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t (h.t_mem_normalizer_yamadaD₁ d)).1 hgt with
    h1 | ⟨a, ha, h1⟩
  · exfalso
    apply h561.2.1
    have := (mem_normalizer_iff.1 (inv_mem hgD) _).1 h1
    rwa [show g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t by group] at this
  · have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
    refine ⟨t * a * t, ?_, ?_⟩
    · have := (mem_normalizer_iff.1 (h.t_mem_normalizer_yamadaD₁ d) a).1 ha
      rwa [htinv] at this
    · rw [h1]
      calc a * t = (t * t) * a * t := by rw [h.t_mul_t, one_mul]
        _ = t * (t * a * t) := by group

include h hNH h561 h562 in
theorem crossed_mem_yamadaD₁ {x : G} (hx : x ∈ normalizer (yamadaC₁ d t : Set G)) :
    t * x * t * x⁻¹ ∈ yamadaD₁ d t := by
  obtain ⟨δ, hδ, e⟩ := h.exists_conj_t_eq d hNH h561 h562 hx
  rw [show t * x * t * x⁻¹ = t * (x * t * x⁻¹) by group, e, ← mul_assoc, h.t_mul_t, one_mul]
  exact hδ

include h hNH h561 h562 in
theorem crossed_mul_mem {x y : G} (hx : x ∈ yamadaQ₅ d t)
    (hy : y ∈ normalizer (yamadaC₁ d t : Set G)) :
    (t * x * t * x⁻¹ * (t * y * t * y⁻¹))⁻¹ * (t * (x * y) * t * (x * y)⁻¹) ∈ yamadaV₁ d t := by
  obtain ⟨-, hxc⟩ := mem_yamadaQ₅.1 hx
  have hδy := h.crossed_mem_yamadaD₁ d hNH h561 h562 hy
  have hδyN : t * y * t * y⁻¹ ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (le_normalizer hδy)
  have h1 := hxc _ hδy
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right h.t_mul_t
  have e : (t * x * t * x⁻¹ * (t * y * t * y⁻¹))⁻¹ * (t * (x * y) * t * (x * y)⁻¹) =
      (t * y * t * y⁻¹)⁻¹ * (x * (t⁻¹ * y * t * y⁻¹) * x⁻¹ * (t * y * t * y⁻¹)⁻¹) *
        (t * y * t * y⁻¹)⁻¹⁻¹ := by group
  rw [e, htinv]
  exact (mem_normalizer_iff.1 (inv_mem hδyN) _).1 h1

include h hNH h561 h562 in
theorem mem_normalizer_tV₁_of_crossed_mem {x : G} (hxN : x ∈ normalizer (yamadaC₁ d t : Set G))
    (hx : t * x * t * x⁻¹ ∈ yamadaV₁ d t) :
    x ∈ normalizer ((yamadaV₁ d t ⊔ zpowers t : Subgroup G) : Set G) := by
  have hxV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t
    (hNH.1 hxN)
  have htV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (h.t_mem_normalizer_yamadaD₁ d)
  have hxt : x * t * x⁻¹ = t * (t * x * t * x⁻¹) := by
    rw [show t * (t * x * t * x⁻¹) = (t * t) * x * t * x⁻¹ by group, h.t_mul_t, one_mul]
  refine mem_normalizer_fintype fun z hz => ?_
  rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htV₁).1 hz with hz | ⟨w, hw, rfl⟩
  · exact mem_sup_left ((mem_normalizer_iff.1 hxV₁ z).1 hz)
  · rw [show x * (w * t) * x⁻¹ = x * w * x⁻¹ * (x * t * x⁻¹) by group, hxt]
    exact mul_mem (mem_sup_left ((mem_normalizer_iff.1 hxV₁ w).1 hw))
      (mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left hx))

include h h561 h562 in
theorem mem_yamadaC₁_of_mem_yamadaQ₅_of_mem_normalizer {x : G} (hxQ : x ∈ yamadaQ₅ d t)
    (hxN : x ∈ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G)) :
    x ∈ yamadaC₁ d t := by
  obtain ⟨c, hc, y, hy, rfl⟩ := (h.two_core_C₁_all d).2.2.2 x hxN
  have hcQ : c ∈ yamadaQ₅ d t := by
    have := mul_mem hxQ (inv_mem (h.yamadaC₁_le_yamadaQ₅ d h561 h562 hy))
    rwa [mul_inv_cancel_right] at this
  obtain ⟨-, hcc⟩ := mem_yamadaQ₅.1 hcQ
  obtain ⟨hcC, hcV⟩ := mem_inf.1 hc
  have hcD : c ∈ normalizer ((d.D.map L.subtype : Subgroup G) : Set G) :=
    h.centralizer_inf_normalizer_V_le_normalizer_D d hc
  have hV : ∀ z ∈ d.V, h.act ⟨c, hcC⟩ z ∈ d.V := by
    intro z hz
    rw [← h.conj_mem_map_iff hcC]
    exact (mem_normalizer_iff.1 hcV _).1 ⟨z, hz, rfl⟩
  have hD : ∀ z ∈ d.D, h.act ⟨c, hcC⟩ z * z⁻¹ ∈ d.V := by
    intro z hz
    rw [← coe_mem_map_subtype_iff_D4, Subgroup.coe_mul, h.coe_act_apply, Subgroup.coe_inv]
    have hzD : (z : G) ∈ d.D.map L.subtype := ⟨z, hz, rfl⟩
    rw [← h.yamadaV₁_inf_D d h562]
    exact mem_inf.2 ⟨hcc _ (D_le_yamadaD₁ d t hzD),
      mul_mem ((mem_normalizer_iff.1 hcD _).1 hzD) (inv_mem hzD)⟩
  obtain ⟨n, hn, hα⟩ := d.eq_conj_of_trivial_D_mod_V hV hD
  obtain ⟨τ, hτ, rfl⟩ := h.exists_mul_zpowers_of_act_eq_conj d hcC hα
  exact mul_mem (h.tD_le_yamadaC₁ d (mul_mem (mem_sup_left ⟨n, hn, rfl⟩) (mem_sup_right hτ))) hy

include h hNH h561 h562 in
theorem mem_yamadaC₁_of_crossed_mem {x : G} (hxQ : x ∈ yamadaQ₅ d t)
    (hx : t * x * t * x⁻¹ ∈ yamadaV₁ d t) : x ∈ yamadaC₁ d t :=
  h.mem_yamadaC₁_of_mem_yamadaQ₅_of_mem_normalizer d h561 h562 hxQ
    (hNH.2
      (h.mem_normalizer_tV₁_of_crossed_mem d hNH h561 h562 (mem_yamadaQ₅.1 hxQ).1.1 hx))

include h hNH h561 h562 in
theorem isPGroup_yamadaQ₅ : IsPGroup 2 (yamadaQ₅ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := yamadaQ₅ d t with hQdef
  have hQN : ∀ x : Q, (x : G) ∈ normalizer (yamadaC₁ d t : Set G) := fun x =>
    (mem_yamadaQ₅.1 x.2).1.1
  have hV₁n : ((yamadaV₁ d t).subgroupOf (yamadaD₁ d t)).Normal :=
    (normal_subgroupOf_iff_le_normalizer (yamadaV₁_le_yamadaD₁ d t)).2
      (le_normalizer.trans (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t))
  let δf : Q → yamadaD₁ d t := fun x =>
    ⟨t * x * t * (x : G)⁻¹, h.crossed_mem_yamadaD₁ d hNH h561 h562 (hQN x)⟩
  let ψ : Q →* yamadaD₁ d t ⧸ (yamadaV₁ d t).subgroupOf (yamadaD₁ d t) :=
    { toFun := fun x => QuotientGroup.mk (δf x)
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        change t * ((1 : Q) : G) * t * ((1 : Q) : G)⁻¹ ∈ yamadaV₁ d t
        rw [coe_one, mul_one, inv_one, mul_one, h.t_mul_t]
        exact one_mem _
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have h1 := inv_mem (h.crossed_mul_mem d hNH h561 h562 x.2 (hQN y))
        rw [mul_inv_rev, inv_inv] at h1
        change (t * ((x * y : Q) : G) * t * ((x * y : Q) : G)⁻¹)⁻¹ *
          (t * (x : G) * t * (x : G)⁻¹ * (t * (y : G) * t * (y : G)⁻¹)) ∈ yamadaV₁ d t
        rw [coe_mul]
        exact h1 }
  have hC₁Q : IsPGroup 2 ((yamadaC₁ d t).subgroupOf Q) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 _).comap_of_injective Q.subtype Q.subtype_injective
  have hker : IsPGroup 2 ψ.ker := hC₁Q.to_le fun x hx => by
    rw [mem_subgroupOf]
    refine h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 x.2 ?_
    have h1 : QuotientGroup.mk (δf x) =
        (1 : yamadaD₁ d t ⧸ (yamadaV₁ d t).subgroupOf (yamadaD₁ d t)) := hx
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at h1
    exact h1
  have hD₁2 : IsPGroup 2 (yamadaD₁ d t) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (h.yamadaD₁_le_yamadaC₁ d)
  have hQ : IsPGroup 2
      (⊤ : Subgroup (yamadaD₁ d t ⧸ (yamadaV₁ d t).subgroupOf (yamadaD₁ d t))) :=
    (hD₁2.to_quotient _).to_subgroup ⊤
  have hV := hQ.comap_of_ker_isPGroup ψ hker
  rw [comap_top] at hV
  exact hV.of_equiv Subgroup.topEquiv

include h hNH h561 h562 in
theorem yamadaQ₅_le_yamadaC₅ : yamadaQ₅ d t ≤ yamadaC₅ d t :=
  LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (fun _ hx => (mem_yamadaQ₅.1 hx).1.1)
    (fun _ hg => mem_normalizer_fintype fun _ hz => Common.conj_mem_centralizerMod
      (mem_inf.2 ⟨hg, hNH.1 hg⟩) hz)
    (h.isPGroup_yamadaQ₅ d hNH h561 h562)

include h h561 h562 in
theorem yamadaD₁_le_yamadaS₂ : yamadaD₁ d t ≤ yamadaS₂ d t := by
  rw [h.yamadaD₁_eq_sup d h561 h562]
  exact sup_le ((map_mono d.D_le_S).trans le_sup_left) (le_sup_left.trans le_sup_right)

include h h561 h562 h593 in
theorem commutatorElement_mem_yamadaV₁_of_mem_yamadaY₂ {a δ : G} (ha : a ∈ yamadaY₂ d t)
    (hδ : δ ∈ yamadaD₁ d t) : a * δ * a⁻¹ * δ⁻¹ ∈ yamadaV₁ d t := by
  have hδS := h.yamadaD₁_le_yamadaS₂ d h561 h562 hδ
  rw [← h593.2] at ha
  obtain ⟨a', ha', rfl⟩ := ha
  have h1 := (Subgroup.mem_upperCentralSeries_succ_iff (n := 1)).1 ha' ⟨δ, hδS⟩
  rw [← h593.1]
  exact ⟨_, h1, rfl⟩

omit [Finite G] in
include h591 in
theorem yamadaY₂_le_yamadaL₂ : yamadaY₂ d t ≤ yamadaL₂ d t := by
  rw [h591.1]
  exact le_sup_right.trans le_sup_left

include h592 in
theorem M_le_normalizer_yamadaY₂ : d.M.map L.subtype ≤ normalizer (yamadaY₂ d t : Set G) := by
  intro m hm
  have hm₂ : m ∈ yamadaM₂ d t := mem_sup_left hm
  refine mem_normalizer_fintype fun a ha => ?_
  rw [← h592.2.2.2.1] at ha ⊢
  obtain ⟨-, hac⟩ := mem_inf.1 ha
  rw [mem_centralizer_iff.1 hac m hm₂, mul_inv_cancel_right]
  exact ha

include h h591 h592 in
theorem exists_mem_yamadaY₂_conj_eq {y : G} (hy : y ∈ d.Y.map L.subtype) :
    ∃ a ∈ yamadaY₂ d t, a * t * a⁻¹ = t * y := by
  have hmem : t * y ∈ {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} := by
    rw [(h.yamada_5_3_2 d).2.2.2.2.2.1]
    exact ⟨y, hy, rfl⟩
  obtain ⟨c, hc, hct⟩ := hmem
  rw [h591.1] at hc
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    Common.mem_normalizer_sup (h.t_mem_normalizer_map d.M) (h.t_mem_normalizer_yamadaY₂ d)
  rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ ((zpowers_le).2 htM₂),
    Set.mem_mul] at hc
  obtain ⟨m₂, hm₂, τ, hτ, rfl⟩ := hc
  have hM₂ : yamadaM₂ d t = yamadaY₂ d t ⊔ d.M.map L.subtype := sup_comm _ _
  rw [hM₂, coe_mul_of_right_le_normalizer_left _ _ (M_le_normalizer_yamadaY₂ d h592),
    Set.mem_mul] at hm₂
  obtain ⟨a, ha, m, hm, rfl⟩ := hm₂
  refine ⟨a, ha, ?_⟩
  have hmt : m * t = t * m := mem_centralizer_iff.1 h.htL m (map_subtype_le _ hm)
  have hτt : τ * t = t * τ := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hτ
    exact (Commute.zpow_left (Commute.refl t) k).eq
  have hmτ : m * τ * t = t * (m * τ) := by
    rw [mul_assoc, hτt, ← mul_assoc, hmt, mul_assoc]
  rw [← hct]
  calc a * t * a⁻¹ = a * (m * τ * t * (m * τ)⁻¹) * a⁻¹ := by rw [hmτ, mul_inv_cancel_right]
    _ = a * m * τ * t * (a * m * τ)⁻¹ := by group

include h h561 h562 h591 h593 in
theorem yamadaY₂_le_yamadaQ₅ : yamadaY₂ d t ≤ yamadaQ₅ d t := by
  intro a ha
  have hc : ∀ δ ∈ yamadaD₁ d t, a * δ * a⁻¹ * δ⁻¹ ∈ yamadaV₁ d t := fun δ hδ =>
    h.commutatorElement_mem_yamadaV₁_of_mem_yamadaY₂ d h561 h562 h593 ha hδ
  have haD₁ : a ∈ normalizer (yamadaD₁ d t : Set G) := mem_normalizer_fintype fun δ hδ => by
    rw [show a * δ * a⁻¹ = a * δ * a⁻¹ * δ⁻¹ * δ by group]
    exact mul_mem (yamadaV₁_le_yamadaD₁ d t (hc δ hδ)) hδ
  have hat : a * t * a⁻¹ ∈ yamadaC₁ d t := by
    have hmem : a * t * a⁻¹ ∈ {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} :=
      ⟨a, yamadaY₂_le_yamadaL₂ d h591 ha, rfl⟩
    rw [(h.yamada_5_3_2 d).2.2.2.2.2.1] at hmem
    obtain ⟨y, hy, e⟩ := hmem
    rw [← e]
    exact h.tD_le_yamadaC₁ d (mul_mem (mem_sup_right (mem_zpowers t))
      (mem_sup_left (map_mono (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)) hy)))
  have haC₁ : a ∈ normalizer (yamadaC₁ d t : Set G) := by
    refine mem_normalizer_fintype fun z hz => ?_
    rw [h561.1] at hz ⊢
    rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t (h.t_mem_normalizer_yamadaD₁ d)).1 hz with
      hz | ⟨w, hw, rfl⟩
    · exact mem_sup_left ((mem_normalizer_iff.1 haD₁ z).1 hz)
    · rw [show a * (w * t) * a⁻¹ = a * w * a⁻¹ * (a * t * a⁻¹) by group]
      refine mul_mem (mem_sup_left ((mem_normalizer_iff.1 haD₁ w).1 hw)) ?_
      rw [← h561.1]
      exact hat
  exact mem_yamadaQ₅.2 ⟨⟨haC₁, haD₁⟩, hc⟩

theorem conj_mul_eq_of_mem_yamadaQ₅ {x y δ δ' u u' : G} (hx : x ∈ yamadaQ₅ d t)
    (hδ' : δ' ∈ yamadaD₁ d t) (hu : u ∈ yamadaV₁ d t) (hu' : u' ∈ yamadaV₁ d t)
    (e : x * t * x⁻¹ = t * δ * u) (e' : y * t * y⁻¹ = t * δ' * u') :
    ∃ v ∈ yamadaV₁ d t, x * y * t * (x * y)⁻¹ = t * (δ * δ') * v := by
  obtain ⟨⟨-, hxD⟩, hxc⟩ := mem_yamadaQ₅.1 hx
  have hD₁N : yamadaD₁ d t ≤ normalizer (yamadaV₁ d t : Set G) :=
    le_normalizer.trans (normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t)
  have hxV : x ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t hxD
  have hc := hxc δ' hδ'
  have hxu' : x * u' * x⁻¹ ∈ yamadaV₁ d t := (mem_normalizer_iff.1 hxV u').1 hu'
  refine ⟨δ'⁻¹ * (u * (x * δ' * x⁻¹ * δ'⁻¹)) * δ'⁻¹⁻¹ * (x * u' * x⁻¹),
    mul_mem ((mem_normalizer_iff.1 (hD₁N (inv_mem hδ')) _).1 (mul_mem hu hc)) hxu', ?_⟩
  calc x * y * t * (x * y)⁻¹ = x * (y * t * y⁻¹) * x⁻¹ := by group
    _ = x * t * x⁻¹ * (x * δ' * x⁻¹) * (x * u' * x⁻¹) := by rw [e']; group
    _ = t * δ * u * (x * δ' * x⁻¹) * (x * u' * x⁻¹) := by rw [e]
    _ = t * (δ * δ') * (δ'⁻¹ * (u * (x * δ' * x⁻¹ * δ'⁻¹)) * δ'⁻¹⁻¹ * (x * u' * x⁻¹)) := by
        group

theorem conj_inv_eq_of_mem_yamadaQ₅ {x n v : G} (hx : x ∈ yamadaQ₅ d t)
    (hn : n ∈ d.D.map L.subtype) (hv : v ∈ yamadaV₁ d t) (e : x * t * x⁻¹ = t * n * v) :
    ∃ v' ∈ yamadaV₁ d t, x⁻¹ * t * x⁻¹⁻¹ = t * n⁻¹ * v' := by
  obtain ⟨⟨-, hxD⟩, -⟩ := mem_yamadaQ₅.1 hx
  obtain ⟨-, hxc'⟩ := mem_yamadaQ₅.1 (inv_mem hx)
  have hnD₁ : n ∈ yamadaD₁ d t := D_le_yamadaD₁ d t hn
  have hxV : x⁻¹ ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (inv_mem hxD)
  have hnV : n ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (le_normalizer hnD₁)
  have h1 : x⁻¹ * v⁻¹ * x⁻¹⁻¹ ∈ yamadaV₁ d t := (mem_normalizer_iff.1 hxV _).1 (inv_mem hv)
  have h2 := hxc' _ (inv_mem hnD₁)
  refine ⟨n * ((x⁻¹ * v⁻¹ * x⁻¹⁻¹) * (x⁻¹ * n⁻¹ * x⁻¹⁻¹ * n⁻¹⁻¹)) * n⁻¹,
    (mem_normalizer_iff.1 hnV _).1 (mul_mem h1 h2), ?_⟩
  have et : t = x * t * x⁻¹ * (n * v)⁻¹ := by rw [e]; group
  calc x⁻¹ * t * x⁻¹⁻¹ = x⁻¹ * (x * t * x⁻¹ * (n * v)⁻¹) * x⁻¹⁻¹ := by rw [← et]
    _ = t * n⁻¹ * (n * ((x⁻¹ * v⁻¹ * x⁻¹⁻¹) * (x⁻¹ * n⁻¹ * x⁻¹⁻¹ * n⁻¹⁻¹)) * n⁻¹) := by group

include h hNH h561 h562 h591 h592 h593 in
theorem exists_mem_yamadaQ₅_conj_eq_of_mem_D {n : G} (hn : n ∈ d.D.map L.subtype) :
    ∃ x ∈ yamadaQ₅ d t, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * n * v := by
  let T : Subgroup L :=
    { carrier := {m | m ∈ d.D ∧ ∃ x ∈ yamadaQ₅ d t, ∃ v ∈ yamadaV₁ d t,
        x * t * x⁻¹ = t * (m : G) * v}
      mul_mem' := by
        rintro a b ⟨ha, x, hx, u, hu, e⟩ ⟨hb, y, hy, u', hu', e'⟩
        obtain ⟨v, hv, e''⟩ := conj_mul_eq_of_mem_yamadaQ₅ d hx
          (D_le_yamadaD₁ d t ⟨b, hb, rfl⟩) hu hu' e e'
        exact ⟨mul_mem ha hb, x * y, mul_mem hx hy, v, hv, by rw [e'', Subgroup.coe_mul]; rfl⟩
      one_mem' := ⟨one_mem _, 1, one_mem _, 1, one_mem _, by simp⟩
      inv_mem' := by
        rintro a ⟨ha, x, hx, u, hu, e⟩
        obtain ⟨v, hv, e'⟩ := conj_inv_eq_of_mem_yamadaQ₅ d hx ⟨a, ha, rfl⟩ hu e
        exact ⟨inv_mem ha, x⁻¹, inv_mem hx, v, hv, by rw [e', Subgroup.coe_inv]; rfl⟩ }
  have hTD : T ≤ d.D := fun m hm => hm.1
  have hVT : d.V ≤ T := by
    intro m hm
    obtain ⟨x, hx, e⟩ := (h.two_core_C₁_all d).2.2.1 (m : G) ⟨m, hm, rfl⟩
    refine ⟨d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)) hm, x⁻¹,
      h.yamadaC₁_le_yamadaQ₅ d h561 h562 (inv_mem hx), 1, one_mem _, ?_⟩
    rw [inv_inv, mul_one, e]
  have hYT : d.Y ≤ T := by
    intro m hm
    obtain ⟨a, ha, e⟩ := h.exists_mem_yamadaY₂_conj_eq d h591 h592 ⟨m, hm, rfl⟩
    exact ⟨(d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)) hm, a,
      h.yamadaY₂_le_yamadaQ₅ d h561 h562 h591 h593 ha, 1, one_mem _, by rw [mul_one, e]; rfl⟩
  have hTn : d.leviShort ≤ normalizer (T : Set L) := by
    intro s hs
    have hsC : (s : G) ∈ centralizer ({t} : Set G) := h.L_le_centralizer s.2
    have hsV : (s : G) ∈ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
      map_le_normalizer_map d.leviShort_le_normalizer_V ⟨s, hs, rfl⟩
    have hsC₁ : (s : G) ∈ normalizer (yamadaC₁ d t : Set G) :=
      le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d ⟨hsC, hsV⟩)
    have hsD₁ : (s : G) ∈ normalizer (yamadaD₁ d t : Set G) :=
      h561.2.2 ⟨s, d.leviShort_le_normalizer_V hs, rfl⟩
    have hsV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t hsD₁
    have hst : (s : G) * t = t * s := mem_centralizer_singleton_iff.1 hsC
    refine mem_normalizer_fintype fun m hm => ?_
    obtain ⟨hmD, x, hx, v, hv, e⟩ := hm
    refine ⟨(mem_normalizer_iff.1 (d.leviShort_le_normalizer_D hs) m).1 hmD, s * x * s⁻¹,
      Common.conj_mem_centralizerMod (mem_inf.2 ⟨hsC₁, hsD₁⟩) hx, s * v * s⁻¹,
      (mem_normalizer_iff.1 hsV₁ v).1 hv, ?_⟩
    have hst' : (s : G)⁻¹ * t * s = t := by rw [mul_assoc, ← hst, inv_mul_cancel_left]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    calc (s : G) * x * (s : G)⁻¹ * t * ((s : G) * x * (s : G)⁻¹)⁻¹ =
        s * x * ((s : G)⁻¹ * t * s) * x⁻¹ * (s : G)⁻¹ := by group
      _ = s * (x * t * x⁻¹) * (s : G)⁻¹ := by rw [hst']; group
      _ = s * (t * m * v) * (s : G)⁻¹ := by rw [e]
      _ = (s * t) * m * v * (s : G)⁻¹ := by group
      _ = (t * s) * m * v * (s : G)⁻¹ := by rw [hst]
      _ = t * ((s : G) * m * (s : G)⁻¹) * ((s : G) * v * (s : G)⁻¹) := by group
  rcases d.leviShort_irreducible_D_mod_V hVT hTD hTn with h1 | h1
  · exfalso
    have h2 := Subgroup.card_le_of_le (hYT.trans h1.le)
    rw [d.card_Y, d.card_V] at h2
    have h3 : 2 ^ f < (2 ^ f) ^ 2 := by have := d.two_le_q; nlinarith
    omega
  · obtain ⟨m, hm, rfl⟩ := hn
    exact (h1 ▸ hm : m ∈ T).2

include h hNH h561 h562 h591 h592 h593 in
theorem exists_mem_yamadaQ₅_conj_eq {δ : G} (hδ : δ ∈ yamadaD₁ d t) :
    ∃ x ∈ yamadaQ₅ d t, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * δ * v := by
  obtain ⟨n, hn, w, hw, rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hδ
  obtain ⟨x, hx, v, hv, e⟩ := h.exists_mem_yamadaQ₅_conj_eq_of_mem_D d hNH h561 h562 h591 h592
    h593 hn
  exact ⟨x, hx, w⁻¹ * v, mul_mem (inv_mem hw) hv, by rw [e]; group⟩

include h hNH h561 h562 h591 h592 h593 in
theorem exists_mul_of_mem_normalizer_yamadaC₁ {g : G}
    (hg : g ∈ normalizer (yamadaC₁ d t : Set G)) :
    ∃ x ∈ yamadaQ₅ d t, ∃ c ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.V.map L.subtype : Subgroup G) : Set G), g = x * c := by
  obtain ⟨δ, hδ, hgt⟩ := h.exists_conj_t_eq d hNH h561 h562 hg
  obtain ⟨x, hx, v, hv, hxt⟩ := h.exists_mem_yamadaQ₅_conj_eq d hNH h561 h562 h591 h592 h593 hδ
  obtain ⟨⟨hxN, hxD⟩, -⟩ := mem_yamadaQ₅.1 hx
  have hyN : x⁻¹ * g ∈ normalizer (yamadaC₁ d t : Set G) := mul_mem (inv_mem hxN) hg
  have hxV : x⁻¹ ∈ normalizer (yamadaV₁ d t : Set G) :=
    normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t (inv_mem hxD)
  have hκ : t * (x⁻¹ * g) * t * (x⁻¹ * g)⁻¹ ∈ yamadaV₁ d t := by
    have e : t * (x⁻¹ * g) * t * (x⁻¹ * g)⁻¹ = x⁻¹ * v⁻¹ * x⁻¹⁻¹ := by
      have h1 : g * t * g⁻¹ = x * t * x⁻¹ * v⁻¹ := by rw [hxt, hgt]; group
      calc t * (x⁻¹ * g) * t * (x⁻¹ * g)⁻¹ = t * x⁻¹ * (g * t * g⁻¹) * x := by group
        _ = t * x⁻¹ * (x * t * x⁻¹ * v⁻¹) * x := by rw [h1]
        _ = (t * t) * (x⁻¹ * v⁻¹ * x⁻¹⁻¹) := by group
        _ = x⁻¹ * v⁻¹ * x⁻¹⁻¹ := by rw [h.t_mul_t, one_mul]
    rw [e]
    exact (mem_normalizer_iff.1 hxV _).1 (inv_mem hv)
  have hy := hNH.2
    (h.mem_normalizer_tV₁_of_crossed_mem d hNH h561 h562 hyN hκ)
  obtain ⟨c, hc, y, hy', e⟩ := (h.two_core_C₁_all d).2.2.2 _ hy
  have hcN : c ∈ normalizer (yamadaC₁ d t : Set G) :=
    le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d hc)
  have hcy : c * y * c⁻¹ ∈ yamadaQ₅ d t :=
    h.yamadaC₁_le_yamadaQ₅ d h561 h562 ((mem_normalizer_iff.1 hcN y).1 hy')
  refine ⟨x * (c * y * c⁻¹), mul_mem hx hcy, c, hc, ?_⟩
  calc g = x * (x⁻¹ * g) := by group
    _ = x * (c * y) := by rw [e]
    _ = x * (c * y * c⁻¹) * c := by group

include h hNH h561 h562 h591 h592 h593 in
theorem yamadaC₅_eq_yamadaQ₅ : yamadaC₅ d t = yamadaQ₅ d t := by
  refine le_antisymm (fun z hz => ?_) (h.yamadaQ₅_le_yamadaC₅ d hNH h561 h562)
  obtain ⟨x, hx, c, hc, rfl⟩ := h.exists_mul_of_mem_normalizer_yamadaC₁ d hNH h561 h562 h591 h592
    h593 (yamadaC₅_le d t hz)
  have hcC₅ : c ∈ yamadaC₅ d t := by
    have := mul_mem (inv_mem (h.yamadaQ₅_le_yamadaC₅ d hNH h561 h562 hx)) hz
    rwa [inv_mul_cancel_left] at this
  have hcN := h.centralizer_inf_normalizer_V_le d hc
  have hle : yamadaC₅ d t ⊓ normalizer ((d.V.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ≤
      yamadaC₁ d t := by
    refine LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le inf_le_left)
    intro n hn
    exact Common.mem_normalizer_inf (le_normalizer_yamadaC₅ d t (le_normalizer_yamadaC₁ d t hn))
      (le_normalizer hn)
  exact mul_mem hx (h.yamadaC₁_le_yamadaQ₅ d h561 h562 (hle ⟨hcC₅, hcN⟩))

include h h562 in
theorem inv_mul_mem_V_of_conj_eq {x δ δ' u u' : G} (hδ : δ ∈ d.D.map L.subtype)
    (hδ' : δ' ∈ d.D.map L.subtype) (hu : u ∈ yamadaV₁ d t) (hu' : u' ∈ yamadaV₁ d t)
    (e : x * t * x⁻¹ = t * δ * u) (e' : x * t * x⁻¹ = t * δ' * u') :
    δ⁻¹ * δ' ∈ d.V.map L.subtype := by
  have h1 : δ⁻¹ * δ' = u * u'⁻¹ := by
    have h2 : t * δ * u = t * δ' * u' := e.symm.trans e'
    calc δ⁻¹ * δ' = δ⁻¹ * (t⁻¹ * (t * δ' * u')) * u'⁻¹ := by group
      _ = δ⁻¹ * (t⁻¹ * (t * δ * u)) * u'⁻¹ := by rw [h2]
      _ = u * u'⁻¹ := by group
  rw [← h.yamadaV₁_inf_D d h562]
  exact mem_inf.2 ⟨h1 ▸ mul_mem hu (inv_mem hu'), mul_mem (inv_mem hδ) hδ'⟩

include h hNH h561 h562 h591 h592 h593 in
theorem yamada_5_12_module :
    ∃ _ : ((yamadaC₁ d t).subgroupOf (yamadaC₅ d t)).Normal,
      ∃ _ : ((d.V.map L.subtype).subgroupOf (d.D.map L.subtype)).Normal,
        ∃ φ : yamadaC₅ d t ⧸ (yamadaC₁ d t).subgroupOf (yamadaC₅ d t) ≃*
            (d.D.map L.subtype : Subgroup G) ⧸ (d.V.map L.subtype).subgroupOf (d.D.map L.subtype),
          (∀ (x : yamadaC₅ d t) (δ : d.D.map L.subtype), (∃ u ∈ yamadaV₁ d t,
              (x : G) * t * (x : G)⁻¹ = t * δ * u) →
            φ (QuotientGroup.mk x) = QuotientGroup.mk δ) ∧
          ∀ n ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G),
            ∀ (x : yamadaC₅ d t) (δ : d.D.map L.subtype),
              φ (QuotientGroup.mk x) = QuotientGroup.mk δ →
              ∃ (hx : n * x * n⁻¹ ∈ yamadaC₅ d t) (hδ : n * δ * n⁻¹ ∈ d.D.map L.subtype),
                φ (QuotientGroup.mk ⟨_, hx⟩) = QuotientGroup.mk ⟨_, hδ⟩ := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  have hVD : d.V.map L.subtype ≤ d.D.map L.subtype :=
    map_mono (d.V_le_Y.trans (d.Y_le_W.trans (d.W_le_F.trans d.F_le_D)))
  have hDV : d.D.map L.subtype ≤ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :=
    map_le_normalizer_map (d.D_le_S.trans d.S_le_normalizer_V)
  have hVDn : ((d.V.map L.subtype).subgroupOf (d.D.map L.subtype)).Normal :=
    (normal_subgroupOf_iff_le_normalizer hVD).2 hDV
  have hrel : ∀ x : yamadaC₅ d t, ∃ δ ∈ d.D.map L.subtype, ∃ u ∈ yamadaV₁ d t,
      (x : G) * t * (x : G)⁻¹ = t * δ * u := fun x => by
    obtain ⟨δ₁, hδ₁, e⟩ := h.exists_conj_t_eq d hNH h561 h562 (yamadaC₅_le d t x.2)
    obtain ⟨a, ha, b, hb, rfl⟩ := h.exists_mul_of_mem_yamadaD₁ d h561 h562 hδ₁
    exact ⟨a, ha, b, hb, by rw [e, mul_assoc]⟩
  choose δf hδf uf huf hfe using hrel
  have hQ : ∀ x : yamadaC₅ d t, (x : G) ∈ yamadaQ₅ d t := fun x => hCQ ▸ x.2
  let ψ : yamadaC₅ d t →*
      d.D.map L.subtype ⧸ (d.V.map L.subtype).subgroupOf (d.D.map L.subtype) :=
    { toFun := fun x => QuotientGroup.mk ⟨δf x, hδf x⟩
      map_one' := by
        apply (QuotientGroup.eq_one_iff _).2
        rw [mem_subgroupOf]
        have := h.inv_mul_mem_V_of_conj_eq d h562 (hδf 1) (one_mem _) (huf 1) (one_mem _)
          (hfe 1) (by simp)
        rw [mul_one] at this
        exact (inv_mem_iff).1 this
      map_mul' := fun x y => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        obtain ⟨v, hv, hxy⟩ := conj_mul_eq_of_mem_yamadaQ₅ d (hQ x) (D_le_yamadaD₁ d t (hδf y))
          (huf x) (huf y) (hfe x) (hfe y)
        exact h.inv_mul_mem_V_of_conj_eq d h562 (hδf (x * y)) (mul_mem (hδf x) (hδf y))
          (huf (x * y)) hv (hfe (x * y)) (by rw [coe_mul]; exact hxy) }
  have hψ : ∀ x : yamadaC₅ d t, ψ x = QuotientGroup.mk ⟨δf x, hδf x⟩ := fun _ => rfl
  have hform : ∀ (x : yamadaC₅ d t) (δ : d.D.map L.subtype), (∃ u ∈ yamadaV₁ d t,
      (x : G) * t * (x : G)⁻¹ = t * δ * u) → ψ x = QuotientGroup.mk δ := by
    rintro x δ ⟨u, hu, e⟩
    rw [hψ, QuotientGroup.eq, mem_subgroupOf]
    exact h.inv_mul_mem_V_of_conj_eq d h562 (hδf x) δ.2 (huf x) hu (hfe x) e
  have hker : ψ.ker = (yamadaC₁ d t).subgroupOf (yamadaC₅ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf, hψ, QuotientGroup.eq_one_iff, mem_subgroupOf]
    constructor
    · intro hx
      refine h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 (hQ x) ?_
      rw [show t * (x : G) * t * (x : G)⁻¹ = t * ((x : G) * t * (x : G)⁻¹) by group, hfe x,
        ← mul_assoc, ← mul_assoc, h.t_mul_t, one_mul]
      exact mul_mem (V_le_yamadaV₁ d h562 hx) (huf x)
    · intro hx
      have hmem : (x : G) * t * (x : G)⁻¹ ∈ {z | ∃ c ∈ yamadaC₁ d t, c * t * c⁻¹ = z} :=
        ⟨x, hx, rfl⟩
      rw [(h.yamada_5_3_1_all d).2.2.2.2.1] at hmem
      obtain ⟨v₀, hv₀, e⟩ := hmem
      have h1 := h.inv_mul_mem_V_of_conj_eq d h562 (hδf x) (hVD hv₀) (huf x) (one_mem _) (hfe x)
        (by rw [mul_one]; exact e.symm)
      have h2 : (δf x)⁻¹ ∈ d.V.map L.subtype := by
        have := mul_mem h1 (inv_mem hv₀)
        rwa [mul_inv_cancel_right] at this
      exact (inv_mem_iff).1 h2
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨δ, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨x, hx, u, hu, e⟩ :=
      h.exists_mem_yamadaQ₅_conj_eq_of_mem_D d hNH h561 h562 h591 h592 h593 δ.2
    have hx' : x ∈ yamadaC₅ d t := hCQ ▸ hx
    exact ⟨⟨x, hx'⟩, hform ⟨x, hx'⟩ δ ⟨u, hu, e⟩⟩
  have hC₁n : ((yamadaC₁ d t).subgroupOf (yamadaC₅ d t)).Normal := hker ▸ ψ.normal_ker
  set φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj) with hφdef
  have hφ : ∀ x : yamadaC₅ d t, φ (QuotientGroup.mk x) = ψ x := fun _ => rfl
  refine ⟨hC₁n, hVDn, φ, fun x δ hxδ => (hφ x).trans (hform x δ hxδ), ?_⟩
  intro n hn x δ hxδ
  rw [hφ, hψ, QuotientGroup.eq, mem_subgroupOf] at hxδ
  have hnN := h.centralizer_inf_normalizer_V_le d hn
  have hnC₁ := le_normalizer_yamadaC₁ d t hnN
  have hnV₁ := normalizer_yamadaD₁_le_normalizer_yamadaV₁ d t
    (hNH.1 hnC₁)
  have hx : n * x * n⁻¹ ∈ yamadaC₅ d t :=
    (mem_normalizer_iff.1 (le_normalizer_yamadaC₅ d t hnC₁) x).1 x.2
  have hδ : n * δ * n⁻¹ ∈ d.D.map L.subtype :=
    (mem_normalizer_iff.1 (h.centralizer_inf_normalizer_V_le_normalizer_D d hn) δ).1 δ.2
  refine ⟨hx, hδ, ?_⟩
  rw [hφ]
  refine hform ⟨_, hx⟩ ⟨_, hδ⟩ ?_
  have hnt : n * t = t * n := mem_centralizer_singleton_iff.1 hn.1
  have hnt' : n⁻¹ * t * n = t := by rw [mul_assoc, ← hnt, inv_mul_cancel_left]
  set v := (δ : G)⁻¹ * δf x with hvdef
  have hv : v ∈ d.V.map L.subtype := by
    have := inv_mem hxδ
    rw [coe_mul, coe_inv, mul_inv_rev, inv_inv] at this
    exact this
  refine ⟨n * (v * uf x) * n⁻¹,
    (mem_normalizer_iff.1 hnV₁ _).1 (mul_mem (V_le_yamadaV₁ d h562 hv) (huf x)), ?_⟩
  calc n * x * n⁻¹ * t * (n * x * n⁻¹)⁻¹ = n * x * (n⁻¹ * t * n) * (x : G)⁻¹ * n⁻¹ := by group
    _ = n * ((x : G) * t * (x : G)⁻¹) * n⁻¹ := by rw [hnt']; group
    _ = n * (t * δf x * uf x) * n⁻¹ := by rw [hfe x]
    _ = n * t * n⁻¹ * (n * (δ : G) * n⁻¹) * (n * (v * uf x) * n⁻¹) := by rw [hvdef]; group
    _ = t * (n * (δ : G) * n⁻¹) * (n * (v * uf x) * n⁻¹) := by rw [hnt, mul_inv_cancel_right]

include h hNH h561 h562 h591 h592 h593 in
theorem yamada_5_12 :
    (normalizer (yamadaC₁ d t : Set G) = yamadaC₅ d t ⊔
        (centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) ∧
      ((normalizer (yamadaC₁ d t : Set G) : Subgroup G) : Set G) = (yamadaC₅ d t : Set G) *
        ((centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) :
          Subgroup G) : Set G) ∧
      normalizer (yamadaC₁ d t : Set G) ≤ normalizer (yamadaD₁ d t : Set G) ∧
      yamadaC₅ d t ⊓ centralizer ({t} : Set G) = d.D.map L.subtype ⊔ zpowers t) ∧
    ((∀ x ∈ yamadaC₅ d t, ∃ δ ∈ yamadaD₁ d t, x * t * x⁻¹ = t * δ) ∧
      (∀ δ ∈ yamadaD₁ d t, ∃ x ∈ yamadaC₅ d t, ∃ v ∈ yamadaV₁ d t, x * t * x⁻¹ = t * δ * v) ∧
      ∀ x ∈ yamadaC₅ d t, ∀ y ∈ yamadaD₁ d t, x * y * x⁻¹ * y⁻¹ ∈ yamadaV₁ d t) ∧
    yamadaY₂ d t ≤ yamadaC₅ d t ∧
    (standardComponentOddCore (centralizer ({t} : Set G))).map
        (centralizer ({t} : Set G)).subtype ≤ centralizer (yamadaC₅ d t : Set G) := by
  have hCQ := h.yamadaC₅_eq_yamadaQ₅ d hNH h561 h562 h591 h592 h593
  have hNCV : centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G) ≤
      normalizer (yamadaC₁ d t : Set G) := fun n hn =>
    le_normalizer_yamadaC₁ d t (h.centralizer_inf_normalizer_V_le d hn)
  have hN : normalizer (yamadaC₁ d t : Set G) = yamadaC₅ d t ⊔
      (centralizer ({t} : Set G) ⊓ normalizer ((d.V.map L.subtype : Subgroup G) : Set G)) := by
    refine le_antisymm (fun g hg => ?_) (sup_le (yamadaC₅_le d t) hNCV)
    obtain ⟨x, hx, c, hc, rfl⟩ :=
      h.exists_mul_of_mem_normalizer_yamadaC₁ d hNH h561 h562 h591 h592 h593 hg
    exact mul_mem (mem_sup_left (hCQ ▸ hx)) (mem_sup_right hc)
  refine ⟨⟨hN, ?_, hNH.1, ?_⟩,
    ⟨fun x hx => h.exists_conj_t_eq d hNH h561 h562 (yamadaC₅_le d t hx), fun δ hδ => ?_,
      fun x hx => (mem_yamadaQ₅.1 (hCQ ▸ hx)).2⟩,
    hCQ ▸ h.yamadaY₂_le_yamadaQ₅ d h561 h562 h591 h593, ?_⟩
  · rw [hN]
    exact coe_mul_of_right_le_normalizer_left _ _
      (hNCV.trans (le_normalizer_yamadaC₅ d t))
  · refine le_antisymm (fun x hx => ?_) ?_
    · obtain ⟨hxC₅, hxC⟩ := mem_inf.1 hx
      have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxC
      have hxC₁ : x ∈ yamadaC₁ d t := by
        refine h.mem_yamadaC₁_of_crossed_mem d hNH h561 h562 (hCQ ▸ hxC₅) ?_
        rw [show t * x * t * x⁻¹ = 1 by
          rw [mul_assoc t x t, hxt, ← mul_assoc, h.t_mul_t, one_mul, mul_inv_cancel]]
        exact one_mem _
      rw [← (h.two_core_C₁_all d).2.1]
      exact mem_inf.2 ⟨hxC₁, hxC⟩
    · rw [← (h.two_core_C₁_all d).2.1]
      exact inf_le_inf_right _ (hCQ ▸ h.yamadaC₁_le_yamadaQ₅ d h561 h562)
  · obtain ⟨x, hx, v, hv, e⟩ := h.exists_mem_yamadaQ₅_conj_eq d hNH h561 h562 h591 h592 h593 hδ
    exact ⟨x, hCQ ▸ hx, v, hv, e⟩
  · rw [h.core t h.ht, Subgroup.map_bot]
    exact bot_le

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
