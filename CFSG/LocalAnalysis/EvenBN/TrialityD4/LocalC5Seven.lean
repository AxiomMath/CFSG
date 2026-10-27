module

public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LocalC5Six

public section

namespace CFSG.LocalAnalysis.EvenBN.TrialityD4

open Subgroup CFSG.Open
open scoped Pointwise

namespace Setup

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {f : ℕ} {t : G}

section Basic

omit [Finite G] in
theorem t_not_mem_centralizer_yamadaY₂ (d : TrialityD4Data L (2 ^ f))
    (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
      Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
      yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
      yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype) :
    t ∉ centralizer (yamadaY₂ d t : Set G) := by
  intro ht
  have hY₂C : yamadaY₂ d t ≤ centralizer ({t} : Set G) := fun a ha =>
    mem_centralizer_singleton_iff.2 (mem_centralizer_iff.1 ht a ha)
  have heq : yamadaY₂ d t = d.Y.map L.subtype := by
    rw [← h592.2.2.2.2]
    exact (inf_eq_left.2 hY₂C).symm
  have h3 := congrArg (fun H : Subgroup G => Nat.card H) heq
  simp only [h592.2.1, card_map_of_injective L.subtype_injective, d.card_Y] at h3
  have h2f : 2 ≤ 2 ^ f := d.two_le_q
  have : (2 ^ f) ^ 2 < (2 ^ f) ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  omega

theorem isPGroup_yamadaR₅ (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    IsPGroup 2 (yamadaR₅ d t) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
  have hS : IsPGroup 2 (d.S.map L.subtype) := by
    rw [← hP]
    exact P.isPGroup'.map L.subtype
  exact (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_sup_of_normal_left' hS
    ((h.S_le_normalizer_yamadaC₁ d).trans (le_normalizer_yamadaC₅ d t))

theorem yamadaR₂_inf_L (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f)) :
    yamadaR₂ d t ⊓ L = d.S.map L.subtype := by
  have hSN : d.S.map L.subtype ≤ normalizer (yamadaL₂ d t : Set G) := fun s hs =>
    le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d ⟨h.S_le_centralizer d hs,
      map_le_normalizer_map d.S_le_normalizer_Y hs⟩)
  refine le_antisymm (fun x hx => ?_)
    (le_inf (le_sup_right : d.S.map L.subtype ≤ yamadaR₂ d t) (map_subtype_le _))
  obtain ⟨hxR, hxL⟩ := mem_inf.1 hx
  rw [show yamadaR₂ d t = yamadaL₂ d t ⊔ d.S.map L.subtype from rfl, ← SetLike.mem_coe,
    coe_mul_of_right_le_normalizer_left _ _ hSN, Set.mem_mul] at hxR
  obtain ⟨l, hl, s, hs, rfl⟩ := hxR
  have hsL : s ∈ L := map_subtype_le _ hs
  have hlL : l ∈ L := by
    have := mul_mem hxL (inv_mem hsL)
    rwa [mul_inv_cancel_right] at this
  have hlMt : l ∈ d.M.map L.subtype ⊔ zpowers t := by
    rw [← (h.yamada_5_3_2 d).2.2.2.2.1]
    exact mem_inf.2 ⟨hl, h.L_le_centralizer hlL⟩
  rcases (h.mem_sup_zpowers_iff (map_subtype_le _)).1 hlMt with h1 | h1
  · exact mul_mem (map_mono d.M_le_S h1) hs
  · exfalso
    have := mul_mem (map_subtype_le _ h1) (inv_mem hlL)
    rw [mul_inv_cancel_right] at this
    exact h.t_not_mem_L this

theorem yamadaM₂_eq_inf_centralizer (h : Setup G L f t) (d : TrialityD4Data L (2 ^ f))
    (h591 : yamadaL₂ d t = yamadaM₂ d t ⊔ zpowers t ∧ t ∉ yamadaM₂ d t ∧
      yamadaR₂ d t = yamadaS₂ d t ⊔ zpowers t ∧ t ∉ yamadaS₂ d t)
    (h592 : yamadaV₁ d t ⊓ (yamadaV₁ d t).map (MulAut.conj ((d.v : L) : G)).toMonoidHom = ⊥ ∧
      Nat.card (yamadaY₂ d t) = (2 ^ f) ^ 4 ∧ IsMulCommutative (yamadaY₂ d t) ∧
      yamadaM₂ d t ⊓ centralizer (yamadaM₂ d t : Set G) = yamadaY₂ d t ∧
      yamadaY₂ d t ⊓ centralizer ({t} : Set G) = d.Y.map L.subtype) :
    yamadaM₂ d t = yamadaL₂ d t ⊓ centralizer (yamadaY₂ d t : Set G) := by
  have htM₂ : t ∈ normalizer (yamadaM₂ d t : Set G) :=
    Common.mem_normalizer_sup (h.t_mem_normalizer_map d.M) (h.t_mem_normalizer_yamadaY₂ d)
  have hM₂C : yamadaM₂ d t ≤ centralizer (yamadaY₂ d t : Set G) := fun m hm =>
    mem_centralizer_iff.2 fun y hy => by
      rw [← h592.2.2.2.1] at hy
      exact (mem_centralizer_iff.1 (mem_inf.1 hy).2 m hm).symm
  have hM₂L₂ : yamadaM₂ d t ≤ yamadaL₂ d t := by
    rw [h591.1]
    exact le_sup_left
  refine le_antisymm (le_inf hM₂L₂ hM₂C) fun x hx => ?_
  obtain ⟨hxL₂, hxC⟩ := mem_inf.1 hx
  rw [h591.1] at hxL₂
  rcases (mem_sup_zpowers_iff_of_D4 h.t_mul_t htM₂).1 hxL₂ with h1 | ⟨m, hm, rfl⟩
  · exact h1
  · exfalso
    have := mul_mem (inv_mem (hM₂C hm)) hxC
    rw [inv_mul_cancel_left] at this
    exact t_not_mem_centralizer_yamadaY₂ d h592 this

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
  (h5101 : (Subgroup.upperCentralSeries (yamadaR₂ d t) 1).map (yamadaR₂ d t).subtype =
      d.V.map L.subtype ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 2).map (yamadaR₂ d t).subtype = yamadaY₁ d t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 3).map (yamadaR₂ d t).subtype =
      yamadaW₂ d t ⊔ zpowers t ∧
    (Subgroup.upperCentralSeries (yamadaR₂ d t) 4).map (yamadaR₂ d t).subtype =
      yamadaF₂ d t ⊔ zpowers t)
  (h5102 : CFSG.Open.thompsonSubgroup (yamadaF₂ d t ⊔ zpowers t) = yamadaF₂ d t)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₂_le_yamadaL₃ : yamadaL₂ d t ≤ yamadaL₃ d t := by
  rw [h.yamadaL₃_eq_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102]
  exact h.yamadaL₂_le_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₃_le_normalizer_yamadaV₂ :
    yamadaL₃ d t ≤ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) := fun _ hz =>
  (h.normalizer_yamadaL₂_eq d hNH h561 h562 h591 h592 h593 h5101 h5102).le
    (LieType.BorelTits.pCoreOf_le 2 _ hz)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaL₃_inf_centralizer :
    yamadaL₃ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype ⊔ zpowers t := by
  rw [← (h.yamada_5_3_2 d).2.2.2.2.1]
  refine le_antisymm (fun x hx => ?_) (inf_le_inf_right _
    (h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102))
  obtain ⟨hxL₃, hxC⟩ := mem_inf.1 hx
  have hxV := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hxL₃
  have hxt : x * t = t * x := mem_centralizer_singleton_iff.1 hxC
  have hκ : t * x * t * x⁻¹ ∈ d.Y.map L.subtype := by
    rw [show t * x * t * x⁻¹ = t * (x * t) * x⁻¹ by group, hxt,
      show t * (t * x) * x⁻¹ = t * t by group, h.t_mul_t]
    exact one_mem _
  exact mem_inf.2 ⟨yamadaL₃_inf_le d t (mem_inf.2 ⟨hxL₃,
    (h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102 hxV).1 hκ⟩), hxC⟩

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem conj_t_yamadaL₃ :
    {x | ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = x} =
      (fun y => t * y) '' ((d.W.map L.subtype : Subgroup G) : Set G) := by
  have hL₃ := h.yamadaL₃_eq_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    refine ⟨t * c * t * c⁻¹, h.crossed_mem_W d h562 h592
      (h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hc), ?_⟩
    show t * (t * c * t * c⁻¹) = c * t * c⁻¹
    rw [show t * (t * c * t * c⁻¹) = (t * t) * c * t * c⁻¹ by group, h.t_mul_t, one_mul]
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨p, hp, y, hy, e⟩ := h.exists_mem_translationsW₂_crossed d hNH h561 h562 h591 h592 h593
      h5101 h5102 hw
    rw [← hL₃] at hp
    have hpY := h.normalizer_yamadaV₂_le_normalizer_Y d hNH h561 h562 h591 h592 h593 h5101 h5102
      (h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hp)
    have hy' : p⁻¹ * y⁻¹ * p ∈ d.Y.map L.subtype := by
      have := (mem_normalizer_iff.1 (inv_mem hpY) y⁻¹).1 (inv_mem hy)
      rwa [inv_inv] at this
    have hmem : t * (p⁻¹ * y⁻¹ * p) ∈ {x | ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = x} := by
      rw [(h.yamada_5_3_2 d).2.2.2.2.2.1]
      exact ⟨_, hy', rfl⟩
    obtain ⟨l, hl, el⟩ : ∃ c ∈ yamadaL₂ d t, c * t * c⁻¹ = t * (p⁻¹ * y⁻¹ * p) := hmem
    refine ⟨p * l, mul_mem hp
      (h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102 hl), ?_⟩
    have ep : p * t * p⁻¹ = t * (w * y) := by
      rw [← e, show t * (t * p * t * p⁻¹) = (t * t) * p * t * p⁻¹ by group, h.t_mul_t, one_mul]
    calc p * l * t * (p * l)⁻¹ = p * (l * t * l⁻¹) * p⁻¹ := by group
      _ = p * (t * (p⁻¹ * y⁻¹ * p)) * p⁻¹ := by rw [el]
      _ = (p * t * p⁻¹) * y⁻¹ := by group
      _ = t * (w * y) * y⁻¹ := by rw [ep]
      _ = t * w := by group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem exists_mul_of_mem_normalizer_yamadaV₂ {g : G}
    (hg : g ∈ normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G)) :
    ∃ c ∈ yamadaL₃ d t, ∃ x ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G), g = c * x := by
  have hmem : g * t * g⁻¹ ∈ {x | ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = x} := by
    rw [h.conj_t_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102]
    refine ⟨t * g * t * g⁻¹, h.crossed_mem_W d h562 h592 hg, ?_⟩
    show t * (t * g * t * g⁻¹) = g * t * g⁻¹
    rw [show t * (t * g * t * g⁻¹) = (t * t) * g * t * g⁻¹ by group, h.t_mul_t, one_mul]
  obtain ⟨c, hc, e⟩ : ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = g * t * g⁻¹ := hmem
  have hcV := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hc
  refine ⟨c, hc, c⁻¹ * g, mem_inf.2 ⟨mem_centralizer_singleton_iff.2 ?_,
    h.normalizer_yamadaV₂_le_normalizer_Y d hNH h561 h562 h591 h592 h593 h5101 h5102
      (mul_mem (inv_mem hcV) hg)⟩, by rw [mul_inv_cancel_left]⟩
  calc c⁻¹ * g * t = c⁻¹ * (g * t * g⁻¹) * g := by group
    _ = c⁻¹ * (c * t * c⁻¹) * g := by rw [e]
    _ = t * (c⁻¹ * g) := by group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaL₂_eq_sup :
    normalizer (yamadaL₂ d t : Set G) = yamadaL₃ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) := by
  refine le_antisymm (fun g hg => ?_) (sup_le (LieType.BorelTits.pCoreOf_le 2 _)
    fun x hx => le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d hx))
  obtain ⟨c, hc, x, hx, rfl⟩ := h.exists_mul_of_mem_normalizer_yamadaV₂ d hNH h561 h562 h591 h592
    h593 h5101 h5102 ((h.normalizer_yamadaL₂_eq d hNH h561 h562 h591 h592 h593 h5101 h5102).le hg)
  exact mul_mem (mem_sup_left hc) (mem_sup_right hx)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaL₂_eq_tW :
    normalizer (yamadaL₂ d t : Set G) =
      normalizer ((d.W.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) := by
  have hNeq := h.normalizer_yamadaL₂_eq d hNH h561 h562 h591 h592 h593 h5101 h5102
  refine le_antisymm (hNeq.le.trans (h.normalizer_yamadaV₂_le d h562 h592).2.1) fun g hg => ?_
  have hWL : d.W.map L.subtype ≤ L := map_subtype_le _
  have hgt : g * t * g⁻¹ ∈ d.W.map L.subtype ⊔ zpowers t :=
    (mem_normalizer_iff.1 hg t).1 (mem_sup_right (mem_zpowers t))
  have hw : t * (g * t * g⁻¹) ∈ d.W.map L.subtype := by
    rcases (h.mem_sup_zpowers_iff hWL).1 hgt with h1 | h1
    · exact absurd (hWL h1) (h.conj_not_mem_L d g)
    · exact h1
  have hmem : g * t * g⁻¹ ∈ {x | ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = x} := by
    rw [h.conj_t_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102]
    refine ⟨_, hw, ?_⟩
    show t * (t * (g * t * g⁻¹)) = g * t * g⁻¹
    rw [← mul_assoc, h.t_mul_t, one_mul]
  obtain ⟨c, hc, e⟩ : ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = g * t * g⁻¹ := hmem
  have hcV := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hc
  have hcW : c ∈ normalizer ((d.W.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    (h.normalizer_yamadaV₂_le d h562 h592).2.1 hcV
  have hxC : c⁻¹ * g ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.2 (by
    calc c⁻¹ * g * t = c⁻¹ * (g * t * g⁻¹) * g := by group
      _ = c⁻¹ * (c * t * c⁻¹) * g := by rw [e]
      _ = t * (c⁻¹ * g) := by group)
  have hxtW : c⁻¹ * g ∈ normalizer ((d.W.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) :=
    mul_mem (inv_mem hcW) hg
  have hxL := h.centralizer_le_normalizer hxC
  have hxW : c⁻¹ * g ∈ normalizer ((d.W.map L.subtype : Subgroup G) : Set G) := by
    refine mem_normalizer_fintype fun w hw => ?_
    have h1 : c⁻¹ * g * w * (c⁻¹ * g)⁻¹ ∈ d.W.map L.subtype ⊔ zpowers t :=
      (mem_normalizer_iff.1 hxtW w).1 (mem_sup_left hw)
    have h2 : c⁻¹ * g * w * (c⁻¹ * g)⁻¹ ∈ L := (mem_normalizer_iff.1 hxL w).1 (hWL hw)
    rcases (h.mem_sup_zpowers_iff hWL).1 h1 with h3 | h3
    · exact h3
    · exfalso
      have := mul_mem (hWL h3) (inv_mem h2)
      rw [mul_inv_cancel_right] at this
      exact h.t_not_mem_L this
  have hxY : c⁻¹ * g ∈ centralizer ({t} : Set G) ⊓
      normalizer ((d.Y.map L.subtype : Subgroup G) : Set G) := by
    rw [h.centralizer_inf_normalizer_Y_eq_W d]
    exact mem_inf.2 ⟨hxC, hxW⟩
  have := mul_mem (hNeq.ge hcV)
    (le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d hxY))
  rwa [mul_inv_cancel_left] at this

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaL₂_le_normalizer_yamadaM₂ :
    normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₂ d t : Set G) := by
  intro g hg
  have hgY₂ := h.normalizer_yamadaV₂_le_normalizer_yamadaY₂ d hNH h561 h562 h591 h592 h593 h5101
    h5102 ((h.normalizer_yamadaL₂_eq d hNH h561 h562 h591 h592 h593 h5101 h5102).le hg)
  rw [h.yamadaM₂_eq_inf_centralizer d h591 h592]
  refine Common.mem_normalizer_inf hg (mem_normalizer_fintype fun x hx => ?_)
  rw [SetLike.mem_coe, mem_centralizer_iff] at hx ⊢
  intro y hy
  have hy' : g⁻¹ * y * g ∈ yamadaY₂ d t := by
    have := (mem_normalizer_iff.1 (inv_mem hgY₂) y).1 hy
    rwa [inv_inv] at this
  have := hx _ hy'
  calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
    _ = g * x * g⁻¹ * y := by group

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamada_5_17_1 :
    normalizer (yamadaL₂ d t : Set G) =
        normalizer ((d.W.map L.subtype ⊔ zpowers t : Subgroup G) : Set G) ∧
      normalizer (yamadaL₂ d t : Set G) = yamadaL₃ d t ⊔ (centralizer ({t} : Set G) ⊓
        normalizer ((d.Y.map L.subtype : Subgroup G) : Set G)) ∧
      normalizer (yamadaL₂ d t : Set G) ≤ normalizer (yamadaM₂ d t : Set G) ∧
      yamadaL₃ d t ⊓ centralizer ({t} : Set G) = d.M.map L.subtype ⊔ zpowers t ∧
      {x | ∃ c ∈ yamadaL₃ d t, c * t * c⁻¹ = x} =
        (fun y => t * y) '' ((d.W.map L.subtype : Subgroup G) : Set G) :=
  ⟨h.normalizer_yamadaL₂_eq_tW d hNH h561 h562 h591 h592 h593 h5101 h5102,
    h.normalizer_yamadaL₂_eq_sup d hNH h561 h562 h591 h592 h593 h5101 h5102,
    h.normalizer_yamadaL₂_le_normalizer_yamadaM₂ d hNH h561 h562 h591 h592 h593 h5101 h5102,
    h.yamadaL₃_inf_centralizer d hNH h561 h562 h591 h592 h593 h5101 h5102,
    h.conj_t_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102⟩

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamada_5_17_1_module :
    ∃ _ : ((yamadaL₂ d t).subgroupOf (yamadaL₃ d t)).Normal,
      ∃ _ : ((d.Y.map L.subtype).subgroupOf (d.W.map L.subtype)).Normal,
      ∃ φ : yamadaL₃ d t ⧸ (yamadaL₂ d t).subgroupOf (yamadaL₃ d t) ≃*
          d.W.map L.subtype ⧸ (d.Y.map L.subtype).subgroupOf (d.W.map L.subtype),
        (∀ x : yamadaL₃ d t, ∃ hw : t * (x : G) * t * (x : G)⁻¹ ∈ d.W.map L.subtype,
          φ (QuotientGroup.mk x) = QuotientGroup.mk ⟨_, hw⟩) ∧
        ∀ c ∈ centralizer ({t} : Set G) ⊓ normalizer ((d.Y.map L.subtype : Subgroup G) : Set G),
          ∀ x : yamadaL₃ d t, ∃ hx : c * (x : G) * c⁻¹ ∈ yamadaL₃ d t,
            ∃ hw : c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹ ∈ d.W.map L.subtype,
              φ (QuotientGroup.mk ⟨c * (x : G) * c⁻¹, hx⟩) = QuotientGroup.mk ⟨_, hw⟩ := by
  have hL₃eq := h.yamadaL₃_eq_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hL₃V := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hN₁ : ((yamadaL₂ d t).subgroupOf (yamadaL₃ d t)).Normal :=
    normal_subgroupOf_of_le_normalizer (LieType.BorelTits.pCoreOf_le 2 _)
  have hN₂ : ((d.Y.map L.subtype).subgroupOf (d.W.map L.subtype)).Normal :=
    normal_subgroupOf_of_le_normalizer
      (map_le_normalizer_map (d.W_le_S.trans d.S_le_normalizer_Y))
  have hκW : ∀ x : yamadaL₃ d t, t * (x : G) * t * (x : G)⁻¹ ∈ d.W.map L.subtype := fun x =>
    h.crossed_mem_W d h562 h592 (hL₃V x.2)
  have hPE : ∀ x : yamadaL₃ d t, (x : G) ∈ centralizerW₂Y₂ d t := fun x =>
    ((h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 (hL₃eq.le x.2)).1
  let ψ : yamadaL₃ d t →* d.W.map L.subtype ⧸ (d.Y.map L.subtype).subgroupOf (d.W.map L.subtype) :=
    MonoidHom.mk' (fun x => QuotientGroup.mk ⟨_, hκW x⟩) fun x y => by
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
      obtain ⟨y₀, hy₀, e⟩ := h.crossed_mul_mem_Y d hNH h561 h562 h591 h592 h593 h5101 h5102 (hPE x)
        (hL₃V y.2)
      show (t * ((x : G) * y) * t * ((x : G) * y)⁻¹)⁻¹ *
        ((t * x * t * (x : G)⁻¹) * (t * y * t * (y : G)⁻¹)) ∈ d.Y.map L.subtype
      rw [e, show ∀ a b c : G, (a * b * c)⁻¹ * (a * b) = c⁻¹ from fun a b c => by group]
      exact inv_mem hy₀
  have hker : ψ.ker = (yamadaL₂ d t).subgroupOf (yamadaL₃ d t) := by
    ext x
    rw [MonoidHom.mem_ker, mem_subgroupOf]
    show (QuotientGroup.mk ⟨_, hκW x⟩ :
      d.W.map L.subtype ⧸ (d.Y.map L.subtype).subgroupOf (d.W.map L.subtype)) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, mem_subgroupOf]
    show t * (x : G) * t * (x : G)⁻¹ ∈ d.Y.map L.subtype ↔ (x : G) ∈ yamadaL₂ d t
    rw [h.crossed_mem_Y_iff d hNH h561 h562 h591 h592 h593 h5101 h5102 (hL₃V x.2)]
    exact ⟨fun hN => yamadaL₃_inf_le d t (mem_inf.2 ⟨x.2, hN⟩), fun hl => yamadaL₂_le d t hl⟩
  have hsurj : Function.Surjective ψ := by
    intro z
    obtain ⟨⟨w, hw⟩, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨p, hp, y, hy, e⟩ := h.exists_mem_translationsW₂_crossed d hNH h561 h562 h591 h592 h593
      h5101 h5102 hw
    rw [← hL₃eq] at hp
    refine ⟨⟨p, hp⟩, ?_⟩
    show (QuotientGroup.mk ⟨_, hκW ⟨p, hp⟩⟩ :
      d.W.map L.subtype ⧸ (d.Y.map L.subtype).subgroupOf (d.W.map L.subtype)) =
        QuotientGroup.mk ⟨w, hw⟩
    rw [QuotientGroup.eq, mem_subgroupOf]
    show (t * p * t * p⁻¹)⁻¹ * w ∈ d.Y.map L.subtype
    rw [e, show (w * y)⁻¹ * w = y⁻¹ by group]
    exact inv_mem hy
  let φ := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ hsurj)
  refine ⟨hN₁, hN₂, φ, fun x => ⟨hκW x, rfl⟩, fun c hc x => ?_⟩
  have hcL₃ : c ∈ normalizer (yamadaL₃ d t : Set G) :=
    LieType.BorelTits.le_normalizer_pCoreOf 2 _
      (le_normalizer_yamadaL₂ d t (h.centralizer_inf_normalizer_Y_le d hc))
  have hx : c * (x : G) * c⁻¹ ∈ yamadaL₃ d t := (mem_normalizer_iff.1 hcL₃ x).1 x.2
  have hct : c * t = t * c := mem_centralizer_singleton_iff.1 (mem_inf.1 hc).1
  have he : t * (c * (x : G) * c⁻¹) * t * (c * (x : G) * c⁻¹)⁻¹ =
      c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹ := by
    have hct' : c⁻¹ * t * c = t := by rw [mul_assoc, ← hct, inv_mul_cancel_left]
    calc t * (c * (x : G) * c⁻¹) * t * (c * (x : G) * c⁻¹)⁻¹ =
          t * c * x * (c⁻¹ * t * c) * (x : G)⁻¹ * c⁻¹ := by group
      _ = c * t * x * t * (x : G)⁻¹ * c⁻¹ := by rw [hct', ← hct]
      _ = c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹ := by group
  have hw : c * (t * (x : G) * t * (x : G)⁻¹) * c⁻¹ ∈ d.W.map L.subtype := by
    rw [← he]
    exact hκW ⟨_, hx⟩
  refine ⟨hx, hw, ?_⟩
  show (QuotientGroup.mk ⟨_, hκW ⟨_, hx⟩⟩ :
    d.W.map L.subtype ⧸ (d.Y.map L.subtype).subgroupOf (d.W.map L.subtype)) =
      QuotientGroup.mk ⟨_, hw⟩
  exact congrArg QuotientGroup.mk (Subtype.ext he)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem normalizer_yamadaR₂_eq :
    normalizer (yamadaR₂ d t : Set G) = yamadaR₃ d t ⊔ (centralizer ({t} : Set G) ⊓
      normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) := by
  have hR₃ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.1
  refine le_antisymm (fun g hg => ?_) (sup_le hR₃.2 fun c hc => ?_)
  · have hgV := (mem_inf.1 (normalizer_yamadaR₂_le d h592 h5101 h5102 hg)).1
    obtain ⟨x, hx, l, hl, e⟩ := h.exists_conj_t_eq_mul_of_mem_W d hNH h561 h562 h591 h592 h593
      h5101 h5102 (h.crossed_mem_W d h562 h592 hgV)
    have hlR₂ : l ∈ yamadaR₂ d t := (le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) hl
    have hxl : x * l ∈ normalizer (yamadaR₂ d t : Set G) :=
      mul_mem (hR₃.2 hx) (le_normalizer hlR₂)
    have hcN : (x * l)⁻¹ * g ∈ normalizer (yamadaR₂ d t : Set G) := mul_mem (inv_mem hxl) hg
    have e' : x * l * t * (x * l)⁻¹ = g * t * g⁻¹ := by
      rw [e, show t * (t * g * t * g⁻¹) = (t * t) * g * t * g⁻¹ by group, h.t_mul_t, one_mul]
    have hcC : (x * l)⁻¹ * g ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (x * l)⁻¹ * g * t = (x * l)⁻¹ * (g * t * g⁻¹) * g := by group
        _ = (x * l)⁻¹ * (x * l * t * (x * l)⁻¹) * g := by rw [e']
        _ = t * ((x * l)⁻¹ * g) := by group
    have hcS : (x * l)⁻¹ * g ∈ normalizer ((d.S.map L.subtype : Subgroup G) : Set G) := by
      rw [← h.yamadaR₂_inf_L d]
      exact Common.mem_normalizer_inf hcN (h.centralizer_le_normalizer hcC)
    have := mul_mem (mem_sup_left (mul_mem hx (hR₃.1 hlR₂)) :
        x * l ∈ yamadaR₃ d t ⊔ (centralizer ({t} : Set G) ⊓
          normalizer ((d.S.map L.subtype : Subgroup G) : Set G)))
      (mem_sup_right (mem_inf.2 ⟨hcC, hcS⟩))
    rwa [mul_inv_cancel_left] at this
  · have hR := yamadaR_eq_of_eq d (h.centralizer_L_inf_of_data d)
    have hcR : c ∈ normalizer (yamadaR d t : Set G) := by
      rw [hR]
      exact Common.mem_normalizer_sup hc.2
        (mem_normalizer_zpowers_of_comm_D4 (mem_centralizer_singleton_iff.1 hc.1))
    exact h.normalizer_yamadaR_le_normalizer_yamadaR₂ d hcR

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamadaR₃_eq : yamadaR₃ d t = yamadaL₃ d t ⊔ d.S.map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hR₃ := (h.yamada_5_14 d hNH h561 h562 h591 h592 h593).2.2.2.1
  have hNeq := h.normalizer_yamadaL₂_eq d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hL₃eq := h.yamadaL₃_eq_translationsW₂ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hL₂L₃ := h.yamadaL₂_le_yamadaL₃ d hNH h561 h562 h591 h592 h593 h5101 h5102
  have hSR₃ : d.S.map L.subtype ≤ yamadaR₃ d t :=
    (le_sup_right : d.S.map L.subtype ≤ yamadaR₂ d t).trans hR₃.1
  have hNL₃ : normalizer ((yamadaW₂ d t ⊔ zpowers t : Subgroup G) : Set G) ≤
      normalizer (yamadaL₃ d t : Set G) :=
    hNeq.ge.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hR₃N : yamadaR₃ d t ≤ normalizer (yamadaL₃ d t : Set G) := fun x hx =>
    hNL₃ (mem_inf.1 (h.yamadaR₃_le_normalizer d hNH h561 h562 h591 h592 h593 h5101 h5102 hx)).1
  have hSN : d.S.map L.subtype ≤ normalizer (yamadaL₃ d t : Set G) := hSR₃.trans hR₃N
  have hR₃p : IsPGroup 2 (yamadaR₃ d t) := (h.isPGroup_yamadaR₅ d).to_le inf_le_left
  have hTp : IsPGroup 2 (yamadaL₃ d t ⊔ yamadaR₃ d t : Subgroup G) :=
    (LieType.BorelTits.pCoreOf_isPGroup 2 _).to_sup_of_normal_left' hR₃p hR₃N
  have hTL : ∀ s ∈ yamadaL₃ d t ⊔ yamadaR₃ d t, s ∈ L → s ∈ d.S.map L.subtype := by
    intro s hs hsL
    obtain ⟨P, hP⟩ := d.exists_sylow_eq_S
    have hST : (P : Subgroup L) ≤ (yamadaL₃ d t ⊔ yamadaR₃ d t).comap L.subtype := by
      rw [hP]
      exact fun s hs => mem_sup_right (hSR₃ ⟨s, hs, rfl⟩)
    have hTeq := P.is_maximal' hTp.comap_subtype hST
    have hs' : (⟨s, hsL⟩ : L) ∈ (yamadaL₃ d t ⊔ yamadaR₃ d t).comap L.subtype := hs
    rw [hTeq, hP] at hs'
    exact ⟨_, hs', rfl⟩
  have hle : yamadaR₃ d t ≤ yamadaL₃ d t ⊔ d.S.map L.subtype := by
    intro x hx
    have hxX := h.yamadaR₃_le_centralizerW₂Y₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hx
    have hxV := centralizerW₂Y₂_le d t hxX
    obtain ⟨p, hp, y, hy, e⟩ := h.exists_mem_translationsW₂_crossed d hNH h561 h562 h591 h592 h593
      h5101 h5102 (h.crossed_mem_W d h562 h592 hxV)
    have hpX := ((h.mem_translationsW₂_iff d hNH h561 h562 h591 h592 h593 h5101 h5102).1 hp).1
    have hpV := centralizerW₂Y₂_le d t hpX
    have hk : p⁻¹ * x ∈ kernelTW₂ d t := mem_inf.2 ⟨mul_mem (inv_mem hpX) hxX,
      h.inv_mul_mem_normalizer_tY d hNH h561 h562 h591 h592 h593 h5101 h5102 hpV hxV hy e⟩
    have hBL₂ : d.leviLong.map L.subtype ≤ normalizer (yamadaL₂ d t : Set G) := fun b hb =>
      le_normalizer_yamadaL₂ d t (mem_inf.1 (h.leviLong_le_kernelTW₂ d hNH h561 h562 h591 h592
        h593 h5101 h5102 hb)).2
    have hk' := h.kernelTW₂_le d hNH h561 h562 h591 h592 h593 h5101 h5102 hk
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hBL₂, Set.mem_mul] at hk'
    obtain ⟨l, hl, s, hs, els⟩ := hk'
    rw [← hL₃eq] at hp
    have hsT : s ∈ yamadaL₃ d t ⊔ yamadaR₃ d t := by
      have : (p * l)⁻¹ * x ∈ yamadaL₃ d t ⊔ yamadaR₃ d t :=
        mul_mem (inv_mem (mem_sup_left (mul_mem hp (hL₂L₃ hl)))) (mem_sup_right hx)
      rwa [mul_inv_rev, mul_assoc, ← els, inv_mul_cancel_left] at this
    have hsS := hTL s hsT (map_subtype_le _ hs)
    have hx' : x = (p * l) * s := by rw [mul_assoc, els, mul_inv_cancel_left]
    rw [hx']
    exact mul_mem (mem_sup_left (mul_mem hp (hL₂L₃ hl))) (mem_sup_right hsS)
  have hL₃R₃ : yamadaL₃ d t ≤ yamadaR₃ d t := by
    intro z hz
    have hzV := h.yamadaL₃_le_normalizer_yamadaV₂ d hNH h561 h562 h591 h592 h593 h5101 h5102 hz
    obtain ⟨g, hg, l, hl, e⟩ := h.exists_conj_t_eq_mul_of_mem_W d hNH h561 h562 h591 h592 h593
      h5101 h5102 (h.crossed_mem_W d h562 h592 hzV)
    have hlR₃ : l ∈ yamadaR₃ d t := hR₃.1 ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) hl)
    have e' : g * l * t * (g * l)⁻¹ = z * t * z⁻¹ := by
      rw [e, show t * (t * z * t * z⁻¹) = (t * t) * z * t * z⁻¹ by group, h.t_mul_t, one_mul]
    have hcC : (g * l)⁻¹ * z ∈ centralizer ({t} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      calc (g * l)⁻¹ * z * t = (g * l)⁻¹ * (z * t * z⁻¹) * z := by group
        _ = (g * l)⁻¹ * (g * l * t * (g * l)⁻¹) * z := by rw [e']
        _ = t * ((g * l)⁻¹ * z) := by group
    have hcT : (g * l)⁻¹ * z ∈ yamadaL₃ d t ⊔ d.S.map L.subtype :=
      sup_le le_sup_left hle (mul_mem (inv_mem (mem_sup_right (mul_mem hg hlR₃))) (mem_sup_left hz))
    rw [← SetLike.mem_coe, coe_mul_of_right_le_normalizer_left _ _ hSN, Set.mem_mul] at hcT
    obtain ⟨l', hl', s, hs, els⟩ := hcT
    have hl'C : l' ∈ centralizer ({t} : Set G) := by
      have := mul_mem hcC (inv_mem (h.S_le_centralizer d hs))
      rwa [← els, mul_inv_cancel_right] at this
    have hl'R₃ : l' ∈ yamadaR₃ d t := by
      have hl'M : l' ∈ d.M.map L.subtype ⊔ zpowers t := by
        rw [← h.yamadaL₃_inf_centralizer d hNH h561 h562 h591 h592 h593 h5101 h5102]
        exact mem_inf.2 ⟨hl', hl'C⟩
      exact hR₃.1 ((le_sup_left : yamadaL₂ d t ≤ yamadaR₂ d t) (h.tM_le_yamadaL₂ d hl'M))
    have hz' : z = (g * l) * (l' * s) := by rw [els, mul_inv_cancel_left]
    rw [hz']
    exact mul_mem (mul_mem hg hlR₃) (mul_mem hl'R₃ (hSR₃ hs))
  exact le_antisymm hle (sup_le hL₃R₃ hSR₃)

include h hNH h561 h562 h591 h592 h593 h5101 h5102 in
theorem yamada_5_17_2 :
    normalizer (yamadaR₂ d t : Set G) = yamadaR₃ d t ⊔ (centralizer ({t} : Set G) ⊓
        normalizer ((d.S.map L.subtype : Subgroup G) : Set G)) ∧
      yamadaR₃ d t = yamadaL₃ d t ⊔ d.S.map L.subtype :=
  ⟨h.normalizer_yamadaR₂_eq d hNH h561 h562 h591 h592 h593 h5101 h5102,
    h.yamadaR₃_eq d hNH h561 h562 h591 h592 h593 h5101 h5102⟩

end Main

end Setup

end CFSG.LocalAnalysis.EvenBN.TrialityD4
