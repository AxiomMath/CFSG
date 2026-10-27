module

public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.C9Orbit
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.WeakClosure
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntClassBraid
public import CFSG.LocalAnalysis.EvenSmallLie.UnitarySix.HuntSylow
public import CFSG.LocalAnalysis.EvenSmallLie.ThreeTransposition.Section24Central

public section

namespace CFSG.EvenSmallLie.UnitarySix.Hunt

open Subgroup CFSG.Fischer ToddOrbit

variable {G : Type} [Group G]

@[expose] def lclass (L : Subgroup G) (a : G) : Set G := {s | ∃ h ∈ L, h⁻¹ * a * h = s}

theorem conj_mem_lclass {L : Subgroup G} {a s g : G} (hg : g ∈ L) (hs : s ∈ lclass L a) :
    g * s * g⁻¹ ∈ lclass L a := by
  obtain ⟨h, hh, rfl⟩ := hs
  exact ⟨h * g⁻¹, L.mul_mem hh (L.inv_mem hg), by group⟩

theorem lclass_subset {L : Subgroup G} {a : G} (ha : a ∈ L) : lclass L a ⊆ L := by
  rintro _ ⟨h, hh, rfl⟩
  exact L.mul_mem (L.mul_mem (L.inv_mem hh) ha) hh

theorem isConj_of_mem_lclass {L E : Subgroup G} {t a s : G} (ha : a ∈ orb E t)
    (hs : s ∈ lclass L a) : IsConj t s := by
  obtain ⟨n, -, rfl⟩ := ha
  obtain ⟨h, -, rfl⟩ := hs
  exact isConj_iff.2 ⟨(n * h)⁻¹, by group⟩

section Class

variable {t : G} {L E : Subgroup G} {p : L →* Equiv.Perm (Fin 693)}

theorem t_notMem_lclass
    (H : ToddOrbit.Hyp t L E p) {a : G} (hat : a ≠ t) : t ∉ lclass L a := by
  rintro ⟨h, hh, e⟩
  apply hat
  calc a = h * (h⁻¹ * a * h) * h⁻¹ := by group
    _ = t := by rw [e, H.comm_t hh, mul_inv_cancel_right]

theorem mul_t_of_mem_lclass
    (H : ToddOrbit.Hyp t L E p) {a b : G} (hb : b ∈ lclass L a) :
    ∃ h ∈ L, h⁻¹ * (a * t) * h = b * t := by
  obtain ⟨h, hh, rfl⟩ := hb
  refine ⟨h, hh, ?_⟩
  calc h⁻¹ * (a * t) * h = h⁻¹ * a * (t * h) := by group
    _ = h⁻¹ * a * (h * t) := by rw [H.comm_t hh]
    _ = h⁻¹ * a * h * t := by group

theorem mul_t_notMem_lclass
    (H : ToddOrbit.Hyp t L E p) {a : G} (ha : a ∈ orb E t)
    (hnc : ∀ g : G, g⁻¹ * t * g ≠ a * t) {b : G} (hb : b ∈ lclass L a) :
    b * t ∉ lclass L a := by
  rintro ⟨k, -, e⟩
  obtain ⟨h, -, e'⟩ := mul_t_of_mem_lclass H hb
  obtain ⟨n, -, rfl⟩ := ha
  apply hnc (n * k * h⁻¹)
  calc (n * k * h⁻¹)⁻¹ * t * (n * k * h⁻¹) = h * (k⁻¹ * (n⁻¹ * t * n) * k) * h⁻¹ := by group
    _ = h * (h⁻¹ * (n⁻¹ * t * n * t) * h) * h⁻¹ := by rw [e, e']
    _ = n⁻¹ * t * n * t := by group

theorem conj_centralizer_iff
    (H : ToddOrbit.Hyp t L E p) (D : DavisSolomonFacts G t L E)
    (hHL : centralizer ({t} : Set G) = L) {a : G} (ha : a ∈ orb E t)
    (horb : orb E t = insert t {s | ∃ ℓ ∈ normalizer (E : Set G) ⊓ L, ℓ⁻¹ * a * ℓ = s})
    (s : G) : (IsConj t s ∧ s * t = t * s) ↔ s = t ∨ s ∈ lclass L a := by
  constructor
  · rintro ⟨hc, hst⟩
    have hsL : s ∈ L := by
      rw [← hHL]
      exact mem_centralizer_singleton_iff.2 hst
    have h2 : orderOf s = 2 := by
      obtain ⟨c, hc'⟩ := hc
      rw [← SemiconjBy.orderOf_eq _ hc', H.orderOf_t]
    obtain ⟨c, hcs⟩ := isConj_iff.1 hc
    obtain ⟨l, hl, hlE⟩ := D.fuse s hsL h2
    have hmem : l⁻¹ * s * l ∈ orb E t := by
      have e : (c⁻¹ * l)⁻¹ * t * (c⁻¹ * l) = l⁻¹ * s * l := by rw [← hcs]; group
      obtain ⟨n, hn, hn'⟩ := H.fusion (c⁻¹ * l) (e ▸ hlE)
      exact ⟨n, hn, hn'.symm.trans e⟩
    rw [horb] at hmem
    rcases hmem with h | ⟨ℓ, hℓ, e⟩
    · left
      calc s = l * (l⁻¹ * s * l) * l⁻¹ := by group
        _ = t := by rw [h, H.comm_t hl, mul_inv_cancel_right]
    · right
      refine ⟨ℓ * l⁻¹, L.mul_mem hℓ.2 (L.inv_mem hl), ?_⟩
      calc (ℓ * l⁻¹)⁻¹ * a * (ℓ * l⁻¹) = l * (ℓ⁻¹ * a * ℓ) * l⁻¹ := by group
        _ = s := by rw [e]; group
  · rintro (rfl | hs)
    · exact ⟨IsConj.refl s, rfl⟩
    · refine ⟨isConj_of_mem_lclass ha hs, mem_centralizer_singleton_iff.1 ?_⟩
      exact H.le_centralizer (lclass_subset (H.orb_subset_L ha) hs)

theorem exists_pe_eq_tvP
    (H : ToddOrbit.Hyp t L E p) {a : G} (ha : a ∈ L) (hpa : pe p a = j1)
    {s : G} (hs : s ∈ lclass L a) : ∃ m, pe p s = tvP m := by
  obtain ⟨h, hh, rfl⟩ := hs
  refine ⟨(pe p h)⁻¹ 0, ?_⟩
  have e := conj_j1_eq (T46.inv_mem (H.pe_mem_T46 h))
  rw [inv_inv] at e
  rw [pe_mul p (L.mul_mem (L.inv_mem hh) ha) hh, pe_mul p (L.inv_mem hh) ha, pe_inv p hh, hpa, e]

theorem pe_image_lclass
    (H : ToddOrbit.Hyp t L E p) {a : G} (ha : a ∈ L) (hpa : pe p a = j1) :
    pe p '' lclass L a = Set.range tvP := by
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨m, hm⟩ := exists_pe_eq_tvP H ha hpa hs
    exact ⟨m, hm.symm⟩
  · rintro ⟨m, rfl⟩
    obtain ⟨g, hg, hgm⟩ := exists_conj_j1 m
    obtain ⟨h, hh, hph⟩ := H.exists_lift (T46.inv_mem hg)
    refine ⟨h⁻¹ * a * h, ⟨h, hh, rfl⟩, ?_⟩
    rw [pe_mul p (L.mul_mem (L.inv_mem hh) ha) hh, pe_mul p (L.inv_mem hh) ha, pe_inv p hh, hpa,
      hph, inv_inv, hgm]

theorem injOn_pe_lclass
    (H : ToddOrbit.Hyp t L E p) {a : G} (ha : a ∈ orb E t)
    (hnc : ∀ g : G, g⁻¹ * t * g ≠ a * t) : Set.InjOn (pe p) (lclass L a) := by
  intro b hb b' hb' e
  have haL := H.orb_subset_L ha
  rcases (H.pe_eq_pe_iff (lclass_subset haL hb) (lclass_subset haL hb')).1 e.symm with h | h
  · exact h.symm
  · exact absurd (h ▸ hb') (mul_t_notMem_lclass H ha hnc hb)

theorem ncard_lclass
    (H : ToddOrbit.Hyp t L E p) {a : G} (ha : a ∈ orb E t) (hpa : pe p a = j1)
    (hnc : ∀ g : G, g⁻¹ * t * g ≠ a * t) : (lclass L a).ncard = 693 := by
  rw [← (injOn_pe_lclass H ha hnc).ncard_image, pe_image_lclass H (H.orb_subset_L ha) hpa,
    Set.ncard_range_of_injective tvP_injective, Nat.card_eq_fintype_card, Fintype.card_fin]

theorem orderOf_t_L
    (H : ToddOrbit.Hyp t L E p) : orderOf (⟨t, H.t_mem⟩ : L) = 2 := by
  rw [← Subgroup.orderOf_coe]
  exact H.orderOf_t

theorem ker_eq_zpowers
    (H : ToddOrbit.Hyp t L E p) : p.ker = zpowers (⟨t, H.t_mem⟩ : L) := by
  ext y
  rw [MonoidHom.mem_ker, H.ker y, ThreeTransposition.mem_zpowers_iff_of_mul_self
    (Subtype.ext H.t_mul_t : (⟨t, H.t_mem⟩ : L) * ⟨t, H.t_mem⟩ = 1)]
  constructor
  · rintro (h | h)
    · exact Or.inl (Subtype.ext h)
    · exact Or.inr (Subtype.ext h)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

theorem isThreeTranspositionSet_lclass
    (H : ToddOrbit.Hyp t L E p) {a : G} (ha : a ∈ orb E t)
    (hpa : pe p a = j1) (hnc : ∀ g : G, g⁻¹ * t * g ≠ a * t) :
    ThreeTransposition.IsThreeTranspositionSet {y : L | (y : G) ∈ lclass L a} := by
  have haL := H.orb_subset_L ha
  refine ThreeTransposition.isThreeTranspositionSet_of_ker_eq (fun g x hx => ?_) (fun x hx => ?_)
    (orderOf_t_L H) p (ker_eq_zpowers H) (fun x hx y hy => ?_) (fun d hd => ?_)
  · change ((g : G) * x * (g : G)⁻¹) ∈ lclass L a
    exact conj_mem_lclass g.2 hx
  · rw [← Subgroup.orderOf_coe]
    obtain ⟨c, hc⟩ := isConj_of_mem_lclass ha hx
    rw [← SemiconjBy.orderOf_eq _ hc, H.orderOf_t]
  · obtain ⟨m, hm⟩ := exists_pe_eq_tvP H haL hpa hx
    obtain ⟨m', hm'⟩ := exists_pe_eq_tvP H haL hpa hy
    rw [pe_of_mem p x.2] at hm
    rw [pe_of_mem p y.2] at hm'
    rw [hm, hm']
    exact orderOf_tvP_mul_tvP m m'
  · exact mul_t_notMem_lclass H ha hnc hd

theorem exists_transposition_class
    [Finite G] (H : ToddOrbit.Hyp t L E p)
    (D : DavisSolomonFacts G t L E) (hHL : centralizer ({t} : Set G) = L) :
    ∃ a ∈ orb E t, a ≠ t ∧ pe p a = j1 ∧
      (∀ s : G, (IsConj t s ∧ s * t = t * s) ↔ s = t ∨ s ∈ lclass L a) ∧
      t ∉ lclass L a ∧ (∀ b ∈ lclass L a, b * t ∉ lclass L a) ∧ (lclass L a).ncard = 693 ∧
      ThreeTransposition.IsThreeTranspositionSet {y : L | (y : G) ∈ lclass L a} := by
  obtain ⟨z, hzE, hpz, hnc, hzt, horb⟩ := H.orb_eq
  have hzL := H.E_le_L hzE
  have hpa : pe p (z * t) = j1 := by rw [pe_mul p hzL H.t_mem, H.pe_t, mul_one, hpz]
  have hnc' : ∀ g : G, g⁻¹ * t * g ≠ z * t * t := by
    rwa [mul_assoc, H.t_mul_t, mul_one]
  have hat : z * t ≠ t := fun h => by
    have e := congrArg (pe p) h
    rw [hpa, H.pe_t, j1_eq_tvP_zero] at e
    exact tvP_ne_one 0 e
  exact ⟨z * t, hzt, hat, hpa, conj_centralizer_iff H D hHL hzt horb, t_notMem_lclass H hat,
    fun b hb => mul_t_notMem_lclass H hzt hnc' hb, ncard_lclass H hzt hpa hnc',
    isThreeTranspositionSet_lclass H hzt hpa hnc'⟩

theorem ncard_conj_centralizer
    [Finite G] (H : ToddOrbit.Hyp t L E p)
    (D : DavisSolomonFacts G t L E) (hHL : centralizer ({t} : Set G) = L) :
    {s : G | IsConj t s ∧ s * t = t * s}.ncard = 694 := by
  obtain ⟨a, -, -, -, hiff, ht, -, hcard, -⟩ := exists_transposition_class H D hHL
  have e : {s : G | IsConj t s ∧ s * t = t * s} = insert t (lclass L a) := by
    ext s
    exact hiff s
  rw [e, Set.ncard_insert_of_notMem ht, hcard]

theorem card_L
    (H : ToddOrbit.Hyp t L E p) : Nat.card L = 2 ^ 16 * 280665 := by
  have hrange : p.range = T46 := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact H.mem_T46 y
    · exact H.surj x
  have h1 := card_mul_index p.ker
  rw [index_ker, hrange, card_T46, ker_eq_zpowers H, Nat.card_zpowers, orderOf_t_L H] at h1
  rw [← h1]
  norm_num

theorem card_sylow
    [Finite G] (H : ToddOrbit.Hyp t L E p) (D : DavisSolomonFacts G t L E)
    (hHL : centralizer ({t} : Set G) = L) (hG : ∀ K : Subgroup G, K.index ≠ 2)
    (P : Sylow 2 G) : Nat.card P = 2 ^ 17 :=
  card_sylow_of_fixed hG H.orderOf_t (ncard_conj_centralizer H D hHL)
    (by rw [hHL]; exact card_L H) P

end Class

end CFSG.EvenSmallLie.UnitarySix.Hunt
