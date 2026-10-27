module

public import CFSG.GH74.AS16.E2.OuterPure
public import CFSG.GH74.AS16.DeltaNonempty
public import CFSG.GH74.AS16.E2.Std
public import CFSG.GH74.AS16.Notation1641
public import CFSG.GH74.Uniqueness.SU.SU1Arith

public section

namespace CFSG.GH74.AS16.E2

open Subgroup CFSG CFSG.ComponentClassification.AschbacherTightEmbedding
  CFSG.ComponentClassification.LiteratureLocal.TightCommuting CFSG.ABGLocalTools
open CFSG.GH74.E2 hiding Hyp
open CFSG.GH74.AS16 (Pair LNormal InDelta lemma1642_one lemma1642_three lemma1642_four
  lemma1652_one delta_nonempty inDelta_rightConjugate conjugate_centralizer
  conjugate_centralizer_singleton isCompIn_conj conjugate_eq_self_iff zpow_eq_one_or_self)
open CFSG.GH74.Uniqueness (S_CorZD)

section Act

variable {G : Type*} [Group G] {L : Subgroup G}

@[expose] def IsInn {K : Type*} [Group K] (φ : MulAut K) : Prop :=
  ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹

theorem act_mul {x y : G} (hx : x ∈ normalizer (L : Set G)) (hy : y ∈ normalizer (L : Set G))
    (hxy : x * y ∈ normalizer (L : Set G)) :
    L.normalizerMonoidHom ⟨x * y, hxy⟩ =
      L.normalizerMonoidHom ⟨x, hx⟩ * L.normalizerMonoidHom ⟨y, hy⟩ := by
  rw [← map_mul]
  rfl

theorem act_eq_one_iff {x : G} (hx : x ∈ normalizer (L : Set G)) :
    L.normalizerMonoidHom ⟨x, hx⟩ = 1 ↔ x ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    refine mem_centralizer_iff.2 fun y hy => ?_
    have h2 : x * y * x⁻¹ = y := congrArg (fun φ : MulAut ↥L => ((φ ⟨y, hy⟩ : ↥L) : G)) h
    have h3 : x * y = y * x := by
      calc x * y = (x * y * x⁻¹) * x := by group
        _ = y * x := by rw [h2]
    exact h3.symm
  · exact normalizerMonoidHom_eq_one hx

theorem act_isInn_iff {x : G} (hx : x ∈ normalizer (L : Set G)) :
    IsInn (L.normalizerMonoidHom ⟨x, hx⟩) ↔ InnerAt L x := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨(k : G), k.2, fun y hy => congrArg Subtype.val (hk ⟨y, hy⟩)⟩
  · rintro ⟨l, hl, h⟩
    exact ⟨⟨l, hl⟩, fun y => Subtype.ext (h y y.2)⟩

theorem act_conj {l : G} (hl : l ∈ L) :
    L.normalizerMonoidHom ⟨l, Subgroup.le_normalizer hl⟩ = MulAut.conj (⟨l, hl⟩ : ↥L) := by
  ext y
  rfl

theorem InnerAt.conj {x k : G} (hk : k ∈ normalizer (L : Set G)) (hx : InnerAt L x) :
    InnerAt L (k * x * k⁻¹) := by
  obtain ⟨l, hl, h⟩ := hx
  refine ⟨k * l * k⁻¹, (Subgroup.mem_normalizer_iff.1 hk l).1 hl, fun y hy => ?_⟩
  have hy' : k⁻¹ * y * k ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 ((normalizer (L : Set G)).inv_mem hk) y).1 hy
    simpa using this
  have h1 := h _ hy'
  calc k * x * k⁻¹ * y * (k * x * k⁻¹)⁻¹ = k * (x * (k⁻¹ * y * k) * x⁻¹) * k⁻¹ := by group
    _ = k * (l * (k⁻¹ * y * k) * l⁻¹) * k⁻¹ := by rw [h1]
    _ = k * l * k⁻¹ * y * (k * l * k⁻¹)⁻¹ := by group

end Act

section Rank3

variable {G : Type*} [Group G]

structure Rank3Sub (L : Subgroup G) : Prop where
  elemAb9 : ∃ E : Subgroup G, E ≤ L ∧ ElemAb 3 E ∧ Nat.card E = 9
  exists3 : ∀ v ∈ L, orderOf v = 2 → ∃ c ∈ L, orderOf c = 3 ∧ c * v = v * c
  inner3 : ∀ c ∈ normalizer (L : Set G), c ^ 3 ∈ centralizer (L : Set G) →
    ∃ l ∈ L, l⁻¹ * c ∈ centralizer (L : Set G)

structure Rank3Table (K : Type*) [Group K] : Prop where
  elemAb9 : ∃ E : Subgroup K, ElemAb 3 E ∧ Nat.card E = 9
  exists3 : ∀ v : K, orderOf v = 2 → ∃ c : K, orderOf c = 3 ∧ c * v = v * c

@[expose] def Rank3Data (P : (K : Type) → [Group K] → Prop) : Prop :=
  ∀ (K : Type) [Group K] [Finite K], P K → Rank3Table K ∧
    ∀ φ : MulAut K, φ ^ 3 = 1 → ∃ k : K, ∀ x : K, φ x = k * x * k⁻¹

theorem Rank3Sub.of_table {L : Subgroup G} (hT : Rank3Table ↥L)
    (hin : ∀ φ : MulAut ↥L, φ ^ 3 = 1 → ∃ k : ↥L, ∀ x : ↥L, φ x = k * x * k⁻¹) :
    Rank3Sub L := by
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨E, hE, hcard⟩ := hT.elemAb9
    refine ⟨E.map L.subtype, ?_, ⟨?_, ?_⟩, ?_⟩
    · rintro _ ⟨x, -, rfl⟩
      exact x.2
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      exact congrArg Subtype.val (hE.1 a ha b hb)
    · rintro _ ⟨a, ha, rfl⟩
      simpa using congrArg Subtype.val (hE.2 a ha)
    · rw [Subgroup.card_map_of_injective L.subtype_injective]
      exact hcard
  · intro v hv hv2
    have hv2' : orderOf (⟨v, hv⟩ : ↥L) = 2 := by rw [← Subgroup.orderOf_coe]; exact hv2
    obtain ⟨c, hc3, hcv⟩ := hT.exists3 ⟨v, hv⟩ hv2'
    exact ⟨c, c.2, by rw [Subgroup.orderOf_coe]; exact hc3, congrArg Subtype.val hcv⟩
  · intro c hcN hc3C
    have hφ : (L.normalizerMonoidHom ⟨c, hcN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨c, hcN⟩ : normalizer (L : Set G)) ^ 3 =
          ⟨c ^ 3, (normalizer (L : Set G)).pow_mem hcN 3⟩ := Subtype.ext (by simp)
      rw [this]
      exact normalizerMonoidHom_eq_one _ hc3C
    obtain ⟨k, hk⟩ := hin _ hφ
    refine ⟨(k : G), k.2, mem_centralizer_iff.2 fun x hx => ?_⟩
    have h1 := congrArg Subtype.val (hk ⟨x, hx⟩)
    have h2 : c * x * c⁻¹ = (k : G) * x * (k : G)⁻¹ := h1
    calc x * ((k : G)⁻¹ * c) = (k : G)⁻¹ * ((k : G) * x * (k : G)⁻¹) * c := by group
      _ = (k : G)⁻¹ * (c * x * c⁻¹) * c := by rw [h2]
      _ = ((k : G)⁻¹ * c) * x := by group

end Rank3

section Std

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.isStandard' (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : center ↥L = ⊥) (hR3 : Rank3Sub L) : IsStandardSubgroup L :=
  AS16.isStandardSubgroup_of_terminal h.pair.isQuasisimple h.pair.orderOf_eq
    h.pair.mem_centralizer (fun t htL ht2 => hterm.2.2.2 t ht2 htL)
    (not_isCompIn_conj_centralizer h.quasithin h.pair.isQuasisimple (center_trivial hZ)
      hR3.elemAb9 hR3.exists3)

theorem Cfg.decomp_inner0 (h : Cfg G T z L) (hZ : center ↥L = ⊥) :
    ∀ t ∈ (T : Subgroup G), InnerAt L t → ∃ s ∈ (T : Subgroup G) ⊓ L,
      ∃ c ∈ (T : Subgroup G) ⊓ centralizer (L : Set G), t = s * c := by
  have hT0L : innerSub (T : Subgroup G) L ⊓ L = (T : Subgroup G) ⊓ L := by
    ext x
    constructor
    · rintro ⟨hx, hxL⟩
      exact ⟨hx.1, hxL⟩
    · rintro ⟨hxT, hxL⟩
      exact ⟨⟨hxT, InnerAt.of_mem hxL⟩, hxL⟩
  have hdec := exists_decomp_of_inner (T := innerSub (T : Subgroup G) L) (L := L)
    (T.isPGroup'.to_le innerSub_le) (center_trivial' hZ)
    (fun P hP hPL hle => by
      rw [hT0L]
      rw [hT0L] at hle
      exact h.isSylowOf_inf.eq_of_le hle hPL hP)
    (fun t ht => ht.2)
  intro t ht hti
  obtain ⟨s, hs, c, hc, e⟩ := hdec t ⟨ht, hti⟩
  refine ⟨s, ?_, c, ⟨hc.1.1, hc.2⟩, e⟩
  rw [hT0L] at hs
  exact hs

end Std

section DeltaConj

variable {G : Type} [Group G] [Finite G]

theorem delta_triple_conj {K K' R : Subgroup G} (hK' : InDelta K K')
    (hR : IsSylowOf 2 R (K' ⊓ normalizer (K : Set G))) {k : G}
    (hk : k ∈ normalizer (K : Set G)) :
    InDelta K (rightConjugate K' k) ∧
      IsSylowOf 2 (rightConjugate R k) (rightConjugate K' k ⊓ normalizer (K : Set G)) := by
  have hN' : rightConjugate (normalizer (K : Set G)) k = normalizer (K : Set G) :=
    (rightConjugate_eq_self_iff _ k).mpr (le_normalizer hk)
  have hinfeq : rightConjugate (K' ⊓ normalizer (K : Set G)) k =
      rightConjugate K' k ⊓ normalizer (K : Set G) := by rw [rightConjugate_inf, hN']
  refine ⟨inDelta_rightConjugate hK' hk, ?_⟩
  rw [← hinfeq]
  refine isSylowOf_of_card (rightConjugate_mono k hR.le) ?_
  rw [rightConjugate_card, rightConjugate_card, hR.card_eq]

variable {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem exists_delta_sylow_le_T' {X K' : Subgroup G} (hp : Pair T z L) (hN : LNormal z L)
    (hS : IsStandardSubgroup L) (hK' : InDelta (centralizer (L : Set G)) K')
    (hX : IsPGroup 2 X) (hXK : X ≤ K' ⊓ normalizer (centralizer (L : Set G) : Set G)) :
    ∃ (k : G) (R : Subgroup G), k ∈ normalizer (L : Set G) ∧
      InDelta (centralizer (L : Set G)) (rightConjugate K' k) ∧
      IsSylowOf 2 R (rightConjugate K' k ⊓ normalizer (centralizer (L : Set G) : Set G)) ∧
      R ≤ (T : Subgroup G) ∧ rightConjugate X k ≤ R := by
  set C : Subgroup G := centralizer (L : Set G) with hC
  obtain ⟨R₀, hR₀, hXR₀⟩ := exists_isSylowOf_ge hXK hX
  have hH : normalizer (C : Set G) = normalizer (L : Set G) := hS.2.2.2.1
  have hR₀H : R₀ ≤ normalizer (L : Set G) := hH ▸ (hR₀.le.trans inf_le_right)
  obtain ⟨T', hT', hR₀T'⟩ := exists_isSylowOf_ge hR₀H hR₀.isPGroup
  obtain ⟨k, hk, hkconj⟩ := (hp.isSylowOf_normalizer hN).exists_mem_conj hT'
  have hkC : k ∈ normalizer (C : Set G) := hH ▸ hk
  have hRle : rightConjugate R₀ k ≤ (T : Subgroup G) := by
    intro y hy
    have hy' : k * y * k⁻¹ ∈ R₀ := (mem_rightConjugate_iff R₀ k y).mp hy
    have h1 := (hkconj (k * y * k⁻¹)).mp (hR₀T' hy')
    have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
    rw [e] at h1
    exact h1
  have hconj := delta_triple_conj hK' hR₀ hkC
  exact ⟨k, rightConjugate R₀ k, hk, hconj.1, hconj.2, hRle, rightConjugate_mono k hXR₀⟩

end DeltaConj

section Three

variable {G : Type} [Group G] [Finite G] {T : Sylow 2 G} {z : G} {L : Subgroup G}

theorem Cfg.three_mem_of_centralizes (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : ∀ x ∈ L, x ∈ centralizer (L : Set G) → x = 1) (hR3 : Rank3Sub L)
    {i : G} (hi : orderOf i = 2) (hiD : i ∈ centralizer (L : Set G)) {c : G}
    (hc : orderOf c = 3) (hci : c * i = i * c) : c ∈ L := by
  have hcomp : IsCompCen i L := hterm.2.2.2 i hi hiD
  have hcenN : ∀ x : G, x * i = i * x → x ∈ normalizer (L : Set G) := by
    intro x hx
    have hxC : x ∈ Cen i := mem_Cen'.2 hx
    have hc' := conjugate_eq_of_unique hcomp
      (fun K'' hK'' => h.uniq i hi K'' L hK'' hcomp) hxC
    exact (conjugate_eq_self_iff L x).1 hc'
  exact mem_of_order_three h.quasithin hi hiD hZ hR3.elemAb9 hR3.inner3 hcenN hc hci

theorem Cfg.three_mem_conj (h : Cfg G T z L) (hterm : GLS.IsTerminalPair 2 z L)
    (hZ : ∀ x ∈ L, x ∈ centralizer (L : Set G) → x = 1) (hR3 : Rank3Sub L)
    {g r : G} (hr : orderOf r = 2) (hrD : g⁻¹ * r * g ∈ centralizer (L : Set G)) {c : G}
    (hc : orderOf c = 3) (hcr : c * r = r * c) : g⁻¹ * c * g ∈ L := by
  have hord : ∀ x : G, orderOf (g⁻¹ * x * g) = orderOf x := by
    intro x
    calc orderOf (g⁻¹ * x * g) = orderOf ((MulAut.conj g⁻¹) x) := by simp
      _ = orderOf x := (MulAut.conj g⁻¹).orderOf_eq x
  refine h.three_mem_of_centralizes hterm hZ hR3 (i := g⁻¹ * r * g) (by rw [hord]; exact hr) hrD
    (c := g⁻¹ * c * g) (by rw [hord]; exact hc) ?_
  calc g⁻¹ * c * g * (g⁻¹ * r * g) = g⁻¹ * (c * r) * g := by group
    _ = g⁻¹ * (r * c) * g := by rw [hcr]
    _ = g⁻¹ * r * g * (g⁻¹ * c * g) := by group

end Three

end CFSG.GH74.AS16.E2
