module

public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterStructBalance
public import CFSG.LocalAnalysis.EvenSporadicStandard.HSStd.Zassenhaus.OuterSwapCaseLayerAbs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer

open Subgroup Equiv Equiv.Perm CFSG.EvenSporadicStandard.HSStd CFSG.EvenSporadicStandard
  CFSG.EvenSporadicStandard.Induction CFSG.EvenSporadicStandard.Solomon78
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {t : G} {S : Subgroup G}
  {z n v s : G}

@[expose] def SwapNoE8 (L : Subgroup G) (v : G) : Prop :=
  ∀ E : Subgroup G, E ≤ centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G) →
    (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 4

@[expose] def lamIn (L : Subgroup G) (v : G) : Subgroup ↥(centralizer ({v} : Set G)) :=
  (derivedCentralizerIn L v).subgroupOf (centralizer ({v} : Set G))

@[expose] def tIn (h : HSOuterSetup G L t S z n v s) : ↥(centralizer ({v} : Set G)) := h.tElem

theorem sq_mem_derived (h : HSOuterSetup G L t S z n v s) {β : G}
    (hβ : β ∈ centralizer ({v} : Set G) ⊓ L) : β * β ∈ derivedCentralizerIn L v := by
  obtain ⟨e⟩ := h.ctx.v_cls
  set T := centralizer ({v} : Set G) ⊓ L with hT
  let ψ : Perm (Fin 8) →* G := T.subtype.comp e.symm.toMonoidHom
  have hψ : Function.Injective ψ := Subtype.val_injective.comp e.symm.injective
  have hrange : ψ.range = T := by
    ext g
    constructor
    · rintro ⟨σ, rfl⟩
      exact (e.symm σ).2
    · intro hg
      exact ⟨e ⟨g, hg⟩, by simp [ψ]⟩
  have hΛ : derivedCentralizerIn L v = (alternatingGroup (Fin 8)).map ψ :=
    map_commutator_range ψ hψ T hrange
  rw [hΛ]
  refine ⟨e ⟨β, hβ⟩ * e ⟨β, hβ⟩, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_alternatingGroup, map_mul]
    exact Int.units_mul_self _
  · simp [ψ]

theorem bp_pair_sq (h : HSOuterSetup G L t S z n v s) (a b : Bool) :
    (bp t a * bp v b) * (bp t a * bp v b) = 1 := by
  have ht2 : t * t = 1 := t_sq h
  have hv2 : v * v = 1 := h.ctx.v_sq
  have htv : t * v = v * t := h.t_comm_v
  cases a <;> cases b <;> simp only [bp, ite_true, Bool.false_eq_true, ite_false, one_mul, mul_one]
  · exact hv2
  · exact ht2
  · calc t * v * (t * v) = t * (v * t) * v := by group
      _ = t * (t * v) * v := by rw [htv]
      _ = (t * t) * (v * v) := by group
      _ = 1 := by rw [ht2, hv2]; group

theorem sq_mem_derived_of_centralizes (h : HSOuterSetup G L t S z n v s) {x : G}
    (hxt : x * t = t * x) (hxv : x * v = v * x) : x * x ∈ derivedCentralizerIn L v := by
  obtain ⟨β, hβ, a, b, rfl⟩ := decomp_Y h hxt hxv
  have hβc : β * (bp t a * bp v b) = (bp t a * bp v b) * β :=
    bp_comm a b (mem_centralizer_iff.1 h.t_mem β hβ.2) (mem_centralizer_singleton_iff.1 hβ.1)
  have e : β * (bp t a * bp v b) * (β * (bp t a * bp v b)) = β * β := by
    calc β * (bp t a * bp v b) * (β * (bp t a * bp v b))
        = β * ((bp t a * bp v b) * β) * (bp t a * bp v b) := by group
      _ = β * (β * (bp t a * bp v b)) * (bp t a * bp v b) := by rw [← hβc]
      _ = β * β * ((bp t a * bp v b) * (bp t a * bp v b)) := by group
      _ = β * β := by rw [bp_pair_sq h a b, mul_one]
  rw [e]
  exact sq_mem_derived h hβ

theorem card_centralizer_tIn_le (h : HSOuterSetup G L t S z n v s) :
    Nat.card ↥(centralizer ({tIn h} : Set ↥(centralizer ({v} : Set G)))) ≤ 161280 := by
  obtain ⟨e⟩ := h.ctx.v_cls
  have hT : Nat.card ↥(centralizer ({v} : Set G) ⊓ L) = 40320 := by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm]
    simp [Nat.factorial]
  let F : Bool × Bool × ↥(centralizer ({v} : Set G) ⊓ L) → G :=
    fun p => (p.2.2 : G) * (bp t p.1 * bp v p.2.1)
  have hsub : ∀ w : ↥(centralizer ({tIn h} : Set ↥(centralizer ({v} : Set G)))),
      ((w : ↥(centralizer ({v} : Set G))) : G) ∈ Set.range F := by
    intro w
    have hw : (w : ↥(centralizer ({v} : Set G))) * tIn h = tIn h * w :=
      (mem_centralizer_iff.1 w.2 (tIn h) rfl).symm
    have hxt : ((w : ↥(centralizer ({v} : Set G))) : G) * t = t * (w : G) :=
      congrArg Subtype.val hw
    have hxv : ((w : ↥(centralizer ({v} : Set G))) : G) * v = v * (w : G) :=
      mem_centralizer_singleton_iff.1 (w : ↥(centralizer ({v} : Set G))).2
    obtain ⟨β, hβ, a, b, hx⟩ := decomp_Y h hxt hxv
    exact ⟨(a, b, ⟨β, hβ⟩), hx.symm⟩
  let φ : ↥(centralizer ({tIn h} : Set ↥(centralizer ({v} : Set G)))) → ↥(Set.range F) :=
    fun w => ⟨((w : ↥(centralizer ({v} : Set G))) : G), hsub w⟩
  have hφ : Function.Injective φ := by
    intro a b hab
    have := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext this)
  have h1 := Nat.card_le_card_of_injective φ hφ
  have h2 : Nat.card ↥(Set.range F) ≤
      Nat.card (Bool × Bool × ↥(centralizer ({v} : Set G) ⊓ L)) :=
    Nat.card_le_card_of_surjective _ (Set.rangeFactorization_surjective (f := F))
  have h3 : Nat.card (Bool × Bool × ↥(centralizer ({v} : Set G) ⊓ L)) = 161280 := by
    rw [Nat.card_prod, Nat.card_prod, hT, Nat.card_eq_fintype_card, Fintype.card_bool]
  omega

theorem lamIn_le_layer (h15 : FS79Lemma15Sec G) (h : HSOuterSetup G L t S z n v s) :
    lamIn L v ≤ CFSG.layer ↥(centralizer ({v} : Set G)) := by
  intro x hx
  have hx' : (x : G) ∈ (CFSG.layer ↥(centralizer ({v} : Set G))).map
      (centralizer ({v} : Set G)).subtype :=
    layerIn_le_map_layer _ (derived_le_layerIn h15 h (mem_subgroupOf.1 hx))
  obtain ⟨y, hy, hyx⟩ := hx'
  have : y = x := Subtype.ext hyx
  exact this ▸ hy

theorem swapX_of_setup (h15 : FS79Lemma15Sec G) (h : HSOuterSetup G L t S z n v s) :
    SwapX ↥(centralizer ({v} : Set G)) (lamIn L v) (tIn h) where
  sq := Subtype.ext (t_sq h)
  cent := by
    intro j hj
    have hj' : (j : G) ∈ derivedCentralizerIn L v := hj
    exact Subtype.ext (mem_centralizer_iff.1 h.t_mem j (derivedCentralizerIn_le L v hj'))
  alt8 := by
    obtain ⟨e⟩ := derivedCentralizerIn_equiv h.ctx.v_cls
    exact ⟨(Subgroup.subgroupOfEquivOfLe (derivedCentralizerIn_le_centralizer L v)).trans e⟩
  le_layer := lamIn_le_layer h15 h
  comm_mem := by
    intro w w' hw hw'
    have hxt : (w : G) * t = t * (w : G) := congrArg Subtype.val hw
    have hxv : (w : G) * v = v * (w : G) := mem_centralizer_singleton_iff.1 w.2
    have hxt' : (w' : G) * t = t * (w' : G) := congrArg Subtype.val hw'
    have hxv' : (w' : G) * v = v * (w' : G) := mem_centralizer_singleton_iff.1 w'.2
    have := commutator_mem_derived h hxt hxv hxt' hxv'
    exact mem_subgroupOf.2 (by simpa [commutatorElement_def] using this)
  sq_mem := by
    intro w hw
    have hxt : (w : G) * t = t * (w : G) := congrArg Subtype.val hw
    have hxv : (w : G) * v = v * (w : G) := mem_centralizer_singleton_iff.1 w.2
    exact mem_subgroupOf.2 (by simpa using sq_mem_derived_of_centralizes h hxt hxv)
  not_normal := h.not_normal
  oddCore := h.setting.1.oddCore v
    (orderOf_eq_prime (by rw [pow_two]; exact h.ctx.v_sq) h.v_ne_one)
  card_le := card_centralizer_tIn_le h

theorem swapNoE8_of (hE8 : SwapNoE8 L v) :
    ∀ E : Subgroup ↥(centralizer ({v} : Set G)), E ≤ centralizer ((lamIn L v : Subgroup _) : Set _) →
      (∀ e ∈ E, e * e = 1) → Nat.card E ≤ 4 := by
  intro E hE hE2
  have hle : E.map (centralizer ({v} : Set G)).subtype ≤
      centralizer ((derivedCentralizerIn L v : Subgroup G) : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    rw [mem_centralizer_iff]
    intro l hl
    have hlH : l ∈ centralizer ({v} : Set G) := derivedCentralizerIn_le_centralizer L v hl
    have := mem_centralizer_iff.1 (hE he) ⟨l, hlH⟩ (mem_subgroupOf.2 hl)
    exact congrArg Subtype.val this
  have hsq : ∀ e ∈ E.map (centralizer ({v} : Set G)).subtype, e * e = 1 := by
    rintro _ ⟨e, he, rfl⟩
    have := hE2 e he
    exact congrArg Subtype.val this
  have h4 := hE8 _ hle hsq
  rwa [Subgroup.card_map_of_injective (centralizer ({v} : Set G)).subtype_injective] at h4

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.Outer
