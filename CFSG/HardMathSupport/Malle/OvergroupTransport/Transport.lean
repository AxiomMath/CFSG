module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.HardMathSupport.Malle.OvergroupTransport

open CFSG.Open

theorem pRank_map_of_injective {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (p : ℕ) {f : G →* G'} (hf : Function.Injective f) (H : Subgroup G) :
    pRank p (H.map f) = pRank p H := by
  unfold pRank
  congr 1
  ext k
  constructor
  · rintro ⟨E', hE'H, hE', hcard⟩
    have hle : E'.comap f ≤ H := by
      have := Subgroup.comap_mono (f := f) hE'H
      rwa [Subgroup.comap_map_eq_self_of_injective hf] at this
    have hE'r : E' ≤ f.range := hE'H.trans (Subgroup.map_le_range f H)
    have hmap : (E'.comap f).map f = E' := Subgroup.map_comap_eq_self hE'r
    refine ⟨E'.comap f, hle, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · apply Subtype.ext
      apply hf
      have := (hE'.1).is_comm.comm ⟨f a, a.2⟩ ⟨f b, b.2⟩
      simpa using congrArg Subtype.val this
    · apply hf
      have := hE'.2 (f x) hx
      simpa using this
    · rw [← (Subgroup.card_map_of_injective hf : Nat.card ((E'.comap f).map f) = _), hmap]
      exact hcard
  · rintro ⟨E, hEH, hE, hcard⟩
    refine ⟨E.map f, Subgroup.map_mono hEH, ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
    · obtain ⟨a', ha', ha⟩ := a.2
      obtain ⟨b', hb', hb⟩ := b.2
      apply Subtype.ext
      have := hE.1.is_comm.comm ⟨a', ha'⟩ ⟨b', hb'⟩
      show (a : G') * b = b * a
      rw [← ha, ← hb, ← map_mul, ← map_mul]
      exact congrArg (fun z : E => f (z : G)) this
    · obtain ⟨x', hx', rfl⟩ := hx
      rw [← map_pow, hE.2 x' hx', map_one]
    · rw [Subgroup.card_map_of_injective hf, hcard]

theorem pRank_subgroupOf {Y : Type} [Group Y] [Finite Y] (p : ℕ) {K P : Subgroup Y} (h : P ≤ K) :
    pRank p (P.subgroupOf K) = pRank p P := by
  have := pRank_map_of_injective p K.subtype_injective (P.subgroupOf K)
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h] at this
  exact this.symm

theorem not_dvd_relIndex_inf_sylow {Y : Type} [Group Y] [Finite Y] {p : ℕ} [Fact p.Prime]
    (K : Subgroup Y) [K.Normal] (T : Sylow p Y) :
    ¬ p ∣ ((T : Subgroup Y) ⊓ K).relIndex K := by
  intro hp
  have h1 := Subgroup.relIndex_mul_index (inf_le_right : (T : Subgroup Y) ⊓ K ≤ K)
  have h2 := Subgroup.relIndex_mul_index (inf_le_left : (T : Subgroup Y) ⊓ K ≤ T)
  rw [Subgroup.inf_relIndex_left] at h2
  obtain ⟨b', hb'⟩ := Subgroup.relIndex_dvd_index_of_normal K (T : Subgroup Y)
  have hd : 0 < K.relIndex (T : Subgroup Y) := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have h3 : ((T : Subgroup Y) ⊓ K).relIndex K * b' = (T : Subgroup Y).index := by
    have h4 : K.relIndex (T : Subgroup Y) * (((T : Subgroup Y) ⊓ K).relIndex K * b') =
        K.relIndex (T : Subgroup Y) * (T : Subgroup Y).index := by
      calc K.relIndex (T : Subgroup Y) * (((T : Subgroup Y) ⊓ K).relIndex K * b')
          = ((T : Subgroup Y) ⊓ K).relIndex K * (K.relIndex (T : Subgroup Y) * b') := by ring
        _ = ((T : Subgroup Y) ⊓ K).relIndex K * K.index := by rw [← hb']
        _ = ((T : Subgroup Y) ⊓ K).index := h1
        _ = _ := by rw [← h2]
    exact Nat.eq_of_mul_eq_mul_left hd h4
  exact T.not_dvd_index (h3 ▸ Dvd.dvd.mul_right hp b')

@[expose] def NormalizerMaximal {G : Type*} [Group G] (P : Subgroup G) : Prop :=
  ∀ H : Subgroup G, Subgroup.normalizer (P : Set G) ≤ H →
    H = Subgroup.normalizer (P : Set G) ∨ H = ⊤

theorem hmax_of_normalizerMaximal_subgroupOf {Y : Type} [Group Y] {K T₀ : Subgroup Y}
    (hT : T₀ ≤ K) (h : NormalizerMaximal (T₀.subgroupOf K)) :
    ∀ H : Subgroup Y, H ≤ K → K ⊓ Subgroup.normalizer (T₀ : Set Y) ≤ H →
      H = K ⊓ Subgroup.normalizer (T₀ : Set Y) ∨ H = K := by
  intro H hHK hH
  have hN : Subgroup.normalizer ((T₀.subgroupOf K : Subgroup K) : Set K) ≤ H.subgroupOf K := by
    rw [← Subgroup.subgroupOf_normalizer_eq hT]
    intro x hx
    exact hH ⟨x.2, hx⟩
  rcases h _ hN with h1 | h1
  · left
    rw [← Subgroup.subgroupOf_normalizer_eq hT, Subgroup.subgroupOf_inj, inf_eq_left.mpr hHK] at h1
    rw [h1]
    exact inf_comm _ _
  · right
    exact le_antisymm hHK (Subgroup.subgroupOf_eq_top.mp h1)

end CFSG.HardMathSupport.Malle.OvergroupTransport
