module

public import CFSG.FeitThompson.Local.PLengthOneNormalSeries

namespace CFSG.FeitThompson

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

variable {p : ℕ} {X : Type*} [Group X] [Finite X]

omit [Finite X] in
theorem relIndex_map_dvd {Y : Type*} [Group Y] (f : X →* Y) (D T : Subgroup X) :
    (D.map f).relIndex (T.map f) ∣ D.relIndex T := by
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left T (Subgroup.le_comap_map f D)

omit [Finite X] in
theorem card_comap_mk' (D : Subgroup X) [D.Normal] (S : Subgroup (X ⧸ D)) :
    Nat.card (S.comap (QuotientGroup.mk' D)) = Nat.card D * Nat.card S := by
  have hle : D ≤ S.comap (QuotientGroup.mk' D) := fun x hx => by
    simp [Subgroup.mem_comap, (QuotientGroup.eq_one_iff x).2 hx]
  have h1 : Nat.card (D.subgroupOf (S.comap (QuotientGroup.mk' D))) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  have h2 := Subgroup.card_mul_index (D.subgroupOf (S.comap (QuotientGroup.mk' D)))
  rw [h1] at h2
  rw [← h2, show (D.subgroupOf (S.comap (QuotientGroup.mk' D))).index
    = D.relIndex (S.comap (QuotientGroup.mk' D)) from rfl, relIndex_comap_mk']

variable [Fact p.Prime]

theorem HasPLengthLeOne.of_surjective {Y : Type*} [Group Y] [Finite Y] {f : X →* Y}
    (hf : Function.Surjective f) (h : HasPLengthLeOne p X) : HasPLengthLeOne p Y := by
  rw [hasPLengthLeOne_iff_exists_normal] at h ⊢
  obtain ⟨D, T, hD, hT, hDT, hDcard, ⟨n, hn⟩, hTidx⟩ := h
  refine ⟨D.map f, T.map f, hD.map f hf, hT.map f hf, Subgroup.map_mono hDT, ?_, ?_, ?_⟩
  · exact fun hdvd => hDcard (hdvd.trans (Subgroup.card_map_dvd D f))
  · rw [natCard_quotient_subgroupOf] at hn ⊢
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Fact.out).1 (hn ▸ relIndex_map_dvd f D T)
    exact ⟨m, hm⟩
  · exact fun hdvd => hTidx (hdvd.trans (Subgroup.index_map_dvd (H := T) hf))

theorem HasPLengthLeOne.quotient (D : Subgroup X) [D.Normal] (h : HasPLengthLeOne p X) :
    HasPLengthLeOne p (X ⧸ D) :=
  h.of_surjective (QuotientGroup.mk'_surjective D)

theorem hasPLengthLeOne_of_quotient {D : Subgroup X} [D.Normal] (hD : ¬ p ∣ Nat.card D)
    (h : HasPLengthLeOne p (X ⧸ D)) : HasPLengthLeOne p X := by
  have hp : p.Prime := Fact.out
  rw [hasPLengthLeOne_iff_exists_normal] at h ⊢
  obtain ⟨D₀, T, hD₀, hT, hDT, hD₀card, ⟨n, hn⟩, hTidx⟩ := h
  refine ⟨D₀.comap (QuotientGroup.mk' D), T.comap (QuotientGroup.mk' D),
    hD₀.comap _, hT.comap _, Subgroup.comap_mono hDT, ?_, ?_, ?_⟩
  · rw [card_comap_mk']
    exact fun hdvd => (hp.dvd_mul.1 hdvd).elim hD hD₀card
  · refine ⟨n, ?_⟩
    rw [natCard_quotient_subgroupOf, Subgroup.relIndex_comap,
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective D),
      ← natCard_quotient_subgroupOf]
    exact hn
  · rwa [Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective D)]

theorem hasPLengthLeOne_quotient_iff {D : Subgroup X} [D.Normal] (hD : ¬ p ∣ Nat.card D) :
    HasPLengthLeOne p X ↔ HasPLengthLeOne p (X ⧸ D) :=
  ⟨fun h => h.quotient D, hasPLengthLeOne_of_quotient hD⟩

end

end CFSG.FeitThompson
