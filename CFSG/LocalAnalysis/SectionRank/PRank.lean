module

public import CFSG.Open.Defs

public section

namespace CFSG.SectionRank

open CFSG.Open

variable {G : Type*} [Group G] [Finite G] {p : ℕ}

omit [Finite G] in
theorem isElemAbelian_bot (p : ℕ) : IsElemAbelian p (⊥ : Subgroup G) :=
  ⟨⟨⟨fun a b => Subtype.ext (by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.mem_bot.1 a.2, Subgroup.mem_bot.1 b.2])⟩⟩,
    fun x hx => by rw [Subgroup.mem_bot.1 hx, one_pow]⟩

theorem pRank_bddAbove (hp : 1 < p) (H : Subgroup G) :
    BddAbove {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k} := by
  refine ⟨Nat.card G, ?_⟩
  rintro k ⟨E, -, -, hk⟩
  have h1 : k < p ^ k := Nat.lt_pow_self hp
  have h2 : Nat.card E ≤ Nat.card G := Subgroup.card_le_card_group E
  change k ≤ Nat.card G
  omega

theorem le_pRank (hp : 1 < p) {H E : Subgroup G} (hEH : E ≤ H) (hE : IsElemAbelian p E)
    {k : ℕ} (hk : Nat.card E = p ^ k) : k ≤ pRank p H :=
  le_csSup (pRank_bddAbove hp H) ⟨E, hEH, hE, hk⟩

theorem exists_pRank (hp : 1 < p) (H : Subgroup G) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ pRank p H :=
  Nat.sSup_mem (s := {k | ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ k})
    ⟨0, ⊥, bot_le, isElemAbelian_bot p, by simp⟩ (pRank_bddAbove hp H)

theorem pRank_le (hp : 1 < p) {H : Subgroup G} {k : ℕ}
    (h : ∀ E : Subgroup G, E ≤ H → IsElemAbelian p E → Nat.card E ≤ p ^ k) :
    pRank p H ≤ k := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp H
  have := h E hEH hE
  rw [hcard] at this
  exact (Nat.pow_le_pow_iff_right hp).1 this

theorem pRank_mono (hp : 1 < p) {H K : Subgroup G} (hHK : H ≤ K) : pRank p H ≤ pRank p K := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp H
  exact le_pRank hp (hEH.trans hHK) hE hcard

omit [Finite G] in
theorem isElemAbelian_map {G' : Type*} [Group G'] {E : Subgroup G} (hE : IsElemAbelian p E)
    (f : G →* G') : IsElemAbelian p (E.map f) := by
  have := hE.1
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
  · obtain ⟨x, hx, hax⟩ := Subgroup.mem_map.1 a.2
    obtain ⟨z, hz, hbz⟩ := Subgroup.mem_map.1 b.2
    apply Subtype.ext
    change (a : G') * b = b * a
    rw [← hax, ← hbz, ← map_mul, ← map_mul]
    exact congrArg (fun w : E => f w) (mul_comm' (⟨x, hx⟩ : E) ⟨z, hz⟩)
  · obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
    rw [← map_pow, hE.2 x hx, map_one]

theorem le_pRank_of_injective {A : Type*} [Group A] (hp : 1 < p)
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) {k : ℕ}
    (hA : Nat.card A = p ^ k) (f : A →* G) (hf : Function.Injective f) {H : Subgroup G}
    (hH : f.range ≤ H) : k ≤ pRank p H := by
  refine le_pRank hp hH ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩ ?_
  · obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 a.2
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 b.2
    apply Subtype.ext
    change (a : G) * b = b * a
    rw [← hx, ← hz, ← map_mul, ← map_mul, hcomm]
  · obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    rw [← map_pow, hpow, map_one]
  · rw [← hA]
    exact (Nat.card_congr (MonoidHom.ofInjective hf).toEquiv).symm

variable {G' : Type*} [Group G'] [Finite G']

theorem pRank_le_map (hp : 1 < p) (f : G →* G') (hf : Function.Injective f) (H : Subgroup G) :
    pRank p H ≤ pRank p (H.map f) := by
  obtain ⟨E, hEH, hE, hcard⟩ := exists_pRank hp H
  refine le_pRank hp (Subgroup.map_mono hEH) (isElemAbelian_map hE f) ?_
  rw [Subgroup.card_map_of_injective hf, hcard]

theorem pRank_top_le_of_injective (hp : 1 < p) (f : G →* G') (hf : Function.Injective f) :
    pRank p (⊤ : Subgroup G) ≤ pRank p (⊤ : Subgroup G') :=
  (pRank_le_map hp f hf ⊤).trans (pRank_mono hp le_top)

theorem pRank_top_eq_of_mulEquiv (hp : 1 < p) (e : G ≃* G') :
    pRank p (⊤ : Subgroup G) = pRank p (⊤ : Subgroup G') :=
  le_antisymm (pRank_top_le_of_injective hp e.toMonoidHom e.injective)
    (pRank_top_le_of_injective hp e.symm.toMonoidHom e.symm.injective)

omit [Finite G'] in
theorem comm_pow_of_injective {A : Type*} [Group A] {f : A →* G'} (hf : Function.Injective f)
    (hcomm : ∀ a b : A, f a * f b = f b * f a) (hpow : ∀ a : A, f a ^ p = 1) :
    (∀ a b : A, a * b = b * a) ∧ ∀ a : A, a ^ p = 1 :=
  ⟨fun a b => hf (by rw [map_mul, map_mul, hcomm]),
    fun a => hf (by rw [map_pow, hpow, map_one])⟩

theorem pRank_quotient_eq [hp : Fact p.Prime] (N : Subgroup G) [N.Normal]
    (hN : ¬ p ∣ Nat.card N) :
    pRank p (⊤ : Subgroup (G ⧸ N)) = pRank p (⊤ : Subgroup G) := by
  have hp1 : 1 < p := hp.out.one_lt
  have hcop : ∀ {k : ℕ}, Nat.Coprime (p ^ k) (Nat.card N) := fun {k} =>
    Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hN)
  apply le_antisymm
  ·
    obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup (G ⧸ N))
    set P : Subgroup G := E.comap (QuotientGroup.mk' N)
    have hPcard : Nat.card P = Nat.card N * p ^ pRank p (⊤ : Subgroup (G ⧸ N)) := by
      rw [← hcard]
      exact QuotientGroup.card_preimage_mk N (E : Set (G ⧸ N))
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p P))
    have hScard : Nat.card S = p ^ pRank p (⊤ : Subgroup (G ⧸ N)) := by
      rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
        (pow_ne_zero _ hp.out.ne_zero), Finsupp.add_apply,
        Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow hp.out,
        Finsupp.single_eq_same, zero_add]
    set ι : S →* G := P.subtype.comp (S : Subgroup P).subtype
    set φ : S →* E := ((QuotientGroup.mk' N).comp ι).codRestrict E fun s => s.1.2
    have hker : ∀ s : S, ι s ∈ N → s = 1 := by
      intro s hs
      have hdisj := Subgroup.disjoint_of_coprime_natCard (H := (S : Subgroup P).map P.subtype)
        (K := N) (by
          rw [Subgroup.card_map_of_injective Subtype.val_injective, hScard]
          exact hcop)
      have h1 : ι s ∈ (S : Subgroup P).map P.subtype ⊓ N :=
        ⟨⟨s, s.2, rfl⟩, hs⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
      exact Subtype.ext (Subtype.ext h1)
    have hφ : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro s hs
      rw [MonoidHom.mem_ker] at hs
      have h2 : (QuotientGroup.mk' N) (ι s) = 1 := congrArg Subtype.val hs
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact (Subgroup.mem_bot).2 (hker s h2)
    have := hE.1
    obtain ⟨hcomm, hpow⟩ := comm_pow_of_injective (p := p) hφ (fun a b => mul_comm' _ _)
      (fun a => Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ (φ a).2))
    refine le_pRank_of_injective hp1 hcomm hpow hScard ι ?_ le_top
    exact Subtype.val_injective.comp Subtype.val_injective
  ·
    obtain ⟨E, -, hE, hcard⟩ := exists_pRank hp1 (⊤ : Subgroup G)
    have hdisj : Disjoint E N := Subgroup.disjoint_of_coprime_natCard (by rw [hcard]; exact hcop)
    have hinj : Function.Injective ((QuotientGroup.mk' N).comp E.subtype) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro s hs
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hs
      have h1 : (s : G) ∈ E ⊓ N := ⟨s.2, hs⟩
      rw [hdisj.eq_bot, Subgroup.mem_bot] at h1
      exact (Subgroup.mem_bot).2 (Subtype.ext h1)
    have := hE.1
    exact le_pRank_of_injective hp1 (fun a b => mul_comm' a b)
      (fun a => Subtype.ext (by
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
        exact hE.2 _ a.2)) hcard _ hinj le_top

end CFSG.SectionRank
