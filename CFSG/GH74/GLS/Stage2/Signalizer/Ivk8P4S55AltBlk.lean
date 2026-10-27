module

public import CFSG.GH74.GLS.Stage2.Signalizer.Odd87AltOrb
public import Mathlib.GroupTheory.IndexNormal

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltBlk

open Equiv Equiv.Perm Subgroup CFSG.GH74.GLS.Stage2.Signalizer.Odd87.AltOrb

variable {α : Type*} [Fintype α] [DecidableEq α]

@[expose] def stabS (T : Subgroup (Perm α)) (B : Set α) : Subgroup (Perm α) where
  carrier := {t | t ∈ T ∧ ∀ x, t x ∈ B ↔ x ∈ B}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨T.mul_mem ha hb, fun x => by rw [Perm.mul_apply, ha', hb']⟩
  one_mem' := ⟨T.one_mem, fun x => Iff.rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨T.inv_mem ha, fun x => ?_⟩
    have h1 : a (a⁻¹ x) = x := by simp
    have := ha' (a⁻¹ x)
    rw [h1] at this
    exact this.symm

@[expose] def fixB (T : Subgroup (Perm α)) (B : Set α) : Subgroup (Perm α) where
  carrier := {t | t ∈ T ∧ ∀ b ∈ B, t b = b}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    exact ⟨T.mul_mem ha hb, fun x hx => by rw [Perm.mul_apply, hb' x hx, ha' x hx]⟩
  one_mem' := ⟨T.one_mem, fun x _ => rfl⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨T.inv_mem ha, fun x hx => (Perm.inv_eq_iff_eq).2 (ha' x hx).symm⟩

omit [Fintype α] [DecidableEq α] in
theorem fixB_le (T : Subgroup (Perm α)) (B : Set α) : fixB T B ≤ T := fun _ h => h.1

omit [Fintype α] [DecidableEq α] in
theorem stabS_le (T : Subgroup (Perm α)) (B : Set α) : stabS T B ≤ T := fun _ h => h.1

omit [DecidableEq α] in
theorem fix_of_stab {p : ℕ} [hp : Fact p.Prime] {X : Subgroup (Perm α)} (hX : IsPGroup p ↥X)
    {y : α} (hB : (Orb X y).ncard = p) {h : Perm α} (hh : h ∈ X) (hy : h y = y) :
    ∀ b ∈ Orb X y, h b = b := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hX
  let S : Subgroup ↥X := MulAction.stabilizer ↥X y
  have hidx : S.index = p := by
    rw [MulAction.index_stabilizer, ← Orb_eq_orbit, hB]
  have hk0 : k ≠ 0 := by
    rintro rfl
    have hdvd : p ∣ Nat.card ↥X := hidx ▸ S.index_dvd_card
    rw [hk, pow_zero] at hdvd
    exact hp.out.one_lt.ne' (Nat.dvd_one.1 hdvd)
  have hmin : (Nat.card ↥X).minFac = p := by
    rw [hk]
    exact Nat.Prime.pow_minFac hp.out hk0
  have hnorm : S.Normal := Subgroup.normal_of_index_eq_minFac_card (hidx.trans hmin.symm)
  rintro b ⟨g, hg, rfl⟩
  have hmem : (⟨h, hh⟩ : ↥X) ∈ S := by
    show (⟨h, hh⟩ : ↥X) • y = y
    exact hy
  have h2 := hnorm.conj_mem _ hmem ⟨g⁻¹, X.inv_mem hg⟩
  have h3 : (g⁻¹ * h * g⁻¹⁻¹) y = y := h2
  have h5 : (g⁻¹ * h * g) y = y := by simpa using h3
  have h6 : h (g y) = g y := by
    have := congrArg g h5
    simpa using this
  exact h6

@[expose, reducible] def actOn (T' : Subgroup (Perm α)) (B : Set α)
    (h : ∀ t ∈ T', ∀ x, t x ∈ B ↔ x ∈ B) : MulAction ↥T' ↥B where
  smul t b := ⟨(t : Perm α) b, (h t t.2 b).2 b.2⟩
  one_smul _ := Subtype.ext rfl
  mul_smul _ _ _ := Subtype.ext rfl

theorem card_le_mul_fixB {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {X T' : Subgroup (Perm α)}
    (hX : IsPGroup p ↥X) (hT : IsPGroup 2 ↥T') (hN : T' ≤ normalizer (X : Set (Perm α)))
    {x₀ : α} (hB : (Orb X x₀).ncard = p)
    (hinv : ∀ t ∈ T', ∀ x, t x ∈ Orb X x₀ ↔ x ∈ Orb X x₀) :
    Nat.card ↥T' ≤ (p - 1) * Nat.card ↥(fixB T' (Orb X x₀)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B := Orb X x₀ with hBdef
  have hp3 : 3 ≤ p := by
    have := hp.out.two_le
    omega
  have hpodd : Odd p := hp.out.odd_of_ne_two hp2
  obtain ⟨y, hyB, hyfix⟩ : ∃ y ∈ B, ∀ t ∈ T', t y = y := by
    let _ := actOn T' B hinv
    have hmod := IsPGroup.card_modEq_card_fixedPoints hT ↥B
    have hBc : Nat.card ↥B = p := by rw [Nat.card_coe_set_eq]; exact hB
    rw [hBc] at hmod
    have hne : Nat.card ↥(MulAction.fixedPoints ↥T' ↥B) ≠ 0 := by
      intro h0
      rw [h0] at hmod
      have : p % 2 = 0 := hmod
      have h3 := Nat.odd_iff.mp hpodd
      omega
    have hpos : 0 < Nat.card ↥(MulAction.fixedPoints ↥T' ↥B) := Nat.pos_of_ne_zero hne
    obtain ⟨⟨⟨y, hyB⟩, hy⟩⟩ := (Nat.card_pos_iff.mp hpos).1
    refine ⟨y, hyB, fun t ht => ?_⟩
    have := hy ⟨t, ht⟩
    exact congrArg Subtype.val this
  have hOrbB : Orb X y = B := Orb_eq_of_mem hyB
  have hBy : (Orb X y).ncard = p := by rw [hOrbB]; exact hB
  obtain ⟨b, hbB, hby⟩ : ∃ b ∈ B, b ≠ y := by
    have h1 : 1 < B.ncard := by omega
    obtain ⟨a, c, ha, hc, hac⟩ := (Set.one_lt_ncard_iff (Set.toFinite _)).1 h1
    by_cases hay : a = y
    · exact ⟨c, hc, fun h => hac (hay.trans h.symm)⟩
    · exact ⟨a, ha, hay⟩
  have hXB : ∀ g ∈ X, ∀ c ∈ B, g c ∈ B := by
    rintro g hg c ⟨x, hx, rfl⟩
    exact ⟨g * x, X.mul_mem hg hx, rfl⟩
  have key : ∀ t ∈ T', t b = b → ∀ c ∈ B, t c = c := by
    intro t ht htb
    have hbOy : b ∈ Orb X y := by rw [hOrbB]; exact hbB
    obtain ⟨g, hgX, hgy⟩ := hbOy
    have htN := hN ht
    set g' : Perm α := t * g * t⁻¹ with hg'
    have hg'X : g' ∈ X := (mem_normalizer_iff.mp htN g).mp hgX
    have hg'y : g' y = b := by
      have h1 : t⁻¹ y = y := (Perm.inv_eq_iff_eq).2 (hyfix t ht).symm
      simp only [hg', Perm.mul_apply, h1, hgy, htb]
    have hhX : g⁻¹ * g' ∈ X := X.mul_mem (X.inv_mem hgX) hg'X
    have hhy : (g⁻¹ * g') y = y := by
      rw [Perm.mul_apply, hg'y, ← hgy]
      simp
    have hfixB : ∀ c ∈ Orb X y, (g⁻¹ * g') c = c := fix_of_stab hX hBy hhX hhy
    have hg'g : ∀ c ∈ B, g' c = g c := by
      intro c hc
      have h1 := hfixB c (by rw [hOrbB]; exact hc)
      rw [Perm.mul_apply] at h1
      have h2 := congrArg g h1
      simpa using h2
    have hgen : ∀ c ∈ B, ∃ n : ℕ, (g ^ n) y = c := by
      let Y : Subgroup (Perm α) := zpowers g
      have hYX : Y ≤ X := (zpowers_le).2 hgX
      have hYp : IsPGroup p ↥Y := hX.to_le hYX
      obtain ⟨j, hj⟩ := ncard_Orb_pow hYp y
      have hsub : Orb Y y ⊆ B := by
        rintro c ⟨z, hz, rfl⟩
        rw [← hOrbB]
        exact ⟨z, hYX hz, rfl⟩
      have hy_in : y ∈ Orb Y y := mem_Orb_self Y y
      have hb_in : b ∈ Orb Y y := ⟨g, mem_zpowers g, hgy⟩
      have h2 : 2 ≤ (Orb Y y).ncard := by
        have : 1 < (Orb Y y).ncard :=
          (Set.one_lt_ncard_iff (Set.toFinite _)).2 ⟨y, b, hy_in, hb_in, hby.symm⟩
        omega
      have hjp : p ^ j ≤ p := by
        have := Set.ncard_le_ncard hsub (Set.toFinite _)
        rw [hj, hB] at this
        exact this
      have hj1 : j = 1 := by
        rcases Nat.lt_or_ge j 2 with hj2 | hj2
        · interval_cases j
          · rw [pow_zero] at hj
            omega
          · rfl
        · exfalso
          have h3 : p ^ 2 ≤ p ^ j := Nat.pow_le_pow_right hp.out.pos hj2
          have h4 : p ^ 2 = p * p := sq p
          have h5 : 2 * p ≤ p * p := Nat.mul_le_mul_right p hp.out.two_le
          omega
      have hEq : Orb Y y = B :=
        Set.eq_of_subset_of_ncard_le hsub (by rw [hB, hj, hj1, pow_one]) (Set.toFinite _)
      intro c hc
      rw [← hEq] at hc
      obtain ⟨z, hz, rfl⟩ := hc
      have : z ∈ Submonoid.powers g := mem_powers_iff_mem_zpowers.2 hz
      obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff _ _).1 this
      exact ⟨n, by rw [hn]⟩
    have hpowB : ∀ n : ℕ, (g ^ n) y ∈ B := by
      intro n
      induction n with
      | zero => simpa using hyB
      | succ n ih =>
        rw [pow_succ', Perm.mul_apply]
        exact hXB g hgX _ ih
    have hpow : ∀ n : ℕ, t ((g ^ n) y) = (g ^ n) y := by
      intro n
      induction n with
      | zero => simpa using hyfix t ht
      | succ n ih =>
        have h1 : t (g ((g ^ n) y)) = g' (t ((g ^ n) y)) := by simp [hg', Perm.mul_apply]
        rw [pow_succ', Perm.mul_apply, h1, ih, hg'g _ (hpowB n)]
    intro c hc
    obtain ⟨n, rfl⟩ := hgen c hc
    exact hpow n
  have hOsub : MulAction.orbit ↥T' b ⊆ B \ {y} := by
    rintro _ ⟨t, rfl⟩
    refine ⟨(hinv t t.2 b).2 hbB, ?_⟩
    intro h
    have h1 : (t : Perm α) b = (t : Perm α) y := by
      rw [hyfix t t.2]
      exact h
    exact hby ((t : Perm α).injective h1)
  have hOcard : (MulAction.orbit ↥T' b).ncard ≤ p - 1 := by
    calc (MulAction.orbit ↥T' b).ncard ≤ (B \ {y}).ncard :=
          Set.ncard_le_ncard hOsub (Set.toFinite _)
      _ = p - 1 := by rw [Set.ncard_sdiff_singleton_of_mem hyB, hB]
  have hstab : MulAction.stabilizer ↥T' b = (fixB T' B).subgroupOf T' := by
    ext t
    simp only [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨t.2, key t t.2 h⟩
    · intro h
      exact h.2 b hbB
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥T' b)
  rw [MulAction.index_stabilizer, hstab] at h1
  have h2 : Nat.card ↥((fixB T' B).subgroupOf T') = Nat.card ↥(fixB T' B) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (fixB_le T' B)).toEquiv
  rw [h2] at h1
  rw [← h1, mul_comm (p - 1)]
  exact Nat.mul_le_mul_left _ hOcard

theorem relIndex_mul_ncard_le {X T : Subgroup (Perm α)}
    (hN : T ≤ normalizer (X : Set (Perm α))) (x₀ : α) :
    (stabS T (Orb X x₀)).relIndex T * (Orb X x₀).ncard ≤ Fintype.card α := by
  classical
  set B := Orb X x₀ with hBdef
  let H : Subgroup ↥T := (stabS T B).subgroupOf T
  let r : (↥T ⧸ H) → ↥T := fun q => Quotient.out q
  have hr : ∀ q, (QuotientGroup.mk (r q) : ↥T ⧸ H) = q := fun q => Quotient.out_eq' q
  let S : (↥T ⧸ H) → Finset α := fun q => ((r q : Perm α) '' B).toFinset
  have himg : ∀ q, (r q : Perm α) '' B = Orb X ((r q : Perm α) x₀) := fun q =>
    image_Orb (hN (r q).2) x₀
  have hdisj : ∀ q q', q ≠ q' → Disjoint (S q) (S q') := by
    intro q q' hqq'
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [S, Set.mem_toFinset] at hx hx'
    rw [himg] at hx hx'
    have hEq : Orb X ((r q : Perm α) x₀) = Orb X ((r q' : Perm α) x₀) :=
      Orb_eq_of_mem_inter hx hx'
    apply hqq'
    rw [← hr q, ← hr q', QuotientGroup.eq]
    show (((r q)⁻¹ * r q' : ↥T) : Perm α) ∈ stabS T B
    refine ⟨T.mul_mem (T.inv_mem (r q).2) (r q').2, fun x => ?_⟩
    have h1 : (r q : Perm α) '' B = (r q' : Perm α) '' B := by rw [himg, himg, hEq]
    have h2 : (r q' : Perm α) x ∈ (r q' : Perm α) '' B ↔ x ∈ B :=
      (r q' : Perm α).injective.mem_set_image
    rw [← h1] at h2
    have h3 : (r q : Perm α)⁻¹ ((r q' : Perm α) x) ∈ B ↔
        (r q' : Perm α) x ∈ (r q : Perm α) '' B := by
      constructor
      · intro h
        exact ⟨_, h, by simp⟩
      · rintro ⟨c, hc, hcx⟩
        have : (r q : Perm α)⁻¹ ((r q' : Perm α) x) = c := by
          rw [← hcx]; simp
        rw [this]; exact hc
    show ((r q : Perm α)⁻¹ * (r q' : Perm α)) x ∈ B ↔ x ∈ B
    rw [Perm.mul_apply, h3, h2]
  have hcard : ∀ q, (S q).card = B.ncard := by
    intro q
    simp only [S]
    rw [← Set.ncard_eq_toFinset_card', Set.ncard_image_of_injective _ (r q : Perm α).injective]
  have hsum : (Finset.univ.biUnion S).card = Fintype.card (↥T ⧸ H) * B.ncard := by
    rw [Finset.card_biUnion (fun q _ q' _ h => hdisj q q' h)]
    simp [hcard]
  have hle : (Finset.univ.biUnion S).card ≤ Fintype.card α := Finset.card_le_univ _
  rw [hsum] at hle
  have hidx : (stabS T B).relIndex T = Fintype.card (↥T ⧸ H) := by
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [hidx]
  exact hle

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8.AltBlk
