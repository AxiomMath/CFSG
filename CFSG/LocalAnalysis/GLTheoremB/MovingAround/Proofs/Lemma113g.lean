module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma113b

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open scoped Pointwise

namespace Lemma113g

open Classical in
theorem card_and_prod_fixed {K : Type} [Group K] [Finite K] {p : ℕ} [Fact p.Prime] {α : Type}
    [MulAction K α] [Finite α] {M : Type} [CommMonoid M] (hK : IsPGroup p K) (F : α → M)
    (hF : ∀ (k : K) (t : α), F (k • t) = F t) (T : Finset α) :
    (∀ k : K, ∀ t ∈ T, k • t ∈ T) → (∀ t ∈ T, F t ^ p = 1) →
      T.card ≡ (T.filter (fun t => ∀ k : K, k • t = t)).card [MOD p] ∧
        ∏ t ∈ T, F t = ∏ t ∈ T.filter (fun t => ∀ k : K, k • t = t), F t := by
  induction T using Finset.strongInduction with
  | H T ih =>
  intro hT hpow
  by_cases hall : ∀ t ∈ T, ∀ k : K, k • t = t
  · rw [Finset.filter_true_of_mem hall]
    exact ⟨Nat.ModEq.refl _, rfl⟩
  push Not at hall
  obtain ⟨t₀, ht₀, k₀, hk₀⟩ := hall
  set O : Finset α := T.filter (fun u => u ∈ MulAction.orbit K t₀) with hO
  have hmemO : ∀ u, u ∈ O ↔ u ∈ T ∧ u ∈ MulAction.orbit K t₀ := fun u => Finset.mem_filter
  have hOT : O ⊆ T := Finset.filter_subset _ _
  have ht₀O : t₀ ∈ O := (hmemO t₀).2 ⟨ht₀, MulAction.mem_orbit_self t₀⟩
  have hk₀O : k₀ • t₀ ∈ O := (hmemO _).2 ⟨hT k₀ t₀ ht₀, MulAction.mem_orbit t₀ k₀⟩
  have hOcard : O.card = Nat.card (MulAction.orbit K t₀) := by
    rw [← Set.ncard_coe_finset O, Nat.card_coe_set_eq]
    congr 1
    ext u
    simp only [Finset.mem_coe, hmemO]
    constructor
    · exact fun h => h.2
    · intro hu
      obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 hu
      exact ⟨hT k t₀ ht₀, hu⟩
  obtain ⟨n, hn⟩ := IsPGroup.card_orbit hK t₀
  have hOone : 1 < O.card :=
    Finset.one_lt_card.2 ⟨t₀, ht₀O, k₀ • t₀, hk₀O, fun h => hk₀ h.symm⟩
  have hOp : p ∣ O.card := by
    rw [hOcard, hn] at hOone ⊢
    have hn0 : n ≠ 0 := by
      rintro rfl
      simp at hOone
    exact dvd_pow_self p hn0
  have hOmod : O.card ≡ 0 [MOD p] := Nat.modEq_zero_iff_dvd.2 hOp
  have hFO : ∀ u ∈ O, F u = F t₀ := by
    intro u hu
    obtain ⟨k, rfl⟩ := MulAction.mem_orbit_iff.1 ((hmemO u).1 hu).2
    exact hF k t₀
  have hprodO : ∏ u ∈ O, F u = 1 := by
    rw [Finset.prod_congr rfl hFO, Finset.prod_const]
    obtain ⟨m, hm⟩ := hOp
    rw [hm, pow_mul, hpow t₀ ht₀, one_pow]
  have hstab : ∀ k : K, ∀ u ∈ T \ O, k • u ∈ T \ O := by
    intro k u hu
    rw [Finset.mem_sdiff] at hu ⊢
    refine ⟨hT k u hu.1, fun hkuO => hu.2 ?_⟩
    obtain ⟨-, hkuorb⟩ := (hmemO _).1 hkuO
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 hkuorb
    refine (hmemO u).2 ⟨hu.1, MulAction.mem_orbit_iff.2 ⟨k⁻¹ * g, ?_⟩⟩
    rw [mul_smul, hg, inv_smul_smul]
  have hOfix : ∀ u ∈ O, ∃ k : K, k • u ≠ u := by
    intro u hu
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.1 ((hmemO u).1 hu).2
    by_contra hcon
    push Not at hcon
    have ht : t₀ = u := by
      calc t₀ = g⁻¹ • (g • t₀) := (inv_smul_smul g t₀).symm
        _ = g⁻¹ • u := by rw [hg]
        _ = u := hcon g⁻¹
    exact hk₀ (by rw [ht]; exact hcon k₀)
  have hfilt : T.filter (fun t => ∀ k : K, k • t = t) =
      (T \ O).filter (fun t => ∀ k : K, k • t = t) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hu, hfix⟩
      refine ⟨⟨hu, fun hO' => ?_⟩, hfix⟩
      obtain ⟨k, hk⟩ := hOfix u hO'
      exact hk (hfix k)
    · rintro ⟨⟨hu, -⟩, hfix⟩
      exact ⟨hu, hfix⟩
  have hsub : T \ O ⊂ T := Finset.sdiff_ssubset hOT ⟨t₀, ht₀O⟩
  obtain ⟨ihc, ihp⟩ := ih (T \ O) hsub hstab (fun t ht => hpow t (Finset.sdiff_subset ht))
  have hcardsplit : (T \ O).card + O.card = T.card := Finset.card_sdiff_add_card_eq_card hOT
  have hprodsplit : (∏ u ∈ T \ O, F u) * ∏ u ∈ O, F u = ∏ u ∈ T, F u :=
    Finset.prod_sdiff hOT
  constructor
  · rw [hfilt, ← hcardsplit]
    have := Nat.ModEq.add ihc hOmod
    simpa using this
  · rw [hfilt, ← hprodsplit, ihp, hprodO, mul_one]

section Transfer

variable {X : Type} [Group X] [Finite X] {C : Type} [CommGroup C]

open Classical in
noncomputable def termAt (H : Subgroup X) (ϕ : H →* C) (b x : X) : C :=
  if h : x⁻¹ * b * x ∈ H then ϕ ⟨x⁻¹ * b * x, h⟩ else 1

theorem termAt_mul_right {H : Subgroup X} (ϕ : H →* C) (b x : X) {h : X} (hh : h ∈ H) :
    termAt H ϕ b (x * h) = termAt H ϕ b x := by
  unfold termAt
  by_cases hy : x⁻¹ * b * x ∈ H
  · have hy' : (x * h)⁻¹ * b * (x * h) ∈ H := by
      have e : (x * h)⁻¹ * b * (x * h) = h⁻¹ * (x⁻¹ * b * x) * h := by group
      rw [e]
      exact H.mul_mem (H.mul_mem (H.inv_mem hh) hy) hh
    rw [dif_pos hy, dif_pos hy']
    have e : (⟨(x * h)⁻¹ * b * (x * h), hy'⟩ : H) =
        ⟨h, hh⟩⁻¹ * ⟨x⁻¹ * b * x, hy⟩ * ⟨h, hh⟩ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e, map_mul, map_mul, map_inv, mul_comm ((ϕ ⟨h, hh⟩)⁻¹), mul_assoc, inv_mul_cancel,
      mul_one]
  · rw [dif_neg hy]
    have hy' : ¬ (x * h)⁻¹ * b * (x * h) ∈ H := by
      intro hy'
      apply hy
      have e : x⁻¹ * b * x = h * ((x * h)⁻¹ * b * (x * h)) * h⁻¹ := by group
      rw [e]
      exact H.mul_mem (H.mul_mem hh hy') (H.inv_mem hh)
    rw [dif_neg hy']

theorem termAt_mul_left {H : Subgroup X} (ϕ : H →* C) (b : X) {s x : X} (hs : b * s = s * b) :
    termAt H ϕ b (s * x) = termAt H ϕ b x := by
  have hs' : s⁻¹ * b * s = b := by
    calc s⁻¹ * b * s = s⁻¹ * (b * s) := by group
      _ = s⁻¹ * (s * b) := by rw [hs]
      _ = b := by group
  have e : (s * x)⁻¹ * b * (s * x) = x⁻¹ * b * x := by
    calc (s * x)⁻¹ * b * (s * x) = x⁻¹ * (s⁻¹ * b * s) * x := by group
      _ = x⁻¹ * b * x := by rw [hs']
  unfold termAt
  rw [e]

theorem termAt_eq_of_coe_eq {H : Subgroup X} (ϕ : H →* C) (b : X) {x y : X}
    (h : (x : X ⧸ H) = (y : X ⧸ H)) : termAt H ϕ b x = termAt H ϕ b y := by
  have hxy : x⁻¹ * y ∈ H := QuotientGroup.eq.1 h
  have e : y = x * (x⁻¹ * y) := by group
  calc termAt H ϕ b x = termAt H ϕ b (x * (x⁻¹ * y)) := (termAt_mul_right ϕ b x hxy).symm
    _ = termAt H ϕ b y := by rw [← e]

theorem termAt_pow {H : Subgroup X} (ϕ : H →* C) {b : X} {p : ℕ} (hbp : b ^ p = 1) (x : X) :
    termAt H ϕ b x ^ p = 1 := by
  unfold termAt
  split_ifs with h
  · rw [← map_pow]
    have h1 : (⟨x⁻¹ * b * x, h⟩ : H) ^ p = 1 := by
      apply Subtype.ext
      show (x⁻¹ * b * x) ^ p = 1
      rw [show x⁻¹ * b * x = x⁻¹ * b * x⁻¹⁻¹ from by rw [inv_inv], conj_pow, hbp]
      simp
    rw [h1, map_one]
  · exact one_pow p

theorem iterate_smul_fun {M : Type} [Group M] (M' : Type) [MulAction M M'] (b : M) (n : ℕ) (x : M') :
    (fun y : M' => b • y)^[n] x = b ^ n • x := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', ih, pow_succ', mul_smul]

theorem mem_of_smul_fix (H : Subgroup X) {b x : X} (h : b • (x : X ⧸ H) = (x : X ⧸ H)) :
    x⁻¹ * b * x ∈ H := by
  have h1 : (b * x)⁻¹ * x ∈ H := QuotientGroup.eq.1 h
  have e : x⁻¹ * b * x = ((b * x)⁻¹ * x)⁻¹ := by group
  rw [e]
  exact H.inv_mem h1

theorem coe_out_eq (H : Subgroup X) (ω : X ⧸ H) : ((Quotient.out ω : X) : X ⧸ H) = ω :=
  QuotientGroup.out_eq' ω

open Classical in
theorem transfer_eq_prod_fix (H : Subgroup X) [Fintype (X ⧸ H)] (ϕ : H →* C) {b : X} {p : ℕ}
    (hp : p.Prime) (hbp : b ^ p = 1) :
    MonoidHom.transfer ϕ b =
      ∏ ω ∈ Finset.univ.filter (fun ω : X ⧸ H => b • ω = ω), termAt H ϕ b (Quotient.out ω) := by
  letI : Fintype (Quotient (MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H))) :=
    Fintype.ofFinite _
  rw [MonoidHom.transfer_eq_prod_quotient_orbitRel_zpowers_quot ϕ b]
  have out_eq_of_fix : ∀ ω : X ⧸ H, b • ω = ω →
      (Quotient.mk'' ω : Quotient (MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H))).out = ω := by
    intro ω hω
    have h1 : (Quotient.mk'' ((Quotient.mk'' ω : Quotient
        (MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H))).out) :
        Quotient (MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H))) =
        Quotient.mk'' ω := Quotient.out_eq _
    have h2 : MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H)
        ((Quotient.mk'' ω : Quotient (MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H))).out) ω :=
      Quotient.exact h1
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h2
    obtain ⟨g, hg⟩ := h2
    have hgω : g • ω = ω := by
      have hb : b ∈ MulAction.stabilizer X ω := MulAction.mem_stabilizer_iff.2 hω
      have hz : Subgroup.zpowers b ≤ MulAction.stabilizer X ω := Subgroup.zpowers_le.2 hb
      exact MulAction.mem_stabilizer_iff.1 (hz g.2)
    rw [← hg, hgω]
  have hone : ∀ (y : X) (hy : y ∈ H), y = 1 → ϕ ⟨y, hy⟩ = 1 := by
    intro y hy h
    subst h
    have h1 : (⟨1, hy⟩ : H) = 1 := Subtype.ext rfl
    rw [h1, map_one]
  refine (Finset.prod_subset (Finset.subset_univ
    (Finset.univ.filter (fun q : Quotient (MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H)) =>
      Function.minimalPeriod (fun y : X ⧸ H => b • y) q.out = 1))) ?_).symm.trans ?_
  · intro q _ hq
    have hne : Function.minimalPeriod (fun y : X ⧸ H => b • y) q.out ≠ 1 := by
      intro h1
      exact hq (Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩)
    have hdvd : Function.minimalPeriod (fun y : X ⧸ H => b • y) q.out ∣ p := by
      apply Function.IsPeriodicPt.minimalPeriod_dvd
      show (fun y : X ⧸ H => b • y)^[p] q.out = q.out
      rw [iterate_smul_fun (X ⧸ H) b p q.out, hbp, one_smul]
    have hmp : Function.minimalPeriod (fun y : X ⧸ H => b • y) q.out = p := by
      rcases (Nat.dvd_prime hp).1 hdvd with h | h
      · exact absurd h hne
      · exact h
    apply hone
    rw [hmp, hbp]
    group
  · refine Finset.prod_nbij' (fun q => q.out)
      (fun ω : X ⧸ H => (Quotient.mk'' ω : Quotient (MulAction.orbitRel (Subgroup.zpowers b) (X ⧸ H))))
      ?_ ?_ ?_ ?_ ?_
    · intro q hq
      have h1 : Function.minimalPeriod (fun y : X ⧸ H => b • y) q.out = 1 :=
        (Finset.mem_filter.1 hq).2
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,
        Function.minimalPeriod_eq_one_iff_isFixedPt.1 h1⟩
    · intro ω hω
      have hωfix : b • ω = ω := (Finset.mem_filter.1 hω).2
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      rw [out_eq_of_fix ω hωfix]
      exact Function.minimalPeriod_eq_one_iff_isFixedPt.2 hωfix
    · intro q _
      exact Quotient.out_eq q
    · intro ω hω
      exact out_eq_of_fix ω (Finset.mem_filter.1 hω).2
    · intro q hq
      have hq1 : Function.minimalPeriod (fun y : X ⧸ H => b • y) q.out = 1 :=
        (Finset.mem_filter.1 hq).2
      have hqfix : b • q.out = q.out := Function.minimalPeriod_eq_one_iff_isFixedPt.1 hq1
      have hcoe : ((q.out.out : X) : X ⧸ H) = q.out := coe_out_eq H q.out
      have hmem : (q.out.out)⁻¹ * b * q.out.out ∈ H :=
        mem_of_smul_fix H (by rw [hcoe]; exact hqfix)
      unfold termAt
      rw [dif_pos hmem]
      congr 1
      apply Subtype.ext
      simp only [hq1, pow_one]

end Transfer

section Extremal

variable {X : Type} [Group X] [Finite X]

theorem isExtremalIn_of_sylow {p : ℕ} [Fact p.Prime] {H : Subgroup X} (hH : IsPGroup p ↥H)
    {b : X} {S : Subgroup X} (hS : IsSylowIn p (Subgroup.centralizer ({b} : Set X)) S) (x : X)
    (hSx : ∀ s ∈ S, x⁻¹ * s * x ∈ H) :
    Lemma113b.IsExtremalIn X H (x⁻¹ * b * x) := by
  classical
  set y : X := x⁻¹ * b * x with hy
  set K : Subgroup X := Subgroup.centralizer ({y} : Set X) with hK
  set T : Subgroup X := S.comap (MulAut.conj x).toMonoidHom with hT
  have hTmem : ∀ r : X, r ∈ T ↔ x * r * x⁻¹ ∈ S := fun r => Iff.rfl
  have hSC : ∀ s ∈ S, b * s = s * b := fun s hs =>
    Subgroup.mem_centralizer_iff.1 (hS.1 hs) b (Set.mem_singleton b)
  have hTK : T ≤ K := by
    intro r hr
    have hc := hSC _ ((hTmem r).1 hr)
    rw [hK, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    calc y * r = x⁻¹ * (b * (x * r * x⁻¹)) * x := by rw [hy]; group
      _ = x⁻¹ * ((x * r * x⁻¹) * b) * x := by rw [hc]
      _ = r * y := by rw [hy]; group
  have hTH : T ≤ H := by
    intro r hr
    have h1 := hSx _ ((hTmem r).1 hr)
    have e : x⁻¹ * (x * r * x⁻¹) * x = r := by group
    rw [e] at h1
    exact h1
  have hTp : IsPGroup p ↥T := hS.2.1.comap_of_injective _ (MulAut.conj x).injective
  have hTmax : ∀ R' : Subgroup X, R' ≤ K → IsPGroup p ↥R' → T ≤ R' → R' = T := by
    intro R' hR'K hR'p hTR'
    set R'' : Subgroup X := R'.comap (MulAut.conj x⁻¹).toMonoidHom with hR''
    have hR''mem : ∀ c : X, c ∈ R'' ↔ x⁻¹ * c * x ∈ R' := fun c => by
      show x⁻¹ * c * x⁻¹⁻¹ ∈ R' ↔ x⁻¹ * c * x ∈ R'
      rw [inv_inv]
    have hR''C : R'' ≤ Subgroup.centralizer ({b} : Set X) := by
      intro c hc
      have hr := Subgroup.mem_centralizer_iff.1 (hR'K ((hR''mem c).1 hc)) y (Set.mem_singleton y)
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.1 hh]
      calc b * c = x * (y * (x⁻¹ * c * x)) * x⁻¹ := by rw [hy]; group
        _ = x * ((x⁻¹ * c * x) * y) * x⁻¹ := by rw [hr]
        _ = c * b := by rw [hy]; group
    have hR''p : IsPGroup p ↥R'' := hR'p.comap_of_injective _ (MulAut.conj x⁻¹).injective
    have hSR'' : S ≤ R'' := by
      intro s hs
      rw [hR''mem]
      apply hTR'
      rw [hTmem]
      have e : x * (x⁻¹ * s * x) * x⁻¹ = s := by group
      rw [e]
      exact hs
    have hR''eq : R'' = S := hS.2.2 R'' hR''C hR''p hSR''
    ext r
    constructor
    · intro hr
      have hc : x * r * x⁻¹ ∈ R'' := by
        rw [hR''mem]
        have e : x⁻¹ * (x * r * x⁻¹) * x = r := by group
        rw [e]
        exact hr
      rw [hR''eq] at hc
      exact (hTmem r).2 hc
    · intro hr
      exact hTR' hr
  have hTsyl : IsSylowIn p K T := ⟨hTK, hTp, hTmax⟩
  have hHKT : H ⊓ K = T :=
    hTsyl.2.2 (H ⊓ K) inf_le_right (hH.to_le inf_le_left) (le_inf hTH hTK)
  intro z hzH hz'
  obtain ⟨x', hz⟩ := hz'
  show Nat.card ↥(H ⊓ Subgroup.centralizer ({z} : Set X)) ≤ Nat.card ↥(H ⊓ K)
  rw [hHKT]
  set D : Subgroup X := H ⊓ Subgroup.centralizer ({z} : Set X) with hD
  have hDp : IsPGroup p ↥D := hH.to_le inf_le_left
  set R₂ : Subgroup X := D.comap (MulAut.conj x'⁻¹).toMonoidHom with hR₂
  have hR₂mem : ∀ c : X, c ∈ R₂ ↔ x'⁻¹ * c * x' ∈ D := fun c => by
    show x'⁻¹ * c * x'⁻¹⁻¹ ∈ D ↔ x'⁻¹ * c * x' ∈ D
    rw [inv_inv]
  have hR₂K : R₂ ≤ K := by
    intro c hc
    have hcD := (hR₂mem c).1 hc
    have hr := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hcD).2 z (Set.mem_singleton z)
    rw [hK, Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.1 hh]
    calc y * c = x' * (z * (x'⁻¹ * c * x')) * x'⁻¹ := by rw [hz]; group
      _ = x' * ((x'⁻¹ * c * x') * z) * x'⁻¹ := by rw [hr]
      _ = c * y := by rw [hz]; group
  have hR₂p : IsPGroup p ↥R₂ := hDp.comap_of_injective _ (MulAut.conj x'⁻¹).injective
  obtain ⟨c₀, -, hc₀⟩ := Lemma113b.exists_conj_mem_of_isSylowIn hTsyl hR₂K hR₂p
  have hmemR : ∀ r : D, c₀ * (x' * (r : X) * x'⁻¹) * c₀⁻¹ ∈ T := by
    intro r
    apply hc₀
    rw [hR₂mem]
    have e : x'⁻¹ * (x' * (r : X) * x'⁻¹) * x' = r := by group
    rw [e]
    exact r.2
  let f : D → T := fun r => ⟨c₀ * (x' * (r : X) * x'⁻¹) * c₀⁻¹, hmemR r⟩
  have hf : Function.Injective f := by
    intro r₁ r₂ h
    have h2 : c₀ * (x' * (r₁ : X) * x'⁻¹) * c₀⁻¹ = c₀ * (x' * (r₂ : X) * x'⁻¹) * c₀⁻¹ :=
      congrArg Subtype.val h
    have h3 : x' * (r₁ : X) * x'⁻¹ = x' * (r₂ : X) * x'⁻¹ :=
      mul_left_cancel (mul_right_cancel h2)
    apply Subtype.ext
    calc (r₁ : X) = x'⁻¹ * (x' * (r₁ : X) * x'⁻¹) * x' := by group
      _ = x'⁻¹ * (x' * (r₂ : X) * x'⁻¹) * x' := by rw [h3]
      _ = (r₂ : X) := by group
  exact Nat.card_le_card_of_injective f hf

end Extremal

theorem transfer_core {X : Type} [Group X] [Finite X] {p : ℕ} [Fact p.Prime] {C : Type}
    [CommGroup C] (H : Subgroup X)
    (hHp : IsPGroup p ↥H) (hHi : ¬ p ∣ H.index) (φ : H →* C) (b : X) (hbH : b ∈ H)
    (hord : orderOf b = p) (hφb : φ ⟨b, hbH⟩ ≠ 1)
    (hext : ∀ (y : X) (hyH : y ∈ H), Lemma113b.IsExtremalIn X H y →
      (∃ x : X, y = x⁻¹ * b * x) → φ ⟨b⁻¹ * y, H.mul_mem (H.inv_mem hbH) hyH⟩ = 1) :
    MonoidHom.transfer φ b ≠ 1 := by
  classical
  letI : Fintype (X ⧸ H) := Fintype.ofFinite _
  have hp : p.Prime := Fact.out
  have hbp : b ^ p = 1 := by
    rw [← hord]
    exact pow_orderOf_eq_one b
  have hzp : IsPGroup p ↥(Subgroup.zpowers b) :=
    IsPGroup.iff_card.2 ⟨1, by rw [Nat.card_zpowers, hord, pow_one]⟩
  have hbC : Subgroup.zpowers b ≤ Subgroup.centralizer ({b} : Set X) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_centralizer_iff.2 (fun h hh => by rw [Set.mem_singleton_iff.1 hh])
  obtain ⟨S, hS, -⟩ := Lemma113b.exists_sylowIn_above' hbC hzp
  have hSC : ∀ s ∈ S, b * s = s * b := fun s hs =>
    Subgroup.mem_centralizer_iff.1 (hS.1 hs) b (Set.mem_singleton b)
  have htr := transfer_eq_prod_fix H φ hp hbp
  set Fix : Finset (X ⧸ H) := Finset.univ.filter (fun ω : X ⧸ H => b • ω = ω) with hFix
  set F : X ⧸ H → C := fun ω => termAt H φ b (Quotient.out ω) with hF
  have hFS : ∀ (k : S) (ω : X ⧸ H), F (k • ω) = F ω := by
    intro k ω
    have h1 : ((Quotient.out (k • ω) : X) : X ⧸ H) =
        (((k : X) * Quotient.out ω : X) : X ⧸ H) := by
      rw [coe_out_eq H (k • ω)]
      calc k • ω = (k : X) • ω := rfl
        _ = (k : X) • ((Quotient.out ω : X) : X ⧸ H) := by rw [coe_out_eq H ω]
        _ = (((k : X) * Quotient.out ω : X) : X ⧸ H) := rfl
    simp only [hF]
    rw [termAt_eq_of_coe_eq φ b h1, termAt_mul_left φ b (hSC k k.2)]
  have hFpow : ∀ ω, F ω ^ p = 1 := fun ω => termAt_pow φ hbp (Quotient.out ω)
  have hFixS : ∀ (k : S), ∀ ω ∈ Fix, k • ω ∈ Fix := by
    intro k ω hω
    have hωb : b • ω = ω := (Finset.mem_filter.1 hω).2
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    show b • ((k : X) • ω) = (k : X) • ω
    rw [← mul_smul, hSC k k.2, mul_smul, hωb]
  obtain ⟨hcard1, hprod1⟩ :=
    card_and_prod_fixed (K := S) (α := X ⧸ H) (M := C) hS.2.1 F hFS Fix hFixS
      (fun t _ => hFpow t)
  have hvalS : ∀ ω ∈ Fix.filter (fun t => ∀ k : S, k • t = t), F ω = φ ⟨b, hbH⟩ := by
    intro ω hω
    obtain ⟨hωFix, hωS⟩ := Finset.mem_filter.1 hω
    have hωb : b • ω = ω := (Finset.mem_filter.1 hωFix).2
    have hxω : ((Quotient.out ω : X) : X ⧸ H) = ω := coe_out_eq H ω
    have hSx : ∀ s ∈ S, (Quotient.out ω)⁻¹ * s * Quotient.out ω ∈ H := by
      intro s hs
      have h1 := hωS ⟨s⁻¹, S.inv_mem hs⟩
      have h2 : ((s⁻¹ * Quotient.out ω : X) : X ⧸ H) = ((Quotient.out ω : X) : X ⧸ H) := by
        calc ((s⁻¹ * Quotient.out ω : X) : X ⧸ H) = s⁻¹ • ((Quotient.out ω : X) : X ⧸ H) := rfl
          _ = s⁻¹ • ω := by rw [hxω]
          _ = ω := h1
          _ = ((Quotient.out ω : X) : X ⧸ H) := hxω.symm
      have h3 := QuotientGroup.eq.1 h2
      have e : (Quotient.out ω)⁻¹ * s * Quotient.out ω =
          (s⁻¹ * Quotient.out ω)⁻¹ * Quotient.out ω := by group
      rw [e]
      exact h3
    have hyH : (Quotient.out ω)⁻¹ * b * Quotient.out ω ∈ H :=
      mem_of_smul_fix H (by rw [hxω]; exact hωb)
    have hext' : Lemma113b.IsExtremalIn X H ((Quotient.out ω)⁻¹ * b * Quotient.out ω) :=
      isExtremalIn_of_sylow hHp hS (Quotient.out ω) hSx
    have h1 := hext _ hyH hext' ⟨Quotient.out ω, rfl⟩
    have e : (⟨(Quotient.out ω)⁻¹ * b * Quotient.out ω, hyH⟩ : H) =
        ⟨b, hbH⟩ * ⟨b⁻¹ * ((Quotient.out ω)⁻¹ * b * Quotient.out ω),
          H.mul_mem (H.inv_mem hbH) hyH⟩ := by
      apply Subtype.ext
      simp
    simp only [hF]
    unfold termAt
    rw [dif_pos hyH, e, map_mul, h1, mul_one]
  have hcardb := card_and_prod_fixed (K := Subgroup.zpowers b) (α := X ⧸ H) (M := C) hzp
    (fun _ => (1 : C)) (fun _ _ => rfl) Finset.univ (fun _ _ _ => Finset.mem_univ _)
    (fun _ _ => one_pow p)
  have hfixb : Finset.univ.filter (fun t : X ⧸ H => ∀ k : Subgroup.zpowers b, k • t = t) = Fix := by
    apply Finset.filter_congr
    intro ω _
    constructor
    · intro h
      exact h ⟨b, Subgroup.mem_zpowers b⟩
    · intro h k
      have hb : b ∈ MulAction.stabilizer X ω := MulAction.mem_stabilizer_iff.2 h
      have hz : Subgroup.zpowers b ≤ MulAction.stabilizer X ω := Subgroup.zpowers_le.2 hb
      exact MulAction.mem_stabilizer_iff.1 (hz k.2)
  have hcard_univ : (Finset.univ : Finset (X ⧸ H)).card = Nat.card (X ⧸ H) := by
    rw [Finset.card_univ, Nat.card_eq_fintype_card]
  have hN : Nat.card (X ⧸ H) ≡ (Fix.filter (fun t => ∀ k : S, k • t = t)).card [MOD p] := by
    have h1 : Nat.card (X ⧸ H) ≡ Fix.card [MOD p] := by
      rw [← hcard_univ, ← hfixb]
      exact hcardb.1
    exact h1.trans hcard1
  have hndvd : ¬ p ∣ Nat.card (X ⧸ H) := by
    rwa [Subgroup.index_eq_card] at hHi
  have hpN : ¬ p ∣ (Fix.filter (fun t => ∀ k : S, k • t = t)).card := fun h =>
    hndvd ((hN.dvd_iff dvd_rfl).2 h)
  intro htr1
  have hval : MonoidHom.transfer φ b = φ ⟨b, hbH⟩ ^ (Fix.filter (fun t => ∀ k : S, k • t = t)).card := by
    calc MonoidHom.transfer φ b = ∏ ω ∈ Fix, F ω := htr
      _ = ∏ ω ∈ Fix.filter (fun t => ∀ k : S, k • t = t), F ω := hprod1
      _ = ∏ ω ∈ Fix.filter (fun t => ∀ k : S, k • t = t), φ ⟨b, hbH⟩ :=
          Finset.prod_congr rfl hvalS
      _ = φ ⟨b, hbH⟩ ^ (Fix.filter (fun t => ∀ k : S, k • t = t)).card := Finset.prod_const _
  rw [hval] at htr1
  have hpowφ : φ ⟨b, hbH⟩ ^ p = 1 := by
    rw [← map_pow]
    have h1 : (⟨b, hbH⟩ : H) ^ p = 1 := Subtype.ext (by simpa using hbp)
    rw [h1, map_one]
  have hordφ : orderOf (φ ⟨b, hbH⟩) = p := orderOf_eq_prime hpowφ hφb
  have hdvd : p ∣ (Fix.filter (fun t => ∀ k : S, k • t = t)).card := by
    rw [← hordφ]
    exact orderOf_dvd_of_pow_eq_one htr1
  exact hpN hdvd

theorem input32_7_holds : Lemma113b.Input32_7 := by
  intro X _ _ p _ P C _ φ b hbP hord hφb hext
  exact transfer_core (X := X) (P : Subgroup X) P.isPGroup' P.not_dvd_index φ b hbP hord hφb hext

section PieceD

@[expose] def PieceD_SubEConj : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (_h : Cfg113 G m B M E A a e K Q) (_hC : Claim113C E A Q) (R : Subgroup G),
    IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R →
      ∀ g : G, g⁻¹ * e * g ∈ R →
        g⁻¹ * e * g ∈ E ∧ ∃ z ∈ R, z⁻¹ * (g⁻¹ * e * g) * z ∈ Subgroup.zpowers e

@[expose] def PieceD_SubNorm : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (_h : Cfg113 G m B M E A a e K Q) (_hC : Claim113C E A Q),
    Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
    Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) ≤
      Subgroup.normalizer (K : Set G) ∧
    (∀ q ∈ Q, (∃ k ∈ K, ∀ u ∈ K, ∃ z ∈ GLAPPrimeCoreOf 3 K, q * u * q⁻¹ = k * u * k⁻¹ * z) →
      q ∈ E)

@[expose] def PieceD_SubOut : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (_h : Cfg113 G m B M E A a e K Q) (_hC : Claim113C E A Q),
    ∀ x ∈ Subgroup.normalizer (K : Set G), ∀ n ∈ Subgroup.normalizer (K : Set G),
      ∃ k ∈ K, ∀ u ∈ K, ∃ z ∈ GLAPPrimeCoreOf 3 K,
        (x⁻¹ * n⁻¹ * x * n) * u * (x⁻¹ * n⁻¹ * x * n)⁻¹ = k * u * k⁻¹ * z

@[expose] def PieceD_SubR4 : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {m : ℕ} {B M E A : Subgroup G} {a e : G} {K Q : Subgroup G}
    (_h : Cfg113 G m B M E A a e K Q) (_hC : Claim113C E A Q) (R : Subgroup G),
    IsSylowIn 3 (Subgroup.normalizer (E : Set G)) R → Q ≤ R → Lemma113b.PieceD_R4 E R

theorem pieceD_claims_of_inputs (hE : PieceD_SubEConj) (hN : PieceD_SubNorm) (hO : PieceD_SubOut)
    (hR4 : PieceD_SubR4) : Lemma113_ii_pieceD_Claims := by
  intro G _ _ m B M E A a e K Q h hC
  refine ⟨fun R hR hQR g hg => ?_, fun R hR hQR => hR4 h hC R hR hQR, ?_⟩
  ·
    obtain ⟨-, z, hzR, hz⟩ := hE h hC R hR hQR g hg
    refine ⟨z, hzR, ?_⟩
    have hw : (g * z)⁻¹ * e * (g * z)⁻¹⁻¹ ∈ Subgroup.zpowers e := by
      have e1 : (g * z)⁻¹ * e * (g * z)⁻¹⁻¹ = z⁻¹ * (g⁻¹ * e * g) * z := by group
      rw [e1]
      exact hz
    have hinv : (g * z)⁻¹ ∈ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
      apply mem_normalizer_of_conj_le
      intro k hk
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hk
      rw [← conj_zpow]
      exact (Subgroup.zpowers e).zpow_mem hw m
    have h2 := (Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G)).inv_mem hinv
    simpa using h2
  ·
    intro x hx _hxE n hn hnQ
    obtain ⟨hC1, hN1, hInn⟩ := hN h hC
    have hxQ : x ∈ Q := h.hQ.2 (le_sup_right (a := E) hx)
    have hxN : x ∈ Subgroup.normalizer (K : Set G) := hC1 (h.hQ.1.1 hxQ)
    have hnN : n ∈ Subgroup.normalizer (K : Set G) := hN1 hn
    have hcQ : x⁻¹ * n⁻¹ * x * n ∈ Q := by
      have e1 : x⁻¹ * n⁻¹ * x * n = x⁻¹ * (n⁻¹ * x * n) := by group
      rw [e1]
      exact Q.mul_mem (Q.inv_mem hxQ) hnQ
    have hcE : x⁻¹ * n⁻¹ * x * n ∈ E := hInn _ hcQ (hO h hC x hxN n hnN)
    have e2 : x⁻¹ * (n⁻¹ * x * n) = x⁻¹ * n⁻¹ * x * n := by group
    rw [e2]
    exact hcE

theorem lemma113_ii_pieceD_of_subclaims (hE : PieceD_SubEConj) (hN : PieceD_SubNorm)
    (hO : PieceD_SubOut) (hR4 : PieceD_SubR4) : Lemma113_ii_pieceDStatement :=
  lemma113_ii_pieceD_of input32_7_holds (pieceD_claims_of_inputs hE hN hO hR4)

end PieceD

end Lemma113g

end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
