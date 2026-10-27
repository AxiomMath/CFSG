module

public import CFSG.CGT.Timmesfeld75.MultPrime
public import CFSG.CGT.Timmesfeld75.Sec5Ten
public import CFSG.ClassicalInvolution.SmallCases.Hat2A7Cover
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover

public section

namespace CFSG.CGT.Timmesfeld75

open Equiv Equiv.Perm
open CFSG.ClassicalInvolution.Hat2A7 (not_isPerfect_of_split_over_sylow card_closure_pair_le_eight)
open CFSG.ClassicalInvolution.QuaternionStructure (natCard_comap_eq)

section Generic

variable {E G : Type*} [Group E] [Finite E] [Group G] [Finite G]

omit [Finite E] [Finite G] in
theorem mul_self_eq_of_map_eq_of_ker {π : E →* G} {z : E}
    (hker : ∀ w : E, π w = 1 ↔ w = 1 ∨ w = z) (hcen : ∀ x : E, x * z = z * x) (hz2 : z * z = 1)
    {u v : E} (huv : π u = π v) : u * u = v * v := by
  have h0 : π (v⁻¹ * u) = 1 := by rw [map_mul, map_inv, huv, inv_mul_cancel]
  rcases (hker _).1 h0 with h1 | h1
  · rw [(inv_mul_eq_one.1 h1).symm]
  · have hu : u = v * z := by rw [← h1]; group
    rw [hu]
    calc v * z * (v * z) = v * (z * v) * z := by group
      _ = v * (v * z) * z := by rw [hcen v]
      _ = v * v * (z * z) := by group
      _ = v * v := by rw [hz2, mul_one]

theorem card_closure_pair_eq_eight {s t : G} (hs : s * s = 1) (ht : t * t = 1)
    (hst : (s * t) ^ 4 = 1) (hne : (s * t) ^ 2 ≠ 1) :
    Nat.card (Subgroup.closure ({s, t} : Set G)) = 8 := by
  have hle := card_closure_pair_le_eight hs ht hst
  have hsC : s ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
  have htC : t ∈ Subgroup.closure ({s, t} : Set G) := Subgroup.subset_closure (by simp)
  have hord : orderOf (s * t) = 4 := by
    have h := orderOf_eq_prime_pow (p := 2) (n := 1) (x := s * t) (by simpa using hne)
      (by simpa using hst)
    simpa using h
  have hNle : Subgroup.zpowers (s * t) ≤ Subgroup.closure ({s, t} : Set G) :=
    Subgroup.zpowers_le.2 ((Subgroup.closure ({s, t} : Set G)).mul_mem hsC htC)
  have hNcard : Nat.card (Subgroup.zpowers (s * t)) = 4 := by rw [Nat.card_zpowers, hord]
  have hdvd : 4 ∣ Nat.card (Subgroup.closure ({s, t} : Set G)) :=
    hNcard ▸ Subgroup.card_dvd_of_le hNle
  have hsN : s ∉ Subgroup.zpowers (s * t) := by
    intro h
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h
    have hc : Commute (s * t) s := by
      have h0 : Commute (s * t) ((s * t) ^ k) := (Commute.refl (s * t)).zpow_right k
      rwa [hk] at h0
    have h1 : s * t * s = t := by
      calc s * t * s = s * (s * t) := hc.eq
        _ = t := by rw [← mul_assoc, hs, one_mul]
    have h2 : s * t = t * s := by
      calc s * t = s * t * (s * s) := by rw [hs, mul_one]
        _ = (s * t * s) * s := by group
        _ = t * s := by rw [h1]
    apply hne
    calc (s * t) ^ 2 = s * t * (s * t) := pow_two _
      _ = s * (t * s) * t := by group
      _ = s * (s * t) * t := by rw [← h2]
      _ = (s * s) * (t * t) := by group
      _ = 1 := by rw [hs, ht, one_mul]
  have hlt : 4 < Nat.card (Subgroup.closure ({s, t} : Set G)) := by
    have h0 : 0 < Nat.card (Subgroup.closure ({s, t} : Set G)) := Nat.card_pos
    rcases Nat.lt_or_ge 4 (Nat.card (Subgroup.closure ({s, t} : Set G))) with h | h
    · exact h
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge hNle (by omega)
      exact hsN (heq ▸ hsC)
  obtain ⟨c, hc⟩ := hdvd
  omega

theorem involution_mem_ker_of_double_cover {π : E →* G} (hπ : Function.Surjective π) {z : E}
    (hzne : z ≠ 1) (hz2 : z * z = 1) (hcen : ∀ x : E, x * z = z * x)
    (hker : ∀ w : E, π w = 1 ↔ w = 1 ∨ w = z) (hperf : Group.IsPerfect E) {s t : G}
    (hs : s * s = 1) (ht : t * t = 1) (hst : (s * t) ^ 4 = 1) (hne : (s * t) ^ 2 ≠ 1)
    (hodd : Odd (Subgroup.closure ({s, t} : Set G)).index)
    (hconj : ∀ y : G, y ≠ 1 → y * y = 1 → ∃ g : G, g * t * g⁻¹ = y) :
    ∀ w : E, w * w = 1 → w = 1 ∨ w = z := by
  intro w hw2
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hw1, hwz⟩ := hcon
  have hs1 : s ≠ 1 := by
    rintro rfl
    apply hne
    rw [one_mul, pow_two]
    exact ht
  have ht1 : t ≠ 1 := by
    rintro rfl
    apply hne
    rw [mul_one, pow_two]
    exact hs
  have hsq : ∀ {u v : E}, π u = π v → u * u = v * v := fun huv =>
    mul_self_eq_of_map_eq_of_ker hker hcen hz2 huv
  have hlift : ∀ y : G, y ≠ 1 → y * y = 1 → ∃ u : E, u * u = 1 ∧ π u = y := by
    have hπw : π w ≠ 1 := fun h1 => by
      rcases (hker w).1 h1 with h2 | h2
      exacts [hw1 h2, hwz h2]
    have hπw2 : π w * π w = 1 := by rw [← map_mul, hw2, map_one]
    obtain ⟨g₀, hg₀⟩ := hconj (π w) hπw hπw2
    obtain ⟨x₀, hx₀⟩ := hπ g₀
    have hu₀ : (x₀⁻¹ * w * x₀) * (x₀⁻¹ * w * x₀) = 1 := by
      calc (x₀⁻¹ * w * x₀) * (x₀⁻¹ * w * x₀) = x₀⁻¹ * (w * w) * x₀ := by group
        _ = 1 := by rw [hw2]; group
    have hu₀π : π (x₀⁻¹ * w * x₀) = t := by
      rw [map_mul, map_mul, map_inv, hx₀, ← hg₀]
      group
    intro y hy hy2
    obtain ⟨g, hg⟩ := hconj y hy hy2
    obtain ⟨x, hx⟩ := hπ g
    refine ⟨x * (x₀⁻¹ * w * x₀) * x⁻¹, ?_, ?_⟩
    · calc x * (x₀⁻¹ * w * x₀) * x⁻¹ * (x * (x₀⁻¹ * w * x₀) * x⁻¹)
          = x * ((x₀⁻¹ * w * x₀) * (x₀⁻¹ * w * x₀)) * x⁻¹ := by group
        _ = 1 := by rw [hu₀]; group
    · rw [map_mul, map_mul, map_inv, hu₀π, hx, ← hg]
  have hc2 : ((s * t) ^ 2) * ((s * t) ^ 2) = 1 := by rw [← pow_add]; exact hst
  obtain ⟨s', hs'2, hs'⟩ := hlift s hs1 hs
  obtain ⟨t', ht'2, ht'⟩ := hlift t ht1 ht
  obtain ⟨c', hc'2, hc'⟩ := hlift ((s * t) ^ 2) hne hc2
  have hst' : π ((s' * t') ^ 2) = π c' := by rw [map_pow, map_mul, hs', ht', hc']
  have hsq' : (s' * t') ^ 2 * (s' * t') ^ 2 = 1 := by rw [hsq hst', hc'2]
  have h4' : (s' * t') ^ 4 = 1 := by rw [show 4 = 2 + 2 from rfl, pow_add]; exact hsq'
  set C : Subgroup E := Subgroup.closure ({s', t'} : Set E) with hC
  have hC8 : Nat.card C ≤ 8 := card_closure_pair_le_eight hs'2 ht'2 h4'
  set D : Subgroup G := Subgroup.closure ({s, t} : Set G) with hD
  have hD8 : Nat.card D = 8 := card_closure_pair_eq_eight hs ht hst hne
  have hmap : C.map π = D := by
    rw [hC, MonoidHom.map_closure, Set.image_pair, hs', ht']
  have hker' := Subgroup.card_ker_mul_card_range (π.comp C.subtype)
  have hrange : (π.comp C.subtype).range = D := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hmap]
  rw [hrange, hD8] at hker'
  have hCpos : 0 < Nat.card C := Nat.card_pos
  have hkerpos : 0 < Nat.card (π.comp C.subtype).ker := Nat.card_pos
  have hker1 : Nat.card (π.comp C.subtype).ker = 1 := by omega
  have hC8' : Nat.card C = 8 := by omega
  have hker0 : (π.comp C.subtype).ker = ⊥ := Subgroup.eq_bot_of_card_eq _ hker1
  have hzC : z ∉ C := by
    intro hzC
    have hmem : (⟨z, hzC⟩ : C) ∈ (π.comp C.subtype).ker := by
      rw [MonoidHom.mem_ker]
      exact (hker z).2 (Or.inr rfl)
    rw [hker0, Subgroup.mem_bot] at hmem
    exact hzne (congrArg Subtype.val hmem)
  set P : Subgroup E := D.comap π with hP
  have hkerc : Nat.card π.ker = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨1, ⟨z, (hker z).2 (Or.inr rfl)⟩, fun h1 => hzne (congrArg Subtype.val h1).symm, ?_⟩
    ext ⟨u, hu⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    rcases (hker u).1 hu with rfl | rfl
    · left; rfl
    · right; rfl
  have hPcard : Nat.card P = 2 * 8 := by rw [hP, natCard_comap_eq π hπ D, hkerc, hD8]
  have hCP : C ≤ P := Subgroup.map_le_iff_le_comap.mp hmap.le
  have hzP : z ∈ P := by
    show π z ∈ D
    rw [(hker z).2 (Or.inr rfl)]
    exact D.one_mem
  have hPodd : Odd P.index := by
    rw [hP, Subgroup.index_comap_of_surjective D hπ]
    exact hodd
  exact not_isPerfect_of_split_over_sylow hcen hz2 hPodd hzP hCP (by omega) hzC hperf

end Generic

section Six

abbrev A6 : Type := alternatingGroup (Fin 6)

@[expose] def sSix : A6 :=
  ⟨swap 1 3 * swap 4 5, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

@[expose] def tSix : A6 :=
  ⟨swap 0 1 * swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩

theorem dihedral_rel_six :
    sSix * sSix = 1 ∧ tSix * tSix = 1 ∧ (sSix * tSix) ^ 4 = 1 ∧ (sSix * tSix) ^ 2 ≠ 1 := by
  decide

theorem a6_involution_conj :
    ∀ y : A6, y ≠ 1 → y * y = 1 → ∃ g : A6, g * tSix * g⁻¹ = y := by
  decide +kernel

theorem card_A6 : Nat.card A6 = 360 := by
  rw [nat_card_alternatingGroup]
  norm_num [Nat.card_eq_fintype_card, Nat.factorial]

theorem odd_index_closure_six : Odd (Subgroup.closure ({sSix, tSix} : Set A6)).index := by
  obtain ⟨h1, h2, h3, h4⟩ := dihedral_rel_six
  have h := Subgroup.card_mul_index (Subgroup.closure ({sSix, tSix} : Set A6))
  rw [card_closure_pair_eq_eight h1 h2 h3 h4, card_A6] at h
  have : (Subgroup.closure ({sSix, tSix} : Set A6)).index = 45 := by omega
  rw [this]
  decide

theorem involution_mem_ker_of_double_cover_six {E : Type*} [Group E] [Finite E] {π : E →* A6}
    (hπ : Function.Surjective π) {z : E} (hzne : z ≠ 1) (hz2 : z * z = 1)
    (hcen : ∀ x : E, x * z = z * x) (hker : ∀ w : E, π w = 1 ↔ w = 1 ∨ w = z)
    (hperf : Group.IsPerfect E) : ∀ w : E, w * w = 1 → w = 1 ∨ w = z := by
  obtain ⟨h1, h2, h3, h4⟩ := dihedral_rel_six
  exact involution_mem_ker_of_double_cover hπ hzne hz2 hcen hker hperf h1 h2 h3 h4
    odd_index_closure_six a6_involution_conj

end Six

section Seven

open CFSG.ClassicalInvolution.Hat2A7 (A7 sD tD D8 card_D8 card_A7 dihedral_rel)

theorem odd_index_closure_seven : Odd (Subgroup.closure ({sD, tD} : Set A7)).index := by
  have h := Subgroup.card_mul_index D8
  rw [card_D8, card_A7] at h
  have : D8.index = 315 := by omega
  change Odd D8.index
  rw [this]
  decide

theorem involution_mem_ker_of_double_cover_seven {E : Type*}
    [Group E] [Finite E] {π : E →* A7} (hπ : Function.Surjective π) {z : E} (hzne : z ≠ 1)
    (hz2 : z * z = 1) (hcen : ∀ x : E, x * z = z * x) (hker : ∀ w : E, π w = 1 ↔ w = 1 ∨ w = z)
    (hperf : Group.IsPerfect E) : ∀ w : E, w * w = 1 → w = 1 ∨ w = z := by
  obtain ⟨h1, h2, h3, h4⟩ := dihedral_rel
  exact involution_mem_ker_of_double_cover hπ hzne hz2 hcen hker hperf h1 h2 h3 h4
    odd_index_closure_seven CFSG.ClassicalInvolution.Hat2A7.a7_involution_conj

end Seven

theorem involution_mem_ker_of_double_cover_alt {k : ℕ}
    (hk : k = 6 ∨ k = 7) {E : Type*} [Group E] [Finite E] {π : E →* alternatingGroup (Fin k)}
    (hπ : Function.Surjective π) {z : E} (hzne : z ≠ 1) (hz2 : z * z = 1)
    (hcen : ∀ x : E, x * z = z * x) (hker : ∀ w : E, π w = 1 ↔ w = 1 ∨ w = z)
    (hperf : Group.IsPerfect E) : ∀ w : E, w * w = 1 → w = 1 ∨ w = z := by
  rcases hk with rfl | rfl
  · exact involution_mem_ker_of_double_cover_six hπ hzne hz2 hcen hker hperf
  · exact involution_mem_ker_of_double_cover_seven hπ hzne hz2 hcen hker hperf

theorem altCoverInput : AltCoverInput := by
  intro k hk Y _ _ hperf Z hZn hZc ⟨e⟩ ⟨y, hyZ, hy2⟩
  have hperf' : Group.IsPerfect Y := Group.isPerfect_def.2 hperf
  have hn5 : 5 ≤ k := by rcases hk with rfl | rfl <;> norm_num
  have hn8 : k ≤ 8 := by rcases hk with rfl | rfl <;> norm_num
  have hodd : Odd (Nat.card Z) := by
    by_contra hnodd
    have h2 : 2 ∣ Nat.card Z := even_iff_two_dvd.1 (Nat.not_odd_iff_even.1 hnodd)
    obtain ⟨Q, hQZ, hpQ, hQpow⟩ := exists_central_pPrime_subgroup Z hZc 2 Nat.prime_two
    have hQn : Q.Normal := Subgroup.normal_of_le_center (hQZ.trans hZc)
    have hQ1 : Group.IsPerfect (Y ⧸ Q) := inferInstance
    let π : Y ⧸ Q →* alternatingGroup (Fin k) :=
      (e : Y ⧸ Z →* alternatingGroup (Fin k)).comp
        (QuotientGroup.map Q Z (MonoidHom.id Y) (fun x hx => hQZ hx))
    have hπmk : ∀ x : Y, π (x : Y ⧸ Q) = e (x : Y ⧸ Z) := fun _ => rfl
    have hπ : Function.Surjective π := by
      intro w
      obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (e.symm w)
      exact ⟨(x : Y ⧸ Q), by rw [hπmk, hx, MulEquiv.apply_symm_apply]⟩
    have hker : ∀ x : Y, π (x : Y ⧸ Q) = 1 ↔ x ∈ Z := by
      intro x
      rw [hπmk, ← map_one e, e.injective.eq_iff]
      exact QuotientGroup.eq_one_iff x
    have hkerc : π.ker ≤ Subgroup.center (Y ⧸ Q) := by
      intro g hg
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      have hx : x ∈ Z := (hker x).1 hg
      rw [Subgroup.mem_center_iff]
      intro h
      obtain ⟨x', rfl⟩ := QuotientGroup.mk_surjective h
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.1 (hZc hx) x']
    have hkerp : IsPGroup 2 π.ker := by
      rintro ⟨g, hg⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
      obtain ⟨j, hj⟩ := hQpow x ((hker x).1 hg)
      refine ⟨j, Subtype.ext ?_⟩
      change (x : Y ⧸ Q) ^ (2 ^ j) = 1
      rw [← QuotientGroup.mk_pow]
      exact (QuotientGroup.eq_one_iff _).2 hj
    have hle2 : Nat.card π.ker ≤ 2 :=
      CFSG.LocalAnalysis.ComponentInitial.alternating_perfect_central_two_kernel_order_at_most_two
        hn5 π hπ hkerc hkerp
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Z) 2 h2
    have hzord : orderOf (z : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hz
    have hz2 : (z : Y) * (z : Y) = 1 := by
      rw [← pow_two, ← hzord]
      exact pow_orderOf_eq_one _
    have hzQ : (z : Y) ∉ Q := fun h => hpQ (hzord ▸ Subgroup.orderOf_dvd_natCard Q h)
    have hzb1 : ((z : Y) : Y ⧸ Q) ≠ 1 := fun h => hzQ ((QuotientGroup.eq_one_iff _).1 h)
    have hzb2 : ((z : Y) : Y ⧸ Q) * ((z : Y) : Y ⧸ Q) = 1 := by
      rw [← QuotientGroup.mk_mul, hz2]
      exact QuotientGroup.mk_one _
    have hzbker : π ((z : Y) : Y ⧸ Q) = 1 := (hker z).2 z.2
    have hzcen : ∀ x : Y ⧸ Q, x * ((z : Y) : Y ⧸ Q) = ((z : Y) : Y ⧸ Q) * x := fun x =>
      Subgroup.mem_center_iff.1 (hkerc hzbker) x
    have hcard2 : Nat.card π.ker = 2 := by
      refine le_antisymm hle2 ?_
      have : Nontrivial π.ker :=
        ⟨⟨1, ⟨((z : Y) : Y ⧸ Q), hzbker⟩, fun h => hzb1 (congrArg Subtype.val h).symm⟩⟩
      exact Finite.one_lt_card
    have hkeriff : ∀ w : Y ⧸ Q, π w = 1 ↔ w = 1 ∨ w = ((z : Y) : Y ⧸ Q) := by
      intro w
      constructor
      · intro hw
        by_contra hcon
        rw [not_or] at hcon
        obtain ⟨hw1, hwz⟩ := hcon
        rw [Nat.card_eq_two_iff' (1 : π.ker)] at hcard2
        obtain ⟨u, -, huniq⟩ := hcard2
        have h1 := huniq ⟨w, hw⟩ (fun h => hw1 (congrArg Subtype.val h))
        have h2 := huniq ⟨((z : Y) : Y ⧸ Q), hzbker⟩ (fun h => hzb1 (congrArg Subtype.val h))
        exact hwz (congrArg Subtype.val (h1.trans h2.symm))
      · rintro (rfl | rfl)
        · exact map_one π
        · exact hzbker
    have hyb2 : (y : Y ⧸ Q) * (y : Y ⧸ Q) = 1 := by
      rw [← QuotientGroup.mk_mul, hy2]
      exact QuotientGroup.mk_one _
    have hmem := involution_mem_ker_of_double_cover_alt hk hπ hzb1 hzb2 hzcen hkeriff hQ1
      (y : Y ⧸ Q) hyb2
    exact hyZ ((hker y).1 ((hkeriff _).2 hmem))
  let π' : Y →* alternatingGroup (Fin k) :=
    (e : Y ⧸ Z →* alternatingGroup (Fin k)).comp (QuotientGroup.mk' Z)
  have hπ' : Function.Surjective π' := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker' : π'.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (x : Y ⧸ Z) = 1 ↔ x ∈ Z
    rw [← map_one e, e.injective.eq_iff]
    exact QuotientGroup.eq_one_iff x
  have hbound := CFSG.SectionRank.alternating_small_odd_cover_bound hn5 hn8 π' hπ'
    (by rw [hker']; exact hZc) (by rw [hker']; exact hodd)
  have h13 := hbound.2 hk
  rw [hker'] at h13
  rcases h13 with h | h
  · rw [h]
    exact one_dvd _
  · rw [h]

end CFSG.CGT.Timmesfeld75
