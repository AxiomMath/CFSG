module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsOuter
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsUnitaryCentralizer
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwGen
import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34TwRLev
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsInner

public section

namespace CFSG.ComponentClassification.GrSLit.L34Tw

namespace Q8

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer CFSG.ComponentClassification.GrSLit.L34Facts

section Centre

variable {G : Type} [Group G]

theorem center_jhat_eq_bot {J : Subgroup G} (hZ : zStarIn J = oddIn J) : center (Jhat J) = ⊥ := by
  rw [eq_bot_iff]
  intro e he
  obtain ⟨j, rfl⟩ := jq_surjective J e
  have h1 : (j : G) ∈ zStarIn J := (mem_zStarIn_iff j.2).2 he
  rw [hZ] at h1
  exact mem_bot.mpr ((mem_oddIn_iff j.2).1 h1)

theorem injective_of_ker {J : Subgroup G} (hZ : zStarIn J = oddIn J)
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqker : q.ker = center (Jhat J)) :
    Function.Injective q :=
  (MonoidHom.ker_eq_bot_iff q).1 (by rw [hqker, center_jhat_eq_bot hZ])

theorem odd_card_ker_phiC [Finite G] {J : Subgroup G} {x : G} {q : Jhat J →* Equiv.Perm (Fin 42)}
    (hq : Function.Injective q) : Odd (Nat.card (phiC J x q).ker) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmem : ∀ u : (phiC J x q).ker,
      (Subgroup.inclusion (inf_le_left : J ⊓ centralizer ({x} : Set G) ≤ J)
        (u : ↥(J ⊓ centralizer ({x} : Set G))) : ↥J) ∈ pPrimeCore 2 ↥J := by
    intro u
    have h0 : phiC J x q (u : ↥(J ⊓ centralizer ({x} : Set G))) = 1 := MonoidHom.mem_ker.mp u.2
    have h1 : q (jq J (Subgroup.inclusion (inf_le_left : J ⊓ centralizer ({x} : Set G) ≤ J)
        (u : ↥(J ⊓ centralizer ({x} : Set G))))) = 1 := h0
    have h2 := hq (h1.trans (map_one q).symm)
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
  let f : (phiC J x q).ker →* pPrimeCore 2 ↥J :=
    ((Subgroup.inclusion (inf_le_left : J ⊓ centralizer ({x} : Set G) ≤ J)).comp
      (phiC J x q).ker.subtype).codRestrict (pPrimeCore 2 ↥J) hmem
  have hf : Function.Injective f := by
    intro u v h
    have h' := congrArg (fun w : pPrimeCore 2 ↥J => ((w : ↥J) : G)) h
    exact Subtype.ext (Subtype.ext h')
  have h := Subgroup.card_dvd_of_injective f hf
  exact Odd.of_dvd_nat (Nat.coprime_two_left.mp pPrimeCore_coprime_card) h

end Centre

section Elementary

theorem isElemTwo_map_conj {E : Subgroup (Equiv.Perm (Fin 42))} (hE : IsElemTwo E)
    (k : Equiv.Perm (Fin 42)) : IsElemTwo (E.map (MulAut.conj k).toMonoidHom) := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨t, ht, rfl⟩ _ ⟨t', ht', rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h := hE.1 t ht t' ht'
    calc k * t * k⁻¹ * (k * t' * k⁻¹) = k * (t * t') * k⁻¹ := by group
      _ = k * (t' * t) * k⁻¹ := by rw [h]
      _ = k * t' * k⁻¹ * (k * t * k⁻¹) := by group
  · rintro _ ⟨t, ht, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc k * t * k⁻¹ * (k * t * k⁻¹) = k * (t * t) * k⁻¹ := by group
      _ = 1 := by rw [hE.2 t ht]; group

private theorem factorization_20160 : (20160 : ℕ).factorization 2 = 6 := by
  have h : (20160 : ℕ) = 2 ^ 6 * 315 := by norm_num
  rw [h, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 2 ∣ 315)]
  simp

theorem card_C₁_subgroupOf :
    Nat.card (C₁.subgroupOf S) = 2 ^ (Nat.card S).factorization 2 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (show C₁ ≤ S from inf_le_right)).toEquiv,
    card_C₁, card_S, factorization_20160]
  norm_num

theorem r₁_mul_self : r₁ * r₁ = 1 := by
  have h := pow_orderOf_eq_one r₁R
  rw [orderOf_r₁R, pow_two] at h
  exact congrArg Subtype.val h

theorem r₁_ne_one : r₁ ≠ 1 := by
  intro h
  have h1 : r₁R = 1 := Subtype.ext h
  have h2 := orderOf_r₁R
  rw [h1, orderOf_one] at h2
  exact absurd h2 (by norm_num)

theorem exists_E16_centralizer
    {s : Equiv.Perm (Fin 42)} (hs : s ∈ S) (hs2 : s * s = 1) :
    ∃ E : Subgroup (Equiv.Perm (Fin 42)),
      E ≤ centralizer ({s} : Set (Equiv.Perm (Fin 42))) ⊓ S ∧ IsElemTwo E ∧ Nat.card E = 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E₀, hE₀T, hE₀e, hE₀c⟩ := exists_E16_T0
  by_cases hs1 : s = 1
  · subst hs1
    exact ⟨E₀, fun y hy => mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (by simp),
      T0_le_S (hE₀T hy)⟩, hE₀e, hE₀c⟩
  · obtain ⟨c, hcS, hcs⟩ :=
      inner_invol_conj hs r₁_mem_S hs2 r₁_mul_self hs1 r₁_ne_one
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq S sylowT0
      (Sylow.ofCard (C₁.subgroupOf S) card_C₁_subgroupOf)
    have hgC : ∀ t ∈ T0, (g : Equiv.Perm (Fin 42)) * t * (g : Equiv.Perm (Fin 42))⁻¹ ∈ C₁ := by
      intro t ht
      have hyS : (g : Equiv.Perm (Fin 42)) * t * (g : Equiv.Perm (Fin 42))⁻¹ ∈ S :=
        S.mul_mem (S.mul_mem g.2 (T0_le_S ht)) (S.inv_mem g.2)
      have hT : (g : Equiv.Perm (Fin 42))⁻¹ *
          ((g : Equiv.Perm (Fin 42)) * t * (g : Equiv.Perm (Fin 42))⁻¹) * g ∈ T0 := by
        rwa [show (g : Equiv.Perm (Fin 42))⁻¹ *
          ((g : Equiv.Perm (Fin 42)) * t * (g : Equiv.Perm (Fin 42))⁻¹) * g = t by group]
      have h1 := (mem_smul_sylowT0_iff g ⟨_, hyS⟩).2 hT
      rw [hg, Sylow.coe_ofCard] at h1
      exact mem_subgroupOf.mp h1
    refine ⟨E₀.map (MulAut.conj (c⁻¹ * (g : Equiv.Perm (Fin 42)))).toMonoidHom, ?_,
      isElemTwo_map_conj hE₀e _, ?_⟩
    · rintro _ ⟨t, ht, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      obtain ⟨hw1, -⟩ := mem_inf.mp (hgC t (hE₀T ht))
      have hw : (g : Equiv.Perm (Fin 42)) * t * (g : Equiv.Perm (Fin 42))⁻¹ * r₁ =
          r₁ * ((g : Equiv.Perm (Fin 42)) * t * (g : Equiv.Perm (Fin 42))⁻¹) :=
        mem_centralizer_singleton_iff.mp hw1
      rw [← hcs] at hw
      refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr ?_, ?_⟩
      · calc c⁻¹ * (g : Equiv.Perm (Fin 42)) * t * (c⁻¹ * (g : Equiv.Perm (Fin 42)))⁻¹ * s
            = c⁻¹ * ((g : Equiv.Perm (Fin 42)) * t * (g : Equiv.Perm (Fin 42))⁻¹ *
                (c * s * c⁻¹)) * c := by group
          _ = c⁻¹ * ((c * s * c⁻¹) * ((g : Equiv.Perm (Fin 42)) * t *
                (g : Equiv.Perm (Fin 42))⁻¹)) * c := by rw [hw]
          _ = s * (c⁻¹ * (g : Equiv.Perm (Fin 42)) * t *
                (c⁻¹ * (g : Equiv.Perm (Fin 42)))⁻¹) := by group
      · have hc : c⁻¹ ∈ S := S.inv_mem hcS
        exact S.mul_mem (S.mul_mem (S.mul_mem hc g.2) (T0_le_S (hE₀T ht)))
          (S.inv_mem (S.mul_mem hc g.2))
    · rw [Subgroup.card_map_of_injective (MulAut.conj _).injective, hE₀c]

end Elementary

section Lift

variable {G : Type} [Group G] [Finite G]

theorem not_mem_withKernel
    {J : Subgroup G} {a : G} (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hZ : zStarIn J = oddIn J)
    (haN : a ∈ normalizer (J : Set G)) (ha2 : a * a = 1)
    (hrank : ∀ E : Subgroup G, E ≤ J ⊓ centralizer ({a} : Set G) → IsElemTwo E →
      Nat.card E ≠ 16) : a ∉ withKernel J := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro haK
  obtain ⟨q, hqS, hqsurj, hqker, -⟩ := exists_jq hL
  have hqinj : Function.Injective q := injective_of_ker hZ hqker
  obtain ⟨e₀, he₀⟩ := exists_inner haK haN
  have he₀2 : e₀ * e₀ = 1 := by
    have hc : e₀ * e₀ ∈ center (Jhat J) := by
      rw [mem_center_iff]
      intro e
      have h := betaHat_betaHat J haN ha2 e
      rw [he₀ e, he₀ (e₀⁻¹ * e * e₀)] at h
      calc e * (e₀ * e₀) = e₀ * e₀ * (e₀⁻¹ * (e₀⁻¹ * e * e₀) * e₀) := by group
        _ = e₀ * e₀ * e := by rw [h]
    rwa [center_jhat_eq_bot hZ, mem_bot] at hc
  have hs2 : q e₀ * q e₀ = 1 := by rw [← map_mul, he₀2, map_one]
  obtain ⟨E₀, hE₀le, hE₀e, hE₀c⟩ := exists_E16_centralizer (hqS e₀) hs2
  have hrange : E₀ ≤ (phiC J a q).range := by
    intro y hy
    obtain ⟨hyc, hyS⟩ := mem_inf.mp (hE₀le hy)
    obtain ⟨e, rfl⟩ := hqsurj y hyS
    have hcomm : e * e₀ = e₀ * e := by
      apply hqinj
      rw [map_mul, map_mul]
      exact mem_centralizer_singleton_iff.mp hyc
    have hfix : betaHat J haN e = e := by
      rw [he₀ e]
      calc e₀⁻¹ * e * e₀ = e₀⁻¹ * (e * e₀) := by group
        _ = e₀⁻¹ * (e₀ * e) := by rw [hcomm]
        _ = e := by group
    obtain ⟨j, hj, hjx⟩ := exists_fixed_lift haN ha2 hfix
    have hjc : (j : G) ∈ centralizer ({a} : Set G) := by
      apply mem_centralizer_of_conj_eq
      have := congrArg Subtype.val hjx
      rwa [coe_conjJ] at this
    exact ⟨⟨j, j.2, hjc⟩, by show q (jq J j) = q e; rw [hj]⟩
  have hE₀p : IsPGroup 2 E₀ := IsPGroup.of_card (n := 4) (by rw [hE₀c]; norm_num)
  obtain ⟨E', -, hE'map, hE'card⟩ :=
    exists_lift_two_subgroup (phiC J a q) (odd_card_ker_phiC hqinj) hE₀p hrange
  have hbij : Function.Bijective ((phiC J a q).subgroupMap E') :=
    (MonoidHom.subgroupMap_surjective _ _).bijective_of_nat_card_le (by
      rw [hE'map]; exact hE'card.le)
  have hinj : ∀ u ∈ E', ∀ v ∈ E', phiC J a q u = phiC J a q v → u = v := by
    intro u hu v hv h
    have := hbij.1 (a₁ := ⟨u, hu⟩) (a₂ := ⟨v, hv⟩) (Subtype.ext h)
    exact congrArg Subtype.val this
  have hmemE₀ : ∀ u ∈ E', phiC J a q u ∈ E₀ := fun u hu => by
    rw [← hE'map]; exact mem_map_of_mem _ hu
  refine hrank (E'.map (J ⊓ centralizer ({a} : Set G)).subtype) (map_subtype_le _) ⟨?_, ?_⟩ ?_
  · rintro _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩
    have h1 : phiC J a q (u * v) = phiC J a q (v * u) := by
      rw [map_mul, map_mul]; exact hE₀e.1 _ (hmemE₀ u hu) _ (hmemE₀ v hv)
    exact congrArg Subtype.val (hinj (u * v) (E'.mul_mem hu hv) (v * u) (E'.mul_mem hv hu) h1)
  · rintro _ ⟨u, hu, rfl⟩
    have h1 : phiC J a q (u * u) = phiC J a q 1 := by
      rw [map_mul, map_one]; exact hE₀e.2 _ (hmemE₀ u hu)
    exact congrArg Subtype.val (hinj (u * u) (E'.mul_mem hu hu) 1 E'.one_mem h1)
  · rw [Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE'card, hE₀c]

end Lift

section Unitary

variable {G : Type} [Group G] [Finite G]

theorem card_conjSet_of_realization {J : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    {q : Jhat J →* Equiv.Perm (Fin 42)} (hqsurj : ∀ s ∈ S, ∃ e, q e = s)
    (hqS : ∀ e, q e ∈ S) (hqker : q.ker = center (Jhat J)) {r : Equiv.Perm (Fin 42)}
    (hr : ∀ e, q (betaHat J hxN e) = r * q e * r⁻¹) :
    Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} =
      Nat.card ↥(centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S) *
        Nat.card (zStarIn J) := by
  set φ : ↥J →* Equiv.Perm (Fin 42) := q.comp (jq J) with hφ
  set C := centralizer ({r} : Set (Equiv.Perm (Fin 42))) ⊓ S with hC
  have hCφ : C ≤ φ.range := by
    intro s hs
    obtain ⟨e, he⟩ := hqsurj s hs.2
    obtain ⟨j, rfl⟩ := jq_surjective J e
    exact ⟨j, he⟩
  have h1 := card_comap_eq φ C hCφ
  have hker : Nat.card φ.ker = Nat.card (zStarIn J) := by
    have hk : φ.ker = Open.fusionZStar J := by
      ext j
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hqker,
        ← mem_zStarIn_iff j.2, zStarIn, mem_map]
      constructor
      · rintro ⟨j', hj', hjj⟩
        rwa [Subtype.ext hjj] at hj'
      · intro hj
        exact ⟨j, hj, rfl⟩
    rw [hk, zStarIn, Subgroup.card_map_of_injective Subtype.val_injective]
  have hset : Nat.card {j : J // (j : G)⁻¹ * x⁻¹ * j * x ∈ zStarIn J} =
      Nat.card (C.comap φ) := by
    apply Nat.card_congr
    refine Equiv.subtypeEquivRight fun j => ?_
    have hmem : (j : G)⁻¹ * x⁻¹ * j * x ∈ J := by
      have := conj_mem_of_mem_normalizer hxN j.2
      have e1 : (j : G)⁻¹ * x⁻¹ * j * x = (j : G)⁻¹ * (x⁻¹ * j * x) := by group
      rw [e1]
      exact J.mul_mem (J.inv_mem j.2) this
    rw [mem_zStarIn_iff hmem]
    have e1 : (⟨(j : G)⁻¹ * x⁻¹ * j * x, hmem⟩ : J) = j⁻¹ * conjJ J hxN j := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_conjJ]
      group
    rw [e1, ← hqker, MonoidHom.mem_ker, map_mul, map_mul, map_inv, map_inv, ← betaHat_jq, hr,
      mem_comap, hC, mem_inf, mem_centralizer_singleton_iff, inv_mul_conj_eq_one_iff]
    simp only [hφ, MonoidHom.comp_apply]
    exact ⟨fun h => ⟨h, hqS _⟩, fun h => h.1⟩
  rw [hset, h1, hker]

theorem false_of_even_perfect {J : Subgroup G} {x : G} (hxN : x ∈ normalizer (J : Set G))
    (hx2 : x * x = 1) {q : Jhat J →* Equiv.Perm (Fin 42)} (hqS : ∀ e, q e ∈ S)
    (hqsurj : ∀ s ∈ S, ∃ e, q e = s) (hqker : q.ker = center (Jhat J))
    {ρ : Equiv.Perm (Fin 42)} (hβ : ∀ e, q (betaHat J hxN e) = ρ * q e * ρ⁻¹)
    (hperfC : ⁅centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S,
      centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S⁆ =
        centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S)
    (heven : Even (Nat.card ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S)))
    (hperf : ∀ (H : Subgroup G) (Q : Type) [Group Q] (π : ↥H →* Q),
      H ≤ J ⊓ centralizer ({x} : Set G) → Function.Surjective π → Group.IsPerfect Q →
        Odd (Nat.card Q)) : False := by
  have hle := range_le_of_realization hxN hqS hβ
  have hge := le_range_of_perfect hxN hx2 hqsurj hqker hβ hperfC
  have hmem : ∀ u, phiC J x q u ∈ centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S :=
    fun u => hle ⟨u, rfl⟩
  let π : ↥(J ⊓ centralizer ({x} : Set G)) →*
      ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S) := (phiC J x q).codRestrict _ hmem
  have hsurj : Function.Surjective π := by
    rintro ⟨c, hc⟩
    obtain ⟨u, hu⟩ := hge hc
    exact ⟨u, Subtype.ext hu⟩
  have hP : Group.IsPerfect ↥(centralizer ({ρ} : Set (Equiv.Perm (Fin 42))) ⊓ S) :=
    Subgroup.isPerfect_iff.2 hperfC
  exact (Nat.not_even_iff_odd.mpr (hperf _ _ π le_rfl hsurj hP)) heven

theorem isL34Unitary_of_perf {J : Subgroup G} {a : G}
    (hJ : ⁅J, J⁆ = J) (hL : IsL34Type (J ⧸ Open.fusionZStar J))
    (haN : a ∈ normalizer (J : Set G)) (ha2 : a * a = 1) (haK : a ∉ withKernel J)
    (hperf : ∀ (H : Subgroup G) (Q : Type) [Group Q] (π : ↥H →* Q),
      H ≤ J ⊓ centralizer ({a} : Set G) → Function.Surjective π → Group.IsPerfect Q →
        Odd (Nat.card Q)) : IsL34Unitary J a := by
  obtain ⟨q, hqS, hqsurj, hqker, -, ρ, hρ, hβ⟩ := exists_outer_realization hJ hL haN ha2 haK
  rcases hρ with rfl | rfl | rfl
  · exfalso
    have : IsSimpleGroup C₂ := isSimpleGroup_C₂
    have hperfC : ⁅C₂, C₂⁆ = C₂ := commutator_eq_of_simple exists_mul_ne_C₂
    exact false_of_even_perfect haN ha2 hqS hqsurj hqker hβ hperfC
      (by rw [show Nat.card ↥(centralizer ({r₂} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 168 from
        card_C₂]; decide) hperf
  · exfalso
    have : IsSimpleGroup C₃ := isSimpleGroup_C₃
    have hperfC : ⁅C₃, C₃⁆ = C₃ := commutator_eq_of_simple exists_mul_ne_C₃
    exact false_of_even_perfect haN ha2 hqS hqsurj hqker hβ hperfC
      (by rw [show Nat.card ↥(centralizer ({r₃} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 60 from
        card_C₃]; decide) hperf
  · refine ⟨haN, ha2, haK, ?_⟩
    rw [card_conjSet_of_realization haN hqsurj hqS hqker hβ]
    have h72 : Nat.card ↥(centralizer ({r₄} : Set (Equiv.Perm (Fin 42))) ⊓ S) = 72 := card_C₄
    rw [h72]

end Unitary

section Quaternion

variable {G : Type} [Group G] [Finite G]

theorem exists_a_invariant_sylow {J : Subgroup G} {a : G} (haN : a ∈ normalizer (J : Set G))
    (ha2 : a * a = 1) : ∃ P : Subgroup G, IsSylowTwoIn P J ∧ a ∈ normalizer (P : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N : Subgroup G := J ⊔ zpowers a
  have hNn : N ≤ normalizer (J : Set G) := sup_le le_normalizer (zpowers_le.mpr haN)
  have haN' : a ∈ N := mem_sup_right (mem_zpowers a)
  have ha'2 : (⟨a, haN'⟩ : ↥N) * ⟨a, haN'⟩ = 1 := Subtype.ext ha2
  have hp : IsPGroup 2 (zpowers (⟨a, haN'⟩ : ↥N)) := by
    rintro ⟨h, n, rfl⟩
    refine ⟨1, Subtype.ext ?_⟩
    simp only [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_two, ha'2, one_zpow]
  obtain ⟨U, hU⟩ := hp.exists_le_sylow
  have hS₀N : (U : Subgroup ↥N).map N.subtype ≤ N := map_subtype_le _
  have hUS : ∃ T : Sylow 2 ↥N,
      (T : Subgroup ↥N) = ((U : Subgroup ↥N).map N.subtype).subgroupOf N :=
    ⟨U, (comap_map_eq_self_of_injective N.subtype_injective _).symm⟩
  obtain ⟨T, hT⟩ := UnbalancedGS.RankProjectiveAction.exists_sylow_inf_of_le_normalizer hS₀N hUS
    le_sup_left hNn
  refine ⟨((U : Subgroup ↥N).map N.subtype) ⊓ J, ⟨inf_le_right, T, hT⟩, ?_⟩
  have haS₀ : a ∈ (U : Subgroup ↥N).map N.subtype := ⟨⟨a, haN'⟩, hU (mem_zpowers _), rfl⟩
  exact inf_normalizer_le_normalizer_inf ⟨le_normalizer haS₀, haN⟩

theorem exists_q8_of_unitary
    {J : Subgroup G} {a : G} (hJ : ⁅J, J⁆ = J)
    (hL : IsL34Type (J ⧸ Open.fusionZStar J)) (hZ : zStarIn J = oddIn J)
    (haN : a ∈ normalizer (J : Set G)) (ha2 : a * a = 1) (hU : IsL34Unitary J a) :
    ∃ z ∈ J, ∃ q ∈ J, ∃ y ∈ J ⊓ centralizer ({a} : Set G),
      z * z = 1 ∧ z ≠ 1 ∧ y * y = z ∧ z * a = a * z ∧ q⁻¹ * a * q = a * z := by
  obtain ⟨P, hP, haP⟩ := exists_a_invariant_sylow haN ha2
  have hPZ : P ⊓ zStarIn J = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzP, hzZ⟩ := mem_inf.mp hz
    have hzJ : z ∈ J := hP.1 hzP
    rw [hZ] at hzZ
    exact mem_bot.mpr (eq_one_of_jq_eq_one hP.1 (GrS4.isPGroup_of_isSylowTwoIn hP) hzP
      ((mem_oddIn_iff hzJ).1 hzZ))
  obtain ⟨-, -, -, hQ8, -, -, -, hinv⟩ := l34UnitaryCentralizerFact G J P a hJ hL hU hP haP
  obtain ⟨φ⟩ := hQ8 hPZ
  have e22 : (QuaternionGroup.a 2 : QuaternionGroup 2) * QuaternionGroup.a 2 = 1 := by
    rw [QuaternionGroup.a_mul_a, QuaternionGroup.one_def]
    congr 1
  have e11 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by
    rw [QuaternionGroup.a_mul_a]
    congr 1
  have hne : (QuaternionGroup.a 2 : QuaternionGroup 2) ≠ 1 := by
    rw [QuaternionGroup.one_def]
    intro h
    exact absurd (QuaternionGroup.a.inj h) (by decide)
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : ↥(P ⊓ centralizer ({a} : Set G)),
      z₀ = φ.symm (QuaternionGroup.a 2) := ⟨_, rfl⟩
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ↥(P ⊓ centralizer ({a} : Set G)),
      y₀ = φ.symm (QuaternionGroup.a 1) := ⟨_, rfl⟩
  have hz₀2 : z₀ * z₀ = 1 := by rw [hz₀, ← map_mul, e22, map_one]
  have hz₀1 : z₀ ≠ 1 := by
    intro h
    apply hne
    have h' := congrArg φ h
    rwa [hz₀, MulEquiv.apply_symm_apply, map_one] at h'
  have hy₀z₀ : y₀ * y₀ = z₀ := by rw [hy₀, hz₀, ← map_mul, e11]
  have hza : (z₀ : G) * a = a * z₀ := mem_centralizer_singleton_iff.mp z₀.2.2
  have hz2 : (z₀ : G) * z₀ = 1 := congrArg Subtype.val hz₀2
  have hza2 : (z₀ : G) * a * ((z₀ : G) * a) = 1 := by
    calc (z₀ : G) * a * ((z₀ : G) * a) = (z₀ : G) * (a * z₀) * a := by group
      _ = (z₀ : G) * ((z₀ : G) * a) * a := by rw [← hza]
      _ = ((z₀ : G) * z₀) * (a * a) := by group
      _ = 1 := by rw [hz2, ha2, one_mul]
  obtain ⟨q, hqP, hq⟩ := hinv z₀ z₀.2.1 hza2
  exact ⟨z₀, hP.1 z₀.2.1, q, hP.1 hqP, y₀, ⟨hP.1 y₀.2.1, y₀.2.2⟩, hz2,
    fun h => hz₀1 (Subtype.ext h), congrArg Subtype.val hy₀z₀, hza, hq.symm.trans hza⟩

end Quaternion

end Q8

open CFSG Subgroup CFSG.ComponentClassification.PSL3Four
  CFSG.ComponentClassification.UnbalancedLayer

variable {G : Type} [Group G] [Finite G]

theorem exists_q8_step
    {J' : Subgroup G} {a : G}
    (hJ : ⁅J', J'⁆ = J')
    (hL : IsL34Type (J' ⧸ Open.fusionZStar J')) (hZ : zStarIn J' = oddIn J')
    (haN : a ∈ normalizer (J' : Set G)) (ha2 : a * a = 1)
    (hrank : ∀ E : Subgroup G, E ≤ J' ⊓ centralizer ({a} : Set G) → IsElemTwo E →
      Nat.card E ≠ 16)
    (hperf : ∀ (H : Subgroup G) (Q : Type) [Group Q] (π : ↥H →* Q),
      H ≤ J' ⊓ centralizer ({a} : Set G) → Function.Surjective π → Group.IsPerfect Q →
        Odd (Nat.card Q)) :
    a ∉ J' ∧ ∃ z ∈ J', ∃ q ∈ J', ∃ y ∈ J' ⊓ centralizer ({a} : Set G),
      z * z = 1 ∧ z ≠ 1 ∧ y * y = z ∧ z * a = a * z ∧ q⁻¹ * a * q = a * z := by
  have haK : a ∉ withKernel J' := Q8.not_mem_withKernel hL hZ haN ha2 hrank
  have hU : IsL34Unitary J' a := Q8.isL34Unitary_of_perf hJ hL haN ha2 haK hperf
  exact ⟨fun h => haK (mem_sup_left h), Q8.exists_q8_of_unitary hJ hL hZ haN ha2 hU⟩

end CFSG.ComponentClassification.GrSLit.L34Tw
