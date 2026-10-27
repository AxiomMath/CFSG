module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Center
public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsTransvModel

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem exists_odd_pow [Finite G] (g : G) : ∃ b : ℕ, Odd (orderOf (g ^ (2 ^ b))) := by
  obtain ⟨b, m, hm, hbm⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  refine ⟨b, ?_⟩
  rw [orderOf_pow_of_dvd (by positivity) (hbm ▸ dvd_mul_right _ _), hbm,
    Nat.mul_div_cancel_left _ (by positivity)]
  exact hm

theorem exists_pow_mul_self_eq {f : G} (hf : Odd (orderOf f)) : ∃ n : ℕ, (f * f) ^ n = f := by
  obtain ⟨m, hm⟩ := hf
  refine ⟨m + 1, ?_⟩
  rw [← pow_two, ← pow_mul, show 2 * (m + 1) = orderOf f + 1 by omega, pow_succ,
    pow_orderOf_eq_one, one_mul]

theorem exists_complement_fixed [Finite G] {A : Subgroup G} (hA : IsElemTwo A) {f : G}
    (hfA : f ∈ normalizer (A : Set G)) (hf : Odd (orderOf f)) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ f ∈ normalizer (A₀ : Set G) ∧
      A₀ ⊓ centralizer ({f} : Set G) = ⊥ ∧
      Nat.card A₀ * Nat.card ↥(A ⊓ centralizer ({f} : Set G)) = Nat.card A := by
  have hc : ∀ a ∈ A, f * a * f⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.mp hfA a).mp ha
  have hc' : ∀ a ∈ A, f⁻¹ * a * f ∈ A := fun a ha => by
    refine (mem_normalizer_iff.mp hfA (f⁻¹ * a * f)).mpr ?_
    rwa [show f * (f⁻¹ * a * f) * f⁻¹ = a by group]
  have hθA : ∀ a ∈ A, a⁻¹ * (f * a * f⁻¹) ∈ A := fun a ha => A.mul_mem (A.inv_mem ha) (hc a ha)
  let θ : A →* A := MonoidHom.mk' (fun a => ⟨a⁻¹ * (f * a * f⁻¹), hθA a a.2⟩) fun a b => by
    apply Subtype.ext
    have hcomm := hA.1 _ (A.inv_mem b.2) _ (hθA a a.2)
    show ((a : G) * b)⁻¹ * (f * (a * b) * f⁻¹) =
      (a : G)⁻¹ * (f * a * f⁻¹) * ((b : G)⁻¹ * (f * b * f⁻¹))
    calc ((a : G) * b)⁻¹ * (f * (a * b) * f⁻¹) =
        (b : G)⁻¹ * ((a : G)⁻¹ * (f * a * f⁻¹)) * (f * b * f⁻¹) := by group
      _ = (a : G)⁻¹ * (f * a * f⁻¹) * (b : G)⁻¹ * (f * b * f⁻¹) := by rw [hcomm]
      _ = (a : G)⁻¹ * (f * a * f⁻¹) * ((b : G)⁻¹ * (f * b * f⁻¹)) := by group
  have hθ : ∀ a : A, ((θ a : A) : G) = (a : G)⁻¹ * (f * a * f⁻¹) := fun a => rfl
  have hker : ∀ a : A, a ∈ θ.ker ↔ (a : G) ∈ centralizer ({f} : Set G) := by
    intro a
    rw [MonoidHom.mem_ker, mem_centralizer_singleton_iff, ← Subtype.coe_inj, hθ,
      OneMemClass.coe_one, inv_mul_eq_one]
    constructor
    · intro h
      calc (a : G) * f = f * a * f⁻¹ * f := by rw [← h]
        _ = f * a := by group
    · intro h
      rw [← h]
      group
  set A₀ : Subgroup G := θ.range.map A.subtype with hA₀
  have hmemA₀ : ∀ g : G, g ∈ A₀ ↔ ∃ a ∈ A, a⁻¹ * (f * a * f⁻¹) = g := by
    intro g
    constructor
    · rintro ⟨x, ⟨a, rfl⟩, rfl⟩
      exact ⟨a, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨θ ⟨a, ha⟩, ⟨⟨a, ha⟩, rfl⟩, rfl⟩
  refine ⟨A₀, map_subtype_le _, ?_, ?_, ?_⟩
  · rw [mem_normalizer_iff]
    intro g
    rw [hmemA₀, hmemA₀]
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨f * a * f⁻¹, hc a ha, by group⟩
    · rintro ⟨a, ha, he⟩
      refine ⟨f⁻¹ * a * f, hc' a ha, ?_⟩
      calc (f⁻¹ * a * f)⁻¹ * (f * (f⁻¹ * a * f) * f⁻¹) = f⁻¹ * (a⁻¹ * (f * a * f⁻¹)) * f := by
            group
        _ = g := by rw [he]; group
  · rw [eq_bot_iff]
    rintro g ⟨hg, hgc⟩
    obtain ⟨a, ha, rfl⟩ := (hmemA₀ g).1 hg
    replace hgc := mem_centralizer_singleton_iff.mp hgc
    have hgA : a⁻¹ * (f * a * f⁻¹) ∈ A := hθA a ha
    set g := a⁻¹ * (f * a * f⁻¹) with hgd
    have h1 : f * a * f⁻¹ = a * g := by rw [hgd]; group
    have hfg : f * g * f⁻¹ = g := by
      calc f * g * f⁻¹ = g * f * f⁻¹ := by rw [hgc]
        _ = g := by group
    have h2 : (f * f) * a = a * (f * f) := by
      have h3 : (f * f) * a * (f * f)⁻¹ = a := by
        calc (f * f) * a * (f * f)⁻¹ = f * (f * a * f⁻¹) * f⁻¹ := by group
          _ = f * (a * g) * f⁻¹ := by rw [h1]
          _ = (f * a * f⁻¹) * (f * g * f⁻¹) := by group
          _ = a * g * g := by rw [h1, hfg]
          _ = a := by rw [mul_assoc, hA.2 g hgA, mul_one]
      calc (f * f) * a = (f * f) * a * (f * f)⁻¹ * (f * f) := by group
        _ = a * (f * f) := by rw [h3]
    obtain ⟨n, hn⟩ := exists_pow_mul_self_eq hf
    have h4 : f * a = a * f := by
      have := ((Commute.pow_left h2 n) : (f * f) ^ n * a = a * (f * f) ^ n)
      rwa [hn] at this
    show g ∈ (⊥ : Subgroup G)
    rw [mem_bot, hgd, h4]
    group
  · rw [hA₀, Subgroup.card_map_of_injective Subtype.val_injective]
    have h1 : Nat.card θ.ker = Nat.card ↥(A ⊓ centralizer ({f} : Set G)) := by
      refine Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.1.2, (hker a.1).1 a.2⟩
          invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hker ⟨g.1, g.2.1⟩).2 g.2.2⟩
          left_inv := fun a => rfl
          right_inv := fun g => rfl }
    rw [← h1, mul_comm, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem h0_pow_four_pow (b : ℕ) : h0 ^ (4 ^ b) = h0 := by
  have h3 : h0 ^ 3 = 1 := by rw [pow_three, ← mul_assoc]; exact h0_cube
  rw [pow_eq_pow_mod (4 ^ b) h3, Nat.pow_mod]
  norm_num

theorem eq_one_of_comm_h0_pow
    {U : Subgroup (Equiv.Perm (Fin 42))} (hU : U = U1 ∨ U = U2) (b : ℕ)
    {t : Equiv.Perm (Fin 42)} (ht : t ∈ U) (hc : h0 ^ (2 ^ b) * t = t * h0 ^ (2 ^ b)) :
    t = 1 := by
  have hc' : h0 * t = t * h0 := by
    have h1 : Commute ((h0 ^ (2 ^ b)) ^ (2 ^ b)) t := Commute.pow_left hc _
    rw [← pow_mul, ← mul_pow, show (2 : ℕ) * 2 = 4 from rfl, h0_pow_four_pow] at h1
    exact h1
  rcases hU with rfl | rfl
  · obtain ⟨k, hk, rfl⟩ := mem_U1_iff.1 ht
    by_contra hne
    have hk0 : k ≠ 0 := fun h => hne (by rw [h, wordPerm_tg_zero])
    exact (h0_moves hk hk0).1 hc'
  · obtain ⟨k, hk, rfl⟩ := mem_U2_iff.1 ht
    by_contra hne
    have hk0 : k ≠ 0 := fun h => hne (by rw [h, mul_zero, wordPerm_tg_zero])
    exact (h0_moves hk hk0).2 hc'

variable {K P : Subgroup G} {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K}

theorem exists_fpf_lift
    [Finite G] (hP : IsSylowTwoIn P K) (hQ : IsQSetting q l)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e)
    {U : Subgroup (Equiv.Perm (Fin 42))} (hU : U = U1 ∨ U = U2) :
    ∃ f, ∃ hf : f ∈ K, Odd (orderOf f) ∧
      f ∈ normalizer (pullP K P hP.1 (U.comap q) : Set G) ∧
      ∀ t ∈ U, q (jq K ⟨f, hf⟩) * t = t * q (jq K ⟨f, hf⟩) → t = 1 := by
  have hUT : U ≤ T0 := by
    rcases hU with rfl | rfl
    exacts [U1_le_T0, U2_le_T0]
  have hh0U : h0 ∈ normalizer (U : Set (Equiv.Perm (Fin 42))) := by
    rcases hU with rfl | rfl
    · exact P1_le_normalizer_U1 (B0_le_P1_P2.1 h0_mem_B0)
    · exact P2_le_normalizer_U2 (B0_le_P1_P2.2 h0_mem_B0)
  obtain ⟨n, hn, hnN, hnu⟩ :=
    exists_lift_normalizer hP hQ.qsurj hT hUT (B0_le_S h0_mem_B0) hh0U
  obtain ⟨p, hpP, hpK, hpq⟩ := exists_over hQ hT (hUT (U.inv_mem hnu))
  have hpA : p ∈ pullP K P hP.1 (U.comap q) := by
    refine mem_pullP.2 ⟨hpP, ?_⟩
    rw [mem_comap, show (⟨p, hP.1 hpP⟩ : K) = ⟨p, hpK⟩ from rfl, hpq]
    exact U.inv_mem hnu
  have hn₁ : p * n ∈ K := K.mul_mem hpK hn
  have hq₁ : q (jq K ⟨p * n, hn₁⟩) = h0 := by
    have e1 : (⟨p * n, hn₁⟩ : K) = ⟨p, hpK⟩ * ⟨n, hn⟩ := rfl
    rw [e1, map_mul, map_mul, hpq]
    group
  obtain ⟨b, hb⟩ := exists_odd_pow (p * n)
  have hfK : (p * n) ^ (2 ^ b) ∈ K := K.pow_mem hn₁ _
  refine ⟨(p * n) ^ (2 ^ b), hfK, hb, pow_mem (mul_mem (le_normalizer hpA) hnN) _,
    fun t ht hc => ?_⟩
  have hq : q (jq K ⟨(p * n) ^ (2 ^ b), hfK⟩) = h0 ^ (2 ^ b) := by
    rw [show (⟨(p * n) ^ (2 ^ b), hfK⟩ : K) = ⟨p * n, hn₁⟩ ^ (2 ^ b) from
      Subtype.ext (by rw [SubmonoidClass.coe_pow]), map_pow, map_pow, hq₁]
  rw [hq] at hc
  exact eq_one_of_comm_h0_pow hU b ht hc

theorem maxElementaryThree :
    ∀ (G : Type) [Group G] [Finite G] (K P A : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
      (∀ z ∈ P ⊓ zStarIn K, z * z = 1) → A ≤ P → IsElemTwo A →
      Nat.card A = 16 * Nat.card ↥(P ⊓ zStarIn K) →
      ∃ f ∈ K, Odd (orderOf f) ∧ f ∈ normalizer (A : Set G) ∧
        A ⊓ centralizer ({f} : Set G) = P ⊓ zStarIn K ∧
        ∃ A₀ : Subgroup G, A₀ ≤ A ∧ Nat.card A₀ = 16 ∧ A₀ ⊓ zStarIn K = ⊥ ∧
          f ∈ normalizer (A₀ : Set G) ∧ A₀ ⊓ centralizer ({f} : Set G) = ⊥ := by
  intro G _ _ K P A hK hL hP hZ hAP hA hcard
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  obtain ⟨U, hU, hAU⟩ := exists_U hP.1 hT hAP fun {y} hy => by
    rw [← map_mul, ← map_mul]
    have e1 : (⟨y, hP.1 (hAP hy)⟩ : K) * ⟨y, hP.1 (hAP hy)⟩ = 1 := Subtype.ext (hA.2 y hy)
    rw [e1, map_one, map_one]
  have hUT : U ≤ T0 := by
    rcases hU with rfl | rfl
    exacts [U1_le_T0, U2_le_T0]
  have hcardU : Nat.card U = 16 := by
    rcases hU with rfl | rfl
    exacts [card_U1, card_U2]
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  have hAA : A = pullP K P hP.1 (U.comap q) := by
    refine Subgroup.eq_of_le_of_card_ge (fun y hy => mem_pullP.2 ⟨hAP hy, hAU hy⟩) ?_
    rw [card_pullP hP2 hT (comap_mono hUT),
      card_comap_eq q U (fun t ht => hqsurj t (T0_le_S (hUT ht))), hcardU,
      ← Nat.card_congr ζ.toEquiv, hcard]
  obtain ⟨f, hfK, hfo, hfN, hfp⟩ := exists_fpf_lift hP hQ hT hU
  rw [← hAA] at hfN
  have hCA : A ⊓ centralizer ({f} : Set G) = P ⊓ zStarIn K := by
    ext y
    rw [mem_inf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hyA, hyc⟩
      have hyP := hAP hyA
      refine ⟨hyP, (mem_zStarIn_iff (hP.1 hyP)).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker]
      refine hfp _ (hAU hyA) ?_
      have e1 : (⟨f, hfK⟩ : K) * ⟨y, hP.1 hyP⟩ = ⟨y, hP.1 hyP⟩ * ⟨f, hfK⟩ :=
        Subtype.ext hyc.symm
      have h1 := congrArg (fun k => q (jq K k)) e1
      simp only [map_mul] at h1
      exact h1
    · rintro ⟨hyP, hyZ⟩
      have hyA : y ∈ A := by
        rw [hAA]
        refine mem_pullP.2 ⟨hyP, ?_⟩
        have hk : jq K ⟨y, hP.1 hyP⟩ ∈ q.ker := by
          rw [hqker]
          exact (mem_zStarIn_iff _).1 hyZ
        rw [mem_comap, MonoidHom.mem_ker.mp hk]
        exact U.one_mem
      refine ⟨hyA, ?_⟩
      have hfy : f * y * f⁻¹ ∈ A := (mem_normalizer_iff.mp hfN y).mp hyA
      have h1 : f * y * f⁻¹ = y := by
        refine eq_of_jq_eq hP.1 hP2 (hAP hfy) hyP ?_
        have e1 : (⟨f * y * f⁻¹, hP.1 (hAP hfy)⟩ : K) =
            ⟨f, hfK⟩ * ⟨y, hP.1 hyP⟩ * (⟨f, hfK⟩ : K)⁻¹ := rfl
        have hc := mem_center_iff.mp ((mem_zStarIn_iff (hP.1 hyP)).1 hyZ) (jq K ⟨f, hfK⟩)
        rw [e1, map_mul, map_mul, map_inv, hc]
        group
      calc y * f = f * y * f⁻¹ * f := by rw [h1]
        _ = f * y := by group
  obtain ⟨A₀, hA₀A, hfA₀, hA₀c, hcard₀⟩ := exists_complement_fixed hA hfN hfo
  rw [hCA, hcard] at hcard₀
  refine ⟨f, hfK, hfo, hfN, hCA, A₀, hA₀A,
    Nat.eq_of_mul_eq_mul_right Nat.card_pos hcard₀, ?_, hfA₀, hA₀c⟩
  rw [eq_bot_iff]
  rintro g ⟨hg₀, hgZ⟩
  have hgC : g ∈ A ⊓ centralizer ({f} : Set G) := by
    rw [hCA]
    exact ⟨hAP (hA₀A hg₀), hgZ⟩
  have : g ∈ A₀ ⊓ centralizer ({f} : Set G) := ⟨hg₀, hgC.2⟩
  rwa [hA₀c] at this

end CFSG.ComponentClassification.GrSLit.L34Facts
