module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34FactsSec5Three

public section

namespace CFSG.ComponentClassification.GrSLit.L34Facts

open CFSG Subgroup CFSG.PSL3Four CFSG.ComponentClassification.PSL3Four
open CFSG.LieType.Multipliers CFSG.LieType.Multipliers.L34

variable {G : Type} [Group G]

theorem exists_complement_fixed₂ [Finite G] {A : Subgroup G}
    (hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hA2 : IsPGroup 2 A) {f : G}
    (hfA : f ∈ normalizer (A : Set G)) (hf : Odd (orderOf f)) :
    ∃ A₀ : Subgroup G, A₀ ≤ A ∧ (∀ g : G, g ∈ A₀ ↔ ∃ a ∈ A, a⁻¹ * (f * a * f⁻¹) = g) ∧
      f ∈ normalizer (A₀ : Set G) ∧ A₀ ⊓ centralizer ({f} : Set G) = ⊥ ∧
      Nat.card A₀ * Nat.card ↥(A ⊓ centralizer ({f} : Set G)) = Nat.card A := by
  have hc : ∀ a ∈ A, f * a * f⁻¹ ∈ A := fun a ha => (mem_normalizer_iff.mp hfA a).mp ha
  have hc' : ∀ a ∈ A, f⁻¹ * a * f ∈ A := fun a ha => by
    refine (mem_normalizer_iff.mp hfA (f⁻¹ * a * f)).mpr ?_
    rwa [show f * (f⁻¹ * a * f) * f⁻¹ = a by group]
  have hθA : ∀ a ∈ A, a⁻¹ * (f * a * f⁻¹) ∈ A := fun a ha => A.mul_mem (A.inv_mem ha) (hc a ha)
  let θ : A →* A := MonoidHom.mk' (fun a => ⟨a⁻¹ * (f * a * f⁻¹), hθA a a.2⟩) fun a b => by
    apply Subtype.ext
    have h1 := hcomm _ (A.inv_mem b.2) _ (hθA a a.2)
    show ((a : G) * b)⁻¹ * (f * (a * b) * f⁻¹) =
      (a : G)⁻¹ * (f * a * f⁻¹) * ((b : G)⁻¹ * (f * b * f⁻¹))
    calc ((a : G) * b)⁻¹ * (f * (a * b) * f⁻¹) =
        (b : G)⁻¹ * ((a : G)⁻¹ * (f * a * f⁻¹)) * (f * b * f⁻¹) := by group
      _ = (a : G)⁻¹ * (f * a * f⁻¹) * (b : G)⁻¹ * (f * b * f⁻¹) := by rw [h1]
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
  refine ⟨A₀, map_subtype_le _, hmemA₀, ?_, ?_, ?_⟩
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
    have hfg : Commute f g := hgc.symm
    have hk : ∀ k : ℕ, f ^ k * a * (f ^ k)⁻¹ = a * g ^ k := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        calc f ^ (k + 1) * a * (f ^ (k + 1))⁻¹ = f * (f ^ k * a * (f ^ k)⁻¹) * f⁻¹ := by
              rw [pow_succ']; group
          _ = f * (a * g ^ k) * f⁻¹ := by rw [ih]
          _ = (f * a * f⁻¹) * (f * g ^ k * f⁻¹) := by group
          _ = a * g * g ^ k := by rw [h1, (hfg.pow_right k).eq, mul_inv_cancel_right]
          _ = a * g ^ (k + 1) := by rw [pow_succ', mul_assoc]
    have hgm : g ^ orderOf f = 1 := by
      have := hk (orderOf f)
      rw [pow_orderOf_eq_one, inv_one, one_mul, mul_one] at this
      exact (mul_eq_left.mp this.symm)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨j, hj⟩ := hA2 ⟨g, hgA⟩
    have hj' : g ^ (2 ^ j) = 1 := congrArg Subtype.val hj
    have hcop : Nat.Coprime (2 ^ j) (orderOf f) :=
      Nat.Coprime.pow_left j (Nat.coprime_two_left.2 hf)
    have h2 := Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hj')
      (orderOf_dvd_of_pow_eq_one hgm)
    show g ∈ (⊥ : Subgroup G)
    rw [mem_bot]
    exact orderOf_eq_one_iff.mp h2
  · rw [hA₀, Subgroup.card_map_of_injective Subtype.val_injective]
    have h1 : Nat.card θ.ker = Nat.card ↥(A ⊓ centralizer ({f} : Set G)) := by
      refine Nat.card_congr
        { toFun := fun a => ⟨a.1.1, a.1.2, (hker a.1).1 a.2⟩
          invFun := fun g => ⟨⟨g.1, g.2.1⟩, (hker ⟨g.1, g.2.1⟩).2 g.2.2⟩
          left_inv := fun a => rfl
          right_inv := fun g => rfl }
    rw [← h1, mul_comm, ← Subgroup.index_ker, Subgroup.card_mul_index]

theorem B0_le_normalizer_Z0 :
    B0 ≤ normalizer (Z0 : Set (Equiv.Perm (Fin 42))) := by
  intro b hb
  have hT : ∀ {c : Equiv.Perm (Fin 42)}, c ∈ B0 → ∀ t ∈ Z0, c * t * c⁻¹ ∈ Z0 := by
    intro c hc t ht
    have hcT := B0_le_normalizer hc
    refine ⟨mem_centralizer_iff.mpr fun u hu => ?_, (mem_normalizer_iff.mp hcT t).mp ht.2⟩
    have hu' : c⁻¹ * u * c ∈ T0 := by
      refine (mem_normalizer_iff.mp hcT (c⁻¹ * u * c)).mpr ?_
      rwa [show c * (c⁻¹ * u * c) * c⁻¹ = u by group]
    have h1 := (mem_centralizer_iff.mp ht.1) _ hu'
    calc u * (c * t * c⁻¹) = c * ((c⁻¹ * u * c) * t) * c⁻¹ := by group
      _ = c * (t * (c⁻¹ * u * c)) * c⁻¹ := by rw [h1]
      _ = c * t * c⁻¹ * u := by group
  rw [mem_normalizer_iff]
  intro t
  refine ⟨hT hb t, fun h => ?_⟩
  have := hT (B0.inv_mem hb) _ h
  rwa [show b⁻¹ * (b * t * b⁻¹) * b⁻¹⁻¹ = t by group] at this

variable {K P : Subgroup G} {q : Jhat K →* Equiv.Perm (Fin 42)} {l : Cover →* Jhat K}

theorem exists_odd_lift_h0
    [Finite G] (hP : IsSylowTwoIn P K) (hQ : IsQSetting q l)
    (hT : ∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e) :
    ∃ f, ∃ hf : f ∈ K, f ∈ normalizer (P : Set G) ∧ Odd (orderOf f) ∧
      ∃ b : ℕ, q (jq K ⟨f, hf⟩) = h0 ^ (2 ^ b) := by
  have hPP : pullP K P hP.1 (T0.comap q) = P := by
    ext y
    rw [mem_pullP]
    exact ⟨fun ⟨hy, _⟩ => hy, fun hy => ⟨hy, (hT _).2 ⟨y, hy, _, rfl⟩⟩⟩
  obtain ⟨n, hn, hnN, hnu⟩ := exists_lift_normalizer hP hQ.qsurj hT le_rfl
    (B0_le_S h0_mem_B0) (B0_le_normalizer h0_mem_B0)
  rw [hPP] at hnN
  obtain ⟨p, hpP, hpK, hpq⟩ := exists_over hQ hT (T0.inv_mem hnu)
  have hn₁ : p * n ∈ K := K.mul_mem hpK hn
  have hq₁ : q (jq K ⟨p * n, hn₁⟩) = h0 := by
    have e1 : (⟨p * n, hn₁⟩ : K) = ⟨p, hpK⟩ * ⟨n, hn⟩ := rfl
    rw [e1, map_mul, map_mul, hpq]
    group
  obtain ⟨b, hb⟩ := exists_odd_pow (p * n)
  have hfK : (p * n) ^ (2 ^ b) ∈ K := K.pow_mem hn₁ _
  refine ⟨(p * n) ^ (2 ^ b), hfK, pow_mem (mul_mem (le_normalizer hpP) hnN) _, hb, b, ?_⟩
  rw [show (⟨(p * n) ^ (2 ^ b), hfK⟩ : K) = ⟨p * n, hn₁⟩ ^ (2 ^ b) from
    Subtype.ext (by rw [SubmonoidClass.coe_pow]), map_pow, map_pow, hq₁]

theorem IsQSetting.comm_of_Z0
    {E : Type*} [Group E] {q : E →* Equiv.Perm (Fin 42)}
    {l : Cover →* E} (h : IsQSetting q l) {x y : E} (hx : q x ∈ Z0) (hy : q y ∈ Z0) :
    x * y = y * x := by
  set e₄ := l (cv (tw 4)) with he₄
  set e₈ := l (cv (tw 8)) with he₈
  have c48 : Commute e₄ e₈ := by
    have h1 := congrArg l (cv_comm_of_commData (d := (4, 8, 0, 0, 0)) (by decide) rfl)
    rw [map_mul, map_mul] at h1
    exact h1
  have hq4 : q e₄ = wordPerm (tg 4) := h.q_lift (by norm_num)
  have hq8 : q e₈ = wordPerm (tg 8) := h.q_lift (by norm_num)
  have hdec : ∀ {x : E}, q x ∈ Z0 → ∃ i j : ℕ, ∃ z ∈ center E, x = e₄ ^ i * e₈ ^ j * z := by
    intro x hx
    obtain ⟨k, hk, hkx⟩ := mem_Z0.1 hx
    have hz : ∀ i j : ℕ, q (e₄ ^ i * e₈ ^ j) = q x →
        ∃ i' j' : ℕ, ∃ z ∈ center E, x = e₄ ^ i' * e₈ ^ j' * z := by
      intro i j hq
      refine ⟨i, j, (e₄ ^ i * e₈ ^ j)⁻¹ * x, h.ker_le ?_, by group⟩
      rw [MonoidHom.mem_ker, map_mul, map_inv, hq, inv_mul_cancel]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl
    · exact hz 0 0 (by rw [pow_zero, pow_zero, mul_one, map_one, ← hkx, wordPerm_tg_zero])
    · exact hz 1 0 (by rw [pow_one, pow_zero, mul_one, hq4, hkx])
    · exact hz 0 1 (by rw [pow_zero, pow_one, one_mul, hq8, hkx])
    · exact hz 1 1 (by rw [pow_one, pow_one, map_mul, hq4, hq8, tg4_mul_tg8, hkx])
  obtain ⟨i, j, z, hz, rfl⟩ := hdec hx
  obtain ⟨i', j', z', hz', rfl⟩ := hdec hy
  have hc : Commute (e₄ ^ i * e₈ ^ j) (e₄ ^ i' * e₈ ^ j') :=
    (((Commute.refl e₄).pow_pow i i').mul_right (c48.pow_pow i j')).mul_left
      ((c48.symm.pow_pow j i').mul_right ((Commute.refl e₈).pow_pow j j'))
  have hzc := mem_center_iff.mp hz
  have hzc' := mem_center_iff.mp hz'
  have hc' : Commute (e₄ ^ i * e₈ ^ j * z) (e₄ ^ i' * e₈ ^ j' * z') :=
    Commute.mul_left (Commute.mul_right hc (hzc' _))
      (Commute.mul_right (show Commute z (e₄ ^ i' * e₈ ^ j') from (hzc _).symm) (hzc' z))
  exact hc'.eq

private theorem commutator_le_self₀ (H : Subgroup G) : ⁅H, H⁆ ≤ H :=
  Subgroup.commutator_le.2 fun _ ha _ hb =>
    mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)

theorem commutatorFourGroupStrengthened :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G),
      (hK : ⁅K, K⁆ = K) → (hL : IsL34Type (K ⧸ Open.fusionZStar K)) →
      (hP : IsSylowTwoIn P K) →
      ∃ (q : Jhat K →* Equiv.Perm (Fin 42)) (_l : Cover →* Jhat K)
        (Y Zh : Subgroup G),
        (∀ e, q e ∈ S) ∧
        (∀ s ∈ S, ∃ e, q e = s) ∧
        q.ker = Subgroup.center (Jhat K) ∧
        (∀ e, q e ∈ T0 ↔ ∃ p ∈ P, ∃ hp : p ∈ K, jq K ⟨p, hp⟩ = e) ∧
        Zh = pullP K P hP.1 (Z0.comap q) ∧
        Y ≤ Zh ∧
        (∀ a ∈ Zh, ∀ b ∈ Zh, a * b = b * a) ∧
        Nat.card Zh = 4 * Nat.card ↥(P ⊓ zStarIn K) ∧
        Y ≤ P ∧ IsElemTwo Y ∧ Nat.card Y = 4 ∧ Y ⊓ zStarIn K = ⊥ ∧
        Y ≤ ⁅P, P⁆ ⊔ (P ⊓ zStarIn K) ∧
        ∀ y ∈ P, (∀ p ∈ P, p⁻¹ * y⁻¹ * p * y ∈ zStarIn K) →
          ∃ y' ∈ Y, y'⁻¹ * y ∈ zStarIn K := by
  intro G _ _ K P hK hL hP
  obtain ⟨q, l, hqS, hqsurj, hqker, h3, hl, hls, hT⟩ := exists_sylow_standard hK hL hP
  have hQ : IsQSetting q l := ⟨hqS, hqsurj, hqker, h3, hl, hls⟩
  have hP2 := GrS4.isPGroup_of_isSylowTwoIn hP
  set Zh := pullP K P hP.1 (Z0.comap q) with hZhd
  have hZc : ∀ x ∈ Zh, ∀ y ∈ Zh, x * y = y * x := by
    intro x hx y hy
    obtain ⟨hxP, hxZ⟩ := mem_pullP.1 hx
    obtain ⟨hyP, hyZ⟩ := mem_pullP.1 hy
    apply eq_of_jq_eq hP.1 hP2 (P.mul_mem hxP hyP) (P.mul_mem hyP hxP)
    show jq K (⟨x, hP.1 hxP⟩ * ⟨y, hP.1 hyP⟩) = jq K (⟨y, hP.1 hyP⟩ * ⟨x, hP.1 hxP⟩)
    rw [map_mul, map_mul]
    exact hQ.comm_of_Z0 hxZ hyZ
  have hZh2 : IsPGroup 2 Zh := hP2.to_le (pullP_le _)
  obtain ⟨f, hfK, hfP, hfo, b, hfq⟩ := exists_odd_lift_h0 hP hQ hT
  have hfZh : f ∈ normalizer (Zh : Set G) := by
    refine mem_normalizer_pullP hP hfK hfP ?_
    rw [hfq]
    exact pow_mem (B0_le_normalizer_Z0 h0_mem_B0) _
  have hCZ : Zh ⊓ centralizer ({f} : Set G) = P ⊓ zStarIn K := by
    ext y
    rw [mem_inf, mem_inf, mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hyZh, hyc⟩
      obtain ⟨hyP, hyZ⟩ := mem_pullP.1 hyZh
      refine ⟨hyP, (mem_zStarIn_iff (hP.1 hyP)).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker]
      refine eq_one_of_comm_h0_pow (U := U1) (Or.inl rfl) b (Z0_le_U1 hyZ) ?_
      have e1 : (⟨f, hfK⟩ : K) * ⟨y, hP.1 hyP⟩ = ⟨y, hP.1 hyP⟩ * ⟨f, hfK⟩ :=
        Subtype.ext hyc.symm
      have h1 := congrArg (fun k => q (jq K k)) e1
      simp only [map_mul] at h1
      rw [← hfq]
      exact h1
    · rintro ⟨hyP, hyZ⟩
      have hk : jq K ⟨y, hP.1 hyP⟩ ∈ q.ker := by
        rw [hqker]
        exact (mem_zStarIn_iff _).1 hyZ
      have hyZh : y ∈ Zh := by
        refine mem_pullP.2 ⟨hyP, ?_⟩
        rw [mem_comap, MonoidHom.mem_ker.mp hk]
        exact Z0.one_mem
      refine ⟨hyZh, ?_⟩
      have hfy : f * y * f⁻¹ ∈ P := (mem_normalizer_iff.mp hfP y).mp hyP
      have h1 : f * y * f⁻¹ = y := by
        refine eq_of_jq_eq hP.1 hP2 hfy hyP ?_
        have e1 : (⟨f * y * f⁻¹, hP.1 hfy⟩ : K) =
            ⟨f, hfK⟩ * ⟨y, hP.1 hyP⟩ * (⟨f, hfK⟩ : K)⁻¹ := rfl
        have hc := mem_center_iff.mp ((mem_zStarIn_iff (hP.1 hyP)).1 hyZ) (jq K ⟨f, hfK⟩)
        rw [e1, map_mul, map_mul, map_inv, hc]
        group
      calc y * f = f * y * f⁻¹ * f := by rw [h1]
        _ = f * y := by group
  obtain ⟨Y, hYZh, -, -, hYc, hcardY⟩ := exists_complement_fixed₂ hZc hZh2 hfZh hfo
  obtain ⟨ζ, -⟩ := exists_zeta hP hqker
  have hcardZh : Nat.card Zh = 4 * Nat.card ↥(P ⊓ zStarIn K) := by
    rw [hZhd, card_pullP hP2 hT (comap_mono (show Z0 ≤ T0 from inf_le_right)),
      card_comap_eq q Z0 (fun t ht => hqsurj t (T0_le_S ht.2)), card_Z0,
      ← Nat.card_congr ζ.toEquiv]
  rw [hCZ, hcardZh] at hcardY
  have hY4 : Nat.card Y = 4 := Nat.eq_of_mul_eq_mul_right Nat.card_pos hcardY
  have hYP : Y ≤ P := hYZh.trans (pullP_le _)
  have hYZ : Y ⊓ zStarIn K = ⊥ := by
    rw [eq_bot_iff]
    rintro g ⟨hgY, hgZ⟩
    have hgC : g ∈ Zh ⊓ centralizer ({f} : Set G) := by
      rw [hCZ]
      exact ⟨hYP hgY, hgZ⟩
    have : g ∈ Y ⊓ centralizer ({f} : Set G) := ⟨hgY, hgC.2⟩
    rwa [hYc] at this
  have hY0 : ∀ {y : G} (hy : y ∈ Y), q (jq K ⟨y, hP.1 (hYP hy)⟩) ∈ Z0 :=
    fun hy => (mem_pullP.1 (hYZh hy)).2
  have hbot : ∀ {u : G} (hu : u ∈ Y), q (jq K ⟨u, hP.1 (hYP hu)⟩) = 1 → u = 1 := by
    intro u hu hu1
    have huZ : u ∈ Y ⊓ zStarIn K := by
      refine ⟨hu, (mem_zStarIn_iff (hP.1 (hYP hu))).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker]
      exact hu1
    rw [hYZ] at huZ
    exact (mem_bot.mp huZ)
  refine ⟨q, l, Y, Zh, hqS, hqsurj, hqker, hT, hZhd, hYZh, hZc, hcardZh,
    hYP, ⟨fun x hx y hy => hZc x (hYZh hx) y (hYZh hy), fun y hy => ?_⟩, hY4, hYZ,
    fun y hy => ?_, fun y hyP hy => ?_⟩
  · refine hbot (Y.mul_mem hy hy) ?_
    show q (jq K (⟨y, hP.1 (hYP hy)⟩ * ⟨y, hP.1 (hYP hy)⟩)) = 1
    rw [map_mul, map_mul]
    exact mul_self_Z0 (hY0 hy)
  · obtain ⟨u, hu, huK, hq⟩ := exists_commutator_over hQ hT (hY0 hy)
    have huP : u ∈ P := commutator_le_self₀ P hu
    have hv : u⁻¹ * y ∈ P ⊓ zStarIn K := by
      refine ⟨P.mul_mem (P.inv_mem huP) (hYP hy), (mem_zStarIn_iff (hP.1 (P.mul_mem
        (P.inv_mem huP) (hYP hy)))).2 ?_⟩
      rw [← hqker, MonoidHom.mem_ker]
      have e1 : (⟨u⁻¹ * y, hP.1 (P.mul_mem (P.inv_mem huP) (hYP hy))⟩ : K) =
          (⟨u, huK⟩ : K)⁻¹ * ⟨y, hP.1 (hYP hy)⟩ := rfl
      rw [e1, map_mul, map_mul, map_inv, map_inv, hq, inv_mul_cancel]
    have hv' : u⁻¹ * y ∈ ⁅P, P⁆ ⊔ (P ⊓ zStarIn K) := mem_sup_right hv
    have := mul_mem (mem_sup_left hu) hv'
    rwa [mul_inv_cancel_left] at this
  · have hyZ0 : q (jq K ⟨y, hP.1 hyP⟩) ∈ Z0 := by
      refine (mem_Z0_iff_comm hP hqsurj hqker hT hyP).2 fun w hw => ?_
      have := inv_mem (hy w hw)
      rwa [show (w⁻¹ * y⁻¹ * w * y)⁻¹ = y⁻¹ * w⁻¹ * y * w by group] at this
    let ψ : ↥Y → ↥Z0 := fun y' => ⟨q (jq K ⟨y', hP.1 (hYP y'.2)⟩), hY0 y'.2⟩
    have hinj : Function.Injective ψ := by
      intro a c hac
      have h1 : q (jq K ⟨a, hP.1 (hYP a.2)⟩) = q (jq K ⟨c, hP.1 (hYP c.2)⟩) :=
        congrArg Subtype.val hac
      have h2 := hbot (Y.mul_mem (Y.inv_mem a.2) c.2) (by
        have e1 : (⟨(a : G)⁻¹ * c, hP.1 (hYP (Y.mul_mem (Y.inv_mem a.2) c.2))⟩ : K) =
            (⟨a, hP.1 (hYP a.2)⟩ : K)⁻¹ * ⟨c, hP.1 (hYP c.2)⟩ := rfl
        rw [e1, map_mul, map_mul, map_inv, map_inv, h1, inv_mul_cancel])
      exact Subtype.ext (inv_mul_eq_one.mp h2)
    obtain ⟨y', hy'⟩ := (hinj.bijective_of_nat_card_le (by rw [card_Z0, hY4])).2 ⟨_, hyZ0⟩
    refine ⟨y', y'.2, (mem_zStarIn_iff (hP.1 (P.mul_mem (P.inv_mem (hYP y'.2)) hyP))).2 ?_⟩
    rw [← hqker, MonoidHom.mem_ker]
    have h1 : q (jq K ⟨y', hP.1 (hYP y'.2)⟩) = q (jq K ⟨y, hP.1 hyP⟩) := congrArg Subtype.val hy'
    have e1 : (⟨(y' : G)⁻¹ * y, hP.1 (P.mul_mem (P.inv_mem (hYP y'.2)) hyP)⟩ : K) =
        (⟨y', hP.1 (hYP y'.2)⟩ : K)⁻¹ * ⟨y, hP.1 hyP⟩ := rfl
    rw [e1, map_mul, map_mul, map_inv, map_inv, h1, inv_mul_cancel]

theorem commutatorFourGroup :
    ∀ (G : Type) [Group G] [Finite G] (K P : Subgroup G), ⁅K, K⁆ = K →
      IsL34Type (K ⧸ Open.fusionZStar K) → IsSylowTwoIn P K →
      ∃ Y : Subgroup G, Y ≤ P ∧ IsElemTwo Y ∧ Nat.card Y = 4 ∧ Y ⊓ zStarIn K = ⊥ ∧
        Y ≤ ⁅P, P⁆ ⊔ (P ⊓ zStarIn K) ∧
        ∀ y ∈ P, (∀ p ∈ P, p⁻¹ * y⁻¹ * p * y ∈ zStarIn K) → ∃ y' ∈ Y, y'⁻¹ * y ∈ zStarIn K := by
  intro G _ _ K P hK hL hP
  obtain ⟨q, _l, Y, Zh, hqS, hqsurj, hqker, hT, hZh, hYZh, hZc, hcardZh,
    hYP, hY2, hY4, hYZ, hY0, hYcentral⟩ :=
    commutatorFourGroupStrengthened (G := G) (K := K) (P := P) hK hL hP
  exact ⟨Y, hYP, hY2, hY4, hYZ, hY0, hYcentral⟩

end CFSG.ComponentClassification.GrSLit.L34Facts
