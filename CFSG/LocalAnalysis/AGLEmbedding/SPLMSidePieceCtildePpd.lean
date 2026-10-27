module

public import CFSG.LocalAnalysis.AGLEmbedding.SPLMSidePieceCtildeAux
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux

public section

namespace CFSG.AGLEmbedding

open CFSG.Open CFSG.Quasithin

namespace SPLMSide

theorem exists_prime_dvd_sq_add_one_odd {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ∃ r : ℕ, r.Prime ∧ r ∣ p ^ 2 + 1 ∧ r ≠ p ∧ r ∣ p ^ 4 - 1 ∧
      ∀ k : ℕ, 0 < k → k < 4 → ¬ r ∣ p ^ k - 1 := by
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  have hm1 : 1 ≤ m := by
    have := hp.two_le
    omega
  have hsq : p ^ 2 + 1 = 2 * (2 * (m ^ 2 + m) + 1) := by subst hm; ring
  have hn1 : 2 * (m ^ 2 + m) + 1 ≠ 1 := by
    have : 1 ≤ m ^ 2 + m := le_add_left hm1
    omega
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd hn1
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h1 : 2 ∣ 1 := (Nat.dvd_add_right (Dvd.intro _ rfl)).mp hrn
    omega
  have hrp : r ∣ p ^ 2 + 1 := hsq ▸ hrn.mul_left 2
  have : Fact r.Prime := ⟨hr⟩
  have hx : ((p : ZMod r)) ^ 2 + 1 = 0 := by
    have := (ZMod.natCast_eq_zero_iff (p ^ 2 + 1) r).mpr hrp
    push_cast at this
    exact this
  have htwo : (2 : ZMod r) ≠ 0 := by
    intro h2
    have h2' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h2
    rw [ZMod.natCast_eq_zero_iff] at h2'
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp h2')
  have hcast : ∀ k : ℕ, r ∣ p ^ k - 1 → (p : ZMod r) ^ k - 1 = 0 := by
    intro k hk
    have h1 : 1 ≤ p ^ k := Nat.one_le_pow _ _ hp.pos
    have := (ZMod.natCast_eq_zero_iff (p ^ k - 1) r).mpr hk
    rw [Nat.cast_sub h1] at this
    push_cast at this
    exact this
  refine ⟨r, hr, hrp, ?_, ?_, ?_⟩
  · rintro rfl
    have h0 : ((r : ℕ) : ZMod r) = 0 := ZMod.natCast_self r
    rw [h0] at hx
    norm_num at hx
  · have h4 : p ^ 4 - 1 = (p ^ 2 + 1) * (p ^ 2 - 1) := by
      rw [← Nat.sq_sub_sq, one_pow, ← pow_mul]
    rw [h4]
    exact hrp.mul_right _
  · intro k hk0 hk4 hk
    have h1 := hcast k hk
    apply htwo
    interval_cases k
    · linear_combination hx - ((p : ZMod r) + 1) * h1
    · linear_combination hx - h1
    · linear_combination (1 - (p : ZMod r) * ((p : ZMod r) - 1)) * hx +
        ((p : ZMod r) - 1) * h1

variable {X : Type} [Group X] [Finite X]

theorem mem_normalizer_centerOf_of_mem_normalizer {S : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (S : Set X)) :
    g ∈ Subgroup.normalizer ((centerOf S : Subgroup X) : Set X) := by
  apply mem_normalizer_of_conj_map_le
  rintro _ ⟨x, ⟨hxS, hxC⟩, rfl⟩
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg x).mp hxS, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro s hs
  have hs' : g⁻¹ * s * g ∈ S := by
    have h1 : g * (g⁻¹ * s * g) * g⁻¹ = s := by group
    exact (Subgroup.mem_normalizer_iff.mp hg _).mpr (h1.symm ▸ hs)
  have hc := Subgroup.mem_centralizer_iff.mp hxC _ hs'
  change s * (g * x * g⁻¹) = g * x * g⁻¹ * s
  calc s * (g * x * g⁻¹) = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by rw [hc]
    _ = g * x * g⁻¹ * s := by group

theorem commute_of_orderOf_eq_prime_of_card {V : Subgroup X} {s : X} {r q : ℕ} [Fact r.Prime]
    (hq : q.Prime) (hrq : r ≠ q) (hs : orderOf s = r)
    (hsN : s ∈ Subgroup.normalizer (V : Set X)) {a : ℕ} (hV : Nat.card V = q ^ a)
    (hra : ∀ c, 1 ≤ c → c ≤ a → ¬ r ∣ q ^ c - 1) : ∀ v ∈ V, s * v = v * s := by
  set S := Subgroup.zpowers s
  have hSN : S ≤ Subgroup.normalizer (V : Set X) := Subgroup.zpowers_le.mpr hsN
  let _ : MulAction S V :=
    { smul := fun k v => ⟨(k : X) * v * (k : X)⁻¹,
        (Subgroup.mem_normalizer_iff.mp (hSN k.2) v).mp v.2⟩
      one_smul := fun v => by
        apply Subtype.ext
        change (1 : X) * v * 1⁻¹ = v
        group
      mul_smul := fun k l v => by
        apply Subtype.ext
        change ((k : X) * l) * v * ((k : X) * l)⁻¹ = k * (l * v * (l : X)⁻¹) * (k : X)⁻¹
        group }
  have hSp : IsPGroup r S := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hs, pow_one])
  have hmod := hSp.card_modEq_card_fixedPoints V
  let F : Subgroup V :=
    { carrier := MulAction.fixedPoints S V
      one_mem' := fun k => by
        apply Subtype.ext
        change (k : X) * 1 * (k : X)⁻¹ = 1
        group
      mul_mem' := fun {x y} hx hy k => by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (hx k)
        have h2 := congrArg Subtype.val (hy k)
        change (k : X) * x * (k : X)⁻¹ = x at h1
        change (k : X) * y * (k : X)⁻¹ = y at h2
        change (k : X) * (x * y) * (k : X)⁻¹ = x * y
        calc (k : X) * (x * y) * (k : X)⁻¹ =
            ((k : X) * x * (k : X)⁻¹) * ((k : X) * y * (k : X)⁻¹) := by group
          _ = x * y := by rw [h1, h2]
      inv_mem' := fun {x} hx k => by
        apply Subtype.ext
        have h1 := congrArg Subtype.val (hx k)
        change (k : X) * x * (k : X)⁻¹ = x at h1
        change (k : X) * (x : X)⁻¹ * (k : X)⁻¹ = (x : X)⁻¹
        calc (k : X) * (x : X)⁻¹ * (k : X)⁻¹ = ((k : X) * x * (k : X)⁻¹)⁻¹ := by group
          _ = (x : X)⁻¹ := by rw [h1] }
  have hFcard : Nat.card (MulAction.fixedPoints S V) = Nat.card F := rfl
  obtain ⟨b, hb, hFb⟩ := (Nat.dvd_prime_pow hq).1 (hV ▸ Subgroup.card_subgroup_dvd_card F)
  have hba : b = a := by
    by_contra hne
    have hlt : b < a := lt_of_le_of_ne hb hne
    rw [hV, hFcard, hFb] at hmod
    have hdvd : r ∣ q ^ a - q ^ b :=
      (Nat.modEq_iff_dvd' (Nat.pow_le_pow_right hq.pos hb)).1 hmod.symm
    have hfac : q ^ a - q ^ b = q ^ b * (q ^ (a - b) - 1) := by
      rw [Nat.mul_sub, mul_one, ← pow_add, Nat.add_sub_cancel' hb]
    rw [hfac] at hdvd
    have hcop : Nat.Coprime r (q ^ b) :=
      Nat.Coprime.pow_right _ ((Nat.coprime_primes Fact.out hq).2 hrq)
    exact hra (a - b) (by omega) (by omega) (hcop.dvd_of_dvd_mul_left hdvd)
  have htop : F = ⊤ := Subgroup.eq_top_of_card_eq _ (by rw [hFb, hba, hV])
  intro v hv
  have hfix : (⟨v, hv⟩ : V) ∈ F := by rw [htop]; exact Subgroup.mem_top _
  have := congrArg Subtype.val (hfix ⟨s, Subgroup.mem_zpowers s⟩)
  change s * v * s⁻¹ = v at this
  calc s * v = s * v * s⁻¹ * s := by group
    _ = v * s := by rw [this]

variable {p : ℕ} {R : Sylow p X} {X₀ : Subgroup X}

theorem sylow_facts_of_torus [Fact p.Prime] {K : Subgroup X} {T : Sylow p K}
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (hTF : OneLieTorusFacts p K T 2 1)
    (h2 : Nat.card (centerOf ((R : Subgroup X) ⊓ K)) = p ^ 2) :
    (∀ t ∈ (R : Subgroup X) ⊓ K, t ^ p = 1) ∧
    (∀ a ∈ (R : Subgroup X) ⊓ K, ∀ b ∈ (R : Subgroup X) ⊓ K,
      a * b * a⁻¹ * b⁻¹ ∈ centerOf ((R : Subgroup X) ⊓ K)) ∧
    ∃ a ∈ (R : Subgroup X) ⊓ K, ∃ b ∈ (R : Subgroup X) ⊓ K, a * b ≠ b * a := by
  obtain ⟨h6, hcomm, hexp, -⟩ := hTF.pair rfl
  have hZmap : ((T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)).map
      K.subtype = centerOf ((R : Subgroup X) ⊓ K) := by
    rw [map_inf_centralizer_eq_centerOf, hT]
  refine ⟨?_, ?_, ?_⟩
  · rintro _ ht
    obtain ⟨u, hu, rfl⟩ := hT.symm ▸ ht
    rw [Subgroup.coe_subtype, ← Subgroup.coe_pow, hexp u hu, Subgroup.coe_one]
  · intro a ha b hb
    obtain ⟨u, hu, rfl⟩ := hT.symm ▸ ha
    obtain ⟨v, hv, rfl⟩ := hT.symm ▸ hb
    have hmem : u * v * u⁻¹ * v⁻¹ ∈ ⁅(T : Subgroup K), (T : Subgroup K)⁆ := by
      rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hu hv
    rw [hcomm] at hmem
    rw [← hZmap]
    exact ⟨_, hmem, by simp⟩
  · by_contra hc
    have heq : centerOf ((R : Subgroup X) ⊓ K) = (R : Subgroup X) ⊓ K :=
      le_antisymm inf_le_left (le_inf le_rfl fun a ha =>
        Subgroup.mem_centralizer_iff.mpr fun b hb => not_not.mp fun hne => hc ⟨b, hb, a, ha, hne⟩)
    have h6' : Nat.card ((R : Subgroup X) ⊓ K : Subgroup X) = p ^ 6 := by
      rw [← hT, Subgroup.card_map_of_injective K.subtype_injective, h6]
    rw [heq, h6'] at h2
    have := Nat.pow_right_injective (Fact.out : p.Prime).two_le h2
    omega

theorem exists_eq_conj_of_fix_sylow [Fact p.Prime] {K : Subgroup X} {T : Sylow p K}
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K) (hF : OneLieFacts p K T)
    (hTF : OneLieTorusFacts p K T 2 1)
    (h2 : Nat.card (centerOf ((R : Subgroup X) ⊓ K)) = p ^ 2) :
    ∀ f : MulAut K, (∀ v ∈ (T : Subgroup K), f v = v) →
      ∃ t ∈ (T : Subgroup K), f = MulAut.conj t := by
  obtain ⟨h6, -, -, -⟩ := hTF.pair rfl
  have hZ : Nat.card (centerOf (T : Subgroup K)) = p ^ 2 := by
    rw [← h2, ← hT, ← map_inf_centralizer_eq_centerOf,
      Subgroup.card_map_of_injective K.subtype_injective]
    rfl
  have hTne : (T : Subgroup K) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h6
    have := Nat.one_lt_pow (by norm_num : 6 ≠ 0) (Fact.out : p.Prime).one_lt
    omega
  refine (hF.centralizer (T : Subgroup K) le_rfl hTne le_rfl).resolve_right ?_
  rintro ⟨hV, -⟩
  rw [← hV, h6] at hZ
  have := Nat.pow_right_injective (Fact.out : p.Prime).two_le hZ
  omega

theorem exists_ppd_of_torus [Fact p.Prime] (hp2 : p ≠ 2) {K : Subgroup X} {T : Sylow p K}
    (hT : (T : Subgroup K).map K.subtype = (R : Subgroup X) ⊓ K)
    (hTF : OneLieTorusFacts p K T 2 1)
    (hN : K ⊓ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) ≤ X₀)
    (h2 : Nat.card (centerOf ((R : Subgroup X) ⊓ K)) = p ^ 2) :
    ∃ r : ℕ, r.Prime ∧ r ∣ p ^ 2 + 1 ∧ ¬ r ∣ p ^ 2 - 1 ∧ ∃ c ∈ X₀, c ^ r = 1 ∧
      (∀ t ∈ (R : Subgroup X) ⊓ K, c * t * c⁻¹ ∈ (R : Subgroup X) ⊓ K) ∧
      (∀ x ∈ centerOf ((R : Subgroup X) ⊓ K), c * x = x * c) ∧
      ∀ V : Subgroup X, centerOf ((R : Subgroup X) ⊓ K) ≤ V → V ≤ (R : Subgroup X) ⊓ K →
        (∀ v ∈ V, c * v * c⁻¹ ∈ V) →
          V = centerOf ((R : Subgroup X) ⊓ K) ∨ V = (R : Subgroup X) ⊓ K := by
  obtain ⟨r, hr, hrp, hrne, hr4, hrk⟩ := exists_prime_dvd_sq_add_one_odd (Fact.out : p.Prime) hp2
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, -, -, hppd⟩ := hTF.pair rfl
  obtain ⟨c, hcN, hcr, hirr⟩ := hppd r hr hr4 hrk
  have hcNX : (c : X) ∈ Subgroup.normalizer (((R : Subgroup X) ⊓ K : Subgroup X) : Set X) :=
    hT ▸ coe_mem_normalizer_map_of_mem hcN
  have hZmap : ((T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K)).map
      K.subtype = centerOf ((R : Subgroup X) ⊓ K) := by
    rw [map_inf_centralizer_eq_centerOf, hT]
  refine ⟨r, hr, hrp, hrk 2 (by norm_num) (by norm_num), c, hN ⟨c.2, hcNX⟩, ?_, ?_, ?_, ?_⟩
  · have h1 := congrArg Subtype.val (pow_orderOf_eq_one c)
    rw [hcr] at h1
    simpa using h1
  · exact fun t ht => (Subgroup.mem_normalizer_iff.mp hcNX t).mp ht
  · have hcr' : orderOf (c : X) = r := by rw [Subgroup.orderOf_coe, hcr]
    exact commute_of_orderOf_eq_prime_of_card (Fact.out : p.Prime) hrne hcr'
      (mem_normalizer_centerOf_of_mem_normalizer hcNX) h2
      fun k hk1 hk2 => hrk k (by omega) (by omega)
  · intro V hZV hVT hcV
    set V' : Subgroup K := V.comap K.subtype
    have hVeq : V'.map K.subtype = V := by
      rw [Subgroup.map_comap_eq, Subgroup.range_subtype,
        inf_eq_right.mpr (hVT.trans inf_le_right)]
    have hZ : (T : Subgroup K) ⊓ Subgroup.centralizer ((T : Subgroup K) : Set K) ≤ V' :=
      fun y hy => hZV (hZmap ▸ ⟨y, hy, rfl⟩)
    have hV'T : V' ≤ T := fun y hy => by
      obtain ⟨w, hw, hwy⟩ := hT.symm ▸ hVT hy
      exact (Subtype.ext hwy : w = y) ▸ hw
    have hcV' : c ^ 1 ∈ Subgroup.normalizer (V' : Set K) := by
      rw [pow_one]
      apply mem_normalizer_of_conj_map_le
      rintro _ ⟨y, hy, rfl⟩
      exact hcV _ hy
    rcases (hirr 1 hr.not_dvd_one).2 V' hZ hV'T hcV' with h | h
    · left
      rw [← hVeq, h, hZmap]
    · right
      rw [← hVeq, h, hT]

end SPLMSide

end CFSG.AGLEmbedding
