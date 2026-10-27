module

public import CFSG.CGT.Timmesfeld75.Sec66Count
public import CFSG.CGT.Timmesfeld75.Sec66Eight
public import CFSG.CGT.Timmesfeld75.Sec66Stmt

public section

namespace CFSG.CGT.Timmesfeld75

open CFSG.Open

@[expose] def Sec66Three : Prop :=
  ∀ (G : Type) [Group G] (T T₁ : Subgroup G) (n m : ℕ), Sec6Ctx T T₁ n m → n = 3 →
    ∀ x ∈ classD T, ∀ y ∈ classD T, orderOf (x * y) = 4 → (x * y) ^ 2 ∈ classD T

@[expose] def Sec66ThreeStep : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T T₁ : Subgroup G) (m : ℕ), Sec6Ctx T T₁ 3 m →
    Sec62 → Sec63 → ∀ x y g : G, x ∈ T → x ≠ 1 → y ∈ classD T → orderOf (x * y) = 4 →
      y * y = 1 → conjSubgroup y T ≠ T → g ∈ T ⊔ conjSubgroup y T →
      conjSubgroup y (conjSubgroup g T) = conjSubgroup g T → y ∉ conjSubgroup g T →
      (x * y) ^ 2 ∈ classD T

theorem Sec66Three.toStep (h : Sec66Three) : Sec66ThreeStep :=
  fun G _ _ T T₁ m hc _ _ x y _ hx hx1 hy h4 _ _ _ _ _ =>
    h G T T₁ 3 m hc rfl x (mem_classD_of_mem hx hx1) y hy h4

variable {G : Type} [Group G] {T T₁ : Subgroup G} {n m : ℕ}

theorem Sec6Ctx.sec66_core (h62 : Sec62) (h63 : Sec63) (hH : Sec66ThreeStep)
    (hc : Sec6Ctx T T₁ n m)
    {x y : G} (hx : x ∈ T) (hx1 : x ≠ 1) (hy : y ∈ classD T) (h4 : orderOf (x * y) = 4) :
    (x * y) ^ 2 ∈ classD T := by
  have := hc.finite
  have hP := hc.hy.pair
  have hTab := hP.wc.1
  have hyy : y * y = 1 := mul_self_eq_one_of_mem_classD hTab hy
  have hxx : x * x = 1 := elemAbelian_mul_self hTab hx
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hxi : x⁻¹ = x := inv_eq_of_mul_eq_one_right hxx
  have hxD : x ∈ classD T := mem_classD_of_mem hx hx1
  set m' := y * x * y⁻¹ with hm'
  have hsq : (x * y) ^ 2 = x * m' := by
    rw [pow_two, hm', hyi]
    group
  have hne1 : (x * y) ^ 2 ≠ 1 :=
    pow_ne_one_of_lt_orderOf (by norm_num) (by rw [h4]; norm_num)
  by_cases hT' : conjSubgroup y T = T
  · have hm'T : m' ∈ T := by
      have := conj_mem_conjSubgroup y hx
      rwa [hT'] at this
    rw [hsq]
    exact mem_classD_of_mem (T.mul_mem hx hm'T) (hsq ▸ hne1)
  have hm'T' : m' ∈ conjSubgroup y T := conj_mem_conjSubgroup y hx
  have hm'D : m' ∈ classD T := by
    have := classD_conj hxD y⁻¹
    rwa [inv_inv] at this
  have hm'1 : m' ≠ 1 := ne_one_of_mem_classD hm'D
  have hm'm' : m' * m' = 1 := mul_self_eq_one_of_mem_classD hTab hm'D
  have h44 : (x * m') * (x * m') = 1 := by
    have h := pow_orderOf_eq_one (x * y)
    rw [h4] at h
    have e : (x * y) ^ 4 = ((x * y) ^ 2) ^ 2 := by rw [← pow_mul]
    rw [e, hsq, pow_two] at h
    exact h
  have hxm : x * m' = m' * x := by
    have h1 : x * m' = (x * m')⁻¹ := (inv_eq_of_mul_eq_one_right h44).symm
    rw [h1, mul_inv_rev, inv_eq_of_mul_eq_one_right hm'm', hxi]
  have hmN : m' ∈ Subgroup.normalizer (T : Set G) :=
    hP.wc.centralizer_le_normalizer hx hx1 (Subgroup.mem_centralizer_singleton_iff.2 hxm.symm)
  have hxN' : x ∈ Subgroup.normalizer ((conjSubgroup y T : Subgroup G) : Set G) :=
    (hP.wc.conj y).centralizer_le_normalizer hm'T' hm'1
      (Subgroup.mem_centralizer_singleton_iff.2 hxm)
  have hbot : normIn T (conjSubgroup y T) ≠ ⊥ := fun h =>
    hx1 (Subgroup.mem_bot.1 (h ▸ mem_normIn.2 ⟨hx, hxN'⟩))
  have hS3 : Sec3 T (conjSubgroup y T) := hc.hS y hT' hbot
  have hI : Sec3Iso T (conjSubgroup y T) :=
    sec3Iso_of_conj_conj hc.hI ⟨1, (conjSubgroup_one T).symm⟩ ⟨y, rfl⟩ hT' hbot
  have hm'T : m' ∉ T := fun h => hm'1 (by
    have : m' ∈ T ⊓ conjSubgroup y T := ⟨h, hm'T'⟩
    rw [hS3.cfg.inf, Subgroup.mem_bot] at this
    exact this)
  have hmD : m' ∈ normD T := ⟨hm'D, hmN⟩
  have hm2 : m' ^ 2 = 1 := by rw [pow_two]; exact hm'm'
  have h23 := card_commSub_mul_card_centralizer hTab hm2 hmN
  by_cases hcard :
      Nat.card ↥(commSub m' T) = Nat.card ↥(T ⊓ Subgroup.centralizer ({m'} : Set G))
  ·
    have hmx2 : (m' * x) ^ 2 = 1 := by
      rw [pow_two]
      calc m' * x * (m' * x) = m' * (x * m') * x := by group
        _ = m' * (m' * x) * x := by rw [hxm]
        _ = (m' * m') * (x * x) := by group
        _ = 1 := by rw [hm'm', hxx, one_mul]
    obtain ⟨s, hs, hms⟩ := (card_commSub_eq_iff hTab hm2 hmN).1 hcard x hx hmx2
    rw [hsq, hxm, hms]
    exact classD_conj hm'D s
  have hL' : T ⊓ Subgroup.centralizer ({m'} : Set G) = normIn T (conjSubgroup y T) :=
    hS3.cfg.inf_centralizer_eq_normIn (mem_normIn.2 ⟨hm'T', hmN⟩) hm'1
  have hLpos : 0 < Nat.card ↥(normIn T T₁) := Nat.card_pos
  have hL2 : 2 ≤ Nat.card ↥(normIn T T₁) := by
    have h1 : 1 < Nat.card ↥(normIn T T₁) :=
      (Subgroup.one_lt_card_iff_ne_bot _).2 hP.nontriv
    omega
  have hmul := hc.mul_card_normIn
  have hLn := hc.card_normIn
  have hn2 : (2 ^ m) ^ (n - 1) ≠ 2 ^ m ∧ 2 ≤ n := by
    have hn1 := hc.one_le
    refine ⟨?_, ?_⟩
    · rcases h63 G T T₁ n m hc m' hmD hm'T with hC | ⟨h16, h8, h4'⟩
      · intro hh
        apply hcard
        have hcm : Nat.card ↥(commSub m' T) = 2 ^ m := by
          refine Nat.eq_of_mul_eq_mul_right hLpos ?_
          rw [hC] at h23
          rw [h23, hmul]
        rw [hcm, hC, hLn, hh]
      · exfalso
        apply hcard
        rw [h4'] at h23 ⊢
        rw [h16] at h23
        omega
    · by_contra hlt
      have : n = 1 := by omega
      rw [this] at hLn
      simp only [Nat.sub_self, pow_zero] at hLn
      omega
  have hLc : Nat.card ↥(normIn T (conjSubgroup y T)) = Nat.card ↥(normIn T T₁) := by
    rw [← hL']
    rcases h63 G T T₁ n m hc m' hmD hm'T with hC | ⟨h16, h8, h4'⟩
    · exact hC
    · exfalso
      apply hcard
      rw [h4'] at h23 ⊢
      rw [h16] at h23
      omega
  obtain ⟨g, hg, hfix, hu⟩ : ∃ g ∈ T ⊔ conjSubgroup y T,
      conjSubgroup y (conjSubgroup g T) = conjSubgroup g T ∧
        (n = 4 ∧ m = 1 →
          ∃ u ∈ conjSubgroup g T, u ∉ cfgM T (conjSubgroup y T) ∧ y * u = u * y) := by
    by_cases hA8 : n = 4 ∧ m = 1
    · obtain ⟨h16, h8⟩ := hc.card_eq_sixteen_iff.2 hA8
      obtain ⟨g, hg, hfix, hu⟩ := hS3.exists_fixed_conj_eight hI hyy rfl h16 (by rw [hLc]; exact h8)
      exact ⟨g, hg, hfix, fun _ => hu⟩
    · obtain ⟨g, hg, hfix⟩ := hS3.exists_fixed_conj_swap hI hyy rfl
      exact ⟨g, hg, hfix, fun h => absurd h hA8⟩
  by_cases hyS : y ∈ conjSubgroup g T
  ·
    have hxD' : x ∈ classDIn (T ⊔ conjSubgroup y T) T :=
      ⟨hx1, 1, Subgroup.one_mem _, by rwa [conjSubgroup_one]⟩
    have hyD' : y ∈ classDIn (T ⊔ conjSubgroup y T) T := ⟨ne_one_of_mem_classD hy, g, hg, hyS⟩
    obtain ⟨hne, x₀, -, hmem⟩ := hS3.isRootInvolutionSet.2.2 x hxD' y hyD' h4
    exact mem_classD_of_mem_conjSubgroup hmem hne
  ·
    obtain ⟨hc1, hc2⟩ := hc.card_normIn_le_sq_aux h62 h63 hy hyy hS3 hg hfix hyS
    have hyN : y ∈ Subgroup.normalizer ((conjSubgroup g T : Subgroup G) : Set G) :=
      mem_normalizer_iff_conjSubgroup_eq.2 hfix
    have hSab : IsElemAbelian 2 (conjSubgroup g T) := isElemAbelian_conjSubgroup hTab g
    have hy2 : y ^ 2 = 1 := by rw [pow_two]; exact hyy
    have h23S := card_commSub_mul_card_centralizer hSab hy2 hyN
    rw [card_conjSubgroup] at h23S
    have hcnt : Nat.card ↥(normIn T (conjSubgroup y T)) ≤
        Nat.card ↥(commSub y (conjSubgroup g T)) ^ 2 :=
      hc1.trans (Nat.pow_le_pow_left (Subgroup.card_le_of_le hc2) 2)
    by_cases hA8 : n = 4 ∧ m = 1
    ·
      exfalso
      obtain ⟨h16, h8⟩ := hc.card_eq_sixteen_iff.2 hA8
      obtain ⟨u, huU, huM, huy⟩ := hu hA8
      set H := conjSubgroup g T ⊓ cfgM T (conjSubgroup y T) ⊓
        Subgroup.centralizer ({y} : Set G) with hHdef
      set K := conjSubgroup g T ⊓ Subgroup.centralizer ({y} : Set G) with hKdef
      have hHK : H ≤ K := inf_le_inf_right _ inf_le_left
      have huK : u ∈ K := ⟨huU, Subgroup.mem_centralizer_singleton_iff.2 huy.symm⟩
      have huH : u ∉ H := fun h => huM h.1.2
      have h2H := card_ge_two_mul_of_lt hHK huK huH
      have hH2 : Nat.card ↥H ≤ 2 := by
        rcases hc.card_centralizer_conj h63 hy hyN hyS with hS1 | ⟨h16', h8', hS4⟩
        · have hcs : Nat.card ↥(commSub y (conjSubgroup g T)) = 2 := by
            rw [hS1, h8, h16] at h23S
            omega
          exact (Subgroup.card_le_of_le hc2).trans hcs.le
        · have hS4' : Nat.card ↥K = 4 := hS4
          omega
      have h8H : 8 ≤ Nat.card ↥H ^ 2 := by
        rw [← h8, ← hLc]
        exact hc1
      have : Nat.card ↥H ^ 2 ≤ 2 ^ 2 := Nat.pow_le_pow_left hH2 2
      omega
    · have hn : n = 3 := by
        rcases hc.card_centralizer_conj h63 hy hyN hyS with hS1 | ⟨h16, h8, hS4⟩
        · have hcs : Nat.card ↥(commSub y (conjSubgroup g T)) = 2 ^ m := by
            refine Nat.eq_of_mul_eq_mul_right hLpos ?_
            rw [hS1] at h23S
            rw [h23S, hmul]
          rw [hLc, hcs, hLn] at hcnt
          have h2m : 1 < 2 ^ m := Nat.one_lt_two_pow (by have := hc.one_le_m; omega)
          have hle2 : n - 1 ≤ 2 := (Nat.pow_le_pow_iff_right h2m).1 hcnt
          have hne1 : n - 1 ≠ 1 := fun h => hn2.1 (by rw [h, pow_one])
          have := hn2.2
          omega
        · exact absurd (hc.card_eq_sixteen_iff.1 ⟨h16, h8⟩) hA8
      subst hn
      exact hH G T T₁ m hc h62 h63 x y g hx hx1 hy h4 hyy hT' hg hfix hyS

theorem sec66_of_step (h62 : Sec62) (h63 : Sec63) (hH : Sec66ThreeStep) : Sec66 := by
  intro G _ T T₁ n m hc x hx y hy h4
  obtain ⟨k, t, ht, ht1, hxk⟩ := hx
  have hy' : k * y * k⁻¹ ∈ classD T := by
    have := classD_conj hy k⁻¹
    rwa [inv_inv] at this
  have e : t * (k * y * k⁻¹) = k * (x * y) * k⁻¹ := by rw [hxk]; group
  have hconj : orderOf (t * (k * y * k⁻¹)) = 4 := by
    rw [e, ← h4]
    have := orderOf_inv_mul_mul_eq k⁻¹ (x * y)
    rwa [inv_inv] at this
  have hcore := hc.sec66_core h62 h63 hH ht ht1 hy' hconj
  have e2 : (x * y) ^ 2 = k⁻¹ * (t * (k * y * k⁻¹)) ^ 2 * k := by
    have e3 : x * y = k⁻¹ * (t * (k * y * k⁻¹)) * k⁻¹⁻¹ := by
      rw [inv_inv, hxk]
      group
    rw [e3, conj_pow, inv_inv]
  rw [e2]
  exact classD_conj hcore k

theorem sec66_of_three (h62 : Sec62) (h63 : Sec63) (hH : Sec66Three) : Sec66 :=
  sec66_of_step h62 h63 hH.toStep

end CFSG.CGT.Timmesfeld75
