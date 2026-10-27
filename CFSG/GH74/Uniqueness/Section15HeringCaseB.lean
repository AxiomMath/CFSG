module

public import CFSG.GH74.Uniqueness.Section15HeringMin
public import CFSG.GH74.Uniqueness.Section15HeringCyclic

public section

namespace CFSG.GH74.Uniqueness.Hering

open Subgroup MulAction

section Orbit

variable {G Ω : Type*} [Group G] [MulAction G Ω]

@[expose] def fixedSet (P : Subgroup G) (Ω : Type*) [MulAction G Ω] : Set Ω :=
  {x | ∀ g ∈ P, g • x = x}

theorem smul_mem_fixedSet {P : Subgroup G} {n : G} (hn : n ∈ normalizer (P : Set G)) {x : Ω}
    (hx : x ∈ fixedSet P Ω) : n • x ∈ fixedSet P Ω := by
  intro g hg
  have hg' : n⁻¹ * g * n ∈ P := by
    have := (mem_normalizer_iff.mp ((normalizer (P : Set G)).inv_mem hn) g).mp hg
    simpa using this
  calc g • n • x = n • ((n⁻¹ * g * n) • x) := by rw [smul_smul, smul_smul]; group
    _ = n • x := by rw [hx _ hg']

theorem conj_mem_centralizer_of_mem_normalizer {P : Subgroup G} {n c : G}
    (hn : n ∈ normalizer (P : Set G)) (hc : c ∈ centralizer (P : Set G)) :
    n⁻¹ * c * n ∈ centralizer (P : Set G) := by
  rw [mem_centralizer_iff] at hc ⊢
  intro g hg
  have hg' : n * g * n⁻¹ ∈ P := (mem_normalizer_iff.mp hn g).mp hg
  have := hc _ hg'
  calc g * (n⁻¹ * c * n) = n⁻¹ * ((n * g * n⁻¹) * c) * n := by group
    _ = n⁻¹ * (c * (n * g * n⁻¹)) * n := by rw [this]
    _ = n⁻¹ * c * n * g := by group

theorem orbit_argument {P : Subgroup G} {ω : Ω} (hω : ω ∈ fixedSet P Ω)
    (htr : ∀ x ∈ fixedSet P Ω, ∀ y ∈ fixedSet P Ω, x ≠ ω → y ≠ ω →
      ∃ c ∈ centralizer (P : Set G), c • x = y)
    (hNH : ∀ n ∈ normalizer (P : Set G), n • ω = ω → n ∈ centralizer (P : Set G))
    (hNC : ¬ normalizer (P : Set G) ≤ centralizer (P : Set G)) :
    (∀ c ∈ centralizer (P : Set G), c • ω = ω) ∧ ∃ n ∈ normalizer (P : Set G), n • ω ≠ ω ∧
      ∀ y ∈ fixedSet P Ω, y = ω ∨ y = n • ω := by
  have hCN : centralizer (P : Set G) ≤ normalizer (P : Set G) := centralizer_le_normalizer _
  have hfixC : ∀ c ∈ centralizer (P : Set G), c • ω = ω := by
    intro c hc
    by_contra hcω
    apply hNC
    intro n hn
    have hnω : n • ω ∈ fixedSet P Ω := smul_mem_fixedSet hn hω
    obtain ⟨c', hc', hc'ω⟩ : ∃ c' ∈ centralizer (P : Set G), c' • ω = n • ω := by
      by_cases h1 : n • ω = ω
      · exact ⟨1, one_mem _, by rw [one_smul, h1]⟩
      · obtain ⟨c'', hc''C, hc''x⟩ := htr (c • ω) (smul_mem_fixedSet (hCN hc) hω) (n • ω)
          hnω hcω h1
        exact ⟨c'' * c, mul_mem hc''C hc, by rw [mul_smul, hc''x]⟩
    have h1 : c'⁻¹ * n ∈ centralizer (P : Set G) :=
      hNH _ (mul_mem (inv_mem (hCN hc')) hn) (by rw [mul_smul, ← hc'ω, inv_smul_smul])
    have : n = c' * (c'⁻¹ * n) := by group
    rw [this]
    exact mul_mem hc' h1
  obtain ⟨n, hn, hnω⟩ : ∃ n ∈ normalizer (P : Set G), n • ω ≠ ω := by
    by_contra hcon
    push Not at hcon
    exact hNC fun n hn => hNH n hn (hcon n hn)
  refine ⟨hfixC, n, hn, hnω, fun y hy => ?_⟩
  by_cases hyω : y = ω
  · exact Or.inl hyω
  · right
    obtain ⟨c, hc, hcy⟩ := htr (n • ω) (smul_mem_fixedSet hn hω) y hy hnω hyω
    have h1 := hfixC _ (conj_mem_centralizer_of_mem_normalizer hn hc)
    rw [mul_smul, mul_smul] at h1
    have h2 : c • n • ω = n • ω := by
      have := congrArg (n • ·) h1
      simpa using this
    rw [← hcy, h2]

end Orbit

section CaseB

variable {F : Type*} [Field F] {G : Type*} [Group G] [MulAction G F] {m : ℕ}

theorem Hyp.exists_centralizer_smul_eq (hG : Hyp G F m) {P : Subgroup G} (hPΓ : P ≤ stab01 G F)
    {x y : F} (hx : x ∈ fixedSet P F) (hy : y ∈ fixedSet P F) (hx0 : x ≠ 0) (hy0 : y ≠ 0) :
    ∃ c ∈ centralizer (P : Set G), c • x = y := by
  have := hG.faithful
  obtain ⟨k, hk, hkx⟩ := exists_mulSubgroup hG (Units.mk0 (y / x) (div_ne_zero hy0 hx0))
  refine ⟨k, ?_, by rw [hkx, Units.val_mk0, div_mul_cancel₀ y hx0]⟩
  rw [mem_centralizer_iff]
  intro g hg
  have hgΓ := hPΓ hg
  have hσ : semilinPart F g (y / x) = y / x := by
    rw [map_div₀, ← smul_eq_of_mem_stab01 hG hgΓ, ← smul_eq_of_mem_stab01 hG hgΓ, hx g hg,
      hy g hg]
  apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
  intro t
  rw [mul_smul, mul_smul, hkx, smul_eq_of_mem_stab01 hG hgΓ, smul_eq_of_mem_stab01 hG hgΓ, hkx,
    map_mul, Units.val_mk0, hσ]

theorem Hyp.mem_centralizer_of_mem_normalizer [Finite F] (hG : Hyp G F m) {P : Subgroup G}
    (hPΓ : P ≤ stab01 G F) {n : G} (hn : n ∈ normalizer (P : Set G)) (hn0 : n • (0 : F) = 0) :
    n ∈ centralizer (P : Set G) := by
  obtain ⟨k, hk, γ, hγ, rfl⟩ := exists_mul_stab01 hG (show n ∈ stabilizer G (0 : F) from hn0)
  have hγP : γ ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    exact stab01_comm hG (hPΓ hx) hγ
  have hkN : k ∈ normalizer (P : Set G) := by
    have : k = (k * γ) * γ⁻¹ := by group
    rw [this]
    exact mul_mem hn ((centralizer_le_normalizer _) (inv_mem hγP))
  have hkP : k ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro x hx
    have h1 : k * x * k⁻¹ * x⁻¹ ∈ stab01 G F ⊓ mulSubgroup G F := by
      refine Subgroup.mem_inf.mpr ⟨(stab01 G F).mul_mem (hPΓ ((mem_normalizer_iff.mp hkN x).mp hx))
        ((stab01 G F).inv_mem (hPΓ hx)), ?_⟩
      have : k * x * k⁻¹ * x⁻¹ = k * (x * k⁻¹ * x⁻¹) := by group
      rw [this]
      exact mul_mem hk (conj_mem_mulSubgroup hG (stab01_le_stabilizer (hPΓ hx))
        (inv_mem hk))
    rw [stab01_inf_mulSubgroup hG, mem_bot] at h1
    have : k * x = x * k := by
      calc k * x = k * x * k⁻¹ * x⁻¹ * (x * k) := by group
        _ = x * k := by rw [h1, one_mul]
    exact this.symm
  exact mul_mem hkP hγP


theorem CE.endHyp [Finite G] [Finite F] (hC : CE G F m) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpΓ : p ∣ Nat.card (stab01 G F)) :
    m = p ∧ ∃ P : Subgroup G, EndHyp G F p 0 (mulSubgroup G F) P := by
  have hG := hC.toHyp
  have := hC.faithful
  have hfact : Fact p.Prime := ⟨hp⟩
  have hpK := hC.not_dvd_card_mulSubgroup hp hp2 hpΓ
  have := isCyclic_stab01 hG
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := stab01 G F)
  have hord₀ : orderOf g₀ = Nat.card (stab01 G F) := orderOf_eq_card_of_forall_mem_zpowers hg₀
  obtain ⟨a, n', hn', hcardΓ⟩ := Nat.exists_eq_pow_mul_and_not_dvd
    (Nat.card_pos (α := stab01 G F)).ne' p hp.ne_one
  have ha : a ≠ 0 := by
    rintro rfl
    rw [pow_zero, one_mul] at hcardΓ
    exact hn' (hcardΓ ▸ hpΓ)
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hcardΓ
    exact (Nat.card_pos (α := stab01 G F)).ne' hcardΓ
  set r : G := ((g₀ : stab01 G F) : G) ^ n' with hr
  have hrΓ : r ∈ stab01 G F := (stab01 G F).pow_mem g₀.2 n'
  have hrord : orderOf r = p ^ (b + 1) := by
    have h1 : orderOf ((g₀ : stab01 G F) : G) = p ^ (b + 1) * n' := by
      rw [Subgroup.orderOf_coe, hord₀, hcardΓ]
    rw [hr, orderOf_pow_of_dvd hn'0 (by rw [h1]; exact dvd_mul_left _ _), h1,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hn'0)]
  have hRcard : Nat.card (zpowers r) = p ^ (b + 1) := by rw [Nat.card_zpowers, hrord]
  have hRp : IsPGroup p (zpowers r) := IsPGroup.of_card hRcard
  have hRidx : ¬ p ∣ (zpowers r).index := by
    have h1 := (zpowers r).card_mul_index
    rw [hRcard, hG.card_group, hG.card_stabilizer, hcardΓ] at h1
    have h2 : (zpowers r).index = 2 ^ m * ((2 ^ m - 1) * n') := by
      apply Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos (b + 1))
      rw [h1]
      ring
    rw [h2]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp).mp hdvd with h3 | h3
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h3))
    · rcases (Nat.Prime.dvd_mul hp).mp h3 with h4 | h4
      · exact hpK (by rw [card_mulSubgroup hG]; exact h4)
      · exact hn' h4
  set RS := hRp.toSylow hRidx with hRSdef
  have hRS : (RS : Subgroup G) = zpowers r := IsPGroup.toSylow_coe _ _
  set P : Subgroup G := zpowers (r ^ p ^ b) with hPdef
  have hPcard : Nat.card P = p := by
    rw [hPdef, Nat.card_zpowers, orderOf_pow_of_dvd (pow_ne_zero b hp.ne_zero)
      (by rw [hrord]; exact pow_dvd_pow p (Nat.le_succ b)), hrord, pow_succ,
      Nat.mul_div_cancel_left _ (pow_pos hp.pos b)]
  have hPΓ : P ≤ stab01 G F := (zpowers_le (H := stab01 G F)).mpr ((stab01 G F).pow_mem hrΓ _)
  have hNC : ¬ normalizer (P : Set G) ≤ centralizer (P : Set G) := by
    intro hle
    obtain ⟨N, hNn, -, hNidx⟩ := exists_normal_pComplement_of_cyclic RS hRS hrord hle
    have hKN : mulSubgroup G F ≤ N := by
      intro k hk
      have h1 : k ^ Nat.card (mulSubgroup G F) ∈ N := by
        have : k ^ Nat.card (mulSubgroup G F) = 1 :=
          orderOf_dvd_iff_pow_eq_one.mp (Subgroup.orderOf_dvd_natCard _ hk)
        rw [this]
        exact one_mem N
      have hcop : Nat.Coprime (Nat.card (mulSubgroup G F)) N.index := by
        rw [hNidx, hRS, Nat.card_zpowers, hrord]
        exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpK).symm
      exact mem_of_pow_mem_of_coprime h1 (Subgroup.pow_index_mem N k) hcop
    have htop : N = ⊤ := top_le_iff.mp (hC.normalClosure_eq_top ▸ normalClosure_le_normal hKN)
    rw [htop, Subgroup.index_top, hRS, Nat.card_zpowers, hrord] at hNidx
    have : 1 < p ^ (b + 1) := Nat.one_lt_pow (Nat.succ_ne_zero b) hp.one_lt
    omega
  have h0P : (0 : F) ∈ fixedSet P F := fun g hg => (hPΓ hg).1
  have h1P : (1 : F) ∈ fixedSet P F := fun g hg => (hPΓ hg).2
  obtain ⟨hCfix, n, hnN, -, hfix⟩ := orbit_argument h0P
    (fun x hx y hy hx0 hy0 => hG.exists_centralizer_smul_eq hPΓ hx hy hx0 hy0)
    (fun n hn hn0 => hG.mem_centralizer_of_mem_normalizer hPΓ hn hn0) hNC
  have hn1 : n • (0 : F) = 1 := ((hfix 1 h1P).resolve_left one_ne_zero).symm
  have hfix01 : ∀ y ∈ fixedSet P F, y = 0 ∨ y = 1 := fun y hy => by
    rcases hfix y hy with h | h
    · exact Or.inl h
    · exact Or.inr (h.trans hn1)
  set A : Subgroup (F ≃+* F) := (P.subgroupOf (stab01 G F)).map (rhoStab01 hG) with hA
  have hAcard : Nat.card A = p := by
    rw [hA, Subgroup.card_map_of_injective (rhoStab01_injective hG),
      Nat.card_congr (subgroupOfEquivOfLe hPΓ).toEquiv, hPcard]
  have hset : {x : F | ∀ σ ∈ A, σ x = x} = {0, 1} := by
    ext x
    rw [Set.mem_insert_iff, Set.mem_singleton_iff]
    change (∀ σ ∈ A, σ x = x) ↔ x = 0 ∨ x = 1
    constructor
    · intro hx
      apply hfix01
      intro g hg
      have := hx (rhoStab01 hG ⟨g, hPΓ hg⟩) ⟨⟨g, hPΓ hg⟩, mem_subgroupOf.mpr hg, rfl⟩
      rw [rhoStab01_apply] at this
      rw [smul_eq_of_mem_stab01 hG (hPΓ hg)]
      exact this
    · rintro (rfl | rfl) σ _
      · exact map_zero σ
      · exact map_one σ
  have hAfix : Nat.card {x : F // ∀ σ ∈ A, σ x = x} = 2 := by
    rw [show Nat.card {x : F // ∀ σ ∈ A, σ x = x} = ({x : F | ∀ σ ∈ A, σ x = x} : Set F).ncard
      from Nat.card_coe_set_eq _, hset, Set.ncard_pair zero_ne_one]
  have hmp : m = p := by
    have h1 := card_fixed_pow A
    rw [hAfix, hAcard, hG.card] at h1
    exact (Nat.pow_right_injective le_rfl h1).symm
  have hΓP : stab01 G F = P := by
    refine (Subgroup.eq_of_le_of_card_ge hPΓ ?_).symm
    rw [hPcard, ← hmp]
    exact card_stab01_le hG
  have hH : Nat.card (stabilizer G (0 : F)) = (2 ^ p - 1) * p := by
    rw [hG.card_stabilizer, hΓP, hPcard, hmp]
  have hPab : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    stab01_comm hG (hPΓ hx) (hPΓ hy)
  have hCH : ∀ c ∈ centralizer (P : Set G), c • (0 : F) = 0 → c ∈ P := by
    intro c hc hc0
    obtain ⟨k, hk, γ, hγ, rfl⟩ := exists_mul_stab01 hG (show c ∈ stabilizer G (0 : F) from hc0)
    have hγP : γ ∈ P := hΓP ▸ hγ
    have hγC : γ ∈ centralizer (P : Set G) := mem_centralizer_iff.mpr fun x hx => hPab x hx γ hγP
    have hkC : k ∈ centralizer (P : Set G) := by
      have : k = (k * γ) * γ⁻¹ := by group
      rw [this]
      exact mul_mem hc (inv_mem hγC)
    have hk1 : k • (1 : F) ∈ fixedSet P F := by
      intro g hg
      have hgk : g * k = k * g := (mem_centralizer_iff.mp hkC) g hg
      rw [smul_smul, hgk, mul_smul, show g • (1 : F) = 1 from (hPΓ hg).2]
    have hk1' : k • (1 : F) = 1 := (hfix01 _ hk1).resolve_left
      (smul_one_ne_zero (mulSubgroup_le_stabilizer hk : k • (0 : F) = 0))
    have hk_one : k = 1 := by
      apply FaithfulSMul.eq_of_smul_eq_smul (α := F)
      intro x
      rw [smul_eq_of_mem_mulSubgroup hk, hk1', one_mul, one_smul]
    rw [hk_one, one_mul]
    exact hγP
  have hCP : centralizer (P : Set G) ≤ P := fun c hc => hCH c hc (hCfix c hc)
  have hNcard : Nat.card (normalizer (P : Set G)) = 2 * p := by
    have hstabN : stabilizer (normalizer (P : Set G)) (0 : F) =
        P.subgroupOf (normalizer (P : Set G)) := by
      ext ⟨x, hx⟩
      rw [mem_stabilizer_iff, mem_subgroupOf]
      constructor
      · intro hx0
        exact hCH x (hG.mem_centralizer_of_mem_normalizer hPΓ hx hx0) hx0
      · intro hxP
        exact (hPΓ hxP).1
    have horbit : orbit (normalizer (P : Set G)) (0 : F) = {0, 1} := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact hfix01 _ (smul_mem_fixedSet x.2 h0P)
      · rintro (rfl | rfl)
        · exact ⟨1, one_smul _ _⟩
        · exact ⟨⟨n, hnN⟩, hn1⟩
    have h1 := (stabilizer (normalizer (P : Set G)) (0 : F)).card_mul_index
    rw [index_stabilizer, horbit, Set.ncard_pair zero_ne_one, hstabN,
      Nat.card_congr (subgroupOfEquivOfLe (le_normalizer : P ≤ normalizer (P : Set G))).toEquiv,
      hPcard] at h1
    rw [← h1, mul_comm]
  refine ⟨hmp, P, ?_⟩
  exact
    { prime := hp
      three_le := by have := hp.two_le; omega
      faithful := hC.faithful
      twoTrans := hC.twoTrans
      card := by rw [hG.card, hmp]
      K_le := mulSubgroup_le_stabilizer
      K_normal := fun h hh k hk => conj_mem_mulSubgroup hG hh hk
      card_K := by rw [card_mulSubgroup hG, hmp]
      K_fix := fun k hk hk1 x hx => eq_zero_of_mem_mulSubgroup hG hk hk1 hx
      card_stab := hH
      P_le := hPΓ.trans stab01_le_stabilizer
      card_P := hPcard
      card_normalizer := hNcard
      centralizer_le := hCP
      solvable := hC.solvable_eq_bot
      closure := hC.normalClosure_eq_top }

end CaseB

end CFSG.GH74.Uniqueness.Hering
