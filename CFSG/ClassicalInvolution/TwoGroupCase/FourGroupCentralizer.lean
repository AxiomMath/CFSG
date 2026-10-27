module

public import CFSG.CharacterTheory.Semidihedral.NormalForm

public section

namespace CFSG.ClassicalInvolution

universe u

structure FourCentralizer (S : Type u) [Group S] (r z : S) : Prop where
  two : IsPGroup 2 S
  r_sq : r * r = 1
  r_ne : r ≠ 1
  z_sq : z * z = 1
  z_ne : z ≠ 1
  r_ne_z : r ≠ z
  z_central : ∀ s : S, s * z = z * s
  cent : ∀ x : S, x * r = r * x ↔ (x = 1 ∨ x = r ∨ x = z ∨ x = r * z)

namespace FourCentralizer

variable {S : Type u} [Group S] {r z : S}

theorem rz_sq (h : FourCentralizer S r z) : (r * z) * (r * z) = 1 := by
  calc (r * z) * (r * z) = r * (z * r) * z := by group
    _ = r * (r * z) * z := by rw [← h.z_central r]
    _ = (r * r) * (z * z) := by group
    _ = 1 := by rw [h.r_sq, h.z_sq, one_mul]

theorem sq_eq_one_of_commute (h : FourCentralizer S r z) {x : S} (hx : x * r = r * x) :
    x * x = 1 := by
  rcases (h.cent x).mp hx with rfl | rfl | rfl | rfl
  · simp
  · exact h.r_sq
  · exact h.z_sq
  · exact h.rz_sq

theorem orderOf_z (h : FourCentralizer S r z) : orderOf z = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact h.z_sq) h.z_ne

section Basic

variable {G : Type u} [Group G]

theorem mem_zpowers_iff_of_mul_self_eq_one {z y : G} (hz : z * z = 1) (hz1 : z ≠ 1) :
    y ∈ Subgroup.zpowers z ↔ y = 1 ∨ y = z := by
  have hord : orderOf z = 2 := orderOf_eq_prime (by rw [pow_two]; exact hz) hz1
  constructor
  · intro hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have h := zpow_mod_orderOf z k
    rw [hord] at h
    rcases Int.emod_two_eq_zero_or_one k with h0 | h1
    · left
      rw [← h]
      simp [h0]
    · right
      rw [← h]
      simp [h1]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.mem_zpowers _

theorem normal_zpowers_of_central {z : G} (hz : ∀ s : G, s * z = z * s) :
    (Subgroup.zpowers z).Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hn
  have hc : Commute g (z ^ k) := Commute.zpow_right (hz g) k
  rw [show g * z ^ k * g⁻¹ = z ^ k from by rw [hc.eq]; group]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers z) k

theorem mk_eq_mk_iff_of_zpowers {z : G} [(Subgroup.zpowers z).Normal] (hz : z * z = 1)
    (hz1 : z ≠ 1) {x y : G} :
    (QuotientGroup.mk x : G ⧸ Subgroup.zpowers z) = QuotientGroup.mk y ↔ y = x ∨ y = x * z := by
  rw [QuotientGroup.eq, mem_zpowers_iff_of_mul_self_eq_one hz hz1]
  constructor
  · rintro (h1 | h1)
    · left; exact (inv_mul_eq_one.mp h1).symm
    · right; rw [← h1]; group
  · rintro (h1 | h1)
    · left; rw [h1]; group
    · right; rw [h1]; group

end Basic

section LemmaQ

variable {G : Type u} [Group G] [Finite G]

theorem exists_central_of_cover (hG : IsPGroup 2 G) (h8 : 8 ≤ Nat.card G) {ρ ω : G}
    (hρ1 : ρ ≠ 1) (hρ : ρ * ρ = 1) (hω : ω * ω = 1) (hωρ : ω * ρ = ρ * ω)
    (hcov : ∀ x : G, x * ρ = ρ * x → x = 1 ∨ x = ρ ∨ x = ω ∨ x = ω * ρ) :
    ∃ ζ : G, ζ * ζ = 1 ∧ ζ ≠ 1 ∧ ζ ≠ ρ ∧ (∀ s : G, s * ζ = ζ * s) ∧
      ∀ x : G, x * ρ = ρ * x ↔ (x = 1 ∨ x = ρ ∨ x = ζ ∨ x = ρ * ζ) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial G := by
    refine Finite.one_lt_card_iff_nontrivial.mp ?_
    have : 0 < Nat.card G := Nat.card_pos
    omega
  have := hG.center_nontrivial
  obtain ⟨⟨ζ₀, hζ₀c⟩, hζ₀⟩ := exists_ne (1 : Subgroup.center G)
  have hζ₀1 : ζ₀ ≠ 1 := fun h => hζ₀ (Subtype.ext h)
  have hζ₀cent : ∀ s : G, s * ζ₀ = ζ₀ * s := fun s => (Subgroup.mem_center_iff.mp hζ₀c s)
  have hρnc : ¬ ∀ s : G, s * ρ = ρ * s := by
    intro hall
    have hcard : Nat.card G ≤ 4 := by
      have hsub : (Set.univ : Set G) ⊆ ({1, ρ, ω, ω * ρ} : Finset G) := by
        intro x _
        simpa using hcov x (hall x)
      have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_univ] at this
      refine this.trans ?_
      rw [Set.ncard_coe_finset]
      exact Finset.card_le_four
    omega
  have hρζ : ζ₀ ≠ ρ := by
    rintro rfl
    exact hρnc hζ₀cent
  have hcases := hcov ζ₀ (hζ₀cent ρ).symm
  have hζ_cases : ζ₀ = ω ∨ ζ₀ = ω * ρ := by
    rcases hcases with h | h | h | h
    · exact absurd h hζ₀1
    · exact absurd h hρζ
    · exact Or.inl h
    · exact Or.inr h
  have hζ2 : ζ₀ * ζ₀ = 1 := by
    rcases hζ_cases with rfl | rfl
    · exact hω
    · calc (ω * ρ) * (ω * ρ) = (ω * ω) * (ρ * ρ) := by
            calc (ω * ρ) * (ω * ρ) = ω * (ρ * ω) * ρ := by group
              _ = ω * (ω * ρ) * ρ := by rw [hωρ]
              _ = (ω * ω) * (ρ * ρ) := by group
        _ = 1 := by rw [hω, hρ, one_mul]
  refine ⟨ζ₀, hζ2, hζ₀1, hρζ, hζ₀cent, fun x => ⟨fun hx => ?_, fun hx => ?_⟩⟩
  · rcases hcov x hx with h | h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · rcases hζ_cases with rfl | rfl
      · exact Or.inr (Or.inr (Or.inl h))
      ·
        right; right; right
        have e : ρ * (ω * ρ) = ω := by
          rw [hωρ, ← mul_assoc, hρ, one_mul]
        rw [h]
        exact e.symm
    · rcases hζ_cases with rfl | rfl
      ·
        right; right; right
        rw [h, hωρ]
      · exact Or.inr (Or.inr (Or.inl h))
  · rcases hx with rfl | rfl | rfl | rfl
    · simp
    · rfl
    · exact (hζ₀cent ρ).symm
    · rw [mul_assoc, ← hζ₀cent ρ]

end LemmaQ

section Quotient

variable {S : Type u} [Group S] [Finite S] {r z : S}

theorem exists_quotient (h : FourCentralizer S r z) [(Subgroup.zpowers z).Normal]
    (h8 : 8 ≤ Nat.card (S ⧸ Subgroup.zpowers z)) :
    ∃ z' : S ⧸ Subgroup.zpowers z,
      FourCentralizer (S ⧸ Subgroup.zpowers z) (QuotientGroup.mk r) z' := by
  classical
  set N := Subgroup.zpowers z with hN
  have hmem : ∀ y : S, y ∈ N ↔ y = 1 ∨ y = z := fun y =>
    mem_zpowers_iff_of_mul_self_eq_one h.z_sq h.z_ne
  have hπeq : ∀ x y : S, (QuotientGroup.mk x : S ⧸ N) = QuotientGroup.mk y ↔
      y = x ∨ y = x * z := by
    intro x y
    rw [QuotientGroup.eq, hmem]
    constructor
    · rintro (h1 | h1)
      · left; exact (inv_mul_eq_one.mp h1).symm
      · right; rw [← h1]; group
    · rintro (h1 | h1)
      · left; rw [h1]; group
      · right; rw [h1]; group
  have hzc := h.z_central
  have hzz := h.z_sq
  have hmk_z : (QuotientGroup.mk z : S ⧸ N) = 1 :=
    (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
  have hmk_rz : (QuotientGroup.mk (r * z) : S ⧸ N) = QuotientGroup.mk r := by
    rw [QuotientGroup.mk_mul, hmk_z, mul_one]
  have hr1 : (QuotientGroup.mk r : S ⧸ N) ≠ 1 := by
    intro h1
    have := (QuotientGroup.eq_one_iff r).mp h1
    rcases (hmem r).mp this with h2 | h2
    · exact h.r_ne h2
    · exact h.r_ne_z h2
  have hrr : (QuotientGroup.mk r : S ⧸ N) * QuotientGroup.mk r = 1 := by
    rw [← QuotientGroup.mk_mul, h.r_sq]; rfl
  have hcomm : ∀ x : S, (QuotientGroup.mk x : S ⧸ N) * QuotientGroup.mk r =
      QuotientGroup.mk r * QuotientGroup.mk x ↔ (r * x = x * r ∨ r * x = x * r * z) := by
    intro x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hπeq]
  have hcover : ∃ ω : S ⧸ N, ω * ω = 1 ∧ ω * QuotientGroup.mk r = QuotientGroup.mk r * ω ∧
      ∀ xb : S ⧸ N, xb * QuotientGroup.mk r = QuotientGroup.mk r * xb →
        xb = 1 ∨ xb = QuotientGroup.mk r ∨ xb = ω ∨ xb = ω * QuotientGroup.mk r := by
    by_cases hex : ∃ x : S, ¬ (x * r = r * x) ∧ r * x = x * r * z
    · obtain ⟨x₀, hx₀C, hx₀⟩ := hex
      have hx₀' : x₀ * r = r * x₀ * z := by
        calc x₀ * r = x₀ * r * z * z := by rw [mul_assoc, hzz, mul_one]
          _ = r * x₀ * z := by rw [← hx₀]
      have hsq_comm : (x₀ * x₀) * r = r * (x₀ * x₀) := by
        calc (x₀ * x₀) * r = x₀ * (x₀ * r) := mul_assoc _ _ _
          _ = x₀ * (r * x₀ * z) := by rw [hx₀']
          _ = (x₀ * r) * (x₀ * z) := by group
          _ = (r * x₀ * z) * (x₀ * z) := by rw [hx₀']
          _ = r * x₀ * (z * x₀) * z := by group
          _ = r * x₀ * (x₀ * z) * z := by rw [← hzc x₀]
          _ = r * (x₀ * x₀) * (z * z) := by group
          _ = r * (x₀ * x₀) := by rw [hzz, mul_one]
      have hsq : x₀ * x₀ = 1 ∨ x₀ * x₀ = z := by
        rcases (h.cent _).mp hsq_comm with h1 | h1 | h1 | h1
        · exact Or.inl h1
        · exfalso
          apply hx₀C
          calc x₀ * r = x₀ * (x₀ * x₀) := by rw [h1]
            _ = (x₀ * x₀) * x₀ := (mul_assoc _ _ _).symm
            _ = r * x₀ := by rw [h1]
        · exact Or.inr h1
        · exfalso
          apply hx₀C
          have h2 : x₀ * (r * z) = (r * z) * x₀ := by
            calc x₀ * (r * z) = x₀ * (x₀ * x₀) := by rw [h1]
              _ = (x₀ * x₀) * x₀ := (mul_assoc _ _ _).symm
              _ = (r * z) * x₀ := by rw [h1]
          have h3 : (x₀ * r) * z = (r * x₀) * z := by
            calc (x₀ * r) * z = x₀ * (r * z) := mul_assoc _ _ _
              _ = (r * z) * x₀ := h2
              _ = r * (z * x₀) := mul_assoc _ _ _
              _ = r * (x₀ * z) := by rw [hzc x₀]
              _ = (r * x₀) * z := (mul_assoc _ _ _).symm
          exact mul_right_cancel h3
      refine ⟨QuotientGroup.mk x₀, ?_, ?_, ?_⟩
      · rw [← QuotientGroup.mk_mul]
        rcases hsq with h1 | h1
        · rw [h1]; rfl
        · rw [h1]; exact hmk_z
      · exact (hcomm x₀).mpr (Or.inr hx₀)
      · intro xb hxb
        obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
        rcases (hcomm x).mp hxb with h1 | h1
        ·
          rcases (h.cent x).mp h1.symm with rfl | rfl | rfl | rfl
          · exact Or.inl rfl
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl hmk_z
          · exact Or.inr (Or.inl hmk_rz)
        · by_cases hxC : x * r = r * x
          · rcases (h.cent x).mp hxC with rfl | rfl | rfl | rfl
            · exact Or.inl rfl
            · exact Or.inr (Or.inl rfl)
            · exact Or.inl hmk_z
            · exact Or.inr (Or.inl hmk_rz)
          ·
            have hx' : x * r = r * x * z := by
              calc x * r = x * r * z * z := by rw [mul_assoc, hzz, mul_one]
                _ = r * x * z := by rw [← h1]
            have hc : (x₀⁻¹ * x) * r = r * (x₀⁻¹ * x) := by
              have e1 : x₀⁻¹ * r = r * z * x₀⁻¹ := by
                have : x₀⁻¹ * (r * x₀) = r * z := by
                  rw [hx₀]; group
                calc x₀⁻¹ * r = x₀⁻¹ * (r * x₀) * x₀⁻¹ := by group
                  _ = r * z * x₀⁻¹ := by rw [this]
              calc (x₀⁻¹ * x) * r = x₀⁻¹ * (x * r) := mul_assoc _ _ _
                _ = x₀⁻¹ * (r * x * z) := by rw [hx']
                _ = (x₀⁻¹ * r) * (x * z) := by group
                _ = (r * z * x₀⁻¹) * (x * z) := by rw [e1]
                _ = r * (z * (x₀⁻¹ * x) * z) := by group
                _ = r * ((x₀⁻¹ * x) * z * z) := by rw [← hzc (x₀⁻¹ * x)]
                _ = r * (x₀⁻¹ * x) := by rw [mul_assoc, hzz, mul_one]
            have hxx : x = x₀ * (x₀⁻¹ * x) := by group
            have : (QuotientGroup.mk x : S ⧸ N) =
                QuotientGroup.mk x₀ * QuotientGroup.mk (x₀⁻¹ * x) := by
              rw [← QuotientGroup.mk_mul, ← hxx]
            rw [this]
            rcases (h.cent _).mp hc with h2 | h2 | h2 | h2
            · rw [h2]; right; right; left; simp
            · rw [h2]; right; right; right; rfl
            · rw [h2, hmk_z]; right; right; left; simp
            · rw [h2, hmk_rz]; right; right; right; rfl
    · push Not at hex
      refine ⟨1, by simp, by simp, ?_⟩
      intro xb hxb
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective xb
      have hxC : x * r = r * x := by
        rcases (hcomm x).mp hxb with h1 | h1
        · exact h1.symm
        · by_contra hn
          exact hex x hn h1
      rcases (h.cent x).mp hxC with rfl | rfl | rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl hmk_z
      · exact Or.inr (Or.inl hmk_rz)
  obtain ⟨ω, hω, hωr, hcov⟩ := hcover
  have h2 : IsPGroup 2 (S ⧸ N) := h.two.to_quotient N
  obtain ⟨ζ, hζ2, hζ1, hζr, hζc, hζcent⟩ := exists_central_of_cover h2 h8 hr1 hrr hω hωr
    (fun x hx => hcov x hx)
  exact ⟨ζ, ⟨h2, hrr, hr1, hζ2, hζ1, hζr.symm, hζc, hζcent⟩⟩

end Quotient

section Induction

theorem exists_mul_self_ne_one {S : Type u} [Group S] [Finite S] {r z : S}
    (h : FourCentralizer S r z) (hcard : 4 < Nat.card S) : ∃ a : S, a * a ≠ 1 := by
  classical
  by_contra hno
  push Not at hno
  have hall : ∀ x : S, x * r = r * x := by
    intro x
    have hx : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hno x)
    have hr : r⁻¹ = r := inv_eq_of_mul_eq_one_right (hno r)
    have hxr : (x * r)⁻¹ = x * r := inv_eq_of_mul_eq_one_right (hno (x * r))
    rw [← hxr, mul_inv_rev, hr, hx]
  have hsub : (Set.univ : Set S) ⊆ ({1, r, z, r * z} : Finset S) := by
    intro x _
    simpa using (h.cent x).mp (hall x)
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_univ, Set.ncard_coe_finset] at this
  have h4 := Finset.card_le_four (a := (1 : S)) (b := r) (c := z) (d := r * z)
  omega

theorem exists_cyclic_index_two :
    ∀ (m : ℕ), 3 ≤ m → ∀ (S : Type u) [Group S] [Finite S] (r z : S), FourCentralizer S r z →
      Nat.card S = 2 ^ m → ∃ a : S, orderOf a = 2 ^ (m - 1) ∧ ∀ k : ℤ, a ^ k ≠ r := by
  intro m hm
  induction m, hm using Nat.le_induction with
  | base =>
    intro S _ _ r z h hcard
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨a, ha⟩ := h.exists_mul_self_ne_one (by rw [hcard]; norm_num)
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp h.two a
    have hk2 : 2 ≤ k := by
      by_contra hlt
      push Not at hlt
      apply ha
      rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hk]
      calc 2 ^ k ∣ 2 ^ 1 := pow_dvd_pow 2 (by omega)
        _ = 2 := by norm_num
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 2 := ⟨k - 2, by omega⟩
    have hb : orderOf (a ^ (2 ^ k')) = 4 := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [hk]; exact pow_dvd_pow 2 (by omega)), hk,
        pow_add]
      rw [Nat.mul_div_cancel_left _ (by positivity)]
      norm_num
    refine ⟨a ^ (2 ^ k'), by rw [hb]; norm_num, fun k hk' => ?_⟩
    have hcomm : (a ^ (2 ^ k')) * r = r * (a ^ (2 ^ k')) := by
      rw [← hk']
      exact ((Commute.refl _).zpow_right k).eq
    have hsq := h.sq_eq_one_of_commute hcomm
    have : orderOf (a ^ (2 ^ k')) ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hsq
    rw [hb] at this
    omega
  | succ m hm ih =>
    intro S _ _ r z h hcard
    classical
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hnorm : (Subgroup.zpowers z).Normal := normal_zpowers_of_central h.z_central
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
    have hcardN : Nat.card (Subgroup.zpowers z) = 2 := by
      rw [Nat.card_zpowers, h.orderOf_z]
    have hQcard : Nat.card (S ⧸ Subgroup.zpowers z) = 2 ^ (m' + 3) := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.zpowers z)
      rw [hcard, hcardN, pow_succ] at h1
      exact (Nat.eq_of_mul_eq_mul_right (by norm_num) h1).symm
    have h8 : 8 ≤ Nat.card (S ⧸ Subgroup.zpowers z) := by
      rw [hQcard]
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (m' + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    obtain ⟨z', hz'⟩ := h.exists_quotient h8
    obtain ⟨ab, hāord, hā⟩ := ih (S ⧸ Subgroup.zpowers z) (QuotientGroup.mk r) z' hz' hQcard
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective ab
    have hāord' : orderOf (QuotientGroup.mk a : S ⧸ Subgroup.zpowers z) = 2 ^ (m' + 2) := by
      rw [hāord]; rfl
    have hdvd1 : 2 ^ (m' + 2) ∣ orderOf a := by
      rw [← hāord']
      exact orderOf_map_dvd (QuotientGroup.mk' (Subgroup.zpowers z)) a
    have hpowz : a ^ (2 ^ (m' + 2)) ∈ Subgroup.zpowers z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, ← hāord']
      exact pow_orderOf_eq_one _
    have hpow2 : a ^ (2 ^ (m' + 3)) = 1 := by
      rw [pow_succ 2 (m' + 2), pow_mul]
      rcases (mem_zpowers_iff_of_mul_self_eq_one h.z_sq h.z_ne).mp hpowz with h1 | h1
      · rw [h1, one_pow]
      · rw [h1, pow_two]; exact h.z_sq
    obtain ⟨j, hjle, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
      (orderOf_dvd_of_pow_eq_one hpow2)
    have hjge : m' + 2 ≤ j := by
      rw [hj] at hdvd1
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd1
    have hmk_pow : ∀ k : ℤ, a ^ k ≠ r := fun k hk => hā k (by rw [← QuotientGroup.mk_zpow, hk])
    have hord : orderOf a = 2 ^ (m' + 3) := by
      by_contra hne
      have hj2 : j = m' + 2 := by
        rcases Nat.lt_or_ge j (m' + 3) with hlt | hge
        · omega
        · exfalso; apply hne; rw [hj]; congr 1; omega
      rw [hj2] at hj
      have hq2 : 2 ^ (m' + 2) = 2 ^ (m' + 1) * 2 := pow_succ 2 (m' + 1)
      set n : ℕ := 2 ^ (m' + 1) with hn
      have hw_ord : orderOf (a ^ n) = 2 := by
        rw [orderOf_pow_of_dvd (by positivity) (by rw [hj]; exact pow_dvd_pow 2 (by omega)), hj,
          hq2]
        exact Nat.mul_div_cancel_left _ (by positivity)
      set w := a ^ n with hw
      have hw2 : w * w = 1 := by rw [← pow_two, ← orderOf_dvd_iff_pow_eq_one, hw_ord]
      have hw1 : w ≠ 1 := by
        intro h1
        rw [h1, orderOf_one] at hw_ord
        omega
      have hindex : (Subgroup.zpowers (QuotientGroup.mk a : S ⧸ Subgroup.zpowers z)).index = 2 := by
        have h1 := Subgroup.card_mul_index
          (Subgroup.zpowers (QuotientGroup.mk a : S ⧸ Subgroup.zpowers z))
        rw [Nat.card_zpowers, hāord', hQcard] at h1
        have e : 2 ^ (m' + 3) = 2 ^ (m' + 2) * 2 := pow_succ 2 (m' + 2)
        rw [e] at h1
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
      have hnorm' := Subgroup.normal_of_index_eq_two hindex
      have hconj : (QuotientGroup.mk r : S ⧸ Subgroup.zpowers z) * QuotientGroup.mk a *
          (QuotientGroup.mk r)⁻¹ ∈
          Subgroup.zpowers (QuotientGroup.mk a : S ⧸ Subgroup.zpowers z) :=
        hnorm'.conj_mem _ (Subgroup.mem_zpowers _) _
      obtain ⟨j', hj'⟩ := Subgroup.mem_zpowers_iff.mp hconj
      have hmk : (QuotientGroup.mk (a ^ j') : S ⧸ Subgroup.zpowers z) =
          QuotientGroup.mk (r * a * r⁻¹) := by
        rw [QuotientGroup.mk_zpow, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
          QuotientGroup.mk_inv]
        exact hj'
      have hy := (mk_eq_mk_iff_of_zpowers h.z_sq h.z_ne).mp hmk
      have hzn : z ^ n = 1 := by
        rw [hn, pow_succ', pow_mul, pow_two, h.z_sq, one_pow]
      have hpow_j : (a ^ j') ^ n = w ^ j' := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      have hwconj : r * w * r⁻¹ = w ^ j' := by
        have e1 : r * w * r⁻¹ = (r * a * r⁻¹) ^ n := by rw [hw, conj_pow]
        rw [e1]
        rcases hy with h1 | h1
        · rw [h1, hpow_j]
        · rw [h1, Commute.mul_pow (h.z_central _), hzn, mul_one, hpow_j]
      have hwj : w ^ j' = w := by
        have hmem : w ^ j' ∈ Subgroup.zpowers w :=
          Subgroup.zpow_mem _ (Subgroup.mem_zpowers w) j'
        rcases (mem_zpowers_iff_of_mul_self_eq_one hw2 hw1).mp hmem with h1 | h1
        · exfalso
          apply hw1
          have h2 : r * w * r⁻¹ = 1 := by rw [hwconj, h1]
          have h3 := mul_inv_eq_one.mp h2
          exact mul_left_cancel (a := r) (by rw [h3, mul_one])
        · exact h1
      have hwr : w * r = r * w := by
        have h1 : r * w * r⁻¹ = w := by rw [hwconj, hwj]
        exact (mul_inv_eq_iff_eq_mul.mp h1).symm
      have hmkw : (QuotientGroup.mk w : S ⧸ Subgroup.zpowers z) = (QuotientGroup.mk a) ^ n := by
        rw [hw, QuotientGroup.mk_pow]
      have hmkz : (QuotientGroup.mk z : S ⧸ Subgroup.zpowers z) = 1 :=
        (QuotientGroup.eq_one_iff z).mpr (Subgroup.mem_zpowers z)
      rcases (h.cent w).mp hwr with h1 | h1 | h1 | h1
      · exact hw1 h1
      · exact hā (n : ℤ) (by rw [zpow_natCast, ← hmkw, h1])
      · have h2 : (QuotientGroup.mk a : S ⧸ Subgroup.zpowers z) ^ n = 1 := by
          rw [← hmkw, h1]; exact hmkz
        have hdv := orderOf_dvd_of_pow_eq_one h2
        rw [hāord'] at hdv
        have h3 := Nat.le_of_dvd (by positivity) hdv
        have h4 : 2 ^ (m' + 1) < 2 ^ (m' + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
        omega
      · exact hā (n : ℤ) (by
          rw [zpow_natCast, ← hmkw, h1, QuotientGroup.mk_mul, hmkz, mul_one])
    exact ⟨a, by rw [hord]; rfl, hmk_pow⟩

end Induction

section Structure

variable {S : Type u} [Group S] [Finite S] {r z : S}

omit [Finite S] in
theorem not_forall_commute (h : FourCentralizer S r z) (hcard : 4 < Nat.card S) :
    ¬ ∀ x : S, x * r = r * x := by
  classical
  intro hall
  have hsub : (Set.univ : Set S) ⊆ ({1, r, z, r * z} : Finset S) := by
    intro x _
    simpa using (h.cent x).mp (hall x)
  have := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
  rw [Set.ncard_univ, Set.ncard_coe_finset] at this
  have h4 := Finset.card_le_four (a := (1 : S)) (b := r) (c := z) (d := r * z)
  omega

omit [Finite S] in
theorem eq_one_or_eq_of_mul_self_eq_one_of_mem_zpowers {a y : S} {m' : ℕ}
    (ha : orderOf a = 2 ^ (m' + 1)) (hy : y ∈ Subgroup.zpowers a)
    (hy2 : y * y = 1) : y = 1 ∨ y = a ^ (2 ^ m') := by
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have h1 : a ^ (2 * i) = 1 := by rw [two_mul, zpow_add]; exact hy2
  have h2 : ((orderOf a : ℕ) : ℤ) ∣ 2 * i := orderOf_dvd_iff_zpow_eq_one.mpr h1
  rw [ha] at h2
  have h3 : ((2 ^ m' : ℕ) : ℤ) ∣ i := by
    have : ((2 ^ (m' + 1) : ℕ) : ℤ) = 2 * ((2 ^ m' : ℕ) : ℤ) := by
      push_cast; rw [pow_succ]; ring
    rw [this] at h2
    exact Int.dvd_of_mul_dvd_mul_left (by norm_num) h2
  obtain ⟨t, rfl⟩ := h3
  have e : a ^ (((2 ^ m' : ℕ) : ℤ) * t) = (a ^ (2 ^ m')) ^ t := by
    rw [zpow_mul, zpow_natCast]
  rw [e]
  have hu2 : (a ^ (2 ^ m')) * (a ^ (2 ^ m')) = 1 := by
    rw [← pow_add, ← two_mul, ← pow_succ']
    rw [← ha]
    exact pow_orderOf_eq_one a
  by_cases hu1 : a ^ (2 ^ m') = 1
  · left; rw [hu1, one_zpow]
  · have hmem : (a ^ (2 ^ m')) ^ t ∈ Subgroup.zpowers (a ^ (2 ^ m')) :=
      Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) t
    exact (mem_zpowers_iff_of_mul_self_eq_one hu2 hu1).mp hmem

omit [Finite S] in
theorem cyclic_structure (h : FourCentralizer S r z) {m' : ℕ}
    (hcard : Nat.card S = 2 ^ (m' + 3)) {a : S} (ha : orderOf a = 2 ^ (m' + 2))
    (hr : ∀ k : ℤ, a ^ k ≠ r) :
    z = a ^ (2 ^ (m' + 1)) ∧
      (r * a * r = a⁻¹ ∨ (1 ≤ m' ∧ r * a * r = a ^ (2 ^ (m' + 1) - 1))) ∧
      ∀ s : S, s ∈ Subgroup.zpowers a ∨ s * r ∈ Subgroup.zpowers a := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Subgroup.zpowers a with hH
  have hrH : r ∉ H := fun hmem => by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    exact hr k hk
  have hrinv : r⁻¹ = r := inv_eq_of_mul_eq_one_right h.r_sq
  have hHcard : Nat.card H = 2 ^ (m' + 2) := by rw [hH, Nat.card_zpowers, ha]
  have hindex : H.index = 2 := by
    have h1 := Subgroup.card_mul_index H
    have e : 2 ^ (m' + 3) = 2 ^ (m' + 2) * 2 := pow_succ 2 (m' + 2)
    rw [hHcard, hcard, e] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  have hHn : H.Normal := Subgroup.normal_of_index_eq_two hindex
  have hcoset : ∀ s : S, s ∈ H ∨ s * r ∈ H := by
    obtain ⟨g, hg⟩ := Subgroup.index_eq_two_iff.mp hindex
    intro s
    by_cases hs : s ∈ H
    · exact Or.inl hs
    · right
      have hrg : r * g ∈ H := by
        rcases hg r with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd h1 hrH
      have hsg : s * g ∈ H := by
        rcases hg s with ⟨h1, -⟩ | ⟨h1, -⟩
        · exact h1
        · exact absurd h1 hs
      have : s * r⁻¹ ∈ H := by
        have := H.mul_mem hsg (H.inv_mem hrg)
        simpa [mul_assoc] using this
      rwa [hrinv] at this
  have hrmem : ∀ x ∈ H, r * x * r ∈ H := fun x hx => by
    have := hHn.conj_mem x hx r
    rwa [hrinv] at this
  have haH : a ∈ H := Subgroup.mem_zpowers a
  set u := a ^ (2 ^ (m' + 1)) with hu
  have huH : u ∈ H := H.pow_mem haH _
  have hu2 : u * u = 1 := by
    rw [hu, ← pow_add, ← two_mul, ← pow_succ']
    have : 2 ^ (m' + 1 + 1) = orderOf a := by rw [ha]
    rw [this]
    exact pow_orderOf_eq_one a
  have hu1 : u ≠ 1 := by
    intro h1
    have h2 : orderOf a ∣ 2 ^ (m' + 1) := orderOf_dvd_of_pow_eq_one h1
    rw [ha] at h2
    have := Nat.le_of_dvd (by positivity) h2
    have h3 : 2 ^ (m' + 1) < 2 ^ (m' + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  have hru : r * u * r = u := by
    have hmem : r * u * r ∈ H := hrmem u huH
    have hsq : (r * u * r) * (r * u * r) = 1 := by
      calc (r * u * r) * (r * u * r) = r * (u * (r * r) * u) * r := by group
        _ = r * (u * u) * r := by rw [h.r_sq, mul_one]
        _ = 1 := by rw [hu2, mul_one, h.r_sq]
    rcases eq_one_or_eq_of_mul_self_eq_one_of_mem_zpowers (m' := m' + 1) ha hmem hsq with h1 | h1
    · exfalso
      apply hu1
      have h2 : r * u * r = r * 1 * r := by rw [h1]; simp [h.r_sq]
      exact mul_left_cancel (mul_right_cancel h2)
    · exact h1
  have hur : u * r = r * u := by
    calc u * r = (r * u * r) * r := by rw [hru]
      _ = r * u * (r * r) := by group
      _ = r * u := by rw [h.r_sq, mul_one]
  have hcomm_H : ∀ x ∈ H, x * u = u * x := fun x hx => by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((Commute.zpow_left (Commute.pow_right (Commute.refl a) (2 ^ (m' + 1))) k)).eq
  have hucentral : ∀ s : S, s * u = u * s := by
    intro s
    rcases hcoset s with hs | hs
    · exact hcomm_H s hs
    · have h1 : Commute u (s * r) := (hcomm_H (s * r) hs).symm
      have h2 : Commute u r := hur
      have h3 := h1.mul_right h2
      rw [mul_assoc, h.r_sq, mul_one] at h3
      exact h3.eq.symm
  have hcard4 : 4 < Nat.card S := by
    rw [hcard]
    calc 4 < 2 ^ 3 := by norm_num
      _ ≤ 2 ^ (m' + 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hzu : z = u := by
    rcases (h.cent u).mp hur with h1 | h1 | h1 | h1
    · exact absurd h1 hu1
    · exact absurd (by rw [zpow_natCast]; exact h1) (hr ((2 ^ (m' + 1) : ℕ) : ℤ))
    · exact h1.symm
    · exfalso
      apply h.not_forall_commute hcard4
      have hrz : r = u * z := by
        calc r = (r * z) * z := by rw [mul_assoc, h.z_sq, mul_one]
          _ = u * z := by rw [← h1]
      intro x
      rw [hrz]
      exact (Commute.mul_right (hucentral x : Commute x u) (h.z_central x : Commute x z)).eq
  refine ⟨hzu, ?_, hcoset⟩
  have hbH : r * a * r ∈ H := hrmem a haH
  have hba : (r * a * r) * a = a * (r * a * r) := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hbH
    rw [← hk]
    exact ((Commute.zpow_left (Commute.refl a) k)).eq
  have hcH : (r * a * r) * a ∈ H := H.mul_mem hbH haH
  have hcr : ((r * a * r) * a) * r = r * ((r * a * r) * a) := by
    calc ((r * a * r) * a) * r = (a * (r * a * r)) * r := by rw [hba]
      _ = a * r * a * (r * r) := by group
      _ = a * r * a := by rw [h.r_sq, mul_one]
      _ = (r * r) * a * r * a := by rw [h.r_sq, one_mul]
      _ = r * ((r * a * r) * a) := by group
  rcases (h.cent _).mp hcr with h1 | h1 | h1 | h1
  · left
    exact eq_inv_of_mul_eq_one_left h1
  · exact absurd (h1 ▸ hcH) hrH
  · right
    have hb : r * a * r = a ^ (2 ^ (m' + 1) - 1) := by
      rw [pow_sub a (Nat.one_le_two_pow), pow_one, ← hu, ← hzu, ← h1]
      group
    refine ⟨?_, hb⟩
    by_contra hm0
    have hm0' : m' = 0 := by omega
    subst hm0'
    have hcomm : a * r = r * a := by
      have h2 : r * a * r = a := by rw [hb]; simp
      calc a * r = (r * a * r) * r := by rw [h2]
        _ = r * a * (r * r) := by group
        _ = r * a := by rw [h.r_sq, mul_one]
    have := h.sq_eq_one_of_commute hcomm
    have h3 : orderOf a ∣ 2 := by rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact this
    rw [ha] at h3
    have := Nat.le_of_dvd (by norm_num) h3
    norm_num at this
  · exfalso
    have : r = ((r * z) * z) := by rw [mul_assoc, h.z_sq, mul_one]
    apply hrH
    rw [this, ← h1, hzu]
    exact H.mul_mem hcH huH

end Structure

section Dihedral

variable {S : Type u} [Group S]

@[expose] def zmodPow (a : S) {N : ℕ} (i : ZMod N) : S := a ^ i.val

theorem zmodPow_add {a : S} {N : ℕ} [NeZero N] (ha : a ^ N = 1) (i j : ZMod N) :
    zmodPow a (i + j) = zmodPow a i * zmodPow a j := by
  unfold zmodPow
  rw [ZMod.val_add, ← pow_add, ← pow_eq_pow_mod _ ha]

theorem zmodPow_zero (a : S) {N : ℕ} [NeZero N] : zmodPow a (0 : ZMod N) = 1 := by
  simp [zmodPow]

theorem zmodPow_neg {a : S} {N : ℕ} [NeZero N] (ha : a ^ N = 1) (i : ZMod N) :
    zmodPow a (-i) = (zmodPow a i)⁻¹ := by
  refine eq_inv_of_mul_eq_one_right ?_
  rw [← zmodPow_add ha, add_neg_cancel, zmodPow_zero]

@[expose] def dihedralMap (a b : S) (N : ℕ) : DihedralGroup N → S
  | .r i => zmodPow a i
  | .sr i => zmodPow a (-i) * b

theorem dihedralMap_mul {a b : S} {N : ℕ} [NeZero N] (ha : a ^ N = 1) (hb : b * b = 1)
    (hba : b * a * b = a⁻¹) (x y : DihedralGroup N) :
    dihedralMap a b N (x * y) = dihedralMap a b N x * dihedralMap a b N y := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have hconj : ∀ i : ZMod N, b * zmodPow a i = zmodPow a (-i) * b := by
    intro i
    have h1 : (b * a * b⁻¹) ^ i.val = b * a ^ i.val * b⁻¹ := conj_pow
    rw [hbinv, hba, inv_pow] at h1
    have h2 : zmodPow a (-i) = b * zmodPow a i * b := by
      rw [zmodPow_neg ha]; exact h1
    rw [h2, mul_assoc (b * zmodPow a i) b b, hb, mul_one]
  rcases x with i | i <;> rcases y with j | j
  · simp only [DihedralGroup.r_mul_r, dihedralMap]
    exact zmodPow_add ha i j
  · simp only [DihedralGroup.r_mul_sr, dihedralMap]
    calc zmodPow a (-(j - i)) * b = zmodPow a (i + -j) * b := by congr 2; ring
      _ = zmodPow a i * (zmodPow a (-j) * b) := by rw [zmodPow_add ha, mul_assoc]
  · simp only [DihedralGroup.sr_mul_r, dihedralMap]
    calc zmodPow a (-(i + j)) * b = zmodPow a (-i + -j) * b := by congr 2; ring
      _ = zmodPow a (-i) * (zmodPow a (-j) * b) := by rw [zmodPow_add ha, mul_assoc]
      _ = zmodPow a (-i) * (b * zmodPow a j) := by rw [hconj j]
      _ = zmodPow a (-i) * b * zmodPow a j := by rw [mul_assoc]
  · simp only [DihedralGroup.sr_mul_sr, dihedralMap]
    calc zmodPow a (j - i) = zmodPow a (-i + j) := by congr 1; ring
      _ = zmodPow a (-i) * zmodPow a j := zmodPow_add ha _ _
      _ = zmodPow a (-i) * zmodPow a j * (b * b) := by rw [hb, mul_one]
      _ = zmodPow a (-i) * (zmodPow a j * b) * b := by group
      _ = zmodPow a (-i) * (b * zmodPow a (-j)) * b := by
          rw [hconj (-j), neg_neg]
      _ = zmodPow a (-i) * b * (zmodPow a (-j) * b) := by group

@[expose] def dihedralHom (a b : S) (N : ℕ) [NeZero N] (ha : a ^ N = 1) (hb : b * b = 1)
    (hba : b * a * b = a⁻¹) : DihedralGroup N →* S where
  toFun := dihedralMap a b N
  map_one' := by
    rw [DihedralGroup.one_def]
    simp [dihedralMap, zmodPow_zero]
  map_mul' := dihedralMap_mul ha hb hba

theorem zmodPow_intCast {a : S} {N : ℕ} [NeZero N] (ha : orderOf a = N) (k : ℤ) :
    zmodPow a (k : ZMod N) = a ^ k := by
  unfold zmodPow
  have h1 : ((((k : ZMod N).val : ℕ) : ℤ)) = k % (N : ℤ) := ZMod.val_intCast k
  calc a ^ ((k : ZMod N).val) = a ^ ((((k : ZMod N).val : ℕ) : ℤ)) := (zpow_natCast _ _).symm
    _ = a ^ (k % (N : ℤ)) := by rw [h1]
    _ = a ^ k := by rw [← ha]; exact zpow_mod_orderOf a k

theorem nonempty_mulEquiv_dihedral [Finite S] {a b : S} {N : ℕ} [NeZero N] (ha : orderOf a = N)
    (hb : b * b = 1) (hba : b * a * b = a⁻¹)
    (hcover : ∀ s : S, s ∈ Subgroup.zpowers a ∨ s * b ∈ Subgroup.zpowers a)
    (hcard : Nat.card S = 2 * N) : Nonempty (DihedralGroup N ≃* S) := by
  have haN : a ^ N = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  let φ := dihedralHom a b N haN hb hba
  have hφr : ∀ i : ZMod N, φ (DihedralGroup.r i) = zmodPow a i := fun i => rfl
  have hφsr : ∀ i : ZMod N, φ (DihedralGroup.sr i) = zmodPow a (-i) * b := fun i => rfl
  have hsurj : Function.Surjective φ := by
    intro s
    rcases hcover s with hs | hs
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact ⟨DihedralGroup.r (k : ZMod N), by rw [hφr, zmodPow_intCast ha]⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      refine ⟨DihedralGroup.sr (-(k : ZMod N)), ?_⟩
      rw [hφsr, neg_neg, zmodPow_intCast ha, hk, mul_assoc, hb, mul_one]
  have hbij : Function.Bijective φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [DihedralGroup.nat_card, hcard]
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end Dihedral

section Semidihedral

open CFSG.Open

variable {S : Type u} [Group S]

theorem nonempty_mulEquiv_semidihedral [Finite S] {a b : S} {n : ℕ} (hn : 4 ≤ n)
    (ha : orderOf a = 2 ^ (n - 1)) (hb : b * b = 1) (hba : b * a * b = a ^ (2 ^ (n - 2) - 1))
    (hcover : ∀ s : S, s ∈ Subgroup.zpowers a ∨ s * b ∈ Subgroup.zpowers a)
    (hcard : Nat.card S = 2 ^ n) : Nonempty (SemidihedralGroup n ≃* S) := by
  have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  have haN : a ^ (2 ^ (n - 1)) = 1 := by rw [← ha]; exact pow_orderOf_eq_one a
  let φ : SemidihedralGroup n →* S := PresentedGroup.toGroup (f := ![a, b]) (by
    intro w hw
    simp only [semidihedralRels, Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl | rfl
    · simpa only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_zero] using haN
    · simp only [map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [pow_two]
      exact hb
    · simp only [map_mul, map_inv, map_pow, FreeGroup.lift_apply_of, Matrix.cons_val_one,
        Matrix.cons_val_zero]
      rw [hbinv, hba, mul_inv_cancel])
  have hφa : φ (PresentedGroup.of 0) = a := PresentedGroup.toGroup.of _
  have hφb : φ (PresentedGroup.of 1) = b := PresentedGroup.toGroup.of _
  have hsurj : Function.Surjective φ := by
    intro s
    rcases hcover s with hs | hs
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      exact ⟨(PresentedGroup.of 0 : SemidihedralGroup n) ^ k, by rw [map_zpow, hφa]⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hs
      refine ⟨(PresentedGroup.of 0 : SemidihedralGroup n) ^ k * PresentedGroup.of 1, ?_⟩
      rw [map_mul, map_zpow, hφa, hφb, hk, mul_assoc, hb, mul_one]
  have hcardSD : Nat.card (SemidihedralGroup n) = 2 ^ n := CFSG.Semidihedral.card n (by omega)
  have : Finite (SemidihedralGroup n) :=
    Nat.finite_of_card_ne_zero (by rw [hcardSD]; positivity)
  have hbij : Function.Bijective φ := by
    refine hsurj.bijective_of_nat_card_le ?_
    rw [hcardSD, hcard]
  exact ⟨MulEquiv.ofBijective φ hbij⟩

end Semidihedral

section Classification

variable {S : Type u} [Group S] [Finite S] {r z : S}

theorem classification (h : FourCentralizer S r z) :
    Nat.card S = 4 ∨ ∃ m' : ℕ, Nat.card S = 2 ^ (m' + 3) ∧
      (Nonempty (S ≃* DihedralGroup (2 ^ (m' + 2))) ∨
        (1 ≤ m' ∧ Nonempty (S ≃* CFSG.Open.SemidihedralGroup (m' + 3)))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := h.two.exists_card_eq
  have hthree : 2 < Nat.card S := by
    have h3 : ({1, r, z} : Set S).ncard = 3 := by
      refine Set.ncard_eq_three.mpr ⟨1, r, z, h.r_ne.symm, h.z_ne.symm, h.r_ne_z, rfl⟩
    have := Set.ncard_le_ncard (Set.subset_univ ({1, r, z} : Set S)) Set.finite_univ
    rw [Set.ncard_univ, h3] at this
    omega
  have hm2 : 2 ≤ m := by
    by_contra hlt
    push Not at hlt
    have : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  rcases Nat.eq_or_lt_of_le hm2 with rfl | hm3
  · left; rw [hm]; norm_num
  · right
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + 3 := ⟨m - 3, by omega⟩
    refine ⟨m', hm, ?_⟩
    obtain ⟨a, ha, hr⟩ := exists_cyclic_index_two (m' + 3) (by omega) S r z h hm
    have ha' : orderOf a = 2 ^ (m' + 2) := ha
    obtain ⟨-, hcases, hcover⟩ := h.cyclic_structure hm ha' hr
    rcases hcases with hba | ⟨hm1, hba⟩
    · left
      have : NeZero (2 ^ (m' + 2)) := ⟨by positivity⟩
      obtain ⟨e⟩ := nonempty_mulEquiv_dihedral ha' h.r_sq hba hcover
        (by rw [hm, pow_succ]; ring)
      exact ⟨e.symm⟩
    · right
      refine ⟨hm1, ?_⟩
      obtain ⟨e⟩ := nonempty_mulEquiv_semidihedral (n := m' + 3) (by omega) ha h.r_sq hba hcover hm
      exact ⟨e.symm⟩

end Classification

end FourCentralizer

end CFSG.ClassicalInvolution
