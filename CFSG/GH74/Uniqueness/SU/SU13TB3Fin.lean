module

public import CFSG.GH74.Uniqueness.SU.SU13TB3Card
public import CFSG.GH74.Uniqueness.SU.SU13TB3Orb
public import CFSG.Walter.W67.W1Basic

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem orbit_step (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) {p q r m : ℕ}
    [Fact p.Prime] [Fact q.Prime] {U : Subgroup G} (hPU : zpowers e.s₁ ≤ U)
    (hUW : U ≤ oc (centralizer ({e.s₁} : Set G)))
    (hUinv : ∀ g ∈ f.F, ∀ u ∈ U, g * u * g⁻¹ ∈ U) {g : G} (hg : g ∈ f.F) (hgq : orderOf g = q)
    (hUcard : Nat.card U = r * p ^ m) (hr : r ∣ 3) (hqr : ¬ q ∣ r) (hqp : ¬ q ∣ p)
    (hord : ∀ k : ℕ, 0 < k → k ≤ m → ¬ q ∣ p ^ k - 1) : U ≤ zpowers e.s₁ := by
  have hgn : g ∈ normalizer (U : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hUinv g hg x, fun hx => ?_⟩
    have := hUinv g⁻¹ (f.F.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have h3 : 3 ∣ Nat.card (U ⊓ centralizer ({g} : Set G) : Subgroup G) := by
    have hle : zpowers e.s₁ ≤ U ⊓ centralizer ({g} : Set G) :=
      le_inf hPU ((zpowers_le).mpr (mem_centralizer_singleton_iff.mpr (f.F_s₁ g hg).symm))
    have := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, e.s₁_ord] at this
  have hcen := le_centralizer_of_card hgq hgn hUcard hqr hqp (hr.trans h3) hord
  have hg1 : g ≠ 1 := by
    intro h; rw [h, orderOf_one] at hgq
    have := (Fact.out : q.Prime).one_lt
    omega
  exact U_le_P hz e f hUW hUinv hg hg1
    (fun u hu => (mem_centralizer_singleton_iff.mp (hcen hu)).symm)

omit [Finite G] in
theorem zpowers_comm_of_le_oc (e : Elts G z) {V : Subgroup G} (hV : V ≤ oc (centralizer ({e.s₁} : Set G))) :
    ∀ a ∈ zpowers e.s₁, ∀ b ∈ V, a * b = b * a :=
  fun _ ha _ hb => zpowers_comm_of_mem_centralizer (oc_le _ (hV hb)) ha

theorem not_five_dvd (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) (l : Lem232 z e) :
    ¬ 5 ∣ Nat.card (oc (centralizer ({e.s₁} : Set G))) := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hdvd : Nat.card W ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 := W_dvd hKI7d hH hz e f l
  obtain ⟨V, -, hVW, hVp, hVidx, hVcard⟩ := exists_sylow_sub_ge (p := 5) (W := W) (P := ⊥) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  set m := (Nat.card W).factorization 5 with hm
  have hm1 : 1 ≤ m := (Nat.Prime.dvd_iff_one_le_factorization (by norm_num) Nat.card_pos.ne').mp h5
  have hm4 : m ≤ 4 := by
    by_contra hlt
    have h1 : 5 ^ 5 ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 :=
      ((pow_dvd_pow 5 (show 5 ≤ m by omega)).trans (Nat.ordProj_dvd _ 5)).trans hdvd
    revert h1; decide
  have hPV : zpowers e.s₁ ⊓ V = ⊥ := by
    have hd1 : Nat.card (zpowers e.s₁ ⊓ V : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : zpowers e.s₁ ⊓ V ≤ zpowers e.s₁)
      rwa [Nat.card_zpowers, e.s₁_ord] at this
    have hd2 : Nat.card (zpowers e.s₁ ⊓ V : Subgroup G) ∣ 5 ^ m := by
      have := Subgroup.card_dvd_of_le (inf_le_right : zpowers e.s₁ ⊓ V ≤ V)
      rwa [hVcard] at this
    have hcop : Nat.Coprime 3 (5 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hUcard : Nat.card (zpowers e.s₁ ⊔ V : Subgroup G) = 3 * 5 ^ m := by
    have := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (zpowers e.s₁) V
      (zpowers_comm_of_le_oc e hVW)).1
    rw [hPV, Subgroup.card_bot, Nat.card_zpowers, e.s₁_ord, hVcard] at this
    simpa using this
  have hUW : zpowers e.s₁ ⊔ V ≤ W := sup_le (zpowers_le_oc e) hVW
  obtain ⟨g, hgF, hg⟩ := f.F_seven
  have hU := orbit_step hz e f (p := 5) (q := 7) (r := 3) (m := m) (le_sup_left) hUW
    (sup_invariant hz e f hVW hVp hVidx) hgF hg hUcard (dvd_refl 3) (by norm_num) (by norm_num)
    (fun k hk hkm => by
      have : k ≤ 4 := by omega
      interval_cases k <;> norm_num)
  have hle := Subgroup.card_le_of_le hU
  rw [hUcard, Nat.card_zpowers, e.s₁_ord] at hle
  have : 5 ≤ 5 ^ m := by
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  omega

theorem not_seven_dvd (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) (l : Lem232 z e) :
    ¬ 7 ∣ Nat.card (oc (centralizer ({e.s₁} : Set G))) := by
  intro h7
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hdvd : Nat.card W ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 := W_dvd hKI7d hH hz e f l
  obtain ⟨V, -, hVW, hVp, hVidx, hVcard⟩ := exists_sylow_sub_ge (p := 7) (W := W) (P := ⊥) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  set m := (Nat.card W).factorization 7 with hm
  have hm1 : 1 ≤ m := (Nat.Prime.dvd_iff_one_le_factorization (by norm_num) Nat.card_pos.ne').mp h7
  have hm2 : m ≤ 2 := by
    by_contra hlt
    have h1 : 7 ^ 3 ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 :=
      ((pow_dvd_pow 7 (show 3 ≤ m by omega)).trans (Nat.ordProj_dvd _ 7)).trans hdvd
    revert h1; decide
  have hPV : zpowers e.s₁ ⊓ V = ⊥ := by
    have hd1 : Nat.card (zpowers e.s₁ ⊓ V : Subgroup G) ∣ 3 := by
      have := Subgroup.card_dvd_of_le (inf_le_left : zpowers e.s₁ ⊓ V ≤ zpowers e.s₁)
      rwa [Nat.card_zpowers, e.s₁_ord] at this
    have hd2 : Nat.card (zpowers e.s₁ ⊓ V : Subgroup G) ∣ 7 ^ m := by
      have := Subgroup.card_dvd_of_le (inf_le_right : zpowers e.s₁ ⊓ V ≤ V)
      rwa [hVcard] at this
    have hcop : Nat.Coprime 3 (7 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
    exact Subgroup.eq_bot_of_card_eq _ (Nat.eq_one_of_dvd_coprimes hcop hd1 hd2)
  have hUcard : Nat.card (zpowers e.s₁ ⊔ V : Subgroup G) = 3 * 7 ^ m := by
    have := (CFSG.Walter.W67.card_sup_mul_card_inf_of_commute (zpowers e.s₁) V
      (zpowers_comm_of_le_oc e hVW)).1
    rw [hPV, Subgroup.card_bot, Nat.card_zpowers, e.s₁_ord, hVcard] at this
    simpa using this
  have hUW : zpowers e.s₁ ⊔ V ≤ W := sup_le (zpowers_le_oc e) hVW
  obtain ⟨g, hgF, hg⟩ := f.F_five
  have hU := orbit_step hz e f (p := 7) (q := 5) (r := 3) (m := m) (le_sup_left) hUW
    (sup_invariant hz e f hVW hVp hVidx) hgF hg hUcard (dvd_refl 3) (by norm_num) (by norm_num)
    (fun k hk hkm => by
      have : k ≤ 2 := by omega
      interval_cases k <;> norm_num)
  have hle := Subgroup.card_le_of_le hU
  rw [hUcard, Nat.card_zpowers, e.s₁_ord] at hle
  have : 7 ≤ 7 ^ m := by
    calc 7 = 7 ^ 1 := by norm_num
      _ ≤ 7 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  omega

theorem not_nine_dvd (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) (l : Lem232 z e) :
    ¬ 9 ∣ Nat.card (oc (centralizer ({e.s₁} : Set G))) := by
  intro h9
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hdvd : Nat.card W ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 := W_dvd hKI7d hH hz e f l
  have hPW : zpowers e.s₁ ≤ W := zpowers_le_oc e
  obtain ⟨V, hPV, hVW, hVp, hVidx, hVcard⟩ := exists_sylow_sub_ge (p := 3) hPW
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, e.s₁_ord]; norm_num))
  set m := (Nat.card W).factorization 3 with hm
  have hm2 : 2 ≤ m := by
    have : 3 ^ 2 ∣ Nat.card W := by simpa using h9
    exact (Nat.Prime.pow_dvd_iff_le_factorization (by norm_num) Nat.card_pos.ne').mp this
  have hm5 : m ≤ 5 := by
    by_contra hlt
    have h1 : 3 ^ 6 ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 :=
      ((pow_dvd_pow 3 (show 6 ≤ m by omega)).trans (Nat.ordProj_dvd _ 3)).trans hdvd
    revert h1; decide
  have hsup : zpowers e.s₁ ⊔ V = V := sup_eq_right.mpr hPV
  have hU := orbit_step hz e f (p := 3) (q := 7) (r := 1) (m := m) hPV hVW
    (by
      intro g hg u hu
      have := sup_invariant hz e f hVW hVp hVidx g hg u (by rw [hsup]; exact hu)
      rwa [hsup] at this)
    (f.F_seven.choose_spec.1) (f.F_seven.choose_spec.2) (by rw [hVcard, one_mul]) (one_dvd _)
    (by norm_num) (by norm_num)
    (fun k hk hkm => by
      have : k ≤ 5 := by omega
      interval_cases k <;> norm_num)
  have hle := Subgroup.card_le_of_le hU
  rw [hVcard, Nat.card_zpowers, e.s₁_ord] at hle
  have : 3 ^ 2 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  omega

theorem oc_eq_zpowers (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 10)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart10 z e) (l : Lem232 z e) :
    oc (centralizer ({e.s₁} : Set G)) = zpowers e.s₁ := by
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hdvd : Nat.card W ∣ 3 ^ 5 * 5 ^ 4 * 7 ^ 2 := W_dvd hKI7d hH hz e f l
  have h5 : ¬ 5 ∣ Nat.card W := not_five_dvd hKI7d hH hz e f l
  have h7 : ¬ 7 ∣ Nat.card W := not_seven_dvd hKI7d hH hz e f l
  have h9 : ¬ 9 ∣ Nat.card W := not_nine_dvd hKI7d hH hz e f l
  have hPW : zpowers e.s₁ ≤ W := zpowers_le_oc e
  have h3 : 3 ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le hPW
    rwa [Nat.card_zpowers, e.s₁_ord] at this
  have hW3 : Nat.card W ∣ 3 ^ 5 := by
    have c1 : Nat.Coprime (Nat.card W) 5 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5 |>.symm
    have c2 : Nat.Coprime (Nat.card W) 7 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7 |>.symm
    have : Nat.card W ∣ 3 ^ 5 * (5 ^ 4 * 7 ^ 2) := by rw [← mul_assoc]; exact hdvd
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.pow_right _ c1) (Nat.Coprime.pow_right _ c2)) this)
  obtain ⟨j, hj, hjW⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hW3
  have hj1 : j = 1 := by
    rcases Nat.lt_or_ge j 2 with hlt | hge
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [h0, pow_zero] at hjW; rw [hjW] at h3; exact absurd (Nat.le_of_dvd one_pos h3) (by norm_num)
      · omega
    · exfalso
      apply h9
      rw [hjW, show (9 : ℕ) = 3 ^ 2 by norm_num]
      exact pow_dvd_pow 3 hge
  have hWcard : Nat.card W = 3 := by rw [hjW, hj1]; norm_num
  exact (Subgroup.eq_of_le_of_card_ge hPW (by rw [hWcard, Nat.card_zpowers, e.s₁_ord])).symm

end CFSG.GH74.Uniqueness.SU.SU13
