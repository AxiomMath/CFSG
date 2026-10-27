module

public import CFSG.GH74.Uniqueness.SU.SU13TC3W
public import CFSG.GH74.Uniqueness.SU.SU13TC3Free
public import CFSG.GH74.Uniqueness.SU.SU13TB3E
public import CFSG.GH74.Uniqueness.SU.SU13Data9
public import CFSG.GH74.Uniqueness.SU.SU13TB3Fin

public section

namespace CFSG.GH74.Uniqueness.SU.SU13

open Subgroup CFSG.GH74.Uniqueness.SU.SU4 CFSG.GH74.Uniqueness.SU.SU13.TB

variable {G : Type} [Group G] [Finite G] {z : G}

theorem F_five9 {e : Elts G z} (f : FPart9 z e) : ∃ g ∈ f.F, orderOf g = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h : 5 ∣ Nat.card ↥f.F := by rw [f.F_card]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥f.F) 5 h
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem F_three9 {e : Elts G z} (f : FPart9 z e) : ∃ g ∈ f.F, orderOf g = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h : 3 ∣ Nat.card ↥f.F := by rw [f.F_card]; norm_num
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥f.F) 3 h
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

theorem F_sylow9 {e : Elts G z} (f : FPart9 z e) : ∃ D : Subgroup G, D ≤ f.F ∧ Nat.card D = 9 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h : 3 ^ 2 ∣ Nat.card ↥f.F := by rw [f.F_card]; norm_num
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥f.F) 3 h
  refine ⟨K.map f.F.subtype, Subgroup.map_subtype_le _, ?_⟩
  rw [Subgroup.card_map_of_injective f.F.subtype_injective, hK]
  norm_num

theorem not_seven_dvd9 (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart9 z e) (l : Lem232 z e) :
    ¬ 7 ∣ Nat.card (oc (centralizer ({e.s₁} : Set G))) := by
  intro h7
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hdvd : Nat.card W ∣ 3 ^ 5 * 5 ^ 2 * 7 ^ 2 := W_dvd9 hKI7d hH hz e f.toFPart l
  obtain ⟨V, -, hVW, hVp, hVidx, hVcard⟩ := exists_sylow_sub_ge (p := 7) (W := W) (P := ⊥) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  set m := (Nat.card W).factorization 7 with hm
  have hm1 : 1 ≤ m := (Nat.Prime.dvd_iff_one_le_factorization (by norm_num) Nat.card_pos.ne').mp h7
  have hm2 : m ≤ 2 := by
    by_contra hlt
    have h1 : 7 ^ 3 ∣ 3 ^ 5 * 5 ^ 2 * 7 ^ 2 :=
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
  obtain ⟨g, hgF, hg⟩ := F_five9 f
  have hU := orbit_stepF hz e f.toFPart (p := 7) (q := 5) (r := 3) (m := m) (le_sup_left) hUW
    (sup_invariantF hz e f.toFPart hVW hVp hVidx) hgF hg hUcard (dvd_refl 3) (by norm_num) (by norm_num)
    (fun k hk hkm => by
      have : k ≤ 2 := by omega
      interval_cases k <;> norm_num)
  have hle := Subgroup.card_le_of_le hU
  rw [hUcard, Nat.card_zpowers, e.s₁_ord] at hle
  have : 7 ≤ 7 ^ m := by
    calc 7 = 7 ^ 1 := by norm_num
      _ ≤ 7 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  omega

theorem not_five_dvd9 (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart9 z e) (l : Lem232 z e) :
    ¬ 5 ∣ Nat.card (oc (centralizer ({e.s₁} : Set G))) := by
  intro h5
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hdvd : Nat.card W ∣ 3 ^ 5 * 5 ^ 2 * 7 ^ 2 := W_dvd9 hKI7d hH hz e f.toFPart l
  obtain ⟨V, -, hVW, hVp, hVidx, hVcard⟩ := exists_sylow_sub_ge (p := 5) (W := W) (P := ⊥) bot_le
    (IsPGroup.of_card (n := 0) (by simp))
  set m := (Nat.card W).factorization 5 with hm
  have hm1 : 1 ≤ m := (Nat.Prime.dvd_iff_one_le_factorization (by norm_num) Nat.card_pos.ne').mp h5
  have hm2 : m ≤ 2 := by
    by_contra hlt
    have h1 : 5 ^ 3 ∣ 3 ^ 5 * 5 ^ 2 * 7 ^ 2 :=
      ((pow_dvd_pow 5 (show 3 ≤ m by omega)).trans (Nat.ordProj_dvd _ 5)).trans hdvd
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
  have hUinv := sup_invariantF hz e f.toFPart hVW hVp hVidx
  have hVinv : ∀ g ∈ f.F, ∀ v ∈ V, g * v * g⁻¹ ∈ V := by
    intro g hg v hv
    have hu : g * v * g⁻¹ ∈ zpowers e.s₁ ⊔ V := hUinv g hg v (mem_sup_right hv)
    obtain ⟨c, hc, v', hv', hcv⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := V)
      (fun a ha b hb => zpowers_comm_of_le_oc e hVW a ha b hb) hu
    have hpowV : ∀ x ∈ V, x ^ (5 ^ m) = 1 := by
      intro x hx
      have := pow_card_eq_one' (G := V) (x := ⟨x, hx⟩)
      rw [hVcard] at this
      exact congrArg Subtype.val this
    have hord : (g * v * g⁻¹) ^ (5 ^ m) = 1 := by
      rw [conj_pow, hpowV v hv]; group
    have hcomm : Commute c v' := zpowers_comm_of_le_oc e hVW c hc v' hv'
    have hc5 : c ^ (5 ^ m) = 1 := by
      rw [← hcv, hcomm.mul_pow, hpowV v' hv', mul_one] at hord
      exact hord
    have hc3 : orderOf c ∣ 3 := by
      have := Subgroup.orderOf_dvd_natCard (zpowers e.s₁) hc
      rwa [Nat.card_zpowers, e.s₁_ord] at this
    have hcop : Nat.Coprime 3 (5 ^ m) := Nat.Coprime.pow_right _ (by norm_num)
    have hc1 : c = 1 :=
      orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hc3 (orderOf_dvd_of_pow_eq_one hc5))
    rw [← hcv, hc1, one_mul]
    exact hv'
  have hgn : ∀ g ∈ f.F, g ∈ normalizer (V : Set G) := by
    intro g hg
    rw [mem_normalizer_iff]
    intro x
    refine ⟨hVinv g hg x, fun hx => ?_⟩
    have := hVinv g⁻¹ (f.F.inv_mem hg) _ hx
    simpa [mul_assoc] using this
  have h5m : 5 ≤ 5 ^ m := by
    calc 5 = 5 ^ 1 := by norm_num
      _ ≤ 5 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hnc : ∀ g ∈ f.F, g ≠ 1 → (∀ v ∈ V, g * v = v * g) → False := by
    intro g hg hg1 hcen
    have hU := U_le_PF hz e f.toFPart hUW hUinv hg hg1 (fun u hu => by
      obtain ⟨c, hc, v, hv, rfl⟩ := SU1.mem_sup_of_commute (A := zpowers e.s₁) (B := V)
        (fun a ha b hb => zpowers_comm_of_le_oc e hVW a ha b hb) hu
      have hgc : c * g = g * c :=
        zpowers_comm_of_mem_centralizer (F_le_centralizerF e f.toFPart hg) hc
      calc g * (c * v) = (g * c) * v := by group
        _ = (c * g) * v := by rw [hgc]
        _ = c * (g * v) := by group
        _ = c * (v * g) := by rw [hcen v hv]
        _ = c * v * g := by group)
    have hle := Subgroup.card_le_of_le hU
    rw [hUcard, Nat.card_zpowers, e.s₁_ord] at hle
    omega
  have hm12 : m = 1 ∨ m = 2 := by omega
  rcases hm12 with hm1' | hm2'
  ·
    obtain ⟨g, hgF, hg3⟩ := F_three9 f
    have hg1 : g ≠ 1 := by
      intro h; rw [h, orderOf_one] at hg3; omega
    have hcen := le_centralizer_of_card (p := 5) (q := 3) (r := 1) (m := 1) hg3 (hgn g hgF) (A := V)
      (by rw [hVcard, hm1']; norm_num) (by norm_num) (by norm_num) (one_dvd _)
      (fun k hk hk1 => by
        have : k = 1 := by omega
        subst this; norm_num)
    exact hnc g hgF hg1 (fun v hv => (mem_centralizer_singleton_iff.mp (hcen hv)).symm)
  ·
    obtain ⟨D, hDF, hD9⟩ := F_sylow9 f
    have hV25 : Nat.card V = 25 := by rw [hVcard, hm2']; norm_num
    have hfree := card_modEq_one_of_free (D := D) (V := V) (fun d hd => hgn d (hDF hd))
      (fun d hd hd1 v hv hdv => by
        have hDp : IsPGroup 3 D := IsPGroup.of_card (n := 2) (by rw [hD9]; norm_num)
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf).mp hDp ⟨d, hd⟩
        have hdk : orderOf d = 3 ^ k := (Subgroup.orderOf_coe (⟨d, hd⟩ : D)).trans hk
        have hk1 : 1 ≤ k := by
          by_contra hcon
          have : k = 0 := by omega
          rw [this, pow_zero, orderOf_eq_one_iff] at hdk
          exact hd1 hdk
        set g := d ^ (3 ^ (k - 1)) with hg
        have hg3 : orderOf g = 3 := by
          rw [hg, orderOf_pow_of_dvd (by positivity) (by rw [hdk]; exact pow_dvd_pow 3 (by omega)), hdk]
          rw [show 3 ^ k = 3 ^ (k - 1) * 3 by rw [← pow_succ, Nat.sub_add_cancel hk1]]
          rw [Nat.mul_div_cancel_left _ (by positivity)]
        have hgF : g ∈ f.F := f.F.pow_mem (hDF hd) _
        have hg1 : g ≠ 1 := by
          intro h; rw [h, orderOf_one] at hg3; omega
        have hmod := card_modEq_card_inf_centralizer (A := V) hg3 (hgn g hgF)
        have hcdvd : Nat.card (V ⊓ centralizer ({g} : Set G) : Subgroup G) ∣ 5 ^ 2 := by
          have := Subgroup.card_dvd_of_le (inf_le_left : V ⊓ centralizer ({g} : Set G) ≤ V)
          rwa [hV25, show (25 : ℕ) = 5 ^ 2 by norm_num] at this
        obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 5)).mp hcdvd
        rw [hV25, hjc] at hmod
        have hj0 : j = 0 ∨ j = 2 := by
          interval_cases j
          · left; rfl
          · exfalso; revert hmod; decide
          · right; rfl
        have hbot : V ⊓ centralizer ({g} : Set G) = ⊥ := by
          rcases hj0 with h0 | h2
          · rw [h0, pow_zero] at hjc
            exact Subgroup.eq_bot_of_card_eq _ hjc
          · exfalso
            rw [h2] at hjc
            have hVle : V ≤ centralizer ({g} : Set G) := by
              have heq : V ⊓ centralizer ({g} : Set G) = V :=
                Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hjc, hV25]; norm_num)
              exact heq ▸ inf_le_right
            exact hnc g hgF hg1 (fun v hv => (mem_centralizer_singleton_iff.mp (hVle hv)).symm)
        have hvg : v ∈ V ⊓ centralizer ({g} : Set G) := by
          refine mem_inf.mpr ⟨hv, ?_⟩
          rw [mem_centralizer_singleton_iff]
          have hdv' : v * d = d * v := by
            calc v * d = (d * v * d⁻¹) * d := by rw [hdv]
              _ = d * v := by group
          have : Commute v d := hdv'
          exact (this.pow_right _).eq
        rw [hbot, mem_bot] at hvg
        exact hvg)
    rw [hD9, hV25] at hfree
    revert hfree; decide
  
theorem W_card9 (hKI7d : K.KI7d) (hH : K.IsTwoAlt ↥(centralizer ({z} : Set G)) 9)
    (hz : orderOf z = 2) (e : Elts G z) (f : FPart9 z e) (l : Lem232 z e) (hE : EPart10 z e)
    (h3 : 3 ^ 5 ∣ Nat.card (centralizer ({e.s₂} : Set G))) :
    Nat.card (oc (centralizer ({e.s₁} : Set G))) = 3 ^ 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set W := oc (centralizer ({e.s₁} : Set G)) with hW
  have hdvd : Nat.card W ∣ 3 ^ 5 * 5 ^ 2 * 7 ^ 2 := W_dvd9 hKI7d hH hz e f.toFPart l
  have h5 : ¬ 5 ∣ Nat.card W := not_five_dvd9 hKI7d hH hz e f l
  have h7 : ¬ 7 ∣ Nat.card W := not_seven_dvd9 hKI7d hH hz e f l
  have hPW : zpowers e.s₁ ≤ W := zpowers_le_oc e
  have h3W : 3 ∣ Nat.card W := by
    have := Subgroup.card_dvd_of_le hPW
    rwa [Nat.card_zpowers, e.s₁_ord] at this
  have hW3 : Nat.card W ∣ 3 ^ 5 := by
    have c1 : Nat.Coprime (Nat.card W) 5 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h5 |>.symm
    have c2 : Nat.Coprime (Nat.card W) 7 := (Nat.Prime.coprime_iff_not_dvd (by norm_num)).mpr h7 |>.symm
    have : Nat.card W ∣ 3 ^ 5 * (5 ^ 2 * 7 ^ 2) := by rw [← mul_assoc]; exact hdvd
    exact (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.mul_right
      (Nat.Coprime.pow_right _ c1) (Nat.Coprime.pow_right _ c2)) this)
  obtain ⟨j, hj, hjW⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hW3
  have hj1 : 1 ≤ j := by
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · rw [h0, pow_zero] at hjW; rw [hjW] at h3W; exact absurd (Nat.le_of_dvd one_pos h3W) (by norm_num)
    · exact h0
  by_contra hne
  have hj5 : j ≠ 5 := fun h => hne (by rw [hjW, h])
  have hj4 : j ≤ 4 := by omega
  rcases Nat.lt_or_ge j 2 with hlt | hge
  ·
    have hj' : j = 1 := by omega
    have hWc : Nat.card W = 3 := by rw [hjW, hj']; norm_num
    have hoc : oc (centralizer ({e.s₁} : Set G)) = zpowers e.s₁ := by
      have := Subgroup.eq_of_le_of_card_ge hPW (by rw [hWc, Nat.card_zpowers, e.s₁_ord])
      exact this.symm
    exact false_of_oc_eq hz e l hE hoc h3
  ·
    obtain ⟨g, hgF, hg⟩ := F_five9 f
    have hjm : 3 ^ j = 3 * 3 ^ (j - 1) := by
      rw [← pow_succ']; congr 1; omega
    have hU := orbit_stepF hz e f.toFPart (p := 3) (q := 5) (r := 3) (m := j - 1) (U := W) hPW le_rfl
      (fun g hg u hu => conj_mem_oc (F_le_centralizerF e f.toFPart hg) hu) hgF hg
      (by rw [hjW, hjm]) (dvd_refl 3) (by norm_num) (by norm_num)
      (fun k hk hkm => by
        have : k ≤ 3 := by omega
        interval_cases k <;> norm_num)
    have hle := Subgroup.card_le_of_le hU
    rw [hjW, Nat.card_zpowers, e.s₁_ord] at hle
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) hge
    omega

end CFSG.GH74.Uniqueness.SU.SU13
