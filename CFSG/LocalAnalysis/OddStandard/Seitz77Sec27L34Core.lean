module

public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34Conf
public import CFSG.LocalAnalysis.OddStandard.Seitz77Sec27L34Radical
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SolvableMinimalNormal

public section

namespace CFSG.OddStandard.Seitz77

open Matrix Subgroup

variable {G S : Type} [Group G] [Finite G] [Group S] [Finite S]

theorem L34Conf.card_G (c : L34Conf G S) : Nat.card G = 20160 * Nat.card c.π.ker := by
  have h := Subgroup.card_ker_mul_card_of_surjective c.π_surj
  rw [c.S_card] at h
  rw [← h]
  ring

theorem L34Conf.card_ker_dvd (c : L34Conf G S) : Nat.card c.π.ker ∣ 63247905 := by
  have h1 : Nat.card G ∣ Nat.card (GL (Fin 8) (ZMod 2)) :=
    Subgroup.card_dvd_of_injective c.ρ c.ρ_inj
  have h2 : Nat.card (GL (Fin 8) (ZMod 2)) = 20160 * (2 ^ 22 * 63247905) := by
    rw [Matrix.card_GL_field 8, ZMod.card, Fin.prod_univ_eight]
    norm_num
  rw [c.card_G, h2] at h1
  have h3 : Nat.card c.π.ker ∣ 2 ^ 22 * 63247905 :=
    Nat.dvd_of_mul_dvd_mul_left (by norm_num) h1
  have h4 : Nat.Coprime (Nat.card c.π.ker) (2 ^ 22) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.2 c.odd)
  exact h4.dvd_of_dvd_mul_left h3

theorem L34Conf.fpf_of_central (c : L34Conf G S) {z : G} (hz : z ∈ Subgroup.center G)
    (hz1 : z ≠ 1) (v : V8) (hv : glPermHom (c.ρ z) v = v) : v = 0 := by
  have hle : Subgroup.zpowers z ≤ Subgroup.center G := (Subgroup.zpowers_le).2 hz
  have : (Subgroup.zpowers z).Normal := ⟨fun n hn g => by
    have := Subgroup.mem_center_iff.1 (hle hn) g
    rw [this, mul_inv_cancel_right]
    exact hn⟩
  refine c.fix_eq_zero (Subgroup.zpowers z) ?_ v ?_
  · intro h
    apply hz1
    have : z ∈ Subgroup.zpowers z := Subgroup.mem_zpowers z
    rw [h] at this
    exact this
  · intro q hq
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hq
    rw [map_zpow, map_zpow]
    exact Equiv.Perm.zpow_apply_eq_self_of_apply_eq_self hv k

theorem L34Conf.false_of_central_three (c : L34Conf G S) {z : G} (hz : z ∈ Subgroup.center G)
    (hz3 : orderOf z = 3) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz3
    omega
  have hz3' : z ^ 3 = 1 := by rw [← hz3]; exact pow_orderOf_eq_one z
  have hfpf := c.fpf_of_central hz hz1
  have hpg : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz3, pow_one])
  obtain ⟨T, hzT⟩ := hpg.exists_le_sylow
  have hzT' : z ∈ (T : Subgroup G) := hzT (Subgroup.mem_zpowers z)
  let φ : G →* Equiv.Perm V8 := glPermHom.comp c.ρ
  have h0 : ∀ g, φ g 0 = 0 := fun g => glPermHom_zero (c.ρ g)
  obtain ⟨v, hv0, hvcard⟩ := exists_nonzero_orbit_le_three φ h0 (T : Subgroup G) T.isPGroup'
  have hzv : φ z v ≠ v := fun h => hv0 (hfpf v h)
  have hz2v : φ (z ^ 2) v ≠ v := by
    intro h
    apply hzv
    calc φ z v = φ (z ^ 4) v := by rw [show z ^ 4 = z ^ 3 * z by group, hz3', one_mul]
      _ = φ (z ^ 2) (φ (z ^ 2) v) := by
          rw [show z ^ 4 = z ^ 2 * z ^ 2 by group, map_mul, Equiv.Perm.mul_apply]
      _ = v := by rw [h, h]
  have hz12 : φ z v ≠ φ (z ^ 2) v := by
    intro h
    apply hzv
    have h' : φ z (φ z v) = φ z v := by
      rw [← Equiv.Perm.mul_apply, ← map_mul, ← pow_two]
      exact h.symm
    exact (φ z).injective h'
  have hmem : ∀ t ∈ (T : Subgroup G), φ t v = v ∨ φ t v = φ z v ∨ φ t v = φ (z ^ 2) v := by
    intro t ht
    let O : Set V8 := {w | ∃ t ∈ (T : Subgroup G), w = φ t v}
    let A : Set V8 := {v, φ z v, φ (z ^ 2) v}
    have hA3 : A.ncard = 3 := by
      rw [Set.ncard_eq_three]
      exact ⟨v, φ z v, φ (z ^ 2) v, hzv.symm, hz2v.symm, hz12, rfl⟩
    have hAO : A ⊆ O := by
      intro w hw
      rcases hw with rfl | rfl | rfl
      · exact ⟨1, (T : Subgroup G).one_mem, by simp⟩
      · exact ⟨z, hzT', rfl⟩
      · exact ⟨z ^ 2, (T : Subgroup G).pow_mem hzT' 2, rfl⟩
    have hOcard : O.ncard ≤ 3 := by
      have : O.ncard = Nat.card {w : V8 // ∃ t ∈ (T : Subgroup G), w = φ t v} := by
        rw [← Nat.card_coe_set_eq]
        rfl
      rw [this]
      exact hvcard
    have hAeq : A = O :=
      Set.eq_of_subset_of_ncard_le hAO (by rw [hA3]; exact hOcard) (Set.toFinite _)
    have : φ t v ∈ A := by rw [hAeq]; exact ⟨t, ht, rfl⟩
    exact this
  have horb : ∀ t ∈ (T : Subgroup G), ∃ i : ZMod 3, φ t v = φ (z ^ i.val) v := by
    intro t ht
    rcases hmem t ht with h | h | h
    · exact ⟨0, by simpa using h⟩
    · exact ⟨1, by rw [ZMod.val_one, pow_one]; exact h⟩
    · exact ⟨2, by rw [show (2 : ZMod 3).val = 2 from rfl]; exact h⟩
  have hzc : ∀ t ∈ (T : Subgroup G), t * z = z * t := fun t _ =>
    Subgroup.mem_center_iff.1 hz t
  obtain ⟨cc, hcc⟩ := exists_hom_zmod_three_of_small_orbit φ (T : Subgroup G) z hzT' hz3' hzc v
    hzv horb
  exact false_of_central_order_three_transfer c.perf hz hz3 (T : Subgroup G) hzT'
    (Sylow.not_dvd_index T) cc hcc

theorem L34Conf.false_of_central_prime (c : L34Conf G S) {z : G} (hz : z ∈ Subgroup.center G)
    {p : ℕ} [Fact p.Prime] (hp : p = 5 ∨ p = 17) (hzp : orderOf z = p) : False := by
  have h7 : 7 ∣ Nat.card G := by
    rw [c.card_G]
    exact Dvd.dvd.mul_right (by norm_num) _
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hz1 : z ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hzp
    have := (Fact.out : Nat.Prime p).one_lt
    omega
  have hfpf := c.fpf_of_central hz hz1
  have hzp' : (c.ρ z) ^ p = 1 := by rw [← map_pow, ← hzp, pow_orderOf_eq_one, map_one]
  have hh7 : (c.ρ h) ^ 7 = 1 := by rw [← map_pow, ← hh, pow_orderOf_eq_one, map_one]
  have hcomm : c.ρ z * c.ρ h = c.ρ h * c.ρ z := by
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hz h).symm]
  have h1 := card_fix_modEq_one hcomm hzp' hfpf
  have h2 := card_V8_modEq_card_fix (c.ρ h) hh7
  have h3 := eq_one_of_fix_conditions hp h2 h1
  have h4 : h = 1 := c.ρ_inj (by rw [h3, map_one])
  rw [h4, orderOf_one] at hh
  omega

theorem L34Conf.fpf_three_of_ker_bot (c : L34Conf G S) (hker : c.π.ker = ⊥) {u : G}
    (hu : orderOf u = 3) (w : V8) (hw : glPermHom (c.ρ u) w = w) : w = 0 := by
  obtain ⟨x, hxX, hx3⟩ := c.exists_order_three
  have hinj : Function.Injective c.π := (MonoidHom.ker_eq_bot_iff c.π).1 hker
  have hπx : orderOf (c.π x) = 3 := by rw [orderOf_injective c.π hinj x, hx3]
  have hπu : orderOf (c.π u) = 3 := by rw [orderOf_injective c.π hinj u, hu]
  obtain ⟨σ, hσ⟩ := c.inv3 (c.π x) (c.π u) hπx hπu
  obtain ⟨κ, hκ⟩ := c.π_surj σ
  have hconj : κ * x * κ⁻¹ = u := by
    apply hinj
    rw [map_mul, map_mul, map_inv, hκ, hσ]
  have hw' : glPermHom (c.ρ x) (glPermHom (c.ρ κ⁻¹) w) = glPermHom (c.ρ κ⁻¹) w := by
    have h1 : glPermHom (c.ρ κ) (glPermHom (c.ρ x) (glPermHom (c.ρ κ⁻¹) w)) = w := by
      rw [← hconj] at hw
      simpa [map_mul, Equiv.Perm.mul_apply] using hw
    have h2 := congrArg (glPermHom (c.ρ κ⁻¹)) h1
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one,
      Equiv.Perm.one_apply] at h2
    exact h2
  have h0 := c.fpf x hxX hx3 _ hw'
  have h3 : glPermHom (c.ρ κ) (glPermHom (c.ρ κ⁻¹) w) = w := by
    rw [← Equiv.Perm.mul_apply, ← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one,
      Equiv.Perm.one_apply]
  rw [h0, glPermHom_zero] at h3
  exact h3.symm

theorem L34Conf.false_of_ker_bot (c : L34Conf G S) (hker : c.π.ker = ⊥) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG : Nat.card G = 20160 := by rw [c.card_G, hker, Subgroup.card_bot, mul_one]
  obtain ⟨T, hT⟩ := Sylow.exists_subgroup_card_pow_prime 3 (n := 2) (by rw [hG]; norm_num)
  have hTp : IsPGroup 3 T := IsPGroup.of_card hT
  let φ : G →* Equiv.Perm V8 := glPermHom.comp c.ρ
  have h0 : ∀ g, φ g 0 = 0 := fun g => glPermHom_zero (c.ρ g)
  obtain ⟨v, hv0, hcard⟩ := exists_nonzero_orbit_le_three φ h0 T hTp
  have hos := card_orbit_mul_card_stab φ T v
  rw [hT] at hos
  have hstab : 3 ≤ Nat.card {t : T // φ t v = v} := by
    by_contra hlt
    push Not at hlt
    have : Nat.card {w : V8 // ∃ t ∈ T, w = φ t v} * Nat.card {t : T // φ t v = v} ≤ 3 * 2 :=
      Nat.mul_le_mul hcard (by omega)
    omega
  obtain ⟨t, ht1, htv⟩ : ∃ t : T, t ≠ 1 ∧ φ t v = v := by
    by_contra hno
    push Not at hno
    have hsub : Subsingleton {t : T // φ t v = v} :=
      ⟨fun a b => Subtype.ext (by
        have ha : a.1 = 1 := by
          by_contra hne
          exact hno a.1 hne a.2
        have hb : b.1 = 1 := by
          by_contra hne
          exact hno b.1 hne b.2
        rw [ha, hb])⟩
    have : Nat.card {t : T // φ t v = v} ≤ 1 := Finite.card_le_one_iff_subsingleton.2 hsub
    omega
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hTp t
  have hk1 : k ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at hk
    exact ht1 (orderOf_eq_one_iff.1 hk)
  have hk3 : 3 ∣ orderOf t := by
    rw [hk]
    exact dvd_pow_self 3 hk1
  have hord : orderOf ((t : G) ^ (orderOf t / 3)) = 3 := by
    rw [← Subgroup.coe_pow, Subgroup.orderOf_coe]
    exact orderOf_pow_orderOf_div (by rw [hk]; positivity) hk3
  have hfix : glPermHom (c.ρ ((t : G) ^ (orderOf t / 3))) v = v := by
    rw [map_pow, map_pow]
    exact Equiv.Perm.pow_apply_eq_self_of_apply_eq_self htv _
  exact hv0 (c.fpf_three_of_ker_bot hker hord v hfix)

theorem L34Conf.ker_maximal (c : L34Conf G S) (M : Subgroup G) [M.Normal] (hM : c.π.ker ≤ M) :
    M = c.π.ker ∨ M = ⊤ := by
  have hmapN : (M.map c.π).Normal := Subgroup.Normal.map ‹M.Normal› c.π c.π_surj
  rcases c.S_simple.eq_bot_or_eq_top_of_normal (M.map c.π) with hbot | htop
  · left
    apply le_antisymm _ hM
    intro m hm
    have : c.π m ∈ M.map c.π := ⟨m, hm, rfl⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact this
  · right
    rw [eq_top_iff]
    intro g _
    have hg : c.π g ∈ M.map c.π := htop ▸ Subgroup.mem_top _
    obtain ⟨m, hm, hmg⟩ := hg
    have : m⁻¹ * g ∈ c.π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hmg, inv_mul_cancel]
    have h2 : m * (m⁻¹ * g) ∈ M := M.mul_mem hm (hM this)
    simpa using h2

theorem L34Conf.index_ker (c : L34Conf G S) : c.π.ker.index = 20160 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective c.π c.π_surj, Subgroup.card_top,
    c.S_card]

theorem L34Conf.false (c : L34Conf G S) : False := by
  by_cases hR : c.π.ker = ⊥
  · exact c.false_of_ker_bot hR
  have hRn : c.π.ker.Normal := MonoidHom.normal_ker c.π
  obtain ⟨Q, hQR, hQmin⟩ := Finite.exists_le_minimal
    (p := fun M : Subgroup G => M.Normal ∧ M ≠ ⊥) (a := c.π.ker) ⟨hRn, hR⟩
  have hQn : Q.Normal := hQmin.1.1
  have hQne : Q ≠ ⊥ := hQmin.1.2
  have hRsolv : Group.IsSolvable c.π.ker := CFSG.FeitThompson.isSolvable_of_odd_natCard _ c.odd
  have hQsolv : Group.IsSolvable Q :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hQR)
  obtain ⟨p, hp, hab, d, hd, hcard⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.minimal_normal_solvable_elementary Q hQmin hQsolv
  have : Fact p.Prime := ⟨hp⟩
  have hel : IsElementaryAbelian p Q :=
    { toIsMulCommutative := hab.1
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        apply Subtype.ext
        simpa using hab.2 x x.2 }
  have hmod := card_V8_modEq_one_of_pgroup c.ρ Q (IsPGroup.of_card hcard)
    (fun v hv => c.fix_eq_zero Q hQne v hv)
  have hp255 : p ∣ 3 * 5 * 17 := by
    have := (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 256)).1 hmod.symm
    simpa using this
  have hpcases : p = 3 ∨ p = 5 ∨ p = 17 := by
    rcases (Nat.Prime.dvd_mul hp).1 hp255 with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 h)
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
    · exact Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h))
  have hQdvd : p ^ d ∣ 63247905 := by
    rw [← hcard]
    exact (Subgroup.card_dvd_of_le hQR).trans c.card_ker_dvd
  have hbound : (p ^ d) ^ d < 20160 := by
    rcases hpcases with rfl | rfl | rfl
    · have hd3 : d ≤ 3 := by
        by_contra h
        push Not at h
        have h81 : 3 ^ 4 ∣ 63247905 := (pow_dvd_pow 3 h).trans hQdvd
        norm_num at h81
      interval_cases d
      all_goals norm_num
    · have hd1 : d ≤ 1 := by
        by_contra h
        push Not at h
        have h25 : 5 ^ 2 ∣ 63247905 := (pow_dvd_pow 5 h).trans hQdvd
        norm_num at h25
      interval_cases d
      all_goals norm_num
    · have hd1 : d ≤ 1 := by
        by_contra h
        push Not at h
        have h289 : 17 ^ 2 ∣ 63247905 := (pow_dvd_pow 17 h).trans hQdvd
        norm_num at h289
      interval_cases d
      all_goals norm_num
  have hQc : Q ≤ Subgroup.center G :=
    minimal_normal_le_center c.perf c.π.ker c.odd (fun M hM hRM => by
      have := hM
      exact c.ker_maximal M hRM) (by rw [c.index_ker]) Q hcard hbound
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (G := Q) (by
    rw [hcard]
    exact dvd_pow_self p hd.ne')
  have hzc : (z : G) ∈ Subgroup.center G := hQc z.2
  have hzo : orderOf (z : G) = p := by rw [Subgroup.orderOf_coe, hz]
  rcases hpcases with rfl | rfl | rfl
  · exact c.false_of_central_three hzc hzo
  · exact c.false_of_central_prime hzc (Or.inl rfl) hzo
  · exact c.false_of_central_prime hzc (Or.inr rfl) hzo

end CFSG.OddStandard.Seitz77
