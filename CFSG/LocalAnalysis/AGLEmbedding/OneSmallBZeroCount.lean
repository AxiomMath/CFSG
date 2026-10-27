module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBZeroFusion

public section

namespace CFSG.AGLEmbedding

open CFSG.Open

variable {G : Type} [Group G] [Finite G]

theorem ncard_fusionSet_eq {p : ℕ} (hp : p.Prime) {R T : Subgroup G} {z : G} (hTR : T ≤ R)
    (hzR : z ∈ R) (hzT : z ∉ T) (hzp : orderOf z = p)
    (hRz : ∀ r ∈ R, r * z = z * r) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hdec : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i) :
    (fusionSet R z).ncard = (fusionSet R z ∩ T).ncard +
      (p - 1) * {t | t ∈ T ∧ z * t ∈ fusionSet R z}.ncard := by
  have : Fact p.Prime := ⟨hp⟩
  rw [← Set.ncard_inter_add_ncard_sdiff_eq_ncard (fusionSet R z) T]
  congr 1
  set O : Set G := {t | t ∈ T ∧ z * t ∈ fusionSet R z} with hO
  have hzmT : ∀ m : ℕ, z ^ m ∈ T → p ∣ m := by
    intro m hm
    by_contra hpm
    apply hzT
    have h1 : z ^ m ≠ 1 := by
      intro h1
      exact hpm (hzp ▸ orderOf_dvd_of_pow_eq_one h1)
    have := mem_zpowers_of_mem_zpowers_of_prime hp hzp (Subgroup.npow_mem_zpowers z m) h1
    exact (Subgroup.zpowers_le.mpr hm) this
  have hcommT : ∀ t ∈ T, Commute z t := fun t ht => (hRz t (hTR ht)).symm
  rw [mul_comm, ← Set.ncard_Ico_nat 1 p, ← Set.ncard_prod]
  symm
  refine Set.ncard_congr (fun tm _ => (z * tm.1) ^ tm.2) ?_ ?_ ?_
  ·
    rintro ⟨t, m⟩ ⟨⟨htT, htZ⟩, hm1, hmp⟩
    have hzt : (z * t) ^ m = z ^ m * t ^ m := (hcommT t htT).mul_pow m
    have hnT : (z * t) ^ m ∉ T := by
      intro h
      rw [hzt] at h
      have h2 : z ^ m ∈ T := by
        have := T.mul_mem h (T.inv_mem (T.pow_mem htT m))
        simpa using this
      have := hzmT m h2
      have : p ≤ m := Nat.le_of_dvd (by omega) this
      omega
    refine ⟨pow_mem_fusionSet htZ (fun h => hnT (h ▸ T.one_mem)), hnT⟩
  ·
    rintro ⟨t, a⟩ ⟨t', b⟩ ⟨⟨htT, -⟩, ha1, hap⟩ ⟨⟨ht'T, -⟩, hb1, hbp⟩ h
    simp only at h
    rw [(hcommT t htT).mul_pow, (hcommT t' ht'T).mul_pow] at h
    have hab : a = b := by
      by_contra hne
      rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
      · have h2 : z ^ (b - a) ∈ T := by
          have h3 : z ^ (b - a) = t ^ a * (t' ^ b)⁻¹ := by
            have h4 : z ^ b = z ^ a * z ^ (b - a) := by rw [← pow_add]; congr 1; omega
            have h5 : z ^ a * z ^ (b - a) * t' ^ b = z ^ a * t ^ a := by rw [← h4, h]
            have h6 : z ^ (b - a) * t' ^ b = t ^ a := mul_left_cancel (by rw [← mul_assoc, h5])
            rw [← h6]
            group
          rw [h3]
          exact T.mul_mem (T.pow_mem htT a) (T.inv_mem (T.pow_mem ht'T b))
        have := Nat.le_of_dvd (by omega) (hzmT _ h2)
        omega
      · have h2 : z ^ (a - b) ∈ T := by
          have h3 : z ^ (a - b) = t' ^ b * (t ^ a)⁻¹ := by
            have h4 : z ^ a = z ^ b * z ^ (a - b) := by rw [← pow_add]; congr 1; omega
            have h5 : z ^ b * z ^ (a - b) * t ^ a = z ^ b * t' ^ b := by rw [← h4, h]
            have h6 : z ^ (a - b) * t ^ a = t' ^ b := mul_left_cancel (by rw [← mul_assoc, h5])
            rw [← h6]
            group
          rw [h3]
          exact T.mul_mem (T.pow_mem ht'T b) (T.inv_mem (T.pow_mem htT a))
        have := Nat.le_of_dvd (by omega) (hzmT _ h2)
        omega
    subst hab
    have h7 : t ^ a = t' ^ a := mul_left_cancel h
    obtain ⟨a', -, haa'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (Nat.coprime_of_lt_prime (by omega) hap hp).symm hp.one_lt
    have hmod : a * a' ≡ 1 [MOD p] := by
      unfold Nat.ModEq
      rw [haa', Nat.mod_eq_of_lt hp.one_lt]
    have h8 : t = t' := by
      calc t = t ^ (a * a') := by
            rw [pow_congr_modEq (hexp t (hTR htT)) hmod, pow_one]
        _ = t' ^ (a * a') := by rw [pow_mul, h7, ← pow_mul]
        _ = t' := by rw [pow_congr_modEq (hexp t' (hTR ht'T)) hmod, pow_one]
    rw [h8]
  ·
    rintro w ⟨hwZ, hwT⟩
    have hwR : w ∈ R := fusionSet_subset hzR hwZ
    obtain ⟨t, htT, i, rfl⟩ := hdec w hwR
    set m := i % p with hm
    have hm0 : m ≠ 0 := by
      intro h0
      apply hwT
      have : z ^ i = 1 := by
        rw [← Nat.mod_add_div i p, ← hm, h0, zero_add, pow_mul, ← hzp, pow_orderOf_eq_one,
          one_pow]
      rw [this, mul_one]
      exact htT
    have hmp : m < p := Nat.mod_lt _ hp.pos
    have hzi : z ^ i = z ^ m := pow_congr_modEq (hexp z hzR) (Nat.mod_modEq i p).symm
    obtain ⟨m', -, hmm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
      (Nat.coprime_of_lt_prime hm0 hmp hp).symm hp.one_lt
    have hmod : m * m' ≡ 1 [MOD p] := by
      unfold Nat.ModEq
      rw [hmm', Nat.mod_eq_of_lt hp.one_lt]
    have hmod' : m' * m ≡ 1 [MOD p] := by rw [mul_comm]; exact hmod
    refine ⟨⟨t ^ m', m⟩, ⟨⟨T.pow_mem htT m', ?_⟩, ?_, hmp⟩, ?_⟩
    ·
      have h1 : z * t ^ m' = (t * z ^ i) ^ m' := by
        rw [hzi, ((hcommT t htT).symm.pow_right m).mul_pow, ← pow_mul,
          pow_congr_modEq (hexp z hzR) hmod, pow_one]
        exact (hcommT _ (T.pow_mem htT m')).eq
      rw [h1]
      refine pow_mem_fusionSet hwZ ?_
      rw [← h1]
      intro h2
      apply hzT
      have : z = (t ^ m')⁻¹ := by
        calc z = z * t ^ m' * (t ^ m')⁻¹ := by group
          _ = (t ^ m')⁻¹ := by rw [h2, one_mul]
      rw [this]
      exact T.inv_mem (T.pow_mem htT m')
    · omega
    · show (z * t ^ m') ^ m = t * z ^ i
      rw [(hcommT _ (T.pow_mem htT m')).mul_pow, ← pow_mul,
        pow_congr_modEq (hexp t (hTR htT)) hmod', pow_one, hzi]
      exact ((hcommT t htT).pow_left m).eq

omit [Finite G] in
theorem mem_zpowers_of_mem_fusionSet_of_not_mem {p : ℕ} (hp : p.Prime) {R T : Subgroup G} {z : G}
    (hTR : T ≤ R) (hzR : z ∈ R)
    (hRz : ∀ r ∈ R, r * z = z * r) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hdec : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hO : ∀ t ∈ T, z * t ∈ fusionSet R z → t = 1) {w : G} (hw : w ∈ fusionSet R z) (hwT : w ∉ T) :
    w ∈ Subgroup.zpowers z := by
  have hwR : w ∈ R := fusionSet_subset hzR hw
  obtain ⟨t, htT, i, rfl⟩ := hdec _ hwR
  have hcommT : ∀ t ∈ T, Commute z t := fun t ht => (hRz t (hTR ht)).symm
  set m := i % p with hm
  have hzi : z ^ i = z ^ m := pow_congr_modEq (hexp z hzR) (Nat.mod_modEq i p).symm
  have hm0 : m ≠ 0 := by
    intro h0
    apply hwT
    rw [hzi, h0, pow_zero, mul_one]
    exact htT
  have hmp : m < p := Nat.mod_lt _ hp.pos
  obtain ⟨m', -, hmm'⟩ := Nat.exists_mul_mod_eq_one_of_coprime
    (Nat.coprime_of_lt_prime hm0 hmp hp).symm hp.one_lt
  have hmod : m * m' ≡ 1 [MOD p] := by
    unfold Nat.ModEq
    rw [hmm', Nat.mod_eq_of_lt hp.one_lt]
  have hmod' : m' * m ≡ 1 [MOD p] := by rw [mul_comm]; exact hmod
  have h1 : z * t ^ m' = (t * z ^ i) ^ m' := by
    rw [hzi, ((hcommT t htT).symm.pow_right m).mul_pow, ← pow_mul,
      pow_congr_modEq (hexp z hzR) hmod, pow_one]
    exact (hcommT _ (T.pow_mem htT m')).eq
  have h2 : t ^ m' = 1 := by
    refine hO _ (T.pow_mem htT m') ?_
    rw [h1]
    refine pow_mem_fusionSet hw ?_
    rw [← h1]
    intro h3
    apply hwT
    have h4 : z = (t ^ m')⁻¹ := by
      calc z = z * t ^ m' * (t ^ m')⁻¹ := by group
        _ = (t ^ m')⁻¹ := by rw [h3, one_mul]
    have h5 : z ∈ T := by rw [h4]; exact T.inv_mem (T.pow_mem htT m')
    exact T.mul_mem htT (T.pow_mem h5 i)
  have ht1 : t = 1 := by
    calc t = t ^ (m' * m) := by rw [pow_congr_modEq (hexp t (hTR htT)) hmod', pow_one]
      _ = 1 := by rw [pow_mul, h2, one_pow]
  rw [ht1, one_mul]
  exact Subgroup.npow_mem_zpowers z i

theorem false_of_plane_lemma {p : ℕ} (hp : p.Prime) {R T : Subgroup G} {z x : G}
    (hTR : T ≤ R) (hzR : z ∈ R) (hzT : z ∉ T) (hzp : orderOf z = p)
    (hTcard : Nat.card T = p ^ 2)
    (hRz : ∀ r ∈ R, r * z = z * r) (hexp : ∀ r ∈ R, r ^ p = 1)
    (hdec : ∀ r ∈ R, ∃ t ∈ T, ∃ i : ℕ, r = t * z ^ i)
    (hxN : x ∈ Subgroup.normalizer (R : Set G)) (hxz : x * z * x⁻¹ ∉ Subgroup.zpowers z)
    (hO : ∀ t ∈ T, z * t ∈ fusionSet R z → t = 1)
    (hY : 2 * (p - 1) < (fusionSet R z ∩ T).ncard) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hz1 : z ≠ 1 := fun h => by rw [h, orderOf_one] at hzp; exact hp.one_lt.ne hzp
  have hsub : ∀ {w : G}, w ∈ fusionSet R z → w ∉ T → w ∈ Subgroup.zpowers z := fun hw hwT =>
    mem_zpowers_of_mem_fusionSet_of_not_mem hp hTR hzR hRz hexp hdec hO hw hwT
  have hxzZ : x * z * x⁻¹ ∈ fusionSet R z := conj_mem_fusionSet hxN (self_mem_fusionSet hz1)
  have hxzT : x * z * x⁻¹ ∈ T := by
    by_contra h
    exact hxz (hsub hxzZ h)
  set D : Subgroup G := T ⊓ T.comap (MulAut.conj x).toMonoidHom with hD
  set Y : Set G := fusionSet R z ∩ T with hYdef
  set W : Set G := {w | w ∈ Y ∧ x * w * x⁻¹ ∈ T} with hW
  have hWY : W ⊆ Y := fun w hw => hw.1
  have hYW : Y \ W ⊆ (fun g => x⁻¹ * g * x) '' ((Subgroup.zpowers z : Set G) \ {1}) := by
    rintro w ⟨hwY, hwW⟩
    have hxwT : x * w * x⁻¹ ∉ T := fun h => hwW ⟨hwY, h⟩
    have hxwZ : x * w * x⁻¹ ∈ fusionSet R z := conj_mem_fusionSet hxN hwY.1
    refine ⟨x * w * x⁻¹, ⟨hsub hxwZ hxwT, hxwZ.1⟩, by simp only; group⟩
  have hcardZ : ((Subgroup.zpowers z : Set G) \ {1}).ncard = p - 1 := by
    rw [Set.ncard_sdiff_singleton_of_mem (Subgroup.one_mem _), ← Nat.card_coe_set_eq]
    rw [show ((Subgroup.zpowers z : Set G) : Type) = Subgroup.zpowers z from rfl,
      Nat.card_zpowers, hzp]
  have hYW' : (Y \ W).ncard ≤ p - 1 := by
    calc (Y \ W).ncard ≤ ((fun g => x⁻¹ * g * x) '' ((Subgroup.zpowers z : Set G) \ {1})).ncard :=
          Set.ncard_le_ncard hYW (Set.toFinite _)
      _ ≤ ((Subgroup.zpowers z : Set G) \ {1}).ncard := Set.ncard_image_le (Set.toFinite _)
      _ = p - 1 := hcardZ
  have hWcard : p - 1 < W.ncard := by
    have := Set.ncard_sdiff_add_ncard_of_subset hWY (Set.toFinite _)
    omega
  have hWD : W ⊆ (D : Set G) \ {1} := by
    rintro w ⟨hwY, hxw⟩
    exact ⟨⟨hwY.2, hxw⟩, hwY.1.1⟩
  by_cases hDT : D = T
  ·
    have hT : ∀ t ∈ T, x * t * x⁻¹ ∈ T := by
      intro t ht
      have : t ∈ D := hDT ▸ ht
      exact this.2
    let f : T → T := fun t => ⟨x * t * x⁻¹, hT t t.2⟩
    have hfinj : Function.Injective f := by
      intro a b hab
      have h1 : x * (a : G) * x⁻¹ = x * b * x⁻¹ := congrArg Subtype.val hab
      exact Subtype.ext (by simpa using h1)
    obtain ⟨t, ht⟩ := (Finite.injective_iff_surjective.mp hfinj) ⟨x * z * x⁻¹, hxzT⟩
    have h1 : x * (t : G) * x⁻¹ = x * z * x⁻¹ := congrArg Subtype.val ht
    have h2 : (t : G) = z := by simpa using h1
    exact hzT (h2 ▸ t.2)
  ·
    have hDlt : D < T := lt_of_le_of_ne inf_le_left hDT
    have hDdvd : Nat.card D ∣ p ^ 2 := hTcard ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow hp).mp hDdvd
    have hj2 : j ≠ 2 := by
      intro h2
      apply hDT
      exact Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hjeq, h2, hTcard])
    have hDle : Nat.card D ≤ p := by
      rw [hjeq]
      interval_cases j
      · simp; exact hp.one_lt.le
      · simp
      · exact absurd rfl hj2
    have h1 : ((D : Set G) \ {1}).ncard ≤ p - 1 := by
      rw [Set.ncard_sdiff_singleton_of_mem D.one_mem, ← Nat.card_coe_set_eq]
      have : Nat.card (D : Set G) = Nat.card D := rfl
      omega
    have h2 := Set.ncard_le_ncard hWD (Set.toFinite _)
    omega

end CFSG.AGLEmbedding
