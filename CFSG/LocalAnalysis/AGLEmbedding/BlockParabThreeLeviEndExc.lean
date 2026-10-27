module

public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviEnd
public import CFSG.LocalAnalysis.AGLEmbedding.BlockParabThreeLeviCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabPrimeTwo

public section

namespace CFSG.AGLEmbedding

open CFSG.Fischer.Classification
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem mem_normalizer_join_of_mem [Finite G] {H₁ H₂ : Subgroup G} {g : G}
    (h₁ : g ∈ Subgroup.normalizer (H₁ : Set G)) (h₂ : g ∈ Subgroup.normalizer (H₂ : Set G)) :
    g ∈ Subgroup.normalizer ((H₁ ⊔ H₂ : Subgroup G) : Set G) := by
  have e : H₁ ⊔ H₂ = Subgroup.closure ((H₁ : Set G) ∪ H₂) := by
    rw [Subgroup.closure_union, Subgroup.closure_eq, Subgroup.closure_eq]
  rw [e]
  refine mem_normalizer_closure_of_forall_conj_mem ?_
  rintro s (hs | hs)
  · exact Subgroup.subset_closure (Or.inl ((Subgroup.mem_normalizer_iff.1 h₁ s).1 hs))
  · exact Subgroup.subset_closure (Or.inr ((Subgroup.mem_normalizer_iff.1 h₂ s).1 hs))

theorem mem_of_pow_mem_of_pow_three_eq_one {B : Subgroup G} {g : G} (hg : g ^ 3 = 1) {m : ℕ}
    (hm : ¬ 3 ∣ m) (h : g ^ m ∈ B) : g ∈ B := by
  have hmm : m * m % 3 = 1 := by
    have h1 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h1 with h1 | h1 <;> simp [Nat.mul_mod, h1]
  have e : g ^ (m * m) = g := by
    rw [← Nat.div_add_mod (m * m) 3, hmm, pow_add, pow_mul, hg, one_pow, one_mul, pow_one]
  rw [← e, pow_mul]
  exact pow_mem h m

theorem mem_zpowers_of_mem_zpowers_of_pow_three {z a b : G} (hz : z ^ 3 = 1)
    (ha : a ∈ Subgroup.zpowers z) (hb : b ∈ Subgroup.zpowers z) (ha1 : a ≠ 1) (hb1 : b ≠ 1) :
    a ∈ Subgroup.zpowers b := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz1 : z ≠ 1 := fun h1 => ha1 (by
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.mem_bot] at ha
    exact ha)
  have hzo : orderOf z = 3 := orderOf_eq_prime hz hz1
  have hb3 : b ^ 3 = 1 := by
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hle : Subgroup.zpowers b ≤ Subgroup.zpowers z := (Subgroup.zpowers_le).2 hb
  have : Finite (Subgroup.zpowers z) :=
    Nat.finite_of_card_ne_zero (by rw [Nat.card_zpowers, hzo]; norm_num)
  have heq : Subgroup.zpowers b = Subgroup.zpowers z :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hzo, hbo])
  rw [heq]
  exact ha

end Group

namespace EndNodeSUThree

variable {K W : Type*} [Group K] [Group W] [Finite K] [Finite W] {L T U : Subgroup K} {x y : K}
  (h : EndNodeSUThree L T U x y) {π : K →* W} (hπ : Function.Surjective π)
  (hker : π.ker ≤ Subgroup.center K) (hker3 : ∀ c ∈ π.ker, c ^ 3 = 1) {J : Subgroup W}
  (hLJ : L.map π ≤ J) (hTJ : T.map π ≤ J) (hUJ : U.map π ≤ J)
  (hJ : ∀ z ∈ J, ∃ l ∈ L, ∃ t ∈ T, ∃ u ∈ U, z = π (l * t * u))
include h

include hker hLJ hUJ hJ in
theorem exists_normal_three_triple :
    ∃ R V N : Subgroup W, R ≤ N ∧ V ≤ N ∧ N ≤ J ∧ J ≤ Subgroup.normalizer (V : Set W) ∧
      J ≤ Subgroup.normalizer (N : Set W) ∧ Nat.Coprime 3 (Nat.card V) ∧
      (∀ x ∈ N, ∃ e : ℕ, x ^ 3 ^ e ∈ V) ∧ IsPGroup 3 R ∧ ∃ a ∈ R, ∃ b ∈ R, a * b ≠ b * a := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := Subgroup.closure ({x, y} : Set K) with hR
  have hxR : x ∈ R := Subgroup.subset_closure (Set.mem_insert x {y})
  have hyR : y ∈ R := Subgroup.subset_closure (Set.mem_insert_of_mem x rfl)
  refine ⟨R.map π, U.map π, (U ⊔ R).map π, Subgroup.map_mono le_sup_right,
    Subgroup.map_mono le_sup_left, ?_, ?_, ?_, ?_, ?_, h.isPGroup_closure_heis.map π, π x,
    ⟨x, hxR, rfl⟩, π y, ⟨y, hyR, rfl⟩, ?_⟩
  · rw [Subgroup.map_le_iff_le_comap]
    exact sup_le (Subgroup.map_le_iff_le_comap.1 hUJ)
      (h.closure_le_rankOne.trans (Subgroup.map_le_iff_le_comap.1 hLJ))
  · intro z hz
    obtain ⟨l, hl, t, ht, u, hu, rfl⟩ := hJ z hz
    refine Subgroup.le_normalizer_map π ⟨l * t * u, ?_, rfl⟩
    exact mul_mem (mul_mem (h.le_normalizer_unip hl) (h.torus_le_normalizer_unip ht))
      (Subgroup.le_normalizer hu)
  · intro z hz
    obtain ⟨l, hl, t, ht, u, hu, rfl⟩ := hJ z hz
    refine Subgroup.le_normalizer_map π ⟨l * t * u, ?_, rfl⟩
    refine mul_mem (mul_mem ?_ ?_) (Subgroup.le_normalizer (Subgroup.mem_sup_left hu))
    · exact mem_normalizer_join_of_mem (h.le_normalizer_unip hl) (h.le_normalizer hl)
    · exact mem_normalizer_join_of_mem (h.torus_le_normalizer_unip ht)
        (h.mem_normalizer_closure_of_mem_normalizer (h.torus_le_normalizer ht))
  · obtain ⟨k, hk⟩ := (h.isPGroup_unip.map π).exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right _ (by norm_num)
  · rintro _ ⟨g, hg, rfl⟩
    exact ⟨1, by rw [pow_one, ← map_pow]; exact ⟨_, h.pow_three_mem_unip hg, rfl⟩⟩
  · intro hc
    apply h.ne_comm
    have h1 : x * y * (y * x)⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, map_mul, map_mul, hc, mul_inv_cancel]
    have h2 := h.eq_one_of_mem_center _ (hker h1)
      (mul_mem (mul_mem h.x_mem h.y_mem) (inv_mem (mul_mem h.y_mem h.x_mem)))
    exact mul_inv_eq_one.1 h2

omit [Finite W] in
include hker hLJ hTJ in
theorem not_hasThreePair : ¬ HasThreePair J := by
  rintro ⟨N', B', -, -, hJN, hJB, hN3, hBN, hJ2⟩
  obtain ⟨d, hd, q, hq, hdq⟩ := h.exists_comm
  have hdJ : π d ∈ J := hTJ ⟨d, hd, rfl⟩
  obtain ⟨e, he⟩ := hJ2 _ hdJ
  have hdB : π d ∈ B' := mem_of_pow_mem_of_pow_three_eq_one
    (by rw [← map_pow, h.torus_pow d hd, map_one])
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1 (Nat.Coprime.pow_right e (by norm_num)))
    he
  have hqJ : π q ∈ J := hLJ ⟨q, hq, rfl⟩
  have hwB : π (q * d * q⁻¹ * d⁻¹) ∈ B' := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hJB hqJ) _).1 hdB) (inv_mem hdB)
  have hwL : q * d * q⁻¹ * d⁻¹ ∈ L := by
    have h1 : d * q⁻¹ * d⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 (h.torus_le_normalizer hd) _).1 (inv_mem hq)
    have h2 := mul_mem hq h1
    rwa [← mul_assoc, ← mul_assoc] at h2
  obtain ⟨e', he'⟩ := hBN _ hwB
  have hN'L : ∀ m ∈ L, π m ∈ N' → m = 1 := by
    intro m hmL hmN
    refine h.eq_one_of_mem_of_le_normalizer (M := N'.comap π) (fun l hl => ?_) ?_ hmN hmL
    · refine Subgroup.mem_normalizer_fintype fun m hm => ?_
      change π (l * m * l⁻¹) ∈ N'
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 (hJN (hLJ ⟨l, hl, rfl⟩)) _).1 hm
    · intro m hm hmL hm3
      have h1 : π m = 1 := eq_one_of_mem_of_coprime_three hN3 hm (e := 1)
        (by rw [pow_one, ← map_pow, hm3, map_one])
      exact h.eq_one_of_mem_center m (hker h1) hmL
  have hw3e : (q * d * q⁻¹ * d⁻¹) ^ 3 ^ e' = 1 :=
    hN'L _ (pow_mem hwL _) (by rw [map_pow]; exact he')
  exact hdq (h.pow_three_of_pow_eq_one hwL hw3e)

include hπ hker hker3 hLJ hTJ hUJ hJ in
theorem inf_zpowers_ne_bot : ∀ u ∈ J, ∀ v ∈ J, orderOf u = 9 → orderOf v = 9 → Commute u v →
    Subgroup.zpowers u ⊓ Subgroup.zpowers v ≠ ⊥ := by
  intro u hu v hv hu9 hv9 huv
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set R := Subgroup.closure ({x, y} : Set K) with hR
  set P := J.comap π with hP
  have hLP : L ≤ P := Subgroup.map_le_iff_le_comap.1 hLJ
  have hKP : π.ker ≤ P := fun c hc => by
    rw [hP, Subgroup.mem_comap, MonoidHom.mem_ker.1 hc]
    exact one_mem _
  have hT'P : T ⊔ π.ker ≤ P := sup_le (Subgroup.map_le_iff_le_comap.1 hTJ) hKP
  have hCP : (T ⊔ π.ker) ⊔ R ≤ P := sup_le hT'P (h.closure_le_rankOne.trans hLP)
  have hprod : ∀ p ∈ P, ∃ a ∈ (T ⊔ π.ker) ⊔ L, ∃ b ∈ U, p = a * b := by
    intro p hp
    obtain ⟨l, hl, t, ht, w, hw, he⟩ := hJ (π p) hp
    have hcK : (l * t * w)⁻¹ * p ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, ← he, inv_mul_cancel]
    have hcw := Subgroup.mem_center_iff.1 (hker hcK) w
    refine ⟨l * (t * ((l * t * w)⁻¹ * p)), mul_mem (Subgroup.mem_sup_right hl)
      (Subgroup.mem_sup_left (mul_mem (Subgroup.mem_sup_left ht) (Subgroup.mem_sup_right hcK))),
      w, hw, ?_⟩
    calc p = l * t * (w * ((l * t * w)⁻¹ * p)) := by group
      _ = l * (t * ((l * t * w)⁻¹ * p)) * w := by rw [hcw]; group
  have hdvd1 := ParabPrime.card_dvd_mul_of_forall_mem_mul (sup_le hT'P hLP)
    (Subgroup.map_le_iff_le_comap.1 hUJ) hprod
  rw [h.card_sup_rankOne hker hker3] at hdvd1
  obtain ⟨a, ha⟩ := h.isPGroup_unip.exists_card_eq
  have hdvd : Nat.card P ∣ 2 ^ (a + 3) * Nat.card ↥((T ⊔ π.ker) ⊔ R) := by
    refine hdvd1.trans (dvd_of_eq ?_)
    rw [ha, pow_add]
    ring
  have hu3 : IsPGroup 3 (Subgroup.zpowers u) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hu9]; norm_num)
  have hv3 : IsPGroup 3 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 2) (by rw [Nat.card_zpowers, hv9]; norm_num)
  have huvN : Subgroup.zpowers u ≤ Subgroup.normalizer (Subgroup.zpowers v : Set W) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_normalizer_fintype fun s hs => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hs
    rw [(huv.zpow_right k).eq, mul_inv_cancel_right]
    exact hs
  have hQ₀J : Subgroup.zpowers u ⊔ Subgroup.zpowers v ≤ J :=
    sup_le ((Subgroup.zpowers_le).2 hu) ((Subgroup.zpowers_le).2 hv)
  have hK3 : IsPGroup 3 π.ker := fun c => ⟨1, Subtype.ext (by simpa using hker3 c c.2)⟩
  have hQ3 := (hu3.to_sup_of_normal_right' hv3 huvN).comap_of_ker_isPGroup π hK3
  obtain ⟨g, -, hg⟩ := exists_conj_mem_of_card_dvd_two_pow hCP hdvd (Subgroup.comap_mono hQ₀J) hQ3
  have hz3 : π ⁅x, y⁆ ^ 3 = 1 := by rw [← map_pow, h.cubeRel.commutator_pow_three, map_one]
  have hcube : ∀ w ∈ Subgroup.zpowers u ⊔ Subgroup.zpowers v,
      (π g)⁻¹ * w ^ 3 * π g ∈ Subgroup.zpowers (π ⁅x, y⁆) := by
    intro w hw
    obtain ⟨w₁, rfl⟩ := hπ w
    obtain ⟨k, hk⟩ :=
      Subgroup.mem_zpowers_iff.1 (h.pow_three_mem_zpowers_commutator hker hker3 (hg w₁ hw))
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← map_zpow, hk, map_pow, map_mul, map_mul, map_inv]
    simp only [pow_succ, pow_zero, one_mul]
    group
  have hu1 : u ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hu9]; norm_num)
  have hv1 : v ^ 3 ≠ 1 := pow_ne_one_of_lt_orderOf (by norm_num) (by rw [hv9]; norm_num)
  have hconj : ∀ w : W, (π g)⁻¹ * w * π g = 1 → w = 1 := fun w hw => by
    calc w = π g * ((π g)⁻¹ * w * π g) * (π g)⁻¹ := by group
      _ = 1 := by rw [hw]; group
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_of_mem_zpowers_of_pow_three hz3
    (hcube u (Subgroup.mem_sup_left (Subgroup.mem_zpowers u)))
    (hcube v (Subgroup.mem_sup_right (Subgroup.mem_zpowers v)))
    (fun h1 => hu1 (hconj _ h1)) (fun h1 => hv1 (hconj _ h1)))
  have huk : (v ^ 3) ^ k = u ^ 3 := by
    have e := conj_zpow (a := (π g)⁻¹) (b := v ^ 3) (i := k)
    rw [inv_inv, hk] at e
    exact (mul_left_cancel (mul_right_cancel e)).symm
  intro hbot
  have hmem : u ^ 3 ∈ Subgroup.zpowers u ⊓ Subgroup.zpowers v :=
    ⟨pow_mem (Subgroup.mem_zpowers u) 3, huk ▸ zpow_mem (pow_mem (Subgroup.mem_zpowers v) 3) k⟩
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hu1 hmem

include hπ hker hker3 hLJ hTJ hUJ hJ in
theorem isThreeExceptional : IsThreeExceptional J :=
  ⟨h.inf_zpowers_ne_bot hπ hker hker3 hLJ hTJ hUJ hJ, h.not_hasThreePair hker hLJ hTJ,
    h.exists_normal_three_triple hker hLJ hUJ hJ⟩

end EndNodeSUThree

end CFSG.AGLEmbedding
