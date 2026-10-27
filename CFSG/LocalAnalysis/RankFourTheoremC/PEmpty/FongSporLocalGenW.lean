module

public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocalGen
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubAbstract

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal

open CFSG.Open Subgroup
open scoped Pointwise

@[expose] def GenW (G : Type) [Group G] (p : ℕ) : Prop :=
  ∃ (z₀ : G) (ns ms : Set G), orderOf z₀ = p ∧
    (∀ n ∈ ns, n ∈ normalizer (zpowers z₀ : Set G)) ∧
    (∀ m ∈ ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z₀ * t = t * z₀ ∧ m * t = t * m) ∧
    closure (ns ∪ ms) = ⊤

@[expose] def SecW (G : Type) [Group G] (p : ℕ) : Prop :=
  ∃ (z₀ : G) (ns ms : Set G) (H : Subgroup G), orderOf z₀ = p ∧
    (∀ n ∈ ns, n ∈ normalizer (zpowers z₀ : Set G)) ∧
    (∀ m ∈ ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z₀ * t = t * z₀ ∧ m * t = t * m) ∧
    H ≤ closure (ns ∪ ms) ∧ IsSimpleGroup H ∧ ¬ IsMulCommutative H ∧ z₀ ∈ H ∧ 3 ∣ Nat.card H

theorem coe_zpowers_eq_image {N G : Type} [Group N] [Group G] (f : N ≃* G) (z : N) :
    ((zpowers (f z) : Subgroup G) : Set G) = f '' (zpowers z : Set N) := by
  ext a
  constructor
  · intro ha
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp ha
    exact ⟨z ^ k, mem_zpowers_iff.mpr ⟨k, rfl⟩, by rw [map_zpow]; exact hk⟩
  · rintro ⟨b, hb, rfl⟩
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hb
    exact mem_zpowers_iff.mpr ⟨k, by rw [← hk, map_zpow]⟩

theorem mem_normalizer_image_of_mem {N G : Type} [Group N] [Group G] (f : N ≃* G) {S : Set N}
    {x : N} (hx : x ∈ normalizer S) : f x ∈ normalizer (f '' S) := by
  rw [mem_set_normalizer_iff] at hx ⊢
  intro h
  obtain ⟨y, rfl⟩ := f.surjective h
  simp only [← map_mul, ← map_inv, f.injective.mem_set_image]
  exact hx y

theorem mem_normalizer_zpowers_map {N G : Type} [Group N] [Group G] (f : N ≃* G) {z x : N}
    (hx : x ∈ normalizer (zpowers z : Set N)) : f x ∈ normalizer (zpowers (f z) : Set G) := by
  rw [coe_zpowers_eq_image]
  exact mem_normalizer_image_of_mem f hx

theorem closure_image_eq_map {N G : Type} [Group N] [Group G] (f : N ≃* G) (S : Set N) :
    closure (f '' S) = (closure S).map f.toMonoidHom :=
  (MonoidHom.map_closure f.toMonoidHom S).symm

theorem closure_image_eq_top {N G : Type} [Group N] [Group G] (f : N ≃* G) {S : Set N}
    (h : closure S = ⊤) : closure (f '' S) = ⊤ := by
  rw [closure_image_eq_map, h]
  exact Subgroup.map_top_of_surjective f.toMonoidHom f.surjective

theorem commute_of_mem_zpowers {G : Type} [Group G] {x y t : G} (hy : y ∈ zpowers x)
    (hc : x * t = t * x) : y * t = t * y := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  exact Commute.zpow_left (show Commute x t from hc) k

theorem exists_sylow_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) {z : G} (hz : orderOf z = p) :
    ∃ P : Sylow p G, P.toSubgroup = zpowers z := by
  haveI : Fact p.Prime := ⟨hp⟩
  refine ⟨⟨zpowers z, IsPGroup.of_card (n := 1) ?_, ?_⟩, rfl⟩
  · rw [Nat.card_zpowers, hz, pow_one]
  · intro Q hQ hle
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ
    have hdvd : Nat.card Q ∣ Nat.card G := Subgroup.card_subgroup_dvd_card Q
    have hk1 : k ≤ 1 := by
      by_contra hk2
      apply hsyl
      have h2 : p ^ 2 ∣ p ^ k := pow_dvd_pow p (by omega)
      rw [hk] at hdvd
      exact h2.trans hdvd
    have hle' : Nat.card Q ≤ Nat.card (zpowers z) := by
      rw [Nat.card_zpowers, hz, hk]
      calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos hk1
        _ = p := pow_one p
    exact (Subgroup.eq_of_le_of_card_ge hle hle').symm

theorem exists_conj_zpowers {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) {z z' : G} (hz : orderOf z = p) (hz' : orderOf z' = p) :
    ∃ g : G, g * z * g⁻¹ ∈ zpowers z' := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Finite (Sylow p G) :=
    Finite.of_injective (fun P : Sylow p G => (P : Set G)) SetLike.coe_injective
  obtain ⟨P, hP⟩ := exists_sylow_zpowers hp hsyl hz
  obtain ⟨Q, hQ⟩ := exists_sylow_zpowers hp hsyl hz'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G P Q
  refine ⟨g, ?_⟩
  have hconj : MulAut.conj g • (zpowers z : Subgroup G) = zpowers z' := by
    rw [← hP, ← Sylow.coe_subgroup_smul, hg, hQ]
  have h1 := smul_mem_pointwise_smul z (MulAut.conj g) (zpowers z : Subgroup G) (mem_zpowers z)
  rw [hconj] at h1
  exact h1

theorem exists_mulEquiv_zpowers {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) {z z₀ : G} (hz : orderOf z = p) (hz₀ : orderOf z₀ = p) :
    ∃ c : G ≃* G, zpowers (c z₀) = zpowers z := by
  obtain ⟨g, hg⟩ := exists_conj_zpowers hp hsyl hz hz₀
  refine ⟨MulAut.conj g⁻¹, ?_⟩
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp hg
  have hcz : MulAut.conj g⁻¹ (g * z * g⁻¹) = z := by
    rw [MulAut.conj_apply, inv_inv]
    group
  have hpow : (MulAut.conj g⁻¹ z₀) ^ k = z := by
    rw [← map_zpow (MulAut.conj g⁻¹) z₀ k, hk, hcz]
  have hle : zpowers z ≤ zpowers (MulAut.conj g⁻¹ z₀) :=
    zpowers_le.mpr (mem_zpowers_iff.mpr ⟨k, hpow⟩)
  have hord : orderOf (MulAut.conj g⁻¹ z₀) = p := by
    rw [← hz₀]
    exact orderOf_injective (MulAut.conj g⁻¹).toMonoidHom (MulAut.conj g⁻¹).injective z₀
  have hcard : Nat.card (zpowers (MulAut.conj g⁻¹ z₀)) ≤ Nat.card (zpowers z) :=
    le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hz])
  exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm

theorem GenW.of_mulEquiv {N G : Type} [Group N] [Group G] (f : N ≃* G) {p : ℕ} (h : GenW N p) :
    GenW G p := by
  obtain ⟨z₀, ns, ms, hord, hns, hms, hgen⟩ := h
  unfold GenW
  refine ⟨f z₀, f '' ns, f '' ms, ?_, ?_, ?_, ?_⟩
  · exact (orderOf_injective f.toMonoidHom f.injective z₀).trans hord
  · rintro _ ⟨n, hn, rfl⟩
    exact mem_normalizer_zpowers_map f (hns n hn)
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨t, ht2, ht1, hzt, hmt⟩ := hms m hm
    refine ⟨f t, by rw [← map_mul, ht2, map_one],
      fun h => ht1 (f.injective (h.trans (map_one f).symm)), ?_, ?_⟩
    · rw [← map_mul, ← map_mul, hzt]
    · rw [← map_mul, ← map_mul, hmt]
  · rw [← Set.image_union]
    exact closure_image_eq_top f hgen

theorem SecW.of_mulEquiv {N G : Type} [Group N] [Group G] (f : N ≃* G) {p : ℕ} (h : SecW N p) :
    SecW G p := by
  obtain ⟨z₀, ns, ms, H, hord, hns, hms, hHle, hsimp, hnc, hz₀H, h3⟩ := h
  unfold SecW
  refine ⟨f z₀, f '' ns, f '' ms, H.map f.toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (orderOf_injective f.toMonoidHom f.injective z₀).trans hord
  · rintro _ ⟨n, hn, rfl⟩
    exact mem_normalizer_zpowers_map f (hns n hn)
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨t, ht2, ht1, hzt, hmt⟩ := hms m hm
    refine ⟨f t, by rw [← map_mul, ht2, map_one],
      fun h => ht1 (f.injective (h.trans (map_one f).symm)), ?_, ?_⟩
    · rw [← map_mul, ← map_mul, hzt]
    · rw [← map_mul, ← map_mul, hmt]
  · rw [← Set.image_union, closure_image_eq_map]
    exact Subgroup.map_mono hHle
  · exact (MulEquiv.isSimpleGroup_congr (H.equivMapOfInjective f.toMonoidHom f.injective)).mp hsimp
  · intro h
    apply hnc
    rw [isMulCommutative_iff] at h ⊢
    intro a b
    apply (H.equivMapOfInjective f.toMonoidHom f.injective).injective
    rw [map_mul, map_mul]
    exact h _ _
  · exact Subgroup.mem_map_of_mem _ hz₀H
  · have hcard := Nat.card_congr (H.equivMapOfInjective f.toMonoidHom f.injective).toEquiv
    rw [← hcard]
    exact h3

theorem exists_witness_for {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hW : GenW G p) {z : G} (hz : orderOf z = p) :
    ∃ ns ms : Set G, (∀ n ∈ ns, n ∈ normalizer (zpowers z : Set G)) ∧
      (∀ m ∈ ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z * t = t * z ∧ m * t = t * m) ∧
      closure (ns ∪ ms) = ⊤ := by
  obtain ⟨z₀, ns, ms, hord, hns, hms, hgen⟩ := hW
  obtain ⟨c, hzc⟩ := exists_mulEquiv_zpowers hp hsyl hz hord
  refine ⟨c '' ns, c '' ms, ?_, ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    rw [← hzc]
    exact mem_normalizer_zpowers_map c (hns n hn)
  · rintro _ ⟨m, hm, rfl⟩
    obtain ⟨t, ht2, ht1, hzt, hmt⟩ := hms m hm
    refine ⟨c t, by rw [← map_mul, ht2, map_one],
      fun h => ht1 (c.injective (h.trans (map_one c).symm)), ?_, ?_⟩
    · refine commute_of_mem_zpowers (x := c z₀) ?_ ?_
      · rw [hzc]
        exact mem_zpowers z
      · rw [← map_mul, ← map_mul, hzt]
    · rw [← map_mul, ← map_mul, hmt]
  · rw [← Set.image_union]
    exact closure_image_eq_top c hgen

theorem false_of_genW {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hW : GenW G p) {K : Subgroup G} {z : G} (hz : orderOf z = p)
    (hzK : z ∈ K) (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K) (hK : K ≠ ⊤) : False := by
  obtain ⟨ns, ms, hns, hms, hgen⟩ := exists_witness_for hp hsyl hW hz
  exact hK (eq_top_of_gen hN hcl hns hms hgen)

theorem kxSection_of_secW {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    (hsyl : ¬ p ^ 2 ∣ Nat.card G) (hW : SecW G p) {K : Subgroup G} {z : G} (hz : orderOf z = p)
    (hzK : z ∈ K) (hN : normalizer (zpowers z : Set G) ≤ K)
    (hcl : ∀ U : Subgroup G, IsPGroup 2 U → z ∈ normalizer (U : Set G) → U ⊓ K ≠ ⊥ →
      normalizer (U : Set G) ≤ K) : KxSection z K 3 := by
  obtain ⟨z₀, ns, ms, H, hord, hns, hms, hHle, hsimp, hnc, hz₀H, h3⟩ := hW
  obtain ⟨c, hzc⟩ := exists_mulEquiv_zpowers hp hsyl hz hord
  have hns' : ∀ n ∈ c '' ns, n ∈ normalizer (zpowers z : Set G) := by
    rintro _ ⟨n, hn, rfl⟩
    rw [← hzc]
    exact mem_normalizer_zpowers_map c (hns n hn)
  have hms' : ∀ m ∈ c '' ms, ∃ t : G, t * t = 1 ∧ t ≠ 1 ∧ z * t = t * z ∧ m * t = t * m := by
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨t, ht2, ht1, hzt, hmt⟩ := hms m hm
    refine ⟨c t, by rw [← map_mul, ht2, map_one],
      fun h => ht1 (c.injective (h.trans (map_one c).symm)), ?_, ?_⟩
    · refine commute_of_mem_zpowers (x := c z₀) ?_ ?_
      · rw [hzc]
        exact mem_zpowers z
      · rw [← map_mul, ← map_mul, hzt]
    · rw [← map_mul, ← map_mul, hmt]
  have hH'K : H.map c.toMonoidHom ≤ K := by
    have h1 : H.map c.toMonoidHom ≤ closure (c '' ns ∪ c '' ms) := by
      rw [← Set.image_union, closure_image_eq_map]
      exact Subgroup.map_mono hHle
    exact h1.trans (closure_le_of_gen hN hcl hns' hms')
  have hsimp' : IsSimpleGroup (H.map c.toMonoidHom) :=
    (MulEquiv.isSimpleGroup_congr (H.equivMapOfInjective c.toMonoidHom c.injective)).mp hsimp
  have hnc' : ¬ IsMulCommutative (H.map c.toMonoidHom) := by
    intro h
    apply hnc
    rw [isMulCommutative_iff] at h ⊢
    intro a b
    apply (H.equivMapOfInjective c.toMonoidHom c.injective).injective
    rw [map_mul, map_mul]
    exact h _ _
  have hnab : ∃ a b : ↥(H.map c.toMonoidHom), a * b ≠ b * a := by
    by_contra hcon
    exact hnc' (isMulCommutative_iff.mpr fun a b => by_contra fun hab => hcon ⟨a, b, hab⟩)
  have hS : S622IsSimpleSection (H.map c.toMonoidHom) (⊥ : Subgroup G) := by
    haveI := hsimp'
    have h := CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.S622IsSimpleSection.of_surjective
      (MonoidHom.id ↥(H.map c.toMonoidHom)) Function.surjective_id hnab
    rwa [(MonoidHom.ker_eq_bot_iff (MonoidHom.id ↥(H.map c.toMonoidHom))).mpr
      Function.injective_id, Subgroup.map_bot] at h
  have hzH' : z ∈ H.map c.toMonoidHom := by
    have h1 : c z₀ ∈ H.map c.toMonoidHom := Subgroup.mem_map_of_mem _ hz₀H
    have h2 : zpowers (c z₀) ≤ H.map c.toMonoidHom := zpowers_le.mpr h1
    exact h2 (by rw [hzc]; exact mem_zpowers z)
  have hz1 : z ∉ (⊥ : Subgroup G) := by
    intro hmem
    rw [Subgroup.mem_bot] at hmem
    rw [hmem, orderOf_one] at hz
    have := hp.one_lt
    omega
  have h3' : 3 ∣ (⊥ : Subgroup G).relIndex (H.map c.toMonoidHom) := by
    rw [Subgroup.relIndex_bot_left,
      ← Nat.card_congr (H.equivMapOfInjective c.toMonoidHom c.injective).toEquiv]
    exact h3
  unfold KxSection
  exact ⟨H.map c.toMonoidHom, ⊥, hH'K, hS, hzH', hz1, h3'⟩

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.FongSporLocal
