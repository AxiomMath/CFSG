module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFour

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag
open scoped commutatorElement

theorem exists_fin_ne_three {n : ℕ} (hn : 4 ≤ n) (i j l : Fin n) :
    ∃ m : Fin n, m ≠ i ∧ m ≠ j ∧ m ≠ l := by
  classical
  by_contra h
  push Not at h
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j, l} := fun m _ => by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    by_cases hi : m = i
    · exact Or.inl hi
    by_cases hj : m = j
    · exact Or.inr (Or.inl hj)
    exact Or.inr (Or.inr (h m hi hj))
  have h3 := (Finset.card_le_card hsub).trans Finset.card_le_three
  rw [Finset.card_univ, Fintype.card_fin] at h3
  omega

section RootHom

variable {K : Type*} [Field K] {n : ℕ} {G E : Type*} [Group G] [Group E]
  (ρ : SpecialLinearGroup (Fin n) K →* G) (η : E →* G) (hker : ∀ z, η z = 1 → z ∈ center E)
  (hη : Function.Surjective η)
include hker hη

theorem lift_rootHom_mul_comm_of_diag {s : Fin n → K} (hs : ∏ i, s i = 1) {i j k l : Fin n}
    (hjk : j ≠ k) (hli : l ≠ i) (hij : s i ≠ s j) (hkl : s k = s l) {e e' : E} {a b : K}
    (he : η e = ρ (rootElt i j a)) (he' : η e' = ρ (rootElt k l b)) : e * e' = e' * e := by
  have hs0 := ne_zero_of_prod_eq_one hs
  have hx : ∀ a b, ρ (rootElt i j (a + b)) = ρ (rootElt i j a) * ρ (rootElt i j b) :=
    fun a b => by rw [rootElt_add, map_mul]
  have hxy : ∀ a b, ρ (rootElt i j a) * ρ (rootElt k l b) =
      ρ (rootElt k l b) * ρ (rootElt i j a) := fun a b => by
    rw [← map_mul, ← map_mul, rootElt_mul_comm hjk hli]
  have htx : ∀ a, ρ (diagElt s hs) * ρ (rootElt i j a) * (ρ (diagElt s hs))⁻¹ =
      ρ (rootElt i j (s i * (s j)⁻¹ * a)) := fun a => by
    rw [← map_inv, ← map_mul, ← map_mul, diagElt_conj_rootElt]
  have hty : ∀ b, ρ (diagElt s hs) * ρ (rootElt k l b) * (ρ (diagElt s hs))⁻¹ =
      ρ (rootElt k l b) := fun b => by
    rw [← map_inv, ← map_mul, ← map_mul, diagElt_conj_rootElt, hkl, mul_inv_cancel₀ (hs0 l),
      one_mul]
  exact lift_mul_comm_of_torus η hker hη (x := fun a => ρ (rootElt i j a))
    (y := fun b => ρ (rootElt k l b)) hx hxy (t := ρ (diagElt s hs)) (r := s i * (s j)⁻¹)
    (fun h => hij ((mul_inv_eq_one₀ (hs0 j)).mp h)) htx hty he he'

variable [CharP K 2] (hn : 4 ≤ n) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
include hn hc0 hc1

theorem lift_rootHom_mul_comm_of_ne {i j k l : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hli : l ≠ i)
    (hne : (i, j) ≠ (k, l)) {e e' : E} {a b : K} (he : η e = ρ (rootElt i j a))
    (he' : η e' = ρ (rootElt k l b)) : e * e' = e' * e := by
  by_cases hik : i = k
  ·
    have hjl : j ≠ l := fun h => hne (by rw [hik, h])
    obtain ⟨m, hmi, hmj, hml⟩ := exists_fin_ne_three hn i j l
    refine lift_rootHom_mul_comm_of_diag ρ η hker hη (prod_corootVec j m hc0) hjk hli ?_ ?_
      he he'
    · rw [corootVec_apply_of_ne hij (Ne.symm hmi), corootVec_apply_left (Ne.symm hmj)]
      exact Ne.symm hc1
    · rw [← hik, corootVec_apply_of_ne hij (Ne.symm hmi),
        corootVec_apply_of_ne (Ne.symm hjl) (Ne.symm hml)]
  by_cases hjl : j = l
  ·
    obtain ⟨m, hmi, hmk, hmj⟩ := exists_fin_ne_three hn i k j
    refine lift_rootHom_mul_comm_of_diag ρ η hker hη (prod_corootVec i m hc0) hjk hli ?_ ?_
      he he'
    · rw [corootVec_apply_left (Ne.symm hmi), corootVec_apply_of_ne (Ne.symm hij) (Ne.symm hmj)]
      exact hc1
    · rw [← hjl, corootVec_apply_of_ne (Ne.symm hik) (Ne.symm hmk),
        corootVec_apply_of_ne (Ne.symm hij) (Ne.symm hmj)]
  refine lift_rootHom_mul_comm_of_diag ρ η hker hη (prod_corootVec i j hc0) hjk hli ?_ ?_ he he'
  · rw [corootVec_apply_left hij, corootVec_apply_right hij]
    intro h
    apply mul_self_ne_one hc1
    calc c * c = c * c⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ hc0
  · rw [corootVec_apply_of_ne (Ne.symm hik) (Ne.symm hjk),
      corootVec_apply_of_ne hli (Ne.symm hjl)]

theorem lift_rootHom_mul_comm_self {i j : Fin n} (hij : i ≠ j) {e e' : E} {a b : K}
    (he : η e = ρ (rootElt i j a)) (he' : η e' = ρ (rootElt i j b)) : e * e' = e' * e := by
  obtain ⟨m, hmi, hmj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by omega)
  obtain ⟨p, hp⟩ := hη (ρ (rootElt i m a))
  obtain ⟨q, hq⟩ := hη (ρ (rootElt m j 1))
  have h1 : Commute e' p := lift_rootHom_mul_comm_of_ne ρ η hker hη hn hc0 hc1 hij (Ne.symm hij)
    hmi (fun h => hmj (Prod.mk.inj h).2.symm) he' hp
  have h2 : Commute e' q := lift_rootHom_mul_comm_of_ne ρ η hker hη hn hc0 hc1 hij (Ne.symm hmj)
    (Ne.symm hij) (fun h => hmi (Prod.mk.inj h).1.symm) he' hq
  have hw : Commute e' ⁅p, q⁆ := by
    rw [commutatorElement_def]
    exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
  have hζ : ⁅p, q⁆⁻¹ * e ∈ center E := hker _ (by
    rw [map_mul, map_inv, map_commutatorElement, hp, hq, ← map_commutatorElement,
      commutatorElement_rootElt (Ne.symm hmi) hmj hij, mul_one, he, inv_mul_cancel])
  calc e * e' = ⁅p, q⁆ * (⁅p, q⁆⁻¹ * e) * e' := by group
    _ = ⁅p, q⁆ * e' * (⁅p, q⁆⁻¹ * e) := by
        rw [mul_assoc, ← mem_center_iff.mp hζ e', ← mul_assoc]
    _ = e' * ⁅p, q⁆ * (⁅p, q⁆⁻¹ * e) := by rw [hw.eq]
    _ = e' * e := by group

theorem lift_rootHom_mul_comm {i j k l : Fin n} (hij : i ≠ j) (hjk : j ≠ k) (hli : l ≠ i)
    {e e' : E} {a b : K} (he : η e = ρ (rootElt i j a)) (he' : η e' = ρ (rootElt k l b)) :
    e * e' = e' * e := by
  by_cases hne : (i, j) = (k, l)
  · rw [Prod.mk.injEq] at hne
    rw [← hne.1, ← hne.2] at he'
    exact lift_rootHom_mul_comm_self ρ η hker hη hn hc0 hc1 hij he he'
  · exact lift_rootHom_mul_comm_of_ne ρ η hker hη hn hc0 hc1 hij hjk hli hne he he'

theorem exists_rootHom_lift (i j : Fin n) :
    ∃ xl : K → E, (∀ a, η (xl a) = ρ (rootElt i j a)) ∧ (∀ a b, xl (a + b) = xl a * xl b) ∧
      ∀ (g : E) (s : Fin n → K) (hs : ∏ r, s r = 1), η g = ρ (diagElt s hs) →
        ∀ a, g * xl a * g⁻¹ = xl (s i * (s j)⁻¹ * a) := by
  by_cases hij : i = j
  · refine ⟨fun _ => 1, fun a => ?_, fun a b => (mul_one 1).symm, fun g s hs _ a => ?_⟩
    · change η 1 = ρ (rootElt i j a)
      rw [map_one, hij, rootElt_self, map_one]
    · change g * 1 * g⁻¹ = 1
      rw [mul_one, mul_inv_cancel]
  have hx : ∀ a b, ρ (rootElt i j (a + b)) = ρ (rootElt i j a) * ρ (rootElt i j b) :=
    fun a b => by rw [rootElt_add, map_mul]
  have ht₀ : ∀ a, ρ (diagElt (corootVec i j c) (prod_corootVec i j hc0)) * ρ (rootElt i j a) *
      (ρ (diagElt (corootVec i j c) (prod_corootVec i j hc0)))⁻¹ = ρ (rootElt i j (c * c * a)) :=
    fun a => by
      rw [← map_inv, ← map_mul, ← map_mul, diagElt_conj_rootElt, corootVec_apply_left hij,
        corootVec_apply_right hij, inv_inv]
  obtain ⟨xl, hxl, hadd, hconj⟩ := exists_torus_lift η hker hη (x := fun a => ρ (rootElt i j a))
    hx (fun e e' a b he he' => lift_rootHom_mul_comm ρ η hker hη hn hc0 hc1 hij (Ne.symm hij)
      (Ne.symm hij) he he') (mul_self_ne_one hc1) ht₀
  refine ⟨xl, hxl, hadd, fun g s hs hg a => hconj g _ ?_ (fun a => ?_) a⟩
  · rw [hg, ← map_mul, ← map_mul, diagElt_mul_comm]
  · rw [hg, ← map_inv, ← map_mul, ← map_mul, diagElt_conj_rootElt]

end RootHom

theorem ker_eq_bot_of_rootHom {K : Type*} [Field K] [Finite K] [CharP K 2] (hK : 3 ≤ Nat.card K)
    {n : ℕ} (hn : 4 ≤ n) {G : Type*} [Group G] (ρ : SpecialLinearGroup (Fin n) K →* G)
    (hρ : ∀ u ∈ unitriangular n K, ρ u = 1 → u = 1) (S : Sylow 2 G)
    (hS : (S : Subgroup G) ≤ (unitriangular n K).map ρ) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* G) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hC hz
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_three_le hK
  choose xl hxl hadd hconj using fun i j => exists_rootHom_lift ρ η hker hη hn hc0 hc1 i j
  have hrel : ∀ i j l : Fin n, i ≠ j → j ≠ l → i ≠ l → ∀ a b,
      ⁅xl i j a, xl j l b⁆ = xl i l (a * b) := by
    intro i j l hij hjl hil a b
    obtain ⟨m, hmi, hmj, hml⟩ := exists_fin_ne_three hn i j l
    obtain ⟨g, hg⟩ := hη (ρ (diagElt (corootVec i m c) (prod_corootVec i m hc0)))
    have hsi : corootVec i m c i = c := corootVec_apply_left (Ne.symm hmi) c
    have hsj : corootVec i m c j = 1 := corootVec_apply_of_ne (Ne.symm hij) (Ne.symm hmj) c
    have hsl : corootVec i m c l = 1 := corootVec_apply_of_ne (Ne.symm hil) (Ne.symm hml) c
    have hxyz : ∀ a b, ⁅ρ (rootElt i j a), ρ (rootElt j l b)⁆ = ρ (rootElt i l (a * b)) :=
      fun a b => by rw [← map_commutatorElement, commutatorElement_rootElt hij hjl hil]
    refine commutatorElement_lift_eq_of_torus η hker (x := fun a => ρ (rootElt i j a))
      (y := fun b => ρ (rootElt j l b)) (z := fun c => ρ (rootElt i l c)) (hxl i j) (hxl j l)
      (hxl i l) (hadd i j) (hadd i l) hxyz
      (fun a e c' he => lift_rootHom_mul_comm ρ η hker hη hn hc0 hc1 hij (Ne.symm hij)
        (Ne.symm hil) (hxl i j a) he)
      (fun e e' c' c'' he he' => lift_rootHom_mul_comm ρ η hker hη hn hc0 hc1 hil (Ne.symm hil)
        (Ne.symm hil) he he')
      hc1 (g := g) (fun a => ?_) (fun b => ?_) (fun c' => ?_) a b
    · rw [hconj i j g _ _ hg, hsi, hsj, inv_one, mul_one]
    · rw [hconj j l g _ _ hg, hsj, hsl, inv_one, mul_one, one_mul]
    · rw [hconj i l g _ _ hg, hsi, hsl, inv_one, mul_one]
  let M : Fin n → Fin n → Subgroup E := fun i j =>
    (MonoidHom.mk' (fun a : Multiplicative K => xl i j a.toAdd) fun a b => hadd i j _ _).range
  have hmemM : ∀ i j a, xl i j a ∈ M i j := fun i j a => ⟨Multiplicative.ofAdd a, rfl⟩
  have hmem : ∀ i j x, x ∈ M i j → ∃ a, xl i j a = x := fun i j x ⟨a, ha⟩ => ⟨a.toAdd, ha⟩
  have hMcard : ∀ i j, Nat.card (M i j) ≤ Nat.card K := fun i j =>
    (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)).trans_eq
      (Nat.card_congr Multiplicative.toAdd)
  set P₀ := closure {g | ∃ i j, i < j ∧ g ∈ M i j} with hP₀
  have hcount : Nat.card P₀ ≤ Nat.card K ^ (n * (n - 1) / 2) :=
    card_closure_le_of_root_subgroups M (fun i j _ => hMcard i j)
      (fun i j k l hij _ hjk hil _ x hx y hy => by
        obtain ⟨a, rfl⟩ := hmem i j x hx
        obtain ⟨b, rfl⟩ := hmem k l y hy
        exact lift_rootHom_mul_comm ρ η hker hη hn hc0 hc1 hij.ne hjk (Ne.symm hil) (hxl i j a)
          (hxl k l b))
      (fun i j l hij hjl x hx y hy => by
        obtain ⟨a, rfl⟩ := hmem i j x hx
        obtain ⟨b, rfl⟩ := hmem j l y hy
        rw [hrel i j l hij.ne hjl.ne (hij.trans hjl).ne a b]
        exact hmemM i l _)
  have hmap : (unitriangular n K).map ρ ≤ P₀.map η := by
    refine (map_mono unitriangular_le_closure_rootElt).trans ?_
    rw [MonoidHom.map_closure, hP₀, MonoidHom.map_closure]
    refine closure_mono ?_
    rintro _ ⟨_, ⟨i, j, a, hij, rfl⟩, rfl⟩
    exact ⟨xl i j a, ⟨i, j, hij, hmemM i j a⟩, hxl i j a⟩
  have hUρ : Nat.card ((unitriangular n K).map ρ) = Nat.card (unitriangular n K) := by
    refine (Nat.card_congr (Equiv.ofBijective (ρ.subgroupMap (unitriangular n K))
      ⟨fun u v huv => Subtype.ext ?_, ρ.subgroupMap_surjective (unitriangular n K)⟩)).symm
    have h1 : ρ ((u : SpecialLinearGroup (Fin n) K)⁻¹ * v) = 1 := by
      rw [map_mul, map_inv, inv_mul_eq_one]
      exact congrArg Subtype.val huv
    exact inv_mul_eq_one.mp (hρ _ (mul_mem (inv_mem u.2) v.2) h1)
  have : Finite (P₀.map η) := Finite.of_surjective _ (η.subgroupMap_surjective P₀)
  have hbij : Function.Bijective (η.subgroupMap P₀) := by
    refine (η.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ Nat.card K ^ (n * (n - 1) / 2) := hcount
      _ = Nat.card ((unitriangular n K).map ρ) := by rw [hUρ, card_unitriangular]
      _ ≤ Nat.card (P₀.map η) := Subgroup.card_le_of_le hmap
  have hinj : ∀ z ∈ P₀, η z = 1 → z = 1 := by
    intro z hz hz1
    have h : η.subgroupMap P₀ ⟨z, hz⟩ = η.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hz1)
    exact congrArg Subtype.val (hbij.1 h)
  exact ker_eq_bot_of_sylow_le_map η hη hC h2 S P₀ (hS.trans hmap) hinj

theorem ker_eq_bot_of_specialLinear {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 3 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* SpecialLinearGroup (Fin n) K) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  obtain ⟨S, hS⟩ := exists_sylow_unitriangular (K := K) 2 (n := n) (by omega)
  exact ker_eq_bot_of_rootHom hK hn (MonoidHom.id _) (fun _ _ h => h) S
    (by rw [hS, Subgroup.map_id]) η hη hC h2

theorem ker_eq_bot_of_projectiveSL_charTwo {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 3 ≤ Nat.card K) {n : ℕ} (hn : 4 ≤ n) {E : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] (η : E →* projectiveSL n K) (hη : Function.Surjective η)
    (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := n) (by omega)
  exact ker_eq_bot_of_rootHom hK hn (proj n K)
    (fun u hu h => proj_injOn_unitriangular n hu (one_mem _) (h.trans (map_one _).symm)) S
    hS.le η hη hC h2

theorem even_higher_linear_catalog_perfect_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) {n f : ℕ}
    (hn : 4 ≤ n) (hf : 2 ≤ f) (hJ : CFSG.Blueprint.LieModel J .PSL n 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hJ
  have := finite_field_prime_power_characteristic (K := K) Nat.prime_two (by omega) hcard
  have hK : 3 ≤ Nat.card K := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set η' : E →* projectiveSL n K := e.toMonoidHom.comp η
  have hη' : Function.Surjective η' := e.surjective.comp hη
  have hker' : η'.ker = η.ker := by
    ext z
    exact e.map_eq_one_iff
  have hbot := ker_eq_bot_of_projectiveSL_charTwo hK hn η' hη' (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
