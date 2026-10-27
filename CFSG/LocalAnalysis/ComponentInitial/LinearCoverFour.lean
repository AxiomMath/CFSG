module

public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourLift
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverFourRoots
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverModel
public import CFSG.LocalAnalysis.ComponentInitial.LinearCoverDiagonal

public noncomputable section

namespace CFSG.LocalAnalysis.ComponentInitial

namespace LinearCover

open Subgroup Matrix LinearFlag
open scoped commutatorElement

theorem scalars_four_eq_bot (K : Type*) [Field K] [CharP K 2] : scalars 4 K = ⊥ := by
  rw [eq_bot_iff]
  rintro A ⟨c, hc, hA⟩
  rw [Subgroup.mem_bot]
  have hc1 : (c : K) = 1 := by
    have h : ((c : K) - 1) ^ 4 = 0 := by
      have h4 : (c : K) ^ 4 = 1 := by rw [← Units.val_pow_eq_pow_val, hc, Units.val_one]
      linear_combination h4 + (-2 * (c : K) ^ 3 + 3 * (c : K) ^ 2 - 2 * (c : K) + 1) *
        (CharP.cast_eq_zero K 2)
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h)
  apply Subtype.ext
  change (A : Matrix (Fin 4) (Fin 4) K) = 1
  rw [hA, hc1, map_one]

@[expose] def projectiveSLFourEquivSL (K : Type*) [Field K] [CharP K 2] :
    projectiveSL 4 K ≃* SpecialLinearGroup (Fin 4) K :=
  (QuotientGroup.quotientMulEquivOfEq (scalars_four_eq_bot K)).trans QuotientGroup.quotientBot

theorem ker_eq_bot_of_sylow_le_map {E G : Type*} [Group E] [Group G] [Finite E]
    [Group.IsPerfect E] (η : E →* G) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) (S : Sylow 2 G) (P₀ : Subgroup E) (hS : (S : Subgroup G) ≤ P₀.map η)
    (hinj : ∀ z ∈ P₀, η z = 1 → z = 1) : η.ker = ⊥ := by
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hC hz
  have comm_eq : ∀ {a a' b b' : E}, η a = η a' → η b = η b' → ⁅a, b⁆ = ⁅a', b'⁆ :=
    fun ha hb => HeisenbergRoots.commutatorElement_eq_of_map_eq η hker ha hb
  obtain ⟨P, hP, hzP⟩ := exists_sylow_map_eq_twoPart_le η hη hC S
  have hlift : ∀ g ∈ (P : Subgroup E), ∃ p ∈ P₀, η p = η g := fun g hg => by
    have h1 : η g ∈ (P : Subgroup E).map η := mem_map_of_mem η hg
    rw [hP] at h1
    obtain ⟨p, hp, hpg⟩ := mem_map.mp (hS h1)
    exact ⟨p, hp, hpg⟩
  have hPP : ⁅(P : Subgroup E), (P : Subgroup E)⁆ ≤ P₀ := by
    rw [commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨p₁, hp₁, h₁⟩ := hlift g₁ hg₁
    obtain ⟨p₂, hp₂, h₂⟩ := hlift g₂ hg₂
    rw [comm_eq h₁.symm h₂.symm, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hp₁ hp₂) (inv_mem hp₁)) (inv_mem hp₂)
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨k, hk⟩ := h2 ⟨z, hz⟩
  have hk' : z ^ 2 ^ k = 1 := congrArg Subtype.val hk
  exact mem_bot.mpr (hinj z (hPP (hzP z hz ⟨k, hk'⟩)) hz)

theorem exists_fin_four_ne (i j l : Fin 4) : ∃ m : Fin 4, m ≠ i ∧ m ≠ j ∧ m ≠ l := by
  revert i j l
  decide

theorem mul_self_ne_one {K : Type*} [Field K] [CharP K 2] {c : K} (hc : c ≠ 1) : c * c ≠ 1 := by
  intro h
  apply hc
  have h' : (c - 1) ^ 2 = 0 := by
    linear_combination h + (1 - c) * (CharP.cast_eq_zero K 2)
  exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h')

section Diagonal

variable {K : Type*} [Field K] {E : Type*} [Group E] {n : ℕ}
  (η : E →* SpecialLinearGroup (Fin n) K) (hker : ∀ z, η z = 1 → z ∈ center E)
  (hη : Function.Surjective η)
include hker hη

theorem lift_rootElt_mul_comm_of_diag {s : Fin n → K} (hs : ∏ i, s i = 1) {i j k l : Fin n}
    (hjk : j ≠ k) (hli : l ≠ i) (hij : s i ≠ s j) (hkl : s k = s l) {e e' : E} {a b : K}
    (he : η e = rootElt i j a) (he' : η e' = rootElt k l b) : e * e' = e' * e := by
  have hs0 := ne_zero_of_prod_eq_one hs
  refine lift_mul_comm_of_torus η hker hη (x := rootElt i j) (y := rootElt k l)
    (rootElt_add i j) (rootElt_mul_comm hjk hli) (t := diagElt s hs) (r := s i * (s j)⁻¹)
    (fun h => hij ((mul_inv_eq_one₀ (hs0 j)).mp h)) (fun a => diagElt_conj_rootElt s hs i j a)
    (fun b => ?_) he he'
  rw [diagElt_conj_rootElt, hkl, mul_inv_cancel₀ (hs0 l), one_mul]

end Diagonal

section Four

variable {K : Type*} [Field K] [CharP K 2] {E : Type*} [Group E]
  (η : E →* SpecialLinearGroup (Fin 4) K) (hker : ∀ z, η z = 1 → z ∈ center E)
  (hη : Function.Surjective η) {c : K} (hc0 : c ≠ 0) (hc1 : c ≠ 1)
include hker hη hc0 hc1

theorem lift_rootElt_mul_comm_of_ne {i j k l : Fin 4} (hij : i ≠ j) (hjk : j ≠ k) (hli : l ≠ i)
    (hne : (i, j) ≠ (k, l)) {e e' : E} {a b : K} (he : η e = rootElt i j a)
    (he' : η e' = rootElt k l b) : e * e' = e' * e := by
  by_cases hik : i = k
  ·
    have hjl : j ≠ l := fun h => hne (by rw [hik, h])
    obtain ⟨m, hmi, hmj, hml⟩ := exists_fin_four_ne i j l
    refine lift_rootElt_mul_comm_of_diag η hker hη (prod_corootVec j m hc0) hjk hli ?_ ?_ he he'
    · rw [corootVec_apply_of_ne hij (Ne.symm hmi), corootVec_apply_left (Ne.symm hmj)]
      exact Ne.symm hc1
    · rw [← hik, corootVec_apply_of_ne hij (Ne.symm hmi),
        corootVec_apply_of_ne (Ne.symm hjl) (Ne.symm hml)]
  by_cases hjl : j = l
  ·
    obtain ⟨m, hmi, hmk, hmj⟩ := exists_fin_four_ne i k j
    refine lift_rootElt_mul_comm_of_diag η hker hη (prod_corootVec i m hc0) hjk hli ?_ ?_ he he'
    · rw [corootVec_apply_left (Ne.symm hmi), corootVec_apply_of_ne (Ne.symm hij) (Ne.symm hmj)]
      exact hc1
    · rw [← hjl, corootVec_apply_of_ne (Ne.symm hik) (Ne.symm hmk),
        corootVec_apply_of_ne (Ne.symm hij) (Ne.symm hmj)]
  refine lift_rootElt_mul_comm_of_diag η hker hη (prod_corootVec i j hc0) hjk hli ?_ ?_ he he'
  · rw [corootVec_apply_left hij, corootVec_apply_right hij]
    intro h
    apply mul_self_ne_one hc1
    calc c * c = c * c⁻¹ := by rw [← h]
      _ = 1 := mul_inv_cancel₀ hc0
  · rw [corootVec_apply_of_ne (Ne.symm hik) (Ne.symm hjk), corootVec_apply_of_ne hli (Ne.symm hjl)]

theorem lift_rootElt_mul_comm_self {i j : Fin 4} (hij : i ≠ j) {e e' : E} {a b : K}
    (he : η e = rootElt i j a) (he' : η e' = rootElt i j b) : e * e' = e' * e := by
  obtain ⟨m, hmi, hmj⟩ := Fin.exists_ne_and_ne_of_two_lt i j (by norm_num)
  obtain ⟨p, hp⟩ := hη (rootElt i m a)
  obtain ⟨q, hq⟩ := hη (rootElt m j 1)
  have h1 : Commute e' p := lift_rootElt_mul_comm_of_ne η hker hη hc0 hc1 hij (Ne.symm hij) hmi
    (fun h => hmj (Prod.mk.inj h).2.symm) he' hp
  have h2 : Commute e' q := lift_rootElt_mul_comm_of_ne η hker hη hc0 hc1 hij (Ne.symm hmj)
    (Ne.symm hij) (fun h => hmi (Prod.mk.inj h).1.symm) he' hq
  have hw : Commute e' ⁅p, q⁆ := by
    rw [commutatorElement_def]
    exact ((h1.mul_right h2).mul_right h1.inv_right).mul_right h2.inv_right
  have hζ : ⁅p, q⁆⁻¹ * e ∈ center E := hker _ (by
    rw [map_mul, map_inv, map_commutatorElement, hp, hq,
      commutatorElement_rootElt (Ne.symm hmi) hmj hij, mul_one, he, inv_mul_cancel])
  calc e * e' = ⁅p, q⁆ * (⁅p, q⁆⁻¹ * e) * e' := by group
    _ = ⁅p, q⁆ * e' * (⁅p, q⁆⁻¹ * e) := by
        rw [mul_assoc, ← mem_center_iff.mp hζ e', ← mul_assoc]
    _ = e' * ⁅p, q⁆ * (⁅p, q⁆⁻¹ * e) := by rw [hw.eq]
    _ = e' * e := by group

theorem lift_rootElt_mul_comm {i j k l : Fin 4} (hij : i ≠ j) (hjk : j ≠ k) (hli : l ≠ i)
    {e e' : E} {a b : K} (he : η e = rootElt i j a) (he' : η e' = rootElt k l b) :
    e * e' = e' * e := by
  by_cases hne : (i, j) = (k, l)
  · rw [Prod.mk.injEq] at hne
    rw [← hne.1, ← hne.2] at he'
    exact lift_rootElt_mul_comm_self η hker hη hc0 hc1 hij he he'
  · exact lift_rootElt_mul_comm_of_ne η hker hη hc0 hc1 hij hjk hli hne he he'

theorem exists_rootLift (i j : Fin 4) :
    ∃ xl : K → E, (∀ a, η (xl a) = rootElt i j a) ∧ (∀ a b, xl (a + b) = xl a * xl b) ∧
      ∀ (g : E) (s : Fin 4 → K) (hs : ∏ r, s r = 1), η g = diagElt s hs →
        ∀ a, g * xl a * g⁻¹ = xl (s i * (s j)⁻¹ * a) := by
  by_cases hij : i = j
  · refine ⟨fun _ => 1, fun a => ?_, fun a b => (mul_one 1).symm, fun g s hs _ a => ?_⟩
    · change η 1 = rootElt i j a
      rw [map_one, hij, rootElt_self]
    · change g * 1 * g⁻¹ = 1
      rw [mul_one, mul_inv_cancel]
  obtain ⟨xl, hxl, hadd, hconj⟩ := exists_torus_lift η hker hη (x := rootElt i j)
    (rootElt_add i j)
    (fun e e' a b he he' => lift_rootElt_mul_comm η hker hη hc0 hc1 hij (Ne.symm hij)
      (Ne.symm hij) he he')
    (t₀ := diagElt (corootVec i j c) (prod_corootVec i j hc0)) (r₀ := c * c)
    (mul_self_ne_one hc1) (fun a => by
      rw [diagElt_conj_rootElt, corootVec_apply_left hij, corootVec_apply_right hij, inv_inv])
  refine ⟨xl, hxl, hadd, fun g s hs hg a => hconj g _ ?_ (fun a => ?_) a⟩
  · rw [hg]
    exact diagElt_mul_comm _ _ _ _
  · rw [hg]
    exact diagElt_conj_rootElt s hs i j a

end Four

theorem ker_eq_bot_of_specialLinear_four {K : Type*} [Field K] [Finite K] [CharP K 2]
    (hK : 3 ≤ Nat.card K) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* SpecialLinearGroup (Fin 4) K) (hη : Function.Surjective η) (hC : η.ker ≤ center E)
    (h2 : IsPGroup 2 η.ker) : η.ker = ⊥ := by
  have hker : ∀ z, η z = 1 → z ∈ center E := fun z hz => hC hz
  obtain ⟨c, hc0, hc1⟩ := exists_ne_zero_ne_one_of_three_le hK
  choose xl hxl hadd hconj using fun i j => exists_rootLift η hker hη hc0 hc1 i j
  have hrel : ∀ i j l : Fin 4, i ≠ j → j ≠ l → i ≠ l → ∀ a b,
      ⁅xl i j a, xl j l b⁆ = xl i l (a * b) := by
    intro i j l hij hjl hil a b
    obtain ⟨m, hmi, hmj, hml⟩ := exists_fin_four_ne i j l
    obtain ⟨g, hg⟩ := hη (diagElt (corootVec i m c) (prod_corootVec i m hc0))
    have hsi : corootVec i m c i = c := corootVec_apply_left (Ne.symm hmi) c
    have hsj : corootVec i m c j = 1 := corootVec_apply_of_ne (Ne.symm hij) (Ne.symm hmj) c
    have hsl : corootVec i m c l = 1 := corootVec_apply_of_ne (Ne.symm hil) (Ne.symm hml) c
    refine commutatorElement_lift_eq_of_torus η hker (hxl i j) (hxl j l) (hxl i l) (hadd i j)
      (hadd i l) (fun a b => commutatorElement_rootElt hij hjl hil a b)
      (fun a e c' he => lift_rootElt_mul_comm η hker hη hc0 hc1 hij (Ne.symm hij)
        (Ne.symm hil) (hxl i j a) he)
      (fun e e' c' c'' he he' => lift_rootElt_mul_comm η hker hη hc0 hc1 hil (Ne.symm hil)
        (Ne.symm hil) he he')
      hc1 (g := g) (fun a => ?_) (fun b => ?_) (fun c' => ?_) a b
    · rw [hconj i j g _ _ hg, hsi, hsj, inv_one, mul_one]
    · rw [hconj j l g _ _ hg, hsj, hsl, inv_one, mul_one, one_mul]
    · rw [hconj i l g _ _ hg, hsi, hsl, inv_one, mul_one]
  let M : Fin 4 → Fin 4 → Subgroup E := fun i j =>
    (MonoidHom.mk' (fun a : Multiplicative K => xl i j a.toAdd) fun a b => hadd i j _ _).range
  have hmemM : ∀ i j a, xl i j a ∈ M i j := fun i j a => ⟨Multiplicative.ofAdd a, rfl⟩
  have hmem : ∀ i j x, x ∈ M i j → ∃ a, xl i j a = x := fun i j x ⟨a, ha⟩ => ⟨a.toAdd, ha⟩
  have hMcard : ∀ i j, Nat.card (M i j) ≤ Nat.card K := fun i j =>
    (Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)).trans_eq
      (Nat.card_congr Multiplicative.toAdd)
  set P₀ := closure {g | ∃ i j, i < j ∧ g ∈ M i j} with hP₀
  have hcount : Nat.card P₀ ≤ Nat.card K ^ (4 * (4 - 1) / 2) :=
    card_closure_le_of_root_subgroups M (fun i j _ => hMcard i j)
      (fun i j k l hij _ hjk hil _ x hx y hy => by
        obtain ⟨a, rfl⟩ := hmem i j x hx
        obtain ⟨b, rfl⟩ := hmem k l y hy
        exact lift_rootElt_mul_comm η hker hη hc0 hc1 hij.ne hjk (Ne.symm hil) (hxl i j a)
          (hxl k l b))
      (fun i j l hij hjl x hx y hy => by
        obtain ⟨a, rfl⟩ := hmem i j x hx
        obtain ⟨b, rfl⟩ := hmem j l y hy
        rw [hrel i j l hij.ne hjl.ne (hij.trans hjl).ne a b]
        exact hmemM i l _)
  have hmap : unitriangular 4 K ≤ P₀.map η := by
    rw [hP₀, MonoidHom.map_closure]
    refine unitriangular_le_closure_rootElt.trans (closure_mono ?_)
    rintro _ ⟨i, j, a, hij, rfl⟩
    exact ⟨xl i j a, ⟨i, j, hij, hmemM i j a⟩, hxl i j a⟩
  have : Finite (P₀.map η) := Finite.of_surjective _ (η.subgroupMap_surjective P₀)
  have hbij : Function.Bijective (η.subgroupMap P₀) := by
    refine (η.subgroupMap_surjective P₀).bijective_of_nat_card_le ?_
    calc Nat.card P₀ ≤ Nat.card K ^ (4 * (4 - 1) / 2) := hcount
      _ = Nat.card (unitriangular 4 K) := (card_unitriangular 4).symm
      _ ≤ Nat.card (P₀.map η) := Subgroup.card_le_of_le hmap
  have hinj : ∀ z ∈ P₀, η z = 1 → z = 1 := by
    intro z hz hz1
    have h : η.subgroupMap P₀ ⟨z, hz⟩ = η.subgroupMap P₀ 1 :=
      Subtype.ext (by rw [map_one]; exact hz1)
    exact congrArg Subtype.val (hbij.1 h)
  obtain ⟨S, hS⟩ := exists_sylow_unitriangular (K := K) 2 (n := 4) (by norm_num)
  exact ker_eq_bot_of_sylow_le_map η hη hC h2 S P₀ (by rw [hS]; exact hmap) hinj

theorem even_linear_four_catalog_perfect_central_two_cover_trivial {E : Type*} {J : Type}
    [Group E] [Group J] [Finite E] [Finite J] [Group.IsPerfect E] (η : E →* J)
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) (h2 : IsPGroup 2 η.ker) {f : ℕ}
    (hf : 2 ≤ f) (hJ : CFSG.Blueprint.LieModel J .PSL 4 2 f) :
    η.ker = ⊥ ∧ Function.Bijective η := by
  obtain ⟨K, _, _, hcard, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hJ
  have := finite_field_prime_power_characteristic (K := K) Nat.prime_two (by omega) hcard
  have hK : 3 ≤ Nat.card K := by
    rw [hcard]
    calc 3 ≤ 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  set e' : J ≃* SpecialLinearGroup (Fin 4) K := e.trans (projectiveSLFourEquivSL K)
  set η' : E →* SpecialLinearGroup (Fin 4) K := e'.toMonoidHom.comp η
  have hη' : Function.Surjective η' := e'.surjective.comp hη
  have hker' : η'.ker = η.ker := by
    ext z
    exact e'.map_eq_one_iff
  have hbot := ker_eq_bot_of_specialLinear_four hK η' hη' (hker' ▸ hC) (hker' ▸ h2)
  rw [hker'] at hbot
  exact ⟨hbot, (MonoidHom.ker_eq_bot_iff η).mp hbot, hη⟩

end LinearCover

end CFSG.LocalAnalysis.ComponentInitial
