module

public import CFSG.LocalAnalysis.GH72.Alignment
public import CFSG.Walter.Bender1970
public import CFSG.Adapters.GeneralizedFittingTop
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.GH72

open Subgroup
open scoped MatrixGroups
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)
open CFSG.GorensteinWalter (IsComponentOf componentLayerOf generalizedFittingSubgroupOf)
open CFSG.CGT.Foote81L6 (mem_sup_iff_of_le_normalizer le_normalizer_of_comm)
open CFSG.CGT.Foote81L6.TStruct (mem_normalizer_of_map_conj_eq map_conj_eq_self_of_mem_normalizer)

variable {G : Type} [Group G] [Finite G]

theorem isConj_of_mulEquiv_of_forall {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : ∀ a b : Y, orderOf a = 2 → orderOf b = 2 → IsConj a b) {x y : X} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  have h' := h (e x) (e y) ((MulEquiv.orderOf_eq e x).trans hx)
    ((MulEquiv.orderOf_eq e y).trans hy)
  simpa using e.symm.toMonoidHom.map_isConj h'

theorem isConj_of_isTypeL2_or_isTypeJR {X : Type} [Group X] [Finite X]
    (h : CFSG.Walter.IsTypeL2 X ∨ CFSG.Walter.IsTypeJR X) {x y : X} (hx : orderOf x = 2)
    (hy : orderOf y = 2) : IsConj x y := by
  rcases h with (⟨f, hf, he⟩ | ⟨p, f, hp, hpo, hf, -, -, he⟩) | hJR
  · obtain ⟨e⟩ := he
    exact isConj_of_mulEquiv_of_forall e
      (fun a b ha hb => CFSG.Walter.psl2_even_isConj_of_orderOf_eq_two hf ha hb) hx hy
  · obtain ⟨e⟩ := he
    exact isConj_of_mulEquiv_of_forall e
      (fun a b ha hb => CFSG.Walter.psl2_odd_isConj_of_orderOf_eq_two hpo hf ha hb) hx hy
  · exact hJR.isConj_of_orderOf_eq_two hx hy

omit [Finite G] in
theorem isDih_of_isKleinFour {A : Subgroup G} (hA : IsKleinFour A) : IsDih A := by
  have := hA
  exact ⟨1, le_rfl, by rw [pow_one]; exact IsKleinFour.nonempty_mulEquiv⟩

omit [Finite G] in
theorem comm_of_hasAbelianSylowTwo (hY : CFSG.Walter.HasAbelianSylowTwo G) {S : Sylow 2 G}
    {a b : G} (ha : a ∈ (S : Subgroup G)) (hb : b ∈ (S : Subgroup G)) : a * b = b * a :=
  congrArg Subtype.val ((hY S).is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

section Component

variable {T K : Subgroup G}

theorem isSylowOf_inf_of_le_normalizer (hT : IsSylowOf 2 T ⊤)
    (hTK : T ≤ normalizer (K : Set G)) : IsSylowOf 2 (T ⊓ K) K :=
  (hT.of_le le_sup_right le_top).inf_of_le_normalizer le_sup_left (sup_le le_normalizer hTK)

variable (hO : CFSG.pPrimeCore 2 G = ⊥) (hY : CFSG.Walter.HasAbelianSylowTwo G) {S : Sylow 2 G}
  (hS : (S : Subgroup G) = T) (hK : IsComponentOf K ⊤)
include hO hY hS hK

theorem le_normalizer_component : T ≤ normalizer (K : Set G) :=
  hS ▸ CFSG.Walter.sylow_le_normalizer_of_isComponentOf hO hY S hK

theorem isSylowOf_inf_component : IsSylowOf 2 (T ⊓ K) K := by
  have hT : IsSylowOf 2 T ⊤ := by
    rw [isSylowOf_iff, relIndex_top_right, ← hS]
    exact ⟨le_top, S.isPGroup', S.not_dvd_index⟩
  exact isSylowOf_inf_of_le_normalizer hT (le_normalizer_component hO hY hS hK)

theorem exists_inner_mem_inf {t : G} (ht : t ∈ T) :
    ∃ p ∈ T ⊓ K, p⁻¹ * t ∈ centralizer (K : Set G) := by
  have hKs := CFSG.Walter.isSimpleGroup_of_isComponentOf hO hY hK
  have hTK := le_normalizer_component hO hY hS hK
  have hsyl := isSylowOf_inf_component hO hY hS hK
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    comm_of_hasAbelianSylowTwo hY (hS ▸ ha) (hS ▸ hb)
  obtain ⟨k, hkK, hk⟩ := CFSG.Walter.exists_inner_of_sylow_le_normalizer hY K
    (CFSG.Walter.nonabelian_of_isComponentOf hK) S (hS ▸ hTK) t (hS ▸ ht)
  have hkc : k ∈ centralizer ((T ⊓ K : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro y hy
    have h1 : k * y * k⁻¹ = y := by
      rw [← hk y hy.2, hTab t ht y hy.1, mul_inv_cancel_right]
    calc y * k = k * y * k⁻¹ * k := by rw [h1]
      _ = k * y := by group
  have hpow : ∀ n : ℕ, ∀ x ∈ K, t ^ n * x * (t ^ n)⁻¹ = k ^ n * x * (k ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro x _; simp
    | succ n ih =>
      intro x hx
      have hx' : k ^ n * x * (k ^ n)⁻¹ ∈ K :=
        mul_mem (mul_mem (pow_mem hkK n) hx) (inv_mem (pow_mem hkK n))
      calc t ^ (n + 1) * x * (t ^ (n + 1))⁻¹ = t * (t ^ n * x * (t ^ n)⁻¹) * t⁻¹ := by group
        _ = t * (k ^ n * x * (k ^ n)⁻¹) * t⁻¹ := by rw [ih x hx]
        _ = k * (k ^ n * x * (k ^ n)⁻¹) * k⁻¹ := hk _ hx'
        _ = k ^ (n + 1) * x * (k ^ (n + 1))⁻¹ := by group
  obtain ⟨m, hm⟩ : ∃ m : ℕ, t ^ 2 ^ m = 1 := by
    have hTp : IsPGroup 2 T := hS ▸ S.isPGroup'
    obtain ⟨m, hm⟩ := hTp ⟨t, ht⟩
    exact ⟨m, by simpa using congrArg Subtype.val hm⟩
  have hkm : k ^ 2 ^ m = 1 := by
    have hZ := CFSG.Walter.center_eq_bot_of_isComponentOf hO hY hK
    have hmem : (⟨k ^ 2 ^ m, pow_mem hkK _⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      have h1 := hpow (2 ^ m) y y.2
      rw [hm, one_mul, inv_one, mul_one] at h1
      change (y : G) * k ^ 2 ^ m = k ^ 2 ^ m * y
      calc (y : G) * k ^ 2 ^ m = k ^ 2 ^ m * y * (k ^ 2 ^ m)⁻¹ * k ^ 2 ^ m := by rw [← h1]
        _ = k ^ 2 ^ m * y := by group
    rw [hZ, Subgroup.mem_bot] at hmem
    exact congrArg Subtype.val hmem
  have hkp : IsPGroup 2 (zpowers k) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hkm)
    exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  have hle : zpowers k ≤ normalizer ((T ⊓ K : Subgroup G) : Set G) :=
    (zpowers_le).mpr (centralizer_le_normalizer _ hkc)
  have hsup := hsyl.eq_of_le le_sup_left (sup_le inf_le_right ((zpowers_le).mpr hkK))
    (hsyl.isPGroup.to_sup_of_normal_left' hkp hle)
  have hkT : k ∈ T ⊓ K := hsup ▸ mem_sup_right (mem_zpowers k)
  refine ⟨k, hkT, ?_⟩
  rw [mem_centralizer_iff]
  intro y hy
  have h1 := hk y hy
  calc y * (k⁻¹ * t) = k⁻¹ * (k * y * k⁻¹) * t := by group
    _ = k⁻¹ * (t * y * t⁻¹) * t := by rw [h1]
    _ = k⁻¹ * t * y := by group

theorem mem_normalizer_of_mem_normalizer_inf {g : G} (hgK : g ∈ K)
    (hgN : g ∈ normalizer ((T ⊓ K : Subgroup G) : Set G)) : g ∈ normalizer (T : Set G) := by
  have key : ∀ g ∈ K, g ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) →
      ∀ t ∈ T, g * t * g⁻¹ ∈ T := by
    intro g hgK hgN t ht
    obtain ⟨p, hp, hpc⟩ := exists_inner_mem_inf hO hY hS hK ht
    have h1 : g * p * g⁻¹ ∈ T ⊓ K := (mem_normalizer_iff.mp hgN p).1 hp
    have h2 : g * (p⁻¹ * t) = p⁻¹ * t * g := mem_centralizer_iff.mp hpc g hgK
    have h3 : g * t * g⁻¹ = g * p * g⁻¹ * (p⁻¹ * t) := by
      calc g * t * g⁻¹ = g * p * g⁻¹ * (g * (p⁻¹ * t) * g⁻¹) := by group
        _ = g * p * g⁻¹ * (p⁻¹ * t) := by rw [h2, mul_inv_cancel_right]
    rw [h3]
    exact mul_mem h1.1 (mul_mem (inv_mem hp.1) ht)
  rw [mem_normalizer_iff]
  intro t
  refine ⟨key g hgK hgN t, fun h => ?_⟩
  have h' := key g⁻¹ (inv_mem hgK) (inv_mem hgN) _ h
  have e : g⁻¹ * (g * t * g⁻¹) * g⁻¹⁻¹ = t := by group
  rwa [e] at h'

theorem exists_mem_normalizer_inf_ne :
    ∃ g ∈ K, g ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) ∧ ∃ x ∈ T ⊓ K, g * x * g⁻¹ ≠ x := by
  have hKs := CFSG.Walter.isSimpleGroup_of_isComponentOf hO hY hK
  have hsyl := isSylowOf_inf_component hO hY hS hK
  have hTab : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    comm_of_hasAbelianSylowTwo hY (hS ▸ ha) (hS ▸ hb)
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hmemQ : ∀ x : K, x ∈ (Q : Subgroup K) ↔ (x : G) ∈ T ⊓ K := fun x => by
    rw [hQ, mem_subgroupOf]
  by_contra hcon
  push Not at hcon
  have hP : normalizer ((Q : Subgroup K) : Set K) ≤ centralizer ((Q : Subgroup K) : Set K) := by
    intro g hg
    have hgN : (g : G) ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) := by
      rw [mem_normalizer_iff]
      intro y
      by_cases hyK : y ∈ K
      · have h := (mem_normalizer_iff.mp hg) ⟨y, hyK⟩
        rw [hmemQ, hmemQ] at h
        simpa using h
      · constructor
        · intro hy
          exact absurd hy.2 hyK
        · intro hy
          exfalso
          apply hyK
          have h := mul_mem (mul_mem (inv_mem g.2) hy.2) g.2
          rwa [← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul, mul_assoc, inv_mul_cancel,
            mul_one] at h
    rw [mem_centralizer_iff]
    intro x hx
    have h := hcon g g.2 hgN x ((hmemQ x).1 hx)
    apply Subtype.ext
    change (x : G) * g = g * x
    calc (x : G) * g = (g : G) * x * (g : G)⁻¹ * g := by rw [h]
      _ = g * x := by group
  rcases (MonoidHom.transferSylow Q hP).normal_ker.eq_bot_or_eq_top with h | h
  · have hc := MonoidHom.ker_transferSylow_isComplement' Q hP
    rw [h, isComplement'_bot_left] at hc
    obtain ⟨a, b, hab⟩ := CFSG.Walter.nonabelian_of_isComponentOf hK
    apply hab
    have ha : a ∈ (Q : Subgroup K) := hc ▸ mem_top a
    have hb : b ∈ (Q : Subgroup K) := hc ▸ mem_top b
    rw [hmemQ] at ha hb
    exact Subtype.ext (hTab _ ha.1 _ hb.1)
  · have hodd := MonoidHom.not_dvd_card_ker_transferSylow Q hP
    rw [h, card_top] at hodd
    exact hodd (even_iff_two_dvd.mp
      (CFSG.Walter.even_card_of_isSimpleGroup (CFSG.Walter.nonabelian_of_isComponentOf hK)))

omit hS in
theorem exists_conj_component (hSC : CFSG.Walter.SimpleCaseHyp) {x y : G} (hx : x ∈ K)
    (hy : y ∈ K) (hx2 : orderOf x = 2) (hy2 : orderOf y = 2) : ∃ g ∈ K, g * x * g⁻¹ = y := by
  have hKs := CFSG.Walter.isSimpleGroup_of_isComponentOf hO hY hK
  have htype : CFSG.Walter.IsTypeL2 K ∨ CFSG.Walter.IsTypeJR K :=
    hSC K hKs (CFSG.Walter.nonabelian_of_isComponentOf hK) (hY.subgroup K) fun H _ =>
      CFSG.Walter.isAStar_of_hasAbelianSylowTwo hSC ((hY.subgroup K).subgroup H)
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_isTypeL2_or_isTypeJR htype (x := (⟨x, hx⟩ : K))
    (y := ⟨y, hy⟩) ((Subgroup.orderOf_mk x hx).trans hx2) ((Subgroup.orderOf_mk y hy).trans hy2))
  exact ⟨g, g.2, congrArg Subtype.val hg⟩

end Component

section Fusion

variable {T A B : Subgroup G}

omit [Finite G] in
theorem conj_mem_of_fusion (hT2 : ∀ x ∈ T, x * x = 1) (hAT : A ≤ T)
    (hfusA : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ A ↔ y ∈ A))
    {g : G} (hg : g ∈ normalizer (T : Set G)) {a : G} (ha : a ∈ A) : g * a * g⁻¹ ∈ A := by
  by_cases ha1 : a = 1
  · rw [ha1, mul_one, mul_inv_cancel]
    exact one_mem _
  · have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hT2 a (hAT ha)) ha1
    exact (hfusA a (hAT ha) _ ((mem_normalizer_iff.mp hg a).1 (hAT ha)) ha2
      (isConj_iff.mpr ⟨g, rfl⟩)).1 ha

omit [Finite G] in
theorem normalizer_le_normalizer_of_fusion (hT2 : ∀ x ∈ T, x * x = 1) (hAT : A ≤ T)
    (hfusA : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ A ↔ y ∈ A)) :
    normalizer (T : Set G) ≤ normalizer (A : Set G) := by
  intro g hg
  rw [mem_normalizer_iff]
  intro a
  refine ⟨conj_mem_of_fusion hT2 hAT hfusA hg, fun h => ?_⟩
  have h' := conj_mem_of_fusion hT2 hAT hfusA (inv_mem hg) h
  have e : g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a := by group
  rwa [e] at h'

omit [Finite G] in
theorem inf_eq_or_inf_eq_of_fusion {K : Subgroup G} (hsup : A ⊔ B = T) (hA : IsKleinFour A)
    (hB : IsKleinFour B) (hT2 : ∀ x ∈ T, x * x = 1)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ A ↔ y ∈ A) ∧ (x ∈ B ↔ y ∈ B))
    (hTK : T ≤ normalizer (K : Set G))
    (hconj : ∀ x ∈ K, ∀ y ∈ K, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ K, g * x * g⁻¹ = y)
    (hNT : ∀ g ∈ K, g ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) → g ∈ normalizer (T : Set G))
    (hmove : ∃ g ∈ K, g ∈ normalizer ((T ⊓ K : Subgroup G) : Set G) ∧
      ∃ x ∈ T ⊓ K, g * x * g⁻¹ ≠ x) :
    T ⊓ K = A ∨ T ⊓ K = B := by
  have hAT : A ≤ T := hsup ▸ le_sup_left
  have hBT : B ≤ T := hsup ▸ le_sup_right
  obtain ⟨g, hgK, hgN, x₀, hx₀, hgx₀⟩ := hmove
  have hx₀1 : x₀ ≠ 1 := fun h => hgx₀ (by rw [h, mul_one, mul_inv_cancel])
  have hy₀ : g * x₀ * g⁻¹ ∈ T ⊓ K := (mem_normalizer_iff.mp hgN x₀).1 hx₀
  have hy₀1 : g * x₀ * g⁻¹ ≠ 1 := fun h => hx₀1 (by
    have e : x₀ = g⁻¹ * (g * x₀ * g⁻¹) * g := by group
    rw [e, h, mul_one, inv_mul_cancel])
  have key : ∀ {W : Subgroup G}, IsKleinFour W → T ⊓ K ≤ W → T ⊓ K = W := by
    intro W hW hle
    refine le_antisymm hle fun z hz => ?_
    by_cases hz1 : z = 1
    · rw [hz1]
      exact one_mem _
    by_cases hzx : z = x₀
    · rw [hzx]
      exact hx₀
    by_cases hzy : z = g * x₀ * g⁻¹
    · rw [hzy]
      exact hy₀
    have h := IsKleinFour.eq_mul_of_ne_all (G := W) (x := ⟨x₀, hle hx₀⟩)
      (y := ⟨g * x₀ * g⁻¹, hle hy₀⟩) (z := ⟨z, hz⟩)
      (fun h => hx₀1 (congrArg Subtype.val h)) (fun h => hy₀1 (congrArg Subtype.val h))
      (fun h => hgx₀ (congrArg Subtype.val h).symm) (fun h => hz1 (congrArg Subtype.val h))
      (fun h => hzx (congrArg Subtype.val h)) (fun h => hzy (congrArg Subtype.val h))
    have hz' : z = x₀ * (g * x₀ * g⁻¹) := congrArg Subtype.val h
    rw [hz']
    exact mul_mem hx₀ hy₀
  have hconjV : ∀ x ∈ T ⊓ K, ∀ y ∈ T ⊓ K, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    fun x hx y hy hx2 hy2 => by
      obtain ⟨c, -, hc⟩ := hconj x hx.2 y hy.2 hx2 hy2
      exact isConj_iff.mpr ⟨c, hc⟩
  have hinvol : ∀ {W : Subgroup G}, (∀ x ∈ T ⊓ K, orderOf x = 2 → x ∈ W) → T ⊓ K ≤ W := by
    intro W h x hx
    by_cases hx1 : x = 1
    · rw [hx1]
      exact one_mem _
    · exact h x hx (orderOf_eq_prime (by rw [pow_two]; exact hT2 x hx.1) hx1)
  rcases fusion_trichotomy hfus inf_le_left hconjV with h | h | h
  · exact Or.inl (key hA (hinvol h))
  · exact Or.inr (key hB (hinvol h))
  · exfalso
    have hgT := hNT g hgK hgN
    have hfix : ∀ {W : Subgroup G}, W ≤ T → (∀ a ∈ W, g * a * g⁻¹ ∈ W) → W ⊓ K = ⊥ →
        ∀ a ∈ W, g * a * g⁻¹ = a := by
      intro W hWT hW hWK a ha
      have h1 : a⁻¹ * (g * a * g⁻¹) ∈ W ⊓ K := by
        refine Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem ha) (hW a ha), ?_⟩
        have h2 : a⁻¹ * g * a⁻¹⁻¹ ∈ K := (mem_normalizer_iff.mp (inv_mem (hTK (hWT ha))) g).1 hgK
        have h3 := mul_mem h2 (inv_mem hgK)
        rwa [show a⁻¹ * g * a⁻¹⁻¹ * g⁻¹ = a⁻¹ * (g * a * g⁻¹) by group] at h3
      rw [hWK, mem_bot] at h1
      calc g * a * g⁻¹ = a * (a⁻¹ * (g * a * g⁻¹)) := by group
        _ = a := by rw [h1, mul_one]
    have hWK : ∀ {W : Subgroup G}, W ≤ T → (∀ x ∈ T ⊓ K, orderOf x = 2 → x ∉ W) → W ⊓ K = ⊥ := by
      intro W hWT hW
      rw [eq_bot_iff]
      intro a ha
      by_contra ha1
      have ha2 : orderOf a = 2 := orderOf_eq_prime (by rw [pow_two]; exact hT2 a (hWT ha.1)) ha1
      exact hW a ⟨hWT ha.1, ha.2⟩ ha2 ha.1
    have hA' := hfix hAT (fun a ha => conj_mem_of_fusion hT2 hAT
      (fun x hx y hy hx2 hxy => (hfus x hx y hy hx2 hxy).1) hgT ha)
      (hWK hAT fun x hx hx2 => (h x hx hx2).1)
    have hB' := hfix hBT (fun b hb => conj_mem_of_fusion hT2 hBT
      (fun x hx y hy hx2 hxy => (hfus x hx y hy hx2 hxy).2) hgT hb)
      (hWK hBT fun x hx hx2 => (h x hx hx2).2)
    have hx₀T : x₀ ∈ A ⊔ B := hsup ▸ hx₀.1
    obtain ⟨a, ha, b, hb, rfl⟩ := (mem_sup_iff_of_le_normalizer (le_normalizer_of_comm
      fun x hx y hy => CFSG.CGT.Foote81L6.TStruct.comm_of_mul_self hT2 (hAT hx) (hBT hy))).1 hx₀T
    apply hgx₀
    calc g * (a * b) * g⁻¹ = (g * a * g⁻¹) * (g * b * g⁻¹) := by group
      _ = a * b := by rw [hA' a ha, hB' b hb]

theorem le_centralizer_of_inf_eq {K : Subgroup G} (hsup : A ⊔ B = T) (hinf : A ⊓ B = ⊥)
    (hA : IsKleinFour A) (hT2 : ∀ x ∈ T, x * x = 1)
    (hfusB : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ B ↔ y ∈ B))
    (hconj : ∀ x ∈ K, ∀ y ∈ K, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ K, g * x * g⁻¹ = y)
    (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hinner : ∀ t ∈ T, ∃ p ∈ T ⊓ K, p⁻¹ * t ∈ centralizer (K : Set G)) (hKA : T ⊓ K = A) :
    B ≤ centralizer (K : Set G) := by
  have hAT : A ≤ T := hsup ▸ le_sup_left
  have hBT : B ≤ T := hsup ▸ le_sup_right
  have hAK : A ≤ K := by
    rw [← hKA]
    exact inf_le_right
  have hDB : T ⊓ centralizer (K : Set G) ≤ B :=
    le_of_conj_of_le_centralizer hsup hinf
      (fun x hx y hy => CFSG.CGT.Foote81L6.TStruct.comm_of_mul_self hT2 (hAT hx) (hBT hy)) hAK
      hconj (isDih_of_isKleinFour hA).exists_involution_ne inf_le_left (fun w hw => hT2 w hw.1)
      (le_bot_iff.mp (hZ ▸ le_inf inf_le_right (inf_le_left.trans inf_le_right)))
      (fun g hg w hw => mem_centralizer_iff.mp hw.2 g hg) hfusB
  intro b hb
  obtain ⟨p, hp, hpc⟩ := hinner b (hBT hb)
  have hpB : p⁻¹ * b ∈ B := hDB (Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hp.1) (hBT hb), hpc⟩)
  have hp1 : p = 1 := by
    have h1 : p⁻¹ ∈ B := by
      have h' := mul_mem hpB (inv_mem hb)
      rwa [mul_inv_cancel_right] at h'
    have h2 : p⁻¹ ∈ A ⊓ B := Subgroup.mem_inf.mpr ⟨inv_mem (hKA ▸ hp), h1⟩
    rw [hinf, mem_bot, inv_eq_one] at h2
    exact h2
  rw [hp1, inv_one, one_mul] at hpc
  exact hpc

end Fusion

section Factors

variable {T : Subgroup G} (hO : CFSG.pPrimeCore 2 G = ⊥) (hY : CFSG.Walter.HasAbelianSylowTwo G)
  {S : Sylow 2 G} (hS : (S : Subgroup G) = T)
include hO hY

theorem component_eq_of_inf_eq {K K' A : Subgroup G} (hK : IsComponentOf K ⊤)
    (hK' : IsComponentOf K' ⊤) (hA : A ≠ ⊥) (hKA : T ⊓ K = A) (hK'A : T ⊓ K' = A) : K = K' := by
  rcases CFSG.LocalCores.distinct_components_commute
      ((CFSG.Walter.isComponent_iff_isComponentOf_top K).mpr hK)
      ((CFSG.Walter.isComponent_iff_isComponentOf_top K').mpr hK') with h | h
  · exact h
  · exfalso
    apply hA
    have hZ := CFSG.Walter.center_eq_bot_of_isComponentOf hO hY hK
    rw [eq_bot_iff]
    intro a ha
    have haK : a ∈ K := by
      rw [← hKA] at ha
      exact ha.2
    have haK' : a ∈ K' := by
      rw [← hK'A] at ha
      exact ha.2
    have hmem : (⟨a, haK⟩ : K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (mem_centralizer_iff.mp ((commutator_eq_bot_iff_le_centralizer.mp h) y.2) a haK').symm
    rw [hZ, Subgroup.mem_bot] at hmem
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)

theorem normalizer_le_normalizer_component {K A : Subgroup G} (hK : IsComponentOf K ⊤)
    (hA : A ≠ ⊥) (hKA : T ⊓ K = A)
    (hNA : normalizer (T : Set G) ≤ normalizer (A : Set G)) :
    normalizer (T : Set G) ≤ normalizer (K : Set G) := by
  intro g hg
  have hK' : IsComponentOf (K.map (MulAut.conj g).toMonoidHom) ⊤ :=
    (CFSG.Walter.isComponent_iff_isComponentOf_top _).mp
      (CFSG.LocalCores.isComponent_map_mulEquiv (MulAut.conj g)
        ((CFSG.Walter.isComponent_iff_isComponentOf_top K).mpr hK))
  have hTK' : T ⊓ K.map (MulAut.conj g).toMonoidHom = A := by
    rw [← map_conj_eq_self_of_mem_normalizer hg, ← Subgroup.map_inf_eq _ _ _
      (MulAut.conj g).injective, hKA, map_conj_eq_self_of_mem_normalizer (hNA hg)]
  exact mem_normalizer_of_map_conj_eq
    (component_eq_of_inf_eq hO hY hK hK' hA hKA hTK').symm

include hS

theorem normal_of_le_normalizer {X : Subgroup G} (hTX : T ≤ normalizer (X : Set G))
    (hNX : normalizer (T : Set G) ≤ normalizer (X : Set G))
    (hEX : ∀ E : Subgroup G, IsComponentOf E ⊤ → E ≤ normalizer (X : Set G)) : X.Normal := by
  have hFn : (generalizedFittingSubgroupOf (⊤ : Subgroup G)).Normal :=
    ⟨fun n hn g => (CFSG.GorensteinWalter.generalizedFittingSubgroupOf_isNormalIn ⊤).2 g
      (mem_top g) n hn⟩
  have hTF : (S : Subgroup G) ≤ generalizedFittingSubgroupOf (⊤ : Subgroup G) :=
    CFSG.Walter.sylow_le_generalizedFittingSubgroupOf hO hY S
  have htop := Sylow.normalizer_sup_eq_top' (N := generalizedFittingSubgroupOf (⊤ : Subgroup G))
    S hTF
  have hF : CFSG.fittingSubgroupOf (⊤ : Subgroup G) ≤ T := by
    rw [CFSG.Adapters.fittingSubgroupOf_top_eq_foundations]
    have hF2 : IsPGroup 2 (CFSG.fittingSubgroup G) :=
      CFSG.isPGroup_of_nilpotent_normal _ inferInstance inferInstance hO
    rw [← hS]
    exact hF2.le_sylow_of_normal S
  have hFX : generalizedFittingSubgroupOf (⊤ : Subgroup G) ≤ normalizer (X : Set G) :=
    sup_le (hF.trans hTX) (sSup_le fun E hE => hEX E hE)
  have hNX' : normalizer (S : Set G) ≤ normalizer (X : Set G) := by
    have e : (S : Set G) = (T : Set G) := by rw [← hS]; rfl
    rw [e]
    exact hNX
  rw [← normalizer_eq_top_iff, eq_top_iff, ← htop]
  exact sup_le hNX' hFX

theorem isL2OrA7_component (hSC : CFSG.Walter.SimpleCaseHyp)
    {K : Subgroup G} (hK : IsComponentOf K ⊤) (h4 : Nat.card (T ⊓ K : Subgroup G) = 4) :
    IsL2OrA7 K 5 := by
  have hKs := CFSG.Walter.isSimpleGroup_of_isComponentOf hO hY hK
  have htype : CFSG.Walter.IsTypeL2 K ∨ CFSG.Walter.IsTypeJR K :=
    hSC K hKs (CFSG.Walter.nonabelian_of_isComponentOf hK) (hY.subgroup K) fun H _ =>
      CFSG.Walter.isAStar_of_hasAbelianSylowTwo hSC ((hY.subgroup K).subgroup H)
  obtain ⟨Q, hQ⟩ := isSylowOf_inf_component hO hY hS hK
  have hQ4 : Nat.card (Q : Subgroup K) = 4 := by
    rw [← h4, ← hQ, Subgroup.card_map_of_injective K.subtype_injective]
  rcases htype with (⟨f, hf, he⟩ | ⟨p, f, hp, hpo, -, h5, -, he⟩) | hJR
  · obtain ⟨e⟩ := he
    obtain ⟨U⟩ : Nonempty (Sylow 2 PSL(2, GaloisField 2 f)) := inferInstance
    have hU := (CFSG.Walter.psl2_even_sylow_two hf U).2
    have hcard : Nat.card (U : Subgroup PSL(2, GaloisField 2 f)) = Nat.card (Q : Subgroup K) := by
      rw [Sylow.card_eq_multiplicity, Sylow.card_eq_multiplicity, Nat.card_congr e.toEquiv]
    rw [hU, hQ4] at hcard
    have hf2 : f = 2 := Nat.pow_right_injective le_rfl (hcard.trans (by norm_num))
    subst hf2
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨e'⟩ := CFSG.Walter.nonempty_psl2_five_mulEquiv_psl2_four
    exact Or.inr ⟨5, 1, this, by norm_num, by norm_num, ⟨e.trans e'.symm⟩⟩
  · refine Or.inr ⟨p, f, hp, fun h => ?_, h5, he⟩
    rw [h] at hpo
    exact (Nat.not_odd_iff_even.mpr even_two) hpo
  · exfalso
    have h2 : 2 ∣ Nat.card K :=
      (show 2 ∣ 4 by norm_num).trans (hQ4 ▸ Subgroup.card_subgroup_dvd_card (Q : Subgroup K))
    have h8 := (hJR.sylow_two h2 Q).2
    rw [hQ4] at h8
    omega

theorem exists_factor (hSC : CFSG.Walter.SimpleCaseHyp)
    {A B : Subgroup G} (hsup : A ⊔ B = T) (hinf : A ⊓ B = ⊥) (hA : IsKleinFour A)
    (hB : IsKleinFour B) (hT2 : ∀ x ∈ T, x * x = 1)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ A ↔ y ∈ A) ∧ (x ∈ B ↔ y ∈ B)) :
    ∃ F : Subgroup G, F.Normal ∧ T ⊓ F = A ∧ (IsL2OrA7 F 5 ∨ F = A) := by
  have hAT : A ≤ T := hsup ▸ le_sup_left
  have hfusA : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ A ↔ y ∈ A) :=
    fun x hx y hy hx2 hxy => (hfus x hx y hy hx2 hxy).1
  have hNA := normalizer_le_normalizer_of_fusion hT2 hAT hfusA
  have hA1 : A ≠ ⊥ := by
    intro h
    have h4 := hA.card_four
    rw [h, Subgroup.card_bot] at h4
    omega
  have hconjK : ∀ K, IsComponentOf K ⊤ →
      ∀ x ∈ K, ∀ y ∈ K, orderOf x = 2 → orderOf y = 2 → ∃ g ∈ K, g * x * g⁻¹ = y :=
    fun K hK x hx y hy hx2 hy2 => exists_conj_component hO hY hK hSC hx hy hx2 hy2
  have hcomp : ∀ K, IsComponentOf K ⊤ → T ⊓ K = A ∨ T ⊓ K = B := fun K hK =>
    inf_eq_or_inf_eq_of_fusion hsup hA hB hT2 hfus (le_normalizer_component hO hY hS hK)
      (hconjK K hK) (fun g hgK hgN => mem_normalizer_of_mem_normalizer_inf hO hY hS hK hgK hgN)
      (exists_mem_normalizer_inf_ne hO hY hS hK)
  by_cases h : ∃ K, IsComponentOf K ⊤ ∧ T ⊓ K = A
  · obtain ⟨K, hK, hKA⟩ := h
    refine ⟨K, normal_of_le_normalizer hO hY hS (le_normalizer_component hO hY hS hK)
      (normalizer_le_normalizer_component hO hY hK hA1 hKA hNA) fun E hE => ?_, hKA,
      Or.inl (isL2OrA7_component hO hY hS hSC hK (by rw [hKA]; exact hA.card_four))⟩
    rcases CFSG.LocalCores.distinct_components_commute
        ((CFSG.Walter.isComponent_iff_isComponentOf_top E).mpr hE)
        ((CFSG.Walter.isComponent_iff_isComponentOf_top K).mpr hK) with he | he
    · rw [he]
      exact le_normalizer
    · exact (commutator_eq_bot_iff_le_centralizer.mp he).trans (centralizer_le_normalizer _)
  · push Not at h
    refine ⟨A, normal_of_le_normalizer hO hY hS (le_normalizer_of_comm fun x hx y hy =>
      CFSG.CGT.Foote81L6.TStruct.comm_of_mul_self hT2 (hAT hx) hy) hNA fun E hE => ?_,
      inf_eq_right.mpr hAT, Or.inr rfl⟩
    have hEB : T ⊓ E = B := (hcomp E hE).resolve_left (h E hE)
    have hZ : E ⊓ centralizer (E : Set G) = ⊥ := by
      have hZE := CFSG.Walter.center_eq_bot_of_isComponentOf hO hY hE
      rw [eq_bot_iff]
      intro x hx
      have hmem : (⟨x, hx.1⟩ : E) ∈ Subgroup.center E := by
        rw [Subgroup.mem_center_iff]
        intro y
        exact Subtype.ext (mem_centralizer_iff.mp hx.2 y y.2)
      rw [hZE, Subgroup.mem_bot] at hmem
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hmem)
    have hAE : A ≤ centralizer (E : Set G) :=
      le_centralizer_of_inf_eq (A := B) (B := A) (by rw [sup_comm]; exact hsup)
        (by rw [inf_comm]; exact hinf) hB hT2 hfusA (hconjK E hE) hZ
        (fun t ht => exists_inner_mem_inf hO hY hS hE ht) hEB
    exact (le_centralizer_iff.mp hAE).trans (centralizer_le_normalizer _)

end Factors

theorem walterE16_of_simpleCase (hSC : CFSG.Walter.SimpleCaseHyp)
    (hO : CFSG.oddCore G = ⊥) (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (T T₁ T₂ : Subgroup G) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTE : IsE16 T)
    (hT₁ : IsKleinFour T₁) (hT₂ : IsKleinFour T₂) (hsup : T₁ ⊔ T₂ = T) (hinf : T₁ ⊓ T₂ = ⊥)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y →
      (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) :
    ∃ F₁ F₂ : Subgroup G, F₁.Normal ∧ F₂.Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd (F₁ ⊔ F₂).index ∧
      (IsL2OrA7 F₁ 5 ∨ F₁ = T₁) ∧ (IsL2OrA7 F₂ 5 ∨ F₂ = T₂) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 T₁ F₁ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ F₂ := by
  have _ := h2
  have hO' : CFSG.pPrimeCore 2 G = ⊥ := by
    rw [CFSG.pPrimeCore_eq_piCore, ← CFSG.oddCore_eq_piCore]
    exact hO
  obtain ⟨S, hS⟩ := exists_sylow_of_isSylowOf_top hT
  have hY : CFSG.Walter.HasAbelianSylowTwo G :=
    CFSG.Walter.hasAbelianSylowTwo_of_sylow S (hS ▸ hTE.1.1)
  have hT2 : ∀ x ∈ T, x * x = 1 := fun x hx => by
    rw [← pow_two]
    exact hTE.1.2 x hx
  obtain ⟨F₁, hF₁, hTF₁, ht₁⟩ := exists_factor hO' hY hS hSC hsup hinf hT₁ hT₂ hT2 hfus
  obtain ⟨F₂, hF₂, hTF₂, ht₂⟩ := exists_factor hO' hY hS hSC (by rw [sup_comm]; exact hsup)
    (by rw [inf_comm]; exact hinf) hT₂ hT₁ hT2 fun x hx y hy hx2 hxy =>
      (hfus x hx y hy hx2 hxy).symm
  have hsyl : ∀ {F : Subgroup G}, F.Normal → IsSylowOf 2 (T ⊓ F) F := fun hF =>
    hT.inf_of_le_normalizer le_top (normalizer_eq_top_iff.mpr hF).ge
  refine ⟨F₁, F₂, hF₁, hF₂, ?_, ?_, ht₁, ht₂, hTF₁ ▸ hsyl hF₁, hTF₂ ▸ hsyl hF₂⟩
  ·
    have hM : (F₁ ⊓ F₂).Normal := by
      have := hF₁
      have := hF₂
      infer_instance
    have hTM : T ⊓ (F₁ ⊓ F₂) = ⊥ := by
      rw [← hinf, ← hTF₁, ← hTF₂, inf_inf_distrib_left]
    have hcard := (hsyl hM).card_eq
    rw [hTM, Subgroup.card_bot] at hcard
    have hv : (Nat.card (F₁ ⊓ F₂ : Subgroup G)).factorization 2 = 0 :=
      (Nat.pow_eq_one.mp hcard.symm).resolve_left (by norm_num)
    have hodd : Odd (Nat.card (F₁ ⊓ F₂ : Subgroup G)) := by
      rcases (Nat.factorization_eq_zero_iff _ _).mp hv with h | h | h
      · exact absurd Nat.prime_two h
      · exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp h)
      · exact absurd h Nat.card_pos.ne'
    have hle : F₁ ⊓ F₂ ≤ CFSG.oddCore G := le_sSup ⟨hM, hodd⟩
    rw [hO] at hle
    exact le_bot_iff.mp hle
  ·
    have hT₁F : T₁ ≤ F₁ := by
      rw [← hTF₁]
      exact inf_le_right
    have hT₂F : T₂ ≤ F₂ := by
      rw [← hTF₂]
      exact inf_le_right
    have hTle : T ≤ F₁ ⊔ F₂ := by
      rw [← hsup]
      exact sup_le_sup hT₁F hT₂F
    have hTodd : ¬ 2 ∣ T.index := by
      have h' := (isSylowOf_iff.mp hT).2.2
      rwa [relIndex_top_right] at h'
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp fun h =>
      hTodd (h.trans (Subgroup.index_dvd_of_le hTle)))

theorem walterE16
    (hO : CFSG.oddCore G = ⊥) (h2 : ∀ N : Subgroup G, N.Normal → N.index ≠ 2)
    (T T₁ T₂ : Subgroup G) (hT : CFSG.ABGLocalTools.IsSylowOf 2 T ⊤) (hTE : IsE16 T)
    (hT₁ : IsKleinFour T₁) (hT₂ : IsKleinFour T₂) (hsup : T₁ ⊔ T₂ = T) (hinf : T₁ ⊓ T₂ = ⊥)
    (hfus : ∀ x ∈ T, ∀ y ∈ T, orderOf x = 2 → IsConj x y → (x ∈ T₁ ↔ y ∈ T₁) ∧ (x ∈ T₂ ↔ y ∈ T₂)) :
    ∃ F₁ F₂ : Subgroup G, F₁.Normal ∧ F₂.Normal ∧ F₁ ⊓ F₂ = ⊥ ∧ Odd (F₁ ⊔ F₂).index ∧
      (IsL2OrA7 F₁ 5 ∨ F₁ = T₁) ∧ (IsL2OrA7 F₂ 5 ∨ F₂ = T₂) ∧
      CFSG.ABGLocalTools.IsSylowOf 2 T₁ F₁ ∧ CFSG.ABGLocalTools.IsSylowOf 2 T₂ F₂ :=
  walterE16_of_simpleCase (CFSG.Walter.simpleCaseHyp_of_benderHyp CFSG.Walter.benderHyp) hO h2
    T T₁ T₂ hT hTE hT₁ hT₂ hsup hinf hfus

end CFSG.GH72
