module

public import CFSG.GH74.GLS.Stage4.LocalAssembly
public import CFSG.GH74.GLS.Stage4.RestSetupRank
public import CFSG.GH74.GLS.IVK.Prod.Basic

public section

namespace CFSG.GH74.GLS.Stage4.Rest

open Subgroup CFSG CFSG.Semidihedral CFSG.Blueprint CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage4
  CFSG.Assembly.LowTwoRank

theorem exists_SL2_quaternion_pair (F : Type) [Field F] [Finite F] (hodd : Odd (Nat.card F)) :
    ∃ x y : Matrix.SpecialLinearGroup (Fin 2) F,
      x * x = OddFieldSL2.minusIdentity F ∧ y * y = OddFieldSL2.minusIdentity F ∧
        x * y = OddFieldSL2.minusIdentity F * (y * x) := by
  obtain ⟨a, b, hab⟩ := OddFieldSL2.sum_two_squares F hodd (-1)
  refine ⟨OddLinearNormals.quarterTurn F, OddFieldSL2.secondGenerator F a b hab, ?_, ?_, ?_⟩
  · rw [← pow_two]
    exact OddFieldSL2.quarterTurn_square F
  · rw [← pow_two]
    exact OddFieldSL2.secondGenerator_square F a b hab
  · have hm : OddFieldSL2.minusIdentity F * OddFieldSL2.minusIdentity F = 1 := by
      rw [← pow_two]
      exact OddFieldSL2.minusIdentity_square F
    have hx2 : OddLinearNormals.quarterTurn F * OddLinearNormals.quarterTurn F =
        OddFieldSL2.minusIdentity F := by
      rw [← pow_two]
      exact OddFieldSL2.quarterTurn_square F
    have hinv : (OddLinearNormals.quarterTurn F)⁻¹ =
        OddLinearNormals.quarterTurn F * OddFieldSL2.minusIdentity F := by
      apply inv_eq_of_mul_eq_one_right
      calc OddLinearNormals.quarterTurn F *
            (OddLinearNormals.quarterTurn F * OddFieldSL2.minusIdentity F)
          = (OddLinearNormals.quarterTurn F * OddLinearNormals.quarterTurn F) *
              OddFieldSL2.minusIdentity F := by group
        _ = 1 := by rw [hx2, hm]
    have hcen := Subgroup.mem_center_iff.1 (OddFieldSL2.minusIdentity_mem_center F)
    calc OddLinearNormals.quarterTurn F * OddFieldSL2.secondGenerator F a b hab
        = OddFieldSL2.secondGenerator F a b hab * (OddLinearNormals.quarterTurn F)⁻¹ :=
          OddFieldSL2.generators_inversion F a b hab
      _ = OddFieldSL2.secondGenerator F a b hab *
            (OddLinearNormals.quarterTurn F * OddFieldSL2.minusIdentity F) := by rw [hinv]
      _ = (OddFieldSL2.secondGenerator F a b hab * OddLinearNormals.quarterTurn F) *
            OddFieldSL2.minusIdentity F := by group
      _ = OddFieldSL2.minusIdentity F * (OddFieldSL2.secondGenerator F a b hab *
            OddLinearNormals.quarterTurn F) :=
          hcen (OddFieldSL2.secondGenerator F a b hab * OddLinearNormals.quarterTurn F)

theorem mem_sup_iff_of_comm {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (x : G) :
    x ∈ K₁ ⊔ K₂ ↔ ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b := by
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ a ∈ K₁, ∃ b ∈ K₂, x = a * b}
        one_mem' := ⟨1, K₁.one_mem, 1, K₂.one_mem, by simp⟩
        mul_mem' := by
          rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
          refine ⟨a * a', K₁.mul_mem ha ha', b * b', K₂.mul_mem hb hb', ?_⟩
          calc a * b * (a' * b') = a * (b * a') * b' := by group
            _ = a * (a' * b) * b' := by rw [← hcomm a' ha' b hb]
            _ = a * a' * (b * b') := by group
        inv_mem' := by
          rintro _ ⟨a, ha, b, hb, rfl⟩
          refine ⟨a⁻¹, K₁.inv_mem ha, b⁻¹, K₂.inv_mem hb, ?_⟩
          have := hcomm a ha b⁻¹ (K₂.inv_mem hb)
          calc (a * b)⁻¹ = b⁻¹ * a⁻¹ := mul_inv_rev a b
            _ = a⁻¹ * b⁻¹ := by
              have h1 : a⁻¹ * b⁻¹ = (b * a)⁻¹ := (mul_inv_rev b a).symm
              rw [h1, ← hcomm a ha b hb, mul_inv_rev] }
    have hle : K₁ ⊔ K₂ ≤ S := sup_le (fun a ha => ⟨a, ha, 1, K₂.one_mem, by simp⟩)
      (fun b hb => ⟨1, K₁.one_mem, b, hb, by simp⟩)
    exact hle hx
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact Subgroup.mul_mem_sup ha hb

theorem eq_one_or_eq_of_central {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]
    (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {a : G} (haK : a ∈ K)
    (hae : e ⟨a, haK⟩ = OddFieldSL2.minusIdentity F) {k : G} (hk : k ∈ K)
    (hc : ∀ y ∈ K, y * k = k * y) : k = 1 ∨ k = a := by
  have hcenter : e ⟨k, hk⟩ ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul]
    exact congrArg e (Subtype.ext (hc y y.2))
  rcases (CFSG.Semidihedral.ProjectiveSL2Cover.mem_center_iff_eq_one_or_minusIdentity F _).1
      hcenter with h | h
  · left
    have : (⟨k, hk⟩ : ↥K) = 1 := e.injective (by rw [h, map_one])
    exact congrArg Subtype.val this
  · right
    have hm : e ⟨k, hk⟩ = e ⟨a, haK⟩ := by
      rw [h, hae, CFSG.Semidihedral.ProjectiveSL2Cover.minusIdentity_eq_neg_one]
      rfl
    exact congrArg Subtype.val (e.injective hm)

theorem quaternion_pair_in_subgroup {G : Type} [Group G] {K : Subgroup G} {F : Type} [Field F]
    [Finite F] (hodd : Odd (Nat.card F)) (e : ↥K ≃* Matrix.SpecialLinearGroup (Fin 2) F) {a : G}
    (haK : a ∈ K) (hae : e ⟨a, haK⟩ = OddFieldSL2.minusIdentity F) :
    ∃ x y : G, x ∈ K ∧ y ∈ K ∧ x * x = a ∧ y * y = a ∧ x * y = a * (y * x) := by
  obtain ⟨X, Y, hX, hY, hXY⟩ := exists_SL2_quaternion_pair F hodd
  have hm : e.symm (OddFieldSL2.minusIdentity F) = ⟨a, haK⟩ := e.symm_apply_eq.2 hae.symm
  refine ⟨(e.symm X : G), (e.symm Y : G), (e.symm X).2, (e.symm Y).2, ?_, ?_, ?_⟩
  · have h1 : e.symm X * e.symm X = ⟨a, haK⟩ := by rw [← map_mul, hX, hm]
    simpa using congrArg Subtype.val h1
  · have h1 : e.symm Y * e.symm Y = ⟨a, haK⟩ := by rw [← map_mul, hY, hm]
    simpa using congrArg Subtype.val h1
  · have h1 : e.symm X * e.symm Y = ⟨a, haK⟩ * (e.symm Y * e.symm X) := by
      calc e.symm X * e.symm Y = e.symm (X * Y) := (map_mul _ _ _).symm
        _ = e.symm (OddFieldSL2.minusIdentity F * (Y * X)) := by rw [hXY]
        _ = e.symm (OddFieldSL2.minusIdentity F) * (e.symm Y * e.symm X) := by
          rw [map_mul, map_mul]
        _ = ⟨a, haK⟩ * (e.symm Y * e.symm X) := by rw [hm]
    simpa using congrArg Subtype.val h1

theorem exists_inter_involution {G : Type} [Group G] {K₁ K₂ : Subgroup G}
    (hcard : Nat.card ↥(K₁ ⊓ K₂) = 2) :
    ∃ a : G, a ∈ K₁ ∧ a ∈ K₂ ∧ a ≠ 1 ∧ a * a = 1 ∧ ∀ g ∈ K₁ ⊓ K₂, g = 1 ∨ g = a := by
  obtain ⟨a', ha'1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(K₁ ⊓ K₂))).1 hcard
  have haa' : a' * a' = 1 := by
    by_contra h
    have h1 := huniq (a' * a') h
    have h2 : a' * a' = a' * 1 := by rw [mul_one]; exact h1
    exact ha'1 (mul_left_cancel h2)
  refine ⟨(a' : G), a'.2.1, a'.2.2, fun h => ha'1 (Subtype.ext h), congrArg Subtype.val haa', ?_⟩
  intro g hg
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  · right
    have := huniq ⟨g, hg⟩ (fun h => hg1 (congrArg Subtype.val h))
    exact congrArg Subtype.val this

theorem z_mem_sup_of_pRank_le {G : Type} [Group G] [Finite G] {K₁ K₂ : Subgroup G} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] (hodd₁ : Odd (Nat.card F₁))
    (hodd₂ : Odd (Nat.card F₂)) (e₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hcard : Nat.card ↥(K₁ ⊓ K₂) = 2) {z : G}
    (hz : z * z = 1) (hzK : ∀ k ∈ K₁ ⊔ K₂, z * k = k * z) (hr : CFSG.pRank 2 G ≤ 3) :
    z ∈ K₁ ⊔ K₂ := by
  by_contra hzn
  obtain ⟨a, ha₁, ha₂, ha1, haa, hinter⟩ := exists_inter_involution hcard
  have hord₁ : orderOf (⟨a, ha₁⟩ : ↥K₁) = 2 := by
    refine orderOf_eq_prime ?_ (fun h => ha1 (congrArg Subtype.val h))
    exact Subtype.ext (by simpa [pow_two] using haa)
  have hord₂ : orderOf (⟨a, ha₂⟩ : ↥K₂) = 2 := by
    refine orderOf_eq_prime ?_ (fun h => ha1 (congrArg Subtype.val h))
    exact Subtype.ext (by simpa [pow_two] using haa)
  have hae₁ : e₁ ⟨a, ha₁⟩ = OddFieldSL2.minusIdentity F₁ :=
    (CFSG.GH74.GLS.IVK.sl_central_involution e₁ ⟨a, ha₁⟩ hord₁
      (fun k => Subtype.ext (hcomm k k.2 a ha₂))).2
  have hae₂ : e₂ ⟨a, ha₂⟩ = OddFieldSL2.minusIdentity F₂ :=
    (CFSG.GH74.GLS.IVK.sl_central_involution e₂ ⟨a, ha₂⟩ hord₂
      (fun k => Subtype.ext (hcomm a ha₁ k k.2).symm)).2
  obtain ⟨x₁, y₁, hx₁, hy₁, hx₁s, hy₁s, hxy₁⟩ := quaternion_pair_in_subgroup hodd₁ e₁ ha₁ hae₁
  obtain ⟨x₂, y₂, hx₂, hy₂, hx₂s, hy₂s, hxy₂⟩ := quaternion_pair_in_subgroup hodd₂ e₂ ha₂ hae₂
  have h4 := four_le_pRank_of_Q8 hx₁ hy₁ hx₂ hy₂ ha₁ ha₂ ha1 hinter hcomm haa hx₁s hy₁s hx₂s hy₂s
    hxy₁ hxy₂ hz hzK hzn
  omega

theorem z_mem_inter_of_pRank_le {G : Type} [Group G] [Finite G] {K₁ K₂ : Subgroup G} {F₁ F₂ : Type}
    [Field F₁] [Field F₂] [Finite F₁] [Finite F₂] (hodd₁ : Odd (Nat.card F₁))
    (hodd₂ : Odd (Nat.card F₂)) (e₁ : ↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
    (e₂ : ↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂)
    (hcomm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x) (hcard : Nat.card ↥(K₁ ⊓ K₂) = 2) {z : G}
    (hz2 : orderOf z = 2) (hzK : ∀ k ∈ K₁ ⊔ K₂, z * k = k * z) (hr : CFSG.pRank 2 G ≤ 3) :
    z ∈ K₁ ∧ z ∈ K₂ ∧ K₁ ⊓ K₂ = Subgroup.zpowers z := by
  have hz1 : z ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz2
    omega
  have hzz : z * z = 1 := by
    have : z ^ 2 = 1 := by rw [← hz2]; exact pow_orderOf_eq_one z
    rwa [pow_two] at this
  have hzmem := z_mem_sup_of_pRank_le hodd₁ hodd₂ e₁ e₂ hcomm hcard hzz hzK hr
  obtain ⟨a, ha₁, ha₂, ha1, haa, hinter⟩ := exists_inter_involution hcard
  have hord₁ : orderOf (⟨a, ha₁⟩ : ↥K₁) = 2 := by
    refine orderOf_eq_prime ?_ (fun h => ha1 (congrArg Subtype.val h))
    exact Subtype.ext (by simpa [pow_two] using haa)
  have hord₂ : orderOf (⟨a, ha₂⟩ : ↥K₂) = 2 := by
    refine orderOf_eq_prime ?_ (fun h => ha1 (congrArg Subtype.val h))
    exact Subtype.ext (by simpa [pow_two] using haa)
  have hae₁ : e₁ ⟨a, ha₁⟩ = OddFieldSL2.minusIdentity F₁ :=
    (CFSG.GH74.GLS.IVK.sl_central_involution e₁ ⟨a, ha₁⟩ hord₁
      (fun k => Subtype.ext (hcomm k k.2 a ha₂))).2
  have hae₂ : e₂ ⟨a, ha₂⟩ = OddFieldSL2.minusIdentity F₂ :=
    (CFSG.GH74.GLS.IVK.sl_central_involution e₂ ⟨a, ha₂⟩ hord₂
      (fun k => Subtype.ext (hcomm a ha₁ k k.2).symm)).2
  obtain ⟨k₁, hk₁, k₂, hk₂, hzk⟩ := (mem_sup_iff_of_comm hcomm z).1 hzmem
  have hk₁c : ∀ y ∈ K₁, y * k₁ = k₁ * y := by
    intro y hy
    have h1 := hzK y (Subgroup.mem_sup_left hy)
    rw [hzk] at h1
    have h2 : k₁ * y * k₂ = y * k₁ * k₂ := by
      calc k₁ * y * k₂ = k₁ * (y * k₂) := by group
        _ = k₁ * (k₂ * y) := by rw [hcomm y hy k₂ hk₂]
        _ = k₁ * k₂ * y := by group
        _ = y * (k₁ * k₂) := h1
        _ = y * k₁ * k₂ := by group
    exact (mul_right_cancel h2).symm
  have hk₂c : ∀ y ∈ K₂, y * k₂ = k₂ * y := by
    intro y hy
    have h1 := hzK y (Subgroup.mem_sup_right hy)
    rw [hzk] at h1
    have h3 : k₁ * (k₂ * y) = k₁ * (y * k₂) := by
      calc k₁ * (k₂ * y) = k₁ * k₂ * y := by group
        _ = y * (k₁ * k₂) := h1
        _ = (y * k₁) * k₂ := by group
        _ = (k₁ * y) * k₂ := by rw [← hcomm k₁ hk₁ y hy]
        _ = k₁ * (y * k₂) := by group
    exact (mul_left_cancel h3).symm
  have hk₁a : k₁ = 1 ∨ k₁ = a := eq_one_or_eq_of_central e₁ ha₁ hae₁ hk₁ hk₁c
  have hk₂a : k₂ = 1 ∨ k₂ = a := eq_one_or_eq_of_central e₂ ha₂ hae₂ hk₂ hk₂c
  have hzK₂ : z ∈ K₂ := by
    rw [hzk]
    rcases hk₁a with h | h
    · rw [h, one_mul]; exact hk₂
    · rw [h]; exact K₂.mul_mem ha₂ hk₂
  have hzK₁ : z ∈ K₁ := by
    rw [hzk]
    rcases hk₂a with h | h
    · rw [h, mul_one]; exact hk₁
    · rw [h]; exact K₁.mul_mem hk₁ ha₁
  refine ⟨hzK₁, hzK₂, ?_⟩
  symm
  apply Subgroup.eq_of_le_of_card_ge
  · rw [Subgroup.zpowers_le]; exact ⟨hzK₁, hzK₂⟩
  · rw [hcard, Nat.card_zpowers, hz2]

structure Ch6Setup (G : Type) [Group G] (Gs : Type) [Group Gs] (q₁ q₂ : ℕ) (z : G)
    (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) [Field F₁] [Field F₂] : Prop where
  S_iso : ∃ (S : Sylow 2 G) (S' : Sylow 2 Gs), Nonempty (↥(S : Subgroup G) ≃* ↥(S' : Subgroup Gs))
  central : IsCentralInvolution z
  one_class : ∀ u : G, orderOf u = 2 → IsConj z u
  O2prime : pPrimeCore 2 ↥(centralizer ({z} : Set G)) = ⊥
  finite₁ : Finite F₁
  finite₂ : Finite F₂
  card₁ : Nat.card F₁ = q₁
  card₂ : Nat.card F₂ = q₂
  odd₁ : Odd q₁
  odd₂ : Odd q₂
  le : q₂ ≤ q₁
  five : 5 ≤ q₁
  iso₁ : Nonempty (↥K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) F₁)
  iso₂ : Nonempty (↥K₂ ≃* Matrix.SpecialLinearGroup (Fin 2) F₂)
  comm : ∀ x ∈ K₁, ∀ y ∈ K₂, x * y = y * x
  inter_card : Nat.card ↥(K₁ ⊓ K₂) = 2
  le_centralizer : K₁ ⊔ K₂ ≤ centralizer ({z} : Set G)
  le_residual : K₁ ⊔ K₂ ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G))
  index_two : (K₁ ⊔ K₂).relIndex (oPrimeResidualOf 2 (centralizer ({z} : Set G))) = 2
  z_mem₁ : z ∈ K₁
  z_mem₂ : z ∈ K₂
  inter_eq : K₁ ⊓ K₂ = Subgroup.zpowers z
  model : ∃ (p f : ℕ) (F : Type) (_ : Field F) (_ : Finite F), p.Prime ∧ p ≠ 2 ∧
    LieModel Gs .G2 0 p f ∧ Nat.card F = p ^ f ∧
    (Nat.card ↥(StatedSL 2 F₁)).factorization 2 = (Nat.card ↥(StatedSL 2 F)).factorization 2 ∧
    (Nat.card ↥(StatedSL 2 F₂)).factorization 2 = (Nat.card ↥(StatedSL 2 F)).factorization 2

theorem ch6_setup {G : Type} [Group G] [Finite G] {Gs : Type} [Group Gs] {q₁ q₂ : ℕ}
    (hr : pRank 2 G = 3) (hAt : IsTwoCentralG2TypeG2At G Gs q₁ q₂) :
    ∃ (z : G) (K₁ K₂ : Subgroup G) (F₁ F₂ : Type) (_ : Field F₁) (_ : Field F₂),
      Ch6Setup G Gs q₁ q₂ z K₁ K₂ F₁ F₂ := by
  obtain ⟨hS, z, hz, hconj, hO, p, f, hp, hp2, hL, F, F₁, F₂, iF, iF₁, iF₂, fF, fF₁, fF₂, hcF,
    hc₁, hc₂, ho₁, ho₂, hle, h5, hs₁, hs₂, K, hKC, hKi, A, B, hAB, hcomm, hcardAB, ⟨eA⟩, ⟨eB⟩⟩ :=
    hAt
  let ι : ↥(centralizer ({z} : Set G)) →* G := (centralizer ({z} : Set G)).subtype
  have hι : Function.Injective ι := (centralizer ({z} : Set G)).subtype_injective
  refine ⟨z, A.map ι, B.map ι, F₁, F₂, iF₁, iF₂, ?_⟩
  have hcomm' : ∀ x ∈ A.map ι, ∀ y ∈ B.map ι, x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hcomm a ha b hb]
  have hcard' : Nat.card ↥(A.map ι ⊓ B.map ι) = 2 := by
    rw [← Subgroup.map_inf A B ι hι, Subgroup.card_map_of_injective hι]
    exact hcardAB
  have hsup : A.map ι ⊔ B.map ι = K.map ι := by
    rw [← Subgroup.map_sup, hAB]
  have hle_C : A.map ι ⊔ B.map ι ≤ centralizer ({z} : Set G) := by
    rw [hsup]
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hle_res : A.map ι ⊔ B.map ι ≤ oPrimeResidualOf 2 (centralizer ({z} : Set G)) := by
    rw [hsup]
    exact Subgroup.map_mono hKC
  have hindex : (A.map ι ⊔ B.map ι).relIndex (oPrimeResidualOf 2 (centralizer ({z} : Set G))) = 2 := by
    rw [hsup]
    unfold oPrimeResidualOf
    rw [Subgroup.relIndex_map_map_of_injective K _ hι]
    exact hKi
  have hz2 : orderOf z = 2 := hz.1
  have hzK : ∀ k ∈ A.map ι ⊔ B.map ι, z * k = k * z := by
    intro k hk
    exact (Subgroup.mem_centralizer_iff.1 (hle_C hk) z (Set.mem_singleton z))
  let e₁ : ↥(A.map ι) ≃* Matrix.SpecialLinearGroup (Fin 2) F₁ :=
    (Subgroup.equivMapOfInjective A ι hι).symm.trans
      (eA.trans (specialLinearGroupEquivStatedSL 2 F₁).symm)
  let e₂ : ↥(B.map ι) ≃* Matrix.SpecialLinearGroup (Fin 2) F₂ :=
    (Subgroup.equivMapOfInjective B ι hι).symm.trans
      (eB.trans (specialLinearGroupEquivStatedSL 2 F₂).symm)
  have hodd₁ : Odd (Nat.card F₁) := ho₁
  have hodd₂ : Odd (Nat.card F₂) := ho₂
  obtain ⟨hz₁, hz₂, hinter⟩ := z_mem_inter_of_pRank_le hodd₁ hodd₂ e₁ e₂ hcomm' hcard' hz2
    (by rw [hsup] at hzK ⊢; exact hzK) hr.le
  exact
    { S_iso := hS
      central := hz
      one_class := hconj
      O2prime := hO
      finite₁ := fF₁
      finite₂ := fF₂
      card₁ := hc₁
      card₂ := hc₂
      odd₁ := hc₁ ▸ ho₁
      odd₂ := hc₂ ▸ ho₂
      le := hc₁ ▸ hc₂ ▸ hle
      five := hc₁ ▸ h5
      iso₁ := ⟨e₁⟩
      iso₂ := ⟨e₂⟩
      comm := hcomm'
      inter_card := hcard'
      le_centralizer := hle_C
      le_residual := hle_res
      index_two := hindex
      z_mem₁ := hz₁
      z_mem₂ := hz₂
      inter_eq := hinter
      model := ⟨p, f, F, iF, fF, hp, hp2, hL, hcF, hs₁, hs₂⟩ }

end CFSG.GH74.GLS.Stage4.Rest
