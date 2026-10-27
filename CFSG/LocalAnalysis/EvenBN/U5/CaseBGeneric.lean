module

public import CFSG.LocalAnalysis.EvenBN.U5.PrelimModules
public import CFSG.LocalAnalysis.EvenBN.U5.ModelA2N2Two
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.ThreeSubgroups

public section

namespace CFSG.LocalAnalysis.EvenBN.U5

open Subgroup
open scoped commutatorElement

section Generic

variable {G : Type*} [Group G]

@[expose] def normalClosureIn (M X : Subgroup G) : Subgroup G :=
  (normalClosure ((X.subgroupOf M : Subgroup M) : Set M)).map M.subtype

theorem normalClosureIn_le_self (M X : Subgroup G) : normalClosureIn M X ≤ M :=
  map_subtype_le _

theorem le_normalClosureIn {M X : Subgroup G} (hXM : X ≤ M) : X ≤ normalClosureIn M X :=
  fun x hx => ⟨⟨x, hXM hx⟩, subset_normalClosure (show (⟨x, hXM hx⟩ : M) ∈ X.subgroupOf M from hx),
    rfl⟩

theorem normalClosureIn_le {M X T : Subgroup G} (hXT : X ≤ T)
    (hMT : M ≤ normalizer (T : Set G)) : normalClosureIn M X ≤ T := by
  have : (T.subgroupOf M).Normal := ⟨fun n hn g => by
    rw [mem_subgroupOf] at hn ⊢
    simpa using (mem_normalizer_iff.1 (hMT g.2) n).1 hn⟩
  have hle : normalClosure ((X.subgroupOf M : Subgroup M) : Set M) ≤ T.subgroupOf M :=
    normalClosure_le_normal fun x hx => mem_subgroupOf.2 (hXT (mem_subgroupOf.1 hx))
  rintro _ ⟨y, hy, rfl⟩
  exact mem_subgroupOf.1 (hle hy)

variable [Finite G]

theorem le_normalizer_normalClosureIn (M X : Subgroup G) :
    M ≤ normalizer (normalClosureIn M X : Set G) := by
  intro m hm
  refine mem_normalizer_fintype fun x hx => ?_
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨⟨m, hm⟩ * y * ⟨m, hm⟩⁻¹, (normalClosure_normal).conj_mem y hy ⟨m, hm⟩, rfl⟩

theorem commutator_normalClosureIn {M X : Subgroup G} (hXM : X ≤ M) (hX : ⁅X, X⁆ = X) :
    ⁅normalClosureIn M X, normalClosureIn M X⁆ = normalClosureIn M X := by
  set N := normalClosureIn M X with hN
  refine le_antisymm (commutator_le_self' N) (normalClosureIn_le ?_ fun m hm => ?_)
  · exact hX.ge.trans (commutator_mono (le_normalClosureIn hXM) (le_normalClosureIn hXM))
  · have hmN := le_normalizer_normalClosureIn M X hm
    refine mem_normalizer_fintype fun c hc => ?_
    have hmap : N.map (MulAut.conj m).toMonoidHom = N := map_conj_eq_of_mem_normalizer hmN
    have : m * c * m⁻¹ ∈ ⁅N, N⁆.map (MulAut.conj m).toMonoidHom := ⟨c, hc, rfl⟩
    rwa [map_commutator, hmap] at this

end Generic

section Generic₂

variable {G : Type*} [Group G]

theorem eq_of_mul_eq_mul_of_inf_eq_bot {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a a' b b' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have hmem : a'⁻¹ * a ∈ A ⊓ B :=
    Subgroup.mem_inf.2 ⟨mul_mem (inv_mem ha') ha, h1 ▸ mul_mem hb' (inv_mem hb)⟩
  rw [hAB, mem_bot] at hmem
  have haa : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [hmem, mul_one]
  refine ⟨haa, ?_⟩
  rw [haa] at h
  exact mul_left_cancel h

theorem sup_inf_eq_of_le {A B C : Subgroup G} (hAC : A ≤ C) (hB : B ≤ normalizer (A : Set G)) :
    (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  apply SetLike.coe_injective
  rw [coe_inf, coe_mul_of_right_le_normalizer_left A B hB,
    coe_mul_of_right_le_normalizer_left A (B ⊓ C) (inf_le_left.trans hB), mul_inf_assoc A B C hAC]

theorem sup_inf_eq_of_le' {A B C : Subgroup G} (hAC : A ≤ C) (hA : A ≤ normalizer (B : Set G)) :
    (A ⊔ B) ⊓ C = A ⊔ (B ⊓ C) := by
  have hA' : A ≤ normalizer ((B ⊓ C : Subgroup G) : Set G) := fun a ha => by
    rw [mem_normalizer_iff]
    intro x
    rw [Subgroup.mem_inf, Subgroup.mem_inf, ← mem_normalizer_iff.1 (hA ha) x,
      ← mem_normalizer_iff.1 (le_normalizer (hAC ha)) x]
  apply SetLike.coe_injective
  rw [coe_inf, coe_mul_of_left_le_normalizer_right A B hA,
    coe_mul_of_left_le_normalizer_right A (B ⊓ C) hA', mul_inf_assoc A B C hAC]

theorem commutatorElement_mem_of_perfect {K F F₂ : Subgroup G} (hK : ⁅K, K⁆ = K)
    (hF : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a)
    (hKF : ∀ k ∈ K, ∀ f ∈ F, k * f * k⁻¹ ∈ F)
    (htriv : ∀ k ∈ K, ∀ f ∈ F, f⁻¹ * (k * f * k⁻¹) ∈ F₂) {y : G}
    (hy : ∀ k ∈ K, ⁅k, y⁆ ∈ F) : ∀ k ∈ K, ⁅k, y⁆ ∈ F₂ := by
  have : IsMulCommutative F := ⟨⟨fun a b => Subtype.ext (hF a a.2 b b.2)⟩⟩
  have : (F₂.subgroupOf F).Normal := normal_of_isMulCommutative _
  have hQ : IsMulCommutative (F ⧸ F₂.subgroupOf F) := ⟨⟨fun a b => by
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      show a * b = b * a from Subtype.ext (hF a a.2 b b.2)]⟩⟩
  let φ : K →* F ⧸ F₂.subgroupOf F :=
    { toFun := fun k => QuotientGroup.mk ⟨⁅(k : G), y⁆, hy k k.2⟩
      map_one' := by
        rw [← QuotientGroup.mk_one]
        congr 1
        exact Subtype.ext (by simp)
      map_mul' := fun k₁ k₂ => by
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq, mem_subgroupOf]
        have h1 := hy k₁ k₁.2
        have h2 := hy k₂ k₂.2
        have h3 := hKF k₁ k₁.2 _ h2
        have hca := hF _ (inv_mem h3) _ h1
        have e : ⁅(k₁ : G) * k₂, y⁆ =
            ((k₁ : G) * ⁅(k₂ : G), y⁆ * (k₁ : G)⁻¹) * ⁅(k₁ : G), y⁆ := by
          simp only [commutatorElement_def]
          group
        simp only [coe_mul, coe_inv, e]
        have e2 : (((k₁ : G) * ⁅(k₂ : G), y⁆ * (k₁ : G)⁻¹) * ⁅(k₁ : G), y⁆)⁻¹ *
            (⁅(k₁ : G), y⁆ * ⁅(k₂ : G), y⁆) =
            ⁅(k₁ : G), y⁆⁻¹ * (((k₁ : G) * ⁅(k₂ : G), y⁆ * (k₁ : G)⁻¹)⁻¹ * ⁅(k₁ : G), y⁆) *
              ⁅(k₂ : G), y⁆ := by group
        rw [e2, hca]
        have e3 : ⁅(k₁ : G), y⁆⁻¹ * (⁅(k₁ : G), y⁆ * ((k₁ : G) * ⁅(k₂ : G), y⁆ * (k₁ : G)⁻¹)⁻¹) *
            ⁅(k₂ : G), y⁆ = (⁅(k₂ : G), y⁆⁻¹ * ((k₁ : G) * ⁅(k₂ : G), y⁆ * (k₁ : G)⁻¹))⁻¹ := by
          group
        rw [e3]
        exact inv_mem (htriv k₁ k₁.2 _ h2) }
  have hper : Group.IsPerfect K := Subgroup.isPerfect_iff.2 hK
  have hker : φ.ker = ⊤ := by
    rw [eq_top_iff, ← hper.commutator_eq_top]
    exact Abelianization.commutator_subset_ker φ
  intro k hk
  have hk' : φ ⟨k, hk⟩ = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    trivial
  change QuotientGroup.mk (⟨⁅k, y⁆, hy k hk⟩ : F) = (1 : F ⧸ F₂.subgroupOf F) at hk'
  rw [QuotientGroup.eq_one_iff, mem_subgroupOf] at hk'
  exact hk'

variable [Finite G]

theorem commutator_eq_of_card {k : Type*} [Field k] [Finite k] {m : ℕ} (hk : Nat.card k = 2 ^ m)
    (hm : 2 ≤ m) (hm3 : m ≠ 3) {X : Subgroup G} (φ : X ≃* Matrix.SpecialLinearGroup (Fin 2) k)
    {A : Subgroup G} (hA : IsPGroup 2 A) (hXA : X ≤ normalizer (A : Set G))
    (hcen : A ⊓ centralizer (X : Set G) = ⊥) (hcard : Nat.card A = 2 ^ (2 * m)) :
    ⁅A, X⁆ = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAX : ⁅A, X⁆ ≤ A := commutator_le.2 fun a ha x hx => by
    have h1 : x * a⁻¹ * x⁻¹ ∈ A := (mem_normalizer_iff.1 (hXA hx) a⁻¹).1 (inv_mem ha)
    rw [show ⁅a, x⁆ = a * (x * a⁻¹ * x⁻¹) by rw [commutatorElement_def]; group]
    exact mul_mem ha h1
  have hXB : X ≤ normalizer ((⁅A, X⁆ : Subgroup G) : Set G) := fun x hx => by
    refine mem_normalizer_fintype fun c hc => ?_
    have hA' : A.map (MulAut.conj x).toMonoidHom = A := map_conj_eq_of_mem_normalizer (hXA hx)
    have hX' : X.map (MulAut.conj x).toMonoidHom = X :=
      map_conj_eq_of_mem_normalizer (le_normalizer hx)
    have : x * c * x⁻¹ ∈ ⁅A, X⁆.map (MulAut.conj x).toMonoidHom := ⟨c, hc, rfl⟩
    rwa [map_commutator, hA', hX'] at this
  by_contra hne
  have hlt : Nat.card (⁅A, X⁆ : Subgroup G) < 2 ^ (2 * m) := by
    rw [← hcard]
    exact lt_of_le_of_ne (card_le_of_le hAX) fun e => hne (eq_of_le_of_card_ge hAX e.ge)
  have hcent := Prelim.le_centralizer_of_card_lt hk hm hm3 φ hXB (hA.to_le hAX) hlt
  have h1 : ⁅⁅A, X⁆, X⁆ = ⊥ := by
    rw [commutator_comm]
    exact commutator_eq_bot_iff_le_centralizer.2 hcent
  have h2 : ⁅⁅X, A⁆, X⁆ = ⊥ := by
    rw [commutator_comm X A]
    exact h1
  have h3 := CFSG.SignalizerFunctorTheorem.McBride.three_subgroups_lemma (X := X) (Y := A)
    (Z := X) h2 h1
  have h4 : 4 ≤ Nat.card k := by
    rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card k h4
  have hXp : Group.IsPerfect X := Group.IsPerfect.ofSurjective (f := φ.symm.toMonoidHom)
    φ.symm.surjective
  rw [Subgroup.isPerfect_iff.1 hXp] at h3
  have hAc : A ≤ centralizer (X : Set G) := by
    rw [commutator_comm] at h3
    exact commutator_eq_bot_iff_le_centralizer.1 h3
  have hbot : A = ⊥ := by
    rw [← hcen]
    exact (inf_eq_left.2 hAc).symm
  rw [hbot, card_bot] at hcard
  have : 1 < 2 ^ (2 * m) := Nat.one_lt_pow (by omega) (by norm_num)
  omega

end Generic₂

end CFSG.LocalAnalysis.EvenBN.U5
