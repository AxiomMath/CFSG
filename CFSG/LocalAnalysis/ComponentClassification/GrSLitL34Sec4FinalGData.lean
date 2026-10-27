module

public import CFSG.LocalAnalysis.ComponentClassification.GrSLitL34Sec4EndT

public section

namespace CFSG.ComponentClassification.GrSLit.FinalG

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

structure Data (G : Type) [Group G] [Finite G] where
  a : G
  c : G
  J : Subgroup G
  S : Subgroup G
  B : Subgroup G
  simple : IsSimpleGroup G
  nab : ∃ g h : G, g * h ≠ h * g
  centralizer_le : centralizer ({a} : Set G) ≤ normalizer (J : Set G)
  perfect : ⁅J, J⁆ = J
  l34 : IsL34Type (J ⧸ Open.fusionZStar J)
  sylow : ∃ P : Sylow 2 G, (P : Subgroup G) = S
  sylowNJ : IsSylowTwoIn S (normalizer (J : Set G))
  S_le_NB : S ≤ normalizer (B : Set G)
  a_cent : ∀ s ∈ S, s * a = a * s
  a_ne : a ≠ 1
  B_le : B ≤ S ⊓ J
  eight : IsEightGroup B
  BZ : B ⊓ zStarIn J = zpowers a
  biff : ∀ y ∈ S ⊓ J, (∀ w ∈ S ⊓ J, y⁻¹ * w⁻¹ * y * w ∈ zStarIn J) ↔ y ∈ B ⊔ (S ⊓ zStarIn J)
  aut : ∀ σ : ↥B ≃* ↥B, ∃ n ∈ normalizer (B : Set G), ∀ b : ↥B, n⁻¹ * (b : G) * n = (σ b : G)
  cls : ∀ y ∈ S ⊓ J, y * y = 1 → y ≠ 1 → ∃ g : G, y = g⁻¹ * a * g
  c_mem : c ∈ S
  c_sq : c * c = 1
  c_not_mem : c ∉ withKernel J
  T_eq : S ⊓ centralizer (B : Set G) = S ⊓ J ⊓ centralizer (B : Set G) ⊔ zpowers c
  T₁_iso : Nonempty (↥(S ⊓ J ⊓ centralizer (B : Set G)) ≃* Multiplicative (Fin 3 → ZMod 4))
  T₁_omega : ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), s * s = 1 → s ∈ B
  T₁_inv : ∀ s ∈ S ⊓ J ⊓ centralizer (B : Set G), c * s * c = s⁻¹
  N_T₁ : normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G) ≤
    normalizer ((S ⊓ J ⊓ centralizer (B : Set G) : Subgroup G) : Set G)
  N_B : normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G) ≤ normalizer (B : Set G)
  phi : ∃ φ : ↥(normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G)) →*
      GL (Fin 3) (ZMod 2), Function.Surjective φ ∧
    φ.ker = (centralizer (B : Set G)).subgroupOf
      (normalizer ((S ⊓ centralizer (B : Set G) : Subgroup G) : Set G))
  card_R : Nat.card ↥(S ⊓ J) = 256
  kernel_cyclic : IsCyclic ↥(S ⊓ coreActionKernel J)
  sq_mem : ∀ s ∈ S, s * s ∈ withKernel J

namespace Data

variable {G : Type} [Group G] [Finite G] (D : Data G)

abbrev T : Subgroup G := D.S ⊓ centralizer (D.B : Set G)

abbrev T₁ : Subgroup G := D.S ⊓ D.J ⊓ centralizer (D.B : Set G)

abbrev L : Subgroup G := normalizer (D.T : Set G)

abbrev R : Subgroup G := D.S ⊓ D.J

noncomputable def φ : ↥D.L →* GL (Fin 3) (ZMod 2) := D.phi.choose

theorem φ_surjective : Function.Surjective D.φ := D.phi.choose_spec.1

theorem φ_ker : D.φ.ker = (centralizer (D.B : Set G)).subgroupOf D.L := D.phi.choose_spec.2

theorem a_mem_B : D.a ∈ D.B := (le_of_eq D.BZ.symm).trans inf_le_left (mem_zpowers _)

theorem B_comm {x y : G} (hx : x ∈ D.B) (hy : y ∈ D.B) : x * y = y * x := D.eight.1.1 x hx y hy

theorem B_sq {x : G} (hx : x ∈ D.B) : x * x = 1 := D.eight.1.2 x hx

theorem a_sq : D.a * D.a = 1 := D.B_sq D.a_mem_B

theorem isPGroup_S : IsPGroup 2 D.S := GrS4.isPGroup_of_isSylowTwoIn D.sylowNJ

theorem T₁_le_T : D.T₁ ≤ D.T := fun _ ht => ⟨ht.1.1, ht.2⟩

theorem T₁_le_R : D.T₁ ≤ D.R := fun _ ht => ht.1

theorem T₁_le_S : D.T₁ ≤ D.S := fun _ ht => ht.1.1

theorem T₁_le_J : D.T₁ ≤ D.J := fun _ ht => ht.1.2

theorem T_le_S : D.T ≤ D.S := inf_le_left

theorem T_le_C : D.T ≤ centralizer (D.B : Set G) := inf_le_right

theorem S_le_L : D.S ≤ D.L := by
  intro s hs
  refine GrS4.mem_normalizer_of_map_le_self ?_
  rintro _ ⟨t, ht, rfl⟩
  change s * t * s⁻¹ ∈ D.T
  refine mem_inf.mpr ⟨mul_mem (mul_mem hs (D.T_le_S ht)) (inv_mem hs),
    mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hb' : s⁻¹ * b * s ∈ D.B := by
    have := (mem_normalizer_iff.mp (D.S_le_NB (inv_mem hs)) b).mp hb
    rwa [inv_inv] at this
  have h1 := mem_centralizer_iff.mp (D.T_le_C ht) _ hb'
  calc b * (s * t * s⁻¹) = s * ((s⁻¹ * b * s) * t) * s⁻¹ := by group
    _ = s * (t * (s⁻¹ * b * s)) * s⁻¹ := by rw [h1]
    _ = s * t * s⁻¹ * b := by group

theorem c_mem_T : D.c ∈ D.T := by
  rw [show D.T = _ from D.T_eq]
  exact (le_sup_right : zpowers D.c ≤ _) (mem_zpowers _)

theorem c_not_mem_J : D.c ∉ D.J := fun h => D.c_not_mem ((le_sup_left : D.J ≤ withKernel D.J) h)

theorem c_not_mem_T₁ : D.c ∉ D.T₁ := fun h => D.c_not_mem_J (D.T₁_le_J h)

theorem c_inv : D.c⁻¹ = D.c := inv_eq_of_mul_eq_one_right D.c_sq

theorem c_ne_one : D.c ≠ 1 := fun h => D.c_not_mem_T₁ (h ▸ one_mem _)

theorem orderOf_c : orderOf D.c = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact D.c_sq) D.c_ne_one

theorem c_mem_N_T₁ : D.c ∈ normalizer (D.T₁ : Set G) := by
  refine GrS4.mem_normalizer_of_map_le_self ?_
  rintro _ ⟨s, hs, rfl⟩
  change D.c * s * D.c⁻¹ ∈ D.T₁
  rw [D.c_inv, D.T₁_inv s hs]
  exact inv_mem hs

theorem mem_T {t : G} (ht : t ∈ D.T) : t ∈ D.T₁ ∨ t * D.c ∈ D.T₁ := by
  have hle : zpowers D.c ≤ normalizer (D.T₁ : Set G) := zpowers_le.mpr D.c_mem_N_T₁
  have ht' : t ∈ ((D.T₁ : Set G) * (zpowers D.c : Set G)) := by
    rw [← coe_mul_of_right_le_normalizer_left D.T₁ (zpowers D.c) hle, ← D.T_eq]
    exact ht
  obtain ⟨s, hs, u, hu, rfl⟩ := ht'
  rcases GrS4.eq_one_or_eq_of_mem_zpowers D.c_sq hu with rfl | rfl
  · left
    simpa using hs
  · right
    rw [mul_assoc, D.c_sq, mul_one]
    exact hs

theorem sq_eq_one_of_mem_T {t : G} (ht : t ∈ D.T) (htT : t ∉ D.T₁) : t * t = 1 := by
  rcases D.mem_T ht with h | h
  · exact absurd h htT
  · have h1 := D.T₁_inv _ h
    have e : (t * D.c) * (D.c * (t * D.c) * D.c) = t * (D.c * D.c) * t * (D.c * D.c) := by group
    calc t * t = (t * D.c) * (D.c * (t * D.c) * D.c) := by rw [e, D.c_sq, mul_one, mul_one]
      _ = 1 := by rw [h1, mul_inv_cancel]

theorem T₁_pow_four {t : G} (ht : t ∈ D.T₁) : t ^ 4 = 1 := by
  obtain ⟨e⟩ := D.T₁_iso
  have h : e (⟨t, ht⟩ ^ 4) = 1 := by
    rw [map_pow]
    refine Multiplicative.toAdd.injective ?_
    funext i
    show 4 • (Multiplicative.toAdd (e ⟨t, ht⟩)) i = 0
    rw [nsmul_eq_mul]
    exact (show ((4 : ℕ) : ZMod 4) = 0 from rfl) ▸ zero_mul _
  have h2 : (⟨t, ht⟩ : ↥D.T₁) ^ 4 = 1 := e.injective (by rw [h, map_one])
  exact congrArg Subtype.val h2

theorem card_T₁ : Nat.card D.T₁ = 64 := by
  obtain ⟨e⟩ := D.T₁_iso
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card]
  rfl

theorem L_le_N_T₁ : D.L ≤ normalizer (D.T₁ : Set G) := D.N_T₁

theorem L_le_N_B : D.L ≤ normalizer (D.B : Set G) := D.N_B

theorem conj_mem_T₁ {x t : G} (hx : x ∈ D.L) (ht : t ∈ D.T₁) : x * t * x⁻¹ ∈ D.T₁ :=
  (mem_normalizer_iff.mp (D.L_le_N_T₁ hx) t).mp ht

theorem conj_mem_T₁_iff {x t : G} (hx : x ∈ D.L) : x * t * x⁻¹ ∈ D.T₁ ↔ t ∈ D.T₁ :=
  (mem_normalizer_iff.mp (D.L_le_N_T₁ hx) t).symm

theorem conj_mem_T {x t : G} (hx : x ∈ D.L) (ht : t ∈ D.T) : x * t * x⁻¹ ∈ D.T :=
  (mem_normalizer_iff.mp hx t).mp ht

theorem conj_c_mul_mem {x : G} (hx : x ∈ D.L) : x * D.c * x⁻¹ * D.c ∈ D.T₁ := by
  rcases D.mem_T (D.conj_mem_T hx D.c_mem_T) with h | h
  · exact absurd ((D.conj_mem_T₁_iff hx).mp h) D.c_not_mem_T₁
  · exact h

theorem sylow_T : IsSylowTwoIn D.T (centralizer (D.B : Set G)) :=
  GrS4.isSylowTwoIn_inf_centralizer D.sylow D.S_le_NB

theorem R_act {r b : G} (hr : r ∈ D.R) (hb : b ∈ D.B) :
    r⁻¹ * b * r = b ∨ r⁻¹ * b * r = b * D.a := by
  have h1 := ((D.biff b (D.B_le hb)).mpr ((le_sup_left : D.B ≤ _) hb)) r hr
  have h2 : r⁻¹ * b * r ∈ D.B := by
    have := (mem_normalizer_iff.mp (D.S_le_NB (inv_mem hr.1)) b).mp hb
    rwa [inv_inv] at this
  have h3 : b⁻¹ * (r⁻¹ * b * r) ∈ D.B ⊓ zStarIn D.J :=
    mem_inf.mpr ⟨mul_mem (inv_mem hb) h2,
      by rw [show b⁻¹ * (r⁻¹ * b * r) = b⁻¹ * r⁻¹ * b * r by group]; exact h1⟩
  rw [D.BZ] at h3
  rcases GrS4.eq_one_or_eq_of_mem_zpowers D.a_sq h3 with h | h
  · left
    calc r⁻¹ * b * r = b * (b⁻¹ * (r⁻¹ * b * r)) := by group
      _ = b := by rw [h, mul_one]
  · right
    calc r⁻¹ * b * r = b * (b⁻¹ * (r⁻¹ * b * r)) := by group
      _ = b * D.a := by rw [h]

theorem sylow_L : IsSylowTwoIn D.S D.L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := D.sylow
  refine GrS4.isSylowTwoIn_of_not_dvd D.S_le_L D.isPGroup_S fun h => ?_
  have h2 := h.trans (relIndex_dvd_index_of_le D.S_le_L)
  rw [← hP] at h2
  exact P.not_dvd_index h2

end Data

end CFSG.ComponentClassification.GrSLit.FinalG
