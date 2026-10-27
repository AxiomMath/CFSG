module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13HE64a
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Sig
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.Lemma611F
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.I13Case

public section

namespace CFSG.EvenSporadicStandard.Fin76b

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Blueprint.NativeSporadic
open scoped Pointwise

structure IsKlein {G : Type*} [Group G] (B : Subgroup G) (b₁ b₂ : G) : Prop where
  mem₁ : b₁ ∈ B
  mem₂ : b₂ ∈ B
  sq₁ : b₁ * b₁ = 1
  sq₂ : b₂ * b₂ = 1
  comm : b₁ * b₂ = b₂ * b₁
  ne₁ : b₁ ≠ 1
  ne₂ : b₂ ≠ 1
  ne₁₂ : b₁ ≠ b₂

namespace IsKlein

variable {G : Type*} [Group G] {B : Subgroup G} {b₁ b₂ : G} (k : IsKlein B b₁ b₂)

include k

theorem cases {g : G} (hg : g ∈ closure ({b₁, b₂} : Set G)) :
    g = 1 ∨ g = b₁ ∨ g = b₂ ∨ g = b₁ * b₂ :=
  E613.closure_pair_subset k.sq₁ k.sq₂ k.comm hg

omit k in
theorem b₁_mem_grp : b₁ ∈ closure ({b₁, b₂} : Set G) := subset_closure (by simp)

omit k in
theorem b₂_mem_grp : b₂ ∈ closure ({b₁, b₂} : Set G) := subset_closure (by simp)

theorem grp_le : closure ({b₁, b₂} : Set G) ≤ B := by
  rw [closure_le]
  rintro g (rfl | rfl)
  · exact k.mem₁
  · exact k.mem₂

theorem prod_mem : b₁ * b₂ ∈ B := mul_mem k.mem₁ k.mem₂

theorem prod_sq : (b₁ * b₂) * (b₁ * b₂) = 1 := by
  calc (b₁ * b₂) * (b₁ * b₂) = b₁ * (b₂ * b₁) * b₂ := by group
    _ = b₁ * (b₁ * b₂) * b₂ := by rw [← k.comm]
    _ = (b₁ * b₁) * (b₂ * b₂) := by group
    _ = 1 := by rw [k.sq₁, k.sq₂, one_mul]

theorem prod_ne_one : b₁ * b₂ ≠ 1 := by
  intro h
  apply k.ne₁₂
  have h1 : b₁ = b₂⁻¹ := mul_eq_one_iff_eq_inv.1 h
  rw [h1]
  exact inv_eq_of_mul_eq_one_right k.sq₂

theorem sq_grp {g : G} (hg : g ∈ closure ({b₁, b₂} : Set G)) : g * g = 1 := by
  rcases k.cases hg with rfl | rfl | rfl | rfl
  · simp
  · exact k.sq₁
  · exact k.sq₂
  · exact k.prod_sq

theorem comm_grp {g g' : G} (hg : g ∈ closure ({b₁, b₂} : Set G))
    (hg' : g' ∈ closure ({b₁, b₂} : Set G)) : g * g' = g' * g := by
  have h1 : closure ({b₁, b₂} : Set G) ≤
      centralizer ((closure ({b₁, b₂} : Set G) : Subgroup G) : Set G) := by
    rw [Subgroup.centralizer_closure, closure_le]
    rintro g (rfl | rfl)
    · exact mem_centralizer_iff.2 (by rintro h (rfl | rfl); exacts [rfl, k.comm.symm])
    · exact mem_centralizer_iff.2 (by rintro h (rfl | rfl); exacts [k.comm, rfl])
  exact mem_centralizer_iff.1 (h1 hg') g hg

end IsKlein

namespace I13Ctx

variable {G : Type} [Group G] [Finite G] {L : Subgroup G} {z t : G} {T₀ E : Subgroup G}
  {Q : Sylow 2 G} {x β : G} {B S : Subgroup G} {α : G}
  (c : I13Ctx L z t T₀ E Q x β B S α)

include c

theorem rho1_B (b : ↥B) : c.rho1 ⟨(b : G), c.B_le_N1 b.2⟩ = c.kappa b :=
  congrArg Prod.fst (c.rho_B b)

theorem theta_conj_B (b : ↥B) (w : ↥c.W1) :
    c.thetaHom ⟨(b : G) * w * (b : G)⁻¹, c.N1_W1 (c.B_le_N1 b.2) w.2⟩ =
      c.kappa b (c.thetaHom w) := by
  have h := c.rho1_theta ⟨(b : G), c.B_le_N1 b.2⟩ w
  rw [c.rho1_B] at h
  exact h.symm

theorem theta_mul' {w w' : G} (hw : w ∈ c.W1) (hw' : w' ∈ c.W1) :
    (w * w') * (z * (w * w') * z⁻¹) = (w * (z * w * z⁻¹)) * (w' * (z * w' * z⁻¹)) :=
  c.h.theta_mul c.hα c.hF c.hWr c.hBD hw hw'

theorem theta_eq_iff' {w w' : G} (hw : w ∈ c.W1) (hw' : w' ∈ c.W1) :
    w * (z * w * z⁻¹) = w' * (z * w' * z⁻¹) ↔ w' = w ∨ w' = w * t :=
  c.h.theta_eq_iff c.hα c.hF c.hWr c.hBD hw hw'

theorem theta_conj_B' {b : G} (hb : b ∈ B) (w : G) :
    (b * w * b⁻¹) * (z * (b * w * b⁻¹) * z⁻¹) = b * (w * (z * w * z⁻¹)) * b⁻¹ :=
  theta_conj_of_comm (c.h.BS b hb z c.h.zS) w

theorem B_comm_z {b : G} (hb : b ∈ B) : b * z = z * b := c.h.BS b hb z c.h.zS

theorem B_comm_alpha {b : G} (hb : b ∈ B) : b * α = α * b := c.h.BS b hb α c.hα.mem

theorem W1_comm {w w' : G} (hw : w ∈ c.W1) (hw' : w' ∈ c.W1) :
    w * w' * w⁻¹ * w'⁻¹ = 1 ∨ w * w' * w⁻¹ * w'⁻¹ = α := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, h, -⟩ := c.cl
  exact h w hw w' hw'

theorem W1_sq {w : G} (hw : w ∈ c.W1) : w * w = 1 ∨ w * w = α :=
  c.h.sq_W1 c.hF c.hα c.cl w hw

theorem mem_Zs_of_W1_W2 {w : G} (h1 : w ∈ c.W1) (h2 : w ∈ c.W2) : w ∈ c.Zs :=
  c.h.W1_inf_W2 c.hα h1 h2

theorem z_conj_alpha : z * α * z⁻¹ = α * t := c.h.z_conj_alpha c.hα

theorem z_conj_t : z * t * z⁻¹ = t := c.h.z_conj_t

theorem t_comm_Qs {q : G} (hq : q ∈ c.Qs) : t * q = q * t :=
  c.Zs_comm_Qs c.t_mem_Zs hq

structure KleinE (b₁ b₂ : G) : Prop where
  cocycle : ∀ b : G, (b = b₁ ∨ b = b₂ ∨ b = b₁ * b₂) → ∀ e ∈ E, e * (b * e * b⁻¹) = 1 →
    ∃ c' ∈ E, e * (b * c' * b⁻¹) = c'
  fix_card : Set.ncard {e : G | e ∈ E ∧ b₁ * e * b₁⁻¹ = e} = 4
  fix_sq : ∀ e ∈ E, b₁ * e * b₁⁻¹ = e → e * e = 1
  fix_sub : ∀ e ∈ E, b₁ * e * b₁⁻¹ = e → b₂ * e * b₂⁻¹ = e
  gen : ∃ (e₀ : ↥E) (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ B), Subgroup.closure
    ({e₀, c.kappa ⟨b₁, hb₁⟩ e₀, c.kappa ⟨b₂, hb₂⟩ e₀,
      c.kappa ⟨b₁, hb₁⟩ (c.kappa ⟨b₂, hb₂⟩ e₀)} : Set ↥E) = ⊤

theorem kleinE_of_facts (hF : EFacts613 E t) {b₁ b₂ : G} (k : IsKlein B b₁ b₂) :
    c.KleinE b₁ b₂ := by
  obtain ⟨π, -, hfix, hcoc, hkl⟩ := hF.exists_pi
  obtain ⟨hB1, hB2, hcomm, hne, hnin⟩ := c.klein_kappa (π := π) k.mem₁ k.mem₂ k.sq₁ k.sq₂
    k.comm k.ne₁ k.ne₂ k.ne₁₂
  have hB3 : BInv E π (c.kappa ⟨b₁ * b₂, k.prod_mem⟩) := by
    refine ⟨?_, c.pi_kappa_mem ⟨b₁ * b₂, k.prod_mem⟩, fun hin => ?_⟩
    · rw [← map_mul, ← map_one c.kappa]
      congr 1
      exact Subtype.ext k.prod_sq
    · exact k.prod_ne_one (congrArg Subtype.val (c.eq_one_of_kappa_mem_inn hin))
  obtain ⟨hf1, hf2⟩ := hfix _ hB1
  obtain ⟨hsub, hgen, -⟩ := hkl _ _ hB1 hB2 hcomm hne hnin
  have hconj : ∀ (b : ↥B) (e : ↥E), ((c.kappa b e : ↥E) : G) = (b : G) * e * (b : G)⁻¹ :=
    fun b e => rfl
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro b hb e he hee
    have hbB : b ∈ B := by
      rcases hb with rfl | rfl | rfl
      exacts [k.mem₁, k.mem₂, k.prod_mem]
    have hbi : BInv E π (c.kappa ⟨b, hbB⟩) := by
      rcases hb with rfl | rfl | rfl
      exacts [hB1, hB2, hB3]
    obtain ⟨c', hc'⟩ := hcoc _ hbi ⟨e, he⟩ (Subtype.ext (by
      rw [Subgroup.coe_mul, hconj]
      exact hee))
    refine ⟨c', c'.2, ?_⟩
    have := congrArg Subtype.val hc'
    rw [Subgroup.coe_mul, hconj] at this
    exact this
  · have hset : {e : G | e ∈ E ∧ b₁ * e * b₁⁻¹ = e} =
        Subtype.val '' {e : ↥E | c.kappa ⟨b₁, k.mem₁⟩ e = e} := by
      ext e
      constructor
      · rintro ⟨he, hee⟩
        exact ⟨⟨e, he⟩, Subtype.ext (by rw [hconj]; exact hee), rfl⟩
      · rintro ⟨e', he', rfl⟩
        refine ⟨e'.2, ?_⟩
        have := congrArg Subtype.val he'
        rw [hconj] at this
        exact this
    rw [hset, Set.ncard_image_of_injective _ Subtype.val_injective, ← Nat.card_coe_set_eq]
    exact hf1
  · intro e he hee
    have := hf2 ⟨e, he⟩ (Subtype.ext (by rw [hconj]; exact hee))
    exact congrArg Subtype.val this
  · intro e he hee
    have := hsub ⟨e, he⟩ (Subtype.ext (by rw [hconj]; exact hee))
    have h2 := congrArg Subtype.val this
    rw [hconj] at h2
    exact h2
  · obtain ⟨e₀, he₀⟩ := hgen
    exact ⟨e₀, k.mem₁, k.mem₂, he₀⟩

end I13Ctx

end CFSG.EvenSporadicStandard.Fin76b
