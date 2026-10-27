module

public import CFSG.CGT.PushingUpLit.A78S4.Side

public section

namespace CFSG.CGT.PushingUpLit.A78S4

open CFSG.CGT.PushingUpLit CFSG.CGT.PushingUpLit.A78 CFSG.CGT.PushingUpLit.A78Sp4
open CFSG.CGT.PushingUpLit.A78L3
open CFSG.ABGLocalTools
open Matrix
open scoped commutatorElement

structure S4Pair (G : Type) [Group G] [Finite G] (L₁ L₂ V W Z Z₂ T : Subgroup G) (e : ℕ) :
    Prop where
  side₁ : S4Side G L₁ V W Z T e
  side₂ : S4Side G L₂ W V Z₂ T e
  nl₁ : Subgroup.normalizer (V : Set G) ≤ Subgroup.normalizer (L₁ : Set G)
  nl₂ : Subgroup.normalizer (W : Set G) ≤ Subgroup.normalizer (L₂ : Set G)
  O2 : ∀ P : Subgroup G, P ≤ T → IsPGroup 2 P → L₁ ≤ Subgroup.normalizer (P : Set G) →
    L₂ ≤ Subgroup.normalizer (P : Set G) → T ≤ Subgroup.normalizer (P : Set G) → P = ⊥

namespace S4Pair

variable {G : Type} [Group G] [Finite G] {L₁ L₂ V W Z Z₂ T : Subgroup G} {e : ℕ}
  (P : S4Pair G L₁ L₂ V W Z Z₂ T e)

include P in
theorem symm : S4Pair G L₂ L₁ W V Z₂ Z T e :=
  ⟨P.side₂, P.side₁, P.nl₂, P.nl₁, fun Q hQ hQ2 h₂ h₁ hT => P.O2 Q hQ hQ2 h₁ h₂ hT⟩

include P

theorem Z₂_le_N : Z₂ ≤ V ⊓ W := by
  have := P.side₂.Z_le_N
  rwa [inf_comm] at this

theorem le_normalizer_of_le_cent {X Y : Subgroup G} (h : Y ≤ Subgroup.centralizer (X : Set G)) :
    X ≤ Subgroup.normalizer (Y : Set G) := by
  have _ := P
  refine le_normalizer_of_conj fun x hx y hy => ?_
  have h1 : x * y * x⁻¹ = y := by
    rw [Subgroup.mem_centralizer_iff.1 (h hy) x hx]
    group
  rw [h1]
  exact hy

theorem inf_Z : Z ⊓ Z₂ = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : Z ⊓ Z₂ ≤ T := (inf_le_left.trans P.side₁.Z_le_V).trans P.side₁.V_le_T
  refine P.O2 _ hle (P.side₁.pT.to_le hle) ?_ ?_ ?_
  · exact P.le_normalizer_of_le_cent (inf_le_left.trans P.side₁.Z_cent)
  · exact P.le_normalizer_of_le_cent (inf_le_right.trans P.side₂.Z_cent)
  · exact le_normalizer_of_conj fun t ht x hx =>
      ⟨conj_mem_of_mem_normalizer (P.side₁.T_le_Z ht) hx.1,
        conj_mem_of_mem_normalizer (P.side₂.T_le_Z ht) hx.2⟩

theorem conj_Z₂ {x : G} (hxW : x ∈ Subgroup.normalizer (W : Set G)) {z : G} (hz : z ∈ Z₂) :
    x * z * x⁻¹ ∈ Z₂ := by
  have hxL : x ∈ Subgroup.normalizer (L₂ : Set G) := P.nl₂ hxW
  refine P.side₂.mem_Z_of_cent (conj_mem_of_mem_normalizer hxW (P.side₂.Z_le_V hz))
    (Subgroup.mem_centralizer_iff.2 fun l hl => ?_)
  have hl' : x⁻¹ * l * x ∈ L₂ := by
    simpa using conj_mem_of_mem_normalizer (inv_mem hxL) hl
  have hzl := Subgroup.mem_centralizer_iff.1 (P.side₂.Z_cent hz) _ hl'
  calc l * (x * z * x⁻¹) = x * ((x⁻¹ * l * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * l * x)) * x⁻¹ := by rw [hzl]
    _ = x * z * x⁻¹ * l := by group

theorem card_Z₂_of_ne_bot (hZ₂ : Z₂ ≠ ⊥) : Nat.card Z₂ = 2 ^ e := by
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D
  obtain ⟨z₀, hz₀, hz₀1⟩ : ∃ z ∈ Z₂, z ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hZ₂ ((Subgroup.eq_bot_iff_forall _).2 hcon)
  have hz₀N := P.Z₂_le_N hz₀
  have hc₀ : fr.c z₀ ≠ 0 := by
    intro h0
    have h1 : z₀ ∈ Z ⊓ Z₂ := ⟨(fr.c_eq_zero_iff hz₀N).1 h0, hz₀⟩
    rw [P.inf_Z] at h1
    exact hz₀1 h1
  have hinj : Function.Injective (fun z : ↥Z₂ => fr.c z) := by
    intro z z' hzz
    have h1 := fr.c_inj_of_inf (P.Z₂_le_N z.2) (P.Z₂_le_N z'.2) hzz
    have h2 : (z : G) * (z' : G)⁻¹ ∈ Z ⊓ Z₂ := Subgroup.mem_inf.2 ⟨h1, mul_mem z.2 (inv_mem z'.2)⟩
    rw [P.inf_Z, Subgroup.mem_bot] at h2
    exact Subtype.ext (mul_inv_eq_one.1 h2)
  have hsurj : Function.Surjective (fun z : ↥Z₂ => fr.c z) := by
    intro r
    by_cases hr : r = 0
    · refine ⟨1, ?_⟩
      show fr.c 1 = r
      rw [fr.c_one, hr]
    · have ht : r / fr.c z₀ ≠ 0 := div_ne_zero hr hc₀
      obtain ⟨x, -, -, hW, -, hN⟩ := fr.torus ht
      refine ⟨⟨x * z₀ * x⁻¹, P.conj_Z₂ (mem_normalizer_of_conj_le hW) hz₀⟩, ?_⟩
      show fr.c (x * z₀ * x⁻¹) = r
      rw [(hN z₀ hz₀N).2]
      field_simp
  rw [Nat.card_eq_of_bijective _ ⟨hinj, hsurj⟩, P.side₁.card_F]

theorem card_Z (hZ : Z ≠ ⊥) : Nat.card Z = 2 ^ e := P.symm.card_Z₂_of_ne_bot hZ

theorem card_Z₂ (hZ : Z ≠ ⊥) : Nat.card Z₂ = 2 ^ e := by
  have h1 := P.side₁.card_V
  have h2 := P.side₂.card_V
  have h3 := P.side₁.jst.card_V₂_eq
  rw [h3, h1, P.card_Z hZ] at h2
  have hpos : 0 < 2 ^ (2 * e) := by positivity
  exact (Nat.eq_of_mul_eq_mul_left hpos h2).symm

theorem Z₂_ne_bot (hZ : Z ≠ ⊥) : Z₂ ≠ ⊥ := by
  intro hbot
  have h1 := P.card_Z₂ hZ
  rw [hbot, Subgroup.card_bot] at h1
  have h2 : 2 ≤ 2 ^ e := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by have := P.side₁.two_le; omega)
  omega

theorem card_N (hZ : Z ≠ ⊥) : Nat.card ↥(V ⊓ W) = 2 ^ (2 * e) := by
  rw [P.side₁.card_N, P.card_Z hZ, ← pow_add, two_mul]

theorem exists_decomp (hZ : Z ≠ ⊥) {n : G} (hn : n ∈ V ⊓ W) :
    ∃ z ∈ Z, ∃ z₂ ∈ Z₂, z * z₂ = n := by
  let f : ↥Z × ↥Z₂ → ↥(V ⊓ W) := fun p =>
    ⟨p.1 * p.2, mul_mem (P.side₁.Z_le_N p.1.2) (P.Z₂_le_N p.2.2)⟩
  have hf : Function.Injective f := by
    rintro ⟨z, z₂⟩ ⟨z', z₂'⟩ hzz
    have h1 : (z : G) * z₂ = z' * z₂' := congrArg Subtype.val hzz
    have h2 : (z' : G)⁻¹ * z = z₂' * (z₂ : G)⁻¹ := by
      calc (z' : G)⁻¹ * z = (z' : G)⁻¹ * (z * z₂) * (z₂ : G)⁻¹ := by group
        _ = (z' : G)⁻¹ * (z' * z₂') * (z₂ : G)⁻¹ := by rw [h1]
        _ = z₂' * (z₂ : G)⁻¹ := by group
    have h3 : (z' : G)⁻¹ * z ∈ Z ⊓ Z₂ :=
      Subgroup.mem_inf.2 ⟨mul_mem (inv_mem z'.2) z.2, by
        rw [h2]; exact mul_mem z₂'.2 (inv_mem z₂.2)⟩
    rw [P.inf_Z, Subgroup.mem_bot] at h3
    have hz : (z : G) = z' := by
      have := congrArg (fun y => (z' : G) * y) h3
      simpa using this
    have hz₂ : (z₂ : G) = z₂' := by
      rw [hz] at h1
      exact mul_left_cancel h1
    exact Prod.ext (Subtype.ext hz) (Subtype.ext hz₂)
  have hcard : Nat.card ↥(V ⊓ W) ≤ Nat.card (↥Z × ↥Z₂) := by
    rw [Nat.card_prod, P.card_Z hZ, P.card_Z₂ hZ, P.card_N hZ, ← pow_add, two_mul]
  obtain ⟨⟨z, z₂⟩, hp⟩ := (hf.bijective_of_nat_card_le hcard).2 ⟨n, hn⟩
  exact ⟨z, z.2, z₂, z₂.2, congrArg Subtype.val hp⟩

theorem sup_Z (hZ : Z ≠ ⊥) : Z ⊔ Z₂ = V ⊓ W := by
  refine le_antisymm (sup_le P.side₁.Z_le_N P.Z₂_le_N) fun n hn => ?_
  obtain ⟨z, hz, z₂, hz₂, rfl⟩ := P.exists_decomp hZ hn
  exact mul_mem (Subgroup.mem_sup_left hz) (Subgroup.mem_sup_right hz₂)

theorem commute_N {x y : G} (hx : x ∈ V ⊓ W) (hy : y ∈ V ⊓ W) : x * y = y * x :=
  (P.side₁.jst.abelian_V x hx.1 y hy.1).eq

theorem exists_ne_zero_one : ∃ t : GaloisField 2 e, t ≠ 0 ∧ t ≠ 1 := by
  classical
  obtain ⟨t, ht⟩ := exists_avoid ({0, 1} : Finset (GaloisField 2 e)) (by
    rw [P.side₁.card_F]
    calc ({0, 1} : Finset (GaloisField 2 e)).card ≤ 2 := Finset.card_le_two
      _ < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) P.side₁.two_le)
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
  exact ⟨t, ht.1, ht.2⟩

theorem Z₂_le_comm (hZ : Z ≠ ⊥) : Z₂ ≤ ⁅V, W⁆ := by
  obtain ⟨D⟩ := P.side₁.nat
  obtain ⟨fr⟩ := P.side₁.exists_frame D
  obtain ⟨t, ht0, ht1⟩ := P.exists_ne_zero_one
  have ht1' : t + 1 ≠ 0 := by
    intro h0
    apply ht1
    linear_combination h0 - CharTwo.add_self_eq_zero (1 : GaloisField 2 e)
  obtain ⟨x, hxL, -, hxW, -, hxN⟩ := fr.torus ht0
  have hxV : x ∈ Subgroup.normalizer (V : Set G) := D.le_normalizer hxL
  have hxW' : x ∈ Subgroup.normalizer (W : Set G) := mem_normalizer_of_conj_le hxW
  have hcjU : cj x ⁅V, W⁆ = ⁅V, W⁆ := by
    have e1 : cj x ⁅V, W⁆ = ⁅cj x V, cj x W⁆ := Subgroup.map_commutator _ _ _
    rw [e1, cj_eq_of_mem_normalizer_set hxV, cj_eq_of_mem_normalizer_set hxW']
  intro z₂ hz₂
  have hz₂N := P.Z₂_le_N hz₂
  obtain ⟨v, hv, hvs⟩ := D.κ_surj ((fr.c z₂ / (t + 1)) • fr.y₀)
  have huU : ⁅v, fr.w₁⁆ ∈ ⁅V, W⁆ := Subgroup.commutator_mem_commutator hv fr.hw₁
  have huN : ⁅v, fr.w₁⁆ ∈ V ⊓ W := P.side₁.jst.commutator_mem hv fr.hw₁
  have hcu : fr.c ⁅v, fr.w₁⁆ = fr.c z₂ / (t + 1) := by
    have hb1 : fr.b fr.w₁ = 1 := fr.hb
    rw [fr.c_comm hv fr.hw₁, hvs, det2_smul_right, fr.hdet, mul_one, hb1, mul_one]
  obtain ⟨z', hz', z₂', hz₂', hdec⟩ := P.exists_decomp hZ huN
  have hxz' : x * z' * x⁻¹ = z' := by
    rw [Subgroup.mem_centralizer_iff.1 (P.side₁.Z_cent hz') x hxL]
    group
  have hy : x * z₂' * x⁻¹ * z₂'⁻¹ ∈ Z₂ := mul_mem (P.conj_Z₂ hxW' hz₂') (inv_mem hz₂')
  have hcomm : z' * (x * z₂' * x⁻¹ * z₂'⁻¹) = (x * z₂' * x⁻¹ * z₂'⁻¹) * z' :=
    P.commute_N (P.side₁.Z_le_N hz') (P.Z₂_le_N hy)
  have hu' : x * ⁅v, fr.w₁⁆ * x⁻¹ * ⁅v, fr.w₁⁆⁻¹ = x * z₂' * x⁻¹ * z₂'⁻¹ := by
    rw [← hdec]
    calc x * (z' * z₂') * x⁻¹ * (z' * z₂')⁻¹ =
          (x * z' * x⁻¹) * (x * z₂' * x⁻¹ * z₂'⁻¹) * z'⁻¹ := by group
      _ = z' * (x * z₂' * x⁻¹ * z₂'⁻¹) * z'⁻¹ := by rw [hxz']
      _ = (x * z₂' * x⁻¹ * z₂'⁻¹) * z' * z'⁻¹ := by rw [hcomm]
      _ = x * z₂' * x⁻¹ * z₂'⁻¹ := by group
  have hcu' : fr.c (x * ⁅v, fr.w₁⁆ * x⁻¹ * ⁅v, fr.w₁⁆⁻¹) = fr.c z₂ := by
    rw [fr.c_mul (hxN _ huN).1.1 (inv_mem huN.1), (hxN _ huN).2, fr.c_inv huN.1, hcu]
    field_simp
  have heq : x * ⁅v, fr.w₁⁆ * x⁻¹ * ⁅v, fr.w₁⁆⁻¹ = z₂ := by
    have hmem : x * ⁅v, fr.w₁⁆ * x⁻¹ * ⁅v, fr.w₁⁆⁻¹ ∈ Z₂ := by rw [hu']; exact hy
    have h1 := fr.c_inj_of_inf (P.Z₂_le_N hmem) hz₂N hcu'
    have h2 : x * ⁅v, fr.w₁⁆ * x⁻¹ * ⁅v, fr.w₁⁆⁻¹ * z₂⁻¹ ∈ Z ⊓ Z₂ :=
      Subgroup.mem_inf.2 ⟨h1, mul_mem hmem (inv_mem hz₂)⟩
    rw [P.inf_Z, Subgroup.mem_bot] at h2
    exact mul_inv_eq_one.1 h2
  rw [← heq]
  refine mul_mem ?_ (inv_mem huU)
  rw [← hcjU]
  exact mul_mem_cj x huU

theorem Z_le_comm (hZ : Z ≠ ⊥) : Z ≤ ⁅V, W⁆ := by
  have h1 := P.symm.Z₂_le_comm (P.Z₂_ne_bot hZ)
  rwa [Subgroup.commutator_comm] at h1

end S4Pair

end CFSG.CGT.PushingUpLit.A78S4
