module

public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic20
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.GrpBasic21
public import CFSG.GH74.GLS.Stage1.Thm3.Sec8.Ctx56

public section

namespace CFSG.GH74.GLS.Stage1.Thm3.Sec8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage1.Thm2.Recip
  CFSG.GH74.GLS.Stage1.Thm3.Sec4 CFSG.GH74.GLS.Stage1.Thm3.Sec5 CFSG.GH74.GLS.Stage1.Thm3.Sec6
open scoped commutatorElement Pointwise

namespace Basic

section Zy

variable {G : Type*} [Group G]

theorem orderOf_y_eq_four {y z : G} (hy2 : y * y = z) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    orderOf y = 4 := by
  have hy4 : y ^ 4 = 1 := by
    calc y ^ 4 = (y * y) * (y * y) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = 1 := by rw [hy2, hz2]
  have hy2' : ¬ y ^ (2 ^ 1) = 1 := by
    intro h1
    apply hz1
    rw [← hy2]
    simpa [pow_two] using h1
  have := orderOf_eq_prime_pow (p := 2) (n := 1) hy2' (by simpa using hy4)
  simpa using this

theorem card_zpowers_y {y z : G} (hy2 : y * y = z) (hz2 : z * z = 1) (hz1 : z ≠ 1) :
    Nat.card ↥(zpowers y) = 4 := by
  rw [Nat.card_zpowers, orderOf_y_eq_four hy2 hz2 hz1]

theorem mem_zpowers_y {y z x : G} (hy2 : y * y = z) (hz2 : z * z = 1) (hz1 : z ≠ 1)
    (hx : x ∈ zpowers y) : x = 1 ∨ x = y ∨ x = z ∨ x = z * y := by
  have hord : orderOf y = 4 := orderOf_y_eq_four hy2 hz2 hz1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← zpow_mod_orderOf, hord]
  have h0 : 0 ≤ k % ((4 : ℕ) : ℤ) := Int.emod_nonneg k (by norm_num)
  have h4 : k % ((4 : ℕ) : ℤ) < 4 := Int.emod_lt_of_pos k (by norm_num)
  obtain ⟨r, hr⟩ := Int.eq_ofNat_of_zero_le h0
  rw [hr]
  have hr4 : r < 4 := by omega
  interval_cases r
  · left; simp
  · right; left; simp
  · right; right; left; simp [pow_two, hy2]
  · right; right; right
    simp only [zpow_natCast]
    calc y ^ 3 = (y * y) * y := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
      _ = z * y := by rw [hy2]

end Zy

end Basic

namespace Setup8

variable {G : Type} [Group G] [Finite G] {z : G} {S K₁ K₂ W₁ W₂ U : Subgroup G} {u h : G}

theorem Lambda_norm (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {δ c y : G}
    (hc : c * z * c⁻¹ = δ) (hy : y * δ = δ * y) :
    ∀ x ∈ conjugate (K₁ ⊔ K₂) c⁻¹, y * x * y⁻¹ ∈ conjugate (K₁ ⊔ K₂) c⁻¹ := by
  intro x hx
  have hM := hs.m4 hII
  rw [mem_conjugate_iff] at hx ⊢
  have hx' : c⁻¹ * x * c ∈ K₁ ⊔ K₂ := by simpa using hx
  have hcy : c⁻¹ * y * c ∈ centralizer ({z} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hz : c⁻¹ * δ * c = z := by rw [← hc]; group
    calc c⁻¹ * y * c * z = c⁻¹ * y * (c * z * c⁻¹) * c := by group
      _ = c⁻¹ * (y * δ) * c := by rw [hc]; group
      _ = c⁻¹ * (δ * y) * c := by rw [hy]
      _ = (c⁻¹ * δ * c) * (c⁻¹ * y * c) := by group
      _ = z * (c⁻¹ * y * c) := by rw [hz]
  have := hM.C_norm_K hcy hx'
  have e : (c⁻¹ * y * c) * (c⁻¹ * x * c) * (c⁻¹ * y * c)⁻¹ = c⁻¹ * (y * x * y⁻¹) * c⁻¹⁻¹ := by group
  rwa [e] at this

theorem false_of_z_mem_Lambda (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {c : G}
    (hint : Interchanges z (conjugate K₁ c⁻¹) (conjugate K₂ c⁻¹))
    (hzΛ : z ∈ conjugate (K₁ ⊔ K₂) c⁻¹) : False := by
  have hM := hs.m4 hII
  have hne : K₁ ≠ K₂ := hs.fused.std.ne
  have hw : c⁻¹ * z * c ∈ K₁ ⊔ K₂ := by
    have := mem_conjugate_iff.1 hzΛ
    simpa using this
  have hle : K₁ ⊔ K₂ ≤ normalizer (K₁ : Set G) :=
    sup_le Subgroup.le_normalizer (fun x hx => (mem_cSec.1 (hM.cs₁ hx)).1)
  have hwN : c⁻¹ * z * c ∈ normalizer (K₁ : Set G) := hle hw
  obtain ⟨h1, -⟩ := hint
  have hA : conjugate (conjugate K₁ c⁻¹) z = conjugate K₁ c⁻¹ := by
    ext t
    simp only [mem_conjugate_iff, inv_inv]
    have := Subgroup.mem_normalizer_iff.1 hwN (c⁻¹ * t * c)
    have e : (c⁻¹ * z * c) * (c⁻¹ * t * c) * (c⁻¹ * z * c)⁻¹ = c⁻¹ * (z * t * z⁻¹) * c := by group
    rw [e] at this
    exact this.symm
  rw [hA] at h1
  apply hne
  ext x
  have key : ∀ x : G, x ∈ K₁ ↔ x ∈ K₂ := by
    intro x
    have hx1 : c * x * c⁻¹ ∈ conjugate K₁ c⁻¹ ↔ x ∈ K₁ := by
      rw [mem_conjugate_iff]
      have : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rw [this]
    have hx2 : c * x * c⁻¹ ∈ conjugate K₂ c⁻¹ ↔ x ∈ K₂ := by
      rw [mem_conjugate_iff]
      have : c⁻¹ * (c * x * c⁻¹) * c⁻¹⁻¹ = x := by group
      rw [this]
    rw [← hx1, ← hx2, h1]
  exact key x

theorem U_le_W' (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) :
    ∀ x ∈ U, x ∈ Wsub S U := fun x hx =>
  ⟨hs.U_le_S hII hx, Subgroup.mem_centralizer_iff.2 (fun y hy => hs.four_comm y hy x hx)⟩

theorem z_mem_Lambda (hII : II4_4_4_center) (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) {δ c : G}
    (hc : c * z * c⁻¹ = δ) (hhδ : h * δ = δ * h) {u₀ : G} (hu₀U : u₀ ∈ U) (hu₀1 : u₀ ≠ 1)
    (hu₀z : u₀ ≠ z) (hu₀Λ : u₀ ∈ conjugate (K₁ ⊔ K₂) c⁻¹) : z ∈ conjugate (K₁ ⊔ K₂) c⁻¹ := by
  have hUh : ∀ x ∈ U, h * x * h⁻¹ ∈ U := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hs.h_norm x).1 hx
  have hUh' : ∀ x ∈ U, h⁻¹ * x * h ∈ U := by
    intro x hx
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hs.h_norm) x).1 hx
    simpa using this
  have hcube : ∀ x ∈ U, h ^ 3 * x = x * h ^ 3 := fun x hx => hs.h_cube x (hs.U_le_W' hII x hx)
  obtain ⟨-, horb⟩ := Basic.U_orbit hs.U_four.2 hs.z_mem hs.z_ne hUh hUh' hcube hs.h_move
  have hhδ' : h * δ = δ * h := hhδ
  rcases horb u₀ hu₀U hu₀1 hu₀z with h1 | h1
  · rw [h1]
    exact hs.Lambda_norm hII hc hhδ' _ hu₀Λ
  · rw [h1]
    exact hs.Lambda_norm hII hc hhδ' _ (hs.Lambda_norm hII hc hhδ' _ hu₀Λ)

theorem isConj_of_y (hII : II4_4_4_center) (h31 : IVK_3_1a_lifted)
    (hs : Setup8 G z S K₁ K₂ W₁ W₂ U u h) (hS128 : Nat.card ↥S = 2 ^ 7)
    (hP32 : Nat.card ↥(Pz S z) = 32) {δ y : G} (hδS : δ ∈ S) (hδS1 : δ ∉ S1 S K₁) (hδ2 : δ * δ = 1)
    (hyS : y ∈ S) (hyS1 : y ∉ S1 S K₁) (hy2 : y * y = z) : IsConj z δ := by
  have hzz := hs.z_sq
  have hz1 := hs.z_ne
  obtain ⟨hyK₁, hyK₂⟩ := hs.swap_of_not_mem hII hyS hyS1
  have hno : ∀ p ∈ Pz S z, (p * y) * (p * y) ≠ 1 := by
    intro p hp
    rw [hs.Pz_eq_sup hII] at hp
    refine Basic.no_invol_coset (hs.P_comm hII) ?_ (hs.z_mem_P hII (Or.inl rfl))
      (hs.z_mem_P hII (Or.inr rfl)) hzz hz1 hy2 ?_ ?_ p hp
    · intro x hx1 hx2
      have : x ∈ Pof S K₁ ⊓ Pof S K₂ := ⟨hx1, hx2⟩
      rw [hs.P_inf hII] at this
      exact (Basic.mem_zpowers_of_sq' hzz).1 this
    · intro p hp
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hyS hp.1) (inv_mem hyS), ?_⟩
      have : p ∈ conjugate K₂ y := by rw [hyK₂]; exact hp.2
      exact mem_conjugate_iff.1 this
    · intro p hp
      refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hyS hp.1) (inv_mem hyS), ?_⟩
      have : p ∈ conjugate K₁ y := by rw [hyK₁]; exact hp.2
      exact mem_conjugate_iff.1 this
  have hPS : Pz S z ≤ S := inf_le_left
  have hPS1 : Pz S z ≤ S1 S K₁ := hs.Pz_le_S1 hII
  have hyN : y ∈ normalizer (Pz S z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hs.S_normalizes_Pz hII hyS x hx
    · intro hx
      have := hs.S_normalizes_Pz hII (inv_mem hyS) _ hx
      have e : y⁻¹ * (y * x * y⁻¹) * y⁻¹⁻¹ = x := by group
      rwa [e] at this
  have hyP : y ∉ Pz S z := fun hp => hyS1 (hPS1 hp)
  have hMS : Pz S z ⊔ zpowers y ≤ S := sup_le hPS (Subgroup.zpowers_le.2 hyS)
  have hzP : z ∈ Pz S z := by
    rw [hs.Pz_eq_sup hII]; exact Subgroup.mem_sup_left (hs.z_mem_P hII (Or.inl rfl))
  have hmemM : ∀ x ∈ Pz S z ⊔ zpowers y, x ∈ Pz S z ∨ ∃ p ∈ Pz S z, x = p * y := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Basic.mem_sup_of_le_normalizer' (A := zpowers y) (B := Pz S z)
      (Subgroup.zpowers_le.2 hyN) (sup_comm (Pz S z) (zpowers y) ▸ hx)
    have hyb : y * b * y⁻¹ ∈ Pz S z := hs.S_normalizes_Pz hII hyS b hb
    rcases Basic.mem_zpowers_y hy2 hzz hz1 ha with h1 | h1 | h1 | h1
    · left; rw [h1, one_mul]; exact hb
    · right
      refine ⟨y * b * y⁻¹, hyb, ?_⟩
      rw [h1]; group
    · left; rw [h1]; exact mul_mem hzP hb
    · right
      refine ⟨z * (y * b * y⁻¹), mul_mem hzP hyb, ?_⟩
      rw [h1]; group
  have hMcard : Nat.card ↥(Pz S z ⊔ zpowers y) = 64 := by
    have h1 := Basic.card_sup_mul_card_inf' (A := Pz S z) (B := zpowers y) (Subgroup.zpowers_le.2 hyN)
    have hinf : Pz S z ⊓ zpowers y = zpowers z := by
      apply le_antisymm
      · intro x hx
        rcases Basic.mem_zpowers_y hy2 hzz hz1 hx.2 with h0 | h0 | h0 | h0
        · rw [h0]; exact one_mem _
        · exact absurd (h0 ▸ hx.1) hyP
        · rw [h0]; exact Subgroup.mem_zpowers z
        · exfalso
          apply hyP
          have : y = z⁻¹ * x := by rw [h0]; group
          rw [this]
          exact mul_mem (inv_mem hzP) hx.1
      · rw [Subgroup.zpowers_le]
        refine ⟨hzP, ?_⟩
        rw [← hy2]
        exact Subgroup.mul_mem _ (Subgroup.mem_zpowers y) (Subgroup.mem_zpowers y)
    rw [hinf, M.card_zpowers_of_sq hzz hz1, Basic.card_zpowers_y hy2 hzz hz1, hP32] at h1
    omega
  have hrel : (Pz S z ⊔ zpowers y).relIndex S = 2 := by
    have h1 := Basic.card_mul_relIndex_of_le hMS
    rw [hMcard, hS128] at h1
    norm_num at h1
    omega
  have hδM : δ ∉ Pz S z ⊔ zpowers y := by
    intro hδ
    rcases hmemM δ hδ with hp | ⟨p, hp, hδp⟩
    · exact hδS1 (hPS1 hp)
    · apply hno p hp
      rw [← hδp]
      exact hδ2
  obtain ⟨g, hgM, -⟩ := hs.transfer8 hII (Pz S z ⊔ zpowers y) δ hMS hrel hδS hδM hδ2
  have hm2 : (g⁻¹ * δ * g) * (g⁻¹ * δ * g) = 1 := by
    calc (g⁻¹ * δ * g) * (g⁻¹ * δ * g) = g⁻¹ * (δ * δ) * g := by group
      _ = 1 := by rw [hδ2]; group
  have hmP : g⁻¹ * δ * g ∈ Pz S z := by
    rcases hmemM _ hgM with hp | ⟨p, hp, hmp⟩
    · exact hp
    · exfalso
      apply hno p hp
      rw [← hmp]
      exact hm2
  have hδ1 : δ ≠ 1 := fun e => hδS1 (e ▸ one_mem _)
  have hm1 : g⁻¹ * δ * g ≠ 1 := by
    intro e
    apply hδ1
    have : δ = g * (g⁻¹ * δ * g) * g⁻¹ := by group
    rw [this, e]
    group
  have hmo : orderOf (g⁻¹ * δ * g) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hm2) hm1
  have h1 := hs.invol_P_conj hII h31 _ hmP hmo
  exact h1.trans (isConj_iff.2 ⟨g, by group⟩)

end Setup8

end CFSG.GH74.GLS.Stage1.Thm3.Sec8
