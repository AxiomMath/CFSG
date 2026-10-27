module

public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.ClassCard
public import CFSG.GH74.GLS.Stage1.Thm6.Sec13.Fixed
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.GH74.GLS.Stage1.Thm6.Sec13

open Subgroup

variable {G : Type*} [Group G]

theorem card_cls_mul' [Finite G] (M : Subgroup G) (x : G) :
    Nat.card (cls M x) * Nat.card ↥(M ⊓ centralizer ({x} : Set G)) = Nat.card M := by
  let _inst : MulAction ↥M G := MulAction.compHom G ((MulAut.conj : G →* MulAut G).comp M.subtype)
  have hsm : ∀ (m : ↥M) (g : G), m • g = (m : G) * g * (m : G)⁻¹ := fun m g => rfl
  have h1 : (MulAction.orbit (↥M) x) = cls M x := by
    ext y
    constructor
    · rintro ⟨m, rfl⟩
      exact ⟨m, m.2, hsm m x⟩
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, (hsm ⟨m, hm⟩ x).symm⟩
  have h2 : Nat.card (MulAction.stabilizer (↥M) x) =
      Nat.card ↥(M ⊓ centralizer ({x} : Set G)) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨s.1.1, s.1.2, ?_⟩
        invFun := fun d => ⟨⟨d.1, d.2.1⟩, ?_⟩
        left_inv := fun s => rfl
        right_inv := fun d => rfl }
    · have hs : (s.1 : ↥M) • x = x := s.2
      rw [hsm] at hs
      show s.1.1 ∈ centralizer ({x} : Set G)
      rw [mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      rw [hy]
      have : (s.1.1 : G) * x * (s.1.1 : G)⁻¹ = x := hs
      calc x * (s.1.1 : G) = ((s.1.1 : G) * x * (s.1.1 : G)⁻¹) * s.1.1 := by rw [this]
        _ = s.1.1 * x := by group
    · show (⟨d.1, d.2.1⟩ : ↥M) • x = x
      rw [hsm]
      have := mem_centralizer_iff.1 d.2.2 x rfl
      show d.1 * x * d.1⁻¹ = x
      calc d.1 * x * d.1⁻¹ = (d.1 * x) * d.1⁻¹ := rfl
        _ = (x * d.1) * d.1⁻¹ := by rw [← this]
        _ = x := by group
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (MulAction.stabilizer (↥M) x)
  have h4 : Nat.card (MulAction.orbit (↥M) x) = Nat.card (↥M ⧸ MulAction.stabilizer (↥M) x) :=
    Nat.card_congr (MulAction.orbitEquivQuotientStabilizer (↥M) x)
  rw [h1] at h4
  rw [h4, h2] at *
  exact h3.symm

theorem card_mul_inf_le [Finite G] {N C F : Subgroup G}
    (hF : ∀ f ∈ F, ∃ n ∈ N, ∃ c ∈ C, f = n * c) :
    Nat.card F * Nat.card ↥(N ⊓ C) ≤ Nat.card N * Nat.card C := by
  classical
  choose! n hn c hc hfc using hF
  have key : Function.Injective (fun p : F × ↥(N ⊓ C) =>
      ((⟨n p.1 * p.2, N.mul_mem (hn p.1 p.1.2) p.2.2.1⟩ : N),
        (⟨(p.2 : G)⁻¹ * c p.1, C.mul_mem (C.inv_mem p.2.2.2) (hc p.1 p.1.2)⟩ : C))) := by
    intro a b hab
    have h1 : n a.1 * (a.2 : G) = n b.1 * (b.2 : G) := congrArg (fun z => (z.1 : G)) hab
    have h2 : (a.2 : G)⁻¹ * c a.1 = (b.2 : G)⁻¹ * c b.1 := congrArg (fun z => (z.2 : G)) hab
    have hfa : (a.1 : G) = n a.1 * c a.1 := hfc a.1 a.1.2
    have hfb : (b.1 : G) = n b.1 * c b.1 := hfc b.1 b.1.2
    have hf : (a.1 : G) = (b.1 : G) := by
      calc (a.1 : G) = n a.1 * c a.1 := hfa
        _ = (n a.1 * (a.2 : G)) * ((a.2 : G)⁻¹ * c a.1) := by group
        _ = (n b.1 * (b.2 : G)) * ((b.2 : G)⁻¹ * c b.1) := by rw [h1, h2]
        _ = n b.1 * c b.1 := by group
        _ = (b.1 : G) := hfb.symm
    have hf' : a.1 = b.1 := Subtype.ext hf
    have hk : (a.2 : G) = (b.2 : G) := by
      have : n a.1 * (a.2 : G) = n a.1 * (b.2 : G) := by rw [h1, hf']
      exact mul_left_cancel this
    exact Prod.ext hf' (Subtype.ext hk)
  have := Nat.card_le_card_of_injective _ key
  rw [Nat.card_prod, Nat.card_prod] at this
  exact this

theorem lift_cent {y : G} (hy : y * y = 1) {N : Subgroup G}
    (hNy : ∀ n ∈ N, y * n * y⁻¹ ∈ N)
    (hconj : ∀ p ∈ N, (p * y) * (p * y) = 1 → ∃ q ∈ N, p * y = q * y * q⁻¹)
    {g : G} (hg : y * g * y⁻¹ * g⁻¹ ∈ N) : ∃ k ∈ N, y * (k * g) * y⁻¹ = k * g := by
  have hyi : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  set n := y * g * y⁻¹ * g⁻¹ with hn
  have hnn : y * n * y⁻¹ = n⁻¹ := by
    rw [hn]
    have h1 : y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ = g * y⁻¹ * g⁻¹ * y⁻¹ := by
      calc y * (y * g * y⁻¹ * g⁻¹) * y⁻¹ = (y * y) * g * y⁻¹ * g⁻¹ * y⁻¹ := by group
        _ = g * y⁻¹ * g⁻¹ * y⁻¹ := by rw [hy, one_mul]
    have h2 : (y * g * y⁻¹ * g⁻¹)⁻¹ = g * y * g⁻¹ * y⁻¹ := by group
    rw [h1, h2, hyi]
  have hinv : (n * y) * (n * y) = 1 := by
    calc (n * y) * (n * y) = n * (y * n * y⁻¹) * (y * y) := by group
      _ = 1 := by rw [hnn, hy]; group
  obtain ⟨q, hq, hqe⟩ := hconj n hg hinv
  refine ⟨(y * q * y⁻¹)⁻¹, N.inv_mem (hNy q hq), ?_⟩
  have e1 : y * g * y * g⁻¹ * y = q * y * q⁻¹ := by
    have : n * y = y * g * y⁻¹ * g⁻¹ * y := rfl
    rw [hyi] at this
    rw [← this]; exact hqe
  have e2 : y * g * y = q * y * q⁻¹ * y * g := by
    calc y * g * y = y * g * y * g⁻¹ * (y * y) * g := by rw [hy]; group
      _ = (y * g * y * g⁻¹ * y) * (y * g) := by group
      _ = (q * y * q⁻¹) * (y * g) := by rw [e1]
      _ = q * y * q⁻¹ * y * g := by group
  rw [hyi]
  have hq' : (y * q * y)⁻¹ = y * q⁻¹ * y := by
    calc (y * q * y)⁻¹ = y⁻¹ * q⁻¹ * y⁻¹ := by group
      _ = y * q⁻¹ * y := by rw [hyi]
  rw [hq']
  calc y * (y * q⁻¹ * y * g) * y = (y * y) * q⁻¹ * y * g * y := by group
    _ = q⁻¹ * (y * g * y) := by rw [hy]; group
    _ = q⁻¹ * (q * y * q⁻¹ * y * g) := by rw [e2]
    _ = y * q⁻¹ * y * g := by group

theorem three_le_card [Finite G] {U : Subgroup G} {a b c : G} (ha : a ∈ U) (hb : b ∈ U)
    (hc : c ∈ U) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) : 3 ≤ Nat.card U := by
  let f : Fin 3 → U := ![⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩]
  have hinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;>
      first | rfl | (exfalso; simp [f, Subtype.ext_iff] at hij; tauto)
  have := Nat.card_le_card_of_injective f hinj
  simpa using this

theorem one_lt_card_of_ne_one [Finite G] {U : Subgroup G} {z : G} (hz : z ∈ U) (hz1 : z ≠ 1) :
    1 < Nat.card U := by
  rw [Finite.one_lt_card_iff_nontrivial]
  exact ⟨⟨⟨z, hz⟩, 1, fun h => hz1 (congrArg Subtype.val h)⟩⟩

theorem central_of_card_le_two [Finite G] {B Z₁ : Subgroup G} (hZ : Nat.card Z₁ ≤ 2)
    (hnorm : ∀ b ∈ B, ∀ z ∈ Z₁, b * z * b⁻¹ ∈ Z₁) : ∀ b ∈ B, ∀ z ∈ Z₁, b * z = z * b := by
  intro b hb z hz
  by_cases hz1 : z = 1
  · rw [hz1]; simp
  · have hbz : b * z * b⁻¹ ∈ Z₁ := hnorm b hb z hz
    have hne : b * z * b⁻¹ ≠ 1 := by
      intro h
      apply hz1
      have : z = b⁻¹ * (b * z * b⁻¹) * b := by group
      rw [this, h]; group
    by_contra hcon
    have hne2 : b * z * b⁻¹ ≠ z := by
      intro h; apply hcon
      calc b * z = (b * z * b⁻¹) * b := by group
        _ = z * b := by rw [h]
    have h3 := three_le_card Z₁.one_mem hz hbz (Ne.symm hz1) (Ne.symm hne) (Ne.symm hne2)
    omega

theorem exists_fixed_ne_one [Finite G] {x : G} (hx : x * x = 1) {Z : Subgroup G}
    (hZ : IsPGroup 2 ↥Z) (hZ1 : 1 < Nat.card Z) (hxZ : ∀ z ∈ Z, x * z * x⁻¹ ∈ Z) :
    ∃ z ∈ Z, z ≠ 1 ∧ x * z * x⁻¹ = z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hSdef⟩ : ∃ S : Set G, S = (Z : Set G) \ {1} := ⟨_, rfl⟩
  have hmemS : ∀ v, v ∈ S ↔ v ∈ Z ∧ v ≠ 1 := by
    intro v
    rw [hSdef]
    simp
  have hS : ∀ v ∈ S, x * v * x⁻¹ ∈ S := by
    intro v hv
    rw [hmemS] at hv ⊢
    refine ⟨hxZ v hv.1, ?_⟩
    intro h
    apply hv.2
    have : v = x⁻¹ * (x * v * x⁻¹) * x := by group
    rw [this, h]
    group
  have hx2 : x ^ 2 ^ 1 = 1 := by rw [pow_one, pow_two]; exact hx
  have hcardS : Nat.card S + 1 = Nat.card Z := by
    have h1 : Nat.card S = S.ncard := (Nat.card_coe_set_eq S).symm
    have h2 : Nat.card (Z : Set G) = (Z : Set G).ncard := (Nat.card_coe_set_eq _).symm
    have h3 : S.ncard = (Z : Set G).ncard - 1 := by
      rw [hSdef]
      exact Set.ncard_sdiff_singleton_of_mem Z.one_mem
    have h4 : 0 < (Z : Set G).ncard := (Set.ncard_pos (Set.toFinite _)).2 ⟨1, Z.one_mem⟩
    have h5 : Nat.card Z = (Z : Set G).ncard := h2
    omega
  obtain ⟨k, hk⟩ := hZ.exists_card_eq
  have hk1 : 1 ≤ k := by
    by_contra hk0
    have : k = 0 := by omega
    rw [this, pow_zero] at hk
    omega
  have h2dvd : 2 ∣ Nat.card Z := by
    rw [hk]; exact dvd_pow_self 2 (by omega)
  have hodd : ¬ 2 ∣ Nat.card S := by
    omega
  obtain ⟨v, hv, hfix⟩ := exists_fixed_of_not_dvd (p := 2) S x 1 hx2 hS hodd
  have hv' := (hmemS v).1 hv
  exact ⟨v, hv'.1, hv'.2, hfix⟩

end CFSG.GH74.GLS.Stage1.Thm6.Sec13
