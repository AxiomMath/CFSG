module

public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771K
public import CFSG.LocalAnalysis.OddStandard.SmallF3.Omega.Sec7L771In

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.OddStandard.SmallF3.Omega

open Subgroup CFSG.Blueprint

variable {G : Type} [Group G]

private theorem sec7l771_normalizer_centralizer {H : Subgroup G} {x : G}
    (hx : x ∈ normalizer (H : Set G)) :
    x ∈ normalizer (centralizer (H : Set G)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro d
  rw [Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  have hconj : ∀ h ∈ H, x⁻¹ * h * x ∈ H := fun h hh =>
    (Subgroup.mem_normalizer_iff''.mp hx h).mp hh
  constructor
  · intro hd h hh
    have h1 := hd (x⁻¹ * h * x) (hconj h hh)
    calc h * (x * d * x⁻¹) = x * ((x⁻¹ * h * x) * d) * x⁻¹ := by group
      _ = x * (d * (x⁻¹ * h * x)) * x⁻¹ := by rw [h1]
      _ = (x * d * x⁻¹) * h := by group
  · intro hd h hh
    have hxh : x * h * x⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp hx h).mp hh
    have h1 := hd (x * h * x⁻¹) hxh
    calc h * d = x⁻¹ * ((x * h * x⁻¹) * (x * d * x⁻¹)) * x := by group
      _ = x⁻¹ * ((x * d * x⁻¹) * (x * h * x⁻¹)) * x := by rw [h1]
      _ = d * h := by group

theorem sec7l771_E_le_K [Finite G] {K B N E : Subgroup G} {s z : G}
    (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hcyc : ∀ P : Subgroup G, IsSylow2Of P (centralizer (K : Set G)) → IsCyclic P)
    (hout : ∀ x ∈ normalizer (K : Set G), Odd (orderOf x) → InnerOn K x)
    (hs : s ∈ centralizer (K : Set G)) (hs2 : orderOf s = 2)
    (hCs : ∀ c : G, c * s = s * c → c ∈ normalizer (K : Set G))
    (hBs : ∀ b ∈ B, b * s = s * b) (hB2 : ∀ b ∈ B, b * b = 1)
    (hBN : ∀ n ∈ N, ∀ b ∈ B, n * b * n⁻¹ ∈ B)
    (hNs : ∀ ν ∈ N, ν * z = z * ν → ν * s = s * ν)
    (hE : ∀ e ∈ E, ∃ b₁ ∈ B, ∃ b₂ ∈ B, ∃ ν₁ ∈ N, ∃ ν₂ ∈ N, ν₁ ^ 3 = 1 ∧ ν₂ ^ 3 = 1 ∧
      ν₁ * z = z * ν₁ ∧ ν₂ * z = z * ν₂ ∧
      e = (b₁ * (ν₁ * b₁⁻¹ * ν₁⁻¹)) * (b₂ * (ν₂ * b₂⁻¹ * ν₂⁻¹))) :
    E ≤ K := by
  intro e he
  obtain ⟨b₁, hb₁, b₂, hb₂, ν₁, hν₁, ν₂, hν₂, hν₁3, hν₂3, hν₁z, hν₂z, rfl⟩ := hE e he
  have hb₁ν : (b₁ * (ν₁ * b₁⁻¹ * ν₁⁻¹)) ^ 2 = 1 := by
    rw [pow_two]
    exact hB2 _ (B.mul_mem hb₁ (hBN ν₁ hν₁ b₁⁻¹ (B.inv_mem hb₁)))
  have hb₂ν : (b₂ * (ν₂ * b₂⁻¹ * ν₂⁻¹)) ^ 2 = 1 := by
    rw [pow_two]
    exact hB2 _ (B.mul_mem hb₂ (hBN ν₂ hν₂ b₂⁻¹ (B.inv_mem hb₂)))
  refine K.mul_mem
    (sec7l771_comm_mem hZ hcyc hout hs hs2 (hCs b₁ (hBs b₁ hb₁))
      (hCs ν₁ (hNs ν₁ hν₁ hν₁z)) (hBs b₁ hb₁) (hNs ν₁ hν₁ hν₁z) hν₁3 hb₁ν)
    (sec7l771_comm_mem hZ hcyc hout hs hs2 (hCs b₂ (hBs b₂ hb₂))
      (hCs ν₂ (hNs ν₂ hν₂ hν₂z)) (hBs b₂ hb₂) (hNs ν₂ hν₂ hν₂z) hν₂3 hb₂ν)

theorem sec7l771_l_of_nu [Finite G] {K E : Subgroup G} {z ν : G}
    (hZ : K ⊓ centralizer (K : Set G) = ⊥)
    (hout : ∀ x ∈ normalizer (K : Set G), Odd (orderOf x) → InnerOn K x)
    (hν : ν ∈ normalizer (K : Set G)) (hν3 : ν ^ 3 = 1)
    (hE : IsElemAb2 E 3) (hEK : E ≤ K) (hνE : ν ∈ normalizer (E : Set G))
    (hνz : ∀ e ∈ E, ν * e = e * ν → e = 1 ∨ e = z) :
    ∃ l ∈ K, orderOf l = 3 ∧ l ∈ normalizer (E : Set G) ∧
      ∀ e ∈ E, l * e = e * l → e = 1 ∨ e = z := by
  classical
  obtain ⟨l, hl, hl3, hlact⟩ := sec7l771_nu_to_l hZ hout hν hν3
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hlne : l ≠ 1 := by
    intro hl1
    have hsubset : ∀ e ∈ E, e = 1 ∨ e = z := by
      intro e he
      refine hνz e he ?_
      have h := hlact e (hEK he)
      rw [hl1, one_mul, inv_one, mul_one] at h
      have he' : ν * e * ν⁻¹ = e := h.symm
      calc ν * e = ν * e * ν⁻¹ * ν := by group
        _ = e * ν := by rw [he']
    have hcard : Nat.card E ≤ 2 := by
      have hinj : Function.Injective (fun e : E => if (e : G) = z then (1 : Fin 2) else 0) := by
        intro e₁ e₂ h
        by_cases h1 : (e₁ : G) = z
        · by_cases h2 : (e₂ : G) = z
          · exact Subtype.ext (h1.trans h2.symm)
          · simp [h1, h2] at h
        · by_cases h2 : (e₂ : G) = z
          · simp [h1, h2] at h
          · rcases hsubset e₁ e₁.2 with h1' | h1'
            · rcases hsubset e₂ e₂.2 with h2' | h2'
              · exact Subtype.ext (h1'.trans h2'.symm)
              · exact absurd h2' h2
            · exact absurd h1' h1
      have := Nat.card_le_card_of_injective _ hinj
      simpa using this
    have h8 : Nat.card E = 8 := by rw [hE.2]; norm_num
    omega
  refine ⟨l, hl, orderOf_eq_prime hl3 hlne, ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hlact h (hEK hh)]
      exact (Subgroup.mem_normalizer_iff.mp hνE h).mp hh
    · intro hh
      have hhK : h ∈ K := by
        have h1 : l * h * l⁻¹ ∈ K := hEK hh
        have h2 : h = l⁻¹ * (l * h * l⁻¹) * l := by group
        rw [h2]
        exact K.mul_mem (K.mul_mem (K.inv_mem hl) h1) hl
      rw [hlact h hhK] at hh
      exact (Subgroup.mem_normalizer_iff.mp hνE h).mpr hh
  · intro e he hle
    refine hνz e he ?_
    have h := hlact e (hEK he)
    have heq : ν * e * ν⁻¹ = e := by
      rw [← h]
      rw [hle]
      group
    calc ν * e = ν * e * ν⁻¹ * ν := by group
      _ = e * ν := by rw [heq]

theorem sec7l771_D_le_S_good [Finite G] {K S E : Subgroup G}
    (hSyl : IsSylow2Of (S ⊓ K) K) (hPE : S ⊓ K ≤ normalizer (E : Set G))
    (hD : IsPGroup 2 ↥(K ⊓ centralizer (E : Set G))) :
    K ⊓ centralizer (E : Set G) ≤ S := by
  have hN : S ⊓ K ≤ normalizer ((K ⊓ centralizer (E : Set G)) : Set G) := by
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx.2, sec7l771_normalizer_centralizer (hPE hx)⟩
  have hle := sec7l771_le_sylow (K := K) (P := S ⊓ K) (D := K ⊓ centralizer (E : Set G))
    hSyl inf_le_left hD hN
  exact hle.trans inf_le_left

theorem sec7l771_D_le_S_a [Finite G] (hE2 : Asc82E8Stab)
    {K L S E : Subgroup G} {z l : G} (hK : IsOm6P K) (hSyl : IsSylow2Of (S ⊓ K) K)
    (hSN : S ≤ normalizer (K : Set G))
    (hE : IsElemAb2 E 3) (hEK : E ≤ K) (hzS : z ∈ S) (hzE : z ∈ E)
    (hzc : ∀ x ∈ S, x * z = z * x)
    (hl : l ∈ K) (hl3 : orderOf l = 3) (hlE : l ∈ normalizer (E : Set G))
    (hlz : ∀ e ∈ E, l * e = e * l → e = 1 ∨ e = z)
    (hY : Nat.card ↥(S ⊓ L) = 128) (hYC : S ⊓ L ⊓ centralizer (K : Set G) = ⊥)
    (hYE : S ⊓ L ≤ normalizer (E : Set G))
    (hCL : ∀ B' : Subgroup G, IsNormalE16In (S ⊓ L) B' → ∀ y ∈ S ⊓ L,
      (∀ b ∈ B', y * b = b * y) → y ∈ B') :
    S ⊓ K ≤ normalizer (E : Set G) := by
  by_contra hnot
  have hzK : z ∈ K := hEK hzE
  have hzcent : z ∈ centerIn (S ⊓ K) :=
    Subgroup.mem_map.mpr ⟨⟨z, hzS, hzK⟩,
      Subgroup.mem_center_iff.mpr (fun a => Subtype.ext (hzc a a.2.1)), rfl⟩
  have hYK : S ⊓ L ≤ normalizer (K : Set G) := fun x hx => hSN hx.1
  have hYP : S ⊓ L ≤ normalizer ((S ⊓ K : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx.1, hSN hx.1⟩
  obtain ⟨B', hB', y, hy, hyB', hyc⟩ :=
    hE2 G K (S ⊓ K) hK hSyl E z l hE hEK hzcent hzE hl hl3 hlE hlz hnot
      (S ⊓ L) hY hYC hYK hYP hYE
  exact hyB' (hCL B' hB' y hy hyc)

theorem sec7l771_le_A {S B D : Subgroup G} (hS : D ≤ S)
    (hC : ∀ d ∈ D, ∀ b ∈ B, d * b = b * d) (h2 : ∀ d ∈ D, d * d = 1) : D ≤ ASub S B := by
  intro d hd
  rw [ASub, omega1]
  refine Subgroup.subset_closure ⟨?_, ?_⟩
  · exact ⟨hS hd, Subgroup.mem_centralizer_iff.mpr (fun b hb => (hC d hd b hb).symm)⟩
  · rw [pow_two]
    exact h2 d hd

end CFSG.OddStandard.SmallF3.Omega
