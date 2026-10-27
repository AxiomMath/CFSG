module

public import CFSG.CGT.Foote81L6.TStruct.Lemma2One
public import CFSG.CGT.Foote81L6.DescentDihedral

public section

namespace CFSG.CGT.Foote81L6

open Subgroup DihedralGroup

namespace FooteCore

variable {G : Type*} [Group G] {T : Subgroup G} {m n : ℕ} (D : FooteCore G T m n)

theorem exists_mul_self_eq_b₀ : ∃ y ∈ D.B₀, y * y = D.b₀ := by
  obtain ⟨k, hk⟩ : ∃ k, n = k + 3 := ⟨n - 3, by have := D.three_le_n; omega⟩
  subst hk
  obtain ⟨e⟩ := D.B₀_iso
  refine ⟨(e.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) : G), (e.symm _).2, ?_⟩
  have h1 : e.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) *
      e.symm (r ((2 ^ k : ℕ) : ZMod (2 ^ (k + 2)))) = e.symm (zc (k + 2)) := by
    rw [← map_mul, r_quarter_mul_self]
  have h2 := congrArg Subtype.val h1
  rw [Subgroup.coe_mul] at h2
  rw [h2]
  have hzc : ((e.symm (zc (k + 2)) : D.B₀) : G) = D.b₀ := by
    rcases eq_one_or_zc_of_comm (a := k + 2) (by omega) (c := e ⟨D.b₀, D.b₀_mem⟩) (fun g => by
        obtain ⟨y, rfl⟩ := e.surjective g
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subtype.ext (D.b₀_comm y y.2))) with h | h
    · exact absurd (congrArg Subtype.val (e.injective (h.trans e.map_one.symm))) D.b₀_ne_one
    · rw [← h, MulEquiv.symm_apply_apply]
  exact hzc

theorem exists_mul_self_eq_b : ∃ y ∈ D.B₀ ⊔ D.B₁, y * y = D.b := by
  obtain ⟨y₀, hy₀, hy₀2⟩ := D.exists_mul_self_eq_b₀
  have hy₁ : D.s * y₀ * D.s⁻¹ ∈ D.B₁ := D.conj_s_mem_B₁ hy₀
  have hc : y₀ * (D.s * y₀ * D.s⁻¹) = (D.s * y₀ * D.s⁻¹) * y₀ := D.B₀_comm_B₁ y₀ hy₀ _ hy₁
  refine ⟨y₀ * (D.s * y₀ * D.s⁻¹), mul_mem (mem_sup_left hy₀) (mem_sup_right hy₁), ?_⟩
  calc y₀ * (D.s * y₀ * D.s⁻¹) * (y₀ * (D.s * y₀ * D.s⁻¹))
      = y₀ * ((D.s * y₀ * D.s⁻¹) * y₀) * (D.s * y₀ * D.s⁻¹) := by group
    _ = y₀ * (y₀ * (D.s * y₀ * D.s⁻¹)) * (D.s * y₀ * D.s⁻¹) := by rw [hc]
    _ = (y₀ * y₀) * (D.s * (y₀ * y₀) * D.s⁻¹) := by group
    _ = D.b := by rw [hy₀2, D.conj_s_b₀]; rfl

section CaseFour

variable {G : Type*} [Group G] {T : Subgroup G} {n : ℕ} (D : FooteCore G T 2 n)

theorem A_comm_of_two {x y : G} (hx : x ∈ D.A) (hy : y ∈ D.A) : x * y = y * x := by
  obtain ⟨e⟩ := D.A_iso
  have h := mul_comm_of_le_one (a := 2 - 1) (by norm_num) (e ⟨x, hx⟩) (e ⟨y, hy⟩)
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (e.injective h)

theorem mul_self_of_two {x : G} (hx : x ∈ D.A) : x * x = 1 := by
  obtain ⟨e⟩ := D.A_iso
  have h : e ⟨x, hx⟩ * e ⟨x, hx⟩ = 1 :=
    (by decide : ∀ g : DihedralGroup (2 ^ (2 - 1)), g * g = 1) _
  rw [← map_mul, ← map_one e] at h
  exact congrArg Subtype.val (e.injective h)

end CaseFour

section Sylow

variable {G : Type*} [Group G] [Finite G] {T : Sylow 2 G} {n : ℕ}
  (D : FooteCore G (T : Subgroup G) 2 n)

theorem sylow_centralizer_A (hcen : D.a ∈ center G) {a₁ : G} (ha₁ : a₁ ∈ D.A) (ha₁1 : a₁ ≠ 1)
    (ha₁a : a₁ ≠ D.a) :
    ∃ SK : Sylow 2 ↥(centralizer ({a₁} : Set G)),
      (SK : Subgroup _) = D.T₀.subgroupOf (centralizer ({a₁} : Set G)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT₀C : D.T₀ ≤ centralizer ({a₁} : Set G) :=
    sup_le (fun x hx => mem_centralizer_singleton_iff.2 (D.A_comm_of_two hx ha₁))
      (fun y hy => mem_centralizer_singleton_iff.2 (D.A_comm_B a₁ ha₁ y hy).symm)
  have hP2 : IsPGroup 2 (D.T₀.subgroupOf (centralizer ({a₁} : Set G))) :=
    (IsPGroup.of_card D.card_T₀).comap_subtype
  obtain ⟨S, hPS⟩ := hP2.exists_le_sylow
  by_cases hS : (S : Subgroup ↥(centralizer ({a₁} : Set G))) =
      D.T₀.subgroupOf (centralizer ({a₁} : Set G))
  · exact ⟨S, hS⟩
  exfalso
  set S' : Subgroup G := (S : Subgroup _).map (centralizer ({a₁} : Set G)).subtype with hS'_def
  have hS'C : S' ≤ centralizer ({a₁} : Set G) := map_subtype_le _
  have hT₀S' : D.T₀ ≤ S' := fun x hx =>
    ⟨⟨x, hT₀C hx⟩, hPS (by rw [mem_subgroupOf]; exact hx), rfl⟩
  have hS'ne : D.T₀ ≠ S' := by
    intro h
    apply hS
    ext ⟨x, hx⟩
    rw [mem_subgroupOf, h]
    constructor
    · intro hxS
      exact ⟨⟨x, hx⟩, hxS, rfl⟩
    · rintro ⟨⟨y, hy⟩, hyS, hyx⟩
      have : y = x := hyx
      subst this
      exact hyS
  have hS'2 : IsPGroup 2 S' := S.2.map _
  obtain ⟨Q, hS'Q⟩ := hS'2.exists_le_sylow
  have hcardQ : Nat.card (Q : Subgroup G) = 2 ^ (2 + 2 * n + 2) := by
    rw [Sylow.card_eq_multiplicity, ← Sylow.card_eq_multiplicity T, D.card_T]
  have hlt : Nat.card D.T₀ < Nat.card S' := by
    by_contra hle
    push Not at hle
    exact hS'ne (Subgroup.eq_of_le_of_card_ge hT₀S' hle)
  have hdvd : Nat.card S' ∣ 2 ^ (2 + 2 * n + 2) := hcardQ ▸ Subgroup.card_dvd_of_le hS'Q
  obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  rw [D.card_T₀, hjeq] at hlt
  have hj' : j = 2 + 2 * n + 2 := by
    have := (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).1 hlt
    omega
  have hS'Qeq : S' = Q := Subgroup.eq_of_le_of_card_ge hS'Q (by rw [hcardQ, hjeq, hj'])
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq G T Q
  have hmemQ : ∀ {y : G}, y ∈ (Q : Subgroup G) ↔ h⁻¹ * y * h ∈ (T : Subgroup G) := by
    intro y
    rw [← hh, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [MulAut.smul_def, MulAut.conj_apply]
      convert hz using 1
      group
    · intro hy
      refine ⟨_, hy, ?_⟩
      rw [MulAut.smul_def, MulAut.conj_apply]
      group
  have hmapT₀ : D.T₀.map (MulAut.conj h⁻¹).toMonoidHom = D.T₀ := by
    refine D.map_T₀_eq (MulAut.conj h⁻¹).injective ?_
    rintro _ ⟨x, hx, rfl⟩
    have hxQ : x ∈ (Q : Subgroup G) := hS'Qeq ▸ hT₀S' hx
    have := hmemQ.1 hxQ
    simpa [MulAut.conj_apply] using this
  have hconjT₀ : ∀ y ∈ D.T₀, h * y * h⁻¹ ∈ D.T₀ := by
    intro y hy
    rw [← hmapT₀] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    have e : h * (MulAut.conj h⁻¹).toMonoidHom z * h⁻¹ = z := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hz
  set c := h⁻¹ * a₁ * h with hc_def
  have hcT₀ : c ∈ D.T₀ := by
    rw [← hmapT₀]
    exact ⟨a₁, D.A_le_T₀ ha₁, by simp [MulAut.conj_apply, hc_def]⟩
  have hcc : ∀ y ∈ (T : Subgroup G), y * c = c * y := by
    intro y hy
    have hyQ : h * y * h⁻¹ ∈ (Q : Subgroup G) := hmemQ.2 (by group; exact hy)
    have hcomm := mem_centralizer_singleton_iff.1 (hS'C (hS'Qeq ▸ hyQ))
    calc y * c = h⁻¹ * ((h * y * h⁻¹) * a₁) * h := by rw [hc_def]; group
      _ = h⁻¹ * (a₁ * (h * y * h⁻¹)) * h := by rw [hcomm]
      _ = c * y := by rw [hc_def]; group
  have hbB : h * D.b * h⁻¹ ∈ D.B := by
    obtain ⟨y, hy, hyy⟩ := D.exists_mul_self_eq_b
    have hyT₀ : h * y * h⁻¹ ∈ D.T₀ := hconjT₀ y (D.B_le_T₀ (D.B₀B₁_le_B hy))
    obtain ⟨α, hα, β, hβ, hαβ⟩ := D.mem_T₀_iff.1 hyT₀
    have : h * D.b * h⁻¹ = β * β := by
      calc h * D.b * h⁻¹ = (h * y * h⁻¹) * (h * y * h⁻¹) := by rw [← hyy]; group
        _ = α * β * (α * β) := by rw [hαβ]
        _ = (α * α) * (β * β) := by
            rw [mul_assoc α β, ← mul_assoc β α, ← D.A_comm_B α hα β hβ]; group
        _ = β * β := by rw [D.mul_self_of_two hα, one_mul]
    rw [this]
    exact mul_mem hβ hβ
  have hAB : ∀ {x : G}, x ∈ D.A → x ∈ D.B → x = 1 := by
    intro x hxA hxB
    have : x ∈ D.A ⊓ D.B := mem_inf.2 ⟨hxA, hxB⟩
    rwa [D.A_inf_B, mem_bot] at this
  have ha₁c : a₁ = h * c * h⁻¹ := by rw [hc_def]; group
  have hha : h * D.a * h⁻¹ = D.a := by
    rw [mem_center_iff.1 hcen h, mul_inv_cancel_right]
  have hct : c * D.t = D.t * c := (hcc D.t D.t_mem_T).symm
  rcases D.mem_CBt_or_of_comm_t hcT₀ hct with hcB | hcaB
  · rcases D.eq_one_or_b_of_comm_B (mem_inf.1 hcB).1 (fun y hy => hcc y (D.B_le_T hy)) with h1 | h1
    · apply ha₁1
      rw [ha₁c, h1]
      group
    · rw [h1] at ha₁c
      exact ha₁1 (hAB ha₁ (ha₁c ▸ hbB))
  · have hcaB' : c * D.a ∈ D.B := (mem_inf.1 hcaB).1
    have hcomm : ∀ y ∈ D.B, y * (c * D.a) = c * D.a * y := by
      intro y hy
      have h1 := hcc y (D.B_le_T hy)
      have h2 := D.a_comm_T (D.B_le_T hy)
      calc y * (c * D.a) = (y * c) * D.a := (mul_assoc y c D.a).symm
        _ = (c * y) * D.a := by rw [h1]
        _ = c * (y * D.a) := mul_assoc c y D.a
        _ = c * (D.a * y) := by rw [h2]
        _ = c * D.a * y := (mul_assoc c D.a y).symm
    rcases D.eq_one_or_b_of_comm_B hcaB' hcomm with h1 | h1
    · apply ha₁a
      have : c = D.a := by
        calc c = c * D.a * D.a := by rw [mul_assoc, D.a_mul_a, mul_one]
          _ = D.a := by rw [h1, one_mul]
      rw [ha₁c, this, hha]
    · have hc' : c = D.b * D.a := by
        calc c = c * D.a * D.a := by rw [mul_assoc, D.a_mul_a, mul_one]
          _ = D.b * D.a := by rw [h1]
      have hmem : D.a * a₁ ∈ D.B := by
        have : D.a * a₁ = h * D.b * h⁻¹ := by
          rw [ha₁c, hc']
          calc D.a * (h * (D.b * D.a) * h⁻¹) = D.a * (h * D.b * h⁻¹) * (h * D.a * h⁻¹) := by group
            _ = D.a * (h * D.b * h⁻¹) * D.a := by rw [hha]
            _ = (h * D.b * h⁻¹) * (D.a * D.a) := by
                rw [← mem_center_iff.1 hcen (h * D.b * h⁻¹)]
                group
            _ = h * D.b * h⁻¹ := by rw [D.a_mul_a, mul_one]
        rw [this]
        exact hbB
      have h1' := hAB (mul_mem D.a_mem ha₁) hmem
      apply ha₁a
      calc a₁ = D.a * (D.a * a₁) := by rw [← mul_assoc, D.a_mul_a, one_mul]
        _ = D.a := by rw [h1', mul_one]

end Sylow

end FooteCore

end CFSG.CGT.Foote81L6
