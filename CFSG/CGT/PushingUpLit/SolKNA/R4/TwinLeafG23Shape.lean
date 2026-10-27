module

public import CFSG.GH74.GLS.IVK.Proofs2.Ivk94G4Top3
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2Shape
public import CFSG.ClassicalInvolution.Q3.TA3LeafQ3G2SL3
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf

open CFSG CFSG.GH74.GLS CFSG.GH74.GLS.IVK.Proofs2.Ivk47ab CFSG.ClassicalInvolution.Q3.TA3
open CFSG.LieType.HighestRoot
open scoped MatrixGroups

theorem mem_of_normal_of_sylow {G : Type*} [Group G] [Finite G] {D M : Subgroup G}
    (hDn : ∀ c d : G, d ∈ D → c * d * c⁻¹ ∈ D) (hMD : M ≤ D) (hM : IsPGroup 2 M)
    (hidx : ¬ 2 ∣ M.index) {g : G} (hg : ∃ k : ℕ, g ^ 2 ^ k = 1) : g ∈ D := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := hg
  have hgp : IsPGroup 2 (Subgroup.zpowers g) := by
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hk)
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  obtain ⟨T, hT⟩ := hgp.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G (hM.toSylow hidx) T
  have hgT : g ∈ (T : Subgroup G) := hT (Subgroup.mem_zpowers g)
  rw [← hc, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hgT
  obtain ⟨s, hs, hsg⟩ := hgT
  have hgs : g = c * s * c⁻¹ := by
    rw [← hsg]
    simp [MulAut.conj_apply]
  rw [hgs]
  exact hDn c s (hMD hs)

section Shape

variable {G : Type} [Group G] {F₁ F₂ : Type} [Field F₁] [Field F₂]

theorem shape_index_sup_eq_two (S : Shape G F₁ F₂) : (S.I₁ ⊔ S.I₂).index = 2 := by
  rw [Subgroup.index_eq_two_iff]
  refine ⟨S.t, fun b => ?_⟩
  have hnot : ∀ b : G, b ∈ S.I₁ ⊔ S.I₂ → b * S.t ∈ S.I₁ ⊔ S.I₂ → False := fun b hb hbt =>
    S.t_not_mem (by simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ hb) hbt)
  rcases Q3Sh.mem_sup_or S b with hb | hbt
  · exact Or.inr ⟨hb, fun hbt => hnot b hb hbt⟩
  · exact Or.inl ⟨hbt, fun hb => hnot b hb hbt⟩

theorem shape_card_sup [Finite G] (S : Shape G F₁ F₂) :
    Nat.card ↥(S.I₁ ⊔ S.I₂) * 2 = Nat.card ↥S.I₁ * Nat.card ↥S.I₂ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute S.I₁ S.I₂ S.comm).1
  have h2 : Nat.card ↥(S.I₁ ⊓ S.I₂) = 2 := by
    rw [S.inter, Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [pow_two]; exact S.z_sq) S.z_ne
  rwa [h2] at h

theorem shape_card_g23 [Finite G] [Finite F₁] [Finite F₂] (S : Shape G F₁ F₂)
    (h₁ : Nat.card F₁ = 3) (h₂ : Nat.card F₂ = 3) : Nat.card G = 576 := by
  have h := shape_card_sup S
  rw [card_eq_24 h₁ S.e₁, card_eq_24 h₂ S.e₂] at h
  have hi := Subgroup.card_mul_index (S.I₁ ⊔ S.I₂)
  rw [shape_index_sup_eq_two S] at hi
  omega

end Shape

variable {G : Type} [Group G] [Finite G] {F₁ F₂ : Type} [Field F₁] [Field F₂] [Finite F₁]
  [Finite F₂]

theorem Shape.false_of_normal_odd_two (S : Shape G F₁ F₂) (h₁ : Nat.card F₁ = 3)
    (h₂ : Nat.card F₂ = 3) {D O M : Subgroup G} (hDn : ∀ c d : G, d ∈ D → c * d * c⁻¹ ∈ D)
    (hOodd : Odd (Nat.card O)) (hDO : ∀ g ∈ D, ∃ k : ℕ, g ^ 2 ^ k ∈ O) (hMD : M ≤ D)
    (hM2 : IsPGroup 2 M) (hM : 64 ≤ Nat.card M) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG := shape_card_g23 S h₁ h₂
  obtain ⟨m, hm⟩ := hM2.exists_card_eq
  have hMdvd : Nat.card M ∣ 576 := hG ▸ Subgroup.card_subgroup_dvd_card M
  have hm6 : m = 6 := by
    have hle : m ≤ 6 := by
      by_contra h
      push Not at h
      have h7 : 2 ^ 7 ∣ 2 ^ m := pow_dvd_pow 2 h
      rw [← hm] at h7
      have := dvd_trans h7 hMdvd
      norm_num at this
    have hge : 6 ≤ m := by
      by_contra h
      push Not at h
      have : 2 ^ m ≤ 2 ^ 5 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    omega
  have hidx : ¬ 2 ∣ M.index := by
    have h := Subgroup.card_mul_index M
    rw [hm, hm6, hG] at h
    have : M.index = 9 := by omega
    rw [this]
    norm_num
  have h2D : ∀ g : G, (∃ k : ℕ, g ^ 2 ^ k = 1) → g ∈ D := fun g hg =>
    mem_of_normal_of_sylow hDn hMD hM2 hidx hg
  have hDtop : D = ⊤ := by
    have hres := S.oPrimeResidual_eq_top_of_odd (by rw [h₁]; decide) (by rw [h₂]; decide)
    rw [eq_top_iff, ← hres]
    exact (Subgroup.closure_le D).2 fun g hg => h2D g hg
  have hmod : ∀ k : ℕ, 2 ^ k % 3 = 1 ∨ 2 ^ k % 3 = 2 := by
    intro k
    induction k with
    | zero => left; rfl
    | succ n ih => rcases ih with h | h <;> simp [pow_succ, Nat.mul_mod, h]
  have h3O : ∀ x : G, x ^ 3 = 1 → x ∈ D → x ∈ O := by
    intro x hx3 hxD
    obtain ⟨k, hk⟩ := hDO x hxD
    rw [pow_eq_pow_mod _ hx3] at hk
    rcases hmod k with h | h
    · rwa [h, pow_one] at hk
    · rw [h] at hk
      have hx : x = (x ^ 2) ^ 2 := by
        rw [← pow_mul, show 2 * 2 = 3 + 1 from rfl, pow_succ, hx3, one_mul]
      rw [hx]
      exact O.pow_mem hk 2
  have hI₁O : S.I₁ ≤ O := fun a ha =>
    (Subgroup.closure_le O).2 (fun x hx => h3O x hx.2 (by rw [hDtop]; exact Subgroup.mem_top x))
      (SL3.le_closure_cube_of_mulEquiv h₁ S.e₁ ha)
  have hdvd : Nat.card ↥S.I₁ ∣ Nat.card O := Subgroup.card_dvd_of_le hI₁O
  rw [card_eq_24 h₁ S.e₁] at hdvd
  obtain ⟨q, hq⟩ := hdvd
  exact (Nat.not_even_iff_odd.2 hOodd) ⟨12 * q, by omega⟩

end CFSG.CGT.PushingUpLit.SolKNA.R4.TwinLeaf
