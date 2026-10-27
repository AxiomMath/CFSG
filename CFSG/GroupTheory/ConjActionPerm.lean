module

public import Mathlib.Data.Finite.Perm

public section

namespace CFSG.GroupTheory

variable {G : Type*} [Group G]

@[expose] noncomputable def conjActionOn (N : Subgroup G) (O : Set G)
    (hO : ∀ n ∈ N, ∀ x ∈ O, n * x * n⁻¹ ∈ O) : N →* Equiv.Perm O where
  toFun n := Equiv.Perm.subtypePerm (p := (· ∈ O)) ((MulAut.conj (n : G)).toEquiv) (fun x => by
    constructor
    · intro h
      have := hO ((n⁻¹ : N) : G) (n⁻¹).2 _ h
      simpa [MulAut.conj_apply, mul_assoc] using this
    · intro h
      exact hO n n.2 x h)
  map_one' := by
    ext x
    simp
  map_mul' m n := by
    ext x
    show ((m * n : N) : G) * x * ((m * n : N) : G)⁻¹ =
      (m : G) * ((n : G) * x * (n : G)⁻¹) * (m : G)⁻¹
    simp [mul_assoc]

theorem conjActionOn_apply (N : Subgroup G) (O : Set G) (hO : ∀ n ∈ N, ∀ x ∈ O, n * x * n⁻¹ ∈ O)
    (n : N) (x : O) : ((conjActionOn N O hO n x : O) : G) = n * x * (n : G)⁻¹ := by
  simp [conjActionOn, Equiv.Perm.subtypePerm_apply, MulAut.conj_apply]

theorem exists_quotient_mulEquiv_perm [Finite G] (N K : Subgroup G) (hKN : K ≤ N) (O : Set G)
    (k : ℕ) (hO : ∀ n ∈ N, ∀ x ∈ O, n * x * n⁻¹ ∈ O) (hcard : Nat.card O = k)
    (hker : ∀ n ∈ N, (∀ x ∈ O, n * x * n⁻¹ = x) ↔ n ∈ K)
    (hord : Nat.card N = Nat.card K * k.factorial) :
    ∃ (_ : (K.subgroupOf N).Normal),
      Nonempty (↥N ⧸ K.subgroupOf N ≃* Equiv.Perm (Fin k)) := by
  let φ := conjActionOn N O hO
  have hkerφ : φ.ker = K.subgroupOf N := by
    ext n
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← hker n n.2]
    constructor
    · intro h x hx
      have := congrArg (fun σ : Equiv.Perm O => ((σ ⟨x, hx⟩ : O) : G)) h
      simpa [φ, conjActionOn_apply] using this
    · intro h
      ext ⟨x, hx⟩
      simpa [φ, conjActionOn_apply] using h x hx
  have hnormal : (K.subgroupOf N).Normal := hkerφ ▸ φ.normal_ker
  refine ⟨hnormal, ?_⟩
  have hK : Nat.card (K.subgroupOf N) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKN).toEquiv
  have hcardQ : Nat.card (↥N ⧸ φ.ker) = k.factorial := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    rw [hkerφ, hK, hord] at h1
    rw [hkerφ]
    have h2 : Nat.card K * k.factorial = Nat.card K * Nat.card (↥N ⧸ K.subgroupOf N) := by
      rw [h1, mul_comm]
    exact (Nat.eq_of_mul_eq_mul_left Nat.card_pos h2).symm
  have hbij : Function.Bijective (QuotientGroup.kerLift φ) :=
    (QuotientGroup.kerLift_injective φ).bijective_of_nat_card_le
      (by rw [Nat.card_perm, hcard, hcardQ])
  let e1 : ↥N ⧸ φ.ker ≃* Equiv.Perm O := MulEquiv.ofBijective (QuotientGroup.kerLift φ) hbij
  let e2 : Equiv.Perm O ≃* Equiv.Perm (Fin k) := (Finite.equivFinOfCardEq hcard).permCongrHom
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hkerφ.symm).trans (e1.trans e2)⟩

end CFSG.GroupTheory
