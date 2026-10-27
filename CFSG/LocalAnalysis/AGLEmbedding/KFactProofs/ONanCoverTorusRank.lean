module

public import CFSG.RankThree.PartOne.K159.CoverPSL
public import CFSG.RankThree.PartOne.K159.CoverPSU
import CFSG.RankThree.PartOne.K159.CenterRank

public section

namespace CFSG.AGLEmbedding.KFactProofs.CoverFive

open scoped commutatorElement
open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Assembly.RankThreeEven
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.RankThree.Classical CFSG.RankThree.Classical2
  CFSG.RankThree.PartOne.K159

theorem exists_elemAbelian_four_psl_of_ne_two {K : Type} [Group K] [Finite K] {p ℓ n f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSL n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f - 1) :
    ∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 4 ≤ Nat.card B := by
  classical
  obtain ⟨⟨hℓ, hf, hn2, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have := Fintype.ofFinite k
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hpk : p ∣ Fintype.card k - 1 := by rwa [← Nat.card_eq_fintype_card, hk]
  have : Fact p.Prime := ⟨hp⟩
  let ψ : K ⧸ Subgroup.center K ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    e.trans (projectiveSpecialLinearGroupEquivStatedProj n k).symm
  let φ : K →* Matrix.ProjectiveSpecialLinearGroup (Fin n) k :=
    ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := ker_comp_mk'_eq_center ψ
  have hodd' : Odd (Nat.card φ.ker) := by rw [hker]; exact hodd
  have hcard : p ∣ Nat.card kˣ := by
    rw [Nat.card_units, Nat.card_eq_fintype_card]
    exact hpk
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' p hcard
  have hζ : ζ ^ p = 1 := by rw [← hζo, pow_orderOf_eq_one]
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hzk : (z : K) ∈ φ.ker := by rw [hker]; exact z.2
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_psl hp hp2 hζo hζ (by omega : 2 ≤ m) hφs
    hker.le hodd' hzk hz1 hzp
  refine ⟨B, hBp, hBc, le_trans ?_ hBcard⟩
  simp only [hpn, ↓reduceIte]
  exact Nat.pow_le_pow_right hp.pos (by omega)

section Unitary

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem exists_elemAbelian_unitary_of_ne_two {Y : Type*} [Group Y] [Finite Y]
    (hK : UnitaryFieldData ℓ f K) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ ℓ ^ f + 1)
    {n : ℕ} (hn : 3 ≤ n) (φ : Y →* unitaryPSU hK n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (hodd : Odd (Nat.card φ.ker)) {z : Y} (hz : z ∈ φ.ker)
    (hz1 : z ≠ 1) (hzp : z ^ p = 1) :
    ∃ B : Subgroup Y, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ (n - 1 - (if p ∣ n then 1 else 0) + 1) ≤ Nat.card B := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one hK hp hpq
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have hn1 : 1 ≤ m + 3 := by omega
  set c : Fin (m + 2) → Fin (m + 3) → Kˣ := fun j i =>
    if i = 0 then ζ else if i = j.succ then ζ⁻¹ else 1 with hcdef
  have hcp : ∀ j i, c j i ^ p = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζp
    · rw [inv_pow, hζp, inv_one]
    · exact one_pow p
  have hcnorm : ∀ j i, c j i ^ (ℓ ^ f + 1) = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζN
    · rw [inv_pow, hζN, inv_one]
    · exact one_pow _
  have hcprod : ∀ j, ∏ i, c j i = 1 := by
    intro j
    rw [Fin.prod_univ_succ]
    have h0 : c j 0 = ζ := by simp [hcdef]
    have h1 : ∀ i : Fin (m + 2), c j i.succ = if i = j then ζ⁻¹ else 1 := by
      intro i
      simp only [hcdef, Fin.succ_ne_zero, ite_false, Fin.succ_inj]
    simp only [h0, h1, Finset.prod_ite_eq', Finset.mem_univ, ite_true]
    group
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = p := by
    intro j
    refine ⟨j.succ, fun j' hj' => ?_, ?_⟩
    · simp only [hcdef, Fin.succ_ne_zero, ite_false, Fin.succ_inj]
      simp [hj'.symm]
    · simp only [hcdef, Fin.succ_ne_zero, ite_false, ite_true]
      rw [orderOf_inv, hζ]
  set d₁ : Fin (m + 3) → Kˣ := fun i => if i = 0 then -1 else 1 with hd₁
  have hd₁norm : ∀ i, ((d₁ i : Kˣ) : K) ^ (ℓ ^ f + 1) = 1 := by
    intro i
    simp only [hd₁]
    split_ifs
    · rw [Units.val_neg, Units.val_one]
      exact neg_one_pow_norm hK
    · rw [Units.val_one, one_pow]
  have hwS : ∀ a b : Fin (m + 3), a ≠ b →
      permGL (Equiv.swap a b) * diagHom (m + 3) d₁ ∈ unitarySU ℓ f K (m + 3) := by
    intro a b hab
    rw [mem_unitarySU_iff hK, Units.val_mul]
    refine ⟨?_, unitary_mul hK (permGL_unitary hK _) (diagHom_unitary hK hd₁norm)⟩
    rw [Matrix.det_mul, det_permGL, Equiv.Perm.sign_swap hab, det_diagHom, Fin.prod_univ_succ]
    simp [hd₁, Fin.succ_ne_zero]
  have hconj : ∀ (σ : Equiv.Perm (Fin (m + 3))) (e : Fin (m + 3) → Kˣ),
      (permGL σ * diagHom (m + 3) d₁) * diagHom (m + 3) e * (permGL σ * diagHom (m + 3) d₁)⁻¹ =
        diagHom (m + 3) (e ∘ σ.symm) := by
    intro σ e
    rw [← permGL_mul_diagHom_mul_inv σ e]
    have hcomm := (diagHom_commute (K := K) d₁ e).eq
    calc (permGL σ * diagHom (m + 3) d₁) * diagHom (m + 3) e *
          (permGL σ * diagHom (m + 3) d₁)⁻¹ =
        permGL σ * (diagHom (m + 3) d₁ * diagHom (m + 3) e) * (diagHom (m + 3) d₁)⁻¹ *
          (permGL σ)⁻¹ := by group
      _ = permGL σ * (diagHom (m + 3) e * diagHom (m + 3) d₁) * (diagHom (m + 3) d₁)⁻¹ *
          (permGL σ)⁻¹ := by rw [hcomm]
      _ = permGL σ * diagHom (m + 3) e * (permGL σ)⁻¹ := by group
  have hswap : ∀ j k, j ≠ k → ∃ w ∈ unitarySU ℓ f K (m + 3),
      w * diagHom (m + 3) (c j) * w⁻¹ = diagHom (m + 3) (c k) ∧
        w * diagHom (m + 3) (c k) * w⁻¹ = diagHom (m + 3) (c j) := by
    intro j k hjk
    have hjk' : j.succ ≠ k.succ := fun h => hjk (Fin.succ_injective _ h)
    have hcσ : ∀ a b : Fin (m + 2), c a ∘ (Equiv.swap a.succ b.succ).symm = c b := by
      intro a b
      funext i
      rw [Function.comp_apply, Equiv.symm_swap]
      have hs0 : Equiv.swap a.succ b.succ 0 = 0 :=
        Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero _).symm (Fin.succ_ne_zero _).symm
      simp only [hcdef, Equiv.swap_apply_eq_iff, hs0, Equiv.swap_apply_left]
    refine ⟨_, hwS _ _ hjk', ?_, ?_⟩
    · rw [hconj, hcσ]
    · rw [hconj, Equiv.swap_comm, hcσ]
  have hinv : ∀ j, ∃ w ∈ unitarySU ℓ f K (m + 3),
      w * diagHom (m + 3) (c j) * w⁻¹ = (diagHom (m + 3) (c j))⁻¹ := by
    intro j
    have h0j : (0 : Fin (m + 3)) ≠ j.succ := (Fin.succ_ne_zero j).symm
    refine ⟨_, hwS _ _ h0j, ?_⟩
    rw [hconj, ← map_inv]
    congr 1
    funext i
    rw [Function.comp_apply, Equiv.symm_swap, Pi.inv_apply]
    by_cases hi0 : i = 0
    · subst hi0
      rw [Equiv.swap_apply_left]
      simp [hcdef]
    by_cases hij : i = j.succ
    · subst hij
      rw [Equiv.swap_apply_right]
      simp [hcdef]
    · rw [Equiv.swap_apply_of_ne_of_ne hi0 hij]
      simp [hcdef, hi0, hij]
  have := exists_elemAbelian_unitary_witness hK hp hp2 hn1 φ hφ hker hodd c hcp
    (diagHom_expHom_mem_unitarySU hK c hcp hcprod hcnorm) (expHom_injective c hcp hpriv) hswap
    hinv hz hz1 hzp
  obtain ⟨B, hBp, hBc, hBcard⟩ := this
  exact ⟨B, hBp, hBc, by simpa using hBcard⟩

end Unitary

theorem exists_elemAbelian_four_psu_of_ne_two {K : Type} [Group K] [Finite K] {p ℓ n f : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hn5 : 5 ≤ n) (hpZ : p ∣ Nat.card (Subgroup.center K))
    (hodd : Odd (Nat.card (Subgroup.center K)))
    (hmod : StatedClassicalModel (K ⧸ Subgroup.center K) .PSU n ℓ f) (hpn : p ∣ n)
    (hpq : p ∣ ℓ ^ f + 1) :
    ∃ B : Subgroup K, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      p ^ 4 ≤ Nat.card B := by
  classical
  obtain ⟨⟨hℓ, hf, hn3, -⟩, k, _, hkfin, hk, ⟨e⟩⟩ := hmod
  have : Fact p.Prime := ⟨hp⟩
  have hU : UnitaryFieldData ℓ f k := ⟨hℓ, hf, by rw [hk, ← pow_mul, mul_comm]⟩
  let ψ : K ⧸ Subgroup.center K ≃* unitaryPSU hU n :=
    e.trans (unitaryPSUEquiv hU (by omega)).symm
  let φ : K →* unitaryPSU hU n := ψ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hφs : Function.Surjective φ := ψ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := ker_comp_mk'_eq_center ψ
  have hodd' : Odd (Nat.card φ.ker) := by rw [hker]; exact hodd
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center K) p hpZ
  have hz1 : (z : K) ≠ 1 := by
    intro h
    have : z = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz
    exact hp.one_lt.ne hz
  have hzp : (z : K) ^ p = 1 := by
    have := pow_orderOf_eq_one z
    rw [hz] at this
    exact congrArg Subtype.val this
  have hzk : (z : K) ∈ φ.ker := by rw [hker]; exact z.2
  obtain ⟨B, hBp, hBc, hBcard⟩ := exists_elemAbelian_unitary_of_ne_two hU hp hp2 hpq
    (by omega : 3 ≤ n) φ hφs hker.le hodd' hzk hz1 hzp
  refine ⟨B, hBp, hBc, le_trans ?_ hBcard⟩
  simp only [hpn, ↓reduceIte]
  exact Nat.pow_le_pow_right hp.pos (by omega)

end CFSG.AGLEmbedding.KFactProofs.CoverFive
