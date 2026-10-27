module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.NormalizerAction.HeisAction

public section

namespace CFSG.AGLEmbeddingD2.Wilson.NormalizerAction

open Subgroup
open scoped Matrix

variable {p : ℕ} {G : Type*} [Group G] {Q : Subgroup G}

theorem mem_inf_centralizer_iff (z : G) :
    z ∈ Q ⊓ Subgroup.centralizer (Q : Set G) ↔ ∃ z' : Subgroup.center Q, (z' : G) = z := by
  constructor
  · rintro ⟨hzQ, hzc⟩
    refine ⟨⟨⟨z, hzQ⟩, ?_⟩, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro q
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hzc q q.2)
  · rintro ⟨⟨z', hz'⟩, rfl⟩
    refine ⟨z'.2, Subgroup.mem_centralizer_iff.2 ?_⟩
    intro g hg
    exact congrArg Subtype.val ((Subgroup.mem_center_iff.1 hz') ⟨g, hg⟩)

theorem normalizerMonoidHom_coe (n : normalizer (Q : Set G)) (q : Q) :
    ((Q.normalizerMonoidHom n q : Q) : G) = (n : G) * q * (n : G)⁻¹ := by
  simp

namespace HeisCoordData

variable (D : HeisCoordData p Q)

theorem actMat_pow (t : normalizer (Q : Set G)) (j : ℕ) :
    D.actMat (t ^ j) = D.actMat t ^ j := by
  induction j with
  | zero => simp [D.actMat_one]
  | succ j ih => rw [pow_succ, D.actMat_mul, ih, pow_succ]

theorem conj_eq_zpow_mul_center (n : normalizer (Q : Set G)) (k : ℤ)
    (h : D.actMat n = (k : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) (q : Q) :
    ∃ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G),
      (n : G) * q * (n : G)⁻¹ = (q : G) ^ k * z := by
  have hπ : D.π ((q ^ k)⁻¹ * Q.normalizerMonoidHom n q) = 1 := by
    apply Multiplicative.toAdd.injective
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, D.π_conj, h, toAdd_one]
    simp [toAdd_zpow, Int.cast_smul_eq_zsmul]
  have hz : (q ^ k)⁻¹ * Q.normalizerMonoidHom n q ∈ Subgroup.center Q := by
    rw [← D.ker_eq]; exact hπ
  refine ⟨(((q ^ k)⁻¹ * Q.normalizerMonoidHom n q : Q) : G),
    (mem_inf_centralizer_iff _).2 ⟨⟨_, hz⟩, rfl⟩, ?_⟩
  rw [← normalizerMonoidHom_coe]
  simp

end HeisCoordData

open HeisCoordData

variable (D : HeisCoordData p Q)

theorem conj_pow_scalar (t : normalizer (Q : Set G)) (m lam : ℕ)
    (h : D.actMat t ^ m = (lam : ZMod p) • (1 : Matrix (Fin 2) (Fin 2) (ZMod p))) :
    ∀ x ∈ Q, ∃ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G),
      (t : G) ^ m * x * ((t : G) ^ m)⁻¹ = x ^ lam * z := by
  intro x hx
  obtain ⟨z, hz, e⟩ := D.conj_eq_zpow_mul_center (t ^ m) (lam : ℤ)
    (by rw [D.actMat_pow, h]; simp) ⟨x, hx⟩
  exact ⟨z, hz, by simpa using e⟩

theorem conj_pow_inv (t : normalizer (Q : Set G)) (e : ℕ) (h : D.actMat t ^ e = -1) :
    ∀ x ∈ Q, ∃ z ∈ Q ⊓ Subgroup.centralizer (Q : Set G),
      (t : G) ^ e * x * ((t : G) ^ e)⁻¹ = x⁻¹ * z := by
  intro x hx
  obtain ⟨z, hz, e'⟩ := D.conj_eq_zpow_mul_center (t ^ e) (-1 : ℤ)
    (by rw [D.actMat_pow, h]; simp) ⟨x, hx⟩
  exact ⟨z, hz, by simpa using e'⟩

section lines

variable [Fact p.Prime]

theorem natCard_coords : Nat.card (Multiplicative (Fin 2 → ZMod p)) = p ^ 2 := by
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin 2 → ZMod p) ≃ _), Nat.card_pi]
  simp [ZMod.card]

theorem pow_not_mem_normalizer_of_no_eigenvector
    (t : normalizer (Q : Set G)) (j : ℕ)
    (hj : ∀ v : Fin 2 → ZMod p, v ≠ 0 → ∀ c : ZMod p, D.actMat t ^ j *ᵥ v ≠ c • v)
    (F : Subgroup G) (hZF : Q ⊓ Subgroup.centralizer (Q : Set G) ≤ F)
    (hF : F.relIndex Q = p) : (t : G) ^ j ∉ Subgroup.normalizer (F : Set G) := by
  intro hn
  set F' : Subgroup Q := F.subgroupOf Q with hF'
  set L : Subgroup (Multiplicative (Fin 2 → ZMod p)) := F'.map D.π with hL
  have hcen : D.π.ker ≤ F' := by
    intro q hq
    rw [D.ker_eq] at hq
    exact hZF ((mem_inf_centralizer_iff _).2 ⟨⟨q, hq⟩, rfl⟩)
  have hcomap : L.comap D.π = F' := by
    ext q
    simp only [hL, Subgroup.mem_comap, Subgroup.mem_map]
    constructor
    · rintro ⟨f, hf, hfq⟩
      have : f⁻¹ * q ∈ D.π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hfq, inv_mul_cancel]
      simpa using F'.mul_mem hf (hcen this)
    · intro hq; exact ⟨q, hq, rfl⟩
  have hidx : L.index = p := by
    rw [← Subgroup.index_comap_of_surjective L D.surj, hcomap]
    exact hF
  have hcardL : Nat.card L = p := by
    have h := Subgroup.card_mul_index L
    rw [hidx, natCard_coords] at h
    have hp0 : 0 < p := (Fact.out : p.Prime).pos
    have : Nat.card L * p = p * p := by rw [h]; ring
    exact Nat.eq_of_mul_eq_mul_right hp0 this
  have hp := (Fact.out : p.Prime)
  have hLne : L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcardL
    exact hp.one_lt.ne hcardL
  obtain ⟨ℓ, hℓL, hℓ1⟩ := (Subgroup.bot_or_exists_ne_one L).resolve_left hLne
  have hord : orderOf ℓ = p := by
    have hd : orderOf ℓ ∣ p := by
      have := Subgroup.orderOf_dvd_natCard L hℓL
      rwa [hcardL] at this
    exact ((Nat.dvd_prime hp).1 hd).resolve_left (fun h => hℓ1 (orderOf_eq_one_iff.1 h))
  have hzp : Subgroup.zpowers ℓ = L := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hℓL) ?_
    rw [Nat.card_zpowers, hord, hcardL]
  obtain ⟨q, hq, rfl⟩ := Subgroup.mem_map.1 hℓL
  have hqF : (q : G) ∈ F := hq
  set nt : normalizer (Q : Set G) := t ^ j with hnt
  have hntG : (nt : G) = (t : G) ^ j := by simp [hnt]
  have hcF : Q.normalizerMonoidHom nt q ∈ F' := by
    show ((Q.normalizerMonoidHom nt q : Q) : G) ∈ F
    rw [normalizerMonoidHom_coe, hntG]
    exact (Subgroup.mem_normalizer_iff.1 hn _).1 hqF
  have hmem : D.π (Q.normalizerMonoidHom nt q) ∈ Subgroup.zpowers (D.π q) := by
    rw [hzp]; exact Subgroup.mem_map_of_mem _ hcF
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hv : Multiplicative.toAdd (D.π q) ≠ 0 := fun h => hℓ1 (by simpa using h)
  apply hj _ hv (k : ZMod p)
  have h1 := D.π_conj nt q
  rw [← hk, hnt, D.actMat_pow] at h1
  rw [← h1]
  simp [toAdd_zpow, Int.cast_smul_eq_zsmul]

end lines

section numerics

@[expose] def J4Matrix : Matrix (Fin 2) (Fin 2) (ZMod 11) := !![8, 10; 6, 5]

theorem J4Matrix_pow_four :
    J4Matrix ^ 4 = (7 : ZMod 11) • (1 : Matrix (Fin 2) (Fin 2) (ZMod 11)) := by
  decide +kernel

theorem J4Matrix_pow_sixty : J4Matrix ^ 60 = -1 := by
  decide +kernel

theorem orderOf_seven : orderOf (((7 : ℕ) : ZMod 11)) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide +kernel, ?_⟩
  intro m hm hm0
  interval_cases m <;> revert hm0 <;> decide +kernel

theorem J4Matrix_no_eigenvector (j : ℕ) (hj : j = 1 ∨ j = 2 ∨ j = 3) :
    ∀ v : Fin 2 → ZMod 11, v ≠ 0 → ∀ c : ZMod 11, J4Matrix ^ j *ᵥ v ≠ c • v := by
  rcases hj with rfl | rfl | rfl <;> decide +kernel

end numerics

end CFSG.AGLEmbeddingD2.Wilson.NormalizerAction
