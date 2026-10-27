module

public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36G
public import CFSG.LocalAnalysis.ComponentClassification.SolMaxSig36H

public section

namespace CFSG.ComponentClassification.SolMax

open CFSG Subgroup Equiv

variable {X : Type} [Group X]

theorem exists_embedding_of_mulEquiv_fixAlt {r k : ℕ} {τ : Perm (Fin r)} {Y : Type*}
    [Fintype Y] [DecidableEq Y] (hk : 7 ≤ k) (hY : Fintype.card Y = k)
    (hτk : r - τ.support.card = k) (Φ : alternatingGroup Y ≃* fixAlt τ) :
    ∃ ι : Y ↪ Fin r, ∀ g : alternatingGroup Y,
      (((Φ g : fixAlt τ) : alternatingGroup (Fin r)) : Perm (Fin r)).support =
        (g : Perm Y).support.map ι := by
  classical
  obtain ⟨φ, hφ⟩ := exists_fixAlt_equiv τ
  have hcard : Fintype.card ↥(τ.supportᶜ : Finset (Fin r)) = k := by
    rw [Fintype.card_coe, Finset.card_compl, Fintype.card_fin, hτk]
  obtain ⟨ε, hε⟩ := exists_equiv_of_mulEquiv_alt hY hcard hk (Φ.trans φ.symm)
  refine ⟨ε.toEmbedding.trans (Function.Embedding.subtype _), fun g => ?_⟩
  have h1 : φ ((Φ.trans φ.symm) g) = Φ g := by
    change φ (φ.symm (Φ g)) = Φ g
    rw [MulEquiv.apply_symm_apply]
  have h3 : (g : Perm Y).support.map ε.toEmbedding = (ε.permCongr (g : Perm Y)).support := by
    ext z
    rw [Finset.mem_map_equiv, Perm.mem_support, Perm.mem_support, Equiv.permCongr_apply]
    exact not_congr ε.eq_symm_apply
  rw [← h1, hφ, hε, ← Finset.map_map, h3]
  convert Perm.support_ofSubtype (ε.permCongr (g : Perm Y))

theorem coreImage_one {J : Subgroup X} {n : ℕ}
    (θ : ↥J ⧸ pPrimeCore 2 ↥J ≃* alternatingGroup (Fin n)) (h : (1 : X) ∈ J) :
    coreImage θ h = 1 := by
  unfold coreImage
  have h1 : ((⟨1, h⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) = 1 := rfl
  rw [h1, map_one]
  rfl

namespace Sig36

variable [Finite X] [IsSimpleGroup X] {t : X} {J : Subgroup X} {n : ℕ}
  {e : J ⧸ pPrimeCore 2 J ≃* alternatingGroup (Fin n)} {E : Subgroup X} {D : Finset (Fin n)}
  (S : Sig36 X t J n e E D)
include S

theorem support_coreImage_E {x : X} (hxE : x ∈ E) (hx1 : x ≠ 1) :
    (coreImage e (S.le hxE)).support = D := by
  have hsub : (coreImage e (S.le hxE)).support ⊆ D := by
    intro ω hω
    by_contra hωD
    exact (Perm.mem_support.mp hω) (S.supp ⟨x, S.le hxE⟩ hxE ω hωD)
  exact Finset.eq_of_subset_of_card_le hsub (by rw [S.card_support_coreImage_E hxE hx1, S.card])

theorem exists_embedding_of_le {M : Subgroup X} {m : ℕ} (htM : t ∈ normalizer (M : Set X))
    (hJM : J ≤ M) (hnm : n < m) (hm6 : m ≠ 6)
    {θ : ↥M ⧸ pPrimeCore 2 ↥M ≃* alternatingGroup (Fin m)}
    {ρ : ↥(normalizer (M : Set X)) →* Perm (Fin m)} (hρ : IsPermAction θ ρ) :
    ∃ ι : Fin n ↪ Fin m, ∀ (x : X) (hx : x ∈ J),
      (ρ ⟨x, le_normalizer (hJM hx)⟩).support = (coreImage e hx).support.map ι := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn9 := S.nine_le
  have hJN : J ≤ normalizer (M : Set X) := hJM.trans le_normalizer
  have hJC := S.pair.1.2.1
  have hJpc := S.pair.1.2.2.1
  have ht2 : t * t = 1 := by rw [← sq, ← S.pair.1.1, pow_orderOf_eq_one]
  obtain ⟨a₁, -, -, h₁, -, -, h₁₁, -⟩ := exists_three_of_klein S.klein
  have hne : ∃ x : ↥J, ρ ⟨x, hJN x.2⟩ ≠ 1 := by
    refine ⟨⟨a₁, S.le h₁⟩, fun h => ?_⟩
    have h4 := S.card_support_of_mem_E htM hJM hnm hm6 hρ h₁ h₁₁
    have h5 : ρ ⟨a₁, le_normalizer (hJM (S.le h₁))⟩ = 1 := h
    rw [h5, Perm.support_one, Finset.card_empty] at h4
    omega
  have hpc : IsPComponent 2 (J.subgroupOf (M ⊓ centralizer ({t} : Set X))) :=
    GSThmB.B5a.isPComponent_subgroupOf_of_le (le_inf hJM hJC) inf_le_right hJpc
  obtain ⟨τ, hτk, ψ, hψ⟩ := exists_image_equiv (by omega) hnm.le hm6 θ hρ hJN
    (primeResidual_eq_top_of_isPComponent hJC hJpc)
    (UnbalancedCorr.commutator_eq_of_isPComponent hJC hJpc) (Fintype.card_fin n) e hne
    (Or.inr ⟨t, htM, ht2, hJM, hJC, hpc⟩)
  obtain ⟨ι, hι⟩ := exists_embedding_of_mulEquiv_fixAlt (by omega) (Fintype.card_fin n) hτk
    (e.symm.trans ψ)
  refine ⟨ι, fun x hx => ?_⟩
  have h1 := hι (e ((⟨x, hx⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J))
  have h2 : (e.symm.trans ψ) (e ((⟨x, hx⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J)) =
      ψ ((⟨x, hx⟩ : ↥J) : ↥J ⧸ pPrimeCore 2 ↥J) := by
    change ψ (e.symm (e _)) = _
    rw [MulEquiv.symm_apply_apply]
  rw [h2, hψ ⟨x, hx⟩] at h1
  exact h1

theorem inf_centralizer_le {e₀ e₁ : X} (he₀E : e₀ ∈ E) (he₁E : e₁ ∈ E) (he₀1 : e₀ ≠ 1)
    (he₁1 : e₁ ≠ 1) (h01 : e₀ ≠ e₁) :
    centralizer ({e₀} : Set X) ⊓ centralizer ({e₁} : Set X) ≤
      normalizer (Sol78.signalizerCompletion E E : Set X) := by
  obtain ⟨hE4, hE2⟩ := card_sq_of_klein S.klein
  have : IsKleinFour ↥E := isKleinFour_of_card hE4 fun g => Subtype.ext (by
    have h := hE2 g g.2
    rw [sq] at h
    exact h)
  intro x hx
  obtain ⟨hx₀, hx₁⟩ := mem_inf.mp hx
  rw [mem_centralizer_singleton_iff] at hx₀ hx₁
  refine normalizer_le_normalizer_signalizerCompletion_self E
    (Subgroup.centralizer_le_normalizer (E : Set X) ?_)
  rw [mem_centralizer_iff]
  intro y hy
  by_cases hy1 : y = 1
  · rw [hy1, mul_one, one_mul]
  by_cases hy₀ : y = e₀
  · rw [hy₀, hx₀]
  by_cases hy₁ : y = e₁
  · rw [hy₁, hx₁]
  have h := IsKleinFour.eq_mul_of_ne_all (G := ↥E) (x := ⟨e₀, he₀E⟩) (y := ⟨e₁, he₁E⟩)
    (z := ⟨y, hy⟩) (fun h => he₀1 (congrArg Subtype.val h))
    (fun h => he₁1 (congrArg Subtype.val h)) (fun h => h01 (congrArg Subtype.val h))
    (fun h => hy1 (congrArg Subtype.val h)) (fun h => hy₀ (congrArg Subtype.val h))
    (fun h => hy₁ (congrArg Subtype.val h))
  have hy' : y = e₀ * e₁ := congrArg Subtype.val h
  rw [hy']
  calc e₀ * e₁ * x = e₀ * (e₁ * x) := by group
    _ = e₀ * (x * e₁) := by rw [hx₁]
    _ = e₀ * x * e₁ := by group
    _ = x * e₀ * e₁ := by rw [hx₀]
    _ = x * (e₀ * e₁) := by group

theorem t_mem_normalizer_completion :
    t ∈ normalizer (Sol78.signalizerCompletion E E : Set X) :=
  normalizer_le_normalizer_signalizerCompletion_self E
    (Subgroup.centralizer_le_normalizer (E : Set X) S.t_mem_centralizer)

end Sig36

end CFSG.ComponentClassification.SolMax
