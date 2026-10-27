module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank

variable {p e : ℕ} [Fact p.Prime]

theorem noTwins_standard_g2 (hp2 : p ≠ 2) (he : 1 ≤ e) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot Tag.G2 γ) {c : ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hc : IsUniqueInvolution (rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
      rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ)) c)
    (g : ↥(adjointGroup Tag.G2 (GaloisField p e)))
    (hg : IsUniqueInvolution (conjSub g (rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
      rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ))) c) :
    conjSub g (rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
        rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ)) =
      rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
        rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ) := by
  set F := GaloisField p e with hF
  have hodd : Odd (Nat.card F) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hK2 : ringChar F ≠ 2 := ringChar_ne_two_of_odd_nat_card hodd
  set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  set Q : Subgroup ↥(adjointGroup Tag.G2 F) :=
    rootGroup (rootOperatorFamily Tag.G2) F γ ⊔ rootGroup (rootOperatorFamily Tag.G2) F (-γ)
    with hQ
  have hQmap : Q.map ι = rootPair Tag.G2 F γ := by
    rw [hQ, ← ModelFacts.subgroupOf_rootSubgroup_sup_eq (rootOperatorFamily Tag.G2) hγ, hι,
      Subgroup.subgroupOf_map_subtype]
    exact inf_eq_left.2 (sup_le (rootSubgroup_le_adjointGroup γ)
      (rootSubgroup_le_adjointGroup (-γ)))
  obtain ⟨a, ha, hne1, hγa⟩ := exists_signKernel_g2 hK2 hγ
  obtain ⟨w, i, φ, hw, hφinj, hφrange, hφneg⟩ := exists_hom_of_isRoot hK2 hγ
  have hφa : φ (-1) = rootDiagUnit Tag.G2 a :=
    hφneg.trans (torusElt_neg_one_conj_eq_rootDiagUnit hodd ha hne1 hγa hw)
  have hmod : IsUniqueInvolution (rootPair Tag.G2 F γ) (rootDiagUnit Tag.G2 a) := by
    have := isUniqueInvolution_range_sl2 hodd hφinj
    rwa [hφa, hφrange] at this
  have hz : IsUniqueInvolution (Q.map ι) (rootDiagUnit Tag.G2 a) := by
    rw [hQmap]
    exact hmod
  obtain ⟨c', hιc, huniq⟩ := isUniqueInvolution_comap hιinj hz
  have hcc' : c = c' := hc.eq huniq
  subst hcc'
  have hgc : g * c * g⁻¹ = c := (hg.eq (hc.conj g)).symm
  have hcent : g * c = c * g := by
    calc g * c = g * c * g⁻¹ * g := by group
      _ = c * g := by rw [hgc]
  have hX : ι g ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨g.2, ?_⟩
    have h1 : ι g * rootDiagUnit Tag.G2 a = rootDiagUnit Tag.G2 a * ι g := by
      rw [← hιc, ← map_mul, ← map_mul, hcent]
    rw [mul_inv_eq_iff_eq_mul, ← h1]
  have hN := toralCentralizer_le_normalizer_rootPair hodd ha hne1 hγa hX
  have hgN : g ∈ Subgroup.normalizer (Q : Set ↥(adjointGroup Tag.G2 F)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp hN (ι x)
    rw [← hQmap, Subgroup.mem_map_iff_mem hιinj] at h1
    have h2 : ι g * ι x * (ι g)⁻¹ = ι (g * x * g⁻¹) := by simp
    rw [h2, Subgroup.mem_map_iff_mem hιinj] at h1
    exact h1
  exact normalizer_iff_conjSub_eq.mp hgN

theorem noTwins_g2 (hp2 : p ≠ 2) (he : 1 ≤ e) :
    ∀ F ∈ fundamentalSubgroups StatedLieTag.G2 (modelUniv StatedLieTag.G2 0 p e Fact.out).D,
      ∀ c : (modelUniv StatedLieTag.G2 0 p e Fact.out).K, IsUniqueInvolution F c →
        ∀ g : (modelUniv StatedLieTag.G2 0 p e Fact.out).K,
          IsUniqueInvolution (conjSub g F) c → conjSub g F = F := by
  change ∀ F ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)),
    ∀ c : ↥(adjointGroup Tag.G2 (GaloisField p e)), IsUniqueInvolution F c →
      ∀ g : ↥(adjointGroup Tag.G2 (GaloisField p e)),
        IsUniqueInvolution (conjSub g F) c → conjSub g F = F
  rintro F ⟨g₀, γ, hγ, rfl⟩ c hc g hg
  have hγroot : IsRoot Tag.G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  set Q : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e)) :=
    rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
      rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ) with hQ
  have h1 : conjSub (g₀⁻¹ * g * g₀) Q = conjSub g₀⁻¹ (conjSub g (conjSub g₀ Q)) := by
    rw [conjSub_mul, conjSub_mul]
  have hc₀ : IsUniqueInvolution Q (g₀⁻¹ * c * g₀⁻¹⁻¹) := by
    have := hc.conj g₀⁻¹
    rwa [conjSub_inv_conjSub] at this
  have hg₀ : IsUniqueInvolution (conjSub (g₀⁻¹ * g * g₀) Q) (g₀⁻¹ * c * g₀⁻¹⁻¹) := by
    rw [h1]
    exact hg.conj g₀⁻¹
  have key := noTwins_standard_g2 hp2 he hγroot hc₀ (g₀⁻¹ * g * g₀) hg₀
  rw [h1] at key
  have h2 := congrArg (conjSub g₀) key
  rw [conjSub_conjSub_inv] at h2
  exact h2

end CFSG.ClassicalInvolution.G2D4Models
