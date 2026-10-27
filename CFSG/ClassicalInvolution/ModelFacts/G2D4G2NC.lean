module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Cent
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Block
public import CFSG.ClassicalInvolution.ModelFacts.ClassicalIsFundamentalAdjoint

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

theorem isUniqueInvolution_range_sl2 {F : Type} [Field F] [Finite F] (hodd : Odd (Nat.card F))
    {G : Type} [Group G] {φ : SL(2, F) →* G} (hφ : Function.Injective φ) :
    IsUniqueInvolution φ.range (φ (-1)) where
  mem := ⟨-1, rfl⟩
  ne_one := fun h => CFSG.ClassicalInvolution.sl2_neg_one_ne_one hodd
    (hφ (h.trans (map_one φ).symm))
  sq := by
    have h : (-1 : SL(2, F)) * -1 = 1 := by simp
    rw [← map_mul, h, map_one]
  unique := by
    rintro _ ⟨A, rfl⟩ hA
    have hA2 : A * A = 1 := hφ (by rw [map_mul, hA, map_one])
    rcases CFSG.ClassicalInvolution.Generic.sl2_sq_eq_one
      (CFSG.Semidihedral.OddFieldSL2.two_ne_zero_of_odd_card F hodd) hA2 with rfl | rfl
    · exact Or.inl (map_one φ)
    · exact Or.inr rfl

section Standard

variable {p e : ℕ} [Fact p.Prime]

theorem noCommutingConj_standard_g2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .G2 0 p e) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ)
    (g : ↥(adjointGroup Tag.G2 (GaloisField p e)))
    (hne : conjSub g (rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
        rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ)) ≠
      rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
        rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ)) :
    ¬ Commutes (rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
        rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ))
      (conjSub g (rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
        rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ))) := by
  intro hcomm
  set F := GaloisField p e with hF
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card F) := by
    rw [GaloisField.card p e he]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ p ^ e := by omega
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
  obtain ⟨c, hιc, huniq⟩ := isUniqueInvolution_comap hιinj hz
  have hQfund : Q ∈ fundamentalSubgroups StatedLieTag.G2
      (modelUniv StatedLieTag.G2 0 p e Fact.out).D :=
    ⟨1, γ, Or.inr (Or.inl ⟨rfl, mem_adjDatum_roots.2 hγ⟩), by rw [conjSub_one]; rfl⟩
  have hQperf : ⁅Q, Q⁆ = Q :=
    le_antisymm
      (Subgroup.commutator_le.mpr fun _ hx _ hy =>
        Q.mul_mem (Q.mul_mem (Q.mul_mem hx hy) (Q.inv_mem hx)) (Q.inv_mem hy))
      (RouteD.Gaps.fundPerfect_modelUniv (t := StatedLieTag.G2) hp2 trivial hadm h4 Q hQfund)
  have hQ'perf : ⁅conjSub g Q, conjSub g Q⁆ = conjSub g Q := by
    show ⁅Q.map (MulAut.conj g).toMonoidHom, Q.map (MulAut.conj g).toMonoidHom⁆ =
      Q.map (MulAut.conj g).toMonoidHom
    rw [← Subgroup.map_commutator, hQperf]
  have huniq' : IsUniqueInvolution (conjSub g Q) (g * c * g⁻¹) := huniq.conj g
  have hPt : ∀ r ∈ conjSub g Q, c * r = r * c := fun r hr => hcomm c huniq.mem r hr
  have hshared := g2_eq_one_or_eq_of_central_in_perfect (K := F) hodd huniq.sq huniq.ne_one hPt
    hQ'perf huniq'.mem (fun r hr => isUniqueInvolution_central huniq' hr)
  have hgc : g * c * g⁻¹ = c := by
    rcases hshared with h | h
    · exact absurd (by simpa using h) huniq.ne_one
    · exact h
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
  exact hne (normalizer_iff_conjSub_eq.mp hgN)

theorem noCommutingConj_g2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .G2 0 p e) :
    ∀ F ∈ fundamentalSubgroups StatedLieTag.G2 (modelUniv StatedLieTag.G2 0 p e Fact.out).D,
      ∀ g : (modelUniv StatedLieTag.G2 0 p e Fact.out).K, conjSub g F ≠ F →
        ¬ Commutes F (conjSub g F) := by
  change ∀ F ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)),
    ∀ g : ↥(adjointGroup Tag.G2 (GaloisField p e)), conjSub g F ≠ F → ¬ Commutes F (conjSub g F)
  rintro F ⟨g₀, γ, hγ, rfl⟩ g hne hcomm
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
  refine noCommutingConj_standard_g2 hp2 hq hadm hγroot (g₀⁻¹ * g * g₀) ?_ ?_
  · rw [h1]
    intro h
    apply hne
    have h2 := congrArg (conjSub g₀) h
    rw [conjSub_conjSub_inv] at h2
    exact h2
  · rw [h1]
    have := (commutes_conjSub_iff g₀⁻¹).mpr hcomm
    rwa [conjSub_inv_conjSub] at this

end Standard

end CFSG.ClassicalInvolution.G2D4Models
