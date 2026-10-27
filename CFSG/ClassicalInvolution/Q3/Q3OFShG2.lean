module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

set_option linter.unusedSectionVars false

public noncomputable section

namespace CFSG.ClassicalInvolution.Q3.Q3OF

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.G2D4Models CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Sign

variable {p e : ℕ} [Fact p.Prime]

theorem g2_exists_signInvolution (hp2 : p ≠ 2) (he : 1 ≤ e) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot Tag.G2 γ) :
    ∃ (a : Fin Tag.G2.rank → (GaloisField p e)ˣ)
      (c : ↥(adjointGroup Tag.G2 (GaloisField p e))),
      (∀ i, a i = 1 ∨ a i = -1) ∧ a ≠ 1 ∧ γ ∈ rootCharKernel a ∧
        (c : ModGL Tag.G2 (GaloisField p e)) = rootDiagUnit Tag.G2 a ∧
        IsUniqueInvolution (rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
          rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ)) c := by
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
  exact ⟨a, c', ha, hne1, hγa, hιc, huniq⟩

abbrev Qr (p e : ℕ) [Fact p.Prime] (γ : Fin Tag.G2.rank → ℤ) :
    Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e)) :=
  rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
    rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ)

theorem map_Qr_subtype {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) :
    (Qr p e γ).map (adjointGroup Tag.G2 (GaloisField p e)).subtype =
      rootPair Tag.G2 (GaloisField p e) γ := by
  rw [Qr, ← ModelFacts.subgroupOf_rootSubgroup_sup_eq (rootOperatorFamily Tag.G2) hγ,
    Subgroup.subgroupOf_map_subtype]
  exact inf_eq_left.2 (sup_le (rootSubgroup_le_adjointGroup γ)
    (rootSubgroup_le_adjointGroup (-γ)))

theorem conjSub_Qr_eq_of_mem_normalizer {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ)
    {h : ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hN : (h : ModGL Tag.G2 (GaloisField p e)) ∈
      Subgroup.normalizer (rootPair Tag.G2 (GaloisField p e) γ : Set (ModGL Tag.G2 _))) :
    conjSub h (Qr p e γ) = Qr p e γ := by
  set ι : ↥(adjointGroup Tag.G2 (GaloisField p e)) →* ModGL Tag.G2 (GaloisField p e) :=
    (adjointGroup Tag.G2 (GaloisField p e)).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  have hN' : ι h ∈ Subgroup.normalizer
      (rootPair Tag.G2 (GaloisField p e) γ : Set (ModGL Tag.G2 (GaloisField p e))) := hN
  have hgN : h ∈ Subgroup.normalizer (Qr p e γ : Set ↥(adjointGroup Tag.G2 (GaloisField p e))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp hN' (ι x)
    rw [← map_Qr_subtype hγ, Subgroup.mem_map_iff_mem hιinj] at h1
    have h2 : ι h * ι x * (ι h)⁻¹ = ι (h * x * h⁻¹) := by simp
    rw [h2, Subgroup.mem_map_iff_mem hιinj] at h1
    exact h1
  exact normalizer_iff_conjSub_eq.mp hgN

theorem conjSub_weylRep_Qr {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ)
    (w : WeylGroup Tag.G2) :
    conjSub (⟨canonicalRep (coxeterSystem Tag.G2) (GaloisField p e) w,
        canonicalRep_mem_adjointGroup _ (GaloisField p e) w⟩ :
        ↥(adjointGroup Tag.G2 (GaloisField p e))) (Qr p e γ) = Qr p e (w • γ) := by
  set F := GaloisField p e with hF
  set ι : ↥(adjointGroup Tag.G2 F) →* ModGL Tag.G2 F := (adjointGroup Tag.G2 F).subtype with hι
  have hιinj : Function.Injective ι := Subtype.val_injective
  set N : ↥(adjointGroup Tag.G2 F) :=
    ⟨canonicalRep (coxeterSystem Tag.G2) F w, canonicalRep_mem_adjointGroup _ F w⟩ with hN
  apply Subgroup.map_injective hιinj
  have hcomm : ι.comp (MulAut.conj N).toMonoidHom = (MulAut.conj (ι N)).toMonoidHom.comp ι := by
    ext x
    simp [hι]
  have h1 : (conjSub N (Qr p e γ)).map ι =
      ((Qr p e γ).map ι).map (MulAut.conj (ι N)).toMonoidHom := by
    show ((Qr p e γ).map (MulAut.conj N).toMonoidHom).map ι = _
    rw [Subgroup.map_map, hcomm, ← Subgroup.map_map]
  have h2 := (canonical_weyl_root_transport Tag.G2 F).2.1 w γ hγ
  have h3 := (canonical_weyl_root_transport Tag.G2 F).2.1 w (-γ) (IsRoot.neg hγ)
  rw [h1, map_Qr_subtype hγ, map_Qr_subtype (IsRoot.smul hγ w)]
  show (rootPair Tag.G2 F γ).map (MulAut.conj (canonicalRep (coxeterSystem Tag.G2) F w)).toMonoidHom
    = _
  rw [rootPair, Subgroup.map_sup, h2, h3, smul_neg]
  rfl

theorem Qr_neg (γ : Fin Tag.G2.rank → ℤ) : Qr p e (-γ) = Qr p e γ := by
  rw [Qr, Qr, neg_neg, sup_comm]

theorem g2_conj_Qr_eq_of_involution (hp2 : p ≠ 2) (he : 1 ≤ e) {γ : Fin Tag.G2.rank → ℤ}
    (hγ : IsRoot Tag.G2 γ) {a : Fin Tag.G2.rank → (GaloisField p e)ˣ}
    (ha : ∀ i, a i = 1 ∨ a i = -1) (ha1 : a ≠ 1)
    {c : ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hc : (c : ModGL Tag.G2 (GaloisField p e)) = rootDiagUnit Tag.G2 a)
    {g : ↥(adjointGroup Tag.G2 (GaloisField p e))}
    (hg : IsUniqueInvolution (conjSub g (Qr p e γ)) c) :
    ∃ δ, δ ∈ rootCharKernel a ∧ conjSub g (Qr p e γ) = Qr p e δ := by
  set F := GaloisField p e with hF
  have hodd : Odd (Nat.card F) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  obtain ⟨a', c', ha', ha'1, hγa', hc'd, hc'u⟩ := g2_exists_signInvolution hp2 he hγ
  have hcc' : g * c' * g⁻¹ = c := (hc'u.conj g).eq hg
  obtain ⟨w, hw⟩ := g2_signTuple_conj ha' ha ha'1 ha1
  set N : ↥(adjointGroup Tag.G2 F) :=
    ⟨canonicalRep (coxeterSystem Tag.G2) F w, canonicalRep_mem_adjointGroup _ F w⟩ with hN
  have hNc : ((N * c' * N⁻¹ : ↥(adjointGroup Tag.G2 F)) : ModGL Tag.G2 F) =
      rootDiagUnit Tag.G2 a := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hc'd, Subgroup.coe_inv, ← hw]
    exact canonicalRep_conj_rootDiagUnit w a'
  set h : ↥(adjointGroup Tag.G2 F) := g * N⁻¹ with hh
  have hX : (h : ModGL Tag.G2 F) ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨h.2, ?_⟩
    have e1 : h * (N * c' * N⁻¹) * h⁻¹ = c := by
      rw [← hcc', hh]
      group
    have e2 := congrArg (fun x : ↥(adjointGroup Tag.G2 F) => (x : ModGL Tag.G2 F)) e1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hNc, hc] at e2
    have e3 : (h : ModGL Tag.G2 F) * rootDiagUnit Tag.G2 a =
        rootDiagUnit Tag.G2 a * (h : ModGL Tag.G2 F) := by
      calc (h : ModGL Tag.G2 F) * rootDiagUnit Tag.G2 a =
          ((h : ModGL Tag.G2 F) * rootDiagUnit Tag.G2 a * (h : ModGL Tag.G2 F)⁻¹) * h := by group
        _ = rootDiagUnit Tag.G2 a * (h : ModGL Tag.G2 F) := by rw [e2]
    rw [mul_inv_eq_iff_eq_mul]
    exact e3.symm
  have hδ : (w • γ) ∈ rootCharKernel a :=
    ⟨IsRoot.smul hγ w, by rw [← hw, rootChar_weylTuple, inv_smul_smul]; exact hγa'.2⟩
  have hnorm := toralCentralizer_le_normalizer_rootPair hodd ha ha1 hδ hX
  have hconj := conjSub_Qr_eq_of_mem_normalizer (IsRoot.smul hγ w) hnorm
  refine ⟨w • γ, hδ, ?_⟩
  have hgh : conjSub g (Qr p e γ) = conjSub h (conjSub N (Qr p e γ)) := by
    rw [← conjSub_mul, hh]
    congr 1
    group
  rw [hgh, conjSub_weylRep_Qr hγ w, hconj]

theorem Qr_commute {α β : Fin Tag.G2.rank → ℤ} (hα : IsRoot Tag.G2 α) (hβ : IsRoot Tag.G2 β)
    (h : ⁅rootPair Tag.G2 (GaloisField p e) α, rootPair Tag.G2 (GaloisField p e) β⁆ = ⊥) :
    ∀ x ∈ Qr p e α, ∀ y ∈ Qr p e β, x * y = y * x := by
  intro x hx y hy
  have hιinj : Function.Injective (adjointGroup Tag.G2 (GaloisField p e)).subtype :=
    Subtype.val_injective
  have h1 : ((adjointGroup Tag.G2 (GaloisField p e)).subtype x) ∈
      rootPair Tag.G2 (GaloisField p e) α := by
    rw [← map_Qr_subtype hα]
    exact Subgroup.mem_map_of_mem _ hx
  have h2 : ((adjointGroup Tag.G2 (GaloisField p e)).subtype y) ∈
      rootPair Tag.G2 (GaloisField p e) β := by
    rw [← map_Qr_subtype hβ]
    exact Subgroup.mem_map_of_mem _ hy
  have h3 := Subgroup.mem_centralizer_iff.mp
    ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) h1) _ h2
  apply hιinj
  rw [map_mul, map_mul]
  exact h3.symm

theorem g2_dichotomy (hp2 : p ≠ 2) (he : 1 ≤ e) :
    ∀ R ∈ fundamentalSubgroups StatedLieTag.G2 (modelUniv StatedLieTag.G2 0 p e Fact.out).D,
      ∀ R' ∈ fundamentalSubgroups StatedLieTag.G2 (modelUniv StatedLieTag.G2 0 p e Fact.out).D,
        ∀ w ∈ R, w ∈ R' → orderOf w = 2 → R = R' ∨ ∀ x ∈ R, ∀ y ∈ R', x * y = y * x := by
  change ∀ R ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)),
    ∀ R' ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)),
    ∀ w ∈ R, w ∈ R' → orderOf w = 2 → R = R' ∨ ∀ x ∈ R, ∀ y ∈ R', x * y = y * x
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e (by omega)]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have hroot : ∀ {γ : Fin Tag.G2.rank → ℤ},
      (IsLongestRoot (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)) γ ∨
        (StatedLieTag.G2 = StatedLieTag.G2 ∧
          γ ∈ (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)).roots) ∨
        (StatedLieTag.G2 = StatedLieTag.trialityD4 ∧
          γ ∈ (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)).roots)) →
      IsRoot Tag.G2 γ := by
    intro γ hγ
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  rintro R ⟨g₀, γ, hγ, rfl⟩ R' ⟨g₁, γ', hγ', rfl⟩ w hwR hwR' hw2
  have hγroot := hroot hγ
  have hγ'root := hroot hγ'
  obtain ⟨a, c, ha, ha1, hγa, hcd, hcu⟩ := g2_exists_signInvolution hp2 he hγroot
  obtain ⟨a', c', ha', ha'1, hγ'a', hc'd, hcu'⟩ := g2_exists_signInvolution hp2 he hγ'root
  have hww : w * w = 1 := by
    rw [← pow_two]
    exact (orderOf_eq_prime_iff.mp hw2).1
  have hw1 : w ≠ 1 := (orderOf_eq_prime_iff.mp hw2).2
  have hwc : w = g₀ * c * g₀⁻¹ := ((hcu.conj g₀).unique w hwR hww).resolve_left hw1
  have hwc' : w = g₁ * c' * g₁⁻¹ := ((hcu'.conj g₁).unique w hwR' hww).resolve_left hw1
  have hg : IsUniqueInvolution (conjSub (g₀⁻¹ * g₁) (Qr p e γ')) c := by
    have h1 := hcu'.conj (g₀⁻¹ * g₁)
    have e1 : g₀⁻¹ * g₁ * c' * (g₀⁻¹ * g₁)⁻¹ = c := by
      calc g₀⁻¹ * g₁ * c' * (g₀⁻¹ * g₁)⁻¹ = g₀⁻¹ * (g₁ * c' * g₁⁻¹) * g₀ := by group
        _ = g₀⁻¹ * w * g₀ := by rw [← hwc']
        _ = c := by rw [hwc]; group
    rwa [e1] at h1
  obtain ⟨δ', hδ'k, hR'⟩ := g2_conj_Qr_eq_of_involution hp2 he hγ'root ha ha1 hcd hg
  obtain ⟨α, β, hcases, hker, -, hcomm, -⟩ := g2_toral_data hodd ha ha1
  have hαroot : IsRoot Tag.G2 α := by
    have : α ∈ rootCharKernel a := by rw [hker]; simp
    exact this.1
  have hβroot : IsRoot Tag.G2 β := by
    have : β ∈ rootCharKernel a := by rw [hker]; simp
    exact this.1
  have hcomm1 : Commutes (Qr p e α) (Qr p e β) := Qr_commute hαroot hβroot hcomm
  have hcomm2 : Commutes (Qr p e β) (Qr p e α) := fun x hx y hy => (hcomm1 y hy x hx).symm
  have hcls : ∀ {δ : Fin Tag.G2.rank → ℤ}, δ ∈ rootCharKernel a →
      Qr p e δ = Qr p e α ∨ Qr p e δ = Qr p e β := by
    intro δ hδ
    rw [hker] at hδ
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hδ
    rcases hδ with h | h | h | h
    · exact Or.inl (by rw [h])
    · exact Or.inl (by rw [h, Qr_neg])
    · exact Or.inr (by rw [h])
    · exact Or.inr (by rw [h, Qr_neg])
  have hR'eq : conjSub g₁ (Qr p e γ') = conjSub g₀ (Qr p e δ') := by
    rw [← hR', ← conjSub_mul]
    congr 1
    group
  show conjSub g₀ (Qr p e γ) = conjSub g₁ (Qr p e γ') ∨
    ∀ x ∈ conjSub g₀ (Qr p e γ), ∀ y ∈ conjSub g₁ (Qr p e γ'), x * y = y * x
  rw [hR'eq]
  rcases hcls hγa with h1 | h1 <;> rcases hcls hδ'k with h2 | h2
  · left
    rw [h1, h2]
  · right
    rw [h1, h2]
    exact hcomm1.conjSub g₀
  · right
    rw [h1, h2]
    exact hcomm2.conjSub g₀
  · left
    rw [h1, h2]

end Sign

end CFSG.ClassicalInvolution.Q3.Q3OF
