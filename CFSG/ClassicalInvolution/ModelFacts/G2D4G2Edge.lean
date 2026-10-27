module

public import CFSG.ClassicalInvolution.ModelFacts.G2D4SL2Core
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2Lin
public import CFSG.ClassicalInvolution.ModelFacts.G2D4G2NC
public import CFSG.ClassicalInvolution.ModelFacts.G2D4Max

public noncomputable section

namespace CFSG.ClassicalInvolution.G2D4Models

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ClassicalInvolution.Balance.Bootstrap CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section Chart

variable {F : Type} [Field F] {K : Type} [Group K]

theorem linAct_conj {Φ : SL2 F →* K} {x : K} (g : K) (h : LinAct Φ x) :
    LinAct ((MulAut.conj g).toMonoidHom.comp Φ) (g * x * g⁻¹) := by
  obtain ⟨D, hD⟩ := h
  refine ⟨D, fun A => ?_⟩
  show g * x * g⁻¹ * (g * Φ A * g⁻¹) * (g * x * g⁻¹)⁻¹ = g * Φ (glConjSL D A) * g⁻¹
  rw [← hD A]
  group

theorem eq_of_sylow_le_normalizer_of_chart [Finite F] (hodd : Odd (Nat.card F))
    (h4 : 4 ≤ Nat.card F) {Φ₀ : SL2 F →* K} (hΦ₀ : Function.Injective Φ₀)
    (H1₀ : ∀ x : K, x * Φ₀ (-1) = Φ₀ (-1) * x → LinAct Φ₀ x) (g₀ g : K)
    (H4 : conjSub g (conjSub g₀ Φ₀.range) ≠ conjSub g₀ Φ₀.range →
      ¬ Commutes (conjSub g₀ Φ₀.range) (conjSub g (conjSub g₀ Φ₀.range)))
    {R : Subgroup K} (hRJ : R ≤ conjSub g (conjSub g₀ Φ₀.range)) (hR2 : IsPGroup 2 R)
    (hmax : ∀ T : Subgroup K, T ≤ conjSub g (conjSub g₀ Φ₀.range) → IsPGroup 2 T →
      R ≤ T → T = R)
    (hRN : R ≤ Subgroup.normalizer ((conjSub g₀ Φ₀.range : Subgroup K) : Set K)) :
    conjSub g (conjSub g₀ Φ₀.range) = conjSub g₀ Φ₀.range := by
  set Φ : SL2 F →* K := (MulAut.conj g₀).toMonoidHom.comp Φ₀ with hΦ
  set Ψ : SL2 F →* K := (MulAut.conj (g * g₀)).toMonoidHom.comp Φ₀ with hΨ
  have hΦr : Φ.range = conjSub g₀ Φ₀.range := MonoidHom.range_comp _ _
  have hΨr : Ψ.range = conjSub g (conjSub g₀ Φ₀.range) := by
    rw [← conjSub_mul]
    exact MonoidHom.range_comp _ _
  have hΨinj : Function.Injective Ψ := (MulAut.conj (g * g₀)).injective.comp hΦ₀
  have hconjLin : ∀ h x : K, x * (h * Φ₀ (-1) * h⁻¹) = (h * Φ₀ (-1) * h⁻¹) * x →
      LinAct ((MulAut.conj h).toMonoidHom.comp Φ₀) x := by
    intro h x hx
    have h1 : (h⁻¹ * x * h) * Φ₀ (-1) = Φ₀ (-1) * (h⁻¹ * x * h) := by
      calc h⁻¹ * x * h * Φ₀ (-1) = h⁻¹ * (x * (h * Φ₀ (-1) * h⁻¹)) * h := by group
        _ = h⁻¹ * ((h * Φ₀ (-1) * h⁻¹) * x) * h := by rw [hx]
        _ = Φ₀ (-1) * (h⁻¹ * x * h) := by group
    have := linAct_conj h (H1₀ _ h1)
    have e : h * (h⁻¹ * x * h) * h⁻¹ = x := by group
    rwa [e] at this
  have H1 : ∀ x : K, x * Φ (-1) = Φ (-1) * x → LinAct Φ x := fun x hx => hconjLin g₀ x hx
  have H2 : ∀ x : K, x * Ψ (-1) = Ψ (-1) * x → LinAct Ψ x := fun x hx => hconjLin (g * g₀) x hx
  have H4' : (∀ A B, Φ A * Ψ B = Ψ B * Φ A) → Ψ.range = Φ.range := by
    intro hcomm
    by_contra hne
    rw [hΨr, hΦr] at hne
    refine H4 hne ?_
    intro x hx y hy
    rw [← hΦr] at hx
    rw [← hΨr] at hy
    obtain ⟨A, rfl⟩ := hx
    obtain ⟨B, rfl⟩ := hy
    exact hcomm A B
  let P : Sylow 2 (SL2 F) :=
    ⟨R.comap Ψ, hR2.comap_of_injective Ψ hΨinj, fun {T} hT hle => by
      have h1 : T.map Ψ ≤ conjSub g (conjSub g₀ Φ₀.range) := hΨr ▸ Subgroup.map_le_range Ψ T
      have h3 : R ≤ T.map Ψ := by
        intro x hx
        obtain ⟨y, rfl⟩ : x ∈ Ψ.range := hΨr ▸ hRJ hx
        exact ⟨y, hle hx, rfl⟩
      have h5 := hmax _ h1 (hT.map Ψ) h3
      refine le_antisymm (fun y hy => ?_) hle
      show Ψ y ∈ R
      rw [← h5]
      exact ⟨y, hy, rfl⟩⟩
  have hc : IsUniqueInvolution (conjSub g₀ Φ₀.range) (g₀ * Φ₀ (-1) * g₀⁻¹) :=
    (isUniqueInvolution_range_sl2 hodd hΦ₀).conj g₀
  have H5 : ∀ x ∈ (P : Subgroup (SL2 F)), Ψ x * Φ (-1) = Φ (-1) * Ψ x := by
    intro x hx
    have hxR : Ψ x ∈ R := hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (normalizer_le_centralizer hc (hRN hxR))
  have := range_eq_of_sylow_commute hodd h4 hΨinj H1 H2 H4' P H5
  rwa [hΨr, hΦr] at this

end Chart

section Standard

variable {p e : ℕ} [Fact p.Prime]

theorem exists_standard_chart_g2 (hodd : Odd (Nat.card (GaloisField p e)))
    {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ) :
    ∃ Φ₀ : SL2 (GaloisField p e) →* ↥(adjointGroup Tag.G2 (GaloisField p e)),
      Function.Injective Φ₀ ∧
        Φ₀.range = rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) γ ⊔
          rootGroup (rootOperatorFamily Tag.G2) (GaloisField p e) (-γ) ∧
        ∀ x : ↥(adjointGroup Tag.G2 (GaloisField p e)), x * Φ₀ (-1) = Φ₀ (-1) * x →
          LinAct Φ₀ x := by
  set F := GaloisField p e with hF
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
  obtain ⟨w, i, hw⟩ := isRoot_iff_exists_smul_single.mp hγ
  have hmem : ∀ A : SL2 F, rootChart Tag.G2 F w i A ∈ adjointGroup Tag.G2 F := by
    intro A
    have h : rootChart Tag.G2 F w i A ∈ (rootChart Tag.G2 F w i).range := ⟨A, rfl⟩
    rw [rootChart_range hw] at h
    exact sup_le (rootSubgroup_le_adjointGroup γ) (rootSubgroup_le_adjointGroup (-γ)) h
  let Φ₀ : SL2 F →* ↥(adjointGroup Tag.G2 F) :=
    (rootChart Tag.G2 F w i).codRestrict (adjointGroup Tag.G2 F) hmem
  have hcomp : ι.comp Φ₀ = rootChart Tag.G2 F w i := MonoidHom.ext fun A => rfl
  have hinj : Function.Injective Φ₀ := fun A B hAB =>
    rootChart_injective hK2 w i (congrArg ι hAB)
  have hrange : Φ₀.range = Q := by
    apply Subgroup.map_injective hιinj
    rw [hQmap, ← rootChart_range hw, ← hcomp, MonoidHom.range_comp]
  have hneg : ι (Φ₀ (-1)) = rootDiagUnit Tag.G2 a := rootChart_neg_one hodd ha hne1 hγa hw
  refine ⟨Φ₀, hinj, hrange, fun x hx => ?_⟩
  have hX : ι x ∈ toralCentralizer Tag.G2 F a := by
    rw [mem_toralCentralizer]
    refine ⟨x.2, ?_⟩
    have h1 : ι x * rootDiagUnit Tag.G2 a = rootDiagUnit Tag.G2 a * ι x := by
      rw [← hneg, ← map_mul, ← map_mul, hx]
    rw [mul_inv_eq_iff_eq_mul, ← h1]
  obtain ⟨D, hD⟩ := toralCentralizer_le_linActSubgroup hodd ha hne1 hγa hw hX
  refine ⟨D, fun A => hιinj ?_⟩
  have h1 : ι (x * Φ₀ A * x⁻¹) = ι x * rootChart Tag.G2 F w i A * (ι x)⁻¹ := by
    rw [map_mul, map_mul, map_inv]
    rfl
  rw [h1, hD A]
  rfl

theorem eq_of_isMaxPGroup_le_normalizer_g2 (hp2 : p ≠ 2) (hq : 5 ≤ p ^ e)
    (hadm : StatedLieAdmissible .G2 0 p e) :
    ∀ Q ∈ fundamentalSubgroups StatedLieTag.G2 (modelUniv StatedLieTag.G2 0 p e Fact.out).D,
      ∀ g : (modelUniv StatedLieTag.G2 0 p e Fact.out).K,
        ∀ R : Subgroup (modelUniv StatedLieTag.G2 0 p e Fact.out).K,
          R ≤ conjSub g Q → IsPGroup 2 R →
          (∀ T : Subgroup (modelUniv StatedLieTag.G2 0 p e Fact.out).K,
            T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
          R ≤ Subgroup.normalizer (Q : Set (modelUniv StatedLieTag.G2 0 p e Fact.out).K) →
          conjSub g Q = Q := by
  have hnc := noCommutingConj_g2 hp2 hq hadm
  change ∀ Q ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)),
    ∀ g : ↥(adjointGroup Tag.G2 (GaloisField p e)),
      ∀ R : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e)),
        R ≤ conjSub g Q → IsPGroup 2 R →
        (∀ T : Subgroup ↥(adjointGroup Tag.G2 (GaloisField p e)),
          T ≤ conjSub g Q → IsPGroup 2 T → R ≤ T → T = R) →
        R ≤ Subgroup.normalizer (Q : Set ↥(adjointGroup Tag.G2 (GaloisField p e))) →
        conjSub g Q = Q
  change ∀ F ∈ fundamentalSubgroups StatedLieTag.G2
      (CFSG.LieType.Steinberg.Adjoint.g2Datum (GaloisField p e)),
    ∀ g : ↥(adjointGroup Tag.G2 (GaloisField p e)), conjSub g F ≠ F → ¬ Commutes F (conjSub g F)
    at hnc
  have he : e ≠ 0 := by
    rintro rfl
    simp at hq
  have hodd : Odd (Nat.card (GaloisField p e)) := by
    rw [GaloisField.card p e he]
    exact (Nat.Prime.odd_of_ne_two Fact.out hp2).pow
  have h4 : 4 ≤ Nat.card (GaloisField p e) := by
    rw [GaloisField.card p e he]
    omega
  intro Q hQ g R hRJ hR2 hmax hRN
  have H4 := hnc Q hQ g
  obtain ⟨g₀, γ, hγ, rfl⟩ := hQ
  have hγroot : IsRoot Tag.G2 γ := by
    rcases hγ with h | ⟨-, h⟩ | ⟨h, -⟩
    · exact mem_adjDatum_roots.1 h.1
    · exact mem_adjDatum_roots.1 h
    · exact absurd h (by decide)
  obtain ⟨Φ₀, hinj, hrange, H1₀⟩ := exists_standard_chart_g2 hodd hγroot
  rw [← hrange] at H4 hRJ hmax hRN ⊢
  exact eq_of_sylow_le_normalizer_of_chart hodd h4 hinj H1₀ g₀ g H4 hRJ hR2 hmax hRN

end Standard

end CFSG.ClassicalInvolution.G2D4Models
