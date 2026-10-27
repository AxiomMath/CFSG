module

public import CFSG.RankThree.PartOne.D4RC.RxFrame
public import CFSG.HardMathSupport.Seitz.TrialityOdd.Inner.PhiRows.RouteWUnitaryIso

public noncomputable section

namespace CFSG.HardMathSupport.Seitz.TrialityOdd.Inner

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.PartOne.KF4 CFSG.RankThree.PartOne
  CFSG.RankThree.Lattice CFSG.RankThree.Chevalley.TrialityFold CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.D4RC (rcl_sigmaFamily_twist rcl_map_fix_eq rcl_card_fix_split
  rcl_card_fix_unitary)
open CFSG.RankThree.Classical2 (fixSubgroup unitarySet)
open scoped Matrix MatrixGroups Pointwise

set_option linter.unusedSectionVars false

local notation "𝒞[" K ", " σ "]" => graphFixedRootGroup TwistTag.D4 K (RingEquiv.toRingHom σ)

structure D4PhiFrame (ℓ f : ℕ) [Fact ℓ.Prime] (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (ε : ℤ)
    (p : ℕ) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    where
  hf : 1 ≤ f
  hK : Nat.card K = (ℓ ^ f) ^ 3
  hσ : ∀ c, σ c = c ^ (ℓ ^ f)
  hε : ε = 1 ∨ ε = -1
  hp : p.Prime
  hp3 : 3 < p
  hpd : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 + ε * ((ℓ ^ f : ℕ) : ℤ) + 1
  n : ModGL TwistTag.D4.tag L
  hn : n ∈ monomialSubgroup TwistTag.D4.tag L
  w : WeylGroup TwistTag.D4.tag
  hnw : weylQuotientHom TwistTag.D4.tag L ⟨n, hn⟩ = w
  hw : ∀ x, w • x = d4T36M ε *ᵥ permLattice TwistTag.D4.perm.symm x
  g0 : ModGL TwistTag.D4.tag L
  hg0C : g0 ∈ adjointGroup TwistTag.D4.tag L
  hg0 : twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) g0 = g0 * n
  hperf : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), P ≤ adjointGroup TwistTag.D4.tag L →
    (∀ x ∈ P, twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) x = x) →
      P ≤ (triEmb K σ L).range
  hconj : ∀ Q : Subgroup 𝒞[K, σ], IsPGroup p Q → ∃ c : 𝒞[K, σ], ∀ y ∈ Q,
    g0⁻¹ * triEmb K σ L (c * y * c⁻¹) * g0 ∈
      twistedTorusOf n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))

section Special

variable {ℓ f : ℕ} [Fact ℓ.Prime] {K : Type} [Field K] [Finite K] {σ : K ≃+* K} {ε : ℤ}
  {p : ℕ} {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]

@[expose] def d4phiQ (F : D4PhiFrame ℓ f K σ ε p L) (i : Fin 4) :
    Subgroup (ModGL TwistTag.D4.tag L) :=
  rootSpan TwistTag.D4.tag L (d4Sigma i) ⊓
    twistedFixedPoints F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))

structure D4PhiSpecial (F : D4PhiFrame ℓ f K σ ε p L) (x : 𝒞[K, σ]) (i : Fin 4) where
  c : 𝒞[K, σ]
  b : Fin TwistTag.D4.tag.rank → Lˣ
  hx : orderOf x = p
  hb : rootDiagUnit TwistTag.D4.tag b = F.g0⁻¹ * triEmb K σ L (c * x * c⁻¹) * F.g0
  hh : rootDiagUnit TwistTag.D4.tag b ∈
    twistedTorusOf F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))
  hker : rootCharKernel b = d4Sigma i

abbrev d4phiPsi {F : D4PhiFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4} (sp : D4PhiSpecial F x i) :
    Subgroup.centralizer ({x} : Set 𝒞[K, σ]) →* ModGL TwistTag.D4.tag L :=
  d4QPsi (triEmb K σ L) F.g0 sp.c x

@[expose] def d4phiPx {F : D4PhiFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : D4PhiSpecial F x i) : Subgroup 𝒞[K, σ] :=
  ((d4phiQ F i).comap (d4phiPsi sp)).map (Subgroup.centralizer ({x} : Set 𝒞[K, σ])).subtype

structure D4PhiAlgData (F : D4PhiFrame ℓ f K σ ε p L) (i : Fin 4) where
  ρ : SL(3, L) →* ModGL TwistTag.D4.tag L
  σ' : Fin 3 → Fin 3 → Fin TwistTag.D4.tag.rank → ℤ
  Φ' : SL(3, L) ≃* SL(3, L)
  H : SL(3, L)
  frame : IsA2Frame ρ σ'
  sigma_eq : {r | ∃ a b : Fin 3, a ≠ b ∧ r = σ' a b} = d4Sigma i
  Φ_eq : ∀ X, F.n * twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) (ρ X) * F.n⁻¹ = ρ (Φ' X)
  fam : IsSigmaFamily (F.n * diagramMap TwistTag.D4 L) (iterateFrobenius L ℓ f) (d4Sigma i)
    (fun _ : Unit => (fixSubgroup Φ').map ρ)
  split : ε = 1 → ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔ ∃ Y : SL(3, fixSubfield σ),
    X = H * Matrix.SpecialLinearGroup.map (algebraMap (fixSubfield σ) L) Y * H⁻¹
  unit : ε = -1 → ∀ X : SL(3, L), X ∈ fixSubgroup Φ' ↔ ∃ Y ∈ unitarySet (ℓ ^ f) 3,
    Matrix.SpecialLinearGroup.toGL X = Matrix.SpecialLinearGroup.toGL H * Y *
      (Matrix.SpecialLinearGroup.toGL H)⁻¹
  std : ∃ v : WeylGroup TwistTag.D4.tag,
    ρ = (MulAut.conj (canonicalRep (coxeterSystem TwistTag.D4.tag) L v)).toMonoidHom.comp
      (d4rhoStd L) ∧ ∀ a b, σ' a b = v • d4Chain a b
  shape : ε = -1 → ∃ (π : Equiv.Perm (Fin 3)) (β : Fin 3 → Fin 3 → Lˣ),
    ∀ (a b : Fin 3) (hab : a ≠ b) (t : L),
      ((Φ' (Matrix.SpecialLinearGroup.transvection hab t) : SL(3, L)) :
        Matrix (Fin 3) (Fin 3) L) = 1 + Matrix.single (π b) (π a) ((β a b : L) * t ^ ℓ ^ f)

theorem d4phi_exists_algData (F : D4PhiFrame ℓ f K σ ε p L) (i : Fin 4) :
    Nonempty (D4PhiAlgData F i) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Module.Finite (fixSubfield σ) K := Module.Finite.of_finite
  have : Algebra.IsAlgebraic (fixSubfield σ) K := Algebra.IsAlgebraic.of_finite _ K
  have : IsAlgClosure (fixSubfield σ) L := IsAlgClosure.ofAlgebraic (fixSubfield σ) K L
  have hkc : Nat.card (fixSubfield σ) = ℓ ^ f := card_fixSubfield_cube hℓ F.hf F.hK σ F.hσ
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  have hq2' : ε = 1 ∨ 2 < ℓ ^ f := by
    have hq2 : 2 ≤ ℓ ^ f := Nat.one_lt_pow (by have := F.hf; omega) hℓ.one_lt
    rcases F.hε with rfl | rfl
    · exact Or.inl rfl
    · refine Or.inr ?_
      by_contra hlt
      have h2 : ℓ ^ f = 2 := by omega
      have hpd := F.hpd
      rw [h2] at hpd
      have h3 : (p : ℤ) ∣ 3 := by simpa using hpd
      have := Int.le_of_dvd (by norm_num) h3
      have := F.hp3
      omega
  obtain ⟨v, hv0, hv2, hvS⟩ := exists_smul_d4StdA2 i
  obtain ⟨ρ, σ', Φ', H, hframe, hS3eq, hΦ'', hfam, hsplit, hunit, hshape, -, hstd, hσstd⟩ :=
    d4phi_family_iso F.hf hkc F.hε hq2' Fr hFr F.n F.hn
      (fun x => by rw [F.hnw]; exact F.hw x) i v hv0 hv2 hvS
  exact ⟨⟨ρ, σ', Φ', H, hframe, hS3eq, hΦ'', hfam, hsplit, hunit, ⟨v, hstd, hσstd⟩, hshape⟩⟩

theorem d4phi_psi_props (F : D4PhiFrame ℓ f K σ ε p L) {x : 𝒞[K, σ]} {i : Fin 4}
    (sp : D4PhiSpecial F x i) :
    Finite (d4phiQ F i) ∧ CFSG.IsQuasisimple (d4phiQ F i) ∧
    (∀ y, d4phiPsi sp y ∈ torusGroup TwistTag.D4.tag L ⊔
      rootSpan TwistTag.D4.tag L (d4Sigma i)) ∧
    (∀ y, F.n * twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) (d4phiPsi sp y) * F.n⁻¹ =
      d4phiPsi sp y) ∧
    (∀ y, d4phiPsi sp y ∈ adjointGroup TwistTag.D4.tag L) ∧
    d4phiQ F i ≤ (d4phiPsi sp).range ∧
    (∀ y, ∀ u ∈ d4phiQ F i, d4phiPsi sp y * u * (d4phiPsi sp y)⁻¹ ∈ d4phiQ F i) ∧
    (∀ y, (∀ u ∈ d4phiQ F i, d4phiPsi sp y * u = u * d4phiPsi sp y) →
      d4phiPsi sp y ∈ subtorusSigma F.n (twistHom TwistTag.D4 L (iterateFrobenius L ℓ f))
        (d4Sigma i)) := by
  classical
  have hℓ : ℓ.Prime := Fact.out
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hcomm := d4Q_hcomm K σ F.hσ L
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  obtain ⟨D⟩ := d4phi_exists_algData F i
  have hrange : D.ρ.range = rootSpan TwistTag.D4.tag L (d4Sigma i) := by
    rw [D.frame.range, D.sigma_eq]
  have hQP : (fixSubgroup D.Φ').map D.ρ = d4phiQ F i :=
    rcl_map_fix_eq D.frame.injective hrange D.Φ_eq
  have hfam := D.fam
  rw [hQP] at hfam
  obtain ⟨hPfin, hPq, hPQ, hPR, hPadj, hPnorm, hPcent⟩ := rcl_sigmaFamily_twist hfam
  have hS : ∀ α ∈ d4Sigma i, IsRoot TwistTag.D4.tag α := fun α hα => isRoot_of_mem_d4Sigma hα
  have hrootneg : ∀ α ∈ rootCharKernel sp.b, -α ∈ rootCharKernel sp.b := fun α hα =>
    ⟨IsRoot.neg hα.1, by rw [d4Q_rootChar_neg, hα.2, inv_one]⟩
  have hSn : ∀ α ∈ d4Sigma i, -α ∈ d4Sigma i := fun α hα => by
    rw [← sp.hker] at hα ⊢
    exact hrootneg α hα
  have hιC := triEmb_mem_adjointGroup (K := K) (σ := σ) (L := L)
  have hιΦ := triEmb_fixed (K := K) (σ := σ) (L := L) Fr hcomm
  have hperf' : ∀ P : Subgroup (ModGL TwistTag.D4.tag L), Finite P →
      P ≤ adjointGroup TwistTag.D4.tag L → (∀ x ∈ P, twistHom TwistTag.D4 L Fr x = x) →
        ⁅P, P⁆ = P → P ≤ (triEmb K σ L).range := fun P _ hPC hPF _ => F.hperf P hPC hPF
  have hordW := not_dvd_card_weylGroup_D4 F.hp F.hp3
  have hsub : ∀ α ∈ d4Sigma i, rootChar sp.b α = 1 := fun α hα => by
    rw [← sp.hker] at hα
    exact hα.2
  have hcb : rootDiagUnit TwistTag.D4.tag sp.b ∈
      subtorusSigma F.n (twistHom TwistTag.D4 L Fr) (d4Sigma i) :=
    Subgroup.mem_inf.2 ⟨sp.hh, (rootDiagUnit_mem_centralizer_rootSpan_iff sp.b hS).2 hsub⟩
  have hcS : sp.c * x * sp.c⁻¹ ∈ subtorusImage (triEmb K σ L) F.g0
      (subtorusSigma F.n (twistHom TwistTag.D4 L Fr) (d4Sigma i)) :=
    (mem_subtorusImage_iff (triEmb K σ L) F.g0 _ (sp.c * x * sp.c⁻¹)).2
      (by rw [← sp.hb]; exact hcb)
  have hkerZ : ∀ a : Fin TwistTag.D4.tag.rank → Lˣ,
      rootDiagUnit TwistTag.D4.tag a = F.g0⁻¹ * triEmb K σ L (sp.c * x * sp.c⁻¹) * F.g0 →
        rootCharKernel a ⊆ d4Sigma i := fun a ha => by
    have hab : a = sp.b :=
      rootDiagUnit_injective (τ := TwistTag.D4.tag) (K := L) (ha.trans sp.hb.symm)
    rw [hab]
    exact sp.hker.subset
  obtain ⟨ψ, -, hψ, h4, h5, h6, hPψ, -⟩ := sigma_embedding_data (triEmb K σ L)
    triEmb_injective hιC (twistHom TwistTag.D4 L Fr) hιΦ F.n F.g0 F.hg0C F.hg0 hperf' F.hp hordW
    hS hSn (fun _ : Unit => d4phiQ F i) (fun _ => hPfin) (fun _ => hPq) (fun _ => hPQ)
    (fun _ => hPR) (fun _ => hPadj) (fun _ y hy hyR u hu => hPnorm y hy hyR u hu)
    (fun y hy hyR hc => hPcent y hy hyR (fun u hu => hc () u hu)) sp.hx sp.c hcS hkerZ
  have hdψ : d4phiPsi sp = ψ :=
    MonoidHom.ext fun y => (d4QPsi_apply (triEmb K σ L) F.g0 sp.c x y).trans (hψ y).symm
  rw [hdψ]
  refine ⟨hPfin, hPq, h4, h5, h6, hPψ (), fun y u hu => ?_, fun y hy => ?_⟩
  · have hyR : ψ y ∈ twistedFixedPoints F.n (twistHom TwistTag.D4 L Fr) :=
      mem_twistedFixedPoints.2 (h5 y)
    exact hPnorm (ψ y) (h4 y) hyR u hu
  · exact hPcent (ψ y) (h4 y) (mem_twistedFixedPoints.2 (h5 y)) hy

section PxBasic

variable {F : D4PhiFrame ℓ f K σ ε p L} {x : 𝒞[K, σ]} {i : Fin 4} (sp : D4PhiSpecial F x i)

theorem d4phiPx_le_centralizer : d4phiPx sp ≤ Subgroup.centralizer ({x} : Set 𝒞[K, σ]) := by
  rintro _ ⟨y, -, rfl⟩
  exact y.2

end PxBasic

end Special

end CFSG.HardMathSupport.Seitz.TrialityOdd.Inner
